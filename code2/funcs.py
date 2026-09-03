"""Interval enclosures of the paper's functions (Fpaper, Dpaper, D2paper,
Mpaper, log X, Sbar) built from the fpi ops, at scale 10^12.

Every op sequence here is meant to be mirrored 1:1 by the Lean checkCell
(see GENERATOR FEEDBACK in Bootstrap/CELLSPEC.md).  Fixed Taylor depths:

  N_LOG = 13   (log series; arguments are kept in [1/2, 2] by the power-of-2
                reduction below, so |z| <= 1/3 and the series error
                |z|^27/(1-z^2) <= 2e-13)
  N_EXP = 16   (exp series on |arg| <= 1: error 17/(16!*16) ~ 5e-14)
  KEXP  = 16   (exp(-D) = exp(-D/16)^16 for D up to ~13.9)

Argument reductions (soundness on the Lean side is one lemma each):
  * log r for r in (0, 2]:  choose minimal k >= 0 with r_hi * 2^k >= scale,
    then log r = log(r * 2^k) - k * log 2, with LOG2I = log 13 (point 2*scale).
  * exp(-D) for D in (0, 16]:  exp(-D) = (exp(-D/16))^16.

Polynomial evaluation: ALWAYS the mean-value form
    P(L) c= P(point m) + P'(L) * (L - m),   m = (L.lo + L.hi) / 2  (ediv)
(on a point interval the second term is exactly (0,0), so this degenerates
to plain Horner - no separate point path needed).
"""

from fractions import Fraction

import fpi
from fpi import (scale, point, add, neg, mul, inv, divNat, mulNat, pow_,
                 ediv, expSafe, logSafe)

N_LOG = 13
N_EXP = 16
KEXP = 16

# ---------------------------------------------------------------- coefficients
# P(l) = sum_{j=1}^8 c_j l^j, coefficients exact decimals * 10^12.
_C = [-348694, -451951, 6611582, -24021517, 43622007, -43154000, 22319017,
      -4736149]
CP = [0] + [c * 10**6 for c in _C]                     # degree 8, index=power
CQ = [q * 10**6 for q in [1352506, -1355324, 1579442, -511711]]  # degree 3

def _deriv(cs):
    return [j * c for j, c in enumerate(cs)][1:]

DCP = _deriv(CP)            # P'
DDCP = _deriv(DCP)          # P''
DQ = _deriv(CQ)             # Q'

def _polysub(a, b):
    n = max(len(a), len(b))
    a = a + [0] * (n - len(a)); b = b + [0] * (n - len(b))
    return [x - y for x, y in zip(a, b)]

CA = _polysub(DCP, CP)                                  # A = P' - P  (deg 8)
DCA = _deriv(CA)
CB = _polysub(_polysub(DDCP, [2 * c for c in DCP]), [-c for c in CP])  # P''-2P'+P
DCB = _deriv(CB)

# ------------------------------------------------------- fast(=bit-identical) ops
# pow_ recomputed from scratch is O(n^2) inside the series; use incremental
# powers -- the recurrence pow(I,n+1) = mul(pow(I,n), I) is followed exactly,
# so results are bit-identical to fpi.pow_ (self-checked in tests.py).

def _powers(I, nmax):
    ps = [point(scale)]
    for _ in range(nmax):
        ps.append(mul(ps[-1], I))
    return ps

def fexp(n, I):
    """bit-identical to fpi.exp(n, I)"""
    def endpoint(z):
        P = point(z)
        ps = _powers(P, n)
        acc = point(0)
        for i in range(n):
            acc = add(acc, divNat(ps[i], fpi.factorial(i)))
        err = divNat(mulNat(pow_(fpi.abs_(P), n), n + 1), fpi.factorial(n) * n)
        return acc, err
    Plo, Elo = endpoint(I[0])
    Phi, Ehi = endpoint(I[1])
    return (Plo[0] - Elo[1], Phi[1] + Ehi[1])

def flog(n, I):
    """bit-identical to fpi.log(n, I)"""
    def endpoint(z):
        Z = fpi.logArgument(z)
        ps = _powers(Z, 2 * n + 1)
        acc = point(0)
        for i in range(n):
            acc = add(acc, divNat(ps[2 * i + 1], 2 * i + 1))
        num = pow_(fpi.abs_(Z), 2 * n + 1)
        den = add(point(scale), neg(ps[2]))
        err = fpi.mulNonneg(num, inv(den))
        return acc, err
    Plo, Elo = endpoint(I[0])
    Phi, Ehi = endpoint(I[1])
    return mulNat((Plo[0] - Elo[1], Phi[1] + Ehi[1]), 2)

# ------------------------------------------------------------------- helpers

class UnsafeOp(Exception):
    """a safety predicate of the Lean checker would fail"""

def _require(b, what):
    if not b:
        raise UnsafeOp(what)

def logDirect(I):
    """log of I c= (0, ~2.3*scale]; use only when I.lo is not tiny."""
    _require(logSafe(N_LOG, I), "logSafe")
    return flog(N_LOG, I)

LOG2I = None  # initialised below (needs logDirect)

def logPos(I):
    """enclosure of log over I with I.lo > 0, via power-of-2 reduction."""
    _require(I[0] > 0, "logPos positive")
    k = 0
    while I[1] << k < scale:
        k += 1
    J = mulNat(I, 1 << k)
    return add(logDirect(J), neg(mulNat(LOG2I, k)))

LOG2I = flog(N_LOG, point(2 * scale))   # [693147180546, 693147180582]
assert logSafe(N_LOG, point(2 * scale))

def expNegCell(I):
    """enclosure of exp(-r) for r in I c= [0, scale]."""
    J = neg(I)
    _require(expSafe(N_EXP, J), "expSafe cell")
    return fexp(N_EXP, J)

def expNegBig(I):
    """enclosure of exp(-D) for D in I c= (0, 16*scale]."""
    J = divNat(neg(I), KEXP)
    _require(expSafe(N_EXP, J), "expSafe big")
    return pow_(fexp(N_EXP, J), KEXP)

def mv(cs, dcs, L):
    """mean-value polynomial enclosure: P(m) + P'(L)(L - m)."""
    m = ediv(L[0] + L[1], 2)
    M = point(m)
    acc = point(cs[-1])
    for c in reversed(cs[:-1]):
        acc = add(mul(acc, M), point(c))
    dacc = point(dcs[-1])
    for c in reversed(dcs[:-1]):
        dacc = add(mul(dacc, L), point(c))
    return add(acc, mul(dacc, add(L, neg(M))))

# ------------------------------------------------- the paper's functions

def regionEnclosures(R):
    """All enclosures needed by checkCell over an interval R c= (0, scale].

    Returns dict with FI, DI, D2I, MI, logMI, xI (log X).
    Raises UnsafeOp if a safety predicate fails (checker returns False then).
    """
    _require(0 < R[0] and R[0] <= R[1] and R[1] <= scale, "R range")
    onePlus = add(point(scale), R)
    log1p = logDirect(onePlus)
    logr = logPos(R)
    entropy = add(mul(onePlus, log1p), neg(mul(R, logr)))
    e = expNegCell(R)
    PI = mv(CP, DCP, R)
    FI = add(entropy, mul(e, PI))
    DI = add(add(log1p, neg(logr)), mul(e, mv(CA, DCA, R)))
    rr1 = mul(R, onePlus)
    _require(rr1[0] > 0, "inv r(1+r)")
    D2I = add(neg(inv(rr1)), mul(e, mv(CB, DCB, R)))
    MI = mul(mul(R, e), mv(CQ, DQ, R))
    xI = None
    logMI = None
    if MI[0] > 0 and MI[1] < scale:
        logMI = logPos(MI)
        oneMinusM = add(point(scale), neg(MI))
        if DI[0] > 0:
            eD = expNegBig(DI)
            pI = add(point(scale), neg(eD))
            if pI[0] > 0:
                xI = add(logDirect(oneMinusM),
                         mul(logDirect(pI), inv(oneMinusM)))
    return dict(FI=FI, DI=DI, D2I=D2I, MI=MI, logMI=logMI, xI=xI)

def witnessEnclosures(w):
    """point enclosures at the witness u0 = w/scale: FW, DW, SbarW."""
    W = point(w)
    enc = regionEnclosuresLight(W)
    FW, DW = enc
    SbarW = add(FW, neg(mul(W, DW)))
    return FW, DW, SbarW

def regionEnclosuresLight(R):
    """F and D only (for witness point evals)."""
    _require(0 < R[0] and R[0] <= R[1] and R[1] <= scale, "R range")
    onePlus = add(point(scale), R)
    log1p = logDirect(onePlus)
    logr = logPos(R)
    entropy = add(mul(onePlus, log1p), neg(mul(R, logr)))
    e = expNegCell(R)
    FI = add(entropy, mul(e, mv(CP, DCP, R)))
    DI = add(add(log1p, neg(logr)), mul(e, mv(CA, DCA, R)))
    return FI, DI

# fixed enclosures of F(1), D(1)
F1I, D1I = regionEnclosuresLight(point(scale))

# ------------------------------------------------------------- sanity values

if __name__ == "__main__":
    print("LOG2I", LOG2I)
    print("F1I", F1I, [x / 1e12 for x in F1I])
    print("D1I", D1I, [x / 1e12 for x in D1I])
    enc = regionEnclosures((953674, 963674))
    for k, v in enc.items():
        print(k, v, None if v is None else [x / 1e12 for x in v])
