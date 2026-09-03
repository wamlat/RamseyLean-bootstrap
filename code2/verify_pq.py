#!/usr/bin/env python3
"""verify_pq.py -- independent, bit-exact verifier of a piecewise-quadratic
spline certificate (pq_cert*.json), mirroring the FINAL Lean checker
RamseyLean/Bootstrap2/Check.lean (checkCellFast / checkChain / checkWitnesses
/ checkTail) op-for-op on top of the fpi.py port of
RamseyLean/Analysis/FixedPointInterval.lean.

checkCell conjuncts, in Check.lean order (UPGRADED two-endpoint PSI form of
SPEC section 3, rev. 2026-09-02: M is required non-decreasing per cell, so
the box is MI = (n0.M, n1.M); DI = (n1.d, n0.d)):

  0 < n0.lam && n0.lam < n1.lam &&
  0 < n1.d && n1.d <= n0.d &&
  n1.F = n0.F + (n0.d + n1.d) * (n1.lam - n0.lam) &&
  0 < n0.M && n0.M <= n1.M && n1.M < SC &&
  0 < X && X < SC && 0 < Y && Y < SC &&
  0 < wa.lam && wa.lam <= SC && 0 < wa.d &&
  0 < wb.lam && wb.lam <= SC && 0 < wb.d &&
  logPosSafe (point X) && logPosSafe (point Y) &&
  logPosSafe (point n0.M) && logPosSafe (point n1.M) &&
  expSafe 16 (divNat (neg DI) 16) &&
  logSafe 13 pI && logSafe 13 oneM &&
  positive pI && positive oneM &&
  lX.hi <= rhsLog.lo &&                                   -- (XLE)
  (add Sa lX).hi <= 0 &&                                  -- (A1)
  (add (add Sa (point wa.d)) (add lX lY)).hi <= 0 &&      -- (A2)
  (add Sb lY).hi <= 0 &&                                  -- (B1)
  (add (add Sb (point wb.d)) (add lY lX)).hi <= 0 &&      -- (B2)
  0 < (add psiLo0 (neg dip)).lo &&                        -- (PSI0)
  0 < (add psiLo1 (neg dip)).lo                           -- (PSI1)

with
  fpt f   = (f // (2*SC), -((-f) // (2*SC)))              (Int.ediv, b > 0)
  lX      = logPos (point X); lY = logPos (point Y)
  lM0     = logPos (point n0.M); lM1 = logPos (point n1.M)
  oneM    = add (point SC) (neg MI)
  pI      = add (point SC) (neg (expNegBig DI))
  rhsLog  = add (mul (log 13 pI) (inv oneM)) (log 13 oneM)
  Sa      = add (fpt wa.F) (neg (mul (point wa.lam) (point wa.d)))  (Sb same)
  psiLo0  = add (fpt n0.F) (divNat (add (add lX (mul (point n0.lam) lM0))
                                        (mul (point n0.lam) lY)) 2)
  psiLo1  = add (fpt n1.F) (divNat (add (add lX (mul (point n1.lam) lM1))
                                        (mul (point n1.lam) lY)) 2)
  dip     = divNat (mul (add lM1 (neg lM0))
                        (add (point n1.lam) (neg (point n0.lam)))) 8
  logPos I     = add (log 13 (mulNat I 2^k)) (neg (mulNat log2I k)),
                 k = logShift I.hi (least k with SC <= hi * 2^k, fuel 64)
  logPosSafe I = logSafe 13 (mulNat I 2^k)
  expNegBig I  = pow (exp 16 (divNat (neg I) 16)) 16
  log2I        = log 13 (point (2*SC))

checkChain: head n0.lam = 10^8, consecutive full-Node equality, last n1.lam
= SC (the JSON stores one shared node list, so consecutive equality is
structural; it is asserted here anyway).  checkWitnesses: two-pointer
mergeAsc over nodes for the wa list (advance while node.lam < w.lam, then
require FULL node equality), mergeDesc against the reversed list for wb.
checkTail (T1): 0 < c0.X && logPosSafe (point c0.X) &&
0 < (add (add (fpt n0.F) (neg (mul (point n0.lam) (point n0.d))))
     (divNat (logPos (point c0.X)) 2)).lo.

Final value (Main2, DEVIATION from a bare `exp 16`): F_N/FS ~ 1.33 exceeds
the expSafe range, so exp(F_N/FS) is enclosed as (exp 16 (divNat (fpt F_N)
2))^2 -- Lean needs the one squaring lemma.

Usage: python3 verify_pq.py pq_cert.json
"""
import json
import sys

LEANPORT = "/Users/ssoh/conductor/workspaces/new-formalization/sao-paulo/bootstrap/leanport"
if LEANPORT not in sys.path:
    sys.path.insert(0, LEANPORT)

import fpi
from fpi import (scale as SC, point, add, neg, mul, inv, divNat, mulNat,
                 pow_, positive, expSafe, logSafe)
from funcs import flog, fexp, UnsafeOp, N_LOG, N_EXP

FS = 2 * SC * SC
L0 = 10**8  # lambda_0 * SC = 1e-4 * 1e12
KEXP = 16

LOG2I = flog(N_LOG, point(2 * SC))  # = Bootstrap.CertCheck.log2I


def fpt(f: int):
    """F-scale (FS) int -> SC-scale interval (Check.lean fpt; ediv = // for
    the positive divisor)."""
    q = 2 * SC
    return (f // q, -((-f) // q))


def logShift(h: int) -> int:
    """Least k >= 0 with SC <= h * 2^k (Lean logShiftAux, fuel 64)."""
    k = 0
    while k < 64 and (h << k) < SC:
        k += 1
    return k


def logPosSafe(I) -> bool:
    k = logShift(I[1])
    return logSafe(N_LOG, mulNat(I, 2 ** k))


def logPos(I):
    k = logShift(I[1])
    return add(flog(N_LOG, mulNat(I, 2 ** k)), neg(mulNat(LOG2I, k)))


def expNegBig(I):
    return pow_(fexp(N_EXP, divNat(neg(I), KEXP)), KEXP)


def rhs_log(d0: int, d1: int, Mlo: int, Mhi: int):
    """rhsLog over the cell box, with its safety conjuncts.

    Returns (rhsLog, safe: bool)."""
    DI = (d1, d0)
    MI = (Mlo, Mhi)
    oneM = add(point(SC), neg(MI))
    if not (expSafe(N_EXP, divNat(neg(DI), KEXP))):
        return None, False
    pI = add(point(SC), neg(expNegBig(DI)))
    if not (logSafe(N_LOG, pI) and logSafe(N_LOG, oneM)
            and positive(pI) and positive(oneM)):
        return None, False
    return add(mul(flog(N_LOG, pI), inv(oneM)), flog(N_LOG, oneM)), True


def check_cell(n0, n1, X, Y, wa, wb):
    """Mirror of Check.lean checkCellFast (two-endpoint PSI form).
    n0,n1,wa,wb are (lam,F,d,M) int 4-tuples.  Returns (ok, margins);
    margins are ints, pass iff >= 0 for XLE/A1/A2/B1/B2 and > 0 for
    INT/PSI0/PSI1."""
    m = {}
    l0, F0, d0, M0 = n0
    l1, F1, d1, M1 = n1

    # integer chain-local conditions + (P) + witness sanity (Check.lean order)
    ints_ok = (0 < l0 and l0 < l1
               and 0 < d1 and d1 <= d0
               and F1 == F0 + (d0 + d1) * (l1 - l0)
               and 0 < M0 and M0 < SC and 0 < M1 and M1 < SC
               and 0 < X and X < SC and 0 < Y and Y < SC
               and 0 < wa[0] and wa[0] <= SC and 0 < wa[2]
               and 0 < wb[0] and wb[0] <= SC and 0 < wb[2])
    m["INT"] = min(l0, l1 - l0, d1, d0 - d1 + 1,
                   1 if F1 == F0 + (d0 + d1) * (l1 - l0) else 0,
                   M0, SC - M0, M1, SC - M1, X, SC - X, Y, SC - Y,
                   wa[0], SC - wa[0] + 1, wa[2],
                   wb[0], SC - wb[0] + 1, wb[2])
    # (MMONO) sits between (B2) and (PSI0) in checkCell; evaluated here so the
    # M box (min/max in Lean, = (M0, M1) under MMONO) is definite below.
    m["MMONO"] = M1 - M0
    if not ints_ok or m["MMONO"] < 0:
        m["unsafe"] = "integer conjuncts"
        return False, m

    # safety predicates (Lean box is (min, max) = (n0.M, n1.M) under MMONO)
    if not (logPosSafe(point(X)) and logPosSafe(point(Y))
            and logPosSafe(point(M0)) and logPosSafe(point(M1))):
        m["unsafe"] = "logPosSafe"
        return False, m
    rhs, safe = rhs_log(d0, d1, M0, M1)
    if not safe:
        m["unsafe"] = "expSafe/logSafe/positive box"
        return False, m

    lX = logPos(point(X))
    lY = logPos(point(Y))
    lM0 = logPos(point(M0))
    lM1 = logPos(point(M1))
    Sa = add(fpt(wa[1]), neg(mul(point(wa[0]), point(wa[2]))))
    Sb = add(fpt(wb[1]), neg(mul(point(wb[0]), point(wb[2]))))
    psiLo0 = add(fpt(F0),
                 divNat(add(add(lX, mul(point(l0), lM0)),
                            mul(point(l0), lY)), 2))
    psiLo1 = add(fpt(F1),
                 divNat(add(add(lX, mul(point(l1), lM1)),
                            mul(point(l1), lY)), 2))
    dip = divNat(mul(add(lM1, neg(lM0)),
                     add(point(l1), neg(point(l0)))), 8)

    m["XLE"] = rhs[0] - lX[1]
    m["A1"] = -(add(Sa, lX)[1])
    m["A2"] = -(add(add(Sa, point(wa[2])), add(lX, lY))[1])
    m["B1"] = -(add(Sb, lY)[1])
    m["B2"] = -(add(add(Sb, point(wb[2])), add(lY, lX))[1])
    m["PSI0"] = add(psiLo0, neg(dip))[0]
    m["PSI1"] = add(psiLo1, neg(dip))[0]

    ok = (m["XLE"] >= 0 and m["A1"] >= 0 and m["A2"] >= 0
          and m["B1"] >= 0 and m["B2"] >= 0
          and m["PSI0"] > 0 and m["PSI1"] > 0)
    return ok, m


def check_chain(nodes):
    """checkChain: head lam = L0, last lam = SC.  Consecutive full-Node
    equality is structural for a shared node list."""
    errs = []
    if nodes[0][0] != L0:
        errs.append(f"first lam {nodes[0][0]} != L0 = {L0}")
    if nodes[-1][0] != SC:
        errs.append(f"last lam {nodes[-1][0]} != SC")
    return errs


def merge_asc(nodes, ws):
    """Check.lean mergeAsc: two-pointer, full node equality."""
    i = 0
    for w in ws:
        while i < len(nodes) and nodes[i][0] < w[0]:
            i += 1
        if i >= len(nodes) or nodes[i] != w:
            return False
    return True


def merge_desc(nodes_rev, ws):
    """Check.lean mergeDesc against the reversed node list."""
    i = 0
    for w in ws:
        while i < len(nodes_rev) and w[0] < nodes_rev[i][0]:
            i += 1
        if i >= len(nodes_rev) or nodes_rev[i] != w:
            return False
    return True


def check_witnesses(nodes, wa_list, wb_list):
    errs = []
    if not merge_asc(nodes, wa_list):
        errs.append("mergeAsc failed for wa list")
    if not merge_desc(list(reversed(nodes)), wb_list):
        errs.append("mergeDesc failed for wb list")
    return errs


def t1_value(nodes, X0: int):
    """checkTail: returns (margin, ok) -- 0 < X0, logPosSafe, and the
    interval lower bound."""
    l0, F0, d0, _ = nodes[0]
    if not (0 < X0 and logPosSafe(point(X0))):
        return None, False
    t = add(add(fpt(F0), neg(mul(point(l0), point(d0)))),
            divNat(logPos(point(X0)), 2))
    return t[0], t[0] > 0


def final_enclosure(FN: int):
    """Enclosure of exp(F_N/FS) as (exp 16 (divNat (fpt F_N) 2))^2
    (DEVIATION: F_N/FS > 1 exceeds expSafe, needs the squaring lemma)."""
    half = divNat(fpt(FN), 2)
    if not expSafe(N_EXP, half):
        raise UnsafeOp("expSafe final")
    E = fexp(N_EXP, half)
    return pow_(E, 2)


def verify(cert, verbose=True):
    nodes = [tuple(int(v) for v in nd) for nd in cert["nodes"]]
    X = [int(v) for v in cert["X"]]
    Y = [int(v) for v in cert["Y"]]
    wa_idx = [int(v) for v in cert["wa"]]
    wb_idx = [int(v) for v in cert["wb"]]
    ncells = len(nodes) - 1
    assert len(X) == len(Y) == len(wa_idx) == len(wb_idx) == ncells
    assert all(0 <= i < len(nodes) for i in wa_idx + wb_idx), "witness index"

    failures = []
    failures += [("chain", e) for e in check_chain(nodes)]
    failures += [("witness-merge", e) for e in
                 check_witnesses(nodes, [nodes[i] for i in wa_idx],
                                 [nodes[i] for i in wb_idx])]

    minm = {}   # name -> (margin, cell)
    for j in range(ncells):
        ok, m = check_cell(nodes[j], nodes[j + 1], X[j], Y[j],
                           nodes[wa_idx[j]], nodes[wb_idx[j]])
        if not ok:
            failures.append((f"cell {j}", str(m)))
        for k, v in m.items():
            if isinstance(v, int) and (k not in minm or v < minm[k][0]):
                minm[k] = (v, j)

    t1, t1ok = t1_value(nodes, X[0])
    if t1 is not None:
        minm["T1"] = (t1, 0)
    if not t1ok:
        failures.append(("T1", f"t1 = {t1}"))

    c_lo = c_hi = None
    try:
        cI = final_enclosure(nodes[-1][1])
        c_lo, c_hi = cI[0] / SC, cI[1] / SC
    except UnsafeOp as e:
        failures.append(("final", f"unsafe: {e}"))

    if verbose:
        print(f"cells: {ncells}   nodes: {len(nodes)}   "
              f"log depth {N_LOG}, exp depth {N_EXP}, SC={SC}, FS={FS}")
        print(f"{'check':>5} {'min margin (int)':>18} {'real (/SC)':>12}  at cell")
        for k in ("INT", "MMONO", "XLE", "A1", "A2", "B1", "B2",
                  "PSI0", "PSI1", "T1"):
            if k in minm:
                v, j = minm[k]
                need = (">=0" if k in ("MMONO", "XLE", "A1", "A2", "B1", "B2")
                        else ">0")
                print(f"{k:>5} {v:>18} {v / SC:>12.3e}  {j}   (need {need})")
        if c_hi is not None:
            import math
            print(f"F_N/FS = {nodes[-1][1] / FS:.10f}   "
                  f"float exp = {math.exp(nodes[-1][1] / FS):.10f}")
            print(f"certified enclosure of c = exp(F(1)): "
                  f"[{c_lo:.10f}, {c_hi:.10f}]")
            print(f"CERTIFIED UPPER BOUND  c <= {c_hi:.10f}")
        if failures:
            print(f"*** {len(failures)} FAILURE(S):")
            for where, what in failures[:50]:
                print(f"  [{where}] {what}")
        else:
            print("ALL CHECKS PASSED")
    return len(failures) == 0, minm, c_hi, failures


if __name__ == "__main__":
    with open(sys.argv[1]) as fh:
        cert = json.load(fh)
    ok, _, _, _ = verify(cert)
    sys.exit(0 if ok else 1)
