#!/usr/bin/env python3
"""pq_export.py -- convert a converged opt2.py fixed point (cert_strict_*.npz)
into a C1 piecewise-quadratic spline certificate per Bootstrap2/SPEC.md
(rev. 2026-09-02: two-endpoint PSI check with dip term, M non-decreasing).

Pipeline (floats only for search/selection; every emitted inequality is
re-validated through the fpi interval mirror imported from verify_pq):

 1. nodal derivatives d_j from the PL slopes (midpoints + half-step endpoint
    extrapolation), rounded to Int*SC, clipped to positive non-increasing;
    lam_j = round(lam*SC) (first = 1e8, last = 1e12 exactly); nodal M_j like
    d, then made non-decreasing by PAV isotonic regression (new chain
    requirement n0.M <= n1.M; the fixed point's M dips only near lam = 1 by
    ~1e-5 per step, so the correction is tiny);
 2. OPTIONAL adaptive subdivision (extra nodes ON the same PL D; exact chain
    preserved): with the two-endpoint PSI the old width loss is gone; the
    remaining per-cell losses (witness quantization, XLE box freeze) shrink
    linearly with the mesh, so a target > 0 subdivides by the legacy width
    criterion when the base mesh is too coarse;
 3. XLE bound per cell: rhsLog over the box via fpi -> hard floor for -log X;
 4. witness selection + slack assignment.  All fixed-point constraints BIND,
    so X_j, Y_j are re-derived from the chosen tangent witnesses: with
    p = -log X, q = -log Y, Sbar(u) = F(u) - u d(u), Sd = Sbar + d,
        p   >= max(Sbar(u_a) + mA, pXLE)      (A1, XLE)
        q   >= Sbar(u_b) + mB                 (B1)
        p+q >= max(Sd(u_a), Sd(u_b)) + mS     (A2, B2), deficit added to q
    (q is the cheaper PSI direction: weight lam <= 1).  Witnesses are chosen
    per cell by coordinate descent minimizing the PSI cost p + lam1 q under
    running monotone bounds (wa up, wb down);
 5. uniform F-shift: F_0 = round(F[0]*FS) + bump, raised until PSI0/PSI1 >=
    mPSI on every cell and T1 >= mT1.  Chain increments are F-independent, so
    the shift is exactly uniform and preserves the chain identity;
 6. X_j = floor(SC exp(-p_j)), Y_j = floor(SC exp(-q_j)) (round DOWN = safe
    direction for A/B/XLE), then a per-cell interval-checked fix-up shrink;
 7. full fpi verification of every cell + chain + merge + T1 before writing.

Usage: python3 pq_export.py cert.npz out.json [subdiv_target|0]
"""
import json
import math
import sys
import time

import numpy as np

import verify_pq as V
from verify_pq import SC, FS, fpt, rhs_log, check_cell, UnsafeOp

# margins (real units).  Interval slop is ~5e-11 and float/int discretization
# ~2e-9, so 1e-6 dominates them comfortably.
MA = 6.0e-7     # A1 margin (also floor for p beyond XLE)
MB = 6.0e-7     # B1 margin
MS = 6.0e-7     # A2/B2 (sum) margin
MPSI = 1.0e-6   # PSI0/PSI1: (psiLo - dip).lo >= MPSI*SC (final-margin target)
MT1 = 1.2e-6    # T1 target margin (task requires >= 1e-6)
XLE_GUARD = 1.0e-9   # p floor above the interval rhsLog.lo
TIE = 1e-9      # witness tie-breaking tolerance (prefers monotone freedom)


def nodal_from_intervals(v):
    """per-interval array (len N) -> nodal (len N+1): midpoints + half-step
    endpoint extrapolation."""
    v = np.asarray(v, dtype=float)
    out = np.empty(len(v) + 1)
    out[1:-1] = 0.5 * (v[:-1] + v[1:])
    out[0] = v[0] + 0.5 * (v[0] - v[1])
    out[-1] = v[-1] - 0.5 * (v[-2] - v[-1])
    return out


def smooth_local_quadratic(lam, y, half=20):
    """De-noise y(lam) by a least-squares local quadratic fit over a +-half
    node window (handles the non-uniform geo grid).  The npz M carries
    ~1e-4 golden-section jitter that would otherwise feed straight into the
    XLE box / psi trade-off."""
    n = len(y)
    out = np.empty(n)
    llam, ly = np.log(lam), np.log(y)   # log-log: uniform RELATIVE residual
    for i in range(n):
        a, b = max(0, i - half), min(n, i + half + 1)
        t = llam[a:b] - llam[i]
        out[i] = math.exp(np.polynomial.polynomial.polyfit(t, ly[a:b], 2)[0])
    return out


def pav_isotonic(y):
    """Pool-adjacent-violators: least-squares non-decreasing fit (equal
    weights).  y is nearly monotone; the correction is minimal."""
    vals, cnts = [], []
    for v in map(float, y):
        vals.append(v)
        cnts.append(1)
        while len(vals) > 1 and vals[-2] > vals[-1]:
            v2 = vals[-2] * cnts[-2] + vals[-1] * cnts[-1]
            c2 = cnts[-2] + cnts[-1]
            vals[-2:] = [v2 / c2]
            cnts[-2:] = [c2]
    out = []
    for v, c in zip(vals, cnts):
        out.extend([v] * c)
    return np.array(out)


def build_chain(F0_int, d_int, lam_int):
    F = [F0_int]
    for j in range(len(lam_int) - 1):
        F.append(F[-1] + (d_int[j] + d_int[j + 1]) * (lam_int[j + 1] - lam_int[j]))
    return F


def subdivide(lam_int, d_int, M_int, wloss, target):
    """Split base cell j into ceil(wloss[j]/target) equal parts; d and M are
    PL-interpolated (in exact int arithmetic on the segment) and rounded."""
    L, D, M = [lam_int[0]], [d_int[0]], [M_int[0]]
    for j in range(len(lam_int) - 1):
        k = max(1, math.ceil(wloss[j] / target))
        l0, l1 = lam_int[j], lam_int[j + 1]
        d0, d1 = d_int[j], d_int[j + 1]
        m0, m1 = M_int[j], M_int[j + 1]
        for i in range(1, k):
            li = l0 + ((l1 - l0) * i) // k
            D.append(d0 + ((d1 - d0) * (li - l0) * 2 + (l1 - l0)) // (2 * (l1 - l0)))
            M.append(m0 + ((m1 - m0) * (li - l0) * 2 + (l1 - l0)) // (2 * (l1 - l0)))
            L.append(li)
        L.append(l1)
        D.append(d1)
        M.append(m1)
    # re-enforce monotonicity (rounding can flip by 1 ulp)
    for j in range(1, len(D)):
        if D[j] > D[j - 1]:
            D[j] = D[j - 1]
        if M[j] < M[j - 1]:
            M[j] = M[j - 1]
    assert D[-1] > 0
    assert all(a < b for a, b in zip(L, L[1:]))
    return L, D, M


def select_witnesses(Sbar, Sd, lam1f, pfloor, headroom=0.0):
    """Monotone per-cell witness selection minimizing PSI cost p + lam1*q.

    headroom: cell 0's witness is forced to satisfy Sbar + mA + headroom <=
    pfloor_0, so that p_0 stays pinned at the XLE floor under the final
    F-bump and (T1) gets the bump at full rate (cost: q_0 rises by
    ~|Sd'|*delta_u, entering psi_0 with weight lam_0/2 ~ 5e-5)."""
    ncells = len(lam1f)
    N = len(Sbar) - 1
    ua = np.empty(ncells, dtype=int)
    ub = np.empty(ncells, dtype=int)
    lo_a, hi_b = 0, N
    ib = N  # warm start for orientation b
    for j in range(ncells):
        lam1 = lam1f[j]
        pfl = pfloor[j]
        pa = np.maximum(Sbar[lo_a:] + MA, pfl)
        sum_a = Sd[lo_a:] + MS
        qb_cur = Sbar[min(ib, hi_b)] + MB
        sumb_cur = Sd[min(ib, hi_b)] + MS
        ia = lo_a
        for _ in range(3):
            qcand = np.maximum(qb_cur, np.maximum(sum_a, sumb_cur) - pa)
            J = pa + lam1 * qcand
            jmin = J.min()
            ia = lo_a + int(np.argmax(J <= jmin + TIE))   # first near-min
            p = pa[ia - lo_a]
            suma = Sd[ia] + MS
            qneed = np.maximum(Sbar[:hi_b + 1] + MB,
                               np.maximum(Sd[:hi_b + 1] + MS, suma) - p)
            qmin = qneed.min()
            ib = hi_b - int(np.argmax(qneed[::-1] <= qmin + TIE))  # last near-min
            qb_cur = Sbar[ib] + MB
            sumb_cur = Sd[ib] + MS
        ua[j], ub[j] = ia, ib
        lo_a, hi_b = ia, ib
    # T1 decoupling (see docstring): largest node keeping p_0 XLE-pinned.
    ok0 = np.nonzero(Sbar + MA + headroom <= pfloor[0])[0]
    ua[0] = min(int(ok0[-1]) if len(ok0) else 0, int(ua[1]) if len(ua) > 1 else 0)
    return ua, ub


def pq_from_witnesses(Sbar, Sd, ua, ub, pfloor):
    p = np.maximum(Sbar[ua] + MA, pfloor)
    q = np.maximum(Sbar[ub] + MB, np.maximum(Sd[ua], Sd[ub]) + MS - p)
    return p, q


def export(npz_path, json_path, subdiv_t=0.0):
    z = np.load(npz_path)
    lam, F, S, M = z["lam"], z["F"], z["S"], z["M"]
    Nbase = len(lam) - 1
    print(f"[export] {npz_path}: {Nbase} base cells, float c = {math.exp(F[-1]):.8f}")

    # --- 1: integer base nodes ------------------------------------------------
    lam_int = [int(round(v * SC)) for v in lam]
    assert lam_int[0] == 10**8 and lam_int[-1] == SC, "lam endpoints"
    assert all(a < b for a, b in zip(lam_int, lam_int[1:])), "lam not increasing"

    d_nod = nodal_from_intervals(S)
    d_int = [int(round(v * SC)) for v in d_nod]
    for j in range(1, Nbase + 1):                    # enforce non-increasing
        if d_int[j] > d_int[j - 1]:
            d_int[j] = d_int[j - 1]
    assert d_int[-1] > 0, "d positivity"

    M_nod = nodal_from_intervals(M)
    M_smooth = smooth_local_quadratic(np.asarray(lam, dtype=float), M_nod)
    M_iso = pav_isotonic(M_smooth)
    print(f"[export] M smoothing: max {np.abs(M_smooth - M_nod).max():.2e}, "
          f"isotonic correction: max {np.abs(M_iso - M_smooth).max():.2e}")
    M_int = [int(round(v * SC)) for v in M_iso]
    for j in range(1, Nbase + 1):                    # enforce non-decreasing
        if M_int[j] < M_int[j - 1]:
            M_int[j] = M_int[j - 1]
    assert 0 < M_int[0] and M_int[-1] < SC, "M range"

    # --- 2: optional subdivision ----------------------------------------------
    # Per-cell deficit model (two-endpoint PSI): the dominant loss is the XLE
    # box-corner freeze  psi-hit ~ [sens_D*(d0-d1) + sens_M*(M1-M0)]/4  (X_j
    # must clear rhs at the worst corner (d1, M1) while the optimizer's X was
    # priced at mid-cell), plus a witness-granularity floor ~ 0.08*dlam.
    # Subdividing k ways divides both (d and M are PL on the cell).
    if subdiv_t > 0:
        dd = np.array([(d_int[j] - d_int[j + 1]) / SC for j in range(Nbase)])
        dM = np.array([(M_int[j + 1] - M_int[j]) / SC for j in range(Nbase)])
        dlam = np.diff(np.array([v / SC for v in lam_int]))
        Dmid = np.array([(d_int[j] + d_int[j + 1]) / (2 * SC) for j in range(Nbase)])
        Mmid = np.array([(M_int[j] + M_int[j + 1]) / (2 * SC) for j in range(Nbase)])
        eD = np.exp(-Dmid)
        pI = 1.0 - eD
        oneM = 1.0 - Mmid
        sensD = eD / (pI * oneM)
        sensM = -np.log(pI) / oneM**2 + 1.0 / oneM
        est = (sensD * dd + sensM * dM) / 4.0
        # witness-service term: a cell at u hosts the a-witness of the cell
        # lamA with -log Y(lamA) = D(u) (tangency) and the b-witness of the
        # cell lamB with -log X(lamB) = D(u); their psi pays
        # ~lam_served * |Sd'| * dlam / 2 (worst node placement) per unit.
        lmid = np.array([(lam_int[j] + lam_int[j + 1]) / (2 * SC)
                         for j in range(Nbase)])
        negY = -np.log(z["Y"])          # decreasing in lam
        negX = -np.log(z["X"])          # increasing in lam
        lamA = np.interp(Dmid, negY[::-1], lmid[::-1])
        lamB = np.where(Dmid <= negX[-1], np.interp(Dmid, negX, lmid), 0.0)
        absDp = dd / dlam
        est = est + (lamA * (1 - lmid) + lamB * lmid) * absDp * dlam / 2.0
        lam_int, d_int, M_int = subdivide(lam_int, d_int, M_int, est, subdiv_t)
    N = len(lam_int) - 1
    print(f"[export] cells: {Nbase} -> {N} (subdiv target "
          f"{subdiv_t if subdiv_t > 0 else 'off'})")

    # --- 3: XLE floors via the fpi box ---------------------------------------
    t0 = time.time()
    pfloor = np.empty(N)
    for j in range(N):
        rhs, safe = rhs_log(d_int[j], d_int[j + 1], M_int[j], M_int[j + 1])
        assert safe, f"box safety predicates fail at cell {j}"
        pfloor[j] = -rhs[0] / SC + XLE_GUARD
    print(f"[export] XLE floors computed in {time.time() - t0:.1f}s "
          f"(max -logX floor {pfloor.max():.6f})")

    lamf = np.array([v / SC for v in lam_int])
    df = np.array([v / SC for v in d_int])
    lam0f, lam1f = lamf[:-1], lamf[1:]
    mM = -np.log(np.array([v / SC for v in M_int]))   # -log M at nodes
    mM0, mM1 = mM[:-1], mM[1:]
    dipf = (mM0 - mM1) * (lam1f - lam0f) / 8.0        # >= 0 (M non-decreasing)

    # --- 4..5: witness selection + F bump fixed point -------------------------
    # chain increments are F-independent: a bump of F_0 shifts every F_j by
    # exactly the same amount, so the chain is built once.
    F0_base = int(round(F[0] * FS))
    F_base = build_chain(F0_base, d_int, lam_int)
    Ff0 = np.array([v / FS for v in F_base])
    def margins_at(b, ua, ub):
        """min slack of (PSI0, PSI1, T1) over all cells at bump b, plus the
        psi arrays (fixed witnesses).  Monotone non-decreasing in b."""
        Sbar = (Ff0 + b) - lamf * df
        Sd = Sbar + df
        p, q = pq_from_witnesses(Sbar, Sd, ua, ub, pfloor)
        psi0 = (Ff0[:-1] + b) - 0.5 * (p + lam0f * (mM0 + q)) - dipf
        psi1 = (Ff0[1:] + b) - 0.5 * (p + lam1f * (mM1 + q)) - dipf
        t1 = Ff0[0] + b - lamf[0] * df[0] - 0.5 * p[0]
        slack = min(float((psi0 - MPSI).min()), float((psi1 - MPSI).min()),
                    t1 - MT1)
        return slack, psi0, psi1, t1, p, q

    bump = 0.0
    ua = ub = None
    for outer in range(8):
        Sbar = (Ff0 + bump) - lamf * df
        Sd = Sbar + df
        t0 = time.time()
        # Sbar already includes the current bump; headroom covers the
        # remaining growth (cost ~0.08/unit in psi_0).
        ua, ub = select_witnesses(Sbar, Sd, lam1f, pfloor, headroom=6e-5)
        # minimal feasible bump for these witnesses (slacks are monotone
        # non-decreasing in the bump: psi slope >= (1-lam)/2 with the binding
        # branch structure, and >= 1/2 wherever p or q is not Sbar-bound)
        hi = max(bump, 1e-5)
        while margins_at(hi, ua, ub)[0] < 0:
            hi *= 2
            assert hi < 1e-2, "bump diverging"
        lo = 0.0
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if margins_at(mid, ua, ub)[0] >= 0:
                hi = mid
            else:
                lo = mid
        bump_new = hi
        _, psi0, psi1, t1, p, q = margins_at(bump_new, ua, ub)
        j0, j1 = int(np.argmin(psi0)), int(np.argmin(psi1))
        print(f"[export] outer {outer}: bump = {bump_new:.4e} "
              f"(select {time.time() - t0:.1f}s, t1 {t1:.3e}; "
              f"psi0 min {psi0[j0]:.2e} @cell {j0} lam={lam0f[j0]:.4f}, "
              f"psi1 min {psi1[j1]:.2e} @cell {j1} lam={lam1f[j1]:.4f})")
        done = abs(bump_new - bump) < 1e-10
        bump = bump_new
        if done:
            break

    bump_int = math.ceil(bump * FS)
    F_int = [v + bump_int for v in F_base]

    # --- 6: integerize X, Y ---------------------------------------------------
    X_int = [max(1, int(math.floor(SC * math.exp(-v)))) for v in p]
    Y_int = [max(1, int(math.floor(SC * math.exp(-v)))) for v in q]

    nodes = [(lam_int[j], F_int[j], d_int[j], M_int[j]) for j in range(N + 1)]

    # --- fix-up + full verification ------------------------------------------
    t0 = time.time()
    nshrunk = 0
    minm = {}
    for j in range(N):
        for attempt in range(12):
            ok, m = check_cell(nodes[j], nodes[j + 1], X_int[j], Y_int[j],
                               nodes[ua[j]], nodes[ub[j]])
            if ok:
                break
            fixed = False
            for key, var in (("XLE", "X"), ("A1", "X"), ("A2", "Y"),
                             ("B1", "Y"), ("B2", "Y")):
                if key in m and m[key] < 0:
                    short = (-m[key] + 50) / SC
                    if var == "X":
                        X_int[j] = max(1, int(X_int[j] * math.exp(-short)) - 1)
                    else:
                        Y_int[j] = max(1, int(Y_int[j] * math.exp(-short)) - 1)
                    fixed = True
            nshrunk += 1
            if not fixed:
                raise RuntimeError(
                    f"cell {j} fails structurally (not fixable by X/Y shrink): {m}")
        else:
            raise RuntimeError(f"cell {j} still failing after shrinks: {m}")
        for k, v in m.items():
            if isinstance(v, int) and (k not in minm or v < minm[k][0]):
                minm[k] = (v, j)
    print(f"[export] per-cell fpi validation in {time.time() - t0:.1f}s, "
          f"{nshrunk} fix-up shrinks")

    # --- write ---------------------------------------------------------------
    cert = {
        "meta": {
            "source": npz_path,
            "SC": SC, "FS": FS,
            "cells": N,
            "base_cells": Nbase,
            "subdiv_target": subdiv_t,
            "margins": {"mA": MA, "mB": MB, "mS": MS, "mPSI": MPSI, "mT1": MT1},
            "F0_base": F0_base,
            "F0_bump": bump_int,
            "F0_bump_real": bump_int / FS,
            "c_float": math.exp(F_int[-1] / FS),
            "psi_form": "two-endpoint psiLo0/psiLo1 with dip (SPEC rev 2026-09-02)",
            "final_exp_note": "exp(F_N/FS) enclosed as (exp 16 (fpt F_N / 2))^2",
        },
        "nodes": [[str(v) for v in nd] for nd in nodes],
        "X": [str(v) for v in X_int],
        "Y": [str(v) for v in Y_int],
        "wa": [int(v) for v in ua],
        "wb": [int(v) for v in ub],
    }
    with open(json_path, "w") as fh:
        json.dump(cert, fh)
    print(f"[export] wrote {json_path}")
    print(f"[export] F_0 bump = {bump_int} ({bump_int / FS:.4e} real); "
          f"c_float = {math.exp(F_int[-1] / FS):.8f}")
    print(f"[export] wa range {ua.min()}..{ua.max()}, wb range {ub.min()}..{ub.max()}")
    return cert


if __name__ == "__main__":
    npz = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else "pq_cert.json"
    t = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
    export(npz, out, t)
