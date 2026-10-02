#!/usr/bin/env python3
"""Audit r4 (adversarial): exactly certify (or refute) a float record of `t4d_immodest_search.py`
-- an IMMODEST, FULL-SUPPORT candidate counterexample to fn 65's weak reading at three cells.

usage: python3 t4d_immodest_certify.py rec_immodest_seed<N>.npz

Steps: rationalise the types (grid 1/DEN, zero coordinates kept exactly, each row renormalised
exactly) and the menu (grid 1/MDEN); check the types are not all collinear (the pair-line system
is complete only then); re-solve the LP at the rational types with the immodest full-support
bounds (m[t,c] >= EPS on supp p_t, = 0 off it) and a safety margin; round the masses to a rational
grid keeping the zero pattern; verify EXACTLY with Fractions: every constraint of the finite
pair-line system (audit r3's `exact_check`), the unique argmax at every type, the Value slack of
the forced strategy, the immodest pattern m[t,c] > 0 <=> p_t(c) > 0, and -- independently of the
pair-line argument -- local Total Trust over every integer direction in {-4..4}^3 at every
attained threshold +- eps.  Register: exact rational arithmetic, not Lean.
"""
import sys, os, json, itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, "..", "audit-r3-probes", "t4d_exact.py")).read().split("def main():")[0]
_argv = sys.argv; sys.argv = ["x", "0", "50"]; exec(_src); sys.argv = _argv  # classes, exact_check

DEN, MDEN, EPS = 200, 100, Fr(1, 100)


def lp_immodest(Pf, menu, j, margin):
    n = len(Pf)
    cls = classes(Pf)
    A, b = [], []
    for (x, s, K) in cls:
        row = np.zeros((n, 3))
        for t in K:
            row[t, :] = -(x - s)
        A.append(row.reshape(-1)); b.append(-margin * np.linalg.norm(x - s) if K else 0.0)
    scores = Pf @ menu.T
    best = scores.argmax(axis=1)
    srt = np.sort(scores, axis=1)
    if np.any(srt[:, -1] - srt[:, -2] < 1e-9) or len(set(best)) < 3:
        return None
    c = np.zeros((n, 3))
    for t in range(n):
        c[t, :] = menu[best[t]] - menu[j]
    bounds = [((float(EPS), None) if Pf[t, k] > 1e-12 else (0.0, 0.0)) for t in range(n) for k in range(3)]
    res = linprog(c.reshape(-1), A_ub=np.array(A), b_ub=np.array(b),
                  A_eq=np.ones((1, 3 * n)), b_eq=[1.0], bounds=bounds, method="highs")
    if res.status != 0:
        return None
    return res.fun, res.x.reshape(n, 3), best


def grid_check(Pq, mq):
    n = len(Pq); worst = Fr(0); cnt = 0
    for x in itertools.product(range(-4, 5), repeat=3):
        x = [Fr(v) for v in x]
        ex = [sum(x[i] * Pq[t][i] for i in range(3)) for t in range(n)]
        for s0 in set(ex):
            for s in (s0, s0 - Fr(1, 10**9), s0 + Fr(1, 10**9)):
                K = [t for t in range(n) if ex[t] >= s]
                g = sum(mq[t][c] * (x[c] - s) for t in K for c in range(3)); cnt += 1
                worst = min(worst, g)
    return cnt, worst


def main():
    rec = np.load(sys.argv[1])
    P0, menu0, j = rec["P"], rec["menu"], int(rec["j"])
    n = len(P0)
    # rational types: round positive coordinates to the grid, renormalise each row exactly
    Pq = []
    for t in range(n):
        row = [Fr(int(round(P0[t][c] * DEN)), DEN) if P0[t][c] > 1e-12 else Fr(0) for c in range(3)]
        tot = sum(row)
        Pq.append([v / tot for v in row])
    Pf = np.array([[float(v) for v in p] for p in Pq])
    rank = np.linalg.matrix_rank(np.c_[Pf, np.ones(n)], tol=1e-9)
    print("types (rational):"); [print("  t%d:" % t, [str(v) for v in Pq[t]]) for t in range(n)]
    print("rank of [p_t, 1]:", rank, "(3 needed for the pair-line system to be complete)")
    if rank < 3:
        print("all types collinear: the pair-line LP is under-constrained; refusing to certify"); return
    menuq = [[Fr(int(round(menu0[o][c] * MDEN)), MDEN) for c in range(3)] for o in range(3)]
    menu = np.array([[float(v) for v in r_] for r_ in menuq])
    cert = None
    for margin in (1e-2, 5e-3, 2e-3, 1e-3, 5e-4, 2e-4, 0.0):
        r = lp_immodest(Pf, menu, j, margin)
        if r is None:
            print(f"margin {margin}: LP infeasible or tie/unused option"); continue
        val, m, best = r
        print(f"margin {margin}: float optimum {val:.6f}")
        if val >= 0:
            continue
        for MD in (100, 1000, 10000, 100000, 1000000):
            mq = [[(Fr(int(round(m[t][c] * MD)), MD) if Pq[t][c] > 0 else Fr(0)) for c in range(3)] for t in range(n)]
            tot = sum(sum(r_) for r_ in mq)
            mq = [[v / tot for v in r_] for r_ in mq]
            pattern_ok = all((mq[t][c] > 0) == (Pq[t][c] > 0) for t in range(n) for c in range(3))
            ok, worst_c, slack = exact_check(Pq, mq, menuq, list(best), j)
            print(f"  MD {MD}: pair-system exact TT {ok} (min {worst_c}), pattern {pattern_ok}, slack {slack}")
            if ok and pattern_ok and slack is not None and slack < 0:
                cert = (margin, MD, mq, list(map(int, best)), slack); break
        if cert is not None:
            break
    if cert is None:
        print("NOT CERTIFIED: no rounding of the LP solution at the rational types passes the exact checks"); return
    margin, MD, mq, best, slack = cert
    cnt, worst = grid_check(Pq, mq)
    print(f"CERTIFIED (margin {margin}, mass grid 1/{MD}): exact pair-system TT ok, immodest full-support pattern ok, slack {slack} = {float(slack):.6f}")
    print("independent exact grid check: directions {-4..4}^3, all attained thresholds +-eps:", cnt, "checks, worst", worst)
    print("menu x_o:"); [print("  o%d:" % o, [str(v) for v in menuq[o]]) for o in range(3)]
    print("best option per type:", best, " j =", j)
    print("masses m[t,c]:"); [print("  t%d:" % t, [str(v) for v in mq[t]]) for t in range(n)]
    print("worlds with positive mass:", sum(1 for t in range(n) for c in range(3) if mq[t][c] > 0),
          "; cell marginal:", [str(sum(mq[t][c] for t in range(n))) for c in range(3)])
    out = os.path.join(HERE, os.path.basename(sys.argv[1]).replace(".npz", "_certificate.json"))
    json.dump({"types": [[str(v) for v in p] for p in Pq], "menu": [[str(v) for v in r_] for r_ in menuq],
               "j": j, "best": best, "m": [[str(v) for v in r_] for r_ in mq],
               "slack": str(slack), "grid_check_worst": str(worst), "margin": margin}, open(out, "w"), indent=1)
    print("written", out)


main()
