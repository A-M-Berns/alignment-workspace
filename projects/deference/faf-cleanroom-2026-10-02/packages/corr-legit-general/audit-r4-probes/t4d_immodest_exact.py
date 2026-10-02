#!/usr/bin/env python3
"""Audit r4 (adversarial): rationalise and EXACTLY verify an immodest, full-support three-cell
counterexample to fn 65's weak reading (the repair hypothesis the handoff does not consider).

Types on a rational grid with random supports (full / two cells / Dirac); LP with the immodest
full-support bounds (m[t,c] >= eps on supp p_t, = 0 off it) and a safety margin on every
local-Total-Trust constraint; masses rounded to rationals (zeros kept); then exact verification
with Fractions of (i) every constraint of the finite local-Total-Trust system (pair-lines x signs
x on-line subsets, as audit r3's `t4d_exact.py`, whose `classes`/`lp`/`exact_check` are reused),
(ii) the Value slack of the forced recommended strategy, (iii) the immodesty/full-support pattern
m[t,c] > 0 <=> p_t(c) > 0, and (iv) an independent exact check over integer directions in
{-4..4}^3 at every attained threshold +- eps (as audit r3's `certify.py`).

Realisation as a frame: one world (t, c) per pair with m[t,c] > 0; pi(t,c) = m[t,c] > 0 (full
support); row of type t: P_t((t,c')) = p_t(c') on t's own worlds, 0 elsewhere -- supported on its
self-cell, so every expert is immodest; pushforward Q_* P_t = p_t.

Register: exact rational arithmetic, not Lean.
"""
import sys, os, json, itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "audit-r3-probes"))
_src = open(os.path.join(HERE, "..", "audit-r3-probes", "t4d_exact.py")).read().split("def main():")[0]
_argv = sys.argv; sys.argv = ["x", "0", "50"]; exec(_src); sys.argv = _argv  # classes, exact_check

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 120
NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 6
DEN, MDEN, EPS = 20, 4, Fr(1, 100)


def sample_types(n):
    P = []
    while len(P) < n:
        u = rng.uniform()
        if u < 0.5:
            a, b = rng.integers(1, DEN - 1, size=2)
            if a + b >= DEN:
                continue
            p = (Fr(int(a), DEN), Fr(int(b), DEN), Fr(int(DEN - a - b), DEN))
        elif u < 0.85:
            i, k = sorted(rng.choice(3, size=2, replace=False).tolist())
            a = int(rng.integers(1, DEN))
            p = [Fr(0)] * 3; p[i] = Fr(a, DEN); p[k] = Fr(DEN - a, DEN); p = tuple(p)
        else:
            i = int(rng.integers(3)); p = [Fr(0)] * 3; p[i] = Fr(1); p = tuple(p)
        if p not in P:
            P.append(p)
    return P


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
    if np.any(srt[:, -1] - srt[:, -2] < 1e-6) or len(set(best)) < 3:
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
    best_rec = None
    for trial in range(TRIALS):
        n = int(rng.integers(3, NMAX + 1))
        Pq = sample_types(n)
        Pf = np.array([[float(v) for v in p] for p in Pq])
        # collinearity guard: the pair-line system is complete only for non-collinear types
        # (see t4d_immodest_search.py); the exact grid check below is independent of it anyway
        if np.linalg.matrix_rank(np.c_[Pf, np.ones(n)], tol=1e-9) < 3:
            continue
        for _ in range(30):
            menu = np.round(rng.normal(size=(3, 3)) * MDEN) / MDEN
            for j in range(3):
                r = lp_immodest(Pf, menu, j, 2e-3)
                if r is None:
                    continue
                val, m, best = r
                if best_rec is None or val < best_rec[0]:
                    best_rec = (val, Pq, menu, j, m, best, n)
    if best_rec is None or best_rec[0] >= 0:
        print("no immodest full-support violation found with margin; best:", None if best_rec is None else best_rec[0]); return
    val, Pq, menu, j, m, best, n = best_rec
    print("float optimum with margin 2e-3:", val, "types:", n)
    menuq = [[Fr(int(round(menu[o][c] * MDEN)), MDEN) for c in range(3)] for o in range(3)]
    cert = None
    for MD in (50, 100, 200, 500, 1000, 10000, 100000):
        mq = [[(Fr(int(round(m[t][c] * MD)), MD) if Pq[t][c] > 0 else Fr(0)) for c in range(3)] for t in range(n)]
        tot = sum(sum(r_) for r_ in mq)
        mq = [[v / tot for v in r_] for r_ in mq]
        pattern_ok = all((mq[t][c] > 0) == (Pq[t][c] > 0) for t in range(n) for c in range(3))
        ok, worst_c, slack = exact_check([list(p) for p in Pq], mq, menuq, list(best), j)
        if ok and pattern_ok and slack < 0:
            cert = (MD, mq, slack); print(f"MD {MD}: exact TT ok (min constraint {worst_c}), immodest pattern ok, slack {slack} = {float(slack):.6f}"); break
        print(f"MD {MD}: TT {ok} pattern {pattern_ok} slack {slack}")
    if cert is None:
        print("rounding failed to certify"); return
    MD, mq, slack = cert
    cnt, worst = grid_check([list(p) for p in Pq], mq)
    print("independent exact grid check: directions {-4..4}^3, all attained thresholds +-eps:", cnt, "checks, worst", worst)
    print("types p_t:"); [print("  t%d:" % t, [str(v) for v in Pq[t]]) for t in range(n)]
    print("menu x_o:"); [print("  o%d:" % o, [str(v) for v in menuq[o]]) for o in range(3)]
    print("best option per type:", list(map(int, best)), " j =", j)
    print("masses m[t,c]:"); [print("  t%d:" % t, [str(v) for v in mq[t]]) for t in range(n)]
    print("worlds with positive mass:", sum(1 for t in range(n) for c in range(3) if mq[t][c] > 0))
    json.dump({"types": [[str(v) for v in p] for p in Pq], "menu": [[str(v) for v in r_] for r_ in menuq],
               "j": j, "best": list(map(int, best)), "m": [[str(v) for v in r_] for r_ in mq],
               "slack": str(slack), "grid_check_worst": str(worst)},
              open(os.path.join(HERE, "t4d_immodest_certificate.json"), "w"), indent=1)


main()
