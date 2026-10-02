#!/usr/bin/env python3
"""Audit r4 (adversarial) probe for corr-legit-general T4(d): does the three-cell refutation of
fn 65 survive the obvious repair hypothesis -- IMMODEST (clear) experts with a FULL-SUPPORT
deferrer?

Why this matters. The refuting frame F7 is modest (every type gives positive probability to
cells it does not occupy), and immodesty is the standing assumption of Managing Misalignment and
of the package's own T8. With pi-null worlds allowed, immodesty is no repair at all: pad F7 with a
pi-null world (t, c) for every (type, cell) pair with m[t, c] = 0 and give type t the row
P_t((t, c')) = p_t(c'), supported on t's own worlds; both predicates ignore pi-null worlds and the
forced strategy is unchanged.  The meaningful question is therefore immodesty WITH full support:
every type occupies exactly the cells in its support, each with positive mass.

In the type-space LP of audit r3 (`../audit-r3-probes/t4d_lp_search.py`, reused) that is the
constraint set  m[t, c] >= eps for c in supp p_t,  m[t, c] = 0 otherwise.  Types are sampled with
random supports (full, two cells, one cell = a Dirac type).  A negative optimum is an immodest,
full-support counterexample (one world per (t, c) with c in supp p_t; row p_t spread on t's own
worlds).

Register: numerical (SciPy HiGHS), not certified; if a violation is found it is reported with
its data for exact certification.
"""
import sys, os, itertools, numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "audit-r3-probes"))
from t4d_lp_search import tt_constraints, value_objective  # noqa: E402

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
EPS = float(sys.argv[3]) if len(sys.argv) > 3 else 0.01


def sample_types(n, C):
    """n types in Delta(C) with random supports: full (p 0.5), two cells (0.35), Dirac (0.15)."""
    P = np.zeros((n, C))
    for t in range(n):
        u = rng.uniform()
        if u < 0.5:
            supp = list(range(C))
        elif u < 0.85:
            supp = sorted(rng.choice(C, size=2, replace=False).tolist())
        else:
            supp = [int(rng.integers(C))]
        P[t, supp] = rng.dirichlet(np.ones(len(supp)) * rng.uniform(0.3, 2.0))
    return P


def search(C, ntypes_range, trials, nmenu, eps):
    worst = 0.0
    record = None
    feasible = 0
    for trial in range(trials):
        n = rng.integers(ntypes_range[0], ntypes_range[1] + 1)
        P = sample_types(n, C)
        # drop duplicate types (two Dirac types on the same cell etc.)
        P = np.unique(np.round(P, 9), axis=0)
        n = P.shape[0]
        if n < 3:
            continue
        # The pair-line system of audit r3 is complete only when the types are NOT all collinear
        # (then every class cone has 2-tight extreme rays = pair lines).  All-collinear types
        # (e.g. on one edge of the simplex) give cones with a lineality direction whose extreme
        # rays are single-type-tight and are never generated: the LP is then under-constrained
        # and reports spurious violations (seed 1 of this script, before this guard: three
        # types on the edge p(0) = 0, "slack -2.51" -- a two-cell question in disguise).
        if np.linalg.matrix_rank(np.c_[P, np.ones(n)], tol=1e-9) < 3:
            continue
        A, b = tt_constraints(P)
        Aeq = np.ones((1, n * C))
        # immodesty with full support: m[t,c] >= eps on supp p_t, = 0 off it
        bounds = []
        for t in range(n):
            for c in range(C):
                bounds.append((eps, None) if P[t, c] > 1e-12 else (0.0, 0.0))
        for _ in range(nmenu):
            menu = rng.normal(size=(3, C))
            for j in range(3):
                cvec, best = value_objective(P, menu, j)
                if cvec is None:
                    break
                if len(set(best)) < 3:   # want all three options used
                    break
                res = linprog(cvec, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[1.0],
                              bounds=bounds, method="highs")
                if res.status != 0:
                    continue
                feasible += 1
                if res.fun < worst:
                    worst = res.fun
                    record = (P.copy(), menu.copy(), j, res.x.copy())
    return worst, record, feasible


if __name__ == "__main__":
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    np.set_printoptions(precision=4, suppress=True)
    # control 1: the unconstrained search of audit r3 still finds violations (eps = 0, any support)
    w0, rec0, f0 = search(3, (4, 9), 40, 25, 0.0)
    print(f"control (eps=0, modest allowed): worst slack {w0:.4f} over {f0} feasible LPs")
    # the question: immodest, full support (argv[4]: max number of types, default 9)
    nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 9
    w, rec, f = search(3, (3, nmax), trials, 25, EPS)
    print(f"immodest, full support (eps={EPS}): worst slack {w:.6f} over {f} feasible LPs")
    if rec is not None:
        P, menu, j, m = rec
        print("types:\n", P); print("menu:\n", menu); print("j:", j)
        print("masses m[t,c]:\n", m.reshape(P.shape))
        print("cell marginal:", m.reshape(P.shape).sum(axis=0))
        seed = sys.argv[1] if len(sys.argv) > 1 else "0"
        np.savez(os.path.join(os.path.dirname(os.path.abspath(__file__)), f"rec_immodest_seed{seed}.npz"),
                 P=P, menu=menu, j=j, m=m.reshape(P.shape))
