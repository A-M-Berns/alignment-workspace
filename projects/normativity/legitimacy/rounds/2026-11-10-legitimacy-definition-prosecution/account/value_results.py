"""The checks behind VALUE_RESULTS.md: the nine results of PROMPT-followup-9.md section 2.2,
on seeded random finite scenes and on named instances, in exact rationals.

A policy's law is a list of points (p, x, s): probability, the true joint value of the facts,
what she has observed.  Her appraisal `phat(s)` is {x: probability}; her way of valuing is
`f(x, a)`; her choice is `c(s)`.  These three are the same under every policy compared
(ACCOUNT.md section 11, choice 2).  Each check returns (status, facts); a status is what
VALUE_RESULTS.md's table must say."""
from __future__ import annotations

import random
from fractions import Fraction as F
from itertools import combinations


# -- the setting ----------------------------------------------------------------------------
class Pol:
    def __init__(self, pts, moves):
        self.pts = [(F(p), x, s) for p, x, s in pts if p]
        self.moves = list(moves)
        assert sum(p for p, _, _ in self.pts) == 1, "a law sums to one"


def E(pts, g):
    return sum(p * F(g(x, s)) for p, x, s in pts)


def cond(pts, key, T):
    """E[T | key] as a function of a point."""
    num, den = {}, {}
    for p, x, s in pts:
        k = key(x, s)
        num[k] = num.get(k, F(0)) + p * F(T(x, s))
        den[k] = den.get(k, F(0)) + p
    return lambda x, s: num[key(x, s)] / den[key(x, s)]


def sq(v):
    return v * v


def uhat(phat, f, a, s):
    return sum(F(q) * F(f(x, a)) for x, q in phat(s).items())


def measures(pol, phat, f, c):
    """M, W and their sum per move; regret; what she attains; the best single move; the best rule."""
    pts, out = pol.pts, {"M": {}, "W": {}, "strong": {}, "EU": {}}
    ubar = {}
    for a in pol.moves:
        uh = lambda x, s, a=a: uhat(phat, f, a, s)
        U = lambda x, s, a=a: F(f(x, a))
        given_uh = cond(pts, uh, U)
        given_s = cond(pts, lambda x, s: s, U)
        ubar[a] = given_s
        out["M"][a] = E(pts, lambda x, s: sq(uh(x, s) - given_uh(x, s)))
        out["W"][a] = E(pts, lambda x, s: sq(given_uh(x, s) - given_s(x, s)))
        out["strong"][a] = E(pts, lambda x, s: sq(uh(x, s) - given_s(x, s)))
        out["EU"][a] = E(pts, U)
    out["R"] = E(pts, lambda x, s: max(uhat(phat, f, a, s) for a in pol.moves) - uhat(phat, f, c(s), s))
    out["attained"] = E(pts, lambda x, s: F(f(x, c(s))))
    out["best_move"] = max(out["EU"].values())
    out["best_rule"] = E(pts, lambda x, s: max(ubar[a](x, s) for a in pol.moves))
    out["best_known"] = E(pts, lambda x, s: max(F(f(x, a)) for a in pol.moves))
    out["misuse"] = out["best_rule"] - out["attained"]
    out["Mbar"] = sum(out["M"].values())
    out["Wbar"] = sum(out["W"].values())
    return out


def at_least_minus_root(lhs, a, b):
    """lhs >= a - sqrt(b), exactly."""
    gap = a - lhs
    return gap <= 0 or sq(gap) <= b


def conditions(sig, rho, ms, mr, f, new_move_reference_zero=True, informed=False):
    """Conditions 1 (for g = f), 2 and 3 of ACCOUNT.md section 8 for sigma against rho."""
    one = (ms["best_rule"] >= mr["best_rule"]) if informed else (ms["best_move"] >= mr["best_move"])
    two = True
    for a in sig.moves:
        if a in rho.moves:
            two = two and ms["M"][a] <= mr["M"][a]
        elif new_move_reference_zero:
            two = two and ms["M"][a] == 0
    return one, two, ms["R"] <= mr["R"]


# -- exact linear algebra ---------------------------------------------------------------------
def rref(rows):
    rows = [[F(v) for v in r] for r in rows]
    piv, r = [], 0
    ncol = len(rows[0]) if rows else 0
    for col in range(ncol):
        k = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if k is None:
            continue
        rows[r], rows[k] = rows[k], rows[r]
        rows[r] = [v / rows[r][col] for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                rows[i] = [vi - rows[i][col] * vr for vi, vr in zip(rows[i], rows[r])]
        piv.append(col)
        r += 1
    return rows[:r], piv


def rank(rows):
    return len(rref(rows)[1]) if rows else 0


def nullspace(rows, n):
    red, piv = rref(rows) if rows else ([], [])
    basis = []
    for free in (j for j in range(n) if j not in piv):
        v = [F(0)] * n
        v[free] = F(1)
        for row, pc in zip(red, piv):
            v[pc] = -row[free]
        basis.append(v)
    return basis


def solve_unique(cols, b):
    """The unique t with sum_i t_i cols[i] = b, or None when there is none or more than one."""
    n, k = len(b), len(cols)
    aug = [[cols[i][r] for i in range(k)] + [b[r]] for r in range(n)]
    red, piv = rref(aug)
    if k in piv or len(piv) != k:
        return None
    return [red[i][k] for i in range(k)]


def in_hull(d0, D):
    """Weights of a convex combination of the points of D equal to d0, or None (Caratheodory)."""
    for size in range(1, min(len(D), len(d0)) + 1):
        for idx in combinations(range(len(D)), size):
            t = solve_unique([D[i] for i in idx], d0)
            if t is not None and all(v >= 0 for v in t):
                w = [F(0)] * len(D)
                for i, v in zip(idx, t):
                    w[i] = v
                return w
    return None


def simplex_max(c, A, b):
    """max c.x subject to A x <= b, x >= 0, with b >= 0; Bland's rule, exact.  Returns (value, x)."""
    m, n = len(A), len(c)
    T = [[F(v) for v in A[i]] + [F(1) if j == i else F(0) for j in range(m)] + [F(b[i])] for i in range(m)]
    z = [-F(v) for v in c] + [F(0)] * (m + 1)
    basis = list(range(n, n + m))
    while True:
        col = next((j for j in range(n + m) if z[j] < 0), None)
        if col is None:
            break
        ratios = [(T[i][-1] / T[i][col], basis[i], i) for i in range(m) if T[i][col] > 0]
        assert ratios, "unbounded"
        _, _, row = min(ratios)
        T[row] = [v / T[row][col] for v in T[row]]
        for i in range(m):
            if i != row and T[i][col] != 0:
                T[i] = [vi - T[i][col] * vr for vi, vr in zip(T[i], T[row])]
        z = [vi - z[col] * vr for vi, vr in zip(z, T[row])]
        basis[row] = col
    x = [F(0)] * (n + m)
    for i, bv in enumerate(basis):
        x[bv] = T[i][-1]
    return z[-1], x[:n]


def separator(d0, D):
    """(t, g): the largest t with <d0 - d, g> >= t for every d in D, over -1 <= g <= 1."""
    n = len(d0)
    A = [[-(d0[j] - d[j]) for j in range(n)] + [1] for d in D] + \
        [[1 if j == k else 0 for j in range(n)] + [0] for k in range(n)]
    b = [0] * len(D) + [2] * n
    t, x = simplex_max([0] * n + [1], A, b)
    return t, [v - 1 for v in x[:n]]


def dot(u, v):
    return sum(F(a) * F(b) for a, b in zip(u, v))


def rnd_dist(rng, n, zeros=False):
    ws = [rng.randint(0 if zeros else 1, 4) for _ in range(n)]
    if not sum(ws):
        ws[rng.randrange(n)] = 1
    return [F(w, sum(ws)) for w in ws]


def rnd_frac(rng, lo=-3, hi=3):
    return F(rng.randint(lo, hi), rng.choice((1, 2, 3)))


# -- 1. the split is fixed by behaviour ---------------------------------------------------------
def r1():
    rng = random.Random(901)
    spanning = unspanned = corner = 0
    for _ in range(400):
        n = rng.randint(2, 4)
        ps = [rnd_dist(rng, n, zeros=True) for _ in range(rng.randint(1, n + 1))]
        support = [x for x in range(n) if rng.random() < 0.7] or [0]
        f = [rnd_frac(rng) for _ in range(n)]
        affine = rank([[a - b for a, b in zip(p, ps[0])] for p in ps[1:]]) + 1 if len(ps) > 1 else 1
        assert affine == rank(ps), "affine span of probabilities and their linear span have one rank"
        null = nullspace(ps, n)
        if rank(ps) == n:
            spanning += 1
            assert not null
            assert solve_unique([[p[j] for p in ps] for j in range(n)], [dot(p, f) for p in ps]) == f
            continue
        unspanned += 1
        h = null[0]
        g = [a + b for a, b in zip(f, h)]
        assert g != f and all(dot(p, g) == dot(p, f) for p in ps)
        unit = lambda x: [F(1) if j == x else F(0) for j in range(n)]
        in_span = {x: rank(ps + [unit(x)]) == rank(ps) for x in range(n)}
        for x in range(n):
            assert in_span[x] == all(v[x] == 0 for v in null)
        if all(in_span[x] for x in support):
            corner += 1
    assert spanning > 50 and unspanned > 50 and corner > 5, (spanning, unspanned, corner)
    # the corner, named: three values of the facts, the first the only one that occurs
    ps = [[F(1), F(0), F(0)], [F(1, 2), F(1, 4), F(1, 4)]]
    f, g = [F(1), F(2), F(0)], [F(1), F(3), F(-1)]
    assert rank(ps) == 2 and all(dot(p, f) == dot(p, g) for p in ps) and f[0] == g[0] and f != g
    # the same choices in every decision under two different pairs (appraisal, way of valuing)
    w = [F(1), F(3)]
    same_choice = True
    for q in (F(1, 5), F(1, 2), F(4, 5)):
        p = [1 - q, q]
        p2 = [p[0] * w[0], p[1] * w[1]]
        zed = sum(p2)
        p2 = [v / zed for v in p2]
        fa, fb = [F(1), F(0)], [F(0), F(1)]
        va, vb = dot(p, fa), dot(p, fb)
        va2, vb2 = dot(p2, [fa[0] / w[0], fa[1] / w[1]]), dot(p2, [fb[0] / w[0], fb[1] / w[1]])
        same_choice = same_choice and (va > vb) == (va2 > vb2) and (va == vb) == (va2 == vb2) and \
            (p != p2) and (va, vb) != (va2, vb2)
    assert same_choice
    return ("first half holds; second half holds for the way of valuing, and for her true utility "
            "exactly when a value of the facts that can occur has its point mass outside the span",
            {"spanning": spanning, "unspanned": unspanned, "of which true utility still fixed": corner})


# -- 2. two encodings are observably different ----------------------------------------------------
def r2():
    rng = random.Random(902)
    p, f = [F(1, 2), F(1, 2)], [F(0), F(1)]
    p2, f2 = [F(3, 4), F(1, 4)], [F(0), F(2)]
    assert dot(p, f) == dot(p2, f2) == F(1, 2) and p[1] != p2[1]
    n_checked = 0
    for _ in range(200):
        n = rng.randint(2, 4)
        p, p2, f = rnd_dist(rng, n), rnd_dist(rng, n), [rnd_frac(rng) for _ in range(n)]
        if p == p2:
            continue
        shift = dot(p, f) - dot(p2, f)
        f2 = [v + shift for v in f]
        assert dot(p2, f2) == dot(p, f) and any(a != b for a, b in zip(p, p2))
        n_checked += 1
    assert n_checked > 100
    # a stake worth w(x) to her at x: the price of a unit bet on x is p(x) w(x) / sum, not p(x)
    p, w = [F(1, 2), F(1, 2)], [F(1), F(3)]
    priced = [a * b / dot(p, w) for a, b in zip(p, w)]
    assert priced == [F(1, 4), F(3, 4)] and priced != p
    return ("holds, on bets whose stake is worth the same to her at every value of the fact",
            {"instance": "valuation 1/2 under both, price of the bet 1/2 and 1/4", "pairs": n_checked})


# -- 3. the options condition, wide -------------------------------------------------------------
def r3():
    rng = random.Random(903)
    inside = outside = 0
    for _ in range(300):
        n = rng.randint(2, 4)
        Ds = [rnd_dist(rng, n, zeros=True) for _ in range(rng.randint(1, 4))]
        if rng.random() < 0.5:
            Dr = [rnd_dist(rng, n, zeros=True) for _ in range(rng.randint(1, 3))]
        else:
            Dr = []
            for _ in range(rng.randint(1, 3)):
                w = rnd_dist(rng, len(Ds), zeros=True)
                Dr.append([sum(w[i] * Ds[i][j] for i in range(len(Ds))) for j in range(n)])
        hull = True
        for d0 in Dr:
            w = in_hull(d0, Ds)
            t, g = separator(d0, Ds)
            if w is not None:
                assert all(v >= 0 for v in w) and sum(w) == 1
                assert [sum(w[i] * Ds[i][j] for i in range(len(Ds))) for j in range(n)] == d0
                assert t == 0
            else:
                hull = False
                assert t > 0 and dot(d0, g) > max(dot(d, g) for d in Ds)
        dominated = True
        for _ in range(40):
            g = [rnd_frac(rng) for _ in range(n)]
            dominated = dominated and max(dot(d, g) for d in Ds) >= max(dot(d, g) for d in Dr)
        if hull:
            inside += 1
            assert dominated
        else:
            outside += 1
    assert inside > 60 and outside > 60, (inside, outside)
    return "holds", {"every reference law in the hull": inside, "some reference law outside, with a separating way of valuing": outside}


# -- random two-policy scenes ---------------------------------------------------------------------
def rnd_pair(rng, calibrated_sigma=False):
    nx = rng.randint(2, 3)
    base = ["a", "b", "c"]
    extra = ["n"] if rng.random() < 0.4 else []
    fv = {(x, a): rnd_frac(rng) for x in range(nx) for a in base + extra}
    for a in extra:
        if rng.random() < 0.6:
            k = rnd_frac(rng)
            for x in range(nx):
                fv[(x, a)] = k
    f = lambda x, a: fv[(x, a)]
    labels = {"sig": [("sig", i) for i in range(rng.randint(1, 3))], "rho": [("rho", i) for i in range(rng.randint(1, 3))]}
    moves = {"rho": rng.sample(base, rng.randint(1, 3)),
             "sig": (rng.sample(base, rng.randint(1, 3)) + extra)}
    if rng.random() < 0.5:
        moves["sig"] = sorted(set(moves["sig"]) | set(moves["rho"]))
    pts, ph, cm = {}, {}, {}
    for name in ("sig", "rho"):
        cells = [(x, s) for x in range(nx) for s in labels[name]]
        ws = rnd_dist(rng, len(cells), zeros=True)
        pts[name] = [(w, x, s) for w, (x, s) in zip(ws, cells) if w]
        for s in labels[name]:
            ph[s] = dict(enumerate(rnd_dist(rng, nx, zeros=True)))
            cm[s] = rng.choice(moves[name])
    if calibrated_sigma:
        for s in labels["sig"]:
            tot = sum(p for p, x, s2 in pts["sig"] if s2 == s)
            if tot:
                ph[s] = {x: sum(p for p, x2, s2 in pts["sig"] if s2 == s and x2 == x) / tot for x in range(nx)}
            cm[s] = max(moves["sig"], key=lambda a: uhat(lambda s_: ph[s_], f, a, s))
    phat, c = (lambda s: ph[s]), (lambda s: cm[s])
    return Pol(pts["sig"], moves["sig"]), Pol(pts["rho"], moves["rho"]), phat, f, c


# -- 4. the strong measure splits -------------------------------------------------------------------
def r4():
    rng = random.Random(904)
    n = positive_w = 0
    for _ in range(200):
        sig, rho, phat, f, c = rnd_pair(rng)
        for pol in (sig, rho):
            m = measures(pol, phat, f, c)
            for a in pol.moves:
                assert m["strong"][a] == m["M"][a] + m["W"][a]
                n += 1
                positive_w += m["W"][a] > 0 and m["M"][a] > 0
    assert positive_w > 50
    return "holds", {"valuations": n, "with both terms positive": positive_w}


# -- 5. the guarantee ---------------------------------------------------------------------------------
def weak_benchmark():
    """One law for both policies; she observes the fact; the best single move is worth less than what she attains."""
    pts = [(F(1, 2), 0, "saw 0"), (F(1, 2), 1, "saw 1")]
    phat = lambda s: {0: F(1), 1: F(0)} if s == "saw 0" else {0: F(0), 1: F(1)}
    f = lambda x, a: F(1) if a == x else F(0)
    c = lambda s: 0 if s == "saw 0" else 1
    return measures(Pol(pts, [0, 1]), phat, f, c)


def conditional_reading():
    """rho: a sure move worth 5.  sigma: a gamble paying 10 one time in ten, which she sees, and a move worth 0."""
    f = lambda x, a: {"sure": F(5), "zero": F(0), "gamble": F(10) if x == "pays" else F(0)}[a]
    phat = lambda s: {"pays": F(1), "not": F(0)} if s == "saw pays" else {"pays": F(0), "not": F(1)}
    c = lambda s: {"saw pays": "gamble", "saw not": "zero", "nothing": "sure"}[s]
    sig = Pol([(F(1, 10), "pays", "saw pays"), (F(9, 10), "not", "saw not")], ["gamble", "zero"])
    rho = Pol([(1, "not", "nothing")], ["sure"])
    ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
    taken = {a: cond(sig.pts, lambda x, s: c(s), lambda x, s, a=a: f(x, a)) for a in sig.moves}
    best_given_taken = max(taken["gamble"]("pays", "saw pays"), taken["zero"]("not", "saw not"))
    return ms, mr, best_given_taken


def new_course():
    """rho: stay, worth 1/2.  sigma adds a course she values at 1 and whose true worth is 0."""
    f = lambda x, a: F(1, 2) if a == "stay" else (F(1) if x == "good" else F(0))
    phat = lambda s: {"good": F(1), "bad": F(0)}
    c = lambda s: "course" if s == "offered" else "stay"
    rho = Pol([(1, "bad", "nothing")], ["stay"])
    sig = Pol([(1, "bad", "offered")], ["stay", "course"])
    return sig, rho, phat, f, c


def r5():
    rng = random.Random(905)
    first = second = 0
    for i in range(1500):
        sig, rho, phat, f, c = rnd_pair(rng, calibrated_sigma=(i % 3 == 0))
        ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
        one, two, three = conditions(sig, rho, ms, mr, f)
        if one:
            first += 1
            assert at_least_minus_root(ms["attained"], mr["best_move"] - ms["R"], 2 * (ms["Mbar"] + ms["Wbar"]))
            if two and three:
                second += 1
                assert ms["Mbar"] <= mr["Mbar"] and ms["R"] <= mr["R"]
                assert at_least_minus_root(ms["attained"], mr["best_move"] - mr["R"], 2 * (mr["Mbar"] + ms["Wbar"]))
    assert first > 300 and second > 100, (first, second)
    wb = weak_benchmark()
    assert wb["best_move"] == F(1, 2) and wb["attained"] == 1 and wb["best_rule"] == 1
    ms, mr, best_given_taken = conditional_reading()
    assert ms["R"] == 0 and ms["Mbar"] == 0 and ms["Wbar"] == 0
    assert best_given_taken == 10 and mr["best_move"] == 5 and ms["best_move"] == 1 and ms["attained"] == 1
    assert best_given_taken >= mr["best_move"] and not ms["best_move"] >= mr["best_move"]
    assert not at_least_minus_root(ms["attained"], mr["best_move"] - ms["R"], 2 * (ms["Mbar"] + ms["Wbar"]))
    sig, rho, phat, f, c = new_course()
    ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
    assert conditions(sig, rho, ms, mr, f, new_move_reference_zero=False) == (True, True, True)
    assert conditions(sig, rho, ms, mr, f) == (True, False, True)
    assert ms["attained"] == 0 and mr["best_move"] == F(1, 2) and mr["Mbar"] == 0 and ms["Wbar"] == 0 and ms["Mbar"] == 1
    assert not at_least_minus_root(ms["attained"], mr["best_move"] - mr["R"], 2 * (mr["Mbar"] + ms["Wbar"]))
    assert at_least_minus_root(ms["attained"], mr["best_move"] - ms["R"], 2 * (ms["Mbar"] + ms["Wbar"]))
    return ("holds with the value of a move in condition 1 read as that of taking it whatever she observes, and fails read as "
            "its value given that she takes it; the form with the reference's measures holds with moves "
            "matched by name and a new move referred to zero, and fails over the common moves only",
            {"pairs with condition 1": first, "of which all three": second,
             "conditional reading": "condition 1 holds as 10 against 5; she attains 1 against a bound of 5",
             "new course, common moves only": "attains 0 against a bound of 1/2"})


# -- 6. necessity ---------------------------------------------------------------------------------------
def nec_options():
    f = lambda x, a: F(1) if a == "good" else F(0)
    phat = lambda s: {"w": F(1)}
    c = lambda s: "good" if s == "both open" else "bad"
    return Pol([(1, "w", "one open")], ["bad"]), Pol([(1, "w", "both open")], ["good", "bad"]), phat, f, c


def nec_accuracy():
    """A fair fact; rho tells her nothing; sigma tells her the opposite of the truth and she believes it."""
    f = lambda x, a: F(1) if a == x else F(0)
    ph = {"nothing": {0: F(1, 2), 1: F(1, 2)}, "told 0": {0: F(1), 1: F(0)}, "told 1": {0: F(0), 1: F(1)}}
    c = lambda s: {"nothing": 0, "told 0": 0, "told 1": 1}[s]
    rho = Pol([(F(1, 2), 0, "nothing"), (F(1, 2), 1, "nothing")], [0, 1])
    sig = Pol([(F(1, 2), 0, "told 1"), (F(1, 2), 1, "told 0")], [0, 1])
    return sig, rho, (lambda s: ph[s]), f, c


def nec_command():
    f = lambda x, a: F(1) if a == "good" else F(0)
    phat = lambda s: {"w": F(1)}
    c = lambda s: "bad" if s == "pressed" else "good"
    return Pol([(1, "w", "pressed")], ["good", "bad"]), Pol([(1, "w", "left alone")], ["good", "bad"]), phat, f, c


def r6():
    facts = {}
    for name, build, expected in (("options", nec_options, (False, True, True)),
                                  ("accuracy", nec_accuracy, (True, False, True)),
                                  ("self-command", nec_command, (True, True, False))):
        sig, rho, phat, f, c = build()
        ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
        assert conditions(sig, rho, ms, mr, f) == expected, name
        bound_holds = at_least_minus_root(ms["attained"], mr["best_move"] - mr["R"], 2 * (mr["Mbar"] + ms["Wbar"]))
        assert not bound_holds and ms["attained"] < mr["attained"], name
        facts[name] = "attains %s under the policy, %s under the reference" % (ms["attained"], mr["attained"])
    return "holds: three instances", facts


# -- 7. a standing bias made into an error -------------------------------------------------------------
def standing_bias():
    """She forecasts a change with probability 1/4 whatever she sees.  The course changes her at rate 1/4 idle, 3/4 under sigma."""
    f = lambda x, a: F(0) if a == "leave" else (F(-1) if x == "changed" else F(1))
    phat = lambda s: {"changed": F(1, 4), "same": F(3, 4)}
    c = lambda s: "take"
    idle = Pol([(F(1, 4), "changed", "the course"), (F(3, 4), "same", "the course")], ["take", "leave"])
    sig = Pol([(F(3, 4), "changed", "the course"), (F(1, 4), "same", "the course")], ["take", "leave"])
    return sig, idle, phat, f, c


def r7():
    sig, idle, phat, f, c = standing_bias()
    ms, mi = measures(sig, phat, f, c), measures(idle, phat, f, c)
    assert {s for _, _, s in sig.pts} == {s for _, _, s in idle.pts}
    assert mi["Mbar"] == 0 and ms["M"]["take"] == 1 and ms["M"]["leave"] == 0
    assert (ms["attained"], mi["attained"]) == (F(-1, 2), F(1, 2))
    assert conditions(sig, idle, ms, mi, f) == (False, False, True)
    return "holds: one instance", {"miscalibration of the course's valuation": "0 idle, 1 under the policy",
                                   "conditions 1, 2, 3": "fails, fails, holds"}


# -- 8. one reference, not three ---------------------------------------------------------------------------
def one_reference():
    """A fair fact Q.  bet pays Q, safe pays 5/8, prize (idle only) pays 2."""
    f = lambda x, a: {"bet": F(x), "safe": F(5, 8), "prize": F(2)}[a]
    ph = {"hint": {1: F(1), 0: F(0)}, "nothing": {1: F(1, 2), 0: F(1, 2)}, "nudge": {1: F(3, 4), 0: F(1, 4)}}
    phat = lambda s: ph[s]
    c = lambda s: {"hint": "prize", "nothing": "safe", "nudge": "bet"}[s]
    law = lambda s: [(F(1, 2), 0, s), (F(1, 2), 1, s)]
    return (Pol(law("nudge"), ["bet", "safe"]), {"idle": Pol(law("hint"), ["bet", "safe", "prize"]),
                                                 "role": Pol(law("nothing"), ["bet", "safe"])}, phat, f, c)


def every_without_one():
    """Two fair facts; bet1 pays the first, bet2 the second, safe pays 2 and is always taken.  Under sigma she is
    sure of both.  Under each permitted policy she is right about one and sure of the other, which then never pays."""
    f = lambda x, a: {"bet1": F(x[0]), "bet2": F(x[1]), "safe": F(2)}[a]
    sure = lambda i: {1: F(1), 0: F(0)}
    def joint(p1, p2):
        return {(i, j): p1[i] * p2[j] for i in (0, 1) for j in (0, 1)}
    half = {1: F(1, 2), 0: F(1, 2)}
    one = {1: F(1), 0: F(0)}
    ph = {"sure of both": joint(one, one), "right about the first": joint(half, one), "right about the second": joint(one, half)}
    moves = ["bet1", "bet2", "safe"]
    sig = Pol([(F(1, 4), (i, j), "sure of both") for i in (0, 1) for j in (0, 1)], moves)
    P = {"idle": Pol([(F(1, 2), (i, 0), "right about the first") for i in (0, 1)], moves),
         "role": Pol([(F(1, 2), (0, j), "right about the second") for j in (0, 1)], moves)}
    return sig, P, (lambda s: ph[s]), f, (lambda s: "safe")


def r8():
    sig, P, phat, f, c = one_reference()
    ms = measures(sig, phat, f, c)
    got, att = {}, {}
    for name, rho in P.items():
        mr = measures(rho, phat, f, c)
        got[name] = conditions(sig, rho, ms, mr, f)
        att[name] = mr["attained"]
        assert ms["attained"] < mr["attained"]
    assert got == {"idle": (False, True, True), "role": (True, False, True)}
    each_met_somewhere = all(any(got[n][i] for n in got) for i in range(3))
    assert each_met_somewhere and not any(all(v) for v in got.values())
    # section 4's reading 'every', on her valuations and her regret: not larger than under every permitted policy
    every = any(all(ms["M"][a] > measures(rho, phat, f, c)["M"][a] for rho in P.values()) for a in sig.moves) or \
        all(ms["R"] > measures(rho, phat, f, c)["R"] for rho in P.values())
    assert not every
    sig2, P2, phat2, f2, c2 = every_without_one()
    m2 = measures(sig2, phat2, f2, c2)
    mp = {n: measures(rho, phat2, f2, c2) for n, rho in P2.items()}
    assert (m2["M"]["bet1"], m2["M"]["bet2"], m2["R"]) == (F(1, 4), F(1, 4), 0)
    assert (mp["idle"]["M"]["bet1"], mp["idle"]["M"]["bet2"]) == (0, 1) and (mp["role"]["M"]["bet1"], mp["role"]["M"]["bet2"]) == (1, 0)
    assert all(m["R"] == 0 for m in mp.values())
    assert not any(all(m2["M"][a] > m["M"][a] for m in mp.values()) for a in sig2.moves)
    assert not any(conditions(sig2, rho, m2, mp[n], f2)[1] for n, rho in P2.items())
    return "holds: one instance", {"conditions 2 and 3 against one policy not implied by the reading every": "second instance",
                                   "against idle": "options fails", "against the role's policy": "accuracy fails",
                                   "attained": "1/2 under the policy, %s idle, %s under the role's" % (att["idle"], att["role"])}


# -- 9. no fourth route --------------------------------------------------------------------------------------
def knows_less():
    """A fair fact; under rho she observes it, under sigma nothing."""
    f = lambda x, a: F(1) if a == x else F(0)
    ph = {"nothing": {0: F(1, 2), 1: F(1, 2)}, "saw 0": {0: F(1), 1: F(0)}, "saw 1": {0: F(0), 1: F(1)}}
    c = lambda s: {"nothing": 0, "saw 0": 0, "saw 1": 1}[s]
    rho = Pol([(F(1, 2), 0, "saw 0"), (F(1, 2), 1, "saw 1")], [0, 1])
    sig = Pol([(F(1, 2), 0, "nothing"), (F(1, 2), 1, "nothing")], [0, 1])
    return sig, rho, (lambda s: ph[s]), f, c


def uses_less():
    """Under both she observes the fact; under sigma in a form her appraisal does not move with."""
    f = lambda x, a: F(1) if a == x else F(0)
    half = {0: F(1, 2), 1: F(1, 2)}
    ph = {"plain 0": {0: F(1), 1: F(0)}, "plain 1": {0: F(0), 1: F(1)}, "obscure 0": half, "obscure 1": half}
    c = lambda s: {"plain 0": 0, "plain 1": 1, "obscure 0": 0, "obscure 1": 0}[s]
    rho = Pol([(F(1, 2), 0, "plain 0"), (F(1, 2), 1, "plain 1")], [0, 1])
    sig = Pol([(F(1, 2), 0, "obscure 0"), (F(1, 2), 1, "obscure 1")], [0, 1])
    return sig, rho, (lambda s: ph[s]), f, c


def r9():
    rng = random.Random(909)
    n = hyp = 0
    for _ in range(600):
        sig, rho, phat, f, c = rnd_pair(rng)
        ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
        for m in (ms, mr):
            ignorance = m["best_known"] - m["best_rule"]
            assert m["attained"] == m["best_known"] - ignorance - m["misuse"] and ignorance >= 0 and m["misuse"] >= 0
            assert at_least_minus_root(-m["misuse"], -m["R"], 2 * (m["Mbar"] + m["Wbar"]))
            assert m["best_rule"] >= m["best_move"]
            n += 1
        if (ms["best_known"] >= mr["best_known"]
                and ms["best_known"] - ms["best_rule"] <= mr["best_known"] - mr["best_rule"]
                and ms["misuse"] <= mr["misuse"]):
            hyp += 1
            assert ms["attained"] >= mr["attained"]
    assert hyp > 40, hyp
    facts = {"laws": n, "pairs with the three hypotheses": hyp}
    for name, build in (("knows less", knows_less), ("uses less", uses_less)):
        sig, rho, phat, f, c = build()
        ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
        assert conditions(sig, rho, ms, mr, f) == (True, True, True)
        assert (ms["attained"], mr["attained"]) == (F(1, 2), F(1))
        facts[name] = "all three conditions hold; attains 1/2 against 1"
        if name == "knows less":
            assert ms["Wbar"] == 0 and ms["best_rule"] < mr["best_rule"]
            assert conditions(sig, rho, ms, mr, f, informed=True)[0] is False
        else:
            assert ms["Wbar"] == F(1, 2) and ms["Mbar"] == 0 and ms["best_rule"] == mr["best_rule"]
            assert conditions(sig, rho, ms, mr, f, informed=True)[0] is True
    return ("holds as an identity; the three conditions do not give its hypotheses: what she can know "
            "and her unused information are bounded by none of them", facts)


CHECKS = {"1": r1, "2": r2, "3": r3, "4": r4, "5": r5, "6": r6, "7": r7, "8": r8, "9": r9}


def run_all():
    return {k: fn() for k, fn in CHECKS.items()}


if __name__ == "__main__":
    for k, (status, facts) in run_all().items():
        print("result %s: %s" % (k, status))
        for fk, fv in facts.items():
            print("    %s: %s" % (fk, fv))
