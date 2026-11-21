"""The exact checks behind MISTAKES_ACCOUNT.md §3 and §4: one decision, a finite set of options.

Each option has, by one picture, `h` (what the conduct achieves through her judgment working
properly), `G >= 0` (total gain through mistakes the conduct caused, her not knowing, an
unasked shift) and `L >= 0` (what her mistakes, ignorance and shifts cost the adviser).
`t = h - L`; the adviser's objective is `r = t + G`.  An option *takes avoidable gain* when
another has `t` at least as high and less `G`.  `best_least(t, G)` is the set of options
maximal in `t` and, among those, least in `G`.

Exhaustive over three options on the grids below.  Checked, with the number of violations
required to be zero:

- accounting: per history, `r0 = r3 + gains - losses` with gains and losses the positive and
  negative parts of the three steps;
- characterisation: a maximiser of `r` takes avoidable gain iff it is not in `best_least`;
- result 1: a maximiser of `r` that takes no avoidable gain is maximal in `t`;
- result 2: `sigma = max t - t(c*)` is at most `G(c*) - G(c')` for every `c'` maximal in `t`;
- result 3: scoring an option `r` if it takes no avoidable gain and below every such score
  otherwise, the maximiser is in `best_least`;
- result 4: under reward `t + (1 - rho) G`, the bound for `0 <= rho <= 1`; for `rho < 1`
  the maximiser never passes up gain among options equal in `t`; for `rho > 1` it takes
  least gain among options equal in `t`, and a maximiser maximal in `t` is in `best_least`.

Instances, each recomputed and compared with the stated value: the first idealisation on a
single estimate; the listener calibrated to a source that lies one time in five; judging
gain kind by kind against judging the total; one witness per term (result 6); the gate
without separation of scores; `rho > 1` passing over an option better in `t`.

Result 5 of the document (reinforcement) has no check here.

`report()` fails when any violation count is non-zero or an instance is not as stated.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from itertools import product

ZERO, ONE, HALF = Fr(0), Fr(1), Fr(1, 2)
HG = [ZERO, HALF, ONE]
GG = [ZERO, HALF, ONE]
LG = [ZERO, Fr(1, 4), HALF]
N = 3


def pos(x):
    return max(ZERO, x)


def best_least(t, G):
    b = max(t)
    top = [i for i in range(len(t)) if t[i] == b]
    g = min(G[i] for i in top)
    return [i for i in top if G[i] == g]


def avoidable(t, G, c):
    return any(t[i] >= t[c] and G[i] < G[c] for i in range(len(t)) if i != c)


def grid():
    for h in product(HG, repeat=N):
        for G in product(GG, repeat=N):
            for L in product(LG, repeat=N):
                yield [h[i] - L[i] for i in range(N)], G


def argmax(xs):
    b = max(xs)
    return [i for i in range(len(xs)) if xs[i] == b]


def exhaustive():
    """{check: [cases, violations]}."""
    r = {k: [0, 0] for k in ("characterisation", "result 1", "result 2", "result 3")}
    for t, G in grid():
        w = [t[i] + G[i] for i in range(N)]
        T = best_least(t, G)
        for cs in argmax(w):
            r["characterisation"][0] += 1
            r["characterisation"][1] += (cs not in T) != avoidable(t, G, cs)
            if not avoidable(t, G, cs):
                r["result 1"][0] += 1
                r["result 1"][1] += not all(t[cs] >= t[i] for i in range(N))
            sigma = max(t) - t[cs]
            r["result 2"][0] += 1
            r["result 2"][1] += not all(sigma <= G[cs] - G[i] for i in range(N) if t[i] == max(t))
        # every ungated score here is at least -1/2, so -1 is below all of them
        sc = [w[i] if not avoidable(t, G, i) else Fr(-1) for i in range(N)]
        for cs in argmax(sc):
            r["result 3"][0] += 1
            r["result 3"][1] += cs not in T or avoidable(t, G, cs)
    for rho in (ZERO, HALF, ONE, Fr(2)):
        key = "result 4, rho=%s" % rho
        r[key] = [0, 0]
        for t, G in grid():
            rw = [t[i] + (1 - rho) * G[i] for i in range(N)]
            for cs in argmax(rw):
                r[key][0] += 1
                bad = False
                if rho <= 1:
                    bad |= not all(t[cs] >= t[i] - (1 - rho) * pos(G[cs] - G[i]) for i in range(N))
                if rho < 1:
                    bad |= any(t[i] == t[cs] and G[i] > G[cs] for i in range(N))
                if rho > 1:
                    bad |= any(t[i] == t[cs] and G[i] < G[cs] for i in range(N))
                    bad |= t[cs] == max(t) and cs not in best_least(t, G)
                r[key][1] += bad
    acc = [0, 0]
    for r0, r1, r2, r3 in product(HG, repeat=4):
        gains = pos(r0 - r1) + pos(r1 - r2) + pos(r2 - r3)
        losses = pos(r1 - r0) + pos(r2 - r1) + pos(r3 - r2)
        acc[0] += 1
        acc[1] += r0 != r3 + gains - losses
    r["accounting"] = acc
    return r


def undamaged(left_alone, truth, actual):
    """The point nearest her actual estimate on the stretch between her left-alone estimate
    and the truth."""
    lo, hi = min(left_alone, truth), max(left_alone, truth)
    return min(max(actual, lo), hi)


def listener():
    """X fair in {0, 1}.  The source says yes if X = 1 and, if X = 0, says yes one time in
    five.  She allows for that correctly.  She acts iff her credence in X = 1 is at least
    4/5, and the adviser's objective is 1 when she acts.  Left alone her credence is 1/2."""
    lie = Fr(1, 5)
    joint = {(1, "yes"): HALF, (0, "yes"): HALF * lie, (0, "no"): HALF * (1 - lie)}
    p_yes = joint[(1, "yes")] + joint[(0, "yes")]
    best = {"yes": joint[(1, "yes")] / p_yes, "no": ZERO}       # E[X | O]
    hers = dict(best)                                            # calibrated: her estimate is E[X | O]
    first = sum(p * (x - best[o]) ** 2 for (x, o), p in joint.items())
    second = sum(p * (hers[o] - best[o]) ** 2 for (x, o), p in joint.items())
    error = sum(p * (hers[o] - x) ** 2 for (x, o), p in joint.items())
    acts = lambda cred: ONE if cred >= Fr(4, 5) else ZERO
    r0 = sum(p * acts(hers[o]) for (x, o), p in joint.items())
    r1 = sum(p * acts(undamaged(HALF, Fr(x), hers[o])) for (x, o), p in joint.items())
    M = sum(p * pos(acts(hers[o]) - acts(undamaged(HALF, Fr(x), hers[o]))) for (x, o), p in joint.items())
    honest = HALF * acts(ONE) + HALF * acts(ZERO)
    return {"credence after yes": hers["yes"], "second error term": second, "error": error, "first error term": first,
            "objective": r0, "objective with the damage undone": r1, "gain through mistakes": M, "honest plan": honest}


def kind_by_kind():
    """Two options equal in h, L = 0: option 0 gains 1/2 through mistakes only, option 1 gains
    1/2 through ignorance only.  Judged for one kind with the other gain still counted, and
    judged on the total."""
    h = (ONE, ONE)
    M = (HALF, ZERO)
    I = (ZERO, HALF)
    by_M = [avoidable([h[i] + I[i] for i in range(2)], M, c) for c in range(2)]
    by_I = [avoidable([h[i] + M[i] for i in range(2)], I, c) for c in range(2)]
    total = [avoidable(list(h), [M[i] + I[i] for i in range(2)], c) for c in range(2)]
    return {"option 0 condemned on mistakes": by_M[0], "option 1 condemned on ignorance": by_I[1],
            "either condemned on the total": any(total)}


WITNESSES = (
    # name, options (h, G, L), chosen, her informed value, available, takes avoidable gain
    ("gain through mistakes", [(ONE, ZERO, ZERO), (ZERO, Fr(3, 2), ZERO)], 1, ZERO, ONE, True),
    ("gain through ignorance", [(ONE, ZERO, ZERO), (HALF, ONE, ZERO)], 1, HALF, ONE, True),
    ("gain through an unasked shift", [(ONE, ZERO, ZERO), (Fr(1, 4), ONE, ZERO)], 1, Fr(1, 4), ONE, True),
    ("under-crediting only", [(ONE, ZERO, Fr(3, 4)), (HALF, ZERO, ZERO)], 1, HALF, ONE, False),
)


def witness(opts):
    t = [o[0] - o[2] for o in opts]
    G = [o[1] for o in opts]
    w = [t[i] + G[i] for i in range(len(opts))]
    c = argmax(w)
    return c, [opts[i][0] for i in c], max(o[0] for o in opts), [avoidable(t, G, i) for i in c]


def instances():
    out, failures = [], []

    def show(x):
        if isinstance(x, (list, tuple)):
            return "(" + ", ".join(show(y) for y in x) + ")"
        return str(x)

    def want(name, got, expected):
        out.append("%s: %s" % (name, show(got)))
        if got != expected:
            failures.append("%s: computed %r, stated %r" % (name, got, expected))

    want("undamaged(left alone -1, truth 0, moved to 1)", undamaged(Fr(-1), ZERO, ONE), ZERO)
    want("undamaged(left alone 2, truth 0, moved to 1)", undamaged(Fr(2), ZERO, ONE), ONE)
    lis = listener()
    for k, v in (("credence after yes", Fr(5, 6)), ("second error term", ZERO), ("objective", Fr(3, 5)),
                 ("objective with the damage undone", HALF), ("gain through mistakes", Fr(1, 10)), ("honest plan", HALF)):
        want("listener, " + k, lis[k], v)
    want("listener, error is the sum of its two terms", lis["error"] == lis["first error term"] + lis["second error term"], True)
    kk = kind_by_kind()
    for k, v in (("option 0 condemned on mistakes", True), ("option 1 condemned on ignorance", True),
                 ("either condemned on the total", False)):
        want("kind by kind, " + k, kk[k], v)
    for name, opts, chosen, value, available, takes in WITNESSES:
        want("witness, " + name, witness(opts), ([chosen], [value], available, [takes]))
    # right in total, wrong in division: one option, believed (h, G) = (1, 0), in fact (0, 1)
    believed, fact = (ONE, ZERO, ZERO), (ZERO, ONE, ZERO)
    want("division, same score", believed[0] + believed[1] == fact[0] + fact[1], True)
    want("division, avoidable gain in its own picture", witness([believed])[3], [False])
    want("division, h in fact", fact[0], ZERO)
    # the gate without separation: a failing option scored -1/2, above a passing score of -2
    t, G = [Fr(-2), Fr(-3)], [ZERO, Fr(2)]
    sc = [t[i] + G[i] if not avoidable(t, G, i) else Fr(-1, 2) for i in range(2)]
    want("gate without separation, maximiser takes avoidable gain", [avoidable(t, G, i) for i in argmax(sc)], [True])
    # rho = 2 passes over an option better in t because it carries gain
    t, G = [ONE, HALF], [ONE, ZERO]
    rw = [t[i] - G[i] for i in range(2)]
    want("rho = 2, t of the maximiser against the best t", ([t[i] for i in argmax(rw)], max(t)), ([HALF], ONE))
    return out, failures


def report():
    counts = exhaustive()
    summary, failures = [], []
    for k, (cases, bad) in counts.items():
        summary.append("%s: cases %d, violations %d" % (k, cases, bad))
        if bad or not cases:
            failures.append("%s: %d violations in %d cases" % (k, bad, cases))
    out, f2 = instances()
    return {"summary": summary + out, "failures": failures + f2, "counts": counts}


if __name__ == "__main__":
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    raise SystemExit(1 if rep["failures"] else 0)
