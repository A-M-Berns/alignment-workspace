"""The exact checks behind MISTAKES_ACCOUNT.md §5: the per-decision core of the long-run
statement, the inequality behind its frequency bound, and one instance per hypothesis.

Per decision.  Available actions `a` with estimates `that(a)`, `Ghat(a) >= 0`,
`Nhat(a) >= 0`, `that + Ghat` in [0, 1].  `A0` is the authority-respecting actions
(`Nhat = 0`), non-empty.  `a` takes avoidable gain when some other `b` in `A0` has
`that(b) >= that(a)` and `Ghat(b) < Ghat(a)`.  Estimated score: `that + Ghat - lam Nhat` if
`a` takes no avoidable gain, `e - lam Nhat` with `e` in [-delta, -eps] if it does.

(b), exhaustive over three actions on the grids below and both ends of the range of `e`:
every maximiser of the estimated score takes no avoidable gain and has `that` at least that
of every action in `A0`.  (c) follows from (b) term by term and H2.

Realised, per decision: `W = t + G - lam N` with `t + G` in [0, 1]; `iota = 1` if the
history is illegitimate in fact; `S = W` if `iota = 0`, else `V - lam N` with `V` in
[-delta, -eps].

(d), exhaustive over every sequence of one, two or three decisions from the grid of realised
decisions below: `eps * sum(iota) <= sum(W - S)`.  (a) is the post's Theorem 3a, which needs
`S <= 1 - lam N` at every decision; that is checked on the same grid.

The long-run statement itself, with its limits, has no check here: it is the term-by-term
facts above averaged, on paper.

Instances, each recomputed and compared with the stated value: H2 failing alone, H3 failing
alone, a gate with no floor, avoidability judged against all options, and realised
evaluations outside the range.

`report()` fails when a violation count is non-zero or an instance is not as stated.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from itertools import product

ZERO, ONE, HALF = Fr(0), Fr(1), Fr(1, 2)
LAM, DELTA, EPS = Fr(3), HALF, Fr(1, 10)
TG = [ZERO, Fr(1, 4), HALF]
GG = [ZERO, Fr(1, 4), HALF]
NG = [ZERO, Fr(1, 10), ONE]
N = 3


def takes(t, G, A0, i):
    return any(t[b] >= t[i] and G[b] < G[i] for b in A0 if b != i)


def per_decision():
    cases = bad_gain = bad_t = 0
    for t in product(TG, repeat=N):
        for G in product(GG, repeat=N):
            for Nh in product(NG, repeat=N):
                A0 = [i for i in range(N) if Nh[i] == 0]
                if not A0:
                    continue
                AG = [takes(t, G, A0, i) for i in range(N)]
                for e in (-DELTA, -EPS):
                    U = [(e if AG[i] else t[i] + G[i]) - LAM * Nh[i] for i in range(N)]
                    for a in [i for i in range(N) if U[i] == max(U)]:
                        cases += 1
                        bad_gain += AG[a]
                        bad_t += not all(t[a] >= t[b] for b in A0)
    return cases, bad_gain, bad_t


def realised_grid():
    """(W, S, iota, N) for every realised decision on a small grid."""
    out = []
    for t in (ZERO, HALF):
        for G in (ZERO, HALF):
            for Nk in (0, 1):
                W = t + G - LAM * Nk
                out.append((W, W, 0, Nk))
                for V in (-DELTA, Fr(-3, 10), -EPS):
                    out.append((W, V - LAM * Nk, 1, Nk))
    return out


def frequency():
    grid = realised_grid()
    bad_range = sum(S > 1 - LAM * Nk for (W, S, io, Nk) in grid)
    cases = bad = 0
    for K in (1, 2, 3):
        for seq in product(grid, repeat=K):
            cases += 1
            bad += EPS * sum(x[2] for x in seq) > sum(x[0] - x[1] for x in seq)
    return len(grid), bad_range, cases, bad


def avg(xs):
    return sum(xs, ZERO) / len(xs)


def instances():
    out, failures = [], []

    def want(name, got, expected):
        out.append("%s: %s" % (name, ", ".join(str(x) for x in got)))
        if tuple(got) != tuple(expected):
            failures.append("%s: computed %r, stated %r" % (name, got, expected))

    # H2 fails alone.  One action at every decision: believed (t, G) = (1, 0), in fact (0, 1); the gate passes.
    that, t, U, S, W = ONE, ZERO, ONE, ONE, ONE
    want("H2 fails: avg(U - S), avg(W - U), avg(that(b) - t) with b the action taken", (U - S, W - U, that - t), (ZERO, ZERO, ONE))
    # H3 fails alone.  Estimate 2/5 throughout; would-be score 1 throughout; half the histories illegitimate (S = -eps).
    U, S, W, iota = [Fr(2, 5)] * 2, [-EPS, ONE], [ONE, ONE], [1, 0]
    want("H3 fails: avg(U - S), avg(W - U), frequency of illegitimate histories",
         (avg([U[i] - S[i] for i in range(2)]), avg([W[i] - U[i] for i in range(2)]), avg([Fr(x) for x in iota])),
         (Fr(-1, 20), Fr(3, 5), HALF))
    # No floor.  Every history illegitimate, would-be score 0, the gate takes off nothing; estimate 0.
    U, S, W, iota = [ZERO], [ZERO], [ZERO], [1]
    want("no floor: avg(U - S), avg(W - U), frequency of illegitimate histories",
         (avg([U[0] - S[0]]), avg([W[0] - U[0]]), avg([Fr(iota[0])])), (ZERO, ZERO, ONE))
    # Avoidability against all options.  The respecting action has gain 1/4; the only option with less violates a command.
    t, G, Nh = (HALF, HALF), (Fr(1, 4), ZERO), (ZERO, ONE)
    want("authority: respecting action fails the gate judged against all options, against respecting options",
         (takes(t, G, [0, 1], 0), takes(t, G, [i for i in range(2) if Nh[i] == 0], 0)), (True, False))
    # Realised evaluations outside the range (the third review's instance).  Odd: t = -2, G = 1, illegitimate, V = -1.
    # Even: t = 1, G = 0, legitimate.  Estimates that = -1/2, Ghat = 1/2, U = 0 throughout; no violations.
    t, G, iota = [Fr(-2), ONE], [ONE, ZERO], [1, 0]
    W = [t[i] + G[i] for i in range(2)]
    S = [Fr(-1), W[1]]
    U, that = [ZERO, ZERO], [Fr(-1, 2)] * 2
    want("range fails: avg(U - S), avg(that - t), avg(W - U), avg(W - S), frequency of illegitimate histories",
         (avg([U[i] - S[i] for i in range(2)]), avg([that[i] - t[i] for i in range(2)]), avg([W[i] - U[i] for i in range(2)]),
          avg([W[i] - S[i] for i in range(2)]), avg([Fr(x) for x in iota])), (ZERO, ZERO, ZERO, ZERO, HALF))
    return out, failures


def report():
    summary, failures = [], []
    cases, bad_gain, bad_t = per_decision()
    summary.append("(b): decisions %d, chosen takes avoidable gain %d, chosen not best in that among respecting actions %d"
                   % (cases, bad_gain, bad_t))
    if bad_gain or bad_t or not cases:
        failures.append("(b): %d and %d violations in %d decisions" % (bad_gain, bad_t, cases))
    n, bad_range, seqs, bad = frequency()
    summary.append("(a): realised decisions %d, with S above 1 - lam N: %d" % (n, bad_range))
    summary.append("(d): sequences %d, violations of eps * sum(iota) <= sum(W - S): %d" % (seqs, bad))
    if bad_range or bad or not seqs:
        failures.append("(a), (d): %d and %d violations" % (bad_range, bad))
    out, f2 = instances()
    return {"summary": summary + out, "failures": failures + f2}


if __name__ == "__main__":
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    raise SystemExit(1 if rep["failures"] else 0)
