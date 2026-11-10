"""The abstract layer of DEFINITIONS.md §2: worlds, actions, goals as payoffs,
beliefs as subsets, disclosures as partitions, believed lies, steering by u.
Uniform prior; sums over W are compared as exact integers or Fractions."""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product


def subsets(n):
    return [frozenset(i for i in range(n) if m >> i & 1) for m in range(1, 1 << n)]


def partitions(n):
    """Every partition of range(n), as a tuple of frozensets."""
    def rec(i, blocks):
        if i == n:
            yield tuple(frozenset(b) for b in blocks)
            return
        for k in range(len(blocks)):
            yield from rec(i + 1, blocks[:k] + [blocks[k] + [i]] + blocks[k + 1:])
        yield from rec(i + 1, blocks + [[i]])
    return list(rec(0, []))


def goals(n, m, P):
    """Every payoff g[w][a] with values in P."""
    for flat in product(P, repeat=n * m):
        yield tuple(tuple(flat[w * m:(w + 1) * m]) for w in range(n))


def act(g, B):
    m = len(g[0])
    return max(range(m), key=lambda a: (sum(g[w][a] for w in B), -a))


def cell(f, w):
    return next(b for b in f if w in b)


def total_disclosure(g, f):
    return sum(g[w][act(g, cell(f, w))] for w in range(len(g)))


def total_claims(g, claim):
    return sum(g[w][act(g, claim[w])] for w in range(len(g)))


def coarsening(fine, coarse):
    """coarse is a coarsening of fine: every cell of fine lies in a cell of coarse."""
    return all(any(b <= c for c in coarse) for b in fine)


def c1a(n=3, m=3, P=(0, 1)):
    base = (frozenset(range(n)),)
    bad = [(g, f) for g in goals(n, m, P) for f in partitions(n)
           if total_disclosure(g, f) < total_disclosure(g, base)]
    return {"domain": "|W|=%d, |A|=%d, payoffs in %s: %d goals, %d disclosures"
                      % (n, m, list(P), len(P) ** (n * m), len(partitions(n))),
            "holds": not bad, "counterexamples": bad[:1]}


def c1b(n=4, m=2, P=(0, 1)):
    G = list(goals(n, m, P))
    parts = partitions(n)
    tot = {f: [total_disclosure(g, f) for g in G] for f in parts}
    bad = []
    for f in parts:
        for f2 in parts:
            dominates = all(x >= y for x, y in zip(tot[f], tot[f2]))
            if dominates != coarsening(f, f2):
                bad.append((f, f2))
    return {"domain": "|W|=%d, |A|=%d, payoffs in %s: %d goals, %d ordered pairs of disclosures"
                      % (n, m, list(P), len(G), len(parts) ** 2),
            "holds": not bad, "counterexamples": bad[:1]}


def lies(n):
    S = subsets(n)
    for claim in product(S, repeat=n):
        if any(w not in claim[w] for w in range(n)):
            yield claim


def c2(n=3, m=2, P=(0, 1, 2)):
    G = list(goals(n, m, P))
    parts = partitions(n)
    base = (frozenset(range(n)),)
    tb = [total_disclosure(g, base) for g in G]
    tp = {f: [total_disclosure(g, f) for g in G] for f in parts}
    no_fall, equal_withholding, rises, count = [], [], None, 0
    for claim in lies(n):
        count += 1
        tl = [total_claims(g, claim) for g in G]
        if not any(x < y for x, y in zip(tl, tb)):
            no_fall.append(claim)
        for f in parts:
            if tl == tp[f]:
                equal_withholding.append((claim, f))
        if rises is None:
            for g, x, y in zip(G, tl, tb):
                if x > y:
                    rises = (claim, g, Q(x, n), Q(y, n))
                    break
    return {"domain": "|W|=%d, |A|=%d, payoffs in %s: %d goals, %d believed lies, %d disclosures"
                      % (n, m, list(P), len(G), count, len(parts)),
            "a_holds": not no_fall, "a_counterexamples": no_fall[:1],
            "b_holds": not equal_withholding, "b_counterexamples": equal_withholding[:1],
            "a_lie_that_raises": rises}


def inducible(g):
    n = len(g)
    return sorted({act(g, B) for B in subsets(n)})


def steered_total(g, u):
    ind = inducible(g)
    return sum(g[w][max(ind, key=lambda a: (u[w][a], -a))] for w in range(len(g)))


def c4(n=4, m=2, P=(0, 1)):
    G = list(goals(n, m, P))
    drivers = {"full": tuple(frozenset([w]) for w in range(n)),
               "one bit": (frozenset([0, 1]), frozenset([2, 3])),
               "baseline": (frozenset(range(n)),)}
    neg = lambda g: tuple(tuple(-x for x in row) for row in g)
    S_self = {g: steered_total(g, g) for g in G}
    S_opp = {g: steered_total(g, neg(g)) for g in G}
    S_all = {g: min(steered_total(g, u) for u in G) for g in G}
    families = {"opposed": S_opp, "aligned": S_self, "all": S_all}
    out = {}
    for dn, d in drivers.items():
        for fn, S in families.items():
            weak_bad = [g for g in G if total_disclosure(g, d) < S[g]]
            strict = [g for g in G if total_disclosure(g, d) > S[g]]
            out[(dn, fn)] = {"weak": not weak_bad, "strict": bool(strict),
                             "weak_counterexample": weak_bad[:1],
                             "counterexample_values": [(Q(total_disclosure(g, d), n), Q(S[g], n))
                                                       for g in weak_bad[:1]]}
    return {"domain": "|W|=%d, |A|=%d, payoffs in %s: %d goals; drivers full, one bit, baseline; "
                      "families opposed {-g}, aligned {g}, all (U(g) = G)" % (n, m, list(P), len(G)),
            "table": out}


def c5c(n=3, m=2, P=(0, 1)):
    G = list(goals(n, m, P))
    S = subsets(n)
    bad = [(B, B2) for B in S for B2 in S if B != B2 and all(act(g, B) == act(g, B2) for g in G)]
    return {"domain": "|W|=%d, |A|=%d, payoffs in %s: %d goals, %d beliefs" % (n, m, list(P), len(G), len(S)),
            "holds": not bad, "counterexamples": bad[:1]}
