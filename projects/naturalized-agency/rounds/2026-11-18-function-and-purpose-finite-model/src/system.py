"""Finite systems of parts, givens and processes; self-maintaining sets; dependence.

A process is a pair (condition, outputs).  A condition is a list of clauses, each a set
of parts and givens; it holds on X when some clause lies inside X together with the
givens.  A process whose condition holds maintains its outputs for one step.
"""
from fractions import Fraction
from itertools import chain, combinations


def subsets(xs):
    xs = list(xs)
    return (frozenset(c) for c in chain.from_iterable(combinations(xs, r) for r in range(len(xs) + 1)))


def k_of(k, xs, also=()):
    """Clauses for 'at least k of xs, together with everything in also'."""
    return [frozenset(c) | frozenset(also) for c in combinations(xs, k)]


class System:
    def __init__(self, parts, givens, procs):
        self.P = frozenset(parts)
        self.F = frozenset(givens)
        self.procs = {n: ([frozenset(c) for c in cond], frozenset(out)) for n, (cond, out) in procs.items()}

    def phi(self, X):
        """Parts maintained for the next step when exactly X is present."""
        avail = frozenset(X) | self.F
        out = set()
        for cond, o in self.procs.values():
            if any(c <= avail for c in cond):
                out |= o
        return frozenset(out)

    def G(self, X):
        """The greatest self-maintaining subset of X."""
        X = frozenset(X)
        while True:
            Y = X & self.phi(X)
            if Y == X:
                return X
            X = Y

    def is_self_maintaining(self, X):
        return frozenset(X) <= self.phi(X)

    def self_maintaining_sets(self):
        return [X for X in subsets(self.P) if X <= self.phi(X)]

    def from_givens(self):
        """Parts producible from the givens alone."""
        X = frozenset()
        while True:
            Y = X | self.phi(X)
            if Y == X:
                return X
            X = Y

    def necessity(self, S):
        """necessity[q] = the other parts of S that do not survive the removal of q."""
        return {q: S - self.G(S - {q}) - {q} for q in S}

    def relevance(self, S):
        """relevance[q] = parts p for which some removal T leaves p alive and T with q does not."""
        rel = {q: set() for q in S}
        for q in S:
            for T in subsets(S - {q}):
                rel[q] |= (self.G(S - T) - self.G(S - T - {q})) - {q}
        return rel

    def interchangeable(self, a, b):
        def sw(s):
            return frozenset(b if x == a else a if x == b else x for x in s)
        new = {n: (sorted(map(sorted, (sw(c) for c in cond))), sorted(sw(o))) for n, (cond, o) in self.procs.items()}
        old = {n: (sorted(map(sorted, cond)), sorted(o)) for n, (cond, o) in self.procs.items()}
        return new == old

    def kinds(self, S):
        """Classes of parts of S under the transitive closure of pairwise interchangeability."""
        cls = {x: {x} for x in S}
        for a, b in combinations(sorted(S), 2):
            if self.interchangeable(a, b):
                u = cls[a] | cls[b]
                for x in u:
                    cls[x] = u
        return {frozenset(c) for c in cls.values()}


def strongly_connected(nodes, edges):
    nodes = list(nodes)
    reach = {n: {n} for n in nodes}
    changed = True
    while changed:
        changed = False
        for n in nodes:
            new = set(reach[n])
            for m in list(reach[n]):
                new |= edges.get(m, set())
            if new != reach[n]:
                reach[n] = new
                changed = True
    return {frozenset(m for m in reach[n] if n in reach[m]) for n in nodes}


def functions(s):
    """Parts ascribed a function: relevant to, and depended on by, others of a
    mutual-relevance class holding at least two kinds of such parts."""
    S = s.G(s.P)
    free = s.from_givens()
    rel = s.relevance(S)
    kinds = s.kinds(S)
    out = set()
    for K in strongly_connected(S, rel):
        if len(K) < 2:
            continue
        cand = {q for q in K if rel[q] and q not in free and any(q in rel[r] for r in K if r != q)}
        if len({k & K for k in kinds if k & cand}) >= 2:
            out |= cand
    return out


def influence(s, rate):
    """I[q][p] = P(p survives | q has not failed) - P(p survives | q has failed),
    the other parts of the greatest self-maintaining set failing independently."""
    S = sorted(s.G(s.P))
    full = frozenset(S)
    I = {q: {p: Fraction(0) for p in S if p != q} for q in S}
    for q in S:
        others = [x for x in S if x != q]
        for T in subsets(others):
            w = Fraction(1)
            for x in others:
                w *= rate[x] if x in T else 1 - rate[x]
            a = s.G(full - T)
            b = s.G(full - T - {q})
            for p in others:
                I[q][p] += w * ((p in a) - (p in b))
    return I


def split(s, q, mode):
    """Replace q by q_1, q_2.  mode 'all': both are needed wherever q was.
    mode 'any': either serves wherever q did.  Every process maintaining q maintains both."""
    subs = [q + "_1", q + "_2"]
    procs = {}
    for n, (cond, o) in s.procs.items():
        new = []
        for c in cond:
            if q not in c:
                new.append(c)
            elif mode == "all":
                new.append((c - {q}) | set(subs))
            else:
                new += [(c - {q}) | {x} for x in subs]
        procs[n] = (new, (o - {q}) | set(subs) if q in o else o)
    return System((s.P - {q}) | set(subs), s.F, procs), subs


def merge(s, a, b, name):
    r = lambda xs: frozenset(name if x in (a, b) else x for x in xs)
    return System(r(s.P), s.F, {n: ([r(c) for c in cond], r(o)) for n, (cond, o) in s.procs.items()})
