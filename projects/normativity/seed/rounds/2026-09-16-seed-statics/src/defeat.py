"""What the landed defeat calculus determines, against the grounded extension.

The landed calculus (`NormativeContinuity.lean` §5; `DefeatTrace`, `Kind`, `Answerable`)
is a *trace discipline*: a resolution of an issue is an `answer`, an answerable
`dispose G` with a fresh successor carrying the load, or a `settle`.  D1 requires every
ground to be *available* at the prefix (born strictly earlier, or settled) — not
vindicated.  Nothing in it computes which arguments survive from the attack structure.

This module has two objects:

* `Graph`: warrants and defeaters as nodes with an attack relation, and the grounded
  extension as the least fixed point of the characteristic function on a finite graph.
* `Trace`: a minimal replay of the landed discipline — issues born at batches, disposals
  admissible when their grounds were born strictly earlier — reporting the live set.

The result the fixture exhibits: the live set is a function of the trace (which
disposals were made, in which batch), the grounded extension is a function of the graph,
and admissible traces exist whose live set is not the grounded extension.
"""

from __future__ import annotations


class Graph:
    def __init__(self, nodes, attacks):
        self.nodes = list(nodes)
        self.attacks = set(attacks)          # (attacker, target)

    def attackers(self, x):
        return {a for a, t in self.attacks if t == x}

    def defended(self, S, x):
        """Every attacker of x is attacked by some member of S."""
        return all(any((s, a) in self.attacks for s in S) for a in self.attackers(x))

    def characteristic(self, S):
        return {x for x in self.nodes if self.defended(S, x)}

    def grounded(self):
        S = set()
        while True:
            T = self.characteristic(S)
            if T == S:
                return S
            S = T

    def conflict_free(self, S):
        return not any((a, t) in self.attacks for a in S for t in S)

    def admissible(self, S):
        return self.conflict_free(S) and all(self.defended(S, x) for x in S)

    def preferred(self):
        """Maximal admissible sets, by enumeration (finite graphs only)."""
        from itertools import combinations
        adm = []
        for k in range(len(self.nodes) + 1):
            for c in combinations(self.nodes, k):
                if self.admissible(set(c)):
                    adm.append(frozenset(c))
        return [S for S in adm if not any(S < T for T in adm)]


class Trace:
    """Issues are born at batch indices; a disposal at batch n of issue q on grounds G
    needs every ground born strictly before n (D1), creates a successor born at n (D2),
    and is made by a resolver distinct from at least one ground's opener with someone
    else standing on the successor (D3, modelled as declared data)."""

    def __init__(self):
        self.born = {}          # issue -> batch
        self.resolved = {}      # issue -> (batch, kind, grounds, successor)
        self.opener = {}
        self.log = []

    def open(self, q, n, opener):
        assert q not in self.born
        self.born[q] = n
        self.opener[q] = opener
        self.log.append(("open", q, n, opener))

    def live(self, n):
        return {q for q, b in self.born.items() if b < n and q not in self.resolved
                or (q in self.resolved and self.resolved[q][0] >= n and b < n)}

    def dispose(self, q, n, grounds, resolver, successor, stander):
        assert q in self.born and self.born[q] < n and q not in self.resolved
        for g in grounds:
            assert g in self.born and self.born[g] < n, "D1: ground not available"
            assert g != q, "D1: self-grounding"
        assert any(self.opener[g] != resolver for g in grounds), "D3: foreign ground"
        assert stander != resolver, "D3: contested"
        self.open(successor, n, stander)
        self.resolved[q] = (n, "dispose", tuple(grounds), successor)
        self.log.append(("dispose", q, n, tuple(grounds), resolver, successor))

    def answer(self, q, n, resolver):
        assert q in self.born and self.born[q] < n and q not in self.resolved
        self.resolved[q] = (n, "answer", (), None)
        self.log.append(("answer", q, n, resolver))

    def live_at_end(self):
        return {q for q in self.born if q not in self.resolved}
