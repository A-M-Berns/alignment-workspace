"""An executable model of the generic integrity conditions I1-I9 of `TARGET.md`.

The model follows the Lean `DefeatTrace` of
`lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` section 5 clause by
clause, so a history accepted here is one the Lean structure admits. Where the Lean
leaves something to an evaluator-supplied parameter (the licence relation `Li`), the
model takes the same thing as a parameter of `check`, because attack A11 turns on it.

Batch record grammar (a history is a list of batches, a batch a list of records):

    ("open",    q, anchor, parents, opener [, load])
        load: Fraction of anchored obligation the issue carries at birth; default 0
    ("resolve", q, successors, kind, resolver [, receipt])
        kind = ("answer",) | ("dispose", grounds) | ("settle", fact)
        grounds: iterable of ("issue", q') / ("settled", s)
        receipt: Fraction share of q's load the resolver claims answered; default 1
    ("settle",  s)                  the world settles fact s from the NEXT prefix on
    ("addpre",  d, q, roots)
    ("droppre", d, q)

`Li` is a dict  licence_issue -> set of (participant, anchor)  — the Lean `Licence`.

Exact arithmetic: every load is a `fractions.Fraction`.
"""
from __future__ import annotations

from fractions import Fraction

ANSWER, DISPOSE, SETTLE = "answer", "dispose", "settle"
DISCHARGING = frozenset({ANSWER, SETTLE})


def issue(q):
    return ("issue", q)


def settled(s):
    return ("settled", s)


class Refused(Exception):
    """A batch one of I1-I9 refuses. `code` names the condition and clause."""

    def __init__(self, code, detail):
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class Trace:
    """One history replayed under I1-I9. Raises `Refused` at the first violation."""

    def __init__(self, Li=None):
        self.Li = {q: set(v) for q, v in (Li or {}).items()}
        self.n = 0
        self.O = set()
        self.born_at = {}
        self.resolved_at = {}
        self.par = {}
        self.anchor = {}
        self.opener = {}
        self.kind = {}
        self.resolver = {}
        self.pre = {}
        self.roots = {}
        self.intro = {}
        self.Settled = set()
        self._pending = set()
        self.edges = []          # (n, q, grounds, q') disposal edges
        # exact load ledger: I1-I9 never read it; the attacks do
        self.load = {}
        self.answered = Fraction(0)
        self.settled_mass = Fraction(0)
        self.closed_by = {}      # q -> fact, for settle-kind resolutions
        self.standing_snapshots = []   # (n, q, q', standers on q' at n) per disposal

    # ---- derived relations, named as in the Lean --------------------------
    def anc(self, m, q):
        return m == q or any(self.anc(m, p) for p in self.par.get(q, ()))

    def live(self, m):
        return {q for q in self.O if self.anc(m, q)}

    def routes(self, d):
        return {r for r in self.O if any(self.anc(t, r) for t in self.roots[d])}

    def met(self, d, n=None):
        n = self.n if n is None else n
        out = True
        for t in self.roots[d]:
            k = self.resolved_at.get(t)
            out = out and k is not None and k < n and self.kind[(k, t)][0] in DISCHARGING
        return out

    def ready(self, q):
        return all(self.met(d) for d in self.pre.get(q, ()))

    def grounded(self, g, n):
        tag, v = g
        if tag == "issue":
            return v in self.born_at and self.born_at[v] < n
        if tag == "settled":
            return v in self.Settled
        raise Refused("bad-ground", repr(g))

    def stands_for(self, b, anchor):
        """Lean `standsFor Li n b anchor`: a live licence issue licenses b for anchor."""
        return any((b, anchor) in self.Li.get(l, ()) for l in self.O)

    def standers(self, anchor):
        return {b for l in self.O for (b, a) in self.Li.get(l, ()) if a == anchor}

    def parentless_roots(self, q):
        """Lean `grounded_replay`: the parentless ancestors of q."""
        ps = self.par.get(q, set())
        if not ps:
            return {q}
        return set().union(*(self.parentless_roots(p) for p in ps))

    # ---- I7: answerable disposal, clause by clause -----------------------
    def check_answerable(self, n, q, grounds, q_succ, resolver):
        for g in grounds:
            if not self.grounded(g, n):
                raise Refused("I4-ungrounded", f"n={n}: {q} cites {g}")
        if issue(q) in grounds:
            raise Refused("I6-self-grounded", f"n={n}: {q} cites itself")
        contested = any(b != resolver for b in self.standers(self.anchor[q_succ]))
        if not contested:
            raise Refused("I7-uncontested", f"n={n}: only {resolver} stands on {q_succ}")
        foreign = any(tag == "settled" or self.opener[v] != resolver
                      for (tag, v) in grounds)
        if not foreign:
            raise Refused("I7-self-grounds", f"n={n}: every ground of {q} is {resolver}'s")

    def answerable_for(self, q_succ, P):
        """Lean `AnswerableFor P`: P stands on the successor at the disposal's prefix.
        Read at the batch of the disposal, so call it from inside `step`'s checks or
        on a trace stopped at that prefix."""
        return P in self.standers(self.anchor[q_succ])

    # ---- one batch --------------------------------------------------------
    def step(self, batch):
        n = self.n
        opens = {r[1]: r for r in batch if r[0] == "open"}
        resolves = {r[1]: r for r in batch if r[0] == "resolve"}
        for r in batch:
            if r[0] == "settle":
                self._pending.add(r[1])
        for q, rec in opens.items():
            if q in self.born_at:
                raise Refused("I1-born-twice", f"n={n}: {q}")
            for p in rec[3]:
                if p not in resolves:
                    raise Refused("I5-parent-not-resolved-here", f"n={n}: {q} <- {p}")
        principal_edges = []
        for q, rec in resolves.items():
            _, _, succs, kind, resolver = rec[:5]
            if q not in self.O:
                raise Refused("I1-resolve-nonoutstanding", f"n={n}: {q}")
            if not self.ready(q):
                raise Refused("I7-not-ready", f"n={n}: {q}")
            for s in succs:
                if s not in opens or q not in opens[s][3]:
                    raise Refused("I5-successor-not-fresh", f"n={n}: {q} -> {s}")
            if kind[0] == DISPOSE:
                if not succs:
                    raise Refused("I7-dispose-without-successor", f"n={n}: {q}")
                for s in succs:
                    self.anchor[s] = opens[s][2]
                    self.opener[s] = opens[s][4]
                for s in succs:
                    self.check_answerable(n, q, frozenset(kind[1]), s, resolver)
                    principal_edges.append((n, q, s, self.standers(self.anchor[s])))
            elif kind[0] == SETTLE:
                if kind[1] not in self.Settled:
                    raise Refused("I9-unsettled", f"n={n}: {q} on {kind[1]}")
            elif kind[0] != ANSWER:
                raise Refused("I7-fourth-kind", f"n={n}: {kind[0]!r}")
        for _, d, q, roots in (r for r in batch if r[0] == "addpre"):
            if d in self.roots:
                raise Refused("I1-prerequisite-reused", f"n={n}: {d}")
            if not (q in self.O or q in opens):
                raise Refused("I1-prerequisite-owner", f"n={n}: {d} on {q}")
            if not set(roots) <= self.O | set(opens):
                raise Refused("I5-route-root-not-live", f"n={n}: {d} roots {roots}")
        # mutate
        for q, rec in opens.items():
            self.born_at[q] = n
            self.par[q] = set(rec[3])
            self.anchor[q] = rec[2]
            self.opener[q] = rec[4]
            self.pre[q] = set()
            self.load[q] = Fraction(rec[5]) if len(rec) > 5 else Fraction(0)
        for q, rec in resolves.items():
            _, _, succs, kind, resolver = rec[:5]
            receipt = Fraction(rec[5]) if len(rec) > 5 else Fraction(1)
            self.kind[(n, q)] = kind
            self.resolver[(n, q)] = resolver
            self.resolved_at[q] = n
            mass = self.load.pop(q, Fraction(0))
            if kind[0] == ANSWER:
                paid = mass * receipt
                self.answered += paid
                rest = mass - paid
            elif kind[0] == SETTLE:
                self.settled_mass += mass
                self.closed_by[q] = kind[1]
                rest = Fraction(0)
            else:
                rest = mass
                for s in succs:
                    self.edges.append((n, q, frozenset(kind[1]), s))
            for s in succs:
                self.load[s] = self.load.get(s, Fraction(0)) + rest / Fraction(len(succs))
            self.O.discard(q)
        self.O |= set(opens)
        for _, d, q in (r for r in batch if r[0] == "droppre"):
            self.pre[q].discard(d)
        for _, d, q, roots in (r for r in batch if r[0] == "addpre"):
            self.roots[d], self.intro[d] = set(roots), n
            self.pre[q].add(d)
        self.Settled |= self._pending
        self._pending = set()
        self.standing_snapshots += principal_edges
        self.n += 1
        return self

    def run(self, history):
        for batch in batches_of(history):
            self.step(batch)
        return self

    # ---- accounts the attacks read ----------------------------------------
    def open_mass(self):
        return sum(self.load.values(), Fraction(0))

    def conserved(self, initial):
        """The account I1-I9 can see: nothing left except into answered or settled."""
        return self.open_mass() + self.answered + self.settled_mass == Fraction(initial)

    def answers_by(self):
        return {self.resolver[k] for k, kind in self.kind.items() if kind[0] == ANSWER}


def batches_of(history):
    return list(history)


def check(history, Li=None):
    """Replay `history` under I1-I9 with licence relation `Li`. Returns the trace, or
    raises `Refused` naming the first clause violated."""
    return Trace(Li).run(history)


def refused_by(history, Li=None):
    try:
        check(history, Li)
    except Refused as e:
        return e.code
    return None
