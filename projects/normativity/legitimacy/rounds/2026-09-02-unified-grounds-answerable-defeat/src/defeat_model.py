"""The unified-grounds trace as one executable model, with answerable disposal.

Extends the settled Normative Continuity model (`2026-08-30-normative-continuity-
settlement/src/settled_model.py`) by the round's three changes:

1. **One ground type.** `Ground = ("issue", q) | ("settled", s)`. Standing occurrences
   and rule revisions are *issues* of a licence kind on the same trace, so `Ladd` is
   birth, `Ldel` is resolution, `grounds` is `par`, and freshness is birth uniqueness.
   `Settled` is a monotone predicate on settlement facts belonging to no participant's
   write set.
2. **Resolution kinds.** Every resolution carries `answer`, `dispose G`, or
   `settle s` — three, and deliberately not four. Only `answer` and `settle`
   discharge; `dispose` *moves* the debt onto a fresh successor. This is the Defeat
   Principle, and it is the model's central invariant.
3. **`Met` is a definition, not a judgment.** A prerequisite is met exactly when every
   route root was resolved strictly earlier by answer or settlement. A disposed root
   meets nothing, and its route survives into the successor.

Answerable disposal (D1-D3) and the defeat-disciplined trace are checked per batch.
Laundering is a walk in the disposal graph whose edges, grounds and standings all
belong to one participant; `laundering_walks` finds them.

Exact arithmetic throughout (`AGENTS.md` standard 2): every quantity is `Fraction`.

Batch record kinds, extending the settled model's:

    ("open", q, tau, x, kappa, parents, opener)
    ("resolve", q, successors, kind, resolver)
        kind = ("answer",) | ("dispose", grounds) | ("settle", fact)
        grounds: iterable of ("issue", q') / ("settled", s)
    ("addpre", d, q, roots)
    ("droppre", d, q)
    ("settle", s)                 the world settles fact s, from the NEXT prefix on
    ("designate", q)

`("met", d)` is gone: `Met` is computed, which is change 3.
"""
from __future__ import annotations

from fractions import Fraction


ANSWER = "answer"
DISPOSE = "dispose"
SETTLE = "settle"

DISCHARGING = frozenset({ANSWER, SETTLE})


def issue(q):
    """The ground that is a prior issue."""
    return ("issue", q)


def settled(s):
    """The ground that is a settlement fact."""
    return ("settled", s)


class DefeatViolation(Exception):
    """A batch the specification refuses. Carries the clause that refused it."""

    def __init__(self, code, detail):
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class DefeatModel:
    """One trace over the unified ground type.

    `settled_writer` names the participant whose writes may set `Settled`, or `None`
    for the intended case in which settlement is nobody's to write. Fixture
    `settlement_written_by_disposer` sets it to test the necessity of independence.
    """

    def __init__(self, licences=None, settled_writer=None):
        # --- issue layer (unified: licence occurrences are issues too) ----------
        self.O = set()
        self.born_at = {}
        self.parents = {}
        self.pre = {}
        self.roots = {}
        self.owner = {}
        self.matters = set()
        # --- unified additions --------------------------------------------------
        self.kind = {}            # (n, q) -> ("answer",) | ("dispose", frozenset) | ("settle", s)
        self.resolver = {}        # (n, q) -> participant
        self.opener = {}          # q -> participant
        self.resolved_at = {}     # q -> n
        self.Settled = set()      # settlement facts settled so far
        self.pending_settled = set()
        self.settled_writer = settled_writer
        self.licences = dict(licences or {})   # q -> set of (kappa, tau, x)
        self.anchor = {}          # q -> (tau, x, kappa)
        self.disposal_edges = []  # (q, q', resolver, grounds)
        self.n = 0
        self.violations = []

    # ---- derived relations -------------------------------------------------
    def desc(self, a, b):
        if a == b:
            return True
        return any(self.desc(a, p) for p in self.parents.get(b, ()))

    def live(self, m):
        return {q for q in self.O if self.desc(m, q)}

    def routes(self, d):
        return {r for r in self.O if any(self.desc(t, r) for t in self.roots[d])}

    def discharged_before(self, t, n):
        """`t` was resolved strictly before `n` by answer or settlement."""
        k = self.resolved_at.get(t)
        if k is None or k >= n:
            return False
        return self.kind[(k, t)][0] in DISCHARGING

    def met(self, d, n=None):
        """Change 3: `Met` is a definition, and a disposed root meets nothing."""
        n = self.n if n is None else n
        return all(self.discharged_before(t, n) for t in self.roots[d])

    def ready(self, q):
        return all(self.met(d) for d in self.pre[q])

    def waits(self, q):
        out = set()
        for d in self.pre[q]:
            if not self.met(d):
                out |= self.routes(d)
        return out

    # ---- grounds -----------------------------------------------------------
    def grounded(self, g, n=None):
        """`Grounded n g`: an issue in the record strictly before `n`, or a settled
        fact. Note what this does *and does not* refuse — see `no_self_grounding`."""
        n = self.n if n is None else n
        tag, v = g
        if tag == "issue":
            j = self.born_at.get(v)
            return j is not None and j < n
        if tag == "settled":
            return v in self.Settled
        raise DefeatViolation("bad-ground", f"unknown ground tag {tag!r}")

    def stands_for(self, kappa, tau, x):
        """Standing is now a filter on live issues, not a separate `L_n`."""
        return any((kappa, tau, x) in self.licences.get(q, ()) for q in self.O)

    def ancestor_tree(self, q):
        """Grounded Replay, unified: the parentless ancestors of `q`."""
        seen, stack, roots = set(), [q], set()
        while stack:
            r = stack.pop()
            if r in seen:
                continue
            seen.add(r)
            ps = self.parents.get(r, set())
            if not ps:
                roots.add(r)
            else:
                stack.extend(ps)
        return roots

    # ---- answerable disposal ------------------------------------------------
    def check_answerable(self, n, q, grounds, successors, resolver):
        """D1-D3. Raises `DefeatViolation` naming the clause that refused."""
        # D1 grounded
        for g in grounds:
            if not self.grounded(g, n):
                raise DefeatViolation("D1-ungrounded", f"n={n}: {q} cites {g}")
        # D1, the clause ancestry does not supply
        if issue(q) in grounds:
            raise DefeatViolation("D1-self-grounded", f"n={n}: {q} cites itself")
        # D2 routed: a fresh successor inheriting q's load
        if not successors:
            raise DefeatViolation("D2-unrouted", f"n={n}: disposal of {q} opens no successor")
        # D3 separated
        contested = any(
            self.anchor.get(s) and self.stands_for_other(s, resolver) for s in successors
        )
        if not contested:
            raise DefeatViolation(
                "D3-uncontested", f"n={n}: nobody but {resolver} stands on {sorted(successors)}"
            )
        foreign = any(
            tag == "issue" and self.opener.get(v) not in (None, resolver)
            for (tag, v) in grounds
        )
        if not foreign:
            raise DefeatViolation(
                "D3-self-grounds", f"n={n}: every ground of {q} was opened by {resolver}"
            )

    def stands_for_other(self, s, resolver):
        """Someone other than `resolver` has standing on successor `s`."""
        tau, x, _ = self.anchor[s]
        holders = {
            self.opener[q]
            for q in self.O
            if any(t == tau and xx == x for (_, t, xx) in self.licences.get(q, ()))
        }
        return bool(holders - {resolver})

    # ---- one batch ----------------------------------------------------------
    def step(self, batch):
        n = self.n
        opens = {r[1]: r for r in batch if r[0] == "open"}
        resolves = {r[1]: r for r in batch if r[0] == "resolve"}

        # settlement is applied from the next prefix, and belongs to nobody
        for r in batch:
            if r[0] == "settle":
                self.pending_settled.add(r[1])

        for q, rec in resolves.items():
            _, _, successors, kind, resolver = rec
            successors = set(successors)
            if q not in self.O:
                raise DefeatViolation("resolve-nonoutstanding", f"n={n}: {q}")
            if not self.ready(q):
                raise DefeatViolation("Req10-not-ready", f"n={n}: {q} not ready")
            if not successors <= set(opens):
                raise DefeatViolation("Req5-successor-not-fresh", f"n={n}: {q}")
            if kind[0] == DISPOSE:
                grounds = frozenset(kind[1])
                # the one new structural requirement
                if not successors:
                    raise DefeatViolation(
                        "dispose-successor", f"n={n}: disposal of {q} opens no successor"
                    )
                # anchors of the successors must exist before D3 can read them
                for s in successors:
                    orec = opens[s]
                    self.anchor[s] = (orec[2], orec[3], orec[4])
                    self.opener[s] = orec[6]
                self.check_answerable(n, q, grounds, successors, resolver)
            elif kind[0] == SETTLE:
                fact = kind[1]
                if fact not in self.Settled:
                    raise DefeatViolation(
                        "settle-unsettled", f"n={n}: {q} settles unsettled {fact}"
                    )
                if self.settled_writer is not None and self.settled_writer == resolver:
                    raise DefeatViolation(
                        "settlement-not-independent",
                        f"n={n}: {resolver} both settled and resolved on it",
                    )
            elif kind[0] != ANSWER:
                raise DefeatViolation("bad-kind", f"n={n}: {kind[0]!r} is not one of three")

        for _, d, q, roots in [r for r in batch if r[0] == "addpre"]:
            if d in self.roots:
                raise DefeatViolation("pre-reused", f"n={n}: {d}")
            if not (q in self.O or q in opens):
                raise DefeatViolation("Req8-owner", f"n={n}: {d} on {q}")
            if not set(roots) <= self.O | set(opens):
                raise DefeatViolation("Req8-roots", f"n={n}: {d}")

        # --- mutate -----------------------------------------------------------
        for q, rec in opens.items():
            if q in self.born_at:
                raise DefeatViolation("born-twice", f"n={n}: {q}")
            self.born_at[q] = n
            self.parents[q] = {p for p, r in resolves.items() if q in set(r[2])}
            self.pre[q] = set()
            self.anchor[q] = (rec[2], rec[3], rec[4])
            self.opener[q] = rec[6]
        for q, rec in resolves.items():
            _, _, successors, kind, resolver = rec
            self.kind[(n, q)] = kind
            self.resolver[(n, q)] = resolver
            self.resolved_at[q] = n
            if kind[0] == DISPOSE:
                for s in successors:
                    self.disposal_edges.append((q, s, resolver, frozenset(kind[1])))
            self.O.discard(q)
            del self.pre[q]
        self.O |= set(opens)
        for _, d, q in [r for r in batch if r[0] == "droppre"]:
            self.pre[q].discard(d)
        for _, d, q, roots in [r for r in batch if r[0] == "addpre"]:
            self.roots[d], self.owner[d] = set(roots), q
            self.pre[q].add(d)
        for r in batch:
            if r[0] == "designate":
                self.matters.add(r[1])
        for q in opens:
            if not self.parents[q]:
                self.matters.add(q)
        self.Settled |= self.pending_settled
        self.pending_settled = set()
        self.n += 1
        return self

    # ---- laundering ---------------------------------------------------------
    def laundering_walks(self):
        """A laundering walk: a disposal walk of length >= 1 whose edges, grounds and
        standings all belong to one participant. Separation (D3) is what forbids it,
        so on a disciplined trace this is empty — see `test_separation_forbids`."""
        found = []
        by_source = {}
        for (q, s, r, g) in self.disposal_edges:
            by_source.setdefault(q, []).append((q, s, r, g))

        def extend(path, actor):
            tail = path[-1][1]
            found.append((actor, list(path)))
            for edge in by_source.get(tail, ()):
                if edge[2] != actor:
                    continue
                if any(self.opener.get(v) not in (None, actor)
                       for (tag, v) in edge[3] if tag == "issue"):
                    continue
                extend(path + [edge], actor)

        for edge in self.disposal_edges:
            actor = edge[2]
            if any(self.opener.get(v) not in (None, actor)
                   for (tag, v) in edge[3] if tag == "issue"):
                continue
            extend([edge], actor)
        return [(a, p) for (a, p) in found if len(p) >= 1]

    def alternating_walks(self):
        """A walk whose consecutive edges alternate resolver. Each edge can satisfy
        D3 — the *other* participant supplies the foreign ground and the standing —
        while the pair as a coalition launders. This is the round's finding."""
        out = []
        by_source = {}
        for e in self.disposal_edges:
            by_source.setdefault(e[0], []).append(e)
        for e in self.disposal_edges:
            for f in by_source.get(e[1], ()):
                if f[2] != e[2]:
                    out.append([e, f])
        return out


# ---------------------------------------------------------------------------
# Mass: the service layer's two fates, and disposal as a claim-to-claim step.
# ---------------------------------------------------------------------------

class MassLedger:
    """Numeric obligation mass with the Defeat Principle as its invariant.

    `open + answered + settled == initial` at every prefix, and disposal contributes
    zero to either terminal fate: it moves mass along a disposal edge. `terminal`
    pushes mass forward along disposal chains, which is the terminal claim measure
    `mu-tilde`; the push is a transport step with `L = 1`, `eps = 0`.
    """

    def __init__(self, initial):
        self.initial = {q: Fraction(v) for q, v in initial.items()}
        self.mass = dict(self.initial)
        self.answered = Fraction(0)
        self.settled = Fraction(0)
        self.moved = Fraction(0)
        self.edges = []

    def answer(self, q):
        self.answered += self.mass.pop(q, Fraction(0))

    def settle(self, q):
        self.settled += self.mass.pop(q, Fraction(0))

    def dispose(self, q, successors):
        """Split `q`'s mass evenly across its successors. Nothing is destroyed."""
        m = self.mass.pop(q, Fraction(0))
        if not successors:
            raise DefeatViolation("dispose-successor", f"{q} disposed with no successor")
        share = m / Fraction(len(successors))
        for s in successors:
            self.mass[s] = self.mass.get(s, Fraction(0)) + share
            self.edges.append((q, s, share))
        self.moved += m

    def open_mass(self):
        return sum(self.mass.values(), Fraction(0))

    def conserved(self):
        """T1, the service layer: open == initial - answered - settled."""
        total = sum(self.initial.values(), Fraction(0))
        return self.open_mass() == total - self.answered - self.settled

    def contest_residual(self, total=None):
        """kappa: mass sitting in open successors of disposals, over total."""
        total = total or sum(self.initial.values(), Fraction(0))
        if total == 0:
            return Fraction(0)
        contested = sum(
            (self.mass.get(s, Fraction(0)) for (_, s, _) in self.edges), Fraction(0)
        )
        return contested / total
