"""Executable fixtures for the Normative Continuity freeze audit (29 Aug 2026).

A tiny reference model of the issue/prerequisite/matter layer of
`normative_continuity_refined (freeze).tex`, used to check the countermodels
and regression traces of the hostile proof pass. Standing (L_n, Permit, Due)
is not modelled: none of the fixtures needs it and none of the structural
theorems after Grounded Replay reads it.

Trace format: a list of batches; each batch is a list of records
    ("open",   q, parents)            parents = list of issues resolving into q
    ("resolve", q, successors)        successors must be opened in the same batch
    ("addpre", d, q, roots)           fresh prerequisite d on q, route roots
    ("droppre", d, q)
    ("met", d)                        Met_n(d) becomes true from the NEXT prefix on
    ("designate", q)
Positions: batch e_n is applied to prefix state n and yields prefix state n+1.
"""

from itertools import count


class Model:
    def __init__(self):
        self.O = set()            # outstanding at current prefix
        self.born_at = {}         # issue -> position of Q+
        self.parents = {}         # issue -> set of parents
        self.pre = {}             # issue -> set of active prerequisites
        self.roots = {}           # d -> route roots T_d
        self.owner = {}           # d -> q_d
        self.met = set()
        self.matters = set()
        self.M_birth = {}
        self.pending_met = set()
        self.n = 0
        self.violations = []

    # ---- derived relations at the current prefix ------------------------
    def desc(self, a, b):                      # a ⪯ b
        if a == b:
            return True
        return any(self.desc(a, p) for p in self.parents.get(b, ()))

    def live(self, m):
        return {q for q in self.O if self.desc(m, q)}

    def routes(self, d):
        return {r for r in self.O if any(self.desc(t, r) for t in self.roots[d])}

    def ready(self, q):
        return all(d in self.met for d in self.pre[q])

    def waits(self, q):
        out = set()
        for d in self.pre[q]:
            if d not in self.met:
                out |= self.routes(d)
        return out

    def reach(self, m):
        R, frontier = set(), list(self.live(m))
        while frontier:
            q = frontier.pop()
            if q in R:
                continue
            R.add(q)
            frontier.extend(self.waits(q))
        return R

    def on_cycle(self, q):
        seen, stack = set(), list(self.waits(q))
        while stack:
            r = stack.pop()
            if r == q:
                return True
            if r not in seen:
                seen.add(r)
                stack.extend(self.waits(r))
        return False

    def work(self, m):
        R = self.reach(m)
        return {q for q in R if self.ready(q) or self.on_cycle(q)}

    def noroute(self, m):
        return {d for q in self.reach(m) for d in self.pre[q]
                if d not in self.met and not self.routes(d)}

    # ---- applying one batch ------------------------------------------------
    def step(self, batch, gate="reach"):
        n = self.n
        opens = {r[1] for r in batch if r[0] == "open"}
        resolves = {r[1]: set(r[2]) for r in batch if r[0] == "resolve"}
        adds = [r for r in batch if r[0] == "addpre"]
        drops = [r for r in batch if r[0] == "droppre"]
        for q in resolves:
            assert q in self.O, f"n={n}: resolve of non-outstanding {q}"
            assert self.ready(q), f"n={n}: Req 10 violated, {q} not ready"
            assert resolves[q] <= opens, f"n={n}: Req 5 violated"
        for _, d, q, roots in adds:
            assert d not in self.roots, f"n={n}: prerequisite {d} re-added"
            assert q in self.O or q in opens, f"n={n}: Req 8 owner"
            assert set(roots) <= self.O | opens, f"n={n}: Req 8 roots"
        # the gate under test: Requirement 12 (reach) or the weaker Live gate
        for _, d, q, _ in adds:
            if q in self.O and q not in resolves:
                for m in self.matters:
                    rel = self.reach(m) if gate == "reach" else self.live(m)
                    if q in rel and not self.work(m):
                        self.violations.append((n, gate, d, q, m))
        # snapshot opportunity before mutating
        opp = {m: bool(self.work(m)) for m in self.matters}
        # mutate
        for q in opens:
            self.born_at[q] = n
            self.parents[q] = {p for p, S in resolves.items() if q in S}
            self.pre[q] = set()
        for q in resolves:
            self.O.discard(q)
            del self.pre[q]
        self.O |= opens
        for _, d, q in drops:
            self.pre[q].discard(d)
        for _, d, q, roots in adds:
            self.roots[d], self.owner[d] = set(roots), q
            self.pre[q].add(d)
        for r in batch:
            if r[0] == "met":
                self.met.add(r[1])
            if r[0] == "designate":
                self._add_matter(r[1], n + 1)
        for q in opens:
            if not self.parents[q]:
                self._add_matter(q, n + 1)
        self.n += 1
        return opp

    def _add_matter(self, q, birth):
        if q not in self.matters:
            self.matters.add(q)
            self.M_birth[q] = birth


def run(trace, gate="reach", tail=None, horizon=12):
    """Replay `trace`; if `tail` is given, repeat it after the trace up to horizon.
    Returns (model, per-position opportunity dict list)."""
    M, opps = Model(), []
    batches = list(trace)
    while len(batches) < horizon and tail is not None:
        batches.append(tail(len(batches)))
    for b in batches:
        opps.append(M.step(b, gate))
    return M, opps


# ---------------------------------------------------------------------------
# Fixture A — rotating prerequisite (the regression countermodel)
#   m1 = a  waits through d0 -> b1 forever;  b1 belongs to busy matter m2 = b.
#   From n>=2, b1's no-route prerequisite is withdrawn and replaced every batch.
#   Live gate: permitted (b1 ∈ Live(m2) only, m2 has work c) -> PW conclusion fails.
#   Reach gate: rejected at n=2 because b1 ∈ Reach(m1) and Work_2(m1) = ∅.
def fixture_A(n):
    return [("droppre", f"e{n-2}", "b1"), ("addpre", f"e{n-1}", "b1", [])]

TRACE_A = [
    [("open", "a", []), ("open", "b", [])],                       # e_0
    [("resolve", "b", ["b1", "c"]), ("open", "b1", ["b"]), ("open", "c", ["b"]),
     ("addpre", "d0", "a", ["b1"]), ("addpre", "e0", "b1", [])],  # e_1
]

# Fixture B — co-opened route root: Routes_1(d) = ∅ but Routes_2(d) = {t}.
TRACE_B = [
    [("open", "a", [])],
    [("open", "t", []), ("addpre", "d", "a", ["t"])],
    [],
]

# Fixture C — genuine no-route wait: PW must return d.
TRACE_C = [
    [("open", "a", [])],
    [("addpre", "d", "a", [])],
]

# Fixture D — route extinction after introduction: t resolves terminally,
#   then d is a no-route wait from the next prefix on (Lemma 3 as repaired).
TRACE_D = [
    [("open", "a", []), ("open", "t", [])],
    [("addpre", "d", "a", ["t"])],
    [("resolve", "t", [])],
    [],
]

# Fixture E — waiting cycle a <-> t counts as work at every position.
TRACE_E = [
    [("open", "a", []), ("open", "t", [])],
    [("addpre", "d", "a", ["t"]), ("addpre", "f", "t", ["a"])],
    [],
]

# Fixture F — Met at the same transition as a withdrawal elsewhere; branching
#   and merging of succession; designation of a descendant as a new matter.
TRACE_F = [
    [("open", "a", [])],
    [("addpre", "d1", "a", []), ("addpre", "d2", "a", [])],
    [("met", "d1"), ("droppre", "d2", "a")],
    [("resolve", "a", ["a1", "a2"]), ("open", "a1", ["a"]), ("open", "a2", ["a"]),
     ("designate", "a2")],
    [("resolve", "a1", ["a3"]), ("resolve", "a2", ["a3"]), ("open", "a3", ["a1", "a2"])],
]


def main():
    ok = True

    # A under the weak gate: no violation, m1 never has work after n=1, and no
    # single prerequisite is a persistent no-route wait.
    M, opps = run(TRACE_A, gate="live", tail=fixture_A, horizon=10)
    assert not M.violations, M.violations
    assert all(not o["a"] for o in opps[2:]) and M.live("a")
    # recompute no-route sets along the tail
    M2, _ = run(TRACE_A, gate="live", tail=fixture_A, horizon=6)
    nr6 = M2.noroute("a")
    M3, _ = run(TRACE_A, gate="live", tail=fixture_A, horizon=7)
    nr7 = M3.noroute("a")
    assert nr6 and nr7 and not (nr6 & nr7), (nr6, nr7)   # the wait keeps moving
    print("A/live : Live gate admits the rotation; Persistent-Wait conclusion fails")

    M, _ = run(TRACE_A, gate="reach", tail=fixture_A, horizon=4)
    assert M.violations and M.violations[0][:2] == (2, "reach"), M.violations
    assert M.violations[0][3:] == ("b1", "a")
    print("A/reach: rejected at n=2 on (b1, m1=a) by Requirement 12 alone")

    # B: the literal Lemma 3 fails at the introduction position.
    M, _ = run(TRACE_B[:1]); M.roots["d"] = {"t"}; r1 = M.routes("d")   # prefix 1
    M, _ = run(TRACE_B[:2]); r2 = M.routes("d")                          # prefix 2
    assert r1 == set() and r2 == {"t"}
    print("B      : Routes_1(d)=∅, Routes_2(d)={t}: Lemma 3 needs n after d's introduction")

    # C: no-route wait from n=2 on.
    M, opps = run(TRACE_C, tail=lambda n: [], horizon=5)
    assert M.noroute("a") == {"d"} and not opps[-1]["a"]
    print("C      : fixed no-route wait d, no work")

    # D: route extinction is permanent after introduction.
    M, _ = run(TRACE_D[:3]); assert M.routes("d") == set() and M.noroute("a") == {"d"}
    M, opps = run(TRACE_D); assert M.noroute("a") == {"d"} and opps[2]["a"]  # t was work
    print("D      : route t resolved (an opportunity), then d is no-route forever")

    # E: cycle is work forever.
    M, opps = run(TRACE_E, tail=lambda n: [], horizon=6)
    assert all(o["a"] and o["t"] for o in opps[2:])
    print("E      : 2-cycle counts as work at every position")

    # F: sanity of continuity bookkeeping.
    M, _ = run(TRACE_F)
    assert M.live("a") == {"a3"} and M.live("a2") == {"a3"} and M.M_birth["a2"] == 4
    assert not M.violations
    print("F      : branch, merge, same-transition Met/withdraw, designation OK")
    print("all fixtures pass" if ok else "FAIL")


if __name__ == "__main__":
    main()
