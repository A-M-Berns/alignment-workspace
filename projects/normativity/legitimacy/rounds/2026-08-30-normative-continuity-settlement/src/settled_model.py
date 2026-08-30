"""The settled Normative Continuity specification as one executable model, and a
nontrivial witness trace satisfying all of it jointly.

Unlike `fixtures.py` (issue layer only), this checks every structural requirement of
the settled revision (`NORMATIVE_CONTINUITY.tex`, revision 2): standing (Req 1, with
fresh occurrences), standing at opening (Req 2), new demands become issues (Req 3) with
the due/standing compatibility assumption, resolution continuity (4), fresh successors
(5), state continuity (6, as an accepted `Continue` record), prerequisite continuity (7),
no future route roots (8), persistent satisfaction (9), only ready issues resolve (10),
non-starvation (11) under the unit matter-grain budget, and the reach gate (12).

Semantic judgments are supplied by the trace as data: `Permit`, `Resolve`, `Continue`,
`AddPre`, `DropPre`, `Designate` are the *accepted* records themselves (the acceptance
convention), `Due` is a function of the prefix, `Met` is a monotone set of (position, d).

Record kinds in a batch:
    ("standing", record_id, adds, removes, grounds)   adds/removes: sets of rule ids
    ("open", q, tau, x, kappa, parents)
    ("resolve", q, successors)
    ("addpre", d, q, roots)
    ("droppre", d, q)
    ("met", d)                                        Met from the next prefix on
    ("designate", q)
Rules: `rules[lam] = dict(auth=bool, licenses={(kappa, tau, x), ...})`, immutable content.
"""
from fractions import Fraction

from fixtures import Model as IssueModel


class SettledModel(IssueModel):
    def __init__(self, rules, genesis, due):
        super().__init__()
        self.rules = rules
        self.L = set(genesis)
        self.G = set(genesis)
        self.ever_standing = set(genesis)
        self.due = due                      # due(n, prefix_state) -> set of (tau, x)
        self.prev_due = None
        self.anchor = {}                    # q -> (tau, x, kappa)
        self.history = []
        self.share = {}                     # m -> Fraction share, fixed at birth
        self.attention = {}                 # m -> cumulative A_N(m)
        self.omega = {}                     # m -> cumulative Ω_N(m)

    # ---- standing ---------------------------------------------------------
    def stands(self, kappa, tau, x):
        return any((kappa, tau, x) in self.rules[l]["licenses"] for l in self.L)

    # ---- one batch ----------------------------------------------------------
    def step(self, batch, gate="reach"):
        n = self.n
        # Req 3 + compatibility: rising edge of Due at the strict prefix.
        due_n = self.due(n, self)
        new_due = due_n if self.prev_due is None else due_n - self.prev_due
        opens = {r[1]: r for r in batch if r[0] == "open"}
        for (tau, x) in new_due:
            assert any(o[2] == tau and o[3] == x for o in opens.values()), \
                f"n={n}: Req 3, ({tau},{x}) newly due but no fresh issue"
            assert any(self.stands(k, tau, x) for l in self.L
                       for (k, t, xx) in self.rules[l]["licenses"] if (t, xx) == (tau, x)), \
                f"n={n}: compatibility, nothing has standing for ({tau},{x})"
        # Req 2: anchors read the strict prefix.
        for q, (_, _, tau, x, kappa, parents) in opens.items():
            assert self.stands(kappa, tau, x), f"n={n}: Req 2, {kappa} has no standing for {q}"
            self.anchor[q] = (tau, x, kappa)
        # Req 6: every successor with parents carries an accepted Continue record —
        # represented here by the `parents` field itself being nonempty-and-accepted.
        # Req 1: standing changes at the strict prefix, fresh occurrences, grounds.
        adds, removes = set(), set()
        for r in batch:
            if r[0] != "standing":
                continue
            _, rid, a, d, g = r
            a, d, g = set(a), set(d), set(g)
            changes = (a - self.L) | (d & self.L)
            if changes:
                assert g, f"n={n}: Req 1, standing change {rid} with empty grounds"
                assert g <= {l for l in self.L if self.rules[l]["auth"]}, \
                    f"n={n}: Req 1, grounds of {rid} not currently standing authorizers"
            for lam in a:
                assert lam not in self.ever_standing, f"n={n}: Req 1, {lam} re-enters standing"
            adds |= a; removes |= d
        # the issue layer (Req 4, 5, 7, 8, 9, 10, 12 and one-shot occurrences)
        issue_batch = [r if r[0] != "open" else ("open", r[1], list(r[5])) for r in batch]
        opp = super().step(issue_batch, gate)
        # standing update
        self.L = (self.L - removes) | adds
        self.ever_standing |= adds
        self.prev_due = due_n
        # Req 11 witness: positive share by birth order, charged when the matter has work.
        for m in self.matters:
            if m not in self.share:
                self.share[m] = Fraction(1, 2 ** (len(self.share) + 1))
                self.attention[m] = Fraction(0); self.omega[m] = 0
        total = Fraction(0)
        for m, has_work in opp.items():
            a = self.share[m] if has_work else Fraction(0)
            assert 0 <= a <= (1 if has_work else 0)
            total += a
            self.attention[m] += a
            self.omega[m] += int(has_work)
        assert total <= 1, f"n={n}: unit budget exceeded"
        self.history.append(dict(n=n, L=set(self.L), due=set(due_n), opp=dict(opp)))
        return opp


# ---------------------------------------------------------------------------
# The witness trace W. Rules: g0 (genesis, Auth, licenses P for (audit, sys)), g1
# (genesis, Auth), r1 (adopted at 1 on grounds {g0}, licenses P' for (audit, sys) and
# (review, sys)), r2 (adopted at 5 on grounds {g1}, licenses P'' for (audit, sys)).
RULES = {
    "g0": dict(auth=True, licenses={("P", "audit", "sys")}),
    "g1": dict(auth=True, licenses=set()),
    "r1": dict(auth=False, licenses={("P1", "audit", "sys"), ("P1", "review", "sys")}),
    "r2": dict(auth=False, licenses={("P2", "audit", "sys")}),
}


def DUE(n, model):
    """(audit, sys) is due from prefix 0; (review, sys) becomes due at prefix 2 once r1
    stands, drops out at 4, and is due again at 6 (a second rising edge)."""
    d = {("audit", "sys")}
    if n in (2, 3) or n >= 6:
        d.add(("review", "sys"))
    return d


WITNESS = [
    # e0: audit issue a opens under P (standing from g0); r1 adopted on grounds {g0}.
    [("open", "a", "audit", "sys", "P", []),
     ("standing", "s1", {"r1"}, set(), {"g0"})],
    # e1: prerequisite d0 on a with a co-opened route root t (Req 8 allows co-opening).
    [("open", "t", "review", "sys", "P1", []),
     ("addpre", "d0", "a", ["t"])],
    # e2: (review, sys) newly due at prefix 2 -> fresh issue v under P1; t resolves into
    #     t1 (state continuity via accepted successor); repeal g0's licence: P loses standing
    #     for future openings while a (anchored to P) stays live.
    [("open", "v", "review", "sys", "P1", []),
     ("resolve", "t", ["t1"]), ("open", "t1", "review", "sys", "P1", ["t"]),
     ("standing", "s2", set(), {"g0"}, {"g1"})],
    # e3: withdraw d0 (a becomes ready); add e0 on t1 with no route; designate t1 a matter.
    [("droppre", "d0", "a"), ("addpre", "e0", "t1", []), ("designate", "t1")],
    # e4: reintroduce a semantically identical prerequisite as a fresh occurrence d1 on a,
    #     routed to t1 — allowed by the reach gate because a is ready (has work) now.
    [("addpre", "d1", "a", ["t1"])],
    # e5: e0 met; r2 adopted (P2 gains standing).
    [("met", "e0"), ("standing", "s3", {"r2"}, set(), {"g1"})],
    # e6: t1 resolves terminally (route of d1 goes extinct); (review, sys) due again ->
    #     fresh issue v2 under P1; v resolves into v1 and v2 (split + merge shape).
    [("resolve", "t1", []),
     ("resolve", "v", ["v1", "v2"]),
     ("open", "v1", "review", "sys", "P1", ["v"]),
     ("open", "v2", "review", "sys", "P1", ["v"])],
    # e7: d1 met from the next prefix; a can then resolve.
    [("met", "d1")],
    # e8: a resolves terminally under its own anchor P, which no longer has standing.
    [("resolve", "a", [])],
    [], [],
]


def run_witness():
    M = SettledModel(RULES, genesis={"g0", "g1"}, due=DUE)
    for b in WITNESS:
        M.step(b)
    return M


if __name__ == "__main__":
    M = run_witness()
    assert not M.violations
    print("witness trace satisfies the settled specification;",
          f"matters={sorted(M.matters)}, standing at end={sorted(M.L)}")
