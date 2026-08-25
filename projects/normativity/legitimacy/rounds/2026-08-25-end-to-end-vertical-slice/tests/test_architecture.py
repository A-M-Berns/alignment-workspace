"""The compressed type story, pressed against the cases that would break it.

`ARCHITECTURE.md` claims three things this file exists to check: that the reason
substrate is a directed multihypergraph whose edges carry identity, that schema
revision is ordinary standing supersession and needs no new mechanism, and that
the persistent state is three components with everything else derived.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import li
import safety
import variants as v
from epistemic import pc_worlds
from pipeline import operative_projection, run_day
from ri_core import (ACCOUNT_FOR_SUCCESSION, ACTIVE, GENESIS, AnsRoot,
                     Derivation, History, PAuth, PForce, ReasonOcc, Seed,
                     SchemaCode, Standing, StandingState, Supersede, creating)
from standing import PValue, values_projection
from toy import Trajectory, j0, x0, x1


class TheReasonSubstrateIsAMultihypergraph(unittest.TestCase):
    """Vertices `V + SettleId`, edges `ReasonOcc`, and edges carry identity."""

    def test_an_occurrence_is_a_directed_hyperedge(self):
        """Sources are a finite set of vertices; the target is one vertex."""
        e = ReasonOcc("e1", frozenset([li.Atom("p"), li.Atom("q")]),
                      frozenset(["l:1"]), li.Atom("r"), 1)
        self.assertIsInstance(e.s_V, frozenset)
        self.assertIsInstance(e.s_L, frozenset)
        self.assertEqual(e.target, li.Atom("r"))

    def test_sources_are_content_expressions_not_occurrence_ids(self):
        """`s_V : Finset V`. An occurrence does not cite other occurrences.

        This is what keeps the graph a support structure over *content* rather
        than a derivation tree. Occurrence-level provenance is `Derivation`'s
        job, and it cites ids.
        """
        e = ReasonOcc("e1", frozenset([li.Atom("p")]), frozenset(), li.Atom("r"))
        for src in e.s_V:
            self.assertNotIsInstance(src, ReasonOcc)
            self.assertIsInstance(src, (li.Atom, li.Neg, li.And, li.Or,
                                        li.Implies))

    def test_two_occurrences_may_share_tail_and_head(self):
        """Which is what makes it a *multi*hypergraph rather than a hypergraph."""
        tail_v, tail_l, head = frozenset([li.Atom("p")]), frozenset(["l:1"]), li.Atom("r")
        a = ReasonOcc("e1", tail_v, tail_l, head, 1)
        b = ReasonOcc("e2", tail_v, tail_l, head, 2)
        self.assertEqual((a.s_V, a.s_L, a.target), (b.s_V, b.s_L, b.target))
        self.assertNotEqual(a.id, b.id)
        self.assertNotEqual(a, b)

    def test_a_derivation_cites_identities_and_the_two_are_distinguishable(self):
        """Same content, different history: a derivation can pick one."""
        traj = Trajectory()
        traj.history.settle("l:1")
        traj.history.reason("e1", s_L=frozenset(["l:1"]), target=li.Atom("r"))
        traj.history.reason("e2", s_L=frozenset(["l:1"]), target=li.Atom("r"))
        d = Derivation(concl=li.Atom("r"), leaves=frozenset(["e2"]))
        self.assertEqual(d.leaves, frozenset(["e2"]))
        occurrences = {e.id for e in traj.history.reasons()}
        self.assertTrue({"e1", "e2"} <= occurrences)

    def test_enablement_is_a_predicate_on_an_edge_not_a_propagation(self):
        """`Enabled_{B,L}(e) <=> s_V(e) subset B and s_L(e) subset L`.

        It reads two vertex sets — the stance and the ledger — and never
        another edge. So there is no fixpoint, no label to maintain, and
        adopting a conclusion is a standing act rather than a graph
        consequence.
        """
        def enabled(e, B, L):
            return e.s_V <= frozenset(B) and e.s_L <= frozenset(L)

        e = ReasonOcc("e1", frozenset([li.Atom("p")]), frozenset(["l:1"]),
                      li.Atom("r"))
        self.assertTrue(enabled(e, {li.Atom("p")}, {"l:1"}))
        self.assertFalse(enabled(e, set(), {"l:1"}))
        self.assertFalse(enabled(e, {li.Atom("p")}, set()))
        # the target being enabled elsewhere does not enable this edge
        self.assertFalse(enabled(e, {li.Atom("r")}, {"l:1"}))

    def test_an_undercutter_is_an_ordinary_edge(self):
        """A reason for `~App(sigma, c, n)` needs no attack primitive."""
        target = li.Neg(li.Atom("App(sigma,c,3)"))
        e = ReasonOcc("e:undercut", frozenset([li.Atom("the-case-differs")]),
                      frozenset(), target)
        self.assertEqual(e.target, target)
        self.assertIsInstance(e.target, li.Neg)


class SchemaRevisionIsOrdinarySupersession(unittest.TestCase):
    """No new mechanism: `PAuth(s0) ~> PAuth(s1)`, and the code never mutates."""

    def history_with_self_retiring_authority(self):
        successor = PAuth(creating("successor", []))
        code = SchemaCode(
            "retire-self",
            lambda wit, pre: Standing(Supersede(frozenset(["auth:self"]),
                                                (successor,))))
        std0 = {"auth:self": StandingState(ACTIVE, frozenset(), PAuth(code))}
        roots0 = (AnsRoot("q0", ("P0", 0), "A", "auth:self",
                          ACCOUNT_FOR_SUCCESSION, GENESIS, 0),)
        h = History(Seed("P0", std0, roots0))
        h.norm("a1", "auth:self", author="A")
        return h

    def test_a_schema_may_license_the_event_that_retires_its_standing(self):
        """The reflective loop closes in one step, and the record stays good."""
        h = self.history_with_self_retiring_authority()
        std = h.std()
        self.assertEqual(std["auth:self"].kind, "Terminated")
        self.assertEqual(std["auth:self"].status[1], "a1")
        self.assertTrue(h.good())

    def test_the_successor_records_the_lineage(self):
        h = self.history_with_self_retiring_authority()
        successor = [x for x in h.std() if x.startswith("@s")]
        self.assertEqual(len(successor), 1)
        self.assertEqual(h.std()[successor[0]].pred, frozenset(["auth:self"]))

    def test_the_retired_standing_keeps_its_payload(self):
        """Supersession terminates a standing; it does not rewrite its code.

        So an old derivation naming that standing stays interpretable: the
        object is still there, still carrying the schema it carried.
        """
        h = self.history_with_self_retiring_authority()
        st = h.std()["auth:self"]
        self.assertIsInstance(st.payload, PAuth)
        self.assertEqual(st.payload.code.name, "retire-self")

    def test_an_event_is_never_licensed_by_standing_it_creates(self):
        """The allocator excludes it, rather than a side condition.

        `schemaRef(a)` lies in the strict pre-state's domain by G4, and fresh
        ids are disjoint from that domain, so self-licensing cannot be written.
        """
        h = self.history_with_self_retiring_authority()
        a = h.norm_events()[0]
        from ri_core import ctx_of, fresh_n
        self.assertNotIn(a.schema_ref, fresh_n(ctx_of(a), h.effect(a)))


class TheThreeGraphsAreSeparate(unittest.TestCase):
    """Different vertex types, different questions, no shared edges."""

    def setUp(self):
        self.traj = Trajectory().stage_a().stage_b().stage_c()

    def test_reason_edges_have_content_vertices(self):
        for e in self.traj.history.reasons():
            self.assertTrue(e.s_L <= {s.id for s in self.traj.history.settlements()})

    def test_standing_lineage_has_standing_vertices(self):
        std = self.traj.history.std()
        for x, state in std.items():
            for parent in state.pred:
                self.assertIn(parent, std)

    def test_answerability_succession_has_root_vertices(self):
        roots = {q.id for q in self.traj.history.roots()}
        for q in self.traj.history.roots():
            for successor in self.traj.history.succ(q):
                self.assertIn(successor.id, roots)

    def test_no_vertex_universe_is_shared(self):
        std = set(self.traj.history.std())
        roots = {q.id for q in self.traj.history.roots()}
        settlements = {s.id for s in self.traj.history.settlements()}
        self.assertFalse(std & roots)
        self.assertFalse(std & settlements)
        self.assertFalse(roots & settlements)


class ThePersistentStateIsThreeComponents(unittest.TestCase):
    """History, price history, account. Everything else is derived or rigid."""

    def test_standing_is_a_fold_and_not_stored(self):
        traj = Trajectory().stage_a()
        first = traj.history.std()
        rebuilt = Trajectory().stage_a().history.std()
        self.assertEqual(set(first), set(rebuilt))

    def test_the_stage_is_derived_from_the_ledger_and_rigid_semantics(self):
        traj = Trajectory().stage_a().stage_b()
        stage = traj.stage()
        settled = [s.id for s in traj.history.settlements()]
        for sid in settled:
            for phi in traj.sem.sem(sid):
                self.assertIn(phi, stage.sentences())

    def test_the_value_registry_is_rigid_rather_than_mutable(self):
        """Admission reveals a partial function; it never redefines one."""
        traj = Trajectory()
        before = traj.registry.compile_value("v0", "q")
        self.assertIsInstance(v.rewriting_a_frozen_spec(), ValueError)
        self.assertEqual(before, traj.registry.compile_value("v0", "q"))

    def test_the_settlement_semantics_is_rigid_rather_than_mutable(self):
        self.assertIsInstance(v.rewriting_a_settlement(), ValueError)
        early, later = v.old_settlement_stays_rigid()
        self.assertEqual(early, later)

    def test_the_account_is_the_only_thing_that_shrinks(self):
        traj = Trajectory()
        traj.stage_a()
        start = traj.account.remaining
        traj.day(0)
        self.assertLess(traj.account.remaining, start)
        self.assertEqual(traj.history.now, 2, "no step was appended")


class ThePresentationIsTheTheoremFacingObject(unittest.TestCase):
    """`ForceRequest`, not a region: two presentations of one region differ."""

    def two_presentations(self):
        X = x0()
        from waist import Expect, Ineq, Injunction
        row = Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2))
        one = Injunction("J1", (row,))
        twice = Injunction("J2", (row, row))
        stage = v.base_stage(X)
        return (run_day(2, stage, v._std([("s", one)])),
                run_day(2, stage, v._std([("s", twice)])))

    def test_the_same_prices_are_enforced(self):
        a, b = self.two_presentations()
        self.assertEqual(set(a.region_vertices), set(b.region_vertices))

    def test_but_the_requests_differ(self):
        a, b = self.two_presentations()
        self.assertNotEqual(a.charged.request, b.charged.request)
        self.assertNotEqual(a.charged.request.rows, b.charged.request.rows)

    def test_and_so_does_the_charge(self):
        a, b = self.two_presentations()
        self.assertEqual(b.charge, 2 * a.charge)

    def test_a_request_carries_the_four_identities_the_certificate_binds(self):
        a, _ = self.two_presentations()
        r = a.charged.request
        self.assertEqual(r.date, a.day)
        self.assertEqual(r.support, safety.support_of(a.compiled))
        self.assertEqual(r.live_worlds, a.live_worlds)
        self.assertIsNone(a.charged.certificate.binds(
            r.date, r.region(), r.support, r.live_worlds))


class EqualPayloadsAtDistinctStandings(unittest.TestCase):
    """The projection keeps identity, so the charge counts both."""

    def test_two_standings_with_equal_payloads_are_two_items(self):
        X = x0()
        J = j0(X)
        view = v._std([("s:one", J), ("s:two", J)])
        self.assertEqual(len(operative_projection(view)), 2)

    def test_and_their_rows_are_attributable_separately(self):
        X = x0()
        J = j0(X)
        run = run_day(1, v.base_stage(X), v._std([("s:one", J), ("s:two", J)]))
        owners = {row.standing_id for row in run.compiled.rows}
        self.assertEqual(owners, {"s:one", "s:two"})


class ValueSupersessionLeavesTheQuantityFixed(unittest.TestCase):

    def test_the_old_luv_is_unchanged_by_the_new_specification(self):
        traj = Trajectory().stage_a()
        before = traj.X0.luv
        traj.stage_b()
        self.assertEqual(before, traj.X0.luv)
        self.assertNotEqual(traj.X0.luv, traj.X1.luv)

    def test_and_the_old_injunction_still_names_it(self):
        traj = Trajectory().stage_a().stage_b()
        run = traj.day(1)
        self.assertTrue(any("X[v0:q]" in repr(c) for c in run.coords))
        self.assertEqual(values_projection(traj.history.std()),
                         (("@s5.0", "v1"),))


if __name__ == "__main__":
    unittest.main()
