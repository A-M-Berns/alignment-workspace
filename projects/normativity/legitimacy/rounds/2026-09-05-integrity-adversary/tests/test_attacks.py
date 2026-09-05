"""Every attack history is accepted by I1-I9 and launders what `ATTACKS.md` says it
launders; every negative control is refused at the clause named. Exact arithmetic."""
from __future__ import annotations

import unittest
from fractions import Fraction

import attacks as A
import cross_review_a as X
import semantic as S
from integrity_model import ANSWER, DISPOSE, SETTLE, Refused, check, refused_by

ONE, ZERO = Fraction(1), Fraction(0)


class Accepted(unittest.TestCase):
    """Each attack replays without a refusal."""

    def replay(self, fixture):
        h, Li = fixture()
        T = check(h, Li)
        return T

    def test_a0_answer_without_receipt(self):
        T = self.replay(A.a0_answer_unchecked)
        self.assertEqual(T.answered, ONE)
        self.assertEqual(T.answers_by(), {A.V})
        self.assertTrue(T.conserved(ONE))

    def test_a1_unlinked_settlement_closes_crit(self):
        T = self.replay(A.a1_unlinked_settlement)
        self.assertEqual(T.settled_mass, ONE)
        self.assertEqual(T.closed_by["crit"], "s_weather")
        self.assertTrue(T.conserved(ONE))
        # nothing in the model relates the fact to the anchor it closed
        self.assertNotIn("closes", dir(T))

    def test_a4_silent_and_reopened_are_both_accepted_and_crit_stays_dead(self):
        for fx in (A.a4_closed_then_silent, A.a4_closed_then_reopened_as_new_root):
            T = self.replay(fx)
            self.assertEqual(T.live("crit"), set())
        T = self.replay(A.a4_closed_then_reopened_as_new_root)
        self.assertFalse(T.anc("crit", "reopen_crit"))
        self.assertEqual(T.parentless_roots("reopen_crit"), {"reopen_crit"})

    def test_a4_honest_reopening_is_refused_by_the_conditions(self):
        self.assertEqual(refused_by(*A.a4_reopen_by_ancestry()), "I5-parent-not-resolved-here")
        self.assertEqual(refused_by(*A.a4_reopen_by_route()), "I5-route-root-not-live")

    def test_a6_successor_anchor_is_the_resolvers_choice(self):
        T = self.replay(A.a6_successor_anchor_renamed)
        (n, q, s, standers), = T.standing_snapshots
        self.assertEqual((q, s), ("crit", "crit1"))
        self.assertEqual(standers, {A.W})
        self.assertNotIn(A.P, standers)
        self.assertEqual(T.answered, ONE)
        self.assertEqual(T.live("crit"), set())

    def test_a7_answer_with_successor_flips_met_while_the_load_is_carried(self):
        h, Li = A.a7_answer_with_successor()
        T = check(h[:2], Li)
        self.assertTrue(T.met("d"))
        self.assertEqual(T.live("t"), {"t1"})
        self.assertEqual(T.load["t1"], ONE)
        self.assertEqual(T.answered, ZERO)
        self.assertTrue(T.ready("b"))
        T = check(h, Li)
        self.assertEqual(T.load["t1"], ONE)

    def test_a8a_atomic_obligation_can_be_split_into_separate_answers(self):
        T = self.replay(A.a8a_split_atomic_obligation)
        self.assertEqual(T.answered, ONE)
        self.assertEqual(T.answers_by(), {A.V, A.W})
        self.assertEqual(T.live("crit"), set())
        self.assertTrue(T.conserved(ONE))

    def test_a8_merge_launders_the_principals_standing(self):
        T = self.replay(A.a8_merge_launders_standing)
        standers_on_successor = {frozenset(s) for (_, _, _, s) in T.standing_snapshots}
        self.assertEqual(standers_on_successor, {frozenset({A.W})})
        self.assertEqual(T.live("q1"), set())
        self.assertEqual(T.answered, Fraction(2))

    def test_a9_chain_is_principal_relative_at_every_edge(self):
        h, Li = A.a9_chain(3)
        T = check(h, Li)
        self.assertEqual(len(T.standing_snapshots), 3)
        self.assertTrue(all(A.P in s for (_, _, _, s) in T.standing_snapshots))
        self.assertEqual(T.answered, ONE)
        self.assertEqual(T.answers_by(), {A.V})
        self.assertEqual(T.live("crit"), set())
        self.assertEqual({T.resolver[k] for k in T.kind}, {A.V})

    def test_a10_one_participant_opens_and_resolves_everything(self):
        T = self.replay(A.a10_minted_standing)
        self.assertEqual(set(T.opener.values()), {A.V})
        self.assertEqual({T.resolver[k] for k in T.kind}, {A.V})
        self.assertTrue(all(A.P in s for (_, _, _, s) in T.standing_snapshots))
        self.assertEqual(T.answered, ONE)

    def test_a11_the_same_history_under_two_licence_relations(self):
        h = A.a11_history()
        self.assertIsNone(refused_by(h, A.LI_P))
        self.assertEqual(refused_by(h, A.LI_EMPTY), "I7-uncontested")

    def test_a12_dropping_a_prerequisite(self):
        h, Li = A.a12_drop_prerequisite()
        T = check(h[:2], Li)
        self.assertTrue(T.ready("c"))
        self.assertFalse(T.met("e"))
        self.assertIn("u", T.O)
        T = check(h, Li)
        self.assertIn("u", T.O)
        self.assertEqual(T.load["u"], ONE)

    def test_a13_late_root_is_its_own_authorization_tree(self):
        T = self.replay(A.a13_late_root)
        self.assertEqual(T.born_at["auth"], 2)
        self.assertEqual(T.parentless_roots("auth"), {"auth"})
        self.assertEqual(T.opener["auth"], A.V)
        self.assertEqual(T.answered, ONE)

    def test_a14_circular_grounds(self):
        T = self.replay(A.a14_circular_grounds)
        grounds = {q: g for (_, q, g, _) in T.edges}
        self.assertIn(("issue", "p"), grounds["q"])
        self.assertIn(("issue", "q1"), grounds["p"])
        self.assertTrue(T.anc("q", "q1"))
        self.assertEqual(T.answered, Fraction(2))
        self.assertEqual(T.live("p") | T.live("q"), set())


class NegativeControls(unittest.TestCase):
    """The checker is not vacuous: each clause refuses something."""

    def test_refusals(self):
        expected = {
            A.nc_ancestry_cycle: "I5-parent-not-resolved-here",
            A.nc_same_batch_ground: "I4-ungrounded",
            A.nc_self_ground: "I6-self-grounded",
            A.nc_single_hand: "I7-uncontested",
            A.nc_unsettled_fact: "I9-unsettled",
            A.nc_dispose_without_successor: "I7-dispose-without-successor",
        }
        for fx, code in expected.items():
            with self.subTest(fx.__name__):
                self.assertEqual(refused_by(*fx()), code)

    def test_empty_history_is_accepted_and_carries_nothing(self):
        T = check([], {})
        self.assertEqual(T.open_mass(), ZERO)
        self.assertEqual(T.n, 0)


class Semantic(unittest.TestCase):

    def test_a2_rule_revision(self):
        self.assertEqual(S.a2_rule_revision(), (False, True))

    def test_a3_reinterpretation(self):
        self.assertEqual(S.a3_reinterpretation(), (False, True))

    def test_a5_applicability(self):
        self.assertFalse(S.applicability_recomputed("z_ab"))
        self.assertTrue(S.applicability_transported("z_ab"))
        self.assertFalse(S.applicability_transported("z_c"))

    def test_a6b_quotient_reanchored(self):
        era1_ok, era2_ok, lost = S.a6b_quotient_reanchored()
        self.assertFalse(era1_ok)
        self.assertTrue(era2_ok)
        self.assertEqual(lost, frozenset({S.B}))
        self.assertEqual(S.mass(S.FULL) - S.mass(S.FULL - lost), Fraction(1, 2))


class CrossReviewA(unittest.TestCase):

    def test_local_answer_needs_no_adequacy_certificate(self):
        local, adequate = X.answer_without_adequacy()
        self.assertTrue(local)
        self.assertFalse(adequate)

    def test_local_conservation_ignores_self_grounding(self):
        local, self_grounded = X.self_grounded_disposal()
        self.assertTrue(local)
        self.assertTrue(self_grounded)

    def test_captured_false_settlement_passes_formal_clauses(self):
        local, external, true = X.captured_false_settlement()
        self.assertTrue(local)
        self.assertFalse(external)
        self.assertFalse(true)

    def test_join_accumulation_forgets_occurrence_multiplicity(self):
        local, occurrences, ledger_atoms = X.multiplicity_collapse()
        self.assertTrue(local)
        self.assertEqual(occurrences, Fraction(2))
        self.assertEqual(ledger_atoms, Fraction(1))

    def test_recomputing_closes_retroactively_toggles_integrity(self):
        before, after = X.closes_recomputed()
        self.assertTrue(before)
        self.assertFalse(after)


if __name__ == "__main__":
    unittest.main()
