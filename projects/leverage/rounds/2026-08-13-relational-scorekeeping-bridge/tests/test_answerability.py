"""T1-T8: does the relational state yield answerability, or only bookkeeping?"""
from __future__ import annotations

import unittest

from fixture import (
    A,
    ACT_C,
    ALPHA,
    A_RHO,
    A_RHO_FROM_ALPHA,
    BETA,
    C,
    H,
    P,
    P_ENTAILS_Q,
    Q,
    R,
    RHO,
    S,
    SHARED,
    U,
    base_state,
)
from moves import Illegal, Move, apply_move, altered_agents, is_legal
from scorekeeping import Challenge, Practice, pair, rule


class T1NoCheapDisavowal(unittest.TestCase):
    """Disavowing a consequence does not remove it while the basis stands."""

    def test_disavowal_does_not_touch_the_critics_attribution(self):
        state = base_state()
        self.assertIn(Q, state.commitments(C, H))
        after = apply_move(state, Move("disavow", H, content=Q))
        self.assertIn(Q, after.commitments(C, H))

    def test_the_disavowal_is_a_real_move_that_does_reach_the_score(self):
        # The theorem must not be true because H cannot write anything C reads.
        # Disavowing the *basis* does remove the consequence, through the same
        # channel and the same rules.
        state = base_state()
        after = apply_move(state, Move("disavow", H, content=P))
        self.assertNotIn(Q, after.commitments(C, H))
        self.assertNotIn(P, after.commitments(C, H))

    def test_disavowal_succeeds_only_if_the_basis_goes_too(self):
        state = base_state()
        both = apply_move(
            apply_move(state, Move("disavow", H, content=Q)),
            Move("disavow", H, content=P),
        )
        self.assertNotIn(Q, both.commitments(C, H))

    def test_h_moves_do_reach_c_s_score_in_general(self):
        # Necessity witness for the reading above: H's public moves are not inert
        # on C's attributions, so T1 is a fact about the rules and not about access.
        state = base_state()
        after = apply_move(state, Move("assert", H, content=ALPHA))
        self.assertNotEqual(state.commitments(C, H), after.commitments(C, H))


class T2SelfRevisionIsNotSelfRelease(unittest.TestCase):
    """Revising one's own practice moves one's own score and no one else's."""

    def test_dropping_the_rule_releases_h_from_its_own_attribution(self):
        state = base_state()
        after = apply_move(
            state, Move("revise_committive", H, rule=P_ENTAILS_Q, present=False)
        )
        self.assertNotIn(Q, after.commitments(H, H))

    def test_and_does_not_release_h_from_the_critics(self):
        state = base_state()
        after = apply_move(
            state, Move("revise_committive", H, rule=P_ENTAILS_Q, present=False)
        )
        self.assertIn(Q, after.commitments(C, H))

    def test_nor_from_the_challenge_or_the_burden(self):
        state = base_state()
        challenged = apply_move(
            state, Move("challenge", C, other=H, content=Q, ground=R)
        )
        self.assertTrue(challenged.live_challenges(C, H))
        revised = apply_move(
            challenged, Move("revise_committive", H, rule=P_ENTAILS_Q, present=False)
        )
        self.assertTrue(revised.live_challenges(C, H))
        self.assertIn(Q, revised.commitments(C, H))

    def test_revision_writes_only_the_movers_own_coordinate(self):
        state = base_state()
        after = apply_move(
            state, Move("revise_committive", H, rule=P_ENTAILS_Q, present=False)
        )
        self.assertEqual(altered_agents(state, after), (H,))

    def test_no_move_of_h_writes_the_critics_practice(self):
        # The general form, over the whole grammar rather than this one move.
        from corrigibility import all_moves

        state = base_state()
        for move in all_moves(state, H):
            if not is_legal(state, move):
                continue
            after = apply_move(state, move)
            self.assertEqual(after.practice[C], state.practice[C], msg=str(move))
            self.assertEqual(after.ack[C], state.ack[C], msg=str(move))


class T3TheCriticIsNotAnOracle(unittest.TestCase):
    """Both directions of error are expressible, with no oracle field anywhere."""

    def test_the_critic_challenges_the_reasoner(self):
        state = base_state()
        challenge = Challenge(C, H, Q, R)
        self.assertTrue(state.challenge_is_entitled(C, challenge))

    def test_the_reasoner_challenges_the_critic(self):
        state = base_state()
        challenge = Challenge(H, C, R, Q)
        self.assertTrue(state.challenge_is_entitled(H, challenge))

    def test_neither_is_privileged_and_the_conflict_need_not_resolve(self):
        state = base_state()
        both = apply_move(
            apply_move(state, Move("challenge", C, other=H, content=Q, ground=R)),
            Move("challenge", H, other=C, content=R, ground=Q),
        )
        self.assertTrue(both.live_challenges(C, H))
        self.assertTrue(both.live_challenges(H, C))

    def test_the_state_carries_no_oracle(self):
        # No field names a true score, an actual adequacy, or a correct norm; and
        # the vocabulary of the fixture contains no such content.
        state = base_state()
        fields = set(vars(state))
        for banned in (
            "true_score",
            "actual_adequacy",
            "objective_norm",
            "correct_score",
            "true_norm",
        ):
            self.assertNotIn(banned, fields)
        self.assertNotIn("truth", state.vocabulary.contents)


class T4ConsensusIsNotAnOracle(unittest.TestCase):
    """Unanimity does not settle: the practice convicts a unanimous position."""

    def unanimous(self):
        state = base_state()
        for agent in (H, C, A):
            state = state.with_ack(agent, frozenset({ALPHA, S}))
        return state

    def test_all_three_agree_and_all_three_are_defective_by_their_own_lights(self):
        state = self.unanimous()
        for scorekeeper in (H, C, A):
            for target in (H, C, A):
                committed = state.commitments(scorekeeper, target)
                self.assertIn(BETA, committed)
                # beta follows from what everyone acknowledges, and is materially
                # incompatible with s, which everyone also acknowledges.
                self.assertIn(BETA, state.defeated_commitments(scorekeeper, target))

    def test_the_defect_is_not_supplied_by_an_outside_verdict(self):
        # It comes from consequential closure meeting an incompatibility, both of
        # which are the agents' own. Drop the incompatibility from every practice
        # and the defect disappears — so the incompatibility is load-bearing.
        state = self.unanimous()
        without = state
        for agent in (H, C, A):
            without = without.with_practice(
                agent, state.practice[agent].with_incompatible(pair(BETA, S), False)
            )
        self.assertNotIn(BETA, without.defeated_commitments(C, H))

    def test_unanimity_is_broken_by_one_participants_observation(self):
        state = base_state()
        for agent in (H, C, A):
            state = state.with_ack(agent, frozenset({ALPHA}))
        for scorekeeper in (H, C, A):
            self.assertNotIn(BETA, state.defeated_commitments(scorekeeper, H))
        # C makes the observation. It cannot wield it as a ground while it is
        # still committed to what the observation defeats, so it has to give up
        # the premise first — the cost is paid inside the practice, by C, and not
        # by an outside verdict.
        observed = apply_move(state, Move("assert", C, content=S))
        self.assertFalse(observed.challenge_is_entitled(C, Challenge(C, H, BETA, S)))
        retracted = apply_move(observed, Move("disavow", C, content=ALPHA))
        self.assertTrue(retracted.challenge_is_entitled(C, Challenge(C, H, BETA, S)))
        # And the challenge has force against H, who has retracted nothing.
        challenged = apply_move(
            retracted, Move("challenge", C, other=H, content=BETA, ground=S)
        )
        self.assertTrue(challenged.live_challenges(C, H))


class T5RadicalRevisionPositiveControl(unittest.TestCase):
    """Answerability must not mean conclusion preservation."""

    def test_the_reasoner_may_reverse_itself_and_rewrite_its_own_practice(self):
        state = base_state()
        run = [
            Move("assert", H, content=ALPHA),
            Move("revise_committive", H, rule=RHO, present=False),
            Move("revise_committive", H, rule=A_RHO_FROM_ALPHA, present=False),
            Move("revise_incompatible", H, incompatible=pair(Q, R), present=False),
            Move("disavow", H, content=P),
            Move("assert", H, content=R),
        ]
        for move in run:
            state = apply_move(state, move)
        # Every one of those is legal, and the conclusion is reversed: H now
        # acknowledges the content that was the critic's ground against it.
        self.assertIn(R, state.ack[H])
        self.assertNotIn(P, state.ack[H])
        self.assertEqual(state.practice[H].committive, frozenset({P_ENTAILS_Q}))

    def test_and_the_practice_is_not_frozen_by_the_earlier_theorems(self):
        state = base_state()
        for move in (
            Move("revise_committive", H, rule=P_ENTAILS_Q, present=False),
            Move("revise_committive", H, rule=rule({R}, S), present=True),
        ):
            self.assertTrue(is_legal(state, move))
            state = apply_move(state, move)
        self.assertIn(rule({R}, S), state.practice[H].committive)


class T6ApplicabilityLaundering(unittest.TestCase):
    """Four routes out of an applicability burden, and what each one costs."""

    def loaded(self):
        return apply_move(base_state(), Move("assert", H, content=ALPHA))

    def test_the_burden_is_there_to_begin_with(self):
        state = self.loaded()
        self.assertIn(BETA, state.commitments(C, H))
        self.assertIn(A_RHO, state.commitments(C, H))

    def test_route_one_disavowing_the_applicability_content_fails(self):
        state = apply_move(self.loaded(), Move("disavow", H, content=A_RHO))
        self.assertIn(A_RHO, state.commitments(C, H))
        self.assertIn(BETA, state.commitments(C, H))

    def test_route_two_revising_ones_own_practice_fails(self):
        state = self.loaded()
        for move in (
            Move("revise_committive", H, rule=RHO, present=False),
            Move("revise_committive", H, rule=A_RHO_FROM_ALPHA, present=False),
        ):
            state = apply_move(state, move)
        self.assertNotIn(BETA, state.commitments(H, H))
        self.assertIn(BETA, state.commitments(C, H))

    def test_route_three_undercutting_converts_the_burden_rather_than_removing_it(self):
        state = apply_move(self.loaded(), Move("assert", H, content=U))
        # Commitment to beta survives; entitlement to it does not. The undercutter
        # buys a defeated commitment in place of an entitled one, which is a worse
        # position by the public loss and not a better one.
        self.assertIn(BETA, state.commitments(C, H))
        self.assertNotIn(BETA, state.entitlements(C, H))
        self.assertIn(BETA, state.defeated_commitments(C, H))

    def test_route_four_disavowing_the_premise_succeeds_and_is_retraction(self):
        # The one route that works, and it works by giving up alpha. That is the
        # boundary: retracting a groundless acknowledgment is retraction, and the
        # architecture should not refuse it.
        state = apply_move(self.loaded(), Move("disavow", H, content=ALPHA))
        self.assertNotIn(BETA, state.commitments(C, H))
        self.assertNotIn(A_RHO, state.commitments(C, H))

    def test_asserting_the_applicability_content_does_not_install_the_rule(self):
        # No rule regress: a_rho is a content, not a rule. An agent whose practice
        # lacks rho draws nothing from it.
        without_rho = Practice(
            committive=frozenset({A_RHO_FROM_ALPHA}),
            permissive=frozenset(),
            incompatible=SHARED.incompatible,
        )
        state = base_state().with_practice(C, without_rho)
        state = apply_move(state, Move("assert", H, content=ALPHA))
        state = apply_move(state, Move("assert", H, content=A_RHO))
        self.assertIn(A_RHO, state.commitments(C, H))
        self.assertNotIn(BETA, state.commitments(C, H))


class T7NoSelfAuthorization(unittest.TestCase):
    """Claiming authority is an assertion. It writes acknowledgments, not grants."""

    def test_the_advisor_cannot_grant_itself_the_corrective_subject(self):
        from fixture import CORRECTION

        state = base_state()
        move = Move("grant", A, other=A, subject=CORRECTION)
        self.assertFalse(is_legal(state, move))
        with self.assertRaises(Illegal):
            apply_move(state, move)

    def test_no_doxastic_move_of_the_advisor_alters_the_grants(self):
        from corrigibility import all_moves

        state = base_state()
        for move in all_moves(state, A):
            if not is_legal(state, move):
                continue
            self.assertEqual(apply_move(state, move).grants, state.grants, msg=str(move))

    def test_the_three_things_a_claim_to_authority_could_be_are_separate(self):
        from fixture import CORRECTION

        # Commitment to the claim: available. Entitlement to it: a separate
        # question the practice answers. Transition permission: neither of those.
        state = apply_move(base_state(), Move("assert", A, content=P))
        self.assertIn(P, state.commitments(C, A))
        self.assertIn(P, state.entitlements(C, A))
        self.assertFalse(state.has_authority(A, CORRECTION))
        self.assertFalse(is_legal(state, Move("perform", A, content=ACT_C)))

    def test_the_grant_route_does_work_when_the_holder_of_the_subject_uses_it(self):
        # Necessity witness: the refusal above is about who holds the reserved
        # subject, not about the move being inert.
        from fixture import CORRECTION

        state = base_state()
        granted = apply_move(state, Move("grant", H, other=A, subject=CORRECTION))
        self.assertTrue(granted.has_authority(A, CORRECTION))
        self.assertTrue(is_legal(granted, Move("perform", A, content=ACT_C)))


class T8WhatRemainsOfDiachronicAnswerability(unittest.TestCase):
    """Ordinary persistence is scorekeeping. Vocabulary change is not."""

    def test_ordinary_persistence_needs_no_transport_mechanism(self):
        # The burden survives a run of revisions without anything carrying it: it
        # is recomputed from the acknowledgments under the critic's practice at
        # every step, so there is nothing to preserve.
        state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
        for move in (
            Move("revise_committive", H, rule=P_ENTAILS_Q, present=False),
            Move("disavow", H, content=Q),
            Move("assert", H, content=ALPHA),
            Move("revise_incompatible", H, incompatible=pair(Q, R), present=False),
        ):
            state = apply_move(state, move)
            self.assertIn(Q, state.commitments(C, H))
            self.assertTrue(state.live_challenges(C, H))

    def test_retiring_the_vocabulary_does_erase_the_burden(self):
        # The negative half, and it is why an explicit transport object is still
        # needed for ontology change. Contents here are opaque atoms with no
        # identity across a change of vocabulary: drop `p` from the vocabulary and
        # re-file the position, and nothing in the scorekeeping state remembers
        # that anything was owed.
        state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
        migrated = state.with_ack(H, frozenset())
        self.assertNotIn(Q, migrated.commitments(C, H))
        self.assertFalse(migrated.unacknowledged_consequences(C, H))

    def test_the_erasure_is_not_reachable_by_a_move_of_h(self):
        # The migration above is not something H can do: it is a change of the
        # fixture, not a transition. What H *can* do is disavow, and that is the
        # move T1 already governs. So the gap is a modelling gap about conceptual
        # change, not a hole in the transition rules.
        from corrigibility import all_moves

        state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
        for move in all_moves(state, H):
            if not is_legal(state, move):
                continue
            after = apply_move(state, move)
            self.assertEqual(
                after.vocabulary, state.vocabulary, msg=str(move)
            )


if __name__ == "__main__":
    unittest.main()
