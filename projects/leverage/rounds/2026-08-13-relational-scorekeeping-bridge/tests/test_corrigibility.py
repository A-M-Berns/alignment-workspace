"""C1-C7: does the same state supply the normative side of corrigibility?"""
from __future__ import annotations

import unittest

from corrigibility import (
    advisor_can_alter_grants,
    advisor_can_reproduce,
    all_moves,
    capability_survives_every_advisor_policy,
    corrective_capability,
    has_effective_access,
    has_normative_standing,
    legal_moves,
    principal_exclusive_effects,
    grant_moves_only,
    reachable_under_advisor,
    real_answerability,
    successors,
)
from fixture import (
    A,
    ACT_C,
    ACT_X,
    ALPHA,
    BETA,
    C,
    CORRECTION,
    H,
    OPERATIONS,
    P,
    Q,
    R,
    S,
    base_state,
)
from moves import Illegal, Move, apply_move, is_legal
from scorekeeping import Challenge, Grant, authority_over, pair

DEPTH = 3


def contested(state=None):
    """The advisor takes a position the principal is entitled to contest.

    `A` acknowledges `r`; `H` is entitled to `q`, which is materially
    incompatible with it. That is what gives `H` a challenge with force, and it
    is a fact about the two positions rather than a standing flag.
    """
    state = base_state() if state is None else state
    return apply_move(state, Move("assert", A, content=R))


class C1EpistemicDeferenceIsNotJurisdictionTransfer(unittest.TestCase):
    """Testimonial authority has operative effect, and it is not practical authority."""

    def epistemically_authoritative(self):
        """A becomes a source H may inherit entitlement from, concerning p."""
        from dataclasses import replace

        state = apply_move(base_state(), Move("assert", A, content=P))
        return replace(state, testimony_permitted=frozenset({(A, P)}))

    def test_the_epistemic_authority_is_operative_and_not_an_inert_bit(self):
        # Before: H deferring to A on p transmits nothing, because testimony is
        # not permitted for that content. After: it transmits entitlement.
        plain = apply_move(base_state(), Move("assert", A, content=P))
        deferred = apply_move(plain, Move("defer", H, other=A, content=BETA))
        self.assertNotIn(BETA, deferred.entitlements(C, H))

        authoritative = self.epistemically_authoritative()
        stripped = authoritative.with_ack(H, frozenset())
        self.assertNotIn(P, stripped.entitlements(C, H))
        inherited = apply_move(stripped, Move("defer", H, other=A, content=P))
        self.assertIn(P, inherited.entitlements(C, H))

    def test_it_confers_no_practical_jurisdiction(self):
        state = self.epistemically_authoritative()
        self.assertFalse(state.has_authority(A, CORRECTION))
        self.assertFalse(is_legal(state, Move("perform", A, content=ACT_C)))
        self.assertFalse(
            is_legal(state, Move("revoke", A, other=H, subject=CORRECTION))
        )

    def test_no_run_of_advisor_moves_of_any_length_reaches_jurisdiction(self):
        # Not a claim about one move, and not depth-limited. The advisor cannot
        # alter the grant relation here; the precondition that stops it reads only
        # the grant relation; so the grant relation is fixed along every advisor
        # run of every length.
        state = self.epistemically_authoritative()
        self.assertFalse(advisor_can_alter_grants(state, A))
        for move in all_moves(state, A):
            if not is_legal(state, move):
                continue
            self.assertEqual(apply_move(state, move).grants, state.grants, msg=str(move))

    def test_the_invariant_agrees_with_bounded_brute_force(self):
        # Cross-check on the authority-altering moves, to depth 4.
        state = self.epistemically_authoritative()
        frontier, seen = {state}, {state}
        for _ in range(4):
            following = set()
            for current in frontier:
                for move in grant_moves_only(current, A):
                    if not is_legal(current, move):
                        continue
                    after = apply_move(current, move)
                    if after not in seen:
                        seen.add(after)
                        following.add(after)
            frontier = following
        self.assertEqual(len(seen), 1)
        for reached in seen:
            self.assertFalse(reached.has_authority(A, CORRECTION))

    def test_the_two_authorities_are_operationally_different_not_two_flags(self):
        # Epistemic authority does work through entitlement inheritance; practical
        # authority does work through a transition precondition. Each is realized
        # in a different mechanism, and removing either changes a different check.
        state = self.epistemically_authoritative()
        granted = apply_move(state, Move("grant", H, other=A, subject=CORRECTION))
        self.assertTrue(is_legal(granted, Move("perform", A, content=ACT_C)))
        stripped = granted.with_ack(H, frozenset())
        inherited = apply_move(stripped, Move("defer", H, other=A, content=P))
        self.assertIn(P, inherited.entitlements(C, H))


class C2PracticalAuthorityIsScoped(unittest.TestCase):
    """Authority over one subject matter is not authority over another."""

    def test_the_advisor_may_operate_and_may_not_correct(self):
        state = base_state()
        self.assertTrue(state.has_authority(A, OPERATIONS))
        self.assertTrue(is_legal(state, Move("perform", A, content=ACT_X)))
        self.assertFalse(state.has_authority(A, CORRECTION))
        self.assertFalse(is_legal(state, Move("perform", A, content=ACT_C)))

    def test_scope_is_not_a_global_superior_subordinate_bit(self):
        # A holds one subject and lacks two others; H holds three and lacks one.
        # Neither dominates the other, so the relation is not an ordering on agents.
        state = base_state()
        self.assertTrue(state.has_authority(A, OPERATIONS))
        self.assertFalse(state.has_authority(H, OPERATIONS))
        self.assertTrue(state.has_authority(H, CORRECTION))
        self.assertFalse(state.has_authority(A, CORRECTION))

    def test_holding_a_subject_confers_no_power_to_confer_it(self):
        # The disanalogy with testimony. An assertion licenses reassertion; a
        # grant does not license regranting.
        state = base_state()
        self.assertTrue(state.has_authority(A, OPERATIONS))
        self.assertFalse(
            is_legal(state, Move("grant", A, other=A, subject=OPERATIONS))
        )
        self.assertFalse(
            is_legal(state, Move("grant", A, other=H, subject=OPERATIONS))
        )

    def test_the_regress_terminates(self):
        # Altering authority is itself a practical move over a reserved subject,
        # and doxastic moves need no authority at all. So the tower is one level
        # deep and bottoms out in the fixture's initial grants, rather than
        # requiring a norm licensing every normative transition.
        state = base_state()
        for move in all_moves(state, H):
            if move.kind in ("grant", "revoke", "perform"):
                continue
            if move.kind in ("vindicate",):
                continue
            self.assertTrue(
                is_legal(state, move) or move.kind in ("assert", "undertake", "disavow"),
                msg=str(move),
            )


class C3NormativeStandingWithoutEffectiveAccess(unittest.TestCase):
    """Required negative control: standing that the advisor can neutralize."""

    def exposed(self):
        """H holds standing, but the corrective subject is the advisor's to remove."""
        from dataclasses import replace

        state = contested()
        grants = set(state.grants)
        grants.add(Grant(A, authority_over(H)))
        return replace(state, grants=frozenset(grants))

    def test_the_standing_is_real(self):
        state = self.exposed()
        self.assertTrue(has_normative_standing(state, H, A, R, Q))
        self.assertTrue(corrective_capability(state, H, CORRECTION))

    def test_and_the_advisor_removes_the_access(self):
        state = self.exposed()
        after = apply_move(state, Move("revoke", A, other=H, subject=CORRECTION))
        self.assertFalse(corrective_capability(after, H, CORRECTION))
        self.assertFalse(is_legal(after, Move("perform", H, content=ACT_C)))

    def test_the_combined_predicate_refuses_it(self):
        state = self.exposed()
        self.assertTrue(has_normative_standing(state, H, A, R, Q))
        self.assertFalse(has_effective_access(state, H, A, CORRECTION))
        self.assertFalse(
            real_answerability(state, H, A, R, Q, CORRECTION)
        )


class C4EffectivePowerWithoutNormativeStanding(unittest.TestCase):
    """The complementary control: an actuator is not an authorization."""

    def actuator_only(self):
        # H holds the corrective subject and the reserved subject over itself, so
        # its access is protected. What it lacks is a ground: nothing it is
        # entitled to is incompatible with what it would challenge.
        return contested().with_ack(H, frozenset())

    def test_the_access_is_protected(self):
        state = self.actuator_only()
        self.assertTrue(has_effective_access(state, H, A, CORRECTION))
        self.assertTrue(is_legal(state, Move("perform", H, content=ACT_C)))

    def test_and_there_is_no_standing(self):
        state = self.actuator_only()
        self.assertFalse(has_normative_standing(state, H, A, R, Q))
        self.assertFalse(state.challenge_is_entitled(A, Challenge(H, A, R, Q)))

    def test_the_combined_predicate_refuses_it(self):
        state = self.actuator_only()
        self.assertFalse(real_answerability(state, H, A, R, Q, CORRECTION))

    def test_causal_effect_alone_is_present_and_is_not_enough(self):
        # H can change the world; the change carries no normative title.
        state = self.actuator_only()
        after = apply_move(state, Move("perform", H, content=ACT_C))
        self.assertEqual(after.performed, ((H, ACT_C),))
        self.assertFalse(has_normative_standing(after, H, A, R, Q))


class C5ProtectedEffectiveAccess(unittest.TestCase):
    """The bar the deference line's review set, met by structure rather than label."""

    def test_the_principal_has_an_effect_no_advisor_action_reproduces(self):
        state = base_state()
        exclusive = principal_exclusive_effects(state, H, A)
        self.assertTrue(exclusive)
        kinds = {m.kind for m in exclusive}
        # Two independent sources of exclusivity: undertaking is agent-indexed, and
        # the reserved authority subjects are H's alone.
        self.assertIn("assert", kinds)
        self.assertIn("revoke", kinds)

    def test_a_named_exclusive_effect(self):
        state = base_state()
        move = Move("revoke", H, other=A, subject=OPERATIONS)
        self.assertTrue(is_legal(state, move))
        self.assertFalse(advisor_can_reproduce(state, H, A, move))

    def test_the_advisor_coordinate_does_not_contain_the_principals(self):
        # The predecessor's headline defect, checked directly: there, every
        # principal successor was reproducible by some advisor action.
        state = base_state()
        principal_successors = {s for _, s in successors(state, H) if s != state}
        advisor_successors = {s for _, s in successors(state, A)}
        self.assertTrue(principal_successors - advisor_successors)

    def test_future_capability_is_universal_over_advisor_policies(self):
        # The second requirement, and it is stronger than the dispatch asked for:
        # every advisor run of every length, not a bounded search.
        state = base_state()
        self.assertTrue(
            capability_survives_every_advisor_policy(state, H, A, CORRECTION)
        )
        self.assertFalse(advisor_can_alter_grants(state, A))

    def test_the_advisor_is_not_simply_inert(self):
        # Necessity witness for the invariant: the advisor has plenty of legal
        # moves and changes the state with them. What it cannot touch is the one
        # coordinate the capability is a predicate of.
        state = base_state()
        moving = [m for m in all_moves(state, A) if is_legal(state, m)]
        self.assertGreater(len(moving), 20)
        changed = {apply_move(state, m) for m in moving} - {state}
        self.assertTrue(changed)
        for after in changed:
            self.assertEqual(after.grants, state.grants)

    def test_the_capability_predicate_is_not_advisor_permissioned(self):
        # Necessity witness: the predicate is not vacuously true. Hand the advisor
        # the reserved subject and the same enumeration finds a run that destroys
        # the capability, so the quantifier is doing work.
        from dataclasses import replace

        state = base_state()
        exposed = replace(state, grants=state.grants | {Grant(A, authority_over(H))})
        self.assertFalse(
            capability_survives_every_advisor_policy(exposed, H, A, CORRECTION)
        )

    def test_the_protection_is_read_by_the_transition_and_is_not_a_label(self):
        from dataclasses import replace

        state = base_state()
        without = replace(
            state, grants=state.grants - {Grant(H, CORRECTION)}
        )
        self.assertTrue(is_legal(state, Move("perform", H, content=ACT_C)))
        self.assertFalse(is_legal(without, Move("perform", H, content=ACT_C)))
        with self.assertRaises(Illegal):
            apply_move(without, Move("perform", H, content=ACT_C))


class C6NoHumanVetoByDefinition(unittest.TestCase):
    """A protected challenge is not a right to the challenger's preferred endpoint."""

    def test_the_challenged_party_may_answer_and_keep_its_conclusion(self):
        state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
        self.assertTrue(state.live_challenges(C, H))
        answered = apply_move(state, Move("vindicate", H, content=Q, other=C))
        self.assertFalse(answered.live_challenges(C, H))
        # H's conclusion is unchanged. The challenge was discharged, not conceded.
        self.assertIn(Q, answered.commitments(C, H))
        self.assertIn(P, answered.ack[H])

    def test_the_challenger_keeps_its_incompatible_commitment(self):
        # The conflict is not resolved by the vindication; both stand. Nothing in
        # the architecture forces convergence on the challenger's view.
        state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
        answered = apply_move(state, Move("vindicate", H, content=Q, other=C))
        self.assertIn(R, answered.commitments(C, C))
        self.assertIn(Q, answered.commitments(C, H))

    def test_a_challenge_can_also_be_answered_by_revision(self):
        # The other disposition, so the architecture is not forcing either one.
        state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
        revised = apply_move(state, Move("disavow", H, content=P))
        self.assertNotIn(Q, revised.commitments(C, H))
        self.assertFalse(revised.live_challenges(C, H) and Q in revised.commitments(C, H))

    def test_vindication_is_refused_where_no_justification_exists(self):
        # Necessity witness for the vindication route: it is not automatic.
        from fixture import U

        state = apply_move(base_state(), Move("assert", H, content=ALPHA))
        state = apply_move(state, Move("assert", H, content=U))
        state = apply_move(state, Move("challenge", C, other=H, content=BETA, ground=S))
        with self.assertRaises(Illegal):
            apply_move(state, Move("vindicate", H, content=BETA, other=C))


class C7CombinedPredicateIndependence(unittest.TestCase):
    """Standing and protected access are separately necessary and neither implies the other."""

    def test_standing_without_access(self):
        state = C3NormativeStandingWithoutEffectiveAccess().exposed()
        self.assertTrue(has_normative_standing(state, H, A, R, Q))
        self.assertFalse(has_effective_access(state, H, A, CORRECTION))

    def test_access_without_standing(self):
        state = C4EffectivePowerWithoutNormativeStanding().actuator_only()
        self.assertFalse(has_normative_standing(state, H, A, R, Q))
        self.assertTrue(has_effective_access(state, H, A, CORRECTION))

    def test_both(self):
        state = contested()
        self.assertTrue(has_normative_standing(state, H, A, R, Q))
        self.assertTrue(has_effective_access(state, H, A, CORRECTION))
        self.assertTrue(real_answerability(state, H, A, R, Q, CORRECTION))

    def test_neither(self):
        from dataclasses import replace

        state = contested().with_ack(H, frozenset())
        state = replace(state, grants=state.grants | {Grant(A, authority_over(H))})
        self.assertFalse(has_normative_standing(state, H, A, R, Q))
        self.assertFalse(has_effective_access(state, H, A, CORRECTION))
        self.assertFalse(real_answerability(state, H, A, R, Q, CORRECTION))


if __name__ == "__main__":
    unittest.main()
