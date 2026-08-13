"""The refinement pass: what the pressing found, as checks.

Six pressures, in order: the loss dependency overclaim, exposure gating, the
legality/compilation/performance separation, commitment versus entitlement,
action semantics, and endogenous evolution. Plus the public-status sufficiency
question and coordinated standards drift.
"""
from __future__ import annotations

import unittest
from dataclasses import fields, replace
from fractions import Fraction

from corrigibility import all_moves
from evolving import (
    distortion,
    distortion_profile,
    expose_next,
    local_regret,
    replay_regret,
    replenish,
    run_trajectory,
)
from fixture import (
    A,
    ACT_C,
    ACT_X,
    ALPHA,
    A_RHO,
    A_RHO_FROM_ALPHA,
    BETA,
    C,
    CORRECTION,
    H,
    OPERATIONS,
    P,
    P_ENTAILS_Q,
    Q,
    Q_ENTAILS_W,
    R,
    RHO,
    S,
    U,
    W,
    base_state,
)
from learning import (
    ACKNOWLEDGE,
    DISAVOW,
    HOLD,
    LAMBDA,
    PROGRAMS,
    QUERY,
    SELF_REVISE,
    SUSPEND,
    VINDICATE,
    PublicStatus,
    certify,
    decode,
    defect,
    interpret,
    is_lawful,
    loss_vector,
    practical_authority_defect,
    public_status,
    step,
    transformation,
)
from moves import Illegal, Move, apply_move, is_legal
from scorekeeping import Challenge, Grant, authority_over, pair

HORIZONS = (4, 8, 16, 32)


def loaded():
    state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
    return apply_move(state, Move("assert", H, content=ALPHA))


class P1LossDependency(unittest.TestCase):
    """The overclaim, confirmed, and the repair."""

    def test_the_practical_term_was_self_launderable(self):
        # The defect that motivated the split, kept as a live witness. `H` holds
        # authority over its own authority, so it discharges an unsupported
        # practical commitment by granting itself the subject — answering nothing.
        state = apply_move(base_state(), Move("undertake", H, content=ACT_X))
        self.assertEqual(practical_authority_defect(state, H, C), 1)
        grant = Move("grant", H, other=H, subject=OPERATIONS)
        self.assertTrue(is_legal(state, grant))
        after = apply_move(state, grant)
        self.assertEqual(practical_authority_defect(after, H, C), 0)
        # Nothing that counts as an answer changed.
        self.assertEqual(after.ack[H], state.ack[H])
        self.assertEqual(after.challenges, state.challenges)
        self.assertEqual(after.practice[C], state.practice[C])

    def test_and_it_is_excluded_from_the_theorem_facing_loss(self):
        state = apply_move(base_state(), Move("undertake", H, content=ACT_X))
        before = defect(state, H, C)
        after = apply_move(state, Move("grant", H, other=H, subject=OPERATIONS))
        self.assertEqual(defect(after, H, C), before)

    def test_the_exact_class_of_edits_the_loss_resists(self):
        # Stated as an enumeration rather than as prose: over the whole grammar,
        # the only moves of `H` that lower the theorem-facing loss are recognised
        # answers. No revision of H's own standards appears.
        state = loaded()
        lowering = set()
        for move in all_moves(state, H):
            if not is_legal(state, move):
                continue
            if defect(apply_move(state, move), H, C) < defect(state, H, C):
                lowering.add(move.kind)
        self.assertTrue(lowering)
        self.assertLessEqual(lowering, {"assert", "disavow", "vindicate", "suspend"})
        for revision in (
            "revise_committive",
            "revise_permissive",
            "revise_incompatible",
            "grant",
            "revoke",
        ):
            self.assertNotIn(revision, lowering)

    def test_standards_revision_cannot_touch_it_at_all(self):
        state = loaded()
        before = defect(state, H, C)
        for move in all_moves(state, H):
            if move.kind not in (
                "revise_committive",
                "revise_permissive",
                "revise_incompatible",
            ):
                continue
            if not is_legal(state, move):
                continue
            self.assertEqual(defect(apply_move(state, move), H, C), before, msg=str(move))

    def test_a_recognised_answer_does_lower_it(self):
        state = loaded()
        before = defect(state, H, C)
        self.assertLess(defect(step(state, H, C, VINDICATE), H, C), before)


class P2ExposureGating(unittest.TestCase):
    """A consequence is charged when it is raised, not when it is entailed."""

    def test_a_latent_consequence_is_attributed_and_not_charged(self):
        state = base_state()
        self.assertIn(W, state.commitments(C, H))
        self.assertIn(W, state.unacknowledged_consequences(C, H))
        self.assertNotIn(W, state.exposed_unacknowledged(C, H))
        self.assertEqual(defect(state, H, C), 0)

    def test_raising_it_makes_it_due(self):
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        self.assertIn(W, state.exposed_unacknowledged(C, H))
        self.assertEqual(defect(state, H, C), Fraction(1, 2))

    def test_the_exposed_burden_survives_self_revision(self):
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        revised = apply_move(
            state, Move("revise_committive", H, rule=Q_ENTAILS_W, present=False)
        )
        self.assertIn(W, revised.exposed_unacknowledged(C, H))
        self.assertEqual(defect(revised, H, C), defect(state, H, C))

    def test_and_falls_to_a_recognised_disposition(self):
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        answered = apply_move(state, Move("assert", H, content=W))
        self.assertEqual(defect(answered, H, C), 0)

    def test_the_gate_is_what_stops_a_logical_omniscience_norm(self):
        # Without the gate every consequence of everything said would be a debt.
        # The fixture's closure is larger than its acknowledgments at the very
        # first position, and charges nothing.
        state = base_state()
        self.assertGreater(
            len(state.unacknowledged_consequences(C, H)),
            len(state.exposed_unacknowledged(C, H)),
        )


class P3LegalityCompilationPerformance(unittest.TestCase):
    """Three notions, separated."""

    def test_protocol_legality_is_not_normative_licence(self):
        # `self-revise` is a perfectly legal move and no certificate licenses it
        # as a repair. Legality of the transition and lawfulness of the
        # transformation are different predicates over different objects.
        state = loaded()
        move = decode(state, H, C, SELF_REVISE)
        self.assertIsNotNone(move)
        self.assertTrue(is_legal(state, move))
        licensed = {
            p.identifier
            for p in PROGRAMS
            if interpret(p, public_status(state, H, C), HOLD) == SELF_REVISE
        }
        self.assertEqual(licensed, set())

    def test_every_nonidentity_program_names_a_positive_public_reason(self):
        for program in PROGRAMS:
            if program.identifier == "identity":
                self.assertEqual(program.certificate, "none")
                continue
            self.assertNotEqual(program.certificate, "none")
            self.assertIsInstance(program.certificate, str)

    def test_the_compiler_never_sees_the_loss(self):
        # `certify` takes a status and nothing else. Two states with the same
        # status and different loss vectors are certified identically.
        state = loaded()
        heavier = apply_move(state, Move("query", C, other=H, content=BETA))
        status_a, status_b = public_status(state, H, C), public_status(heavier, H, C)
        if status_a == status_b:
            self.assertNotEqual(loss_vector(state, H, C), loss_vector(heavier, H, C))
            for program in PROGRAMS:
                self.assertEqual(
                    is_lawful(program, status_a), is_lawful(program, status_b)
                )

    def test_lawfulness_and_improvement_come_apart_in_both_directions(self):
        # A program can be licensed where it does not help, and unlicensed where
        # it would. If lawfulness tracked improvement, the learner could game it.
        state = loaded()
        status = public_status(state, H, C)
        losses = loss_vector(state, H, C)
        program = next(p for p in PROGRAMS if p.identifier == "query_not_disavow")
        self.assertTrue(is_lawful(program, status))
        target = interpret(program, status, DISAVOW)
        self.assertGreaterEqual(losses[target], losses[DISAVOW])

    def test_the_certificate_is_data_not_a_callable(self):
        for program in PROGRAMS:
            for field in fields(program):
                self.assertIsInstance(getattr(program, field.name), str)


class P4CommitmentVersusEntitlement(unittest.TestCase):
    """The two relations are genuinely separate."""

    def test_a_committive_rule_transmits_commitment_without_entitlement(self):
        state = base_state()
        self.assertIn(Q_ENTAILS_W, state.practice[C].committive)
        self.assertNotIn(Q_ENTAILS_W, state.practice[C].permissive)
        self.assertIn(W, state.commitments(C, H))
        self.assertNotIn(W, state.entitlements(C, H))
        self.assertIn(W, state.unentitled_commitments(C, H))
        # Unentitled is not precluded: nothing incompatible is held.
        self.assertNotIn(W, state.precluded_commitments(C, H))

    def test_a_permissive_rule_does_transmit_entitlement(self):
        state = base_state()
        self.assertIn(P_ENTAILS_Q, state.practice[C].permissive)
        self.assertIn(Q, state.entitlements(C, H))

    def test_a_pattern_may_be_declared_in_both(self):
        state = base_state()
        for relation in (state.practice[C].committive, state.practice[C].permissive):
            self.assertIn(RHO, relation)

    def test_the_undercutter_still_defeats_the_downstream_entitlement(self):
        loaded_here = apply_move(base_state(), Move("assert", H, content=ALPHA))
        self.assertIn(BETA, loaded_here.entitlements(C, H))
        undercut = apply_move(loaded_here, Move("assert", H, content=U))
        self.assertNotIn(BETA, undercut.entitlements(C, H))
        self.assertIn(BETA, undercut.commitments(C, H))

    def test_but_only_a_rho_is_precluded_and_this_is_the_dependency(self):
        # Recorded rather than patched. While committive rules transmitted
        # entitlement, `beta` was precluded and entered the loss directly. Under
        # the faithful separation the loss reaches `beta` only through exposure or
        # challenge, and charges `a_rho` directly.
        undercut = apply_move(
            apply_move(base_state(), Move("assert", H, content=ALPHA)),
            Move("assert", H, content=U),
        )
        self.assertIn(A_RHO, undercut.precluded_commitments(C, H))
        self.assertNotIn(BETA, undercut.precluded_commitments(C, H))

    def test_vindication_needs_an_entitlement_preserving_route(self):
        # A committive rule cannot vindicate: it transmits commitment and settles
        # nothing about title.
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        state = apply_move(state, Move("challenge", C, other=H, content=W, ground=R))
        without = state.with_practice(
            C, state.practice[C].with_permissive(P_ENTAILS_Q, False)
        )
        with self.assertRaises(Illegal):
            apply_move(without, Move("vindicate", H, content=W, other=C))


class P5ActionSemantics(unittest.TestCase):
    """Labels perform the operation their names claim."""

    def undercut(self):
        return apply_move(
            apply_move(base_state(), Move("assert", H, content=ALPHA)),
            Move("assert", H, content=U),
        )

    def test_suspend_is_not_retraction(self):
        state = self.undercut()
        move = decode(state, H, C, SUSPEND)
        self.assertEqual(move.kind, "suspend")
        after = apply_move(state, move)
        # The commitment survives and stays attributable; what stops is reliance.
        self.assertIn(A_RHO, after.commitments(C, H))
        self.assertIn((H, A_RHO), after.suspensions)
        self.assertEqual(after.ack[H], state.ack[H])

    def test_suspension_discounts_only_what_the_scorekeeper_takes_to_be_undercut(self):
        # It cannot be self-awarded: suspending something this scorekeeper does
        # not regard as blocked changes nothing in that scorekeeper's score.
        state = base_state()
        self.assertNotIn(Q, state.blocked(C, H))
        after = apply_move(state, Move("suspend", H, content=Q))
        self.assertEqual(defect(after, H, C), defect(state, H, C))

    def test_suspension_does_reduce_a_genuine_preclusion(self):
        state = self.undercut()
        before = defect(state, H, C)
        after = step(state, H, C, SUSPEND)
        self.assertLess(defect(after, H, C), before)

    def test_query_has_a_real_public_effect_where_the_content_is_unraised(self):
        state = base_state()
        after = apply_move(state, Move("query", C, other=H, content=W))
        self.assertNotEqual(after.exposures, state.exposures)
        self.assertNotEqual(after, state)
        self.assertGreater(defect(after, H, C), defect(state, H, C))

    def test_and_is_redundant_on_a_content_a_challenge_already_raised(self):
        # Why the label is `query` and not `reopen`. Decoded against a live
        # challenge it re-raises what the challenge already raised, so its own
        # effect is nil there. The comparator that uses it carries its force in
        # the substitution away from `disavow`, and the label now says only what
        # the move does.
        state = loaded()
        move = decode(state, H, C, QUERY)
        self.assertEqual(move.kind, "query")
        self.assertEqual(apply_move(state, move), state)

    def test_the_comparators_force_is_the_refusal_to_disavow(self):
        # A position where the erasure bites: the only acknowledgment is the
        # basis of the challenged commitment, so disavowing it makes the
        # challenge lapse.
        state = apply_move(
            base_state(), Move("challenge", C, other=H, content=Q, ground=R)
        )
        self.assertEqual(state.ack[H], frozenset({P}))
        program = next(p for p in PROGRAMS if p.identifier == "query_not_disavow")
        status = public_status(state, H, C)
        self.assertEqual(interpret(program, status, DISAVOW), QUERY)
        erased = step(state, H, C, DISAVOW)
        refused = step(state, H, C, QUERY)
        # Disavowing the basis makes the challenge lapse; refusing to erase keeps
        # the commitment in force and the challenge live.
        self.assertFalse(erased.live_challenges(C, H))
        self.assertTrue(refused.live_challenges(C, H))

    def test_disavow_and_suspend_are_different_operations(self):
        state = self.undercut()
        suspended = apply_move(state, Move("suspend", H, content=A_RHO))
        disavowed = apply_move(state, Move("disavow", H, content=A_RHO))
        self.assertNotEqual(suspended, disavowed)
        self.assertIn(A_RHO, suspended.ack[H] | {A_RHO})
        self.assertNotIn(A_RHO, disavowed.ack[H])

    def test_vindication_does_not_survive_the_premises_being_undercut(self):
        # A vindication displayed against a challenge is not a terminal bit: the
        # same display is refused once the justifying premise loses its title.
        state = apply_move(base_state(), Move("assert", H, content=ALPHA))
        state = apply_move(state, Move("challenge", C, other=H, content=BETA, ground=S))
        self.assertTrue(is_legal(state, Move("vindicate", H, content=BETA, other=C)))
        undercut = apply_move(state, Move("assert", H, content=U))
        self.assertFalse(is_legal(undercut, Move("vindicate", H, content=BETA, other=C)))


class P6EndogenousEvolution(unittest.TestCase):
    """The sharpest hypothesis: does the additive reduction survive evolution?"""

    def test_the_process_really_evolves(self):
        start = loaded()
        run = run_trajectory(start, H, C, 6, lambda s, d: HOLD)
        self.assertNotEqual(run.states[0], run.states[-1])
        self.assertGreater(len(set(run.states)), 1)

    def test_vindicate_live_looks_bounded_under_the_first_environment(self):
        # And this is the trap. Distortion is exactly one at every horizon, which
        # reads as a structural stability property and is not one.
        program = next(p for p in PROGRAMS if p.identifier == "vindicate_live")
        start = loaded()
        for horizon in HORIZONS:
            self.assertEqual(distortion(start, H, C, horizon, program, HOLD), 1)
            self.assertEqual(local_regret(start, H, C, horizon, program, HOLD), horizon)

    def test_but_that_is_saturation_and_it_breaks_when_challenges_replenish(self):
        # The correction. Under the first environment there is exactly one live
        # challenge ever, so a comparator that discharges challenges can only gain
        # a bounded amount. Replenish the licensing condition and the distortion
        # grows with the horizon like every other program.
        program = next(p for p in PROGRAMS if p.identifier == "vindicate_live")
        start = loaded()
        values = [
            abs(
                local_regret(start, H, C, horizon, program, HOLD, replenish)
                - replay_regret(start, H, C, horizon, program, HOLD, replenish)
            )
            for horizon in HORIZONS
        ]
        self.assertEqual(values, [2, 10, 26, 58])
        self.assertGreater(values[3] - values[2], values[2] - values[1])

    def test_the_replenishing_environment_really_replenishes(self):
        # Necessity witness for the correction: an environment that silently
        # failed to add challenges would show boundedness for a third wrong
        # reason. Under `hold` the live count rises and stays up.
        start = loaded()
        run = run_trajectory(start, H, C, 8, lambda s, d: HOLD, replenish)
        live = [len(s.live_challenges(C, H)) for s in run.states]
        self.assertEqual(max(live), 3)
        self.assertGreater(live[-1], 1)

    def test_acknowledge_exposed_has_distortion_growing_with_the_horizon(self):
        # The negative half. Acknowledging changes what is subsequently exposed,
        # so the repair's effect compounds and the additive comparison stops
        # tracking the replay.
        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        start = loaded()
        profile = distortion_profile(start, H, C, HORIZONS, program, HOLD)
        values = [d for _, _, _, d in profile]
        self.assertEqual(values, [1, 7, 19, 43])
        self.assertGreater(values[-1], values[0])
        # Growth is not sublinear: successive doublings of the horizon more than
        # double the gap's increments.
        self.assertGreater(values[3] - values[2], values[2] - values[1])

    def test_no_nonidentity_program_keeps_bounded_distortion(self):
        # The pass's main negative result. Once each program's licensing condition
        # is allowed to recur, every non-identity comparator's local comparison
        # drifts from its replay without bound. The additive reduction the
        # Phi-regret bridge needs does not hold for any of them.
        start = loaded()
        for identifier in ("vindicate_live", "acknowledge_exposed"):
            program = next(p for p in PROGRAMS if p.identifier == identifier)
            values = [
                abs(
                    local_regret(start, H, C, horizon, program, HOLD, replenish)
                    - replay_regret(start, H, C, horizon, program, HOLD, replenish)
                )
                for horizon in HORIZONS
            ]
            self.assertGreater(values[-1], values[0], msg=identifier)
            self.assertGreater(values[3] - values[2], values[2] - values[1], msg=identifier)

    def test_the_coupling_contributes_but_is_not_the_cause(self):
        # A demand process that never reads the learner's acknowledgments still
        # produces growing distortion, so the endogenous coupling is not what
        # drives it. The coupling adds to the magnitude and is not necessary.
        from fixture import A_RHO, BETA, Q, W

        cycle = (A_RHO, BETA, W, Q)

        def exogenous(state, critic, learner):
            raised = len([1 for t, _ in state.exposures if t == learner])
            content = cycle[raised % len(cycle)]
            if (learner, content) in state.exposures:
                return state
            return apply_move(
                state, Move("query", critic, other=learner, content=content)
            )

        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        start = loaded()
        values = [
            abs(
                local_regret(start, H, C, horizon, program, HOLD, exogenous)
                - replay_regret(start, H, C, horizon, program, HOLD, exogenous)
            )
            for horizon in HORIZONS
        ]
        self.assertEqual(values, [1, 5, 13, 29])
        endogenous = [
            distortion(start, H, C, horizon, program, HOLD) for horizon in HORIZONS
        ]
        self.assertEqual(endogenous, [1, 7, 19, 43])
        self.assertGreater(endogenous[-1], values[-1])


class P7PublicStatusSufficiency(unittest.TestCase):
    """Is the guard avoiding date-indexing by being too weak?"""

    def challenged_by(self, challenger):
        state = apply_move(base_state(), Move("assert", H, content=ALPHA))
        if challenger != C:
            state = apply_move(state, Move("assert", challenger, content=R))
        return apply_move(
            state, Move("challenge", challenger, other=H, content=Q, ground=R)
        )

    def test_the_status_conflated_challenges_that_differ_in_standing(self):
        # The gap this pass found. The six original booleans do not record who
        # raised the challenge, while the decoder directs the vindication at the
        # challenger — so the guard was coarser than the move it licenses.
        by_c = self.challenged_by(C)
        by_a = self.challenged_by(A)
        self.assertNotEqual(
            decode(by_c, H, C, VINDICATE).other, decode(by_a, H, C, VINDICATE).other
        )

    def test_the_enrichment_separates_them_by_a_property_not_a_name(self):
        by_c = self.challenged_by(C)
        with_authority = replace(
            by_c, grants=by_c.grants | {Grant(C, CORRECTION)}
        )
        self.assertNotEqual(
            public_status(by_c, H, C), public_status(with_authority, H, C)
        )
        self.assertTrue(
            public_status(with_authority, H, C).challenger_holds_corrective_authority
        )

    def test_the_status_still_carries_no_identity_and_no_date(self):
        state = self.challenged_by(C)
        status = public_status(state, H, C)
        for field in fields(PublicStatus):
            self.assertEqual(field.type, "bool")
            self.assertNotIn("date", field.name)
            self.assertNotIn("agent", field.name)

    def test_a_residual_conflation_remains_and_is_reported(self):
        # Enrichment closed the standing difference and not the content
        # difference: two live challenges on different contents with the same
        # booleans still receive the same map. Recorded as the remaining gap
        # rather than closed, because closing it by adding the content would put
        # an identity in the guard.
        first = apply_move(
            apply_move(base_state(), Move("assert", H, content=ALPHA)),
            Move("challenge", C, other=H, content=Q, ground=R),
        )
        second = apply_move(first, Move("challenge", C, other=H, content=BETA, ground=S))
        if public_status(first, H, C) == public_status(second, H, C):
            for program in PROGRAMS:
                self.assertEqual(
                    transformation(program, first, H, C),
                    transformation(program, second, H, C),
                )


class P8CoordinatedStandardsDrift(unittest.TestCase):
    """What the separation buys, and exactly where it stops."""

    def test_unilateral_self_release_stays_blocked(self):
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        before = defect(state, H, C)
        drifted = apply_move(
            state, Move("revise_committive", H, rule=Q_ENTAILS_W, present=False)
        )
        self.assertEqual(defect(drifted, H, C), before)

    def test_but_coordinated_drift_dissolves_the_burden(self):
        # Both parties revise, the public acknowledged history is untouched, and
        # the burden is gone. This is the exact limit of what the write
        # separation buys.
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        self.assertGreater(defect(state, H, C), 0)
        drifted = state
        for agent in (H, C):
            drifted = apply_move(
                drifted, Move("revise_committive", agent, rule=Q_ENTAILS_W, present=False)
            )
        self.assertEqual(drifted.ack[H], state.ack[H])
        self.assertEqual(drifted.ack[C], state.ack[C])
        self.assertEqual(defect(drifted, H, C), 0)

    def test_the_drift_took_two_agents_and_neither_could_do_it_alone(self):
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        for agent in (H, C):
            alone = apply_move(
                state, Move("revise_committive", agent, rule=Q_ENTAILS_W, present=False)
            )
            if agent == H:
                self.assertGreater(defect(alone, H, C), 0)
            else:
                # Only the scorekeeper whose practice the loss reads can move it,
                # and moving it is not something the learner can bring about.
                self.assertEqual(defect(alone, H, C), 0)
                self.assertNotEqual(agent, H)

    def test_no_move_of_the_learner_produces_the_critics_revision(self):
        state = apply_move(base_state(), Move("query", C, other=H, content=W))
        target = apply_move(
            state, Move("revise_committive", C, rule=Q_ENTAILS_W, present=False)
        )
        for move in all_moves(state, H):
            if not is_legal(state, move):
                continue
            self.assertNotEqual(apply_move(state, move), target, msg=str(move))


if __name__ == "__main__":
    unittest.main()
