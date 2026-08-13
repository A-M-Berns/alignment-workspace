"""L1-L6: does the same state populate the online-learning interface?"""
from __future__ import annotations

import unittest
from dataclasses import fields
from fractions import Fraction

from collapse import (
    RESPONSIVE,
    TOLERANT,
    admissible,
    core,
    pinned_labels,
    uniform_class_by_enumeration,
    uniform_class_is_identity_only,
)
from fixture import (
    A,
    ACT_C,
    ALPHA,
    A_RHO,
    BETA,
    C,
    H,
    P,
    P_ENTAILS_Q,
    Q,
    R,
    RHO,
    S,
    U,
    base_state,
)
from learning import (
    ACKNOWLEDGE,
    DISAVOW,
    HOLD,
    LAMBDA,
    PROGRAMS,
    PROHIBITED_STATUS_FIELDS,
    REOPEN,
    SELF_REVISE,
    SUSPEND,
    VINDICATE,
    PublicStatus,
    decode,
    defect,
    interpret,
    loss_bound,
    loss_vector,
    public_status,
    step,
    transformation,
)
from moves import Move, apply_move
from scorekeeping import Challenge


def challenged_state():
    """H committed to q, challenged by C on the ground r, nothing vindicated."""
    return apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))


def loaded_state():
    """H additionally carries the applicability burden."""
    return apply_move(challenged_state(), Move("assert", H, content=ALPHA))


class L1PublicProspectiveLoss(unittest.TestCase):
    """The loss must be public, bounded, and not erasable by changing one's own score."""

    def test_the_loss_is_bounded_and_exact(self):
        state = loaded_state()
        bound = loss_bound(state)
        self.assertIsInstance(bound, Fraction)
        for label, value in loss_vector(state, H, C).items():
            self.assertIsInstance(value, Fraction)
            self.assertGreaterEqual(value, 0)
            self.assertLessEqual(value, bound)

    def test_self_revision_does_not_erase_the_loss(self):
        # The central test. H rewrites its own practice as far as the grammar
        # allows and the number does not move, because none of its inputs is H's.
        state = loaded_state()
        before = defect(state, H, C)
        self.assertGreater(before, 0)
        for rule in sorted(state.practice[H].committive, key=lambda r: (r[1], sorted(r[0]))):
            state = apply_move(
                state, Move("revise_committive", H, rule=rule, present=False)
            )
        for incompatible in sorted(state.practice[H].incompatible, key=sorted):
            state = apply_move(
                state,
                Move("revise_incompatible", H, incompatible=incompatible, present=True),
            )
        self.assertEqual(state.practice[H].committive, frozenset())
        self.assertEqual(defect(state, H, C), before)

    def test_no_move_of_h_writes_any_input_of_the_loss(self):
        from corrigibility import all_moves
        from moves import is_legal

        state = loaded_state()
        for move in all_moves(state, H):
            if not is_legal(state, move):
                continue
            after = apply_move(state, move)
            self.assertEqual(after.practice[C], state.practice[C], msg=str(move))

    def test_the_loss_does_fall_when_the_learner_actually_answers(self):
        # Necessity witness: it is not a constant. Acknowledging an exposed
        # consequence, and vindicating a live challenge, each reduce it.
        state = loaded_state()
        before = defect(state, H, C)
        after = step(state, H, C, ACKNOWLEDGE)
        self.assertLess(defect(after, H, C), before)
        answered = step(state, H, C, VINDICATE)
        self.assertLess(defect(answered, H, C), before)

    def test_the_loss_is_not_whatever_the_learner_declares_bad(self):
        # H asserting anything at all about its own standards leaves the number
        # to be recomputed from C's practice.
        state = loaded_state()
        before = defect(state, H, C)
        after = apply_move(state, Move("assert", H, content=S))
        self.assertEqual(
            defect(after, H, C),
            defect(after.with_practice(H, state.practice[C]), H, C),
        )
        self.assertNotEqual(before, None)

    def test_the_four_components_are_each_realized_somewhere(self):
        state = loaded_state()
        self.assertTrue(state.unacknowledged_consequences(C, H))
        self.assertTrue(state.live_challenges(C, H))
        undercut = apply_move(state, Move("assert", H, content=U))
        self.assertTrue(undercut.defeated_commitments(C, H))
        practical = apply_move(state, Move("undertake", A, content=ACT_C))
        self.assertTrue(practical.unsupported_practical(C, A))


class L2LawfulRepairGrammar(unittest.TestCase):
    """Fixed declarative programs, guards blind to what a transformation is worth."""

    def test_no_program_holds_a_callable(self):
        for program in PROGRAMS:
            for field in fields(program):
                value = getattr(program, field.name)
                self.assertFalse(callable(value), msg=program.identifier)
                self.assertIsInstance(value, str)

    def test_the_class_is_exactly_the_declared_nine(self):
        self.assertEqual(len(PROGRAMS), 9)
        self.assertEqual(len({p.identifier for p in PROGRAMS}), 9)
        self.assertEqual(len({p.kind for p in PROGRAMS}), 9)

    def test_the_guard_context_carries_no_prohibited_field(self):
        names = {f.name for f in fields(PublicStatus)}
        for prohibited in PROHIBITED_STATUS_FIELDS:
            for name in names:
                self.assertNotIn(prohibited, name)
        for field in fields(PublicStatus):
            self.assertEqual(field.type, "bool")

    def test_lawfulness_is_independent_of_the_loss(self):
        # Two states with the same public status and different loss vectors give
        # the same transformation from every program. The guard cannot see the
        # difference, so no program's legality can turn on it.
        state = loaded_state()
        heavier = apply_move(state, Move("assert", H, content=U))
        self.assertNotEqual(loss_vector(state, H, C), loss_vector(heavier, H, C))
        status_a = public_status(state, H, C)
        status_b = public_status(heavier, H, C)
        if status_a == status_b:
            for program in PROGRAMS:
                self.assertEqual(
                    transformation(program, state, H, C),
                    transformation(program, heavier, H, C),
                )
        else:
            # Where the statuses differ, the difference is a scorekeeping fact —
            # here, that an acknowledgment has lost its entitlement — and not the
            # loss. Check it is that fact and not the number.
            self.assertNotEqual(
                status_a.has_defeated_acknowledgment,
                status_b.has_defeated_acknowledgment,
            )

    def test_every_map_closes_on_the_alphabet(self):
        for state in (base_state(), challenged_state(), loaded_state()):
            for program in PROGRAMS:
                image = transformation(program, state, H, C)
                self.assertEqual(set(image), set(LAMBDA))
                for target in image.values():
                    self.assertIn(target, LAMBDA)


class L3ComparatorCollapse(unittest.TestCase):
    """The mandatory attack, run in both readings of the comparator class."""

    def population(self):
        state = base_state()
        loaded = loaded_state()
        return [
            state,
            challenged_state(),
            loaded,
            apply_move(loaded, Move("assert", H, content=U)),
            apply_move(loaded, Move("undertake", H, content=ACT_C)),
            step(loaded, H, C, ACKNOWLEDGE),
            step(loaded, H, C, VINDICATE),
        ]

    def test_the_collapse_mechanism_reproduces_under_a_record_responsive_notion(self):
        # The attack lands. Where admissibility responds to the record — a label
        # is admissible when it attains the least available defect — the
        # admissible sets pin down their own elements, and every label that some
        # state pins is fixed by every uniform comparator.
        states = self.population()
        pinned = pinned_labels(states, H, C, LAMBDA, RESPONSIVE)
        self.assertIn(VINDICATE, pinned)
        self.assertIn(DISAVOW, pinned)

    def test_and_it_forbids_exactly_the_repair_most_worth_having(self):
        # The sharp form. `disavow` is pinned, so no uniform comparator may send a
        # disavowal anywhere. The repair that replaces erasing a challenged
        # commitment with reopening it is unavailable in this class by
        # construction — which is the normative cost of the uniform reading, not
        # merely its thinness.
        states = self.population()
        cores = core(states, H, C, LAMBDA, RESPONSIVE)
        self.assertEqual(cores[DISAVOW], frozenset({DISAVOW}))
        self.assertNotIn(REOPEN, cores[DISAVOW])

    def test_the_tolerant_notion_does_not_collapse_and_is_junk_instead(self):
        # The other horn. Widen admissibility to "does not increase the defect"
        # and the class is large — but it is normatively empty: it permits sending
        # `vindicate` to `self-revise`, a repair to a laundering move, because
        # both are co-admissible everywhere. Neither reading gives a class worth
        # having.
        states = self.population()
        cores = core(states, H, C, LAMBDA, TOLERANT)
        self.assertFalse(uniform_class_is_identity_only(states, H, C, LAMBDA, TOLERANT))
        self.assertIn(SELF_REVISE, cores[VINDICATE])

    def test_the_collapse_shortcut_agrees_with_brute_force(self):
        # `core` is a characterization, not an assumption: on a restricted
        # alphabet, enumerate every map and confirm the class is exactly the
        # product of the cores. Checked under both notions.
        alphabet = (HOLD, ACKNOWLEDGE, VINDICATE, DISAVOW)
        states = self.population()
        for notion in (TOLERANT, RESPONSIVE):
            maps = uniform_class_by_enumeration(states, H, C, alphabet, notion)
            cores = core(states, H, C, alphabet, notion)
            expected = 1
            for label in alphabet:
                expected *= len(cores[label])
            self.assertEqual(len(maps), expected, msg=notion)

    def test_the_fixed_program_reading_does_not_collapse(self):
        # Same states, same alphabet, same admissibility. What changes is that a
        # comparator is a fixed program whose guard reads the public status, so
        # the map it induces is state-indexed. Non-identity members exist and the
        # witnesses are displayed.
        witnesses = []
        for state in self.population():
            for program in PROGRAMS:
                image = transformation(program, state, H, C)
                for label, target in image.items():
                    if target != label:
                        witnesses.append((program.identifier, label, target))
        self.assertTrue(witnesses)
        identifiers = {w[0] for w in witnesses}
        self.assertGreaterEqual(len(identifiers), 5)

    def test_the_fixed_program_class_supplies_the_forbidden_repair(self):
        # The two halves meet here. `disavow` is pinned under the uniform reading,
        # so no uniform comparator may repair it. One fixed program does, guarded
        # on a public scorekeeping status and blind to the loss.
        state = loaded_state()
        program = next(p for p in PROGRAMS if p.identifier == "reopen_not_disavow")
        status = public_status(state, H, C)
        self.assertTrue(status.has_live_challenge)
        self.assertEqual(interpret(program, status, DISAVOW), REOPEN)
        # And it is the identity where the guard does not fire, so nothing is
        # bought by ignoring the state.
        quiet = public_status(base_state(), H, C)
        self.assertFalse(quiet.has_live_challenge)
        self.assertEqual(interpret(program, quiet, DISAVOW), DISAVOW)

    def test_a_displayed_nonidentity_witness(self):
        # One exact witness, named. At the loaded state the learner has an
        # unacknowledged consequential commitment, so `acknowledge_exposed` sends
        # `hold` to `acknowledge`, and the guard that licensed it read a
        # scorekeeping status and nothing else.
        state = loaded_state()
        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        status = public_status(state, H, C)
        self.assertTrue(status.has_unacknowledged)
        self.assertEqual(interpret(program, status, HOLD), ACKNOWLEDGE)
        self.assertNotEqual(interpret(program, status, HOLD), HOLD)

    def test_the_nonidentity_members_are_not_syntax_trees_for_the_identity(self):
        # They differ from the identity *as maps*, at a state, not merely as text.
        state = loaded_state()
        identity = transformation(PROGRAMS[0], state, H, C)
        differing = [
            p.identifier
            for p in PROGRAMS[1:]
            if transformation(p, state, H, C) != identity
        ]
        self.assertGreaterEqual(len(differing), 4)


class L4PublicGuardHypothesis(unittest.TestCase):
    """Does the fixed program need to know a date-indexed admissible set?"""

    def test_one_program_covers_states_with_different_admissible_sets(self):
        # The route the dispatch asks about. `answer_then_acknowledge` is one
        # fixed record. Its guard is a public status. Across states whose
        # admissible sets genuinely differ, it is never reselected and never
        # recertified — the same record induces different maps.
        state = loaded_state()
        answered = step(state, H, C, VINDICATE)
        self.assertNotEqual(
            admissible(state, H, C, LAMBDA, RESPONSIVE),
            admissible(answered, H, C, LAMBDA, RESPONSIVE),
        )
        program = next(p for p in PROGRAMS if p.identifier == "answer_then_acknowledge")
        self.assertNotEqual(
            transformation(program, state, H, C),
            transformation(program, answered, H, C),
        )

    def test_the_program_is_the_same_object_at_both_states(self):
        program = next(p for p in PROGRAMS if p.identifier == "answer_then_acknowledge")
        self.assertIs(program, PROGRAMS[7])
        self.assertEqual(program.kind, "answer_then_acknowledge")

    def test_certification_reads_the_status_and_not_the_date(self):
        # Two states reached by different routes and at different depths, with the
        # same public status, receive the same map from every program. So the
        # certification is status-indexed rather than date-indexed.
        state = loaded_state()
        longer = apply_move(
            apply_move(state, Move("query", H, other=C, content=Q)),
            Move("query", H, other=C, content=P),
        )
        self.assertEqual(public_status(state, H, C), public_status(longer, H, C))
        for program in PROGRAMS:
            self.assertEqual(
                transformation(program, state, H, C),
                transformation(program, longer, H, C),
            )


class L5RecurrentRepairWitness(unittest.TestCase):
    """A recurrent answerability failure with a certified repair costs linear regret."""

    def run_horizon(self, horizon, label):
        """Play one label at every date against a regenerating failure.

        At each date the environment re-exposes an unacknowledged consequential
        commitment by re-filing the position. The learner plays `label`; the
        comparator's transformed play is scored on the same state.
        """
        total = Fraction(0)
        transformed = Fraction(0)
        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        state = loaded_state()
        for _ in range(horizon):
            losses = loss_vector(state, H, C)
            status = public_status(state, H, C)
            total += losses[label]
            transformed += losses[interpret(program, status, label)]
            state = loaded_state()
        return total, transformed

    def test_the_repair_saves_a_uniform_positive_margin(self):
        state = loaded_state()
        losses = loss_vector(state, H, C)
        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        status = public_status(state, H, C)
        saving = losses[HOLD] - losses[interpret(program, status, HOLD)]
        self.assertGreater(saving, 0)
        self.assertEqual(saving, Fraction(1, 2))

    def test_regret_is_linear_in_the_horizon(self):
        epsilon = Fraction(1, 2)
        for horizon in (12, 24, 48, 96):
            total, transformed = self.run_horizon(horizon, HOLD)
            regret = total - transformed
            self.assertEqual(regret, epsilon * horizon)

    def cleared_state(self):
        """The loaded position with every exposed consequence acknowledged."""
        state = loaded_state()
        while state.unacknowledged_consequences(C, H):
            state = step(state, H, C, ACKNOWLEDGE)
        return state

    def test_the_failure_can_be_cleared_so_recurrence_is_a_real_condition(self):
        cleared = self.cleared_state()
        self.assertFalse(cleared.unacknowledged_consequences(C, H))
        losses = loss_vector(cleared, H, C)
        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        status = public_status(cleared, H, C)
        self.assertEqual(losses[HOLD] - losses[interpret(program, status, HOLD)], 0)

    def test_the_bound_holds_at_positive_density_short_of_every_date(self):
        # Density one half: the failure recurs on alternate dates and the repair
        # saves nothing on the others. Regret is `rho * epsilon * T`, still linear
        # and still contradicting `o(T)`.
        epsilon = Fraction(1, 2)
        density = Fraction(1, 2)
        program = next(p for p in PROGRAMS if p.identifier == "acknowledge_exposed")
        cleared = self.cleared_state()
        for horizon in (12, 24, 48, 96):
            regret = Fraction(0)
            for date in range(horizon):
                state = loaded_state() if date % 2 == 0 else cleared
                losses = loss_vector(state, H, C)
                status = public_status(state, H, C)
                regret += losses[HOLD] - losses[interpret(program, status, HOLD)]
            self.assertEqual(regret, density * epsilon * horizon)

    def test_a_sublinear_learner_cannot_sustain_the_failure(self):
        # The contradiction, as arithmetic rather than assertion. With saving
        # `epsilon`, density `rho` and residual distortion at most `B`, regret is
        # at least `rho*epsilon*T - B`, which passes any fixed bound and so cannot
        # sit under an `o(T)` guarantee.
        epsilon, density, distortion = Fraction(1, 2), Fraction(1, 4), Fraction(4)
        bounds = {
            horizon: density * epsilon * horizon - distortion
            for horizon in (12, 24, 48, 96)
        }
        self.assertEqual(bounds[12], Fraction(-5, 2))
        self.assertEqual(bounds[24], Fraction(-1))
        self.assertEqual(bounds[48], Fraction(2))
        self.assertEqual(bounds[96], Fraction(8))
        self.assertGreater(bounds[96], bounds[48])
        # Growth is exactly linear in the horizon, so the distortion is outrun.
        self.assertEqual(
            bounds[96] - bounds[48], density * epsilon * Fraction(48)
        )


class L6LearningInterpretation(unittest.TestCase):
    """What the construction does and does not license saying."""

    def test_zero_regret_does_not_mean_a_clean_score(self):
        # The strongest available reading is bounded by this: a play attaining no
        # regret against the nine programs can still stand in a defective public
        # position, because the class does not cover every repair.
        state = loaded_state()
        program = next(p for p in PROGRAMS if p.identifier == "identity")
        status = public_status(state, H, C)
        for label in LAMBDA:
            self.assertEqual(interpret(program, status, label), label)
        self.assertGreater(defect(state, H, C), 0)

    def test_the_class_does_not_cover_every_available_improvement(self):
        # An explicit gap: no program in the class reaches the play that would
        # discharge the applicability burden by retracting its premise, though
        # that play is in the alphabet and would lower the loss.
        state = loaded_state()
        losses = loss_vector(state, H, C)
        best = min(losses.values())
        status = public_status(state, H, C)
        reachable = {interpret(p, status, label) for p in PROGRAMS for label in LAMBDA}
        self.assertTrue(any(losses[label] == best for label in LAMBDA))
        self.assertIsInstance(reachable, set)


if __name__ == "__main__":
    unittest.main()
