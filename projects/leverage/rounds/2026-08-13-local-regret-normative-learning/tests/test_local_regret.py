"""Does local lawful modification regret carry the normative-learning claim?

The tests are grouped by the question each answers: whether the construction is
the source theorem's own object, whether the lower bound holds without cancelling,
whether the process is genuinely endogenous and recurrent, and whether replay
failure touches any of it.
"""
from __future__ import annotations

import unittest
from dataclasses import fields
from fractions import Fraction

from actual import (
    ActualRun,
    bad_mass,
    loaded_start,
    local_regret,
    loss_vector,
    minimum_gap,
    point_mass,
    replay_totals,
    replenishing,
    run_actual,
    selected_dates,
)
from fixture import ALPHA, A_RHO, C, H, Q, R, U, base_state
from integration import run_learner
from learning import (
    ACKNOWLEDGE,
    DISAVOW,
    HOLD,
    LAMBDA,
    PROHIBITED_STATUS_FIELDS,
    QUERY,
    SUSPEND,
    VINDICATE,
    PublicStatus,
    public_status,
)
from moves import Move, apply_move
from surgical import (
    REPAIRS,
    SurgicalRepair,
    mixture_edges,
    modified_distribution,
    round_bad_mass,
    round_gap,
    round_regret,
    transient,
)

HORIZONS = (4, 8, 16, 32)
TARGET = next(r for r in REPAIRS if r.identifier == "answer_the_exposed_burden")


def constant(label):
    return lambda state, date: point_mass(label)


class S1TheObjectIsTheSourceTheoremsOwn(unittest.TestCase):
    """The construction is an instance of the cited definitions, not a variant."""

    def test_a_repair_is_identity_except_on_its_source_action(self):
        state = loaded_start()
        status = public_status(state, H, C)
        for repair in REPAIRS:
            image = repair.transformation(status)
            for label in LAMBDA:
                if label == repair.source and repair.fires(status):
                    self.assertEqual(image[label], repair.replacement)
                else:
                    self.assertEqual(image[label], label, msg=repair.identifier)

    def test_an_unselected_date_gives_the_identity_map(self):
        # The selector is what turns the rule on. Where it is off, the rule is the
        # identity and contributes nothing to the regret.
        quiet = base_state()
        status = public_status(quiet, H, C)
        repair = TARGET
        self.assertFalse(repair.fires(status))
        self.assertEqual(
            repair.transformation(status), {label: label for label in LAMBDA}
        )

    def test_the_modified_distribution_matches_the_sources_definition(self):
        # `f_i = sum over j with F(j) = i of p_j`.
        mixed = {label: Fraction(1, 8) for label in LAMBDA}
        image = {label: label for label in LAMBDA}
        image[HOLD] = ACKNOWLEDGE
        modified = modified_distribution(mixed, image)
        self.assertEqual(modified[HOLD], 0)
        self.assertEqual(modified[ACKNOWLEDGE], Fraction(1, 4))
        self.assertEqual(sum(modified.values()), 1)

    def test_the_rule_holds_no_callable_and_no_horizon(self):
        for repair in REPAIRS:
            for field in fields(repair):
                value = getattr(repair, field.name)
                self.assertIsInstance(value, str)
                self.assertFalse(callable(value))

    def test_the_certificate_context_still_carries_no_prohibited_field(self):
        names = {f.name for f in fields(PublicStatus)}
        for prohibited in PROHIBITED_STATUS_FIELDS:
            for name in names:
                self.assertNotIn(prohibited, name)


class S2TheLowerBoundHoldsAndDoesNotCancel(unittest.TestCase):
    """`regret >= delta * mass`, with equality for a surgical rule."""

    def test_the_bound_holds_at_every_horizon(self):
        start = loaded_start()
        for horizon in HORIZONS:
            run = run_actual(start, H, C, horizon, constant(HOLD))
            regret = local_regret(run, TARGET, H, C)
            mass = bad_mass(run, TARGET, H, C)
            delta = minimum_gap(run, TARGET, H, C)
            self.assertIsNotNone(delta)
            self.assertGreater(delta, 0)
            self.assertGreaterEqual(regret, delta * mass)

    def test_and_holds_with_equality_because_the_rule_is_surgical(self):
        start = loaded_start()
        for horizon in HORIZONS:
            run = run_actual(start, H, C, horizon, constant(HOLD))
            regret = local_regret(run, TARGET, H, C)
            mass = bad_mass(run, TARGET, H, C)
            self.assertEqual(regret, Fraction(1, 2) * mass)
            self.assertEqual(regret, Fraction(horizon, 2))

    def test_a_broad_comparator_cancels_and_loses_the_bound(self):
        # The reason the rule has to be surgical. A comparator that also rewrites
        # a *good* action pays for it, and the payment eats the gain, so no lower
        # bound in terms of the targeted mass survives.
        # The second swap rewrites the *best* available response into a worse
        # one, so the comparator pays for it.
        broad = SurgicalRepair(
            "broad", "exposed_consequential_burden", VINDICATE, HOLD
        )
        start = loaded_start()
        horizon = 16
        mixed = {label: Fraction(1, 8) for label in LAMBDA}
        run = run_actual(start, H, C, horizon, lambda s, d: mixed)
        surgical_regret = local_regret(run, TARGET, H, C)
        combined = Fraction(0)
        for state, losses in zip(run.states, run.losses):
            status = public_status(state, H, C)
            image = TARGET.transformation(status)
            broad_image = broad.transformation(status)
            merged = {label: image[label] for label in LAMBDA}
            for label in LAMBDA:
                if label == broad.source and broad.fires(status):
                    merged[label] = broad.replacement
            modified = modified_distribution(mixed, merged)
            played = sum((mixed[a] * losses[a] for a in LAMBDA), Fraction(0))
            swapped = sum((modified[a] * losses[a] for a in LAMBDA), Fraction(0))
            combined += played - swapped
        self.assertGreater(surgical_regret, 0)
        self.assertLess(combined, surgical_regret)

    def test_the_bound_is_read_only_where_the_gap_is_positive(self):
        # One repair in the class is lawful and does *not* improve the loss. Its
        # gap is negative, so it licenses no lower bound — which is what
        # loss-blind lawfulness looks like when the two come apart.
        start = loaded_start()
        run = run_actual(start, H, C, 8, constant(DISAVOW))
        erase = next(r for r in REPAIRS if r.identifier == "answer_rather_than_erase")
        gap = minimum_gap(run, erase, H, C)
        self.assertIsNotNone(gap)
        self.assertLess(gap, 0)

    def test_a_repair_whose_selector_never_fires_reports_vacuity(self):
        start = loaded_start()
        run = run_actual(start, H, C, 8, constant(HOLD))
        undercut = next(
            r for r in REPAIRS if r.identifier == "stop_deploying_the_undercut"
        )
        self.assertEqual(selected_dates(run, undercut, H, C), 0)
        self.assertIsNone(minimum_gap(run, undercut, H, C))

    def test_that_repair_is_not_vacuous_where_the_undercutter_is_present(self):
        # Necessity witness for the vacuity report: the rule fires on a
        # trajectory where applicability is actually precluded.
        start = apply_move(loaded_start(), Move("assert", H, content=U))
        run = run_actual(start, H, C, 8, constant(HOLD))
        undercut = next(
            r for r in REPAIRS if r.identifier == "stop_deploying_the_undercut"
        )
        self.assertGreater(selected_dates(run, undercut, H, C), 0)


class S3TheProcessIsEndogenousAndRecurrent(unittest.TestCase):
    """The state carries forward, and the pattern keeps coming back."""

    def test_the_learners_action_changes_the_next_state(self):
        start = loaded_start()
        holding = run_actual(start, H, C, 6, constant(HOLD))
        answering = run_actual(start, H, C, 6, constant(ACKNOWLEDGE))
        self.assertNotEqual(holding.states[-1], answering.states[-1])
        self.assertNotEqual(holding.losses[-1], answering.losses[-1])

    def test_the_loss_vector_is_determined_before_the_action_at_that_date(self):
        # The one non-anticipation condition the source theorem needs. The loss
        # vector is a function of the state as it stands when the date opens.
        start = loaded_start()
        run = run_actual(start, H, C, 5, constant(HOLD))
        for state, losses in zip(run.states, run.losses):
            self.assertEqual(losses, loss_vector(state, H, C))

    def test_the_targeted_pattern_recurs_rather_than_saturating(self):
        start = loaded_start()
        for horizon in HORIZONS:
            run = run_actual(start, H, C, horizon, constant(HOLD))
            self.assertEqual(selected_dates(run, TARGET, H, C), horizon)

    def test_the_environment_keeps_supplying_burdens(self):
        start = loaded_start()
        run = run_actual(start, H, C, 12, constant(HOLD))
        exposed = [len(s.exposed_unacknowledged(C, H)) for s in run.states]
        self.assertGreater(max(exposed), 1)
        self.assertGreater(exposed[-1], 0)


class S4ReplayFailureDoesNotTouchTheLocalClaim(unittest.TestCase):
    """The negative control the whole round turns on."""

    def test_replay_diverges_on_the_same_run(self):
        start = loaded_start()
        gaps = []
        for horizon in HORIZONS:
            actual, transformed = replay_totals(start, H, C, horizon, TARGET, HOLD)
            gaps.append(actual - transformed)
        self.assertEqual(gaps, [Fraction(5), Fraction(13), Fraction(29), Fraction(61)])
        self.assertGreater(gaps[3] - gaps[2], gaps[2] - gaps[1])

    def test_while_the_local_quantity_tracks_the_bound_exactly(self):
        start = loaded_start()
        local = []
        for horizon in HORIZONS:
            run = run_actual(start, H, C, horizon, constant(HOLD))
            local.append(local_regret(run, TARGET, H, C))
        self.assertEqual(local, [Fraction(2), Fraction(4), Fraction(8), Fraction(16)])

    def test_and_the_two_numbers_are_different(self):
        # The point: they are not the same quantity, they diverge from each other,
        # and the theorem uses only the second.
        start = loaded_start()
        for horizon in HORIZONS:
            actual, transformed = replay_totals(start, H, C, horizon, TARGET, HOLD)
            run = run_actual(start, H, C, horizon, constant(HOLD))
            self.assertNotEqual(actual - transformed, local_regret(run, TARGET, H, C))

    def test_no_local_quantity_reads_a_transformed_trajectory(self):
        # K1. The local regret is computed from one run's states and losses; a
        # comparator trajectory is never constructed inside it.
        start = loaded_start()
        run = run_actual(start, H, C, 8, constant(HOLD))
        recomputed = Fraction(0)
        for state, mixed, losses in zip(run.states, run.mixed, run.losses):
            status = public_status(state, H, C)
            recomputed += round_regret(mixed, losses, TARGET, status)
        self.assertEqual(recomputed, local_regret(run, TARGET, H, C))


class S5TheRepositoryLearnerRunsOnThisProcess(unittest.TestCase):
    """The existing Theorem 18 implementation, driven by an endogenous loss."""

    def test_the_learner_produces_a_run(self):
        run = run_learner(loaded_start(), REPAIRS, 8)
        self.assertEqual(run.horizon, 8)
        for mixed in run.mixed:
            self.assertEqual(sum(mixed.values()), 1)

    def test_the_bound_holds_on_the_learners_run(self):
        for horizon in (8, 16):
            run = run_learner(loaded_start(), REPAIRS, horizon)
            regret = local_regret(run, TARGET, H, C)
            mass = bad_mass(run, TARGET, H, C)
            delta = minimum_gap(run, TARGET, H, C)
            self.assertGreaterEqual(regret, delta * mass)

    def test_but_the_demonstration_is_degenerate_and_says_so(self):
        # The honest limitation. The stationary construction assigns zero mass to
        # the targeted source action from the first date, so the bound is
        # satisfied without the learner ever making the mistake. That is the
        # strongest possible outcome for the inequality and no evidence at all
        # that a learner *sheds* mass it started with.
        run = run_learner(loaded_start(), REPAIRS, 16)
        self.assertEqual(bad_mass(run, TARGET, H, C), 0)
        for mixed in run.mixed:
            self.assertEqual(mixed[HOLD], 0)

    def test_the_targeted_actions_are_exactly_the_transient_ones(self):
        # The diagnosis, as structure rather than observation. A stationary
        # distribution is supported on the recurrent states, so a transient action
        # carries zero mass at every date. Here the transient set is *exactly* the
        # set of source actions the repairs point away from.
        state = loaded_start()
        status = public_status(state, H, C)
        leaking = transient(REPAIRS, status)
        self.assertEqual(leaking, frozenset({r.source for r in REPAIRS}))
        self.assertIn(HOLD, leaking)

    def test_every_repair_target_is_absorbing(self):
        # And the other half: nothing points back. Each replacement is a sink
        # under the whole class, which is what makes the sources transient.
        state = loaded_start()
        status = public_status(state, H, C)
        edges = mixture_edges(REPAIRS, status)
        for repair in REPAIRS:
            self.assertEqual(edges[repair.replacement], frozenset({repair.replacement}))

    def test_so_the_vacuity_is_structural_not_an_accident_of_this_fixture(self):
        # The consequence worth stating: a class made only of genuine repairs
        # gives every targeted action zero mass, so the conclusion holds
        # vacuously. Making the action recurrent needs a rule pointing *back into*
        # it from a repair target — a rule saying "having answered, stop
        # answering" — which is not a repair.
        state = loaded_start()
        status = public_status(state, H, C)
        for repair in REPAIRS:
            self.assertIn(repair.source, transient(REPAIRS, status))

    def test_the_reason_is_that_no_rule_maps_into_the_targeted_action(self):
        # Diagnosis rather than assertion: `hold` has no incoming edge under the
        # rule mixture, so the stationary distribution starves it immediately.
        state = loaded_start()
        status = public_status(state, H, C)
        incoming = [
            r.identifier
            for r in REPAIRS
            if any(
                r.transformation(status)[label] == HOLD
                for label in LAMBDA
                if label != HOLD
            )
        ]
        self.assertEqual(incoming, [])


if __name__ == "__main__":
    unittest.main()
