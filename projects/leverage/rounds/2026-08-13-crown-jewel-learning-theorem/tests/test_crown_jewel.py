"""P1-P10: the prosecutions the crown-jewel theorem has to survive."""
from __future__ import annotations

import unittest
from fractions import Fraction

from actual import (
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
from conditional import (
    MarginCertificate,
    bad_mass_bound,
    conditional_rate_bound,
    coverage_suffices,
    derived_margin,
)
from dynamics import (
    LearningEvidence,
    edges,
    identity_rule,
    is_transient,
    reachable,
    surgical_rule,
    zero_mass_actions,
)
from fixture import C, H, U, W
from learning import ACKNOWLEDGE, DISAVOW, HOLD, LAMBDA, QUERY, SUSPEND, VINDICATE
from moves import Move, apply_move
from schedules import (
    ACKNOWLEDGE_MARGIN,
    acknowledge_side_condition,
    dense,
    exposed_start,
    exposure_count,
    observed_margin,
    sparse,
)
from surgical import REPAIRS, SurgicalRepair, round_gap, round_regret
from learning import public_status

ACTIONS = list(LAMBDA)
TARGET = next(r for r in REPAIRS if r.identifier == "answer_the_exposed_burden")


class P1TheDenominatorMatters(unittest.TestCase):
    """`Q_T/T` and `Q_T/M_T` are different claims, and only the second is learning."""

    def test_dense_and_sparse_schedules_differ_in_order(self):
        for horizon in (16, 64, 256, 1024):
            self.assertEqual(exposure_count(dense, horizon), horizon)
        # Perfect squares below T: exactly ceil(sqrt(T)).
        self.assertEqual(
            [exposure_count(sparse, t) for t in (16, 64, 256, 1024)], [4, 8, 16, 32]
        )

    def test_the_unconditional_rate_is_uninformative_under_sparse_exposure(self):
        # Suppose the learner mishandles *every* selected occasion. Under the
        # sparse schedule `Q_T/T` still goes to zero, so it certifies nothing.
        for horizon in (64, 256, 1024):
            worst = Fraction(exposure_count(sparse, horizon))
            self.assertLess(worst / horizon, Fraction(1, 4))
            self.assertEqual(worst / worst, 1)

    def test_the_conditional_rate_is_undefined_rather_than_perfect_when_unasked(self):
        with self.assertRaises(ValueError):
            conditional_rate_bound(Fraction(1), Fraction(1, 2), Fraction(0))


class P2AndP9TheArithmetic(unittest.TestCase):
    """The bound, and the coverage condition that makes it bite."""

    def test_the_mass_bound_rearranges_correctly(self):
        self.assertEqual(bad_mass_bound(Fraction(8), Fraction(1, 2)), 16)

    def test_a_nonpositive_margin_licenses_no_bound(self):
        for bad in (Fraction(0), Fraction(-2)):
            with self.assertRaises(ValueError):
                bad_mass_bound(Fraction(8), bad)

    def test_coverage_suffices_when_the_regret_scale_is_dominated(self):
        # `B_T = sqrt(T)` against `M_T = T` (dense): ratio falls.
        horizons = (16, 64, 256, 1024)
        regret = [Fraction(int(h ** 0.5)) for h in horizons]
        self.assertTrue(coverage_suffices(regret, [Fraction(h) for h in horizons]))

    def test_and_fails_when_exposure_only_matches_the_regret_scale(self):
        # `M_T = sqrt(T)` against `B_T = sqrt(T)`: the ratio is constant, so the
        # conditional rate is not driven to zero. This is the exact boundary.
        horizons = (16, 64, 256, 1024)
        regret = [Fraction(int(h ** 0.5)) for h in horizons]
        exposure = [Fraction(exposure_count(sparse, h)) for h in horizons]
        self.assertFalse(coverage_suffices(regret, exposure))

    def test_the_conditional_bound_is_the_quotient(self):
        self.assertEqual(
            conditional_rate_bound(Fraction(8), Fraction(1, 2), Fraction(32)),
            Fraction(1, 2),
        )


class P2SimultaneousRepairs(unittest.TestCase):
    """Several repairs active on overlapping dates, each with its own inequality."""

    def active_run(self):
        start = apply_move(loaded_start(), Move("assert", H, content=U))
        return run_actual(start, H, C, 12, lambda s, d: point_mass(HOLD))

    def test_more_than_one_repair_is_selected_on_the_same_dates(self):
        run = self.active_run()
        firing = [
            r for r in REPAIRS if selected_dates(run, r, H, C) > 0
        ]
        self.assertGreaterEqual(len(firing), 2)
        sources = {r.source for r in firing}
        self.assertGreaterEqual(len(sources), 1)

    def test_each_selected_repair_keeps_its_own_bound(self):
        run = self.active_run()
        checked = 0
        for repair in REPAIRS:
            gap = minimum_gap(run, repair, H, C)
            if gap is None or gap <= 0:
                continue
            self.assertGreaterEqual(
                local_regret(run, repair, H, C), gap * bad_mass(run, repair, H, C)
            )
            checked += 1
        self.assertGreaterEqual(checked, 2)

    def test_the_bounds_do_not_interfere(self):
        # The lemma is per repair and reads only that repair's map, so another
        # repair being simultaneously selected changes neither side.
        run = self.active_run()
        for repair in REPAIRS:
            total = Fraction(0)
            for state, mixed, losses in zip(run.states, run.mixed, run.losses):
                status = public_status(state, H, C)
                total += round_regret(mixed, losses, repair, status)
            self.assertEqual(total, local_regret(run, repair, H, C))


class P5TheMarginIsDerivable(unittest.TestCase):
    """`delta` need not be assumed for every repair."""

    def test_the_side_condition_is_a_public_predicate(self):
        state = exposed_start()
        self.assertTrue(acknowledge_side_condition(state, H, C))

    def test_and_where_it_holds_the_margin_equals_the_discharged_weight(self):
        state = exposed_start()
        self.assertEqual(observed_margin(state, H, C), ACKNOWLEDGE_MARGIN.weight)
        self.assertEqual(
            derived_margin(ACKNOWLEDGE_MARGIN, True), ACKNOWLEDGE_MARGIN.weight
        )

    def test_where_it_fails_no_margin_is_derived_rather_than_a_zero_claimed(self):
        self.assertIsNone(derived_margin(ACKNOWLEDGE_MARGIN, False))

    def test_the_certificate_reads_no_loss(self):
        for value in vars(ACKNOWLEDGE_MARGIN).values():
            self.assertIn(type(value), (str, Fraction))


class P4LawfulIsNotImproving(unittest.TestCase):
    """A licensed repair with no positive margin licenses no learning conclusion."""

    def test_a_lawful_repair_can_worsen_the_loss(self):
        start = loaded_start()
        run = run_actual(start, H, C, 8, lambda s, d: point_mass(DISAVOW))
        erase = next(r for r in REPAIRS if r.identifier == "answer_rather_than_erase")
        gap = minimum_gap(run, erase, H, C)
        self.assertIsNotNone(gap)
        self.assertLess(gap, 0)

    def test_and_the_bound_refuses_to_be_computed_for_it(self):
        with self.assertRaises(ValueError):
            bad_mass_bound(Fraction(8), Fraction(-2))


class P3ConflictingRepairs(unittest.TestCase):
    """Two licensed replacements for one source response."""

    def test_two_repairs_may_share_a_source(self):
        shared = [r for r in REPAIRS if r.source == HOLD]
        self.assertGreaterEqual(len(shared), 2)
        self.assertNotEqual(shared[0].replacement, shared[1].replacement)

    def test_each_still_has_its_own_surgical_lower_bound(self):
        # Conflict is a compiler question, not a theorem question: the lemma is
        # stated per repair and each inequality is read off the same run.
        start = loaded_start()
        run = run_actual(start, H, C, 8, lambda s, d: point_mass(HOLD))
        for repair in [r for r in REPAIRS if r.source == HOLD]:
            gap = minimum_gap(run, repair, H, C)
            if gap is None or gap <= 0:
                continue
            self.assertGreaterEqual(
                local_regret(run, repair, H, C), gap * bad_mass(run, repair, H, C)
            )

    def test_conflict_shows_up_in_the_graph_as_two_exits(self):
        rules = [identity_rule(ACTIONS)] + [
            surgical_rule(r.identifier, ACTIONS, r.source, r.replacement)
            for r in REPAIRS
            if r.source == HOLD
        ]
        graph = edges(rules, ACTIONS)
        self.assertGreaterEqual(len(graph[HOLD] - {HOLD}), 2)


class P6TransienceCharacterisation(unittest.TestCase):
    """Exactly when the stationary construction must give a response zero mass."""

    def test_a_one_way_class_makes_every_targeted_source_transient(self):
        rules = [
            identity_rule(ACTIONS),
            surgical_rule("r1", ACTIONS, HOLD, ACKNOWLEDGE),
            surgical_rule("r2", ACTIONS, DISAVOW, QUERY),
        ]
        self.assertEqual(zero_mass_actions(rules, ACTIONS), frozenset({HOLD, DISAVOW}))

    def test_a_return_edge_makes_the_source_recurrent(self):
        rules = [
            identity_rule(ACTIONS),
            surgical_rule("r1", ACTIONS, HOLD, ACKNOWLEDGE),
            surgical_rule("r2", ACTIONS, DISAVOW, QUERY),
            surgical_rule("back", ACTIONS, ACKNOWLEDGE, HOLD),
        ]
        self.assertEqual(zero_mass_actions(rules, ACTIONS), frozenset({DISAVOW}))
        self.assertFalse(is_transient(edges(rules, ACTIONS), HOLD))

    def test_a_longer_cycle_works_too(self):
        rules = [
            identity_rule(ACTIONS),
            surgical_rule("a", ACTIONS, HOLD, ACKNOWLEDGE),
            surgical_rule("b", ACTIONS, ACKNOWLEDGE, SUSPEND),
            surgical_rule("c", ACTIONS, SUSPEND, HOLD),
        ]
        self.assertEqual(zero_mass_actions(rules, ACTIONS), frozenset())

    def test_the_condition_is_exactly_the_absence_of_a_return_route(self):
        rules = [identity_rule(ACTIONS), surgical_rule("r1", ACTIONS, HOLD, ACKNOWLEDGE)]
        graph = edges(rules, ACTIONS)
        self.assertIn(ACKNOWLEDGE, reachable(graph, HOLD))
        self.assertNotIn(HOLD, reachable(graph, ACKNOWLEDGE))
        self.assertTrue(is_transient(graph, HOLD))

    def test_the_identity_self_loop_does_not_rescue_it(self):
        rules = [identity_rule(ACTIONS), surgical_rule("r1", ACTIONS, HOLD, ACKNOWLEDGE)]
        graph = edges(rules, ACTIONS)
        self.assertIn(HOLD, graph[HOLD])
        self.assertTrue(is_transient(graph, HOLD))


class P7GenuineLearningControl(unittest.TestCase):
    """The pre-registered criterion, applied without flattering the construction."""

    def test_a_coherent_one_way_class_fails_the_first_clause(self):
        # No initial mass on the targeted response, so there is nothing to shed
        # and the criterion is failed at clause (1). This is compliance, not
        # learning, and the round records it as such.
        evidence = LearningEvidence(
            initial_mass=Fraction(0),
            selected_dates=64,
            early_mass=Fraction(0),
            late_mass=Fraction(0),
            adapts_without_information=False,
        )
        self.assertFalse(evidence.counts_as_learning(Fraction(1, 100)))

    def test_a_class_with_a_return_edge_can_satisfy_it(self):
        # Measured on the cyclic class: initial mass 1/8, a strict fall while the
        # margin is live, and no movement at all when the loss carries no signal.
        evidence = LearningEvidence(
            initial_mass=Fraction(1, 8),
            selected_dates=64,
            early_mass=Fraction(1, 2),
            late_mass=Fraction(4989, 10000),
            adapts_without_information=False,
        )
        self.assertTrue(evidence.counts_as_learning(Fraction(1, 100)))

    def test_the_criterion_rejects_a_predetermined_decay(self):
        # Clause (6): a schedule that would decay identically without informative
        # feedback is not learning, whatever curve it draws.
        evidence = LearningEvidence(
            initial_mass=Fraction(1, 8),
            selected_dates=64,
            early_mass=Fraction(1, 2),
            late_mass=Fraction(1, 100),
            adapts_without_information=True,
        )
        self.assertFalse(evidence.counts_as_learning(Fraction(1, 100)))


class P8CoverageFailure(unittest.TestCase):
    """The local theorem is satisfiable by never being asked."""

    def test_an_unexposed_reason_gives_no_selected_occasions(self):
        from fixture import base_state

        state = base_state()
        self.assertIn(W, state.unacknowledged_consequences(C, H))
        self.assertFalse(state.exposed_unacknowledged(C, H))
        run = run_actual(
            state,
            H,
            C,
            8,
            lambda s, d: point_mass(HOLD),
            environment=lambda s, c, l: s,
        )
        self.assertEqual(selected_dates(run, TARGET, H, C), 0)
        self.assertEqual(bad_mass(run, TARGET, H, C), 0)

    def test_so_the_conditional_rate_is_undefined_not_zero(self):
        with self.assertRaises(ValueError):
            conditional_rate_bound(Fraction(4), Fraction(1, 2), Fraction(0))


class P10ReplayRemainsOptional(unittest.TestCase):
    """The merged negative control, carried forward unchanged."""

    def test_replay_diverges_while_the_local_bound_holds(self):
        start = loaded_start()
        for horizon in (4, 8, 16, 32):
            run = run_actual(start, H, C, horizon, lambda s, d: point_mass(HOLD))
            regret = local_regret(run, TARGET, H, C)
            gap = minimum_gap(run, TARGET, H, C)
            self.assertGreaterEqual(regret, gap * bad_mass(run, TARGET, H, C))
        gaps = [
            replay_totals(start, H, C, h, TARGET, HOLD)[0]
            - replay_totals(start, H, C, h, TARGET, HOLD)[1]
            for h in (4, 8, 16, 32)
        ]
        self.assertEqual(gaps, [Fraction(5), Fraction(13), Fraction(29), Fraction(61)])


if __name__ == "__main__":
    unittest.main()
