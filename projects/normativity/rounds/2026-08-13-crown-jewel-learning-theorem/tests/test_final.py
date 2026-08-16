"""The final pass: the three interfaces, the dynamics witness, and K1-K12."""
from __future__ import annotations

import ast
import inspect
import textwrap
import unittest
from fractions import Fraction


def code_body(function) -> str:
    """The function's source with its docstring removed.

    The prose deliberately *mentions* loss in order to say that the predicate does
    not read it, so a naive substring check on the raw source tests the comment
    rather than the code.
    """
    tree = ast.parse(textwrap.dedent(inspect.getsource(function)))
    node = tree.body[0]
    if (
        node.body
        and isinstance(node.body[0], ast.Expr)
        and isinstance(node.body[0].value, ast.Constant)
        and isinstance(node.body[0].value.value, str)
    ):
        node.body = node.body[1:]
    return ast.unparse(node)

import interfaces
import regenerating
from interfaces import AnswerabilityProcess, CompiledRepair, compile_repairs
from regenerating import (
    ANSWER,
    ANSWER_THE_DEMAND,
    DO_NOT_COMPOUND,
    HOLD,
    INCOHERENCE,
    REPAIRS,
    RESPONSES,
    SERVICE,
    START,
    State,
    process,
    run,
)

HORIZONS = (16, 64, 256)


class T1TheThreeInterfacesAreDistinct(unittest.TestCase):
    """`Due`, `Licensed` and performance are separate predicates. (K12)"""

    def test_the_process_exposes_three_separate_fields(self):
        fields = {f for f in vars(AnswerabilityProcess("", None, None, None, None, None, Fraction(1)))}
        for name in ("due", "licensed", "loss"):
            self.assertIn(name, fields)

    def test_licensed_does_not_read_the_loss(self):
        body = code_body(regenerating.licensed)
        for banned in ("loss", "margin", "regret", "advantage"):
            self.assertNotIn(banned, body)

    def test_due_does_not_read_the_loss(self):
        self.assertNotIn("loss", code_body(regenerating.due))

    def test_the_compiler_consults_licence_and_never_performance(self):
        body = code_body(compile_repairs)
        self.assertIn("selects", body)
        self.assertIn("is_licensed", body)
        self.assertNotIn("margin", body)
        self.assertNotIn("loss", body)


class T2LicenceIsNotPerformance(unittest.TestCase):
    """K1: `Licensed` must not reduce to 'has lower loss'."""

    def test_a_licensed_response_can_have_a_nonpositive_margin(self):
        # `hold` is licensed as an answer to the standing incoherence, and its
        # margin against `answer` is strictly negative whenever a service demand
        # is outstanding. Licence and performance disagree, visibly.
        proc = process()
        state = proc.arrive(START)
        self.assertTrue(proc.licensed(state, INCOHERENCE, HOLD))
        self.assertLess(DO_NOT_COMPOUND.margin(proc, state), 0)

    def test_while_the_targeted_repair_has_a_positive_margin(self):
        proc = process()
        state = proc.arrive(START)
        self.assertTrue(proc.licensed(state, SERVICE, ANSWER))
        self.assertGreater(ANSWER_THE_DEMAND.margin(proc, state), 0)

    def test_a_response_can_be_unlicensed_yet_lower_loss(self):
        # `answer` lowers the loss but is not a licensed answer to the
        # incoherence demand. Performance does not confer licence either.
        proc = process()
        state = proc.arrive(START)
        self.assertFalse(proc.licensed(state, INCOHERENCE, ANSWER))
        self.assertLess(proc.loss(state, ANSWER), proc.loss(state, HOLD))


class T3TheRegeneratingFixtureIsWhatItClaims(unittest.TestCase):
    """The fixture removes the defect that made the earlier question undecidable."""

    def test_the_reason_recurs_at_every_date(self):
        for horizon in HORIZONS:
            trace = run(horizon)
            self.assertEqual(trace.exposure, horizon)

    def test_the_margin_is_uniform_and_positive_throughout(self):
        trace = run(256)
        self.assertEqual(min(trace.margins), Fraction(1))
        self.assertEqual(max(trace.margins), Fraction(1))

    def test_the_loss_stays_bounded(self):
        proc = process()
        state = proc.arrive(START)
        for response in RESPONSES:
            self.assertLessEqual(proc.loss(state, response), proc.bound)
            self.assertGreaterEqual(proc.loss(state, response), 0)

    def test_the_repair_graph_is_irreducible_on_two_responses(self):
        # Both edges active, so the chain has one recurrent class and a unique
        # stationary distribution — no reducibility to pin the mass.
        proc = process()
        state = proc.arrive(START)
        self.assertEqual(ANSWER_THE_DEMAND.image(proc, state)[HOLD], ANSWER)
        self.assertEqual(DO_NOT_COMPOUND.image(proc, state)[ANSWER], HOLD)

    def test_the_return_route_is_independently_certified(self):
        # K8: the return edge answers a *different* demand, not the service one.
        self.assertEqual(ANSWER_THE_DEMAND.demand, SERVICE)
        self.assertEqual(DO_NOT_COMPOUND.demand, INCOHERENCE)
        self.assertNotEqual(ANSWER_THE_DEMAND.demand, DO_NOT_COMPOUND.demand)


class T4TheDynamicsWitness(unittest.TestCase):
    """The decisive prosecution. Recorded as a witness, not as a theorem."""

    def test_the_learner_starts_with_substantial_mass_on_the_inferior_response(self):
        trace = run(64)
        self.assertEqual(trace.target_mass[0], Fraction(1, 2))

    def test_and_sheds_it(self):
        trace = run(256)
        early = trace.share(0, 32)
        late = trace.share(224, 256)
        self.assertGreater(early, Fraction(1, 5))
        self.assertLess(late, Fraction(1, 100))
        self.assertLess(late, early)

    def test_the_uninformative_control_does_not_move_at_all(self):
        # K9: no predetermined decay. Same graph, same environment, flat loss.
        for horizon in HORIZONS:
            control = run(horizon, informative=False)
            k = max(1, horizon // 8)
            self.assertEqual(control.share(0, k), Fraction(1, 2))
            self.assertEqual(control.share(horizon - k, horizon), Fraction(1, 2))

    def test_the_conditional_rate_falls_with_the_horizon(self):
        rates = []
        for horizon in HORIZONS:
            trace = run(horizon)
            rates.append(trace.bad_mass / trace.exposure)
        for earlier, later in zip(rates, rates[1:]):
            self.assertLess(later, earlier)

    def test_the_cumulative_mass_grows_sublinearly(self):
        # `Q_T` roughly doubles as `T` quadruples — the shape the `sqrt(T)` bound
        # predicts, and far below the linear growth a non-learning play would give.
        masses = [run(h).bad_mass for h in HORIZONS]
        for horizon, mass in zip(HORIZONS, masses):
            self.assertLess(mass, Fraction(horizon, 4))
        self.assertLess(masses[2] / masses[1], Fraction(5, 2))

    def test_the_surgical_bound_holds_on_the_witness(self):
        trace = run(256)
        self.assertGreaterEqual(trace.regret, min(trace.margins) * trace.bad_mass)

    def test_no_exploration_schedule_or_warm_start_is_used(self):
        body = code_body(regenerating.run)
        for banned in ("epsilon", "explore", "warm", "anneal", "decay"):
            self.assertNotIn(banned, body)


class T5PreservedCorrections(unittest.TestCase):
    """The refinement pass's corrections must not regress."""

    def test_the_repair_selector_reads_the_state_not_the_date(self):
        body = code_body(CompiledRepair.selects)
        self.assertIn("due", body)
        self.assertNotIn("date", body)
        self.assertNotIn("horizon", body)

    def test_the_learner_commits_before_reading_the_loss(self):
        # K7. `prepare` then `distribution` then `update`, in that order.
        source = code_body(regenerating.run)
        self.assertLess(source.index("engine.prepare"), source.index("engine.update"))
        self.assertLess(
            source.index("prepared.distribution"), source.index("engine.update")
        )

    def test_the_margin_is_read_from_performance_alone(self):
        body = code_body(CompiledRepair.margin)
        self.assertIn("loss_vector", body)
        self.assertNotIn("licensed", body)

    def test_no_hidden_normative_target_appears(self):
        # K10.
        for module in (interfaces, regenerating):
            source = inspect.getsource(module)
            for banned in ("true_norm", "correct_norm", "oracle", "ground_truth"):
                self.assertNotIn(banned, source)


if __name__ == "__main__":
    unittest.main()
