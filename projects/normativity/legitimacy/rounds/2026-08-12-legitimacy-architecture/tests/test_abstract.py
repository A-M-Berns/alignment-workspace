"""The abstract interface: the four structural properties, and the footprint."""

from __future__ import annotations

import unittest
from fractions import Fraction as Q

from abstract import (ADMIT, CARRY, DISCHARGE, FootprintError, REJECT,
                      UNRESOLVED, Disposition, Edit, FATE_LIVE, Ground,
                      ReasonContext, ReasonView, Step, Trajectory, admissible,
                      apply_edit, constrain, fate, legitimate, record)
from scenarios import (REFLEXIVE, TOLLED, VERDICT, authority_ground, base_reasons,
                       base_state, impediment_ground, interval_ground)


class ConstraintStructureTests(unittest.TestCase):
    """The properties the abstract statics is asserted to have."""

    def test_no_op_is_admissible(self):
        """Non-emptiness: doing nothing is always in the constraint.

        Without it the condition could be vacuously unsatisfiable and every
        result about legitimate trajectories would be about the empty set.
        """
        state, reasons = base_state(), base_reasons()
        no_op = Edit(edit_id="no-op", dispositions=(Disposition("L1", CARRY),))
        self.assertEqual(constrain(state, reasons, no_op, REFLEXIVE).kind, ADMIT)

    def test_availability_is_a_property_of_the_view(self):
        """A ground filed later is invisible, not merely inadmissible."""
        state, reasons = base_state(), base_reasons(
            Ground("g-late", 5, frozenset({VERDICT}), "interval",
                   bears_on=frozenset({VERDICT})))
        edit = Edit(edit_id="cite-late", moves={VERDICT: Q(1)}, cited=("g-late",),
                    dispositions=(Disposition("L1", CARRY),))
        verdict = constrain(state, reasons, edit, REFLEXIVE)
        self.assertEqual(verdict.kind, REJECT)
        self.assertEqual(verdict.code, "constraint.not_available")

    def test_monotone_in_available_reasons(self):
        """More grounds on the record admit weakly more successors."""
        state = base_state()
        alphabet = (
            Edit(edit_id="move-verdict", moves={VERDICT: Q(1)}, cited=("g-interval",),
                 dispositions=(Disposition("L1", CARRY),)),
            Edit(edit_id="move-standards",
                 standards_moves={"defeat": frozenset({VERDICT})},
                 cited=("g-authority",), dispositions=(Disposition("L1", CARRY),)),
        )
        small = {e.edit_id for e in admissible(state, base_reasons(), alphabet,
                                               REFLEXIVE)}
        large = {e.edit_id for e in admissible(state, base_reasons(authority_ground()),
                                               alphabet, REFLEXIVE)}
        self.assertTrue(small.issubset(large))
        self.assertLess(len(small), len(large))

    def test_scope_is_read_through_the_standards(self):
        """A ground reaches only the coordinates the state's standards allow it."""
        state = base_state()
        narrowed = apply_edit(state, Edit(edit_id="narrow"))
        narrowed = type(state)(date=narrowed.date, commitments=narrowed.commitments,
                               standards={**state.standards,
                                          "interval": frozenset()},
                               vocabulary=narrowed.vocabulary,
                               ledger=narrowed.ledger, cost=narrowed.cost)
        edit = Edit(edit_id="move-verdict", moves={VERDICT: Q(1)},
                    cited=("g-interval",), dispositions=(Disposition("L1", CARRY),))
        self.assertEqual(constrain(state, base_reasons(), edit, REFLEXIVE).kind, ADMIT)
        blocked = constrain(narrowed, base_reasons(date=1), edit, REFLEXIVE)
        self.assertEqual(blocked.code, "constraint.out_of_scope")

    def test_reflexive_machinery_is_the_dividing_line(self):
        """Whether the reasoner's own standards are a coordinate decides whether
        an uncited standards move is licensed."""
        state, reasons = base_state(), base_reasons()
        edit = Edit(edit_id="move-standards",
                    standards_moves={"defeat": frozenset({VERDICT})},
                    dispositions=(Disposition("L1", CARRY),))
        from scenarios import NAIVE
        self.assertEqual(constrain(state, reasons, edit, NAIVE).kind, ADMIT)
        self.assertEqual(constrain(state, reasons, edit, REFLEXIVE).code,
                         "constraint.out_of_scope")

    def test_magnitude_returns_unresolved_not_rejected(self):
        """The unbacked endpoint is a normative question the interface declines to
        answer, and answering it by rejecting would be answering it."""
        state = base_state()
        reasons = base_reasons()
        within = Edit(edit_id="toll-small", moves={TOLLED: Q(1)},
                      cited=("g-impediment",), dispositions=(Disposition("L1", CARRY),))
        beyond = Edit(edit_id="toll-large", moves={TOLLED: Q(5)},
                      cited=("g-impediment",), dispositions=(Disposition("L1", CARRY),))
        self.assertEqual(constrain(state, reasons, within, REFLEXIVE).kind, ADMIT)
        verdict = constrain(state, reasons, beyond, REFLEXIVE)
        self.assertEqual(verdict.kind, UNRESOLVED)
        self.assertEqual(verdict.code, "constraint.magnitude_unresolved")

    def test_ratification_is_refused_whenever_filed(self):
        state = base_state()
        early = Ground("g-ratify", 0, frozenset({VERDICT}), "ratification",
                       bears_on=frozenset({VERDICT}))
        reasons = base_reasons(early)
        edit = Edit(edit_id="cite-ratification", moves={VERDICT: Q(1)},
                    cited=("g-ratify",), dispositions=(Disposition("L1", CARRY),))
        self.assertEqual(constrain(state, reasons, edit, REFLEXIVE).code,
                         "constraint.successor_ratification")


class FootprintTests(unittest.TestCase):
    """Cost blindness is structural: a constraint that reads what a move saves
    cannot be written against this interface."""

    def test_cost_is_outside_the_footprint(self):
        view = ReasonView(base_state())
        with self.assertRaises(FootprintError):
            view.read("cost")

    def test_the_constraint_reads_only_declared_fields(self):
        state, reasons = base_state(), base_reasons()
        edit = Edit(edit_id="move-verdict", moves={VERDICT: Q(1)},
                    cited=("g-interval",), dispositions=(Disposition("L1", CARRY),))
        view = ReasonView(state)
        constrain(state, reasons, edit, REFLEXIVE)
        self.assertNotIn("cost", view.log)

    def test_verdict_is_independent_of_accrued_cost(self):
        cheap, expensive = base_state(), base_state()
        expensive = type(expensive)(date=expensive.date,
                                    commitments=expensive.commitments,
                                    standards=expensive.standards,
                                    vocabulary=expensive.vocabulary,
                                    ledger=expensive.ledger, cost=Q(1000))
        edit = Edit(edit_id="move-verdict", moves={VERDICT: Q(1)},
                    cited=("g-interval",), dispositions=(Disposition("L1", CARRY),))
        self.assertEqual(constrain(cheap, base_reasons(), edit, REFLEXIVE),
                         constrain(expensive, base_reasons(), edit, REFLEXIVE))


class RecordTests(unittest.TestCase):
    """What the two conditions are functions of."""

    def test_both_conditions_are_functions_of_the_record(self):
        """Two trajectories with the same record receive the same verdict.

        Checked here on a pair that differs in accrued cost, which the record
        does not carry; the load-bearing instance is the latent pair in
        `test_scenarios.py`.
        """
        from scenarios import prompt_answer
        first = prompt_answer()
        second = Trajectory(
            type(first.initial)(date=first.initial.date,
                                commitments=first.initial.commitments,
                                standards=first.initial.standards,
                                vocabulary=first.initial.vocabulary,
                                ledger=first.initial.ledger, cost=Q(77)),
            first.steps)
        self.assertEqual(record(first), record(second))
        self.assertEqual(legitimate(first, REFLEXIVE).legitimate,
                         legitimate(second, REFLEXIVE).legitimate)


if __name__ == "__main__":
    unittest.main()
