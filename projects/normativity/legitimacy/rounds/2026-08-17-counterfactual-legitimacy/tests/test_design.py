"""Which of the dose-response design constraints the finite setting needs.

The dose-response note builds its contrast physically, so its constraints are
constraints on an *audit*: an advisor that can see the arm assignment can flatten
the measured gradient, and an effect that fires on any exposure at all is
invisible to a design whose arms all have positive dose.  Here the contrast is
definitional — a quantifier over a variation class — so each constraint has to be
re-derived or dropped, and the witnesses below decide which."""

from __future__ import annotations

import unittest

import scenarios as S
from noncapture import Z_FIVE, non_capture


class QuantifyingOverTheClassReplacesPreRegistration(unittest.TestCase):
    """The dose-compensation attack, in definitional form.

    An advisor that knows which pair will be compared can push a revision and
    push it back, so the audited contrast is flat.  Checking one chosen pair
    passes; quantifying over the class does not.  This is what the note's single
    committed stream buys, and in this setting it is bought by the quantifier
    instead."""

    def setUp(self):
        self.fixture, self.variation = S.dose_compensation()
        self.by_name = {p.name: p for p in self.variation}

    def test_the_compensating_pair_reads_clean(self):
        pair = (self.by_name["null"], self.by_name["compensate"])
        runs = [self.fixture.run(p) for p in pair]
        self.assertEqual(Z_FIVE(runs[0]), Z_FIVE(runs[1]))
        self.assertEqual(non_capture(self.fixture, pair, Z_FIVE), ())
        for run in runs:
            self.assertTrue(run.target().legitimate)

    def test_the_class_does_not(self):
        self.assertTrue(non_capture(self.fixture, self.variation, Z_FIVE))
        self.assertFalse(
            self.fixture.run(self.by_name["push"]).target().legitimate)


class TheNullPolicyMustBeInTheClass(unittest.TestCase):
    """Presence-triggered influence: a principal that moves on any exposure at
    all, identically at every positive dose.  Every pair of positive-exposure
    policies agrees, so a class that omits the null policy passes."""

    def setUp(self):
        self.fixture, self.variation = S.presence_triggered()
        self.by_name = {p.name: p for p in self.variation}

    def test_positive_exposure_pairs_agree(self):
        pair = (self.by_name["one"], self.by_name["many"])
        runs = [self.fixture.run(p) for p in pair]
        self.assertEqual(Z_FIVE(runs[0]), Z_FIVE(runs[1]))
        self.assertEqual(non_capture(self.fixture, pair, Z_FIVE), ())
        for run in runs:
            self.assertFalse(run.target().legitimate)

    def test_including_the_null_policy_catches_it(self):
        self.assertTrue(non_capture(self.fixture, self.variation, Z_FIVE))


class DetectionWithoutAttribution(unittest.TestCase):
    """Two principals under one advisor stream: one moved by what was argued,
    one moved by the fact of exposure.  The dose-response note proves these
    produce the same joint record; here they produce the same record, the same
    protected state and the same verdict from both clauses.

    So the condition convicts the exposure and not its author, exactly as the
    note's non-attribution theorem says, and separating them would need a
    content-randomized arm this design does not have."""

    def setUp(self):
        (self.pushed, self.blind), self.variation = S.content_blind_twin()

    def test_the_records_are_identical(self):
        stream = self.variation[1]
        self.assertEqual(self.pushed.run(stream).record(),
                         self.blind.run(stream).record())

    def test_the_protected_state_is_identical(self):
        stream = self.variation[1]
        self.assertEqual(Z_FIVE(self.pushed.run(stream)),
                         Z_FIVE(self.blind.run(stream)))

    def test_both_fire_and_neither_names_a_mechanism(self):
        first = non_capture(self.pushed, self.variation, Z_FIVE)
        second = non_capture(self.blind, self.variation, Z_FIVE)
        self.assertTrue(first)
        self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
