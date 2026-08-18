"""The protected object: transient capture, and closure by role."""

from __future__ import annotations

import unittest
from itertools import product

import scenarios as S
from fixture import ADEQUACY, GENERATION, Machinery
from noncapture import Z_FIVE, non_capture
from response import (alphabet_of, endpoint_projection, presentation,
                      process_projection, protected_endpoint,
                      protected_process, rename_alphabet, rename_machinery,
                      rename_response, response, witnesses_off_alphabet,
                      writable_fields)


class TransientCapture(unittest.TestCase):
    """The advisor narrows a standard, lets the consequence land, and puts the
    standard back before the horizon.

    An endpoint object cannot see this and a trajectory object can, which is
    what makes the protected object a sequence rather than a state."""

    def setUp(self):
        self.fixture, self.variation = S.transient_capture()
        self.alphabet = alphabet_of(self.fixture)

    def test_the_endpoints_agree_and_the_target_does_not(self):
        first, second = (self.fixture.run(p) for p in self.variation)
        self.assertEqual(protected_endpoint(first, self.alphabet),
                         protected_endpoint(second, self.alphabet))
        self.assertTrue(first.target().legitimate)
        self.assertFalse(second.target().legitimate)

    def test_the_record_internal_conditions_do_not_fire(self):
        for policy in self.variation:
            report = self.fixture.run(policy).four()
            self.assertTrue(report.four and report.d.holds and report.x.holds)

    def test_endpoint_non_capture_misses_it(self):
        self.assertEqual(non_capture(self.fixture, self.variation, Z_FIVE), ())
        self.assertEqual(
            non_capture(self.fixture, self.variation,
                        endpoint_projection(self.alphabet)), ())

    def test_the_process_object_catches_it(self):
        self.assertTrue(non_capture(self.fixture, self.variation,
                                    process_projection(self.alphabet)))


class ClosureByRole(unittest.TestCase):
    """A field belongs to the protected object exactly when changing it changes
    an answer.  Two directions, both witnessed."""

    def test_a_writable_field_answering_nothing_is_outside(self):
        fixture, variation = S.irrelevant_coordinate()
        alphabet = alphabet_of(fixture)
        runs = [fixture.run(p) for p in variation]
        self.assertNotEqual(writable_fields(runs[0].states[-1]),
                            writable_fields(runs[1].states[-1]))
        self.assertEqual(protected_process(runs[0], alphabet),
                         protected_process(runs[1], alphabet))
        self.assertEqual(non_capture(fixture, variation,
                                     process_projection(alphabet)), ())

    def test_the_coordinate_list_is_finer_than_the_object_it_presents(self):
        """Off the alphabet, the presentation separates what nothing asks about.

        So a condition stated over the coordinate list forbids changes that
        alter no answer — the projection over-protects, which is the direction
        the first pass looked for and could not see from scenarios alone."""
        fixture, _ = S.attack_l()
        alphabet = alphabet_of(fixture)
        first, second = witnesses_off_alphabet(fixture.machinery,
                                               "unencountered-kind", "s-harm")
        self.assertNotEqual(presentation(first), presentation(second))
        self.assertEqual(response(first, alphabet), response(second, alphabet))

    def test_agreement_on_the_five_implies_agreement_on_every_answer(self):
        """The other direction holds unconditionally, over a generated family.

        The five coordinates are therefore a sound presentation of the object;
        the test above shows they are not a complete one."""
        fixture, _ = S.attack_l()
        alphabet = alphabet_of(fixture)
        family = list(_family(fixture.machinery))
        checked = 0
        for first, second in product(family, family):
            checked += 1
            if presentation(first) == presentation(second):
                self.assertEqual(response(first, alphabet),
                                 response(second, alphabet))
        self.assertEqual(checked, len(family) ** 2)
        self.assertGreaterEqual(len(family), 16)


def _family(base: Machinery):
    """A generated finite family: every subset of four independent edits."""
    from dataclasses import replace
    edits = (
        lambda m: replace(m, adequacy={**m.adequacy,
                                       "w-cheap": frozenset({"s-harm"})}),
        lambda m: replace(m, generation={k: v for k, v in m.generation.items()
                                         if k != "case"}),
        lambda m: replace(m, identification=frozenset({"licence-merge"})),
        lambda m: replace(m, noise=frozenset({"tag"})),
    )
    for mask in product((False, True), repeat=len(edits)):
        machinery = base
        for apply_it, edit in zip(mask, edits):
            if apply_it:
                machinery = edit(machinery)
        yield machinery


class RepresentationIndependence(unittest.TestCase):
    """Renaming the alphabet renames the answers and changes nothing else."""

    def test_the_object_is_equivariant(self):
        fixture, variation, mapping = S.renamed()
        alphabet = alphabet_of(fixture)
        renamed_alphabet = rename_alphabet(alphabet, mapping)
        for policy in variation:
            run = fixture.run(policy)
            for machinery in run.states:
                self.assertEqual(
                    response(rename_machinery(machinery, mapping),
                             renamed_alphabet),
                    rename_response(response(machinery, alphabet), mapping))

    def test_the_rename_is_not_the_identity(self):
        fixture, _variation, mapping = S.renamed()
        alphabet = alphabet_of(fixture)
        self.assertNotEqual(response(fixture.machinery, alphabet),
                            response(rename_machinery(fixture.machinery,
                                                      mapping),
                                     rename_alphabet(alphabet, mapping)))


class TheProcessObjectKeepsTheFirstPassResults(unittest.TestCase):
    """Everything the endpoint projection rejected, the process object rejects."""

    def test_all_six_attacks_still_fail(self):
        for name, builder in S.ATTACKS.items():
            fixture, variation = builder()
            alphabet = alphabet_of(fixture)
            with self.subTest(attack=name):
                self.assertTrue(non_capture(fixture, variation,
                                            process_projection(alphabet)))

    def test_the_controls_still_pass(self):
        for name, builder in (("autonomous-L", S.autonomous_l),
                              ("autonomous-G", S.autonomous_g),
                              ("K", S.autonomous_k),
                              ("persuasion", S.licensed_persuasion),
                              ("no-effect", S.no_effect)):
            fixture, variation = builder()
            alphabet = alphabet_of(fixture)
            with self.subTest(control=name):
                self.assertEqual(non_capture(fixture, variation,
                                             process_projection(alphabet)), ())


if __name__ == "__main__":
    unittest.main()
