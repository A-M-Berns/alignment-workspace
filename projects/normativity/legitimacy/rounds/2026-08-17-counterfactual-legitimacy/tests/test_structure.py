"""Properties of the objects themselves, checked before anything is read off them."""

from __future__ import annotations

import unittest
from itertools import combinations, product

import scenarios as S
from fixture import (ADEQUACY, Fixture, Item, Machinery, Policy, Proposal,
                     SUBSTANCE, licensed)
from noncapture import Z_FIVE, non_capture

DELIVERY = tuple(product(range(6), ("plain", "high"), (0, 1)))


class LicensingIgnoresDelivery(unittest.TestCase):
    """Exhaustive over the delivery grid, for a licensed and an unlicensed
    content: whether an input counts as a reason is a function of content,
    coordinate and provenance alone."""

    def test_the_verdict_is_constant_across_the_grid(self):
        fixture, _ = S.selective_information()
        machinery = fixture.machinery
        checked = 0
        for content, ground in (("audit-finding", "g-audit"),
                                ("rumour", "g-root")):
            verdicts = set()
            for repetitions, salience, position in DELIVERY:
                item = Item(content, ADEQUACY,
                            Proposal(ADEQUACY, "w-x", frozenset({SUBSTANCE})),
                            ground_id=ground, repetitions=repetitions,
                            salience=salience, position=position)
                verdicts.add(licensed(machinery, fixture.grounds, item, 1))
                checked += 1
            self.assertEqual(len(verdicts), 1, content)
        self.assertEqual(checked, 2 * len(DELIVERY))

    def test_the_two_contents_do_not_get_the_same_verdict(self):
        """Otherwise the grid above would be checking nothing."""
        fixture, _ = S.selective_information()
        common = dict(ground_id="g-audit", repetitions=1)
        proposal = Proposal(ADEQUACY, "w-x", frozenset({SUBSTANCE}))
        yes = Item("audit-finding", ADEQUACY, proposal, **common)
        no = Item("rumour", ADEQUACY, proposal, ground_id="g-root")
        self.assertTrue(licensed(fixture.machinery, fixture.grounds, yes, 1))
        self.assertFalse(licensed(fixture.machinery, fixture.grounds, no, 1))


class TheTraceIsNonAnticipating(unittest.TestCase):
    """Two policies agreeing up to a step produce traces agreeing up to that
    step, whatever they do afterwards."""

    def test_prefixes_agree(self):
        fixture, _ = S.selective_information()
        widen, withdraw = S.selective_information()[1][0].items(1)
        variants = []
        for late in ((), (widen,), (widen, withdraw)):
            variants.append(Policy(f"late-{len(late)}",
                                   {1: (widen,), 2: late}))
        checked = 0
        for first, second in combinations(variants, 2):
            a, b = fixture.run(first), fixture.run(second)
            self.assertEqual(a.ltrace_fine[:2], b.ltrace_fine[:2])
            checked += 1
        self.assertEqual(checked, 3)


class TheCoarseTraceIsNotEnough(unittest.TestCase):
    """One name, two proposals.

    With no residual channel at all, an advisor offering two different revisions
    under one `(content, coordinate)` name produces identical coarse traces and
    different protected states.  The trace has to individuate a reason finely
    enough to determine what it licenses, and naming it does not.  Everything
    else in this round uses the fine trace for that reason.
    """

    def _fixture(self):
        fixture, _ = S.selective_information()
        return Fixture(**{**fixture.__dict__, "name": "one-name",
                          "rule": "none"})

    def _policies(self):
        def offered(witness):
            return Policy(f"offer-{witness}", {1: (Item(
                "efficiency-review", ADEQUACY,
                Proposal(ADEQUACY, witness, frozenset({SUBSTANCE})),
                ground_id="g-eff"),)})
        return (offered("w-cheap"), offered("w-partial"))

    def test_the_coarse_trace_agrees_where_the_protected_state_does_not(self):
        fixture = self._fixture()
        first, second = (fixture.run(p) for p in self._policies())
        self.assertEqual(first.ltrace, second.ltrace)
        self.assertNotEqual(first.ltrace_fine, second.ltrace_fine)
        self.assertNotEqual(Z_FIVE(first), Z_FIVE(second))

    def test_the_condition_fails_on_the_coarse_trace_and_holds_on_the_fine(self):
        fixture = self._fixture()
        policies = self._policies()
        coarse = non_capture(fixture, policies, Z_FIVE,
                             trace=lambda run: run.ltrace)
        fine = non_capture(fixture, policies, Z_FIVE)
        self.assertTrue(coarse)
        self.assertEqual(fine, ())


class CouplingIsStructural(unittest.TestCase):
    """Two runs of one fixture share everything but the policy, so nothing has
    to be checked after the fact — except the one channel that reaches outside
    the policy, which `coupled` refuses."""

    def test_runs_of_one_fixture_share_the_exogenous_history(self):
        fixture, variation = S.attack_l()
        histories = {fixture.run(p).encounters for p in variation}
        self.assertEqual(len(histories), 1)

    def test_an_arising_controlling_policy_is_refused(self):
        fixture, (null, suppress) = S.controls_what_arises()
        self.assertTrue(fixture.coupled(null, null))
        self.assertFalse(fixture.coupled(null, suppress))


if __name__ == "__main__":
    unittest.main()
