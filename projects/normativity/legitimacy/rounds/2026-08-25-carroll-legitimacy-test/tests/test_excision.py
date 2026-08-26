"""The excision operator's properties, verified or refuted one by one.

```text
Excise_E(H)   replay H with the settlements of the episodes in E removed,
              each removed step replaced by an inert settlement
```

**Seven** properties hold on the fixtures here. Two tempting algebraic ones fail:
monotonicity in the excised set, and composition. There are **two independent
sources** of the failure and the round found them in that order.

The first is pre-state-sensitive schema interpretation: `[[sigma]]_S` may read
the strict pre-state, and `G5` rejects an event whose schema returns nothing, so
a smaller record can make an event inadmissible.

The second needs no pre-state reading at all. Admission is a *replay* over an
evolving standing view, and removing more history can restore an earlier
standing and with it a later event's admissibility.
`fixtures.suspension_restoration_case` is the witness: one episode suspends an
authority, another reactivates it, and a third event names it. Excising the
reactivating episode leaves the suspension in place and the third event falls;
excising both leaves the authority never suspended and it stands.

So pre-state-blindness buys neither property. What it does buy is narrower and
lives in `test_adversarial.py`: for a *surviving* event, blindness makes the
payload of the authority it names the same one. That is a succession result, not
an algebra one, and the two are kept apart deliberately.

`fixtures.stance_restoration_case` is the negative control for a route that does
*not* work, and it names the clause: `G2` reads ledger membership of reason ids,
not enablement.
"""
from __future__ import annotations

import unittest
from dataclasses import replace

import enrichment as en
import fixtures as F


def occurrence_ids(history) -> tuple:
    return (tuple(s.id for s in history.settlements()),
            tuple(e.id for e in history.reasons()),
            tuple(a.id for a in history.norm_events()),
            tuple(r.id for r in history.responses()))


def events(history) -> set:
    return {a.id for a in history.norm_events()}


def blind_cases() -> list:
    """Every fixture whose schemas are all pre-state-blind."""
    return [F.C10_manufactured_authorization()["case"],
            F.C22_inquiry_laundering()["case"],
            F.C25_split_episode(linked=True)["case"],
            F.C27_unlabelled_intermediate()["case"],
            F.C30_applicability_boundary("mixed")["case"],
            F.C33_standing_without_license()["case"]]


class TestPropertiesThatHold(unittest.TestCase):
    """Seven, on the fixtures below. None is proved for an arbitrary record."""

    def test_determinism(self):
        for case in blind_cases():
            a, b = en.excise(case, ["E"]), en.excise(case, ["E"])
            self.assertEqual(occurrence_ids(a), occurrence_ids(b))
            self.assertEqual(a.std(), b.std())

    def test_position_preservation(self):
        """Every `tau` survives, so minted standing ids are comparable by identity."""
        for case in blind_cases():
            for eps in ([], ["E"], ["E1"], ["E1", "E2"]):
                self.assertEqual(en.excise(case, eps).now, case.history().now)

    def test_the_result_is_an_admissible_record(self):
        for case in blind_cases() + [F.suspension_restoration_case(),
                                     F.stance_restoration_case()]:
            for eps in ([], ["E"], ["E1"], ["E1", "E2"]):
                self.assertTrue(en.excise(case, eps).good())

    def test_subhistory_in_information(self):
        """Every surviving occurrence that is not a void came from the original."""
        for case in blind_cases():
            original = occurrence_ids(case.history())
            after = occurrence_ids(en.excise(case, ["E", "E1", "E2"]))
            for was, now in zip(original, after):
                for oid in now:
                    self.assertTrue(oid in was or oid.startswith(en.VOID),
                                    f"{oid} appeared from nowhere")

    def test_prefix_causality(self):
        """Survival at `tau` is decided by the original prefix through `tau`."""
        for case in blind_cases():
            full = en.excise(case, ["E", "E1", "E2"]).steps
            for k in range(1, len(case.steps) + 1):
                truncated = en.excise(replace(case, steps=case.steps[:k]),
                                      ["E", "E1", "E2"]).steps
                self.assertEqual([type(s).__name__ for s in truncated],
                                 [type(s).__name__ for s in full[:k]])

    def test_idempotence(self):
        for case in blind_cases():
            once = en.excise(case, ["E", "E1", "E2"])
            twice = en.excise(en.excised_case(case, ["E", "E1", "E2"]),
                              ["E", "E1", "E2"])
            self.assertEqual(occurrence_ids(once), occurrence_ids(twice))
            self.assertEqual(once.std(), twice.std())

    def test_excising_nothing_is_the_identity(self):
        for case in blind_cases():
            self.assertEqual(occurrence_ids(en.excise(case, [])),
                             occurrence_ids(case.history()))


class TestPropertiesThatFail(unittest.TestCase):
    """Two, from two independent sources, each with a legal record as witness."""

    def test_a_prestate_reading_schema_breaks_monotonicity(self):
        case = F.nonmonotone_case()
        self.assertTrue(case.history().good())
        small = events(en.excise(case, ["E1"]))
        large = events(en.excise(case, ["E1", "E2"]))
        self.assertEqual((small, large), (set(), {"a:parity"}))
        self.assertFalse(large <= small)

    def test_a_prestate_reading_schema_breaks_composition(self):
        case = F.nonmonotone_case()
        composed = en.excise(en.excised_case(case, ["E1"]), ["E2"])
        joint = en.excise(case, ["E1", "E2"])
        self.assertEqual(events(composed), set())
        self.assertEqual(events(joint), {"a:parity"})

    def test_standing_restoration_breaks_monotonicity_without_reading_anything(self):
        """The sharper witness: every schema here is pre-state-blind."""
        case = F.suspension_restoration_case()
        self.assertTrue(case.history().good())
        self.assertEqual(events(case.history()),
                         {"a:suspend", "a:reactivate", "a:target"})
        small = events(en.excise(case, ["E1"]))
        large = events(en.excise(case, ["E1", "E2"]))
        self.assertEqual(small, {"a:suspend"})
        self.assertEqual(large, {"a:target"})
        self.assertNotIn("a:target", small)
        self.assertFalse(large <= small)

    def test_standing_restoration_breaks_composition(self):
        case = F.suspension_restoration_case()
        composed = en.excise(en.excised_case(case, ["E1"]), ["E2"])
        joint = en.excise(case, ["E1", "E2"])
        self.assertEqual(events(composed), set())
        self.assertEqual(events(joint), {"a:target"})

    def test_blindness_does_not_rescue_either_property(self):
        """Stated as its own case because the round claimed the opposite once."""
        case = F.suspension_restoration_case()
        self.assertTrue(events(en.excise(case, ["E1", "E2"]))
                        - events(en.excise(case, ["E1"])))

    def test_both_properties_hold_on_the_rounds_own_fixtures(self):
        """An observation about this suite, and not a theorem about records.

        Every legitimacy fixture in the round happens to satisfy both. That is
        why neither failure showed up until a record was built to produce one,
        and it is the reason this test is named for what it checks.
        """
        for case in blind_cases():
            small = occurrence_ids(en.excise(case, ["E1"]))
            large = occurrence_ids(en.excise(case, ["E1", "E2"]))
            for was, now in zip(small, large):
                self.assertTrue(
                    {i for i in now if not i.startswith(en.VOID)} <= set(was))
            composed = en.excise(en.excised_case(case, ["E1"]), ["E2"])
            joint = en.excise(case, ["E1", "E2"])
            self.assertEqual(events(composed), events(joint))


class TestTheRouteThatDoesNotWork(unittest.TestCase):
    """Restoring a *stance* reaches nothing, and the clause that says so."""

    def test_removing_a_stance_source_does_not_drop_a_later_event(self):
        case = F.stance_restoration_case()
        self.assertTrue(case.history().good())
        self.assertIn("v", case.history().bhat())
        self.assertIn("a:target", events(en.excise(case, ["E1"])))
        self.assertNotIn("v", en.excise(case, ["E1"]).bhat())

    def test_g2_reads_ledger_membership_and_not_enablement(self):
        """The exact clause, read off the admission rule rather than described."""
        case = F.stance_restoration_case()
        history = case.history()
        target = [a for a in history.norm_events() if a.id == "a:target"][0]
        self.assertEqual(target.derivation.leaves, frozenset({"r:uses-v"}))
        stripped = en.excise(case, ["E1"])
        self.assertIn("r:uses-v", {e.id for e in stripped.reasons()})
        self.assertEqual(stripped.wf_violations(target), [])


if __name__ == "__main__":
    unittest.main()
