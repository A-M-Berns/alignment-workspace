"""The excision operator's properties, verified or refuted one by one.

```text
Excise_E(H)   replay H with the settlements of the episodes in E removed,
              each removed step replaced by an inert settlement
```

Six properties hold. Two tempting algebraic ones fail, and both fail for the
same reason: Reflective Integrity's admissibility is not a monotone function of
the record, because a schema may read the strict pre-state and `G5` rejects an
event whose schema returns nothing. `fixtures.nonmonotone_case` is the witness.
The round keeps the counterexample rather than adding machinery to force the
algebra.
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


def blind_cases() -> list:
    """Every fixture whose schemas are all pre-state-blind."""
    return [F.C10_manufactured_authorization()["case"],
            F.C22_inquiry_laundering()["case"],
            F.C25_split_episode(linked=True)["case"],
            F.C27_unlabelled_intermediate()["case"],
            F.C30_applicability_boundary("mixed")["case"],
            F.C33_standing_without_license()["case"]]


class TestPropertiesThatHold(unittest.TestCase):

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
        for case in blind_cases():
            for eps in ([], ["E"], ["E1", "E2"]):
                self.assertTrue(en.excise(case, eps).good())

    def test_subhistory_in_information(self):
        """Every surviving occurrence that is not a void came from the original."""
        for case in blind_cases():
            original = occurrence_ids(case.history())
            after = occurrence_ids(en.excise(case, ["E", "E1", "E2"]))
            for kind, (was, now) in enumerate(zip(original, after)):
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
    """Two, with one witness, and the witness is a legal Reflective Integrity record."""

    def setUp(self):
        self.case = F.nonmonotone_case()

    def test_the_witness_is_a_legal_record(self):
        self.assertTrue(self.case.history().good())
        self.assertEqual({a.id for a in self.case.history().norm_events()},
                         {"a:parity"})

    def test_monotonicity_fails(self):
        """`E subset E'` does not imply `Survivors(E') subset Survivors(E)`."""
        small = {a.id for a in en.excise(self.case, ["E1"]).norm_events()}
        large = {a.id for a in en.excise(self.case, ["E1", "E2"]).norm_events()}
        self.assertEqual(small, set())
        self.assertEqual(large, {"a:parity"})
        self.assertFalse(large <= small)

    def test_composition_fails(self):
        """`Excise_{E'}(Excise_E(H))` is not `Excise_{E union E'}(H)`."""
        composed = en.excise(en.excised_case(self.case, ["E1"]), ["E2"])
        joint = en.excise(self.case, ["E1", "E2"])
        self.assertEqual({a.id for a in composed.norm_events()}, set())
        self.assertEqual({a.id for a in joint.norm_events()}, {"a:parity"})

    def test_both_failures_need_a_prestate_reading_schema(self):
        """The same two properties hold on every pre-state-blind fixture here."""
        for case in blind_cases():
            small = occurrence_ids(en.excise(case, ["E1"]))
            large = occurrence_ids(en.excise(case, ["E1", "E2"]))
            for was, now in zip(small, large):
                self.assertTrue(set(now) - {i for i in now
                                            if i.startswith(en.VOID)}
                                <= set(was))
            composed = en.excise(en.excised_case(case, ["E1"]), ["E2"])
            joint = en.excise(case, ["E1", "E2"])
            self.assertEqual(
                {a.id for a in composed.norm_events()},
                {a.id for a in joint.norm_events()})


if __name__ == "__main__":
    unittest.main()
