from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.joint import (
    Liability,
    compiler_expansion_can_freeze_reference,
    duplicate_charge_debit,
    exact_joint_trace,
    finite_change_unbounded_scalar,
    liability_keys_unique,
    movement_recursion,
    pooled_cross_effect,
    proposal_bypass_quote,
    jump_step_cap,
    uniform_wealth_cap,
)


class JointExactTests(unittest.TestCase):
    def test_claim_ledger_is_complete(self):
        root = Path(__file__).resolve().parents[1]
        theory = (root / "JOINT_THEORY.md").read_text()
        ledger = (root / "LEDGER.md").read_text()
        theory_ids = set(re.findall(r"\{#(NL-[A-Z0-9]+)\}", theory))
        ledger_ids = set(re.findall(r"^\| (NL-[A-Z0-9]+) ", ledger, re.MULTILINE))
        self.assertEqual(theory_ids, ledger_ids)
        allowed = (
            "PROVED+MACHINE-CHECKED",
            "PROVED+INDEPENDENTLY-REDERIVED",
            "PROVED (single derivation)",
            "PROVED-CONDITIONAL (conditions listed)",
            "REFUTED (witness displayed)",
            "OPEN",
        )
        for claim in theory_ids:
            position = theory.index(f"{{#{claim}}}")
            nearby = theory[position : position + 180]
            self.assertTrue(any(status in nearby for status in allowed), claim)

    def test_load_bearing_movement_recursion(self):
        # theta=1/2, E=0, B=1/2, no ordinary movement.
        self.assertEqual(
            movement_recursion(Q(1, 2), Q(0), Q(1, 2), Q(0), 3),
            (Q(0), Q(1), Q(3), Q(7)),
        )
        self.assertEqual(jump_step_cap(Q(1, 2), Q(0), Q(1, 2), Q(0)), Q(1))
        self.assertEqual(uniform_wealth_cap(Q(1, 2), Q(0), Q(1, 2), Q(1)), Q(3, 2))

    def test_exact_joint_trace(self):
        trace = exact_joint_trace()
        self.assertEqual(trace["regions"], ((Q(1, 2), Q(1)), (Q(0), Q(1))))
        self.assertEqual(trace["movement"], Q(1, 2))
        self.assertEqual(trace["holdings"], (Q(-1), Q(0)))
        self.assertEqual(trace["prefix0"], {Q(0): Q(1, 2), Q(1): Q(-1, 2)})
        self.assertEqual(trace["payoffs"], {Q(0): Q(-1, 2), Q(1): Q(-1, 2)})
        self.assertEqual(trace["closing_balances"], {"charge": Q(0), "service": Q(0)})
        self.assertEqual(trace["stake_escrowed"], trace["stake_returned"])
        self.assertTrue(liability_keys_unique(trace["liabilities"]))

    def test_literal_liability_identity_uses_obligation_id(self):
        first = Liability("event:x", "service", "obligation:1", "service", Q(1, 8))
        duplicate = Liability("event:x", "service", "obligation:1", "service", Q(1, 8))
        distinct_obligation = Liability("event:x", "service", "obligation:2", "service", Q(1, 8))
        distinct_risk = Liability("event:x", "movement-reserve", "obligation:1", "reserve", Q(1, 8))
        self.assertFalse(liability_keys_unique((first, duplicate)))
        self.assertTrue(liability_keys_unique((first, distinct_obligation)))
        self.assertTrue(liability_keys_unique((first, distinct_risk)))

    def test_unactivated_proposal_changes_quote_if_allowed_to_bypass(self):
        self.assertEqual(proposal_bypass_quote(), (Q(1, 2), Q(0)))

    def test_one_change_alone_has_no_uniform_movement_cap(self):
        for m in (1, 10, 10_000):
            self.assertEqual(finite_change_unbounded_scalar(m), Q(m))

    def test_pooling_interval(self):
        self.assertFalse(pooled_cross_effect(Q(3, 4)))
        self.assertTrue(pooled_cross_effect(Q(1)))
        self.assertTrue(pooled_cross_effect(Q(9, 8)))
        self.assertFalse(pooled_cross_effect(Q(5, 4)))

    def test_duplicate_identical_channel_really_doubles_debit(self):
        self.assertEqual(duplicate_charge_debit(Q(1, 4)), (Q(1, 4), Q(1, 2)))

    def test_expansion_stable_suspension_has_zero_jump(self):
        self.assertEqual(compiler_expansion_can_freeze_reference()["movement"], Q(0))


if __name__ == "__main__":
    unittest.main()
