from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.migration import (
    AnalyticMovementEntry,
    LegacyRetention,
    LiteralLiability,
    LossEntry,
    SuspensionEntry,
    TargetKind,
    authorized_legacy_harm_migration,
    exact_migration_trace,
    local_bridge_has_unique_future_extension,
    malformed_harm_migration,
    verify_migration,
)


class MigrationVerifierTests(unittest.TestCase):
    def test_migration_claim_ledger_is_complete(self):
        root = Path(__file__).resolve().parents[1]
        theory = (root / "MIGRATION_THEORY.md").read_text()
        ledger = (root / "LEDGER.md").read_text()
        theory_ids = set(re.findall(r"\{#(AM-[A-Z0-9]+)\}", theory))
        ledger_ids = set(re.findall(r"^\| (AM-[A-Z0-9]+) ", ledger, re.MULTILINE))
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
            nearby = theory[position : position + 260]
            self.assertTrue(any(status in nearby for status in allowed), claim)

    def test_raw_harm_certificate_passes_all_nine_checks(self):
        trace = exact_migration_trace()
        report = trace["report"]
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(len(report.checks), 9)
        self.assertTrue(all(result.passed for result in report.checks.values()))
        self.assertEqual(
            report.reachable_entitlement_roots,
            {"e:physical-or-coercion": ("root:pc+",)},
        )
        frontier = report.challenge_frontiers["c:frustration"]
        self.assertEqual(len(frontier), 1)
        self.assertEqual(frontier[0].kind, TargetKind.ANCESTRY_EDGE)
        self.assertEqual(frontier[0].target_id, "edge:f-support+")
        self.assertNotIn("e:physical-or-coercion", {target.target_id for target in frontier})
        self.assertEqual(
            report.payoff.old_tables["p:harm"],
            report.payoff.new_tables["p:any-harm"],
        )
        self.assertEqual(report.payoff.live_payoff_vectors, ((Q(0),), (Q(1),), (Q(1),), (Q(1),)))
        self.assertEqual(report.payoff.old_reference_lift, (Q(3, 4),))
        self.assertEqual(report.payoff.new_reference_lift, (Q(2, 3),))
        self.assertTrue(report.payoff.old_reference_in_carrier)
        self.assertTrue(report.payoff.new_reference_in_carrier)
        self.assertEqual(report.payoff.transported_holdings, {"p:any-harm": Q(-2)})
        self.assertEqual(report.payoff.new_coordinate_holdings, {"physical-or-coercion": Q(0)})
        self.assertEqual(report.payoff.analytic_movement, Q(1, 6))
        self.assertIsInstance(report.payoff.movement_entry, AnalyticMovementEntry)
        self.assertEqual(report.payoff.movement_entry.total, Q(1, 6))
        self.assertEqual(len(report.payoff.movement_entry.components), 2)
        self.assertTrue(report.old_compiler_valid)
        self.assertTrue(report.endpoint_compiler_valid)
        self.assertEqual(
            report.eventual_route_coverage,
            {
                "c:frustration+": ("route:frustration",),
                "b:justify-frustration+": ("route:frustration",),
            },
        )
        self.assertTrue(report.authorization_binding_valid)
        self.assertTrue(report.atomic_activation_valid)
        certificate = trace["certificate"]
        self.assertEqual(len(certificate.suspensions), 2)
        self.assertIsInstance(certificate.suspensions[0], SuspensionEntry)
        self.assertEqual(certificate.losses, ())
        self.assertEqual(certificate.legacy_retentions, ())
        self.assertEqual(certificate.literal_liabilities, ())
        self.assertIsNot(SuspensionEntry, LossEntry)
        self.assertIsNot(LossEntry, LegacyRetention)
        self.assertIsNot(LegacyRetention, LiteralLiability)
        self.assertIsNot(LiteralLiability, AnalyticMovementEntry)

    def _assert_rejected(self, case: str, code: str):
        old, new, certificate = malformed_harm_migration(case)
        report = verify_migration(old, new, certificate)
        self.assertFalse(report.passed)
        matching = [witness for witness in report.counterwitnesses if witness.code == code]
        self.assertTrue(matching, (case, tuple(w.code for w in report.counterwitnesses)))
        self.assertTrue(all(witness.ids or witness.detail for witness in matching))
        return report

    def test_missing_entitlement_ancestry(self):
        report = self._assert_rejected("missing-ancestry", "entitlement.missing_authorized_root")
        self.assertEqual(report.reachable_entitlement_roots["e:physical-or-coercion"], ())

    def test_split_challenge_has_uncovered_descendant(self):
        self._assert_rejected("uncovered-split-challenge", "challenge.uncovered_frontier")

    def test_merged_incompatibility_cannot_be_hidden(self):
        self._assert_rejected("hidden-incompatibility", "relation.hidden_incompatibility")

    def test_outstanding_payoff_cannot_be_rewritten(self):
        self._assert_rejected("changed-payoff", "payoff.mismatch_without_legacy")

    def test_authorized_legacy_retains_old_payoff_on_local_carrier(self):
        old, new, certificate = authorized_legacy_harm_migration()
        report = verify_migration(old, new, certificate)
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(len(certificate.legacy_retentions), 1)
        self.assertIsInstance(certificate.legacy_retentions[0], LegacyRetention)
        self.assertEqual(
            report.payoff.old_tables["p:harm"],
            report.payoff.new_tables["p:any-harm"],
        )

    def test_proposed_compiler_has_no_preactivation_force(self):
        self._assert_rejected("preactivation-force", "activation.preactivation_force")

    def test_inexpressibility_is_not_discharge(self):
        self._assert_rejected("inexpressibility-discharge", "cell.unbacked_discharge")

    def test_duplicate_loss_key(self):
        self._assert_rejected("duplicate-loss", "accounting.duplicate_loss")

    def test_semantic_coupling_is_not_authorization(self):
        self._assert_rejected("coupling-as-authorization", "authorization.absent")

    def test_lossless_collapse_of_live_distinction(self):
        self._assert_rejected("lossless-collapse", "semantic.lossless_collapse")

    def test_duplicate_consuming_cells(self):
        self._assert_rejected("duplicate-consuming-cell", "occurrence.duplicate_input")

    def test_partial_activation(self):
        self._assert_rejected("partial-activation", "occurrence.orphan_input")

    def test_late_burden_target_reassignment(self):
        self._assert_rejected("late-burden-reassignment", "challenge.late_reassignment")

    def test_uncertified_early_pointer_swap(self):
        self._assert_rejected("uncertified-early-swap", "activation.endpoint_recheck_failed")

    def test_disclosed_but_unauthorized_loss(self):
        self._assert_rejected("unauthorized-loss", "accounting.unauthorized_loss")

    def test_authority_is_not_duplicated_across_split(self):
        self._assert_rejected("duplicated-authority", "authority.duplicated_or_ungranted")

    def test_eventual_route_coverage_is_computed_from_routes(self):
        report = self._assert_rejected("unsupported-terminal-coverage", "endpoint.uncovered_terminal")
        self.assertEqual(report.eventual_route_coverage["c:frustration+"], ())

    def test_local_bridge_does_not_supply_a_universal_ontology(self):
        self.assertFalse(local_bridge_has_unique_future_extension())


if __name__ == "__main__":
    unittest.main()
