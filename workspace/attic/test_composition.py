from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.composition import (
    COMPOSITE_STYLES,
    MERGE_REPAIRS,
    MIGRATION_2_GRANT,
    AdministrativeGrant,
    authority_provenance,
    compose_certificates,
    discharge_legacy_distinction,
    legacy_discharge_report,
    movement_composition,
    reference_reversal_witness,
    build_merge_migration,
    build_two_step_history,
    compose_migrations,
    exact_composition_trace,
    history_questions,
    verify_history,
)
from src.joint import movement_recursion
from dataclasses import replace

from src.migration import (
    DiscrepancyEntry,
    OccurrenceStatus,
    TargetKind,
    build_harm_migration,
    exact_migration_trace,
    verify_migration,
)


class CompositionTests(unittest.TestCase):
    def _codes(self, report):
        return {witness.code for witness in report.counterwitnesses}

    def test_composition_claim_ledger_is_complete(self):
        root = Path(__file__).resolve().parents[1]
        theory = (root / "COMPOSITION_THEORY.md").read_text()
        ledger = (root / "LEDGER.md").read_text()
        theory_ids = set(re.findall(r"\{#(CM-[A-Z0-9]+)\}", theory))
        ledger_ids = set(re.findall(r"^\| (CM-[A-Z0-9]+) ", ledger, re.MULTILINE))
        self.assertEqual(theory_ids, ledger_ids)
        self.assertTrue(theory_ids)
        allowed = (
            "PROVED+MACHINE-CHECKED",
            "PROVED+INDEPENDENTLY-REDERIVED",
            "PROVED (single derivation)",
            "PROVED-CONDITIONAL (conditions listed)",
            "REFUTED (witness displayed)",
            "CONJECTURE (not proved)",
            "OPEN",
        )
        for claim in theory_ids:
            position = theory.index(f"{{#{claim}}}")
            nearby = theory[position : position + 260]
            self.assertTrue(any(status in nearby for status in allowed), claim)

    # 1. The frozen first span is untouched by the version layer.
    def test_first_span_is_unchanged_and_still_passes(self):
        state_0, state_1, certificate_01 = build_harm_migration()
        frozen = exact_migration_trace()
        self.assertTrue(frozen["report"].passed)
        self.assertEqual(certificate_01.certificate_id, "certificate:harm-refinement-v1")
        self.assertEqual(state_1.migration_tokens, ())
        report = verify_history(build_two_step_history("suspended-lineage"))
        component = report.component_reports["step:01"]
        self.assertTrue(component.passed)
        self.assertEqual(component.payoff.analytic_movement, Q(1, 6))
        self.assertEqual(
            component.challenge_frontiers["c:frustration"],
            frozen["report"].challenge_frontiers["c:frustration"],
        )
        # The departure state differs from the arrival state only administratively.
        node_1 = report.versions[1]
        self.assertEqual(node_1.version_id, "v1")
        history = build_two_step_history("suspended-lineage")
        arrival, departure = history.nodes[1].arrival_state, history.nodes[1].departure_state
        self.assertEqual(arrival.occurrences, departure.occurrences)
        self.assertEqual(arrival.relation_edges, departure.relation_edges)
        self.assertEqual(arrival.compiler, departure.compiler)
        self.assertEqual(departure.migration_tokens, ("token:migration-2",))

    # 2. The locally repaired second span passes the nine one-step checks.
    def test_repaired_second_span_passes_locally(self):
        departure_1, state_2, certificate_12 = build_merge_migration("suspended-lineage")
        report = verify_migration(departure_1, state_2, certificate_12)
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(len(report.checks), 9)
        self.assertEqual(state_2.semantic_states, ("none", "bodily-harm", "nonphysical-harm"))
        self.assertEqual(report.payoff.analytic_movement, Q(2, 15))
        self.assertEqual(
            report.challenge_frontiers["c:frustration+"],
            (report.challenge_frontiers["c:frustration+"][0],),
        )
        frontier = report.challenge_frontiers["c:frustration+"][0]
        self.assertEqual(frontier.kind, TargetKind.ANCESTRY_EDGE)
        self.assertEqual(frontier.target_id, "edge:f-support++")

    # 3. The repaired two-step history composes.
    def test_repaired_history_composes(self):
        report = exact_composition_trace("suspended-lineage")["report"]
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(len(report.checks), 13)
        self.assertTrue(all(result.passed for result in report.checks.values()))
        self.assertEqual(report.counterwitnesses, ())
        self.assertEqual(
            tuple(version.version_id for version in report.versions), ("v0", "v1", "v2"))
        self.assertEqual({version.actor_id for version in report.versions}, {"public-learner"})
        self.assertEqual(len(report.fiber_product.pairs), 4)
        self.assertEqual(report.fiber_product.uncovered_intermediate_states, ())
        self.assertEqual(
            report.composite_frontiers["c:frustration"],
            (report.composite_frontiers["c:frustration"][0],))
        target = report.composite_frontiers["c:frustration"][0]
        self.assertEqual((target.kind, target.target_id),
                         (TargetKind.ANCESTRY_EDGE, "edge:f-support++"))

    # 4. A naive lossless coercion/frustration collapse fails.
    def test_naive_collapse_fails(self):
        departure_1, state_2, certificate_12 = build_merge_migration("naive")
        local = verify_migration(departure_1, state_2, certificate_12)
        self.assertFalse(local.passed)
        self.assertIn("semantic.lossless_collapse",
                      {witness.code for witness in local.counterwitnesses})
        report = verify_history(build_two_step_history("naive"))
        self.assertFalse(report.passed)
        self.assertIn("composition.component_failed", self._codes(report))
        self.assertFalse(report.checks["components"].passed)

    # A passed component pair does not imply a passed composite.
    def test_locally_valid_merge_can_still_fail_the_composite(self):
        departure_1, state_2, certificate_12 = build_merge_migration("merged-live")
        self.assertTrue(verify_migration(departure_1, state_2, certificate_12).passed)
        report = verify_history(build_two_step_history("merged-live"))
        self.assertTrue(all(component.passed
                            for component in report.component_reports.values()))
        self.assertFalse(report.passed)
        self.assertTrue(report.checks["components"].passed)
        codes = self._codes(report)
        self.assertIn("composition.standing_not_monotone", codes)
        self.assertIn("composition.suspension_resurrected", codes)
        self.assertIn("composition.unreconciled_duplicate_path", codes)
        for witness in report.counterwitnesses:
            self.assertTrue(witness.ids and witness.detail)

    # 5. A split followed by a merge does not duplicate the original authority.
    def test_split_then_merge_does_not_duplicate_authority(self):
        report = verify_history(build_two_step_history("merged-suspension"))
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(report.authority.start_authoritative,
                         ("e:harm", "k:harm", "p:harm", "w:harm-protect"))
        self.assertEqual(report.authority.end_authoritative,
                         ("k:any-harm++", "p:any-harm++", "w:bodily-or-coercive-protect++"))
        self.assertEqual(report.authority.grants, ())
        self.assertEqual(report.authority.standing_lifts, ())
        self.assertLessEqual(len(report.authority.end_authoritative),
                             len(report.authority.start_authoritative))
        merged = [path for path in report.lineage.paths
                  if path.end_occurrence == "e:merged-suspended++"]
        self.assertEqual(len(merged), 2)
        self.assertEqual(len({path.second_cell for path in merged}), 1)

    # 6. Duplicate intermediate paths are normalized without duplicating ancestry.
    def test_duplicate_intermediate_paths_are_normalized(self):
        report = verify_history(build_two_step_history("merged-suspension"))
        self.assertEqual(len(report.lineage.paths), 8)
        self.assertEqual(len(report.lineage.ancestry), 7)
        self.assertEqual(len(set(report.lineage.ancestry)), 7)
        self.assertEqual(report.lineage.duplicate_pairs,
                         (("e:harm", "e:merged-suspended++"),))
        self.assertEqual(
            report.lineage.intermediates[("e:harm", "e:merged-suspended++")],
            ("e:frustration-suspended", "e:physical-or-coercion"))
        self.assertTrue(report.checks["duplication"].passed)
        self.assertTrue(report.checks["lineage"].passed)

    # 7. A challenge following only one descendant fails.
    def test_challenge_following_one_descendant_fails(self):
        report = verify_history(
            build_two_step_history("suspended-lineage", "partial-target-cover"))
        self.assertFalse(report.passed)
        self.assertFalse(report.checks["targets"].passed)
        uncovered = [witness for witness in report.counterwitnesses
                     if witness.code == "composition.frontier_uncovered"]
        self.assertTrue(uncovered)
        self.assertIn("edge:f-support-b++", uncovered[0].ids)

    # 8. Missing fiber-product support fails.
    def test_missing_fiber_product_support_fails(self):
        report = verify_history(
            build_two_step_history("suspended-lineage", "truncated-arena"))
        self.assertTrue(all(component.passed
                            for component in report.component_reports.values()))
        self.assertFalse(report.passed)
        self.assertFalse(report.checks["coverage"].passed)
        gaps = [witness for witness in report.counterwitnesses
                if witness.code == "composition.fiber_support_gap"]
        self.assertEqual(gaps[0].ids, ("frustration",))
        self.assertEqual(report.fiber_product.uncovered_intermediate_states, ("frustration",))
        self.assertEqual(len(report.fiber_product.pairs), 3)

    # 9. A broken snapshot or activation chain fails.
    def test_broken_activation_chain_fails(self):
        report = verify_history(
            build_two_step_history("suspended-lineage", "relabelled-intermediate"))
        self.assertTrue(all(component.passed
                            for component in report.component_reports.values()))
        self.assertFalse(report.passed)
        self.assertFalse(report.checks["continuity"].passed)
        codes = self._codes(report)
        self.assertIn("composition.activation_chain_broken", codes)
        self.assertIn("composition.unauthorized_intermediate_edit", codes)

    def test_intermediate_state_cannot_be_edited_outside_the_grant(self):
        report = verify_history(build_two_step_history("suspended-lineage", "smuggled-edit"))
        self.assertFalse(report.passed)
        smuggled = [witness for witness in report.counterwitnesses
                    if witness.code == "composition.unauthorized_intermediate_edit"]
        self.assertEqual(smuggled[0].ids, ("force_holdings",))

    def test_one_token_cannot_authorize_two_migrations(self):
        report = verify_history(build_two_step_history("suspended-lineage", "token-reuse"))
        self.assertTrue(all(component.passed
                            for component in report.component_reports.values()))
        self.assertFalse(report.passed)
        self.assertIn("composition.token_reuse", self._codes(report))

    # 10. Both reference movements and their total are derived exactly.
    def test_reference_movements_are_derived_exactly(self):
        report = exact_composition_trace("suspended-lineage")["report"]
        self.assertEqual(report.movement.step_totals, (Q(1, 6), Q(2, 15)))
        self.assertEqual(report.movement.total, Q(3, 10))
        self.assertEqual(report.movement.reference_path, (Q(3, 4), Q(2, 3), Q(3, 5)))
        self.assertEqual(report.movement.reference_jumps, 2)
        self.assertEqual(report.movement.tokens_consumed,
                         ("token:migration-1", "token:migration-2"))
        self.assertEqual(report.movement.composite_payoff_tables,
                         {"p:harm": (Q(0), Q(1), Q(1), Q(1))})
        holdings = {
            component.holdings
            for entry in report.movement.step_entries for component in entry.components
        }
        self.assertEqual(holdings, {Q(-2), Q(0)})
        first, second = report.movement.step_entries
        self.assertEqual(sum((component.charge for component in first.components), Q(0)), Q(1, 6))
        self.assertEqual(sum((component.charge for component in second.components), Q(0)), Q(2, 15))
        self.assertEqual(report.movement.step_totals[0] + report.movement.step_totals[1],
                         report.movement.total)
        # The charge is a holdings-weighted reference difference, not a holdings norm.
        for entry in report.movement.step_entries:
            for component in entry.components:
                self.assertEqual(
                    component.charge,
                    max(Q(0), -component.holdings
                        * (component.old_reference - component.new_reference)))

    def test_start_claim_is_conserved_end_to_end(self):
        """AM-J4 on the fiber product: the start claim survives both steps exactly."""
        history = build_two_step_history("suspended-lineage")
        report = verify_history(history)
        state_0 = history.nodes[0].departure_state
        state_1 = history.nodes[1].arrival_state
        state_2 = history.nodes[2].arrival_state
        fiber = report.fiber_product
        support = fiber.covered_support

        def pull(table, native, projection):
            values = dict(zip(native, table))
            return tuple(values[projection[pair]] for pair in support)

        start = pull(state_0.claim_tables["harm"], state_0.semantic_states,
                     fiber.start_projection)
        # The first step reconstructs `harm` as the disjunction of three v_1 claims;
        # the second reconstructs each of those on the v_2 carrier.  Compose them.
        first_refs = next(r.new_claim_refs for r in history.steps[0].certificate.arena.reconstructions
                          if r.old_claim_ref == "harm")
        second_map = {r.old_claim_ref: r.new_claim_refs
                      for r in history.steps[1].certificate.arena.reconstructions}
        composed = tuple(
            max(pull(state_2.claim_tables[ref], state_2.semantic_states,
                     fiber.end_projection)[index]
                for first in first_refs for ref in second_map[first])
            for index in range(len(support))
        )
        middle = tuple(
            max(pull(state_1.claim_tables[first], state_1.semantic_states,
                     fiber.intermediate_projection)[index] for first in first_refs)
            for index in range(len(support))
        )
        self.assertEqual(start, (Q(0), Q(1), Q(1), Q(1)))
        self.assertEqual(middle, start)
        self.assertEqual(composed, start)
        # Only distinctions v_1 itself introduced are destroyed, and each is keyed.
        deltas = {entry.source_ref: entry.values
                  for entry in history.steps[1].certificate.discrepancies}
        self.assertEqual(deltas["reconstruct:coercion"], (Q(0), Q(0), Q(0), Q(-1)))
        self.assertEqual(deltas["reconstruct:frustration"], (Q(0), Q(0), Q(-1), Q(0)))

    def test_composite_movement_enters_the_joint_cap_without_a_holdings_norm(self):
        """CM-J4: two jumps into NL-J2, using carrier membership rather than |H|."""
        history = build_two_step_history("suspended-lineage")
        report = verify_history(history)
        states = (history.nodes[0].departure_state, history.nodes[1].arrival_state,
                  history.nodes[2].arrival_state)
        theta = min(state.compiler.theta for state in states)
        self.assertEqual(theta, Q(1, 10))
        error_budget, risk, ordinary = Q(1, 100), Q(1, 10), Q(1, 5)
        caps = movement_recursion(theta, error_budget, risk, ordinary,
                                  report.movement.reference_jumps)
        self.assertEqual(len(caps), 3)
        self.assertEqual(caps, (Q(1, 5), Q(31, 10), Q(321, 10)))
        self.assertLessEqual(report.movement.total, caps[-1])
        self.assertEqual(report.movement.total, Q(3, 10))
        # The hypothesis actually discharged at each step is carrier membership of
        # both reference lifts, not any bound on the holdings vector.
        for component in report.component_reports.values():
            self.assertTrue(component.payoff.old_reference_in_carrier)
            self.assertTrue(component.payoff.new_reference_in_carrier)
        self.assertEqual({p.holdings for p in states[0].positions}, {Q(-2)})

    # 11. An unresolved intermediate distinction prevents collection.
    def test_unresolved_distinction_prevents_collection(self):
        report = exact_composition_trace("suspended-lineage")["report"]
        collectable = {record.record_id for record in report.residue.collectable
                       if record.kind == "intermediate-occurrence"}
        self.assertEqual(collectable, set())
        retained = {record.record_id for record in report.residue.retained}
        for identifier in ("c:frustration+", "b:justify-frustration+",
                           "e:frustration-suspended", "w:frustration-suspended"):
            self.assertIn(identifier, retained)
        self.assertIn("arena:step:01", retained)
        self.assertIn("arena:step:12", retained)
        self.assertTrue(report.checks["retention"].passed)
        self.assertTrue(report.checks["collection"].passed)

    # 12. After a valid terminal disposition the residue becomes collectable.
    def test_terminal_disposition_makes_residue_collectable(self):
        report = exact_composition_trace("authorized-loss")["report"]
        self.assertTrue(report.passed, report.counterwitnesses)
        collectable = {record.record_id for record in report.residue.collectable
                       if record.kind == "intermediate-occurrence"}
        self.assertEqual(
            collectable,
            {"c:frustration+", "b:justify-frustration+",
             "e:frustration-suspended", "w:frustration-suspended"})
        reasons = {record.record_id: record.reason for record in report.residue.collectable}
        self.assertIn("terminal", reasons["c:frustration+"])
        # The disclosure records and the outstanding payoff carrier are never collected.
        retained = {record.record_id for record in report.residue.retained}
        self.assertIn("suspension:frustration-entitlement", retained)
        self.assertIn("loss:frustration-ancestry", retained)
        self.assertIn("arena:step:01", retained)
        self.assertEqual(report.composite_frontiers["c:frustration"], ())

    # 13. A stored expected output cannot make an invalid certificate pass.
    def test_stored_expectations_cannot_launder_a_certificate(self):
        tampered = verify_history(
            build_two_step_history("suspended-lineage", "tampered-discrepancy"))
        self.assertFalse(tampered.passed)
        self.assertIn("composition.component_failed", self._codes(tampered))
        self.assertIn(
            "semantic.lossless_collapse",
            {witness.code
             for witness in tampered.component_reports["step:12"].counterwitnesses})
        claimed = verify_history(
            build_two_step_history("suspended-lineage", "claimed-movement"))
        self.assertFalse(claimed.passed)
        mismatch = [witness for witness in claimed.counterwitnesses
                    if witness.code == "composition.declared_movement_mismatch"]
        self.assertEqual(mismatch[0].ids, ("1/6", "3/10"))
        self.assertEqual(claimed.movement.total, Q(3, 10))

    def test_repairs_are_ordered_by_preservation_strength(self):
        strongest = exact_composition_trace("suspended-lineage")["report"]
        conservative = exact_composition_trace("merged-suspension")["report"]
        terminal = exact_composition_trace("authorized-loss")["report"]
        for report in (strongest, conservative, terminal):
            self.assertTrue(report.passed, (report.history_id, report.counterwitnesses))
        # Only the suspended-lineage repair keeps a live, frustration-specific target
        # while retaining the operative coercion standing.
        self.assertTrue(strongest.composite_frontiers["c:frustration"])
        self.assertTrue(conservative.composite_frontiers["c:frustration"])
        self.assertEqual(terminal.composite_frontiers["c:frustration"], ())
        self.assertIn("e:bodily-or-coercive++", strongest.authority.end_authoritative)
        self.assertNotIn("e:merged-suspended++", conservative.authority.end_authoritative)
        self.assertEqual(len(strongest.authority.end_authoritative), 4)
        self.assertEqual(len(conservative.authority.end_authoritative), 3)

    def test_compose_migrations_interface(self):
        state_0, arrival_1, certificate_01 = build_harm_migration()
        departure_1, state_2, certificate_12 = build_merge_migration("suspended-lineage")
        report = compose_migrations(
            state_0, arrival_1, state_2, certificate_01, certificate_12,
            departure_state_1=departure_1, grant=MIGRATION_2_GRANT,
        )
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(report.movement.total, Q(3, 10))
        without_grant = compose_migrations(
            state_0, arrival_1, state_2, certificate_01, certificate_12,
            departure_state_1=departure_1,
        )
        self.assertFalse(without_grant.passed)
        self.assertIn("composition.unauthorized_intermediate_edit",
                      self._codes(without_grant))

    def test_grant_actor_must_match_the_migration_actor(self):
        state_0, arrival_1, certificate_01 = build_harm_migration()
        departure_1, state_2, certificate_12 = build_merge_migration("suspended-lineage")
        foreign = AdministrativeGrant(
            "grant:migration-2", "other-learner", ("auth:migration-2",),
            ("token:migration-2",), None, "a grant made by a different actor")
        report = compose_migrations(
            state_0, arrival_1, state_2, certificate_01, certificate_12,
            departure_state_1=departure_1, grant=foreign)
        self.assertFalse(report.passed)
        self.assertIn("composition.grant_actor_mismatch", self._codes(report))

    def test_history_questions_are_answered_from_derived_data(self):
        report = exact_composition_trace("suspended-lineage")["report"]
        answers = history_questions(report)
        self.assertEqual(len(answers), 8)
        self.assertEqual(len(answers["what changed between versions"]), 2)
        self.assertIn(("e:harm", "e:frustration-suspended++"),
                      answers["which old occurrence is responsible for a current occurrence"])
        self.assertIn("c:frustration+", answers["which challenges and burdens remain unresolved"])
        self.assertTrue(all(valid for _, valid in answers["why was each transition authorized"]))
        self.assertEqual(answers["end-to-end movement ledger"].total, Q(3, 10))

    def test_version_deltas_record_what_changed(self):
        report = exact_composition_trace("suspended-lineage")["report"]
        first, second = report.deltas
        self.assertEqual(first.semantic_states_added,
                         ("none", "physical", "coercion", "frustration"))
        self.assertEqual(first.semantic_states_removed, ("no-harm", "harm"))
        self.assertEqual(second.semantic_states_added, ("bodily-harm", "nonphysical-harm"))
        self.assertEqual(second.semantic_states_removed,
                         ("physical", "coercion", "frustration"))
        self.assertEqual(first.movement, Q(1, 6))
        self.assertEqual(second.movement, Q(2, 15))
        self.assertIn("suspend", second.occurrences_by_mode)
        self.assertIn("d12:e-f", second.occurrences_by_mode["suspend"])

    def test_intermediate_version_is_not_a_permanent_ontology(self):
        report = exact_composition_trace("authorized-loss")["report"]
        # Every intermediate record that is retained is retained for a named live
        # dependent; nothing is retained merely because it once was the ontology.
        for record in report.residue.retained:
            if record.kind == "intermediate-occurrence":
                self.assertTrue(record.live_dependents, record.record_id)
        self.assertTrue(report.residue.collectable)
        suspended_at_v1 = {
            occurrence.occurrence_id
            for occurrence in build_harm_migration()[1].occurrences
            if occurrence.status == OccurrenceStatus.SUSPENDED
        }
        collected = {record.record_id for record in report.residue.collectable}
        self.assertTrue(suspended_at_v1 <= collected)


class CompositeMigrationTests(unittest.TestCase):
    """Does a certified one-step `M_02 : V_0 -> V_2` exist for a two-step history?"""

    def _endpoints(self, history):
        return history.nodes[0].departure_state, history.nodes[2].arrival_state

    def _compose(self, repair="suspended-lineage", style="repaired"):
        history = build_two_step_history(repair)
        composite = compose_certificates(history, style)
        state_0, state_2 = self._endpoints(history)
        return history, composite, verify_migration(state_0, state_2, composite.certificate)

    # 1. Successful exact composition.
    def test_repaired_composite_is_certified_by_the_frozen_kernel(self):
        history, composite, report = self._compose()
        self.assertTrue(report.passed, report.counterwitnesses)
        self.assertEqual(composite.obstructions, ())
        self.assertEqual(len(report.checks), 9)
        # Lineage is composed by component, so each start occurrence is consumed once.
        starts = [identifier for cell in composite.certificate.cells
                  for identifier in cell.inputs]
        self.assertEqual(len(starts), len(set(starts)))
        state_0, _ = self._endpoints(history)
        live_starts = {o.occurrence_id for o in state_0.occurrences
                       if o.status != OccurrenceStatus.TERMINAL}
        self.assertEqual(set(starts), live_starts)
        # The split-then-merge component contributes one composite cell, not two.
        entitlement = next(c for c in composite.components if "e:harm" in c.start)
        self.assertEqual(len(entitlement.paths), 2)
        self.assertEqual(len([c for c in composite.certificate.cells
                              if "e:harm" in c.inputs]), 1)

    # 2. Naive endpoint translation is rejected.
    def test_naive_endpoint_composite_is_rejected(self):
        _, composite, report = self._compose(style="naive")
        self.assertFalse(report.passed)
        codes = {witness.code for witness in report.counterwitnesses}
        self.assertIn("relation.orphaned_edge", codes)
        self.assertIn("challenge.unknown_edge_target", codes)
        # Endpoint semantic correspondence alone supplies no ancestry transport.
        self.assertEqual(composite.certificate.edge_transports, ())
        orphans = {witness.ids[0] for witness in report.counterwitnesses
                   if witness.code == "relation.orphaned_edge"}
        self.assertIn("edge:f-support", orphans)

    # 3. Blind composition collides on shared ancestry.
    def test_blind_composition_collides_on_shared_ancestry(self):
        _, composite, report = self._compose(style="blind")
        self.assertFalse(report.passed)
        self.assertIn("occurrence.duplicate_input",
                      {witness.code for witness in report.counterwitnesses})
        collisions = [item for item in composite.obstructions
                      if item.code == "composite.lineage_collision"]
        self.assertTrue(collisions)
        entitlement = next(item for item in collisions
                           if item.start_occurrence == "e:harm")
        # The obstruction certificate names every part of the collision.
        self.assertEqual(entitlement.start_occurrence, "e:harm")
        self.assertEqual(
            {path[0] for path in entitlement.intermediate_paths},
            {"e:physical-or-coercion", "e:frustration-suspended"})
        self.assertEqual(entitlement.merged_descendant, "e:bodily-or-coercive++")
        self.assertEqual(entitlement.resource, "consuming-disposition")
        self.assertTrue(entitlement.detail)

    # 4. The obstruction theorem.
    def test_composite_certification_and_history_admissibility_are_incomparable(self):
        outcomes = {}
        for repair in MERGE_REPAIRS:
            history = build_two_step_history(repair)
            composite = compose_certificates(history)
            state_0, state_2 = self._endpoints(history)
            certified = (composite.certificate is not None
                         and verify_migration(state_0, state_2, composite.certificate).passed
                         and not composite.obstructions)
            outcomes[repair] = (verify_history(history).passed, certified)
        # A certified composite exists for a history the composition layer rejects.
        self.assertEqual(outcomes["merged-live"], (False, True))
        # And an admissible history has no certified composite.
        self.assertEqual(outcomes["authorized-loss"], (True, False))
        # So neither property implies the other.
        self.assertTrue(any(not h and c for h, c in outcomes.values()))
        self.assertTrue(any(h and not c for h, c in outcomes.values()))

    def test_challenge_laundering_survives_the_composite(self):
        """The composite cannot see an intermediate suspension, so it cannot object."""
        history = build_two_step_history("merged-live")
        composite = compose_certificates(history)
        state_0, state_2 = self._endpoints(history)
        self.assertTrue(verify_migration(state_0, state_2, composite.certificate).passed)
        # No start occurrence is suspended, and the entitlement branch that was
        # suspended at V_1 leaves no suspended trace in the composite at all.
        self.assertEqual(
            [o.occurrence_id for o in state_0.occurrences
             if o.status == OccurrenceStatus.SUSPENDED], [])
        suspended = {identifier for entry in composite.certificate.suspensions
                     for identifier in entry.output_occurrence_ids}
        entitlement = next(c for c in composite.components if "e:harm" in c.start)
        self.assertIn("e:frustration-suspended", entitlement.intermediate)
        self.assertEqual(suspended & set(entitlement.end), set())
        # The history layer is where the laundering is visible.
        report = verify_history(history)
        self.assertFalse(report.passed)
        self.assertIn("composition.suspension_resurrected",
                      {witness.code for witness in report.counterwitnesses})

    # 5. A terminally disposed branch has no composite.
    def test_branch_disposition_has_no_composite(self):
        _, composite, report = self._compose(repair="authorized-loss")
        self.assertFalse(report.passed)
        obstructions = [item for item in composite.obstructions
                        if item.code == "composite.branch_disposition_unexpressible"]
        self.assertTrue(obstructions)
        witness = next(item for item in obstructions if item.start_occurrence == "e:harm")
        self.assertEqual(witness.resource, "terminal-disposition")
        self.assertEqual(witness.merged_descendant, "e:bodily-or-coercive++")
        self.assertIn("accounting.invalid_terminal_disposition",
                      {w.code for w in report.counterwitnesses})
        # The history itself is admissible; only its one-step summary is not.
        self.assertTrue(verify_history(build_two_step_history("authorized-loss")).passed)

    # 6. No double authority.
    def test_recombination_does_not_duplicate_inherited_authority(self):
        for repair in ("suspended-lineage", "merged-suspension", "merged-live"):
            history = build_two_step_history(repair)
            composite = compose_certificates(history)
            ledger = authority_provenance(history, composite)
            self.assertTrue(ledger)
            for record in ledger:
                self.assertFalse(record.duplicated, (repair, record))
            entitlement = next(r for r in ledger if r.start_occurrence == "e:harm")
            self.assertLessEqual(len(entitlement.end_authoritative), 1)
        # Descendants stay genuinely distinct even though only one bears authority.
        history = build_two_step_history("suspended-lineage")
        composite = compose_certificates(history)
        component = next(c for c in composite.components if "e:harm" in c.start)
        self.assertEqual(len(component.end), 2)
        record = next(r for r in authority_provenance(history, composite)
                      if r.start_occurrence == "e:harm")
        self.assertEqual(len(record.end_authoritative), 1)

    # 7/8. Legacy retention while live, discharge after resolution.
    def test_legacy_distinction_is_retained_while_a_challenge_is_live(self):
        history, composite, report = self._compose()
        state_0, state_2 = self._endpoints(history)
        self.assertTrue(report.passed)
        # The endpoint ontology has three states; the composite arena keeps four.
        self.assertEqual(len(state_2.semantic_states), 3)
        self.assertEqual(len(composite.certificate.arena.covered_support), 4)
        self.assertEqual(len(composite.legacy_distinctions), 1)
        group = composite.legacy_distinctions[0]
        self.assertEqual(len(group.arena_states), 2)
        self.assertEqual(group.endpoint_state, "nonphysical-harm")
        verdict = legacy_discharge_report(composite, state_0, state_2)[0]
        self.assertFalse(verdict.dischargeable)
        self.assertEqual(verdict.live_dependents,
                         ("b:justify-frustration++", "c:frustration++"))

    def test_legacy_distinction_is_dischargeable_after_resolution(self):
        history, composite, report = self._compose()
        state_0, state_2 = self._endpoints(history)
        resolved = ("c:frustration++", "b:justify-frustration++")
        verdict = legacy_discharge_report(composite, state_0, state_2, resolved=resolved)[0]
        self.assertTrue(verdict.dischargeable)
        self.assertTrue(verdict.payoff_constant_on_fibers)
        self.assertTrue(verdict.discrepancy_constant_on_fibers)
        reduced = discharge_legacy_distinction(composite, verdict.group_id)
        after = verify_migration(state_0, state_2, reduced)
        # Collecting the scaffolding changes nothing live.
        self.assertTrue(after.passed, after.counterwitnesses)
        self.assertEqual(len(reduced.arena.covered_support), 3)
        self.assertEqual(after.payoff.analytic_movement, report.payoff.analytic_movement)
        self.assertEqual(after.challenge_frontiers, report.challenge_frontiers)
        self.assertEqual(after.reachable_entitlement_roots,
                         report.reachable_entitlement_roots)
        self.assertEqual(set(after.payoff.old_tables["p:harm"]),
                         set(report.payoff.old_tables["p:harm"]))

    def test_only_live_dependents_and_discrepancies_block_discharge(self):
        """A start payoff cannot separate a distinction introduced after V_0."""
        history, composite, _ = self._compose()
        state_0, state_2 = self._endpoints(history)
        arena = composite.certificate.arena
        group = composite.legacy_distinctions[0]
        # Both retained states have the same image in the start ontology, so any
        # start payoff pulled back along the start projection is constant on them.
        images = {arena.old_projection[state] for state in group.arena_states}
        self.assertEqual(len(images), 1)
        resolved = ("c:frustration++", "b:justify-frustration++")
        self.assertTrue(
            legacy_discharge_report(composite, state_0, state_2,
                                    resolved=resolved)[0].payoff_constant_on_fibers)
        # A recorded discrepancy that does separate them does block collection.
        index = [arena.covered_support.index(state) for state in group.arena_states]
        values = [Q(0)] * len(arena.covered_support)
        values[index[0]] = Q(1)
        separating = replace(composite, certificate=replace(
            composite.certificate,
            discrepancies=(DiscrepancyEntry("discrepancy:probe", "reconstruct02:harm",
                                            tuple(values), "auth:migration"),)))
        verdict = legacy_discharge_report(separating, state_0, state_2, resolved=resolved)[0]
        self.assertFalse(verdict.dischargeable)
        self.assertFalse(verdict.discrepancy_constant_on_fibers)
        self.assertIn("a recorded discrepancy separates the states being collapsed",
                      verdict.reasons)

    # 9. Exact reference movement.
    def test_composite_movement_is_exact_and_subadditive(self):
        history, composite, report = self._compose()
        state_0, state_2 = self._endpoints(history)
        state_1 = history.nodes[1].arrival_state
        holdings = next(p.holdings for p in state_0.positions if p.holdings != 0)
        reference = []
        for state, coordinate in ((state_0, "harm"), (state_1, "any-harm"),
                                  (state_2, "any-harm")):
            compiler = state.compiler
            reference.append(compiler.reference[compiler.coordinate_ids.index(coordinate)])
        first, second, whole = movement_composition(holdings, *reference)
        self.assertEqual((first, second, whole), (Q(1, 6), Q(2, 15), Q(3, 10)))
        self.assertEqual(first + second, whole)
        # The composite certificate derives the same number from raw data.
        self.assertEqual(report.payoff.analytic_movement, whole)
        self.assertEqual(verify_history(history).movement.total, whole)
        # The local carrier that suffices: both lifts lie in conv(W) on the
        # fiber product, with no bound on the holdings vector.
        self.assertTrue(report.payoff.old_reference_in_carrier)
        self.assertTrue(report.payoff.new_reference_in_carrier)
        self.assertEqual(report.payoff.live_payoff_vectors,
                         ((Q(0),), (Q(1),), (Q(1),), (Q(1),)))

    def test_composite_movement_can_under_report_the_history(self):
        holdings, first, middle, last, total, whole = reference_reversal_witness()
        self.assertEqual(total, Q(3, 10))
        self.assertEqual(whole, Q(0))
        self.assertLess(whole, total)
        # Subadditivity is general; equality needs both steps to be adverse.
        for a, b, c in ((Q(3, 4), Q(2, 3), Q(3, 5)), (Q(3, 5), Q(3, 4), Q(3, 5)),
                        (Q(1, 2), Q(1, 2), Q(1, 4))):
            one, two, both = movement_composition(Q(-2), a, b, c)
            self.assertLessEqual(both, one + two)

    # 10. Mutation tests: one relevant field flips acceptance.
    def test_mutating_one_field_flips_composite_acceptance(self):
        history, composite, report = self._compose()
        state_0, state_2 = self._endpoints(history)
        self.assertTrue(report.passed)
        certificate = composite.certificate

        dropped = replace(certificate, edge_transports=tuple(
            item for item in certificate.edge_transports
            if item.old_edge_id != "edge:f-support"))
        self.assertIn("relation.orphaned_edge", {
            w.code for w in verify_migration(state_0, state_2, dropped).counterwitnesses})

        rewritten = replace(state_2, payoff_tables={
            "any-harm": (Q(0), Q(1), Q(0))})
        self.assertIn("payoff.mismatch_without_legacy", {
            w.code for w in
            verify_migration(state_0, rewritten, certificate).counterwitnesses})

        unauthorized = replace(certificate, authorization=replace(
            certificate.authorization, migration_token_id="token:absent"))
        self.assertIn("authorization.binding_mismatch", {
            w.code for w in
            verify_migration(state_0, state_2, unauthorized).counterwitnesses})

        collapsed = replace(certificate, arena=replace(
            certificate.arena, new_projection={
                state: "none" for state in certificate.arena.states}))
        self.assertFalse(verify_migration(state_0, state_2, collapsed).passed)

    def test_every_composite_style_is_exercised(self):
        self.assertEqual(set(COMPOSITE_STYLES), {"naive", "blind", "repaired"})
        for style in COMPOSITE_STYLES:
            _, composite, _ = self._compose(style=style)
            self.assertIsNotNone(composite.certificate)
            self.assertEqual(composite.style, style)


if __name__ == "__main__":
    unittest.main()
