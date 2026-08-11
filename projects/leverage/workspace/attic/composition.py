"""Versioned migration histories and the composition of two accountable spans.

The one-step verifier in `src/migration.py` is used unchanged.  This module adds
a thin version/history layer around it and derives a `CompositionReport` for a
two-step history

    v_0 --C_01--> v_1 --C_12--> v_2

from raw finite data only.  Nothing in the report is a stored success
assertion: every displayed rational, lineage relation, frontier, and retention
verdict is recomputed from the states and certificates.  Fractions are exact.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
from fractions import Fraction as Q
from typing import Iterable, Mapping, Sequence

from src.migration import (
    AnalyticMovementEntry,
    ChallengeRoute,
    ChallengeSpec,
    CompilerEndorsement,
    CompilerSpec,
    ComparisonArena,
    DiscrepancyEntry,
    DispositionCell,
    DispositionMode,
    EdgeTransport,
    EndpointRecheck,
    EvidenceRoot,
    LossEntry,
    MigrationCertificate,
    MigrationState,
    NoninterferenceSpec,
    Occurrence,
    OccurrenceSort,
    OccurrenceStatus,
    Position,
    RelationEdge,
    RelationKind,
    SemanticReconstruction,
    SuspensionEntry,
    TargetKind,
    TerminalDisposition,
    TypedTarget,
    VerificationReport,
    build_harm_migration,
    constant_on_fibers,
    verify_migration,
)
from src.migration import ActivationRecord, AuthorizationRecord

DEFAULT_ACTOR = "public-learner"

COMPOSITION_CHECKS = (
    "components",
    "continuity",
    "fiber",
    "coverage",
    "lineage",
    "duplication",
    "edges",
    "targets",
    "authority",
    "residue",
    "movement",
    "retention",
    "collection",
)

STANDING_ORDER = {
    OccurrenceStatus.TERMINAL: 0,
    OccurrenceStatus.SUSPENDED: 1,
    OccurrenceStatus.LIVE: 2,
}


# --------------------------------------------------------------------------
# Version and history records
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class VersionIdentity:
    """Public identity of one ontology version in a history."""

    version_id: str
    ontology_id: str
    sequence_index: int
    actor_id: str
    parent_version_id: str | None = None


@dataclass(frozen=True)
class AdministrativeGrant:
    """The only edit permitted to a state between two migrations.

    A grant may add authorization identifiers and migration tokens (and, if
    declared, retake the freeze snapshot).  It may not touch semantics,
    occurrences, edges, positions, holdings, routes, or the compiler.
    """

    grant_id: str
    actor_id: str
    added_authorization_ids: tuple[str, ...] = ()
    added_migration_tokens: tuple[str, ...] = ()
    new_snapshot_id: str | None = None
    rationale: str = ""


@dataclass(frozen=True)
class VersionNode:
    identity: VersionIdentity
    arrival_state: MigrationState | None
    departure_state: MigrationState | None
    grant: AdministrativeGrant | None = None


@dataclass(frozen=True)
class HistoryStep:
    step_id: str
    from_version_id: str
    to_version_id: str
    actor_id: str
    certificate: MigrationCertificate


@dataclass(frozen=True)
class MigrationHistory:
    history_id: str
    nodes: tuple[VersionNode, ...]
    steps: tuple[HistoryStep, ...]
    declared_movement_total: Q | None = None


# --------------------------------------------------------------------------
# Report records
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CompositionCounterwitness:
    check: str
    code: str
    ids: tuple[str, ...]
    detail: str


@dataclass(frozen=True)
class CompositionCheckResult:
    name: str
    passed: bool
    counterwitnesses: tuple[CompositionCounterwitness, ...]


@dataclass(frozen=True)
class FiberProductArena:
    """The finite fiber product of two local comparison arenas."""

    pairs: tuple[tuple[str, str], ...]
    covered_support: tuple[tuple[str, str], ...]
    start_projection: Mapping[tuple[str, str], str]
    intermediate_projection: Mapping[tuple[str, str], str]
    end_projection: Mapping[tuple[str, str], str]
    uncovered_intermediate_states: tuple[str, ...]


@dataclass(frozen=True)
class LineagePath:
    start_occurrence: str
    intermediate_occurrence: str
    end_occurrence: str
    first_cell: str
    second_cell: str


@dataclass(frozen=True)
class LineageNormalization:
    paths: tuple[LineagePath, ...]
    ancestry: tuple[tuple[str, str], ...]
    intermediates: Mapping[tuple[str, str], tuple[str, ...]]
    duplicate_pairs: tuple[tuple[str, str], ...]
    terminated: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class CompositeEdgeImage:
    start_edge_id: str
    kind: RelationKind
    intermediate_edge_ids: tuple[str, ...]
    end_edge_ids: tuple[str, ...]
    outcome_refs: tuple[str, ...]


@dataclass(frozen=True)
class AuthorityLedger:
    start_authoritative: tuple[str, ...]
    intermediate_authoritative: tuple[str, ...]
    end_authoritative: tuple[str, ...]
    grants: tuple[tuple[str, str], ...]
    standing_lifts: tuple[tuple[str, str, str], ...]


@dataclass(frozen=True)
class CompositeMovementLedger:
    step_ids: tuple[str, ...]
    step_entries: tuple[AnalyticMovementEntry, ...]
    step_totals: tuple[Q, ...]
    total: Q
    reference_jumps: int
    tokens_consumed: tuple[str, ...]
    composite_payoff_tables: Mapping[str, tuple[Q, ...]]
    reference_path: tuple[Q, ...]


@dataclass(frozen=True)
class ResidueRecord:
    record_id: str
    kind: str
    version_id: str
    live_dependents: tuple[str, ...]
    disposition: str
    reason: str


@dataclass(frozen=True)
class RetentionVerdict:
    retained: tuple[ResidueRecord, ...]
    collectable: tuple[ResidueRecord, ...]


@dataclass(frozen=True)
class VersionDelta:
    step_id: str
    semantic_states_added: tuple[str, ...]
    semantic_states_removed: tuple[str, ...]
    claims_added: tuple[str, ...]
    claims_removed: tuple[str, ...]
    occurrences_by_mode: Mapping[str, tuple[str, ...]]
    edges_added: tuple[str, ...]
    edges_removed: tuple[str, ...]
    movement: Q


@dataclass(frozen=True)
class CompositionReport:
    passed: bool
    history_id: str
    versions: tuple[VersionIdentity, ...]
    component_reports: Mapping[str, VerificationReport]
    checks: Mapping[str, CompositionCheckResult]
    counterwitnesses: tuple[CompositionCounterwitness, ...]
    fiber_product: FiberProductArena
    lineage: LineageNormalization
    composite_edges: tuple[CompositeEdgeImage, ...]
    composite_frontiers: Mapping[str, tuple[TypedTarget, ...]]
    authority: AuthorityLedger
    residue: RetentionVerdict
    movement: CompositeMovementLedger
    deltas: tuple[VersionDelta, ...]


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------


def _index(items: Iterable[object], field_name: str) -> dict[str, object]:
    return {str(getattr(item, field_name)): item for item in items}


def _issue(store: dict[str, list[CompositionCounterwitness]], check: str, code: str,
           ids: Iterable[str], detail: str) -> None:
    store[check].append(CompositionCounterwitness(check, code, tuple(ids), detail))


def _active(occurrence: Occurrence) -> bool:
    return occurrence.status in (OccurrenceStatus.LIVE, OccurrenceStatus.SUSPENDED)


def _cell_by_input(certificate: MigrationCertificate) -> dict[str, DispositionCell]:
    return {identifier: cell for cell in certificate.cells for identifier in cell.inputs}


# --------------------------------------------------------------------------
# History assembly
# --------------------------------------------------------------------------


def apply_grant(state: MigrationState, grant: AdministrativeGrant) -> MigrationState:
    """Produce the departure state of an intermediate version from its arrival."""
    return replace(
        state,
        snapshot_id=grant.new_snapshot_id or state.snapshot_id,
        authorization_ids=state.authorization_ids
        + tuple(a for a in grant.added_authorization_ids if a not in state.authorization_ids),
        migration_tokens=state.migration_tokens
        + tuple(t for t in grant.added_migration_tokens if t not in state.migration_tokens),
    )


def build_history(
    state_0: MigrationState,
    state_1: MigrationState,
    state_2: MigrationState,
    certificate_01: MigrationCertificate,
    certificate_12: MigrationCertificate,
    *,
    departure_state_1: MigrationState | None = None,
    grant: AdministrativeGrant | None = None,
    versions: Sequence[VersionIdentity] | None = None,
    actor_id: str = DEFAULT_ACTOR,
    history_id: str = "history:harm",
    declared_movement_total: Q | None = None,
) -> MigrationHistory:
    if versions is None:
        versions = (
            VersionIdentity("v0", state_0.state_id, 0, actor_id, None),
            VersionIdentity("v1", state_1.state_id, 1, actor_id, "v0"),
            VersionIdentity("v2", state_2.state_id, 2, actor_id, "v1"),
        )
    if departure_state_1 is None:
        departure_state_1 = apply_grant(state_1, grant) if grant else state_1
    nodes = (
        VersionNode(versions[0], None, state_0, None),
        VersionNode(versions[1], state_1, departure_state_1, grant),
        VersionNode(versions[2], state_2, None, None),
    )
    steps = (
        HistoryStep("step:01", versions[0].version_id, versions[1].version_id,
                    actor_id, certificate_01),
        HistoryStep("step:12", versions[1].version_id, versions[2].version_id,
                    actor_id, certificate_12),
    )
    return MigrationHistory(history_id, nodes, steps, declared_movement_total)


# --------------------------------------------------------------------------
# The composition report
# --------------------------------------------------------------------------


def verify_history(history: MigrationHistory) -> CompositionReport:
    """Derive the fourteen composition results for a two-step linear history."""
    issues: dict[str, list[CompositionCounterwitness]] = {n: [] for n in COMPOSITION_CHECKS}
    node_0, node_1, node_2 = history.nodes
    step_01, step_12 = history.steps
    certificate_01, certificate_12 = step_01.certificate, step_12.certificate
    state_0 = node_0.departure_state
    arrival_1 = node_1.arrival_state
    departure_1 = node_1.departure_state
    state_2 = node_2.arrival_state
    assert state_0 is not None and arrival_1 is not None
    assert departure_1 is not None and state_2 is not None

    # 1. Both component migrations are verified, not assumed.
    report_01 = verify_migration(state_0, arrival_1, certificate_01)
    report_12 = verify_migration(departure_1, state_2, certificate_12)
    component_reports = {step_01.step_id: report_01, step_12.step_id: report_12}
    for step, report in ((step_01, report_01), (step_12, report_12)):
        for witness in report.counterwitnesses:
            _issue(issues, "components", "composition.component_failed",
                   (step.step_id, witness.code) + witness.ids,
                   f"{step.step_id} fails the one-step check {witness.check}: {witness.detail}")

    # 2. Snapshot, grant, and activation-chain continuity at the shared version.
    grant = node_1.grant
    allowed_auth = set(grant.added_authorization_ids) if grant else set()
    allowed_tokens = set(grant.added_migration_tokens) if grant else set()
    declared_snapshot = grant.new_snapshot_id if grant else None
    for spec in fields(MigrationState):
        arrival_value = getattr(arrival_1, spec.name)
        departure_value = getattr(departure_1, spec.name)
        if arrival_value == departure_value:
            continue
        if spec.name == "authorization_ids":
            added = tuple(a for a in departure_value if a not in arrival_value)
            dropped = tuple(a for a in arrival_value if a not in departure_value)
            if dropped or set(added) - allowed_auth:
                _issue(issues, "continuity", "composition.unauthorized_intermediate_edit",
                       ("authorization_ids",) + added + dropped,
                       "intermediate authorization set changed outside the declared grant")
        elif spec.name == "migration_tokens":
            added = tuple(t for t in departure_value if t not in arrival_value)
            dropped = tuple(t for t in arrival_value if t not in departure_value)
            if dropped or set(added) - allowed_tokens:
                _issue(issues, "continuity", "composition.unauthorized_intermediate_edit",
                       ("migration_tokens",) + added + dropped,
                       "intermediate token set changed outside the declared grant")
        elif spec.name == "snapshot_id" and departure_value == declared_snapshot:
            continue
        else:
            _issue(issues, "continuity", "composition.unauthorized_intermediate_edit",
                   (spec.name,), f"field {spec.name} was edited between the two migrations")
    if certificate_01.activation.final_active_state_id != departure_1.state_id:
        _issue(issues, "continuity", "composition.activation_chain_broken",
               (certificate_01.activation.final_active_state_id, departure_1.state_id),
               "the first activation does not end at the state the second departs from")
    if certificate_12.activation.preactivation_active_state_id != arrival_1.state_id:
        _issue(issues, "continuity", "composition.activation_chain_broken",
               (certificate_12.activation.preactivation_active_state_id, arrival_1.state_id),
               "the second activation does not begin at the state the first produced")
    if certificate_12.old_snapshot_id != departure_1.snapshot_id:
        _issue(issues, "continuity", "composition.snapshot_chain_broken",
               (certificate_12.old_snapshot_id, departure_1.snapshot_id),
               "the second certificate is bound to a snapshot the history does not reach")
    token_01 = certificate_01.authorization.migration_token_id if certificate_01.authorization else None
    token_12 = certificate_12.authorization.migration_token_id if certificate_12.authorization else None
    if token_01 is not None and token_01 == token_12:
        _issue(issues, "continuity", "composition.token_reuse", (str(token_01),),
               "one consuming migration token cannot authorize two ontology changes")
    if grant is not None and grant.actor_id != step_12.actor_id:
        _issue(issues, "continuity", "composition.grant_actor_mismatch",
               (grant.grant_id, grant.actor_id, step_12.actor_id),
               "the administrative grant and the migration it enables have different actors")

    # 3. The finite fiber-product comparison arena.
    arena_01, arena_12 = certificate_01.arena, certificate_12.arena
    pairs: list[tuple[str, str]] = []
    start_projection: dict[tuple[str, str], str] = {}
    intermediate_projection: dict[tuple[str, str], str] = {}
    end_projection: dict[tuple[str, str], str] = {}
    for left in arena_01.states:
        middle = arena_01.new_projection.get(left)
        if middle is None:
            continue
        for right in arena_12.states:
            if arena_12.old_projection.get(right) != middle:
                continue
            start = arena_01.old_projection.get(left)
            end = arena_12.new_projection.get(right)
            if start is None or end is None:
                _issue(issues, "fiber", "composition.undefined_fiber_projection", (left, right),
                       "a fiber-product pair has no start or end projection")
                continue
            pair = (left, right)
            pairs.append(pair)
            start_projection[pair] = start
            intermediate_projection[pair] = middle
            end_projection[pair] = end
    covered = tuple(
        pair for pair in pairs
        if pair[0] in arena_01.covered_support and pair[1] in arena_12.covered_support
    )
    if not pairs:
        _issue(issues, "fiber", "composition.empty_fiber_product", (),
               "the two local arenas share no intermediate semantic state")
    required_intermediate = tuple(sorted({
        arena_01.new_projection[state] for state in arena_01.covered_support
        if state in arena_01.new_projection
    }))
    reached_intermediate = {intermediate_projection[pair] for pair in covered}
    uncovered_intermediate = tuple(s for s in required_intermediate if s not in reached_intermediate)
    fiber = FiberProductArena(tuple(pairs), covered, start_projection,
                              intermediate_projection, end_projection, uncovered_intermediate)

    # 4. Live semantic and payoff support survives to the fiber product.
    for missing in uncovered_intermediate:
        _issue(issues, "coverage", "composition.fiber_support_gap", (missing,),
               "an intermediate state carried by the first arena has no covered second-arena fiber")
    old_positions = _index(state_0.positions, "occurrence_id")
    new_positions = _index(state_2.positions, "occurrence_id")
    composite_payoffs: dict[str, tuple[Q, ...]] = {}
    support_start = tuple(start_projection[pair] for pair in covered)
    support_end = tuple(end_projection[pair] for pair in covered)
    outstanding = tuple(
        position.occurrence_id for position in state_0.positions if position.holdings != 0
    )
    for position_id in outstanding:
        position = old_positions[position_id]
        table = state_0.payoff_tables.get(position.payoff_ref)
        if table is None or len(table) != len(state_0.semantic_states):
            _issue(issues, "coverage", "composition.payoff_support_gap", (position_id,),
                   "an outstanding start payoff has no table on the start ontology")
            continue
        values = dict(zip(state_0.semantic_states, table))
        try:
            composite_payoffs[position_id] = tuple(Q(values[state]) for state in support_start)
        except KeyError:
            _issue(issues, "coverage", "composition.payoff_support_gap", (position_id,),
                   "an outstanding start payoff is undefined on the fiber product")
    for reconstruction in arena_01.reconstructions:
        if reconstruction.old_claim_ref not in state_0.claim_tables:
            _issue(issues, "coverage", "composition.claim_support_gap",
                   (reconstruction.reconstruction_id, reconstruction.old_claim_ref),
                   "a start claim named by the first arena has no table to carry forward")

    # 5. Normalized end-to-end occurrence lineage.
    cells_01, cells_12 = _cell_by_input(certificate_01), _cell_by_input(certificate_12)
    occ_0 = _index(state_0.occurrences, "occurrence_id")
    occ_1 = _index(arrival_1.occurrences, "occurrence_id")
    occ_2 = _index(state_2.occurrences, "occurrence_id")
    paths: list[LineagePath] = []
    for start_id, occurrence in occ_0.items():
        if not _active(occurrence):
            continue
        first = cells_01.get(start_id)
        if first is None:
            continue
        for middle_id in first.outputs:
            second = cells_12.get(middle_id)
            if second is None:
                continue
            for end_id in second.outputs:
                paths.append(LineagePath(start_id, middle_id, end_id,
                                         first.cell_id, second.cell_id))
    ancestry_map: dict[tuple[str, str], list[str]] = {}
    for path in paths:
        ancestry_map.setdefault((path.start_occurrence, path.end_occurrence), []).append(
            path.intermediate_occurrence)
    ancestry = tuple(sorted(ancestry_map))
    intermediates = {key: tuple(sorted(set(value))) for key, value in ancestry_map.items()}
    duplicate_pairs = tuple(key for key in ancestry if len(intermediates[key]) > 1)
    descendants: dict[str, set[str]] = {}
    for start_id, end_id in ancestry:
        descendants.setdefault(start_id, set()).add(end_id)
    reached_end = {end for _, end in ancestry}
    terminated: list[tuple[str, str]] = []
    terminal_cells = {
        item.source_cell_id for certificate in (certificate_01, certificate_12)
        for item in certificate.terminal_dispositions
    }
    loss_cells = {
        loss.source_ref for certificate in (certificate_01, certificate_12)
        for loss in certificate.losses
    }
    for start_id, occurrence in sorted(occ_0.items()):
        if not _active(occurrence):
            continue
        first = cells_01.get(start_id)
        if first is None:
            continue
        if descendants.get(start_id):
            continue
        chain = [first.cell_id] + [
            cells_12[middle].cell_id for middle in first.outputs if middle in cells_12
        ]
        if any(cell_id in terminal_cells or cell_id in loss_cells for cell_id in chain):
            terminated.append((start_id, chain[-1]))
        else:
            _issue(issues, "lineage", "composition.lost_lineage", (start_id,) + tuple(chain),
                   "a live start occurrence reaches neither an end occurrence nor a recorded terminal outcome")
    introduced = {
        identifier for cell in certificate_12.cells
        if cell.mode == DispositionMode.INTRODUCE for identifier in cell.outputs
    }
    first_introduced = {
        identifier for cell in certificate_01.cells
        if cell.mode == DispositionMode.INTRODUCE for identifier in cell.outputs
    }
    for identifier, occurrence in sorted(occ_2.items()):
        if not _active(occurrence) or identifier in reached_end or identifier in introduced:
            continue
        producing = next(
            (cell for cell in certificate_12.cells if identifier in cell.outputs), None)
        if producing is not None and set(producing.inputs) & first_introduced:
            continue
        _issue(issues, "lineage", "composition.unanchored_descendant", (identifier,),
               "a live end occurrence has no start ancestor and no recorded introduction")
    lineage = LineageNormalization(tuple(paths), ancestry, intermediates,
                                  duplicate_pairs, tuple(terminated))

    # 6. Duplicate intermediate paths created by split then merge.
    for key in duplicate_pairs:
        start_id, end_id = key
        statuses = {occ_1[m].status for m in intermediates[key] if m in occ_1}
        end_occurrence = occ_2.get(end_id)
        if end_occurrence is None:
            continue
        weakest = min((STANDING_ORDER[s] for s in statuses), default=STANDING_ORDER[end_occurrence.status])
        if STANDING_ORDER[end_occurrence.status] > weakest:
            _issue(issues, "duplication", "composition.unreconciled_duplicate_path",
                   (start_id, end_id) + intermediates[key],
                   "a merge of intermediate branches of unequal standing produces the stronger standing")
    residue_keys: list[tuple[str, str]] = []
    for certificate in (certificate_01, certificate_12):
        for loss in certificate.losses:
            residue_keys.append((loss.source_ref, loss.lost_content))
    for key in sorted({k for k in residue_keys if residue_keys.count(k) > 1}):
        _issue(issues, "duplication", "composition.duplicate_residue_key", key,
               "the same semantic loss is entered by both certificates")
    literal_keys: list[tuple[str, str, str]] = []
    for certificate in (certificate_01, certificate_12):
        for liability in certificate.literal_liabilities:
            literal_keys.append((liability.event_id, liability.kind, liability.obligation_id))
    for key in sorted({k for k in literal_keys if literal_keys.count(k) > 1}):
        _issue(issues, "duplication", "composition.duplicate_literal_key", key,
               "the same literal obligation is debited by both certificates")

    # 7. Composite relation edges.
    transports_01 = _index(certificate_01.edge_transports, "old_edge_id")
    transports_12 = _index(certificate_12.edge_transports, "old_edge_id")
    edges_1 = _index(arrival_1.relation_edges, "edge_id")
    edges_2 = _index(state_2.relation_edges, "edge_id")
    composite_edges: list[CompositeEdgeImage] = []
    for edge in state_0.relation_edges:
        first = transports_01.get(edge.edge_id)
        if first is None:
            continue
        intermediate_ids = tuple(first.new_edge_ids)
        end_ids: list[str] = []
        outcome_refs: list[str] = []
        if first.outcome_ref:
            outcome_refs.append(first.outcome_ref)
        for middle_id in intermediate_ids:
            second = transports_12.get(middle_id)
            if second is None:
                _issue(issues, "edges", "composition.edge_transport_gap",
                       (edge.edge_id, middle_id),
                       "an intermediate relation edge has no second-step transport")
                continue
            if second.outcome_ref:
                outcome_refs.append(second.outcome_ref)
            end_ids.extend(second.new_edge_ids)
        for end_id in end_ids:
            image = edges_2.get(end_id)
            if image is None or image.kind != edge.kind:
                _issue(issues, "edges", "composition.edge_kind_drift",
                       (edge.edge_id, end_id),
                       "the composite image of a relation edge is absent or changes kind")
        if intermediate_ids and not end_ids and not outcome_refs:
            _issue(issues, "edges", "composition.edge_vanished", (edge.edge_id,),
                   "a start relation edge has an empty composite image and no recorded outcome")
        composite_edges.append(CompositeEdgeImage(
            edge.edge_id, edge.kind, intermediate_ids, tuple(end_ids), tuple(outcome_refs)))

    # 8. Typed challenge targets transported to the complete descendant frontier.
    reconstruction_map_12: dict[str, tuple[str, ...]] = {
        reconstruction.old_claim_ref: reconstruction.new_claim_refs
        for reconstruction in arena_12.reconstructions
    }
    edge_target_kind = {
        RelationKind.JUSTIFICATION: TargetKind.ANCESTRY_EDGE,
        RelationKind.WARRANT_PREMISE: TargetKind.WARRANT_PREMISE,
        RelationKind.WARRANT_CONSEQUENCE: TargetKind.WARRANT_CONSEQUENCE,
    }
    specs_2 = _index(state_2.challenges, "challenge_id")
    composite_frontiers: dict[str, tuple[TypedTarget, ...]] = {}
    for challenge in state_0.challenges:
        frontier_1 = report_01.challenge_frontiers.get(challenge.challenge_id, ())
        required: set[TypedTarget] = set()
        for target in frontier_1:
            if target.kind == TargetKind.OCCURRENCE:
                cell = cells_12.get(target.target_id)
                if cell is not None:
                    required.update(
                        TypedTarget(TargetKind.OCCURRENCE, output) for output in cell.outputs)
            elif target.kind == TargetKind.SEMANTIC_COMPONENT:
                required.update(
                    TypedTarget(TargetKind.SEMANTIC_COMPONENT, ref)
                    for ref in reconstruction_map_12.get(target.target_id, ()))
            else:
                transport = transports_12.get(target.target_id)
                if transport is not None:
                    for edge_id in transport.new_edge_ids:
                        image = edges_2.get(edge_id)
                        if image is not None:
                            required.add(TypedTarget(
                                edge_target_kind.get(image.kind, target.kind), edge_id))
        composite_frontiers[challenge.challenge_id] = tuple(sorted(
            required, key=lambda item: (item.kind.value, item.target_id)))
        successors: set[str] = set()
        second_cells: set[str] = set()
        first_cell = cells_01.get(challenge.challenge_id)
        if first_cell is not None:
            for middle in first_cell.outputs:
                second_cell = cells_12.get(middle)
                if second_cell is not None:
                    successors.update(second_cell.outputs)
                    second_cells.add(second_cell.cell_id)
        actual: set[TypedTarget] = set()
        for successor in successors:
            spec = specs_2.get(successor)
            if spec is not None:
                actual.update(spec.targets)
        missing, extra = required - actual, actual - required
        if missing:
            _issue(issues, "targets", "composition.frontier_uncovered",
                   (challenge.challenge_id,) + tuple(sorted(t.target_id for t in missing)),
                   "a composite descendant of a frozen challenge target is not covered end to end")
        if extra:
            _issue(issues, "targets", "composition.frontier_dilated",
                   (challenge.challenge_id,) + tuple(sorted(t.target_id for t in extra)),
                   "the composite challenge acquires a target that is not a descendant of its frozen target")
        if not required and not successors:
            disposed = any(item.source_cell_id in second_cells
                           for item in certificate_12.terminal_dispositions)
            if not disposed:
                _issue(issues, "targets", "composition.challenge_vanished",
                       (challenge.challenge_id,),
                       "a start challenge has no composite frontier and no recorded terminal outcome")

    # 9. Practical authority across the composite.
    start_authoritative = tuple(sorted(
        i for i, o in occ_0.items() if o.practical_authority and _active(o)))
    intermediate_authoritative = tuple(sorted(
        i for i, o in occ_1.items() if o.practical_authority and _active(o)))
    end_authoritative = tuple(sorted(
        i for i, o in occ_2.items() if o.practical_authority and _active(o)))
    grants: list[tuple[str, str]] = []
    for certificate in (certificate_01, certificate_12):
        if certificate.authorization is not None:
            grants.extend(certificate.authorization.authority_grants)
    standing_lifts: list[tuple[str, str, str]] = []
    for certificate, source_index, target_index in (
        (certificate_01, occ_0, occ_1), (certificate_12, occ_1, occ_2),
    ):
        granted = set(certificate.authorization.authority_grants
                      if certificate.authorization else ())
        disposed_cells = {item.source_cell_id for item in certificate.terminal_dispositions}
        for cell in certificate.cells:
            for source_id in cell.inputs:
                source = source_index.get(source_id)
                if source is None:
                    continue
                for target_id in cell.outputs:
                    target = target_index.get(target_id)
                    if target is None:
                        continue
                    lifted_status = (STANDING_ORDER[target.status]
                                     > STANDING_ORDER[source.status])
                    lifted_authority = target.practical_authority and not source.practical_authority
                    if not (lifted_status or lifted_authority):
                        continue
                    if (cell.cell_id, target_id) in granted or cell.cell_id in disposed_cells:
                        continue
                    standing_lifts.append((cell.cell_id, source_id, target_id))
                    _issue(issues, "authority" if lifted_authority else "residue",
                           "composition.standing_not_monotone",
                           (cell.cell_id, source_id, target_id),
                           "an output acquires standing or practical authority its input did not hold")
    if len(end_authoritative) > len(start_authoritative) + len(grants):
        _issue(issues, "authority", "composition.authority_inflated",
               start_authoritative + end_authoritative,
               "the composite carries more practical authority than the start plus recorded grants")
    authority = AuthorityLedger(start_authoritative, intermediate_authoritative,
                                end_authoritative, tuple(grants), tuple(standing_lifts))

    # 10. Inherited suspensions, losses, and legacy dependencies.
    inherited_suspensions = {
        occurrence_id: entry
        for entry in certificate_01.suspensions
        for occurrence_id in entry.output_occurrence_ids
    }
    second_suspended = {
        occurrence_id
        for entry in certificate_12.suspensions
        for occurrence_id in entry.output_occurrence_ids
    }
    for occurrence_id, entry in sorted(inherited_suspensions.items()):
        cell = cells_12.get(occurrence_id)
        if cell is None:
            _issue(issues, "residue", "composition.suspension_dropped",
                   (entry.suspension_id, occurrence_id),
                   "an inherited suspended occurrence is not consumed by the second migration")
            continue
        disposed = any(item.source_cell_id == cell.cell_id
                       for item in certificate_12.terminal_dispositions)
        if disposed:
            continue
        successors = [occ_2[o] for o in cell.outputs if o in occ_2]
        if entry.burdens_remain and not any(
            o.occurrence_id in second_suspended or o.status == OccurrenceStatus.SUSPENDED
            for o in successors
        ):
            _issue(issues, "residue", "composition.suspension_resurrected",
                   (entry.suspension_id, occurrence_id) + tuple(cell.outputs),
                   "an inherited suspension with a remaining burden ends without a terminal disposition")
    for certificate, label in ((certificate_01, step_01.step_id), (certificate_12, step_12.step_id)):
        authorization = certificate.authorization
        for loss in certificate.losses:
            if authorization is None or loss.loss_id not in authorization.allowed_loss_ids:
                _issue(issues, "residue", "composition.unauthorized_inherited_loss",
                       (label, loss.loss_id), "a composite loss is not bound to its step authorization")
        for legacy in certificate.legacy_retentions:
            if authorization is None or legacy.legacy_id not in authorization.allowed_legacy_ids:
                _issue(issues, "residue", "composition.unauthorized_inherited_legacy",
                       (label, legacy.legacy_id), "a composite legacy carrier is not authorized")

    # 11. Exact composite payoff meanings and reference movements.
    entries = (report_01.payoff.movement_entry, report_12.payoff.movement_entry)
    totals = (report_01.payoff.analytic_movement, report_12.payoff.analytic_movement)
    composite_total = sum(totals, Q(0))
    tokens = tuple(
        certificate.authorization.migration_token_id
        for certificate in (certificate_01, certificate_12)
        if certificate.authorization is not None
    )
    coordinate_map_01 = dict(certificate_01.coordinate_transports)
    coordinate_map_12 = dict(certificate_12.coordinate_transports)
    reference_path: list[Q] = []
    for position_id in outstanding:
        position = old_positions[position_id]
        coordinate_0 = position.payoff_ref
        coordinate_1 = coordinate_map_01.get(coordinate_0)
        coordinate_2 = coordinate_map_12.get(coordinate_1 or "")
        if coordinate_1 is None or coordinate_2 is None:
            _issue(issues, "movement", "composition.reference_path_broken",
                   (position_id, coordinate_0, str(coordinate_1), str(coordinate_2)),
                   "an outstanding payoff coordinate has no end-to-end reference path")
            continue
        try:
            reference_path = [
                state_0.compiler.reference[state_0.compiler.coordinate_ids.index(coordinate_0)],
                arrival_1.compiler.reference[arrival_1.compiler.coordinate_ids.index(coordinate_1)],
                state_2.compiler.reference[state_2.compiler.coordinate_ids.index(coordinate_2)],
            ]
        except ValueError:
            _issue(issues, "movement", "composition.reference_path_broken",
                   (position_id,), "a reference coordinate is absent from one compiler")
            continue
        end_position = next(
            (p for p in new_positions.values() if p.payoff_ref == coordinate_2), None)
        if end_position is None or end_position.holdings != position.holdings:
            _issue(issues, "movement", "composition.holdings_not_transported",
                   (position_id, coordinate_2),
                   "outstanding holdings are not carried unchanged across the composite")
        table_2 = state_2.payoff_tables.get(coordinate_2)
        composite_start = composite_payoffs.get(position_id)
        composite_end = (
            None if table_2 is None
            else tuple(Q(dict(zip(state_2.semantic_states, table_2))[state])
                       for state in support_end)
            if set(support_end) <= set(state_2.semantic_states) else None
        )
        legacy_ids = {entry.legacy_id for entry in certificate_12.legacy_retentions}
        if composite_start is None or composite_end is None:
            if coordinate_2 not in legacy_ids:
                _issue(issues, "movement", "composition.composite_payoff_undefined",
                       (position_id,), "the composite payoff meaning is undefined on the fiber product")
        elif composite_start != composite_end:
            _issue(issues, "movement", "composition.composite_payoff_drift",
                   (position_id, coordinate_0, coordinate_2),
                   "the end payoff does not agree with the start payoff on the fiber product")
    if history.declared_movement_total is not None and history.declared_movement_total != composite_total:
        _issue(issues, "movement", "composition.declared_movement_mismatch",
               (str(history.declared_movement_total), str(composite_total)),
               "a stored movement total disagrees with the value derived from the certificates")
    movement = CompositeMovementLedger(
        (step_01.step_id, step_12.step_id), entries, totals, composite_total,
        len(history.steps), tokens, composite_payoffs, tuple(reference_path))

    # 12/13. Minimal public intermediate records and collection candidates.
    live_target_chain: set[str] = set()
    for targets in composite_frontiers.values():
        for target in targets:
            live_target_chain.add(target.target_id)
    for spec in state_2.challenges:
        for target in spec.targets:
            live_target_chain.add(target.target_id)
    reverse_edge_12 = {
        image: old for old, transport in transports_12.items()
        for image in transport.new_edge_ids
    }
    live_intermediate_edges = {
        reverse_edge_12[target] for target in live_target_chain if target in reverse_edge_12
    }
    retained: list[ResidueRecord] = []
    collectable: list[ResidueRecord] = []
    for identifier, occurrence in sorted(occ_1.items()):
        if not _active(occurrence):
            continue
        cell = cells_12.get(identifier)
        dependents = tuple(sorted(
            output for output in (cell.outputs if cell else ())
            if output in occ_2 and _active(occ_2[output])))
        disposed = bool(cell) and any(
            item.source_cell_id == cell.cell_id for item in certificate_12.terminal_dispositions)
        record = ResidueRecord(
            identifier, "intermediate-occurrence", node_1.identity.version_id, dependents,
            "terminally-disposed" if disposed else ("live" if dependents else "unreferenced"),
            "")
        if dependents:
            retained.append(replace(record, reason="a live or suspended descendant depends on it"))
        elif disposed:
            collectable.append(replace(
                record, reason="its lineage ended in a witnessed terminal disposition"))
        else:
            collectable.append(replace(record, reason="no live descendant and no live target"))
    for edge_id in sorted(edges_1):
        dependents = tuple(sorted(transports_12[edge_id].new_edge_ids)) if edge_id in transports_12 else ()
        record = ResidueRecord(edge_id, "intermediate-edge", node_1.identity.version_id,
                               dependents, "live" if dependents else "unreferenced", "")
        if dependents or edge_id in live_intermediate_edges:
            retained.append(replace(record, reason="a composite relation image or live target depends on it"))
        else:
            collectable.append(replace(record, reason="no composite image and no live target"))
    for certificate, label in ((certificate_01, step_01.step_id), (certificate_12, step_12.step_id)):
        for entry in certificate.suspensions:
            retained.append(ResidueRecord(
                entry.suspension_id, "suspension", label, entry.output_occurrence_ids,
                "suspended", "an authorized suspension is a permanent public record"))
        for loss in certificate.losses:
            retained.append(ResidueRecord(
                loss.loss_id, "loss", label, (), "lost",
                "an authorized loss is a permanent public record"))
        for legacy in certificate.legacy_retentions:
            retained.append(ResidueRecord(
                legacy.legacy_id, "legacy", label, (legacy.output_position_id,), "live",
                "a legacy carrier settles an outstanding contract"))
    arena_disposition = "live" if outstanding else "unreferenced"
    for label, arena in ((step_01.step_id, arena_01), (step_12.step_id, arena_12)):
        record = ResidueRecord(f"arena:{label}", "comparison-arena", label,
                               outstanding, arena_disposition, "")
        if outstanding:
            retained.append(replace(
                record, reason="an outstanding payoff meaning and reference lift are indexed by it"))
        else:
            collectable.append(replace(
                record, reason="no outstanding payoff or discrepancy is indexed by it"))
    retained_ids = {record.record_id for record in retained}
    for record in collectable:
        if record.record_id in retained_ids:
            _issue(issues, "collection", "composition.retention_conflict", (record.record_id,),
                   "a record is simultaneously required and offered for collection")
    for identifier in sorted(live_target_chain):
        if identifier in occ_1 and identifier not in retained_ids:
            _issue(issues, "retention", "composition.retention_gap", (identifier,),
                   "a live composite target depends on an intermediate record marked collectable")
    residue = RetentionVerdict(tuple(retained), tuple(collectable))

    # What changed between versions.
    deltas: list[VersionDelta] = []
    for step, before, after, report in (
        (step_01, state_0, arrival_1, report_01),
        (step_12, departure_1, state_2, report_12),
    ):
        by_mode: dict[str, list[str]] = {}
        for cell in step.certificate.cells:
            by_mode.setdefault(cell.mode.value, []).append(cell.cell_id)
        deltas.append(VersionDelta(
            step.step_id,
            tuple(s for s in after.semantic_states if s not in before.semantic_states),
            tuple(s for s in before.semantic_states if s not in after.semantic_states),
            tuple(sorted(set(after.claim_tables) - set(before.claim_tables))),
            tuple(sorted(set(before.claim_tables) - set(after.claim_tables))),
            {mode: tuple(sorted(ids)) for mode, ids in sorted(by_mode.items())},
            tuple(sorted({e.edge_id for e in after.relation_edges}
                         - {e.edge_id for e in before.relation_edges})),
            tuple(sorted({e.edge_id for e in before.relation_edges}
                         - {e.edge_id for e in after.relation_edges})),
            report.payoff.analytic_movement,
        ))

    results = {name: CompositionCheckResult(name, not issues[name], tuple(issues[name]))
               for name in COMPOSITION_CHECKS}
    witnesses = tuple(w for name in COMPOSITION_CHECKS for w in issues[name])
    return CompositionReport(
        not witnesses, history.history_id,
        tuple(node.identity for node in history.nodes), component_reports, results,
        witnesses, fiber, lineage, tuple(composite_edges), composite_frontiers,
        authority, residue, movement, tuple(deltas),
    )


def compose_migrations(
    state_0: MigrationState,
    state_1: MigrationState,
    state_2: MigrationState,
    certificate_01: MigrationCertificate,
    certificate_12: MigrationCertificate,
    *,
    departure_state_1: MigrationState | None = None,
    grant: AdministrativeGrant | None = None,
    versions: Sequence[VersionIdentity] | None = None,
    actor_id: str = DEFAULT_ACTOR,
    history_id: str = "history:harm",
    declared_movement_total: Q | None = None,
) -> CompositionReport:
    """Compose two accountable migrations and derive the composition report."""
    history = build_history(
        state_0, state_1, state_2, certificate_01, certificate_12,
        departure_state_1=departure_state_1, grant=grant, versions=versions,
        actor_id=actor_id, history_id=history_id,
        declared_movement_total=declared_movement_total,
    )
    return verify_history(history)


def history_questions(report: CompositionReport) -> Mapping[str, object]:
    """The eight history questions, answered from derived report data only."""
    unresolved = tuple(sorted(
        record.record_id for record in report.residue.retained
        if record.kind == "intermediate-occurrence" and record.disposition == "live"
    ))
    return {
        "what changed between versions": report.deltas,
        "which old occurrence is responsible for a current occurrence": report.lineage.ancestry,
        "which challenges and burdens remain unresolved": unresolved,
        "why was each transition authorized": tuple(
            (step_id, component.authorization_binding_valid)
            for step_id, component in report.component_reports.items()
        ),
        "what practical authority survived": report.authority,
        "which conceptual distinctions still have live dependents": tuple(
            (record.record_id, record.live_dependents)
            for record in report.residue.retained if record.live_dependents
        ),
        "why an intermediate arena can or cannot be discarded": tuple(
            (record.record_id, record.reason)
            for record in report.residue.retained + report.residue.collectable
            if record.kind in ("comparison-arena", "intermediate-occurrence")
        ),
        "end-to-end movement ledger": report.movement,
    }


# --------------------------------------------------------------------------
# The exact two-step harm history
# --------------------------------------------------------------------------

MERGE_REPAIRS = (
    "naive",
    "authorized-loss",
    "suspended-lineage",
    "merged-suspension",
    "merged-live",
)

_OMEGA_2 = ("none", "bodily-harm", "nonphysical-harm")
_GAMMA_12 = ("none", "physical", "coercion", "frustration")
_PI_PLUS = {
    "none": "none",
    "physical": "bodily-harm",
    "coercion": "nonphysical-harm",
    "frustration": "nonphysical-harm",
}

MIGRATION_2_GRANT = AdministrativeGrant(
    "grant:migration-2", DEFAULT_ACTOR, ("auth:migration-2",), ("token:migration-2",), None,
    "the public learner admits one further consuming ontology-change token and the "
    "authorization record that the second migration certificate must bind to",
)


def _table_2(values: Mapping[str, int | Q]) -> tuple[Q, ...]:
    return tuple(Q(values[state]) for state in _OMEGA_2)


def _compiler_2() -> CompilerSpec:
    worlds = tuple(
        (Q(state != "none"), Q(state == "bodily-harm"), Q(a))
        for state in _OMEGA_2 for a in (0, 1)
    )
    return CompilerSpec(
        "compiler:merge", ("any-harm", "bodily-harm", "protect"), worlds,
        (
            CompilerEndorsement("endorsement:any-harm-bound-2", (Q(1), Q(0), Q(0)), Q(1, 2),
                                "k:any-harm++", "auth:migration-2"),
            CompilerEndorsement("endorsement:protect-bodily", (Q(0), Q(-1), Q(1)), Q(0),
                                "w:bodily-or-coercive-protect++", "auth:migration-2"),
        ),
        (Q(3, 5), Q(2, 5), Q(3, 4)), Q(1, 10),
    )


def build_merge_migration(
    repair: str = "suspended-lineage",
) -> tuple[MigrationState, MigrationState, MigrationCertificate]:
    """The v1 -> v2 span merging coercion and frustration under one repair policy."""
    if repair not in MERGE_REPAIRS:
        raise ValueError(repair)
    _, arrival_1, _ = build_harm_migration()
    departure_1 = apply_grant(arrival_1, MIGRATION_2_GRANT)

    merged_entitlement = repair in ("merged-suspension", "merged-live", "naive")
    keeps_frustration_branch = repair in ("suspended-lineage", "merged-suspension",
                                          "merged-live", "naive")
    entitlement_id = ("e:merged++" if repair in ("merged-live", "naive")
                      else "e:merged-suspended++" if repair == "merged-suspension"
                      else "e:bodily-or-coercive++")
    entitlement_status = (OccurrenceStatus.SUSPENDED if repair == "merged-suspension"
                          else OccurrenceStatus.LIVE)
    entitlement_authority = repair not in ("merged-suspension",)

    occurrences = [
        Occurrence("k:any-harm++", OccurrenceSort.COMMITMENT, OccurrenceStatus.LIVE,
                   "any-harm", ("k:any-harm", "d12:k"), True),
        Occurrence(entitlement_id, OccurrenceSort.ENTITLEMENT, entitlement_status,
                   "bodily-or-coercive", ("e:physical-or-coercion", "root:pc++"),
                   entitlement_authority),
        Occurrence("w:bodily-or-coercive-protect++", OccurrenceSort.WARRANT,
                   OccurrenceStatus.LIVE, "bodily-or-coercive->protect",
                   ("w:physical-or-coercion-protect",), True),
        Occurrence("p:any-harm++", OccurrenceSort.POSITION, OccurrenceStatus.LIVE,
                   "any-harm", ("p:any-harm",), True),
        Occurrence("o:preference-frustration++", OccurrenceSort.OTHER, OccurrenceStatus.LIVE,
                   "preference-frustration", ("o:preference-frustration",), False),
    ]
    if repair == "suspended-lineage":
        occurrences.append(Occurrence(
            "e:frustration-suspended++", OccurrenceSort.ENTITLEMENT,
            OccurrenceStatus.SUSPENDED, "preference-frustration",
            ("e:frustration-suspended", "root:f++", "c:frustration++"), False))
    if keeps_frustration_branch:
        occurrences.append(Occurrence(
            "w:frustration-suspended++", OccurrenceSort.WARRANT, OccurrenceStatus.SUSPENDED,
            "frustration->protect", ("w:frustration-suspended", "c:frustration++"), False))
        occurrences.append(Occurrence(
            "c:frustration++", OccurrenceSort.CHALLENGE, OccurrenceStatus.LIVE,
            provenance=("c:frustration+",)))
        occurrences.append(Occurrence(
            "b:justify-frustration++", OccurrenceSort.BURDEN, OccurrenceStatus.LIVE,
            provenance=("b:justify-frustration+",)))

    frustration_target = ("e:frustration-suspended++" if repair == "suspended-lineage"
                          else entitlement_id)
    edges = [
        RelationEdge("edge:pc-support++", RelationKind.JUSTIFICATION,
                     ("root:pc++",), (entitlement_id,)),
        RelationEdge("edge:w-premise-pc++", RelationKind.WARRANT_PREMISE,
                     ("bodily-or-coercive",), ("w:bodily-or-coercive-protect++",)),
        RelationEdge("edge:w-consequence-pc++", RelationKind.WARRANT_CONSEQUENCE,
                     ("w:bodily-or-coercive-protect++",), ("protect",)),
        RelationEdge("edge:authority++", RelationKind.AUTHORITY_CONSEQUENCE,
                     ("w:bodily-or-coercive-protect++",), ("protect",)),
        RelationEdge("edge:incompatibility++", RelationKind.INCOMPATIBILITY,
                     ("protect",), ("ignore",)),
        RelationEdge("edge:provenance++", RelationKind.PROVENANCE,
                     (entitlement_id,), ("w:bodily-or-coercive-protect++",)),
    ]
    if keeps_frustration_branch:
        edges.extend([
            RelationEdge("edge:f-support++", RelationKind.JUSTIFICATION,
                         ("root:f++",), (frustration_target,)),
            RelationEdge("edge:w-premise-f++", RelationKind.WARRANT_PREMISE,
                         ("legacy:preference-frustration",), ("w:frustration-suspended++",)),
            RelationEdge("edge:w-consequence-f++", RelationKind.WARRANT_CONSEQUENCE,
                         ("w:frustration-suspended++",), ("protect",)),
            RelationEdge("edge:burden++", RelationKind.BURDEN_SCOPE,
                         ("b:justify-frustration++",), ("edge:f-support++",)),
        ])

    routes = ((ChallengeRoute(
        "route:frustration++", ("c:frustration++", "b:justify-frustration++"),
        ("respond", "authorized-consuming-repair", "suspension", "explicit-terminal-failure"),
        "account:procedure", 1, "auth:migration-2"),) if keeps_frustration_branch else ())
    challenges = ((ChallengeSpec(
        "c:frustration++", (TypedTarget(TargetKind.ANCESTRY_EDGE, "edge:f-support++"),)),)
        if keeps_frustration_branch else ())

    state_2 = MigrationState(
        "state:harm-v3", "snapshot:harm-v3", _OMEGA_2,
        {
            "bodily-harm": _table_2({"none": 0, "bodily-harm": 1, "nonphysical-harm": 0}),
            "nonphysical-harm": _table_2({"none": 0, "bodily-harm": 0, "nonphysical-harm": 1}),
            "any-harm": _table_2({"none": 0, "bodily-harm": 1, "nonphysical-harm": 1}),
        },
        {"any-harm": _table_2({"none": 0, "bodily-harm": 1, "nonphysical-harm": 1})},
        tuple(occurrences),
        (EvidenceRoot("root:pc++", "auth:evidence-pc"),
         EvidenceRoot("root:f++", "auth:evidence-f")),
        tuple(edges), challenges,
        (Position("p:any-harm++", "any-harm", Q(-2)),), _compiler_2(),
        {"any-harm": Q(-2), "bodily-harm": Q(0), "protect": Q(0)},
        routes, ("account:procedure",), 1,
        ("auth:migration-2", "auth:evidence-pc", "auth:evidence-f"), (), NoninterferenceSpec(),
    )

    reconstructions = (
        SemanticReconstruction("reconstruct:physical", "physical-injury",
                               ("bodily-harm",), "identity"),
        SemanticReconstruction("reconstruct:any-harm", "any-harm", ("any-harm",), "identity"),
        SemanticReconstruction("reconstruct:coercion", "coercion", ("nonphysical-harm",),
                               "identity", "discrepancy:coercion-separation"),
        SemanticReconstruction("reconstruct:frustration", "preference-frustration",
                               ("nonphysical-harm",), "identity",
                               "discrepancy:frustration-separation"),
    )
    arena = ComparisonArena(_GAMMA_12, {state: state for state in _GAMMA_12},
                            dict(_PI_PLUS), _GAMMA_12, reconstructions)

    cells: list[DispositionCell] = [
        DispositionCell("d12:k", OccurrenceSort.COMMITMENT, ("k:any-harm",),
                        ("k:any-harm++",), DispositionMode.PRESERVE, "reconstruct:any-harm"),
        DispositionCell("d12:p", OccurrenceSort.POSITION, ("p:any-harm",),
                        ("p:any-harm++",), DispositionMode.PRESERVE, "reconstruct:any-harm"),
        DispositionCell("d12:o", OccurrenceSort.OTHER, ("o:preference-frustration",),
                        ("o:preference-frustration++",), DispositionMode.PRESERVE),
    ]
    suspensions: list[SuspensionEntry] = []
    losses: list[LossEntry] = []
    terminal_dispositions: list[TerminalDisposition] = []
    edge_transports: list[EdgeTransport] = [
        EdgeTransport("edge:pc-support+", ("edge:pc-support++",)),
        EdgeTransport("edge:w-premise-pc+", ("edge:w-premise-pc++",)),
        EdgeTransport("edge:w-consequence-pc+", ("edge:w-consequence-pc++",)),
        EdgeTransport("edge:authority+", ("edge:authority++",)),
        EdgeTransport("edge:incompatibility+", ("edge:incompatibility++",)),
        EdgeTransport("edge:provenance+", ("edge:provenance++",)),
    ]

    if merged_entitlement:
        cells.append(DispositionCell(
            "d12:e-merge", OccurrenceSort.ENTITLEMENT,
            ("e:physical-or-coercion", "e:frustration-suspended"), (entitlement_id,),
            DispositionMode.MERGE, "reconstruct:frustration"))
        cells.append(DispositionCell(
            "d12:w-pc", OccurrenceSort.WARRANT, ("w:physical-or-coercion-protect",),
            ("w:bodily-or-coercive-protect++",), DispositionMode.PRESERVE,
            "reconstruct:coercion"))
        if repair == "merged-suspension":
            suspensions.append(SuspensionEntry(
                "suspension:merged-entitlement-2", "d12:e-merge", (entitlement_id,),
                ("route:frustration++",), "auth:migration-2", True, False))
        else:
            losses.append(LossEntry(
                "loss:frustration-separation", "semantic", "d12:e-merge",
                "the state-level separation of preference frustration from coercion",
                "auth:migration-2", True,
                "the merged entitlement can no longer be challenged on the frustration ground alone"))
    else:
        cells.append(DispositionCell(
            "d12:e-pc", OccurrenceSort.ENTITLEMENT, ("e:physical-or-coercion",),
            ("e:bodily-or-coercive++",), DispositionMode.PRESERVE, "reconstruct:coercion"))
        cells.append(DispositionCell(
            "d12:w-pc", OccurrenceSort.WARRANT, ("w:physical-or-coercion-protect",),
            ("w:bodily-or-coercive-protect++",), DispositionMode.PRESERVE))
        if repair == "suspended-lineage":
            cells.append(DispositionCell(
                "d12:e-f", OccurrenceSort.ENTITLEMENT, ("e:frustration-suspended",),
                ("e:frustration-suspended++",), DispositionMode.SUSPEND,
                "reconstruct:frustration"))
            suspensions.append(SuspensionEntry(
                "suspension:frustration-entitlement-2", "d12:e-f",
                ("e:frustration-suspended++",), ("route:frustration++",),
                "auth:migration-2", True, False))
        else:  # authorized-loss
            cells.append(DispositionCell(
                "d12:e-f", OccurrenceSort.ENTITLEMENT, ("e:frustration-suspended",), (),
                DispositionMode.RETRACT, "reconstruct:frustration", "auth:migration-2"))
            terminal_dispositions.append(TerminalDisposition(
                "terminal:frustration-entitlement", "d12:e-f", "retraction",
                "witness:frustration-response", "auth:migration-2", True))
            losses.append(LossEntry(
                "loss:frustration-separation", "semantic", "d12:e-f",
                "the state-level separation of preference frustration from coercion",
                "auth:migration-2", True,
                "the retracted entitlement carries no further practical consequence"))

    if merged_entitlement or repair == "suspended-lineage":
        losses.append(LossEntry(
            "loss:coercion-separation", "semantic",
            "d12:w-pc" if merged_entitlement else "d12:e-pc",
            "the state-level separation of coercion from preference frustration",
            "auth:migration-2", True,
            "no new warrant premise can name coercion to the exclusion of frustration"))
    else:
        losses.append(LossEntry(
            "loss:coercion-separation", "semantic", "d12:e-pc",
            "the state-level separation of coercion from preference frustration",
            "auth:migration-2", True,
            "no new warrant premise can name coercion to the exclusion of frustration"))

    if keeps_frustration_branch:
        cells.append(DispositionCell(
            "d12:w-f", OccurrenceSort.WARRANT, ("w:frustration-suspended",),
            ("w:frustration-suspended++",), DispositionMode.SUSPEND))
        cells.append(DispositionCell(
            "d12:c", OccurrenceSort.CHALLENGE, ("c:frustration+",), ("c:frustration++",),
            DispositionMode.PRESERVE))
        cells.append(DispositionCell(
            "d12:b", OccurrenceSort.BURDEN, ("b:justify-frustration+",),
            ("b:justify-frustration++",), DispositionMode.PRESERVE))
        suspensions.append(SuspensionEntry(
            "suspension:frustration-force-2", "d12:w-f", ("w:frustration-suspended++",),
            ("route:frustration++",), "auth:migration-2", True, False))
        edge_transports.extend([
            EdgeTransport("edge:f-support+", ("edge:f-support++",)),
            EdgeTransport("edge:w-premise-f+", ("edge:w-premise-f++",)),
            EdgeTransport("edge:w-consequence-f+", ("edge:w-consequence-f++",)),
            EdgeTransport("edge:burden+", ("edge:burden++",)),
        ])
    else:
        cells.append(DispositionCell(
            "d12:w-f", OccurrenceSort.WARRANT, ("w:frustration-suspended",), (),
            DispositionMode.RETRACT, None, "auth:migration-2"))
        cells.append(DispositionCell(
            "d12:c", OccurrenceSort.CHALLENGE, ("c:frustration+",), (),
            DispositionMode.DISCHARGE, None, "auth:migration-2"))
        cells.append(DispositionCell(
            "d12:b", OccurrenceSort.BURDEN, ("b:justify-frustration+",), (),
            DispositionMode.DISCHARGE, None, "auth:migration-2"))
        terminal_dispositions.extend([
            TerminalDisposition("terminal:frustration-force", "d12:w-f", "retraction",
                                "witness:frustration-response", "auth:migration-2", True),
            TerminalDisposition("terminal:frustration-challenge", "d12:c", "discharge",
                                "witness:frustration-response", "auth:migration-2", True),
            TerminalDisposition("terminal:frustration-burden", "d12:b", "discharge",
                                "witness:frustration-response", "auth:migration-2", True),
        ])
        for old_edge, suffix, content in (
            ("edge:f-support+", "ancestry", "the frustration justification edge"),
            ("edge:w-premise-f+", "premise", "the frustration warrant premise"),
            ("edge:w-consequence-f+", "consequence", "the frustration warrant consequence"),
            ("edge:burden+", "burden", "the frustration burden scope edge"),
        ):
            loss_id = f"loss:frustration-{suffix}"
            losses.append(LossEntry(
                loss_id, "relation", old_edge, content, "auth:migration-2", False,
                "the answered challenge removes this edge from the active graph"))
            edge_transports.append(EdgeTransport(old_edge, (), loss_id))

    discrepancies = (
        DiscrepancyEntry("discrepancy:coercion-separation", "reconstruct:coercion",
                         (Q(0), Q(0), Q(0), Q(-1)), "auth:migration-2"),
        DiscrepancyEntry("discrepancy:frustration-separation", "reconstruct:frustration",
                         (Q(0), Q(0), Q(-1), Q(0)), "auth:migration-2"),
    )
    if repair == "naive":
        discrepancies = ()
        losses = []

    authorization = AuthorizationRecord(
        "auth:migration-2", "proposal:harm-merge", "certificate:harm-merge-v1",
        "snapshot:shadow-harm-v2", "token:migration-2",
        tuple(sorted({loss.loss_id for loss in losses})),
        tuple(sorted({entry.suspension_id for entry in suspensions})), (), (),
    )
    recheck = EndpointRecheck("recheck:endpoint-harm-v3", "certificate:harm-merge-v1",
                              "state:harm-v3", "compiler:merge")
    activation = ActivationRecord(
        "proposal:harm-merge", "certificate:harm-merge-v1",
        "snapshot:shadow-harm-v2", "snapshot:shadow-harm-v2",
        "state:shadow-harm-v2", "state:shadow-harm-v2", "state:harm-v3",
        "recheck:endpoint-harm-v3", "state:harm-v3",
    )
    certificate = MigrationCertificate(
        "certificate:harm-merge-v1", "proposal:harm-merge", "snapshot:shadow-harm-v2",
        "state:harm-v3", arena, tuple(cells), tuple(edge_transports),
        (("any-harm", "any-harm"), ("physical-or-coercion", "bodily-harm"),
         ("protect", "protect")),
        (("physical-or-coercion", ("bodily-or-coercive",)),
         ("preference-frustration", ("legacy:preference-frustration",)),
         ("protect", ("protect",)), ("ignore", ("ignore",)),
         ("root:pc+", ("root:pc++",)), ("root:f+", ("root:f++",))),
        discrepancies, tuple(terminal_dispositions), tuple(suspensions), tuple(losses),
        (), (), authorization, recheck, activation,
    )
    return departure_1, state_2, certificate


def build_two_step_history(repair: str = "suspended-lineage",
                           mutation: str | None = None) -> MigrationHistory:
    """The exact two-step harm history under one repair policy and one mutation."""
    state_0, arrival_1, certificate_01 = build_harm_migration()
    departure_1, state_2, certificate_12 = build_merge_migration(repair)
    grant = MIGRATION_2_GRANT
    declared_total: Q | None = None

    if mutation == "truncated-arena":
        support = _GAMMA_12[:3]
        arena = replace(certificate_12.arena, states=support, covered_support=support,
                        old_projection={s: s for s in support},
                        new_projection={s: _PI_PLUS[s] for s in support})
        certificate_12 = replace(
            certificate_12, arena=arena,
            discrepancies=(DiscrepancyEntry(
                "discrepancy:frustration-separation", "reconstruct:frustration",
                (Q(0), Q(0), Q(-1)), "auth:migration-2"),))
    elif mutation == "relabelled-intermediate":
        departure_1 = replace(departure_1, state_id="state:shadow-harm-v2-relabelled")
        certificate_12 = replace(certificate_12, activation=replace(
            certificate_12.activation,
            preactivation_active_state_id="state:shadow-harm-v2-relabelled",
            preactivation_force_state_id="state:shadow-harm-v2-relabelled"))
    elif mutation == "smuggled-edit":
        departure_1 = replace(
            departure_1, force_holdings={**departure_1.force_holdings, "protect": Q(3)})
    elif mutation == "partial-target-cover":
        extra = RelationEdge("edge:f-support-b++", RelationKind.JUSTIFICATION,
                             ("root:f++",), ("e:frustration-suspended++",))
        state_2 = replace(state_2, relation_edges=state_2.relation_edges + (extra,))
        certificate_12 = replace(certificate_12, edge_transports=tuple(
            EdgeTransport(t.old_edge_id, ("edge:f-support++", "edge:f-support-b++"), t.outcome_ref)
            if t.old_edge_id == "edge:f-support+" else t
            for t in certificate_12.edge_transports))
    elif mutation == "token-reuse":
        grant = replace(MIGRATION_2_GRANT, added_migration_tokens=("token:migration-1",))
        departure_1 = apply_grant(arrival_1, grant)
        certificate_12 = replace(certificate_12, authorization=replace(
            certificate_12.authorization, migration_token_id="token:migration-1"))
    elif mutation == "tampered-discrepancy":
        certificate_12 = replace(certificate_12, discrepancies=tuple(
            replace(entry, values=(Q(0), Q(0), Q(0), Q(0)))
            for entry in certificate_12.discrepancies))
    elif mutation == "claimed-movement":
        declared_total = Q(1, 6)
    elif mutation is not None:
        raise ValueError(mutation)

    return build_history(
        state_0, arrival_1, state_2, certificate_01, certificate_12,
        departure_state_1=departure_1, grant=grant,
        history_id=f"history:harm-{repair}",
        declared_movement_total=declared_total,
    )


def exact_composition_trace(repair: str = "suspended-lineage") -> Mapping[str, object]:
    history = build_two_step_history(repair)
    return {"history": history, "report": verify_history(history)}


# --------------------------------------------------------------------------
# Composite migration construction
#
# `verify_history` decides whether a *pair* of certificates is jointly
# admissible.  It never builds the one-step object `M_02 : V_0 -> V_2`.  This
# section does, so that the frozen verifier can be asked directly whether a
# certified composite exists — and so that the gap between "the composite
# verifies" and "the history is admissible" becomes exhibitable.
# --------------------------------------------------------------------------

COMPOSITE_STYLES = ("naive", "blind", "repaired")

_TERMINAL_MODES = (DispositionMode.RETRACT, DispositionMode.DISCHARGE, DispositionMode.LOSS)


@dataclass(frozen=True)
class LineageComponent:
    """One connected component of the tripartite lineage graph.

    A component is the unit of composite disposition: it collects every
    occurrence of all three versions that any composite path touches, so shared
    ancestry is consumed once however many intermediate paths cross it.
    """

    component_id: str
    sort: OccurrenceSort
    start: tuple[str, ...]
    intermediate: tuple[str, ...]
    end: tuple[str, ...]
    paths: tuple[tuple[str, str, str], ...]


@dataclass(frozen=True)
class CompositeObstruction:
    """Why no certified composite exists, in the shape the failure has."""

    kind: str
    code: str
    start_occurrence: str
    intermediate_paths: tuple[tuple[str, ...], ...]
    merged_descendant: str
    resource: str
    detail: str


@dataclass(frozen=True)
class LegacyDistinction:
    """Comparison-arena states the endpoint ontology cannot tell apart."""

    group_id: str
    arena_states: tuple[str, ...]
    endpoint_state: str
    live_dependents: tuple[str, ...]


@dataclass(frozen=True)
class CompositeMigration:
    style: str
    certificate: MigrationCertificate | None
    components: tuple[LineageComponent, ...]
    arena_states: tuple[str, ...]
    legacy_distinctions: tuple[LegacyDistinction, ...]
    obstructions: tuple[CompositeObstruction, ...]


def _pair_id(left: str, right: str) -> str:
    return f"{left}|{right}"


def _lineage_components(
    state_0: MigrationState, state_1: MigrationState, state_2: MigrationState,
    certificate_01: MigrationCertificate, certificate_12: MigrationCertificate,
) -> tuple[LineageComponent, ...]:
    """Connected components of the start/intermediate/end lineage graph."""
    parent: dict[str, str] = {}

    def find(node: str) -> str:
        parent.setdefault(node, node)
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    def union(left: str, right: str) -> None:
        a, b = find(left), find(right)
        if a != b:
            parent[a] = b

    tags: dict[str, tuple[int, str]] = {}
    for index, state in ((0, state_0), (1, state_1), (2, state_2)):
        for occurrence in state.occurrences:
            if _active(occurrence):
                node = f"{index}:{occurrence.occurrence_id}"
                tags[node] = (index, occurrence.occurrence_id)
                find(node)
    for offset, certificate in ((0, certificate_01), (1, certificate_12)):
        for cell in certificate.cells:
            members = ([f"{offset}:{i}" for i in cell.inputs]
                       + [f"{offset + 1}:{o}" for o in cell.outputs])
            members = [node for node in members if node in tags]
            for node in members[1:]:
                union(members[0], node)
    sorts: dict[str, OccurrenceSort] = {}
    for certificate in (certificate_01, certificate_12):
        for cell in certificate.cells:
            for identifier in cell.inputs + cell.outputs:
                sorts[identifier] = cell.sort
    grouped: dict[str, list[str]] = {}
    for node in sorted(tags):
        grouped.setdefault(find(node), []).append(node)
    cells_01, cells_12 = _cell_by_input(certificate_01), _cell_by_input(certificate_12)
    components: list[LineageComponent] = []
    for index, (_, nodes) in enumerate(sorted(grouped.items())):
        levels: dict[int, list[str]] = {0: [], 1: [], 2: []}
        for node in nodes:
            level, identifier = tags[node]
            levels[level].append(identifier)
        sort = next((sorts[i] for level in levels.values() for i in level if i in sorts),
                    OccurrenceSort.OTHER)
        paths = tuple(
            (start, middle, end)
            for start in sorted(levels[0])
            for middle in (cells_01[start].outputs if start in cells_01 else ())
            for end in (cells_12[middle].outputs if middle in cells_12 else ())
        )
        components.append(LineageComponent(
            f"c02:{index}", sort, tuple(sorted(levels[0])), tuple(sorted(levels[1])),
            tuple(sorted(levels[2])), paths))
    return tuple(components)


def _composite_mode(component: LineageComponent, state_2: MigrationState,
                    certificate_12: MigrationCertificate) -> DispositionMode | None:
    outputs = _index(state_2.occurrences, "occurrence_id")
    if not component.start:
        return DispositionMode.INTRODUCE
    if not component.end:
        kinds = {item.kind for item in certificate_12.terminal_dispositions
                 if item.source_cell_id in {c.cell_id for c in certificate_12.cells
                                            if set(c.inputs) & set(component.intermediate)}}
        if "discharge" in kinds:
            return DispositionMode.DISCHARGE
        if kinds:
            return DispositionMode.RETRACT
        return DispositionMode.LOSS
    suspended = all(outputs[o].status == OccurrenceStatus.SUSPENDED
                    for o in component.end if o in outputs)
    if len(component.start) == 1 and len(component.end) == 1:
        return DispositionMode.SUSPEND if suspended else DispositionMode.PRESERVE
    if len(component.start) == 1:
        return DispositionMode.SUSPEND if suspended else DispositionMode.REFINE
    if len(component.end) == 1:
        return DispositionMode.MERGE
    return None


def compose_certificates(history: MigrationHistory,
                         style: str = "repaired") -> CompositeMigration:
    """Build `M_02` from `M_01` and `M_12` under one composition policy.

    `repaired` composes lineage by connected component, retains the fiber-product
    arena with its legacy distinctions, and carries forward every disposition
    record.  `blind` composes cells pairwise, so a split that later merges
    consumes its common ancestor twice.  `naive` keeps only the endpoint
    semantic correspondence and drops the relational, challenge, and disposition
    layers entirely.
    """
    if style not in COMPOSITE_STYLES:
        raise ValueError(style)
    node_0, node_1, node_2 = history.nodes
    step_01, step_12 = history.steps
    certificate_01, certificate_12 = step_01.certificate, step_12.certificate
    state_0, state_1, state_2 = (node_0.departure_state, node_1.arrival_state,
                                 node_2.arrival_state)
    assert state_0 is not None and state_1 is not None and state_2 is not None
    arena_01, arena_12 = certificate_01.arena, certificate_12.arena
    obstructions: list[CompositeObstruction] = []
    occ_2 = _index(state_2.occurrences, "occurrence_id")

    components = _lineage_components(
        state_0, state_1, state_2, certificate_01, certificate_12)

    # The comparison arena is the fiber product; its states are pairs, so a
    # distinction the endpoint ontology drops survives as two arena states.
    pairs = [(left, right) for left in arena_01.states for right in arena_12.states
             if arena_01.new_projection.get(left) is not None
             and arena_01.new_projection.get(left) == arena_12.old_projection.get(right)]
    states = tuple(_pair_id(left, right) for left, right in pairs)
    old_projection = {_pair_id(l, r): arena_01.old_projection[l] for l, r in pairs}
    new_projection = {_pair_id(l, r): arena_12.new_projection[r] for l, r in pairs}
    covered = tuple(_pair_id(l, r) for l, r in pairs
                    if l in arena_01.covered_support and r in arena_12.covered_support)
    second_by_claim = {r.old_claim_ref: r for r in arena_12.reconstructions}
    reconstructions: list[SemanticReconstruction] = []
    for first in arena_01.reconstructions:
        refs: list[str] = []
        for ref in first.new_claim_refs:
            second = second_by_claim.get(ref)
            if second is None:
                refs.append(ref)
                continue
            if second.operation != "identity":
                obstructions.append(CompositeObstruction(
                    "noncommuting-transport", "composite.noncommuting_reconstruction",
                    first.old_claim_ref, ((ref,),), "",
                    "semantic-reconstruction",
                    "a nonidentity second-step reconstruction does not compose into one operation"))
            refs.extend(r for r in second.new_claim_refs if r not in refs)
        reconstructions.append(SemanticReconstruction(
            f"reconstruct02:{first.old_claim_ref}", first.old_claim_ref,
            tuple(refs), first.operation))
    grouped: dict[str, list[str]] = {}
    for identifier in covered:
        grouped.setdefault(new_projection[identifier], []).append(identifier)
    legacy = tuple(
        LegacyDistinction(f"legacy02:{endpoint}", tuple(members), endpoint, ())
        for endpoint, members in sorted(grouped.items()) if len(members) > 1
    )

    # Composite disposition cells.
    cells: list[DispositionCell] = []
    cell_of_start: dict[str, str] = {}
    reconstruction_of_cell: dict[str, str | None] = {}
    for component in components:
        mode = _composite_mode(component, state_2, certificate_12)
        if mode is None:
            obstructions.append(CompositeObstruction(
                "inexpressible-hypercell", "composite.inexpressible_hypercell",
                component.start[0] if component.start else "",
                tuple((path[1],) for path in component.paths),
                component.end[0] if component.end else "", "disposition-cell",
                "a composite component with several inputs and several outputs has no legal mode"))
            continue
        branch_terminals = tuple(
            item.disposition_id for item in certificate_12.terminal_dispositions
            for cell in certificate_12.cells
            if cell.cell_id == item.source_cell_id
            and set(cell.inputs) & set(component.intermediate))
        if branch_terminals and component.end and mode not in _TERMINAL_MODES:
            obstructions.append(CompositeObstruction(
                "branch-disposition", "composite.branch_disposition_unexpressible",
                component.start[0] if component.start else "",
                tuple((path[1],) for path in component.paths),
                component.end[0], "terminal-disposition",
                "one branch of a split is terminally disposed while another survives, so the "
                "composite cell is not terminal and cannot carry the witness"))
        reference = next(
            (cell.reconstruction_ref for cell in certificate_01.cells
             if set(cell.inputs) & set(component.start) and cell.reconstruction_ref), None)
        composite_reference = (
            f"reconstruct02:{reference}" if reference and any(
                r.old_claim_ref == reference for r in arena_01.reconstructions) else None)
        if composite_reference is None and reference:
            composite_reference = next(
                (r.reconstruction_id for r in reconstructions
                 if r.reconstruction_id.endswith(reference)), None)
        authorization_ref = ("auth:migration" if mode in _TERMINAL_MODES else None)
        cells.append(DispositionCell(
            component.component_id, component.sort, component.start, component.end,
            mode, composite_reference, authorization_ref))
        reconstruction_of_cell[component.component_id] = composite_reference
        for start in component.start:
            cell_of_start[start] = component.component_id

    if style == "blind":
        # One composite cell per (first-step cell, second-step cell) pair.  A
        # split whose branches later merge therefore consumes its common
        # ancestor once per branch.
        cells_01, cells_12 = _cell_by_input(certificate_01), _cell_by_input(certificate_12)
        pairwise: dict[tuple[str, str], tuple[list[str], list[str], list[str]]] = {}
        for component in components:
            for start, middle, end in component.paths:
                key = (cells_01[start].cell_id, cells_12[middle].cell_id)
                entry = pairwise.setdefault(key, ([], [], []))
                for bucket, value in zip(entry, (start, middle, end)):
                    if value not in bucket:
                        bucket.append(value)
        cells = []
        consumed: dict[str, list[str]] = {}
        for index, (key, (starts, middles, ends)) in enumerate(sorted(pairwise.items())):
            identifier = f"c02b:{index}"
            sort = next(c.sort for c in certificate_01.cells if c.cell_id == key[0])
            cells.append(DispositionCell(
                identifier, sort, tuple(starts), tuple(ends),
                DispositionMode.PRESERVE if len(starts) == len(ends) == 1
                else DispositionMode.REFINE if len(starts) == 1
                else DispositionMode.MERGE, None, None))
            for start in starts:
                consumed.setdefault(start, []).append(identifier)
        for start, owners in sorted(consumed.items()):
            if len(owners) > 1:
                component = next(c for c in components if start in c.start)
                obstructions.append(CompositeObstruction(
                    "lineage-collision", "composite.lineage_collision", start,
                    tuple((path[1],) for path in component.paths if path[0] == start),
                    component.end[0] if component.end else "",
                    "consuming-disposition",
                    "one start occurrence is consumed by several composite cells, so its "
                    "inherited authority and its single answer are counted once per branch"))

    # Relational, coordinate, and node transport compose by image.
    transports_12 = _index(certificate_12.edge_transports, "old_edge_id")
    node_map_12 = dict(certificate_12.semantic_node_transports)
    root_map_01 = {root.transported_from: root.root_id
                   for root in state_1.evidence_roots if root.transported_from}
    edge_transports: list[EdgeTransport] = []
    outcome_pool: dict[str, str] = {}
    for first in certificate_01.edge_transports:
        images: list[str] = []
        outcome = first.outcome_ref
        for middle in first.new_edge_ids:
            second = transports_12.get(middle)
            if second is None:
                continue
            images.extend(second.new_edge_ids)
            outcome = second.outcome_ref or outcome
        edge_transports.append(EdgeTransport(first.old_edge_id, tuple(images), outcome))
        if not images and outcome:
            outcome_pool[first.old_edge_id] = outcome
    node_transports: list[tuple[str, tuple[str, ...]]] = []
    for node, images in certificate_01.semantic_node_transports:
        composed: list[str] = []
        for middle in images:
            composed.extend(node_map_12.get(middle, (middle,)))
        node_transports.append((node, tuple(composed)))
    for start_root, middle_root in sorted(root_map_01.items()):
        node_transports.append((start_root, tuple(node_map_12.get(middle_root, (middle_root,)))))
    coordinate_map_12 = dict(certificate_12.coordinate_transports)
    coordinate_transports = tuple(
        (start, coordinate_map_12[middle])
        for start, middle in certificate_01.coordinate_transports
        if middle in coordinate_map_12
    )

    # Dispositions carry forward, re-sourced onto the composite cells.
    edge_preimage = {
        middle: first.old_edge_id
        for first in certificate_01.edge_transports for middle in first.new_edge_ids
    }
    start_edges = {edge.edge_id for edge in state_0.relation_edges}

    def owning_cell(reference: str) -> str | None:
        """Re-source a disposition record onto the composite it now belongs to.

        A record may name a cell of either step, or an intermediate relation
        edge; an edge is carried back to its start-version preimage, which is
        the only name the composite certificate can legitimately use.
        """
        for cells_of, level in ((certificate_12.cells, "intermediate"),
                                (certificate_01.cells, "start")):
            for cell in cells_of:
                if cell.cell_id != reference:
                    continue
                for component in components:
                    if set(cell.inputs) & set(getattr(component, level)):
                        return component.component_id
        if reference in start_edges:
            return reference
        return edge_preimage.get(reference)

    suspensions: list[SuspensionEntry] = []
    for entry in certificate_12.suspensions:
        owner = owning_cell(entry.source_ref)
        if owner is None:
            continue
        suspensions.append(replace(entry, source_ref=owner,
                                   authorization_ref="auth:migration"))
    losses: list[LossEntry] = []
    for certificate in (certificate_01, certificate_12):
        for loss in certificate.losses:
            owner = owning_cell(loss.source_ref)
            losses.append(replace(loss, source_ref=owner or loss.source_ref,
                                  authorization_ref="auth:migration"))
    terminal_dispositions = tuple(
        replace(item, source_cell_id=owning_cell(item.source_cell_id) or item.source_cell_id,
                authorization_ref="auth:migration")
        for item in certificate_12.terminal_dispositions
    )
    discrepancies: list[DiscrepancyEntry] = []
    for reconstruction in reconstructions:
        old_table = state_0.claim_tables.get(reconstruction.old_claim_ref)
        new_tables = [state_2.claim_tables.get(ref) for ref in reconstruction.new_claim_refs]
        if old_table is None or any(table is None for table in new_tables):
            continue
        old_pull = _pullback_states(old_table, state_0.semantic_states, old_projection, covered)
        pulled = [_pullback_states(table, state_2.semantic_states, new_projection, covered)
                  for table in new_tables if table is not None]
        combined = _combine_tables(reconstruction.operation, pulled)
        if old_pull is None or combined is None:
            continue
        delta = tuple(a - b for a, b in zip(old_pull, combined))
        if any(delta):
            identifier = f"discrepancy02:{reconstruction.old_claim_ref}"
            discrepancies.append(DiscrepancyEntry(
                identifier, reconstruction.reconstruction_id, delta, "auth:migration"))
            reconstructions[reconstructions.index(reconstruction)] = replace(
                reconstruction, discrepancy_ref=identifier)

    arena = ComparisonArena(states, old_projection, new_projection, covered,
                            tuple(reconstructions))
    if style == "naive":
        # Endpoint semantic correspondence only: the relational, challenge, and
        # disposition layers are not derivable from it and are simply absent.
        endpoint_states = state_2.semantic_states
        arena = ComparisonArena(
            endpoint_states,
            {s: state_0.semantic_states[0] if s == "none" else state_0.semantic_states[1]
             for s in endpoint_states},
            {s: s for s in endpoint_states}, endpoint_states,
            tuple(replace(r, discrepancy_ref=None) for r in reconstructions))
        edge_transports, suspensions, losses = [], [], []
        terminal_dispositions, discrepancies = (), []
        node_transports = []

    authorization = AuthorizationRecord(
        "auth:migration", "proposal:harm-composite", "certificate:harm-composite",
        state_0.snapshot_id, "token:migration-1",
        tuple(sorted({loss.loss_id for loss in losses})),
        tuple(sorted({entry.suspension_id for entry in suspensions})), (), (),
    )
    recheck = EndpointRecheck("recheck:composite", "certificate:harm-composite",
                              state_2.state_id, state_2.compiler.compiler_id)
    activation = ActivationRecord(
        "proposal:harm-composite", "certificate:harm-composite",
        state_0.snapshot_id, state_0.snapshot_id, state_0.state_id, state_0.state_id,
        state_2.state_id, "recheck:composite", state_2.state_id,
    )
    certificate = MigrationCertificate(
        "certificate:harm-composite", "proposal:harm-composite", state_0.snapshot_id,
        state_2.state_id, arena, tuple(cells), tuple(edge_transports),
        coordinate_transports, tuple(node_transports), tuple(discrepancies),
        tuple(terminal_dispositions), tuple(suspensions), tuple(losses), (), (),
        authorization, recheck, activation,
    )
    live_targets = {target.target_id for spec in state_2.challenges for target in spec.targets}
    legacy = tuple(
        replace(item, live_dependents=tuple(sorted(
            identifier for identifier in live_targets
            if identifier in {e.edge_id for e in state_2.relation_edges})))
        if len(item.arena_states) > 1 else item
        for item in legacy
    )
    return CompositeMigration(style, certificate, components, states, legacy,
                              tuple(obstructions))


def _pullback_states(table: Sequence[Q], native: Sequence[str],
                     projection: Mapping[str, str],
                     support: Sequence[str]) -> tuple[Q, ...] | None:
    values = dict(zip(native, table))
    try:
        return tuple(Q(values[projection[state]]) for state in support)
    except KeyError:
        return None


def _combine_tables(operation: str,
                    tables: Sequence[Sequence[Q]]) -> tuple[Q, ...] | None:
    if not tables or any(table is None for table in tables):
        return None
    if operation == "identity" and len(tables) == 1:
        return tuple(tables[0])
    if operation == "or":
        return tuple(max(values) for values in zip(*tables))
    if operation == "sum":
        return tuple(sum(values, Q(0)) for values in zip(*tables))
    return None


# --------------------------------------------------------------------------
# Legacy discharge and composite movement
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class DischargeVerdict:
    """When a retained arena distinction may be collected."""

    group_id: str
    arena_states: tuple[str, ...]
    dischargeable: bool
    live_dependents: tuple[str, ...]
    payoff_constant_on_fibers: bool
    discrepancy_constant_on_fibers: bool
    reasons: tuple[str, ...]


def legacy_discharge_report(
    composite: CompositeMigration, state_0: MigrationState, state_2: MigrationState,
    *, resolved: Sequence[str] = (),
) -> tuple[DischargeVerdict, ...]:
    """Decide, per retained distinction, whether it is live, historical, or scaffolding.

    A distinction is dischargeable only when no live challenge or burden still
    depends on it *and* collapsing it changes no payoff meaning and no recorded
    discrepancy.  Provenance records are never collected; only the arena states
    that made a live claim statable are.
    """
    certificate = composite.certificate
    assert certificate is not None
    arena = certificate.arena
    live = tuple(sorted(
        occurrence.occurrence_id for occurrence in state_2.occurrences
        if occurrence.sort in (OccurrenceSort.CHALLENGE, OccurrenceSort.BURDEN)
        and occurrence.status != OccurrenceStatus.TERMINAL
        and occurrence.occurrence_id not in resolved
    ))
    verdicts: list[DischargeVerdict] = []
    for group in composite.legacy_distinctions:
        members = set(group.arena_states)
        quotient = {state: (group.group_id if state in members else state)
                    for state in arena.covered_support}
        payoff_constant = True
        for position in state_0.positions:
            if position.holdings == 0:
                continue
            table = state_0.payoff_tables.get(position.payoff_ref)
            if table is None:
                continue
            values = dict(zip(state_0.semantic_states, table))
            pulled = {state: values[arena.old_projection[state]]
                      for state in arena.covered_support}
            payoff_constant &= constant_on_fibers(arena.covered_support, quotient, pulled)
        discrepancy_constant = True
        for entry in certificate.discrepancies:
            pulled = dict(zip(arena.covered_support, entry.values))
            discrepancy_constant &= constant_on_fibers(
                arena.covered_support, quotient, pulled)
        reasons: list[str] = []
        if live:
            reasons.append("a live challenge or burden still depends on the distinction")
        if not payoff_constant:
            reasons.append("an outstanding payoff separates the states being collapsed")
        if not discrepancy_constant:
            reasons.append("a recorded discrepancy separates the states being collapsed")
        if not reasons:
            reasons.append("no live dependent and no live meaning separates the states")
        verdicts.append(DischargeVerdict(
            group.group_id, group.arena_states, not live and payoff_constant
            and discrepancy_constant, live, payoff_constant, discrepancy_constant,
            tuple(reasons)))
    return tuple(verdicts)


def discharge_legacy_distinction(composite: CompositeMigration,
                                 group_id: str) -> MigrationCertificate:
    """Collapse one retained distinction and return the reduced certificate."""
    certificate = composite.certificate
    assert certificate is not None
    group = next(item for item in composite.legacy_distinctions if item.group_id == group_id)
    keep = group.arena_states[0]
    dropped = set(group.arena_states[1:])
    arena = certificate.arena
    states = tuple(state for state in arena.states if state not in dropped)
    support = tuple(state for state in arena.covered_support if state not in dropped)
    index = [i for i, state in enumerate(arena.covered_support) if state not in dropped]
    return replace(
        certificate,
        arena=replace(
            arena, states=states, covered_support=support,
            old_projection={k: v for k, v in arena.old_projection.items() if k not in dropped},
            new_projection={k: v for k, v in arena.new_projection.items() if k not in dropped},
        ),
        discrepancies=tuple(
            replace(entry, values=tuple(entry.values[i] for i in index))
            for entry in certificate.discrepancies),
        legacy_retentions=tuple(
            replace(entry, carrier_states=support,
                    retained_payoff=tuple(entry.retained_payoff[i] for i in index))
            for entry in certificate.legacy_retentions),
    )


def movement_composition(holdings: Q, first: Q, middle: Q, last: Q) -> tuple[Q, Q, Q]:
    """Step, step, and composite reference movement for one payoff coordinate."""
    charge = lambda before, after: max(Q(0), -Q(holdings) * (Q(before) - Q(after)))
    return charge(first, middle), charge(middle, last), charge(first, last)


def reference_reversal_witness() -> tuple[Q, Q, Q, Q, Q, Q]:
    """A history whose composite under-reports the movement its steps charged."""
    holdings, first, middle, last = Q(-2), Q(3, 5), Q(3, 4), Q(3, 5)
    step_one, step_two, composite = movement_composition(holdings, first, middle, last)
    return holdings, first, middle, last, step_one + step_two, composite


@dataclass(frozen=True)
class AuthorityProvenance:
    """Authority-bearing occurrences of one component, indexed by version.

    Grants are step-specific: a grant issued by `M_{t,t+1}` names an output at
    version `t+1` and licenses authority from that version onward.  Counting all
    grants against the endpoint alone loses every grant issued earlier, which is
    why `levels` and `grants_by_step` are kept separate.
    """

    start_occurrence: str
    component_id: str
    levels: tuple[tuple[int, tuple[str, ...]], ...]
    grants_by_step: tuple[tuple[int, tuple[str, ...]], ...]
    bound_respected: bool
    grant_free: bool

    @property
    def intermediate_authoritative(self) -> tuple[str, ...]:
        return dict(self.levels).get(1, ())

    @property
    def end_authoritative(self) -> tuple[str, ...]:
        return dict(self.levels).get(max(dict(self.levels)), ())

    @property
    def grants(self) -> tuple[str, ...]:
        return tuple(sorted(o for _, outputs in self.grants_by_step for o in outputs))

    @property
    def duplicated(self) -> bool:
        return not self.bound_respected


def accumulated_authority_bound(
    levels: Mapping[int, Sequence[str]], grants: Mapping[int, Sequence[str]],
) -> bool:
    """`a_j <= a_i + sum_{t=i}^{j-1} g_{t,t+1}` for every `i <= j`.

    The grant-free corollary is the case where every `g` is empty, which
    collapses to monotone non-increase of authority along the component.
    """
    indices = sorted(levels)
    for position, lower in enumerate(indices):
        running = len(levels[lower])
        for upper in indices[position + 1:]:
            running += len(grants.get(upper - 1, ()))
            if len(levels[upper]) > running:
                return False
    return True


def authority_provenance(
    history: MigrationHistory, composite: CompositeMigration,
) -> tuple[AuthorityProvenance, ...]:
    """The grant-aware no-double-authority ledger.

    Descendants may be genuinely distinct occurrences with common provenance;
    what may not happen is that two of them each count as an independent source
    of warrant.  Authority is therefore tracked per version with the grants that
    licensed it at each step, never as a single pooled total.
    """
    states = [history.nodes[0].departure_state] + [
        node.arrival_state for node in history.nodes[1:]]
    assert all(state is not None for state in states)
    indexes = [_index(state.occurrences, "occurrence_id") for state in states]
    grants_at_step: dict[int, list[tuple[str, str]]] = {}
    for position, step in enumerate(history.steps):
        authorization = step.certificate.authorization
        grants_at_step[position] = list(
            authorization.authority_grants if authorization is not None else ())
    records: list[AuthorityProvenance] = []
    for component in composite.components:
        members = {0: component.start, 1: component.intermediate, 2: component.end}
        levels = {
            level: tuple(sorted(
                identifier for identifier in members.get(level, ())
                if identifier in indexes[level]
                and indexes[level][identifier].practical_authority))
            for level in range(len(states))
        }
        grants = {
            position: tuple(sorted(
                output for _, output in pairs if output in members.get(position + 1, ())))
            for position, pairs in grants_at_step.items()
        }
        respected = accumulated_authority_bound(levels, grants)
        grant_free = not any(grants.values())
        for start in (component.start or ("",)):
            records.append(AuthorityProvenance(
                start, component.component_id,
                tuple(sorted(levels.items())), tuple(sorted(grants.items())),
                respected, grant_free))
    return tuple(records)
