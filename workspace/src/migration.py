"""Finite verifier and exact witnesses for accountable ontology migration.

The verifier consumes raw finite states and a raw certificate.  It derives the
nine checks used by MIGRATION_THEORY.md; no Boolean assertion in a witness can
make a check pass.  Fractions are used throughout.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from fractions import Fraction as Q
from itertools import combinations
from typing import Iterable, Mapping, Sequence


class OccurrenceSort(str, Enum):
    COMMITMENT = "commitment"
    ENTITLEMENT = "entitlement"
    WARRANT = "warrant"
    CHALLENGE = "challenge"
    BURDEN = "burden"
    POSITION = "position"
    OTHER = "other"


class OccurrenceStatus(str, Enum):
    LIVE = "live"
    SUSPENDED = "suspended"
    TERMINAL = "terminal"


class DispositionMode(str, Enum):
    PRESERVE = "preserve"
    REFINE = "refine"
    MERGE = "merge"
    RETRACT = "retract"
    DISCHARGE = "discharge"
    SUSPEND = "suspend"
    LOSS = "loss"
    INTRODUCE = "introduce"


class RelationKind(str, Enum):
    JUSTIFICATION = "justification"
    WARRANT_PREMISE = "warrant-premise"
    WARRANT_CONSEQUENCE = "warrant-consequence"
    CHALLENGE_TARGET = "challenge-target"
    BURDEN_SCOPE = "burden-scope"
    INCOMPATIBILITY = "incompatibility"
    PROVENANCE = "provenance"
    AUTHORITY_CONSEQUENCE = "authority-consequence"


class TargetKind(str, Enum):
    OCCURRENCE = "occurrence"
    ANCESTRY_EDGE = "ancestry-edge"
    WARRANT_PREMISE = "warrant-premise"
    WARRANT_CONSEQUENCE = "warrant-consequence"
    SEMANTIC_COMPONENT = "semantic-component"


@dataclass(frozen=True)
class Occurrence:
    occurrence_id: str
    sort: OccurrenceSort
    status: OccurrenceStatus
    reference: str | None = None
    provenance: tuple[str, ...] = ()
    practical_authority: bool = False


@dataclass(frozen=True)
class TypedTarget:
    kind: TargetKind
    target_id: str


@dataclass(frozen=True)
class ChallengeSpec:
    challenge_id: str
    targets: tuple[TypedTarget, ...]


@dataclass(frozen=True)
class EvidenceRoot:
    root_id: str
    authorization_ref: str | None = None
    transported_from: str | None = None


@dataclass(frozen=True)
class RelationEdge:
    edge_id: str
    kind: RelationKind
    sources: tuple[str, ...]
    targets: tuple[str, ...]


@dataclass(frozen=True)
class Position:
    occurrence_id: str
    payoff_ref: str
    holdings: Q


@dataclass(frozen=True)
class CompilerEndorsement:
    endorsement_id: str
    coefficients: tuple[Q, ...]
    rhs: Q
    source_occurrence_id: str
    authorization_ref: str


@dataclass(frozen=True)
class CompilerSpec:
    compiler_id: str
    coordinate_ids: tuple[str, ...]
    represented_worlds: tuple[tuple[Q, ...], ...]
    endorsements: tuple[CompilerEndorsement, ...]
    reference: tuple[Q, ...]
    theta: Q


@dataclass(frozen=True)
class ChallengeRoute:
    route_id: str
    covered_occurrences: tuple[str, ...]
    terminal_outcomes: tuple[str, ...]
    account_id: str
    consuming_cost: int
    authorization_ref: str


@dataclass(frozen=True)
class NoninterferenceSpec:
    mechanism_reads_market_fields: tuple[str, ...] = ()
    market_writes_mechanism_fields: tuple[str, ...] = ()


@dataclass(frozen=True)
class MigrationState:
    state_id: str
    snapshot_id: str
    semantic_states: tuple[str, ...]
    claim_tables: Mapping[str, tuple[Q, ...]]
    payoff_tables: Mapping[str, tuple[Q, ...]]
    occurrences: tuple[Occurrence, ...]
    evidence_roots: tuple[EvidenceRoot, ...]
    relation_edges: tuple[RelationEdge, ...]
    challenges: tuple[ChallengeSpec, ...]
    positions: tuple[Position, ...]
    compiler: CompilerSpec
    force_holdings: Mapping[str, Q]
    routes: tuple[ChallengeRoute, ...]
    accounts: tuple[str, ...]
    remaining_consuming_potential: int
    authorization_ids: tuple[str, ...]
    migration_tokens: tuple[str, ...]
    noninterference: NoninterferenceSpec


@dataclass(frozen=True)
class DispositionCell:
    cell_id: str
    sort: OccurrenceSort
    inputs: tuple[str, ...]
    outputs: tuple[str, ...]
    mode: DispositionMode
    reconstruction_ref: str | None = None
    authorization_ref: str | None = None


@dataclass(frozen=True)
class EdgeTransport:
    old_edge_id: str
    new_edge_ids: tuple[str, ...]
    outcome_ref: str | None = None


@dataclass(frozen=True)
class SemanticReconstruction:
    reconstruction_id: str
    old_claim_ref: str
    new_claim_refs: tuple[str, ...]
    operation: str
    discrepancy_ref: str | None = None


@dataclass(frozen=True)
class ComparisonArena:
    states: tuple[str, ...]
    old_projection: Mapping[str, str]
    new_projection: Mapping[str, str]
    covered_support: tuple[str, ...]
    reconstructions: tuple[SemanticReconstruction, ...]


@dataclass(frozen=True)
class DiscrepancyEntry:
    discrepancy_id: str
    source_ref: str
    values: tuple[Q, ...]
    authorization_ref: str | None = None


@dataclass(frozen=True)
class TerminalDisposition:
    disposition_id: str
    source_cell_id: str
    kind: str
    witness_ref: str
    authorization_ref: str
    burdens_resolved: bool


@dataclass(frozen=True)
class SuspensionEntry:
    suspension_id: str
    source_ref: str
    output_occurrence_ids: tuple[str, ...]
    route_ids: tuple[str, ...]
    authorization_ref: str
    burdens_remain: bool
    practical_authority: bool = False


@dataclass(frozen=True)
class LossEntry:
    loss_id: str
    kind: str
    source_ref: str
    lost_content: str
    authorization_ref: str
    burdens_remain: bool
    practical_effect: str


@dataclass(frozen=True)
class LegacyRetention:
    legacy_id: str
    old_position_id: str
    output_position_id: str
    carrier_states: tuple[str, ...]
    retained_payoff: tuple[Q, ...]
    retained_holdings: Q
    retained_reference: Q
    settlement_rule: str
    authorization_ref: str


@dataclass(frozen=True)
class LiteralLiability:
    event_id: str
    kind: str
    obligation_id: str
    account_id: str
    amount: Q


@dataclass(frozen=True)
class AuthorizationRecord:
    authorization_id: str
    proposal_id: str
    certificate_id: str
    snapshot_id: str
    migration_token_id: str
    allowed_loss_ids: tuple[str, ...] = ()
    allowed_suspension_ids: tuple[str, ...] = ()
    allowed_legacy_ids: tuple[str, ...] = ()
    authority_grants: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True)
class EndpointRecheck:
    recheck_id: str
    certificate_id: str
    shadow_state_id: str
    compiler_id: str


@dataclass(frozen=True)
class ActivationRecord:
    proposal_id: str
    certificate_id: str
    expected_snapshot_id: str
    observed_snapshot_id: str
    preactivation_active_state_id: str
    preactivation_force_state_id: str
    shadow_state_id: str
    endpoint_recheck_id: str
    final_active_state_id: str


@dataclass(frozen=True)
class MigrationCertificate:
    certificate_id: str
    proposal_id: str
    old_snapshot_id: str
    shadow_state_id: str
    arena: ComparisonArena
    cells: tuple[DispositionCell, ...]
    edge_transports: tuple[EdgeTransport, ...]
    coordinate_transports: tuple[tuple[str, str], ...]
    semantic_node_transports: tuple[tuple[str, tuple[str, ...]], ...]
    discrepancies: tuple[DiscrepancyEntry, ...]
    terminal_dispositions: tuple[TerminalDisposition, ...]
    suspensions: tuple[SuspensionEntry, ...]
    losses: tuple[LossEntry, ...]
    legacy_retentions: tuple[LegacyRetention, ...]
    literal_liabilities: tuple[LiteralLiability, ...]
    authorization: AuthorizationRecord | None
    endpoint_recheck: EndpointRecheck | None
    activation: ActivationRecord


@dataclass(frozen=True)
class Counterwitness:
    check: str
    code: str
    ids: tuple[str, ...]
    detail: str


@dataclass(frozen=True)
class CheckResult:
    name: str
    passed: bool
    counterwitnesses: tuple[Counterwitness, ...]


@dataclass(frozen=True)
class MovementComponent:
    old_coordinate: str
    new_coordinate: str
    holdings: Q
    old_reference: Q
    new_reference: Q
    charge: Q


@dataclass(frozen=True)
class AnalyticMovementEntry:
    certificate_id: str
    components: tuple[MovementComponent, ...]
    total: Q


@dataclass(frozen=True)
class PayoffDerivation:
    nonzero_positions: tuple[str, ...]
    old_tables: Mapping[str, tuple[Q, ...]]
    new_tables: Mapping[str, tuple[Q, ...]]
    live_payoff_vectors: tuple[tuple[Q, ...], ...]
    old_reference_lift: tuple[Q, ...]
    new_reference_lift: tuple[Q, ...]
    old_reference_in_carrier: bool
    new_reference_in_carrier: bool
    transported_holdings: Mapping[str, Q]
    new_coordinate_holdings: Mapping[str, Q]
    analytic_movement: Q
    movement_entry: AnalyticMovementEntry


@dataclass(frozen=True)
class VerificationReport:
    passed: bool
    checks: Mapping[str, CheckResult]
    counterwitnesses: tuple[Counterwitness, ...]
    reachable_entitlement_roots: Mapping[str, tuple[str, ...]]
    challenge_frontiers: Mapping[str, tuple[TypedTarget, ...]]
    payoff: PayoffDerivation
    eventual_route_coverage: Mapping[str, tuple[str, ...]]
    old_compiler_valid: bool
    endpoint_compiler_valid: bool
    authorization_binding_valid: bool
    atomic_activation_valid: bool


CHECKS = (
    "cells",
    "semantics",
    "entitlements",
    "challenges",
    "relations",
    "payoffs",
    "accounting",
    "endpoint",
    "activation",
)


def _index(items: Iterable[object], field: str) -> dict[str, object]:
    return {str(getattr(item, field)): item for item in items}


def _issue(store: dict[str, list[Counterwitness]], check: str, code: str,
           ids: Iterable[str], detail: str) -> None:
    store[check].append(Counterwitness(check, code, tuple(ids), detail))


def _active(occurrence: Occurrence) -> bool:
    return occurrence.status in (OccurrenceStatus.LIVE, OccurrenceStatus.SUSPENDED)


def _dot(left: Sequence[Q], right: Sequence[Q]) -> Q:
    return sum((Q(a) * Q(b) for a, b in zip(left, right)), Q(0))


def _solve_square(matrix: Sequence[Sequence[Q]], values: Sequence[Q]) -> tuple[Q, ...] | None:
    n = len(values)
    work = [[Q(x) for x in row] + [Q(values[i])] for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next((row for row in range(column, n) if work[row][column]), None)
        if pivot is None:
            return None
        work[column], work[pivot] = work[pivot], work[column]
        scale = work[column][column]
        work[column] = [x / scale for x in work[column]]
        for row in range(n):
            if row == column:
                continue
            scale = work[row][column]
            work[row] = [x - scale * y for x, y in zip(work[row], work[column])]
    return tuple(work[row][-1] for row in range(n))


def in_convex_hull(point: Sequence[Q], vertices: Sequence[Sequence[Q]]) -> bool:
    """Exact finite-dimensional convex-hull membership by Caratheodory search."""
    p = tuple(Q(x) for x in point)
    vs = tuple(tuple(Q(x) for x in vertex) for vertex in vertices)
    if not vs or any(len(vertex) != len(p) for vertex in vs):
        return False
    equations = [tuple(vertex[d] for vertex in vs) for d in range(len(p))]
    equations.append(tuple(Q(1) for _ in vs))
    targets = list(p) + [Q(1)]
    for size in range(1, min(len(vs), len(p) + 1) + 1):
        for subset in combinations(range(len(vs)), size):
            for rows in combinations(range(len(p) + 1), size):
                matrix = [[equations[row][column] for column in subset] for row in rows]
                solution = _solve_square(matrix, [targets[row] for row in rows])
                if solution is None or any(weight < 0 for weight in solution):
                    continue
                if all(
                    sum(equations[row][column] * solution[j]
                        for j, column in enumerate(subset)) == targets[row]
                    for row in range(len(p) + 1)
                ):
                    return True
    return False


def _compiler_valid(state: MigrationState) -> bool:
    compiler = state.compiler
    dimension = len(compiler.coordinate_ids)
    if not Q(0) < compiler.theta <= Q(1):
        return False
    if len(compiler.reference) != dimension or not compiler.represented_worlds:
        return False
    if any(len(world) != dimension for world in compiler.represented_worlds):
        return False
    if not in_convex_hull(compiler.reference, compiler.represented_worlds):
        return False
    occurrences = _index(state.occurrences, "occurrence_id")
    authorizations = set(state.authorization_ids)
    for endorsement in compiler.endorsements:
        source = occurrences.get(endorsement.source_occurrence_id)
        if (len(endorsement.coefficients) != dimension or source is None
                or not _active(source) or not source.practical_authority
                or endorsement.authorization_ref not in authorizations):
            return False
        for world in compiler.represented_worlds:
            core_point = tuple(
                q + compiler.theta * (z - q)
                for q, z in zip(compiler.reference, world)
            )
            if _dot(endorsement.coefficients, core_point) < endorsement.rhs:
                return False
    return True


def _pullback(table: tuple[Q, ...], native_states: tuple[str, ...],
              projection: Mapping[str, str], support: tuple[str, ...]) -> tuple[Q, ...] | None:
    values = dict(zip(native_states, table))
    try:
        return tuple(Q(values[projection[state]]) for state in support)
    except KeyError:
        return None


def _combine(operation: str, tables: Sequence[tuple[Q, ...]]) -> tuple[Q, ...] | None:
    if not tables:
        return None
    if operation == "identity" and len(tables) == 1:
        return tables[0]
    if operation == "or":
        return tuple(max(values) for values in zip(*tables))
    if operation == "sum":
        return tuple(sum(values, Q(0)) for values in zip(*tables))
    return None


def verify_migration(old_state: MigrationState, proposed_state: MigrationState,
                     certificate: MigrationCertificate) -> VerificationReport:
    issues: dict[str, list[Counterwitness]] = {name: [] for name in CHECKS}
    old_occ = _index(old_state.occurrences, "occurrence_id")
    new_occ = _index(proposed_state.occurrences, "occurrence_id")
    cells = _index(certificate.cells, "cell_id")
    old_edges = _index(old_state.relation_edges, "edge_id")
    new_edges = _index(proposed_state.relation_edges, "edge_id")
    transports = _index(certificate.edge_transports, "old_edge_id")
    losses = _index(certificate.losses, "loss_id")
    suspensions = _index(certificate.suspensions, "suspension_id")
    discrepancies = _index(certificate.discrepancies, "discrepancy_id")
    terminal_dispositions = _index(certificate.terminal_dispositions, "disposition_id")
    auth = certificate.authorization

    # 1. Exact occurrence conservation, typed cell legality, and authority conservation.
    consumed: dict[str, list[str]] = {}
    produced: dict[str, list[str]] = {}
    legal_modes = {
        DispositionMode.PRESERVE, DispositionMode.REFINE, DispositionMode.MERGE,
        DispositionMode.RETRACT, DispositionMode.DISCHARGE, DispositionMode.SUSPEND,
        DispositionMode.LOSS, DispositionMode.INTRODUCE,
    }
    for state, label in ((old_state, "old"), (proposed_state, "new")):
        ids = [item.occurrence_id for item in state.occurrences]
        if len(ids) != len(set(ids)):
            _issue(issues, "cells", "occurrence.duplicate_id", tuple(ids), f"{label} occurrence IDs are not unique")
        for occurrence in state.occurrences:
            if not isinstance(occurrence.sort, OccurrenceSort) or not isinstance(occurrence.status, OccurrenceStatus):
                _issue(issues, "cells", "occurrence.invalid_type", (occurrence.occurrence_id,), "sort and status must be declared enum values")
    cell_ids = [cell.cell_id for cell in certificate.cells]
    if len(cell_ids) != len(set(cell_ids)):
        _issue(issues, "cells", "cell.duplicate_id", tuple(cell_ids), "cell IDs must be unique")
    for cell in certificate.cells:
        if not isinstance(cell.mode, DispositionMode) or cell.mode not in legal_modes or not isinstance(cell.sort, OccurrenceSort):
            _issue(issues, "cells", "cell.illegal_mode", (cell.cell_id,), "unknown disposition mode")
        for identifier in cell.inputs:
            consumed.setdefault(identifier, []).append(cell.cell_id)
            occurrence = old_occ.get(identifier)
            if occurrence is None or occurrence.sort != cell.sort:
                _issue(issues, "cells", "cell.input_sort", (cell.cell_id, identifier), "missing or wrongly sorted input")
            elif not _active(occurrence):
                _issue(issues, "cells", "cell.terminal_input", (cell.cell_id, identifier), "terminal history cannot be consumed as live input")
        for identifier in cell.outputs:
            produced.setdefault(identifier, []).append(cell.cell_id)
            occurrence = new_occ.get(identifier)
            if occurrence is None or occurrence.sort != cell.sort:
                _issue(issues, "cells", "cell.output_sort", (cell.cell_id, identifier), "missing or wrongly sorted output")
            elif not _active(occurrence):
                _issue(issues, "cells", "cell.terminal_output", (cell.cell_id, identifier), "a producing cell output must be live or suspended")
        terminal_modes = {DispositionMode.RETRACT, DispositionMode.DISCHARGE, DispositionMode.LOSS}
        if not cell.inputs and cell.mode != DispositionMode.INTRODUCE:
            _issue(issues, "cells", "cell.empty_input", (cell.cell_id,), "only introductions may have empty input")
        if cell.mode == DispositionMode.INTRODUCE and (cell.inputs or not cell.outputs):
            _issue(issues, "cells", "cell.invalid_introduction", (cell.cell_id,), "introduction requires no inputs and at least one output")
        if not cell.outputs and cell.mode not in terminal_modes:
            _issue(issues, "cells", "cell.empty_output", (cell.cell_id,), "only terminal dispositions may have empty output")
        if cell.mode in terminal_modes and (cell.outputs or cell.authorization_ref is None):
            _issue(issues, "cells", "cell.terminal_shape", (cell.cell_id,), "terminal disposition requires empty output and authorization")
        if cell.mode in (DispositionMode.DISCHARGE, DispositionMode.RETRACT) and not any(
            item.source_cell_id == cell.cell_id and item.witness_ref
            and item.authorization_ref == cell.authorization_ref
            for item in terminal_dispositions.values()
        ):
            code = "cell.unbacked_discharge" if cell.mode == DispositionMode.DISCHARGE else "cell.unbacked_retraction"
            _issue(issues, "cells", code, (cell.cell_id,), "terminal removal requires a specific public witness")
        if cell.mode == DispositionMode.LOSS and not any(
            item.source_ref == cell.cell_id for item in certificate.losses
        ):
            _issue(issues, "cells", "cell.unbacked_loss", (cell.cell_id,), "loss mode requires a disclosed loss entry")
        if cell.authorization_ref is not None and cell.authorization_ref not in old_state.authorization_ids:
            _issue(issues, "cells", "cell.unknown_authorization", (cell.cell_id, cell.authorization_ref), "cell authorization is not prior public authority")
        if cell.mode == DispositionMode.PRESERVE and (len(cell.inputs), len(cell.outputs)) != (1, 1):
            _issue(issues, "cells", "cell.preserve_cardinality", (cell.cell_id,), "preserve is one-to-one")
        if cell.mode == DispositionMode.REFINE and not (len(cell.inputs) == 1 and len(cell.outputs) >= 1):
            _issue(issues, "cells", "cell.refine_cardinality", (cell.cell_id,), "refine has one input and one or more outputs")
        if cell.mode == DispositionMode.MERGE and not (len(cell.inputs) >= 2 and len(cell.outputs) == 1):
            _issue(issues, "cells", "cell.merge_cardinality", (cell.cell_id,), "merge has two or more inputs and one output")
        if cell.mode == DispositionMode.SUSPEND:
            if not cell.inputs or not cell.outputs or any(
                new_occ.get(identifier) is None
                or new_occ[identifier].status != OccurrenceStatus.SUSPENDED
                for identifier in cell.outputs
            ):
                _issue(issues, "cells", "cell.suspend_status", (cell.cell_id,), "suspend outputs must be suspended occurrences")
        old_authority = sum(bool(old_occ.get(i) and old_occ[i].practical_authority) for i in cell.inputs)
        authoritative_outputs = tuple(
            i for i in cell.outputs if new_occ.get(i) and new_occ[i].practical_authority
        )
        grants = set(auth.authority_grants if auth else ())
        ungranted = tuple(i for i in authoritative_outputs if (cell.cell_id, i) not in grants)
        allowed_inherited = old_authority > 0 and len(authoritative_outputs) <= old_authority
        if ungranted and not allowed_inherited:
            _issue(issues, "cells", "authority.duplicated_or_ungranted", (cell.cell_id,) + ungranted,
                   "semantic descent does not duplicate or introduce practical authority")
    for identifier, occurrence in old_occ.items():
        if _active(occurrence) and len(consumed.get(identifier, ())) != 1:
            code = "occurrence.duplicate_input" if len(consumed.get(identifier, ())) > 1 else "occurrence.orphan_input"
            _issue(issues, "cells", code, (identifier,) + tuple(consumed.get(identifier, ())), "old live/suspended occurrence must be consumed exactly once")
    for identifier, occurrence in new_occ.items():
        if _active(occurrence) and len(produced.get(identifier, ())) != 1:
            code = "occurrence.duplicate_output" if len(produced.get(identifier, ())) > 1 else "occurrence.unproduced_output"
            _issue(issues, "cells", code, (identifier,) + tuple(produced.get(identifier, ())), "new live/suspended occurrence must be produced exactly once")

    # 2. Exhaustive comparison-arena reconstruction on declared support.
    arena = certificate.arena
    if set(arena.covered_support) - set(arena.states):
        _issue(issues, "semantics", "semantic.support_outside_arena", arena.covered_support, "covered support must be in Gamma")
    discrepancy_ids = [entry.discrepancy_id for entry in certificate.discrepancies]
    if len(discrepancy_ids) != len(set(discrepancy_ids)):
        _issue(issues, "semantics", "semantic.duplicate_discrepancy_id", tuple(discrepancy_ids), "discrepancy IDs must be unique")
    for reconstruction in arena.reconstructions:
        old_table = old_state.claim_tables.get(reconstruction.old_claim_ref)
        new_tables = [proposed_state.claim_tables.get(ref) for ref in reconstruction.new_claim_refs]
        if (old_table is None or len(old_table) != len(old_state.semantic_states)
                or any(table is None or len(table) != len(proposed_state.semantic_states) for table in new_tables)):
            _issue(issues, "semantics", "semantic.missing_table", (reconstruction.reconstruction_id,), "reconstruction names a missing claim table")
            continue
        old_pull = _pullback(old_table, old_state.semantic_states, arena.old_projection, arena.covered_support)
        pulled = [_pullback(table, proposed_state.semantic_states, arena.new_projection, arena.covered_support) for table in new_tables if table is not None]
        new_pull = None if any(table is None for table in pulled) else _combine(reconstruction.operation, pulled)  # type: ignore[arg-type]
        if old_pull is None or new_pull is None:
            _issue(issues, "semantics", "semantic.invalid_projection_or_operation", (reconstruction.reconstruction_id,), "projection or reconstruction operation is undefined")
            continue
        delta = tuple(left - right for left, right in zip(old_pull, new_pull))
        if any(delta):
            discrepancy = discrepancies.get(reconstruction.discrepancy_ref or "")
            if discrepancy is None or discrepancy.values != delta:
                _issue(issues, "semantics", "semantic.lossless_collapse", (reconstruction.reconstruction_id,), f"unrecorded discrepancy {delta}")
            else:
                affected = {
                    cell.cell_id for cell in certificate.cells
                    if cell.reconstruction_ref == reconstruction.reconstruction_id
                } | {reconstruction.reconstruction_id}
                disposed = any(loss.source_ref in affected for loss in certificate.losses) or any(
                    suspension.source_ref in affected for suspension in certificate.suspensions
                )
                if not disposed:
                    _issue(issues, "semantics", "semantic.discrepancy_without_disposition", (reconstruction.reconstruction_id, discrepancy.discrepancy_id), "discrepancy disclosure alone does not dispose of a live semantic failure")

    # 3. Active entitlement roots are found by graph reachability, not tuple nonemptiness.
    roots = _index(proposed_state.evidence_roots, "root_id")
    old_roots = _index(old_state.evidence_roots, "root_id")
    reverse: dict[str, set[str]] = {}
    for edge in proposed_state.relation_edges:
        if edge.kind == RelationKind.JUSTIFICATION:
            for target in edge.targets:
                reverse.setdefault(target, set()).update(edge.sources)
    reachable_roots: dict[str, tuple[str, ...]] = {}
    for identifier, occurrence in new_occ.items():
        if occurrence.sort != OccurrenceSort.ENTITLEMENT or occurrence.status != OccurrenceStatus.LIVE or not occurrence.practical_authority:
            continue
        seen, frontier, found = {identifier}, [identifier], set()
        while frontier:
            node = frontier.pop()
            if node in roots:
                root = roots[node]
                transported = root.transported_from and old_roots.get(root.transported_from)
                transported_valid = bool(transported and transported.authorization_ref in old_state.authorization_ids)
                new_valid = bool(root.transported_from is None and root.authorization_ref in proposed_state.authorization_ids)
                if transported_valid or new_valid:
                    found.add(node)
            for parent in reverse.get(node, ()):
                if parent not in seen:
                    seen.add(parent)
                    frontier.append(parent)
        reachable_roots[identifier] = tuple(sorted(found))
        if not found:
            _issue(issues, "entitlements", "entitlement.missing_authorized_root", (identifier,), "no path reaches a transported or newly authorized evidence root")

    # 4. Typed challenge descendant frontiers are computed from cells and edge transports.
    new_challenges = _index(proposed_state.challenges, "challenge_id")
    for state, specs, occurrence_index in (
        (old_state, old_state.challenges, old_occ),
        (proposed_state, proposed_state.challenges, new_occ),
    ):
        spec_ids = [spec.challenge_id for spec in specs]
        if len(spec_ids) != len(set(spec_ids)):
            _issue(issues, "challenges", "challenge.duplicate_spec", tuple(spec_ids), "challenge target specifications must be unique")
        active_challenge_ids = {
            identifier for identifier, occurrence in occurrence_index.items()
            if occurrence.sort == OccurrenceSort.CHALLENGE and _active(occurrence)
        }
        if set(spec_ids) != active_challenge_ids:
            _issue(issues, "challenges", "challenge.missing_or_extra_spec", tuple(sorted(set(spec_ids) ^ active_challenge_ids)), f"{state.state_id} challenge occurrences and target specs differ")
    challenge_frontiers: dict[str, tuple[TypedTarget, ...]] = {}
    cell_by_input = {identifier: cell for cell in certificate.cells for identifier in cell.inputs}
    edge_target_kind = {
        RelationKind.JUSTIFICATION: TargetKind.ANCESTRY_EDGE,
        RelationKind.WARRANT_PREMISE: TargetKind.WARRANT_PREMISE,
        RelationKind.WARRANT_CONSEQUENCE: TargetKind.WARRANT_CONSEQUENCE,
    }
    for challenge in old_state.challenges:
        challenge_cell = cell_by_input.get(challenge.challenge_id)
        if challenge_cell is None:
            continue
        successor_challenges = challenge_cell.outputs
        required: set[TypedTarget] = set()
        for target in challenge.targets:
            if target.kind == TargetKind.OCCURRENCE:
                target_cell = cell_by_input.get(target.target_id)
                if target_cell:
                    required.update(TypedTarget(TargetKind.OCCURRENCE, output) for output in target_cell.outputs)
                else:
                    _issue(issues, "challenges", "challenge.unknown_occurrence_target", (challenge.challenge_id, target.target_id), "target occurrence has no consuming cell")
            elif target.kind in (TargetKind.ANCESTRY_EDGE, TargetKind.WARRANT_PREMISE, TargetKind.WARRANT_CONSEQUENCE):
                transport = transports.get(target.target_id)
                if transport:
                    for edge_id in transport.new_edge_ids:
                        edge = new_edges.get(edge_id)
                        if edge:
                            required.add(TypedTarget(edge_target_kind.get(edge.kind, target.kind), edge_id))
                else:
                    _issue(issues, "challenges", "challenge.unknown_edge_target", (challenge.challenge_id, target.target_id), "target edge has no declared transport")
            else:
                matched = False
                for reconstruction in arena.reconstructions:
                    if reconstruction.old_claim_ref == target.target_id:
                        matched = True
                        required.update(TypedTarget(TargetKind.SEMANTIC_COMPONENT, ref) for ref in reconstruction.new_claim_refs)
                if not matched:
                    _issue(issues, "challenges", "challenge.unknown_semantic_target", (challenge.challenge_id, target.target_id), "semantic target has no reconstruction")
        challenge_frontiers[challenge.challenge_id] = tuple(sorted(required, key=lambda item: (item.kind.value, item.target_id)))
        actual: set[TypedTarget] = set()
        for successor in successor_challenges:
            spec = new_challenges.get(successor)
            if spec:
                actual.update(spec.targets)
        missing, extra = required - actual, actual - required
        if missing:
            _issue(issues, "challenges", "challenge.uncovered_frontier", tuple(item.target_id for item in sorted(missing, key=lambda x: x.target_id)), "computed descendant target is not covered")
        if extra:
            _issue(issues, "challenges", "challenge.late_reassignment", tuple(item.target_id for item in sorted(extra, key=lambda x: x.target_id)), "new target is not a descendant of the frozen target")

    # 5. Every old structural edge is transported to matching new edges or explicitly disposed of.
    outcome_refs = set(losses) | set(suspensions)
    semantic_node_map = dict(certificate.semantic_node_transports)
    cell_by_old_occurrence = {
        identifier: cell for cell in certificate.cells for identifier in cell.inputs
    }
    transported_roots = {
        root.transported_from: root.root_id for root in proposed_state.evidence_roots
        if root.transported_from is not None
    }

    def candidate_nodes(old_node: str) -> set[str]:
        if old_node in cell_by_old_occurrence:
            return set(cell_by_old_occurrence[old_node].outputs)
        if old_node in semantic_node_map:
            return set(semantic_node_map[old_node])
        if old_node in transports:
            return set(transports[old_node].new_edge_ids)
        if old_node in transported_roots:
            return {transported_roots[old_node]}
        return {old_node}

    old_edge_ids = [edge.edge_id for edge in old_state.relation_edges]
    new_edge_ids = [edge.edge_id for edge in proposed_state.relation_edges]
    if len(old_edge_ids) != len(set(old_edge_ids)) or len(new_edge_ids) != len(set(new_edge_ids)):
        _issue(issues, "relations", "relation.duplicate_id", tuple(old_edge_ids + new_edge_ids), "relation edge IDs must be unique at each endpoint")
    for edge_id, old_edge in old_edges.items():
        transport = transports.get(edge_id)
        if transport is None:
            _issue(issues, "relations", "relation.orphaned_edge", (edge_id,), "old relation has no transport or disposition")
            continue
        if not transport.new_edge_ids and transport.outcome_ref not in outcome_refs:
            _issue(issues, "relations", "relation.empty_transport", (edge_id,), "relation transport has no image")
        for new_edge_id in transport.new_edge_ids:
            edge = new_edges.get(new_edge_id)
            if edge is None or edge.kind != old_edge.kind:
                code = "relation.hidden_incompatibility" if old_edge.kind == RelationKind.INCOMPATIBILITY else "relation.missing_image"
                _issue(issues, "relations", code, (edge_id, new_edge_id), "transported relation is absent or changes kind")
                continue
            permitted_sources = set().union(*(candidate_nodes(node) for node in old_edge.sources))
            permitted_targets = set().union(*(candidate_nodes(node) for node in old_edge.targets))
            invalid_endpoints = (set(edge.sources) - permitted_sources) | (set(edge.targets) - permitted_targets)
            if invalid_endpoints:
                _issue(issues, "relations", "relation.unrelated_image", (edge_id, new_edge_id) + tuple(sorted(invalid_endpoints)), "edge image uses nodes unrelated to the old endpoints")
        if old_edge.kind == RelationKind.INCOMPATIBILITY:
            expected_pairs = {
                (left, right)
                for source in old_edge.sources for target in old_edge.targets
                for left in candidate_nodes(source) for right in candidate_nodes(target)
            }
            actual_pairs = {
                (left, right)
                for image_id in transport.new_edge_ids if image_id in new_edges
                for left in new_edges[image_id].sources for right in new_edges[image_id].targets
            }
            missing_pairs = expected_pairs - actual_pairs
            if missing_pairs and transport.outcome_ref not in outcome_refs:
                _issue(issues, "relations", "relation.hidden_incompatibility", (edge_id,) + tuple(f"{left}->{right}" for left, right in sorted(missing_pairs)), "split or merged incompatibility pair is neither visible nor disposed")
    for edge in proposed_state.relation_edges:
        if edge.kind == RelationKind.AUTHORITY_CONSEQUENCE and not any(
            source in new_occ and new_occ[source].practical_authority and _active(new_occ[source])
            for source in edge.sources
        ):
            _issue(issues, "relations", "relation.unauthorized_consequence", (edge.edge_id,) + edge.sources, "authority-bearing consequence has no active authorized source occurrence")

    # 6. Outstanding payoff meanings, local carrier, reference lifts, holdings, movement.
    position_cells = [cell for cell in certificate.cells if cell.sort == OccurrenceSort.POSITION]
    new_positions = _index(proposed_state.positions, "occurrence_id")
    old_positions = _index(old_state.positions, "occurrence_id")
    for state, positions, occurrence_index in (
        (old_state, old_state.positions, old_occ),
        (proposed_state, proposed_state.positions, new_occ),
    ):
        position_ids = [position.occurrence_id for position in positions]
        if len(position_ids) != len(set(position_ids)):
            _issue(issues, "payoffs", "payoff.duplicate_position_id", tuple(position_ids), "position occurrence IDs must be unique")
        for position in positions:
            occurrence = occurrence_index.get(position.occurrence_id)
            if (occurrence is None or occurrence.sort != OccurrenceSort.POSITION
                    or occurrence.reference != position.payoff_ref):
                _issue(issues, "payoffs", "payoff.position_occurrence_mismatch", (state.state_id, position.occurrence_id, position.payoff_ref), "position data must match its typed occurrence")
    legacy_by_position = {entry.old_position_id: entry for entry in certificate.legacy_retentions}
    old_payoff_tables: dict[str, tuple[Q, ...]] = {}
    new_payoff_tables: dict[str, tuple[Q, ...]] = {}
    nonzero, old_lift, new_lift, holdings_map = [], [], [], {}
    for old_position in old_state.positions:
        if old_position.holdings == 0:
            continue
        nonzero.append(old_position.occurrence_id)
        cell = next((item for item in position_cells if old_position.occurrence_id in item.inputs), None)
        if cell is None or len(cell.outputs) != 1:
            _issue(issues, "payoffs", "payoff.missing_transport", (old_position.occurrence_id,), "nonzero position needs one payoff successor or legacy retention")
            continue
        new_position = new_positions.get(cell.outputs[0])
        old_native = old_state.payoff_tables.get(old_position.payoff_ref)
        legacy = legacy_by_position.get(old_position.occurrence_id)
        new_native = proposed_state.payoff_tables.get(new_position.payoff_ref) if new_position else None
        old_pull = _pullback(old_native, old_state.semantic_states, arena.old_projection, arena.covered_support) if old_native else None
        new_pull = _pullback(new_native, proposed_state.semantic_states, arena.new_projection, arena.covered_support) if new_native else None
        valid_legacy = bool(
            legacy is not None and new_position is not None and old_pull is not None
            and auth is not None and legacy.authorization_ref == auth.authorization_id
            and legacy.legacy_id in auth.allowed_legacy_ids
            and legacy.output_position_id == new_position.occurrence_id
            and new_position.payoff_ref == legacy.legacy_id
            and legacy.carrier_states == arena.covered_support
            and legacy.retained_payoff == old_pull
            and legacy.retained_holdings == old_position.holdings == new_position.holdings
            and in_convex_hull((legacy.retained_reference,), tuple((value,) for value in legacy.retained_payoff))
        )
        if old_pull is None or (new_pull is None and not valid_legacy):
            _issue(issues, "payoffs", "payoff.missing_table", (old_position.occurrence_id,), "payoff pullback is undefined")
            continue
        effective_new_pull = legacy.retained_payoff if valid_legacy else new_pull
        old_payoff_tables[old_position.occurrence_id] = old_pull
        new_payoff_tables[new_position.occurrence_id] = effective_new_pull  # type: ignore[assignment]
        if old_pull != new_pull and not valid_legacy:
            _issue(issues, "payoffs", "payoff.mismatch_without_legacy", (old_position.occurrence_id, new_position.occurrence_id), "discrepancy cannot rewrite an outstanding contract")
        if new_position.holdings != old_position.holdings:
            _issue(issues, "payoffs", "payoff.holdings_changed", (old_position.occurrence_id, new_position.occurrence_id), "transported holdings must be identical")
        holdings_map[new_position.occurrence_id] = new_position.holdings
        old_coordinate = old_position.payoff_ref
        old_coordinate_index = old_state.compiler.coordinate_ids.index(old_coordinate) if old_coordinate in old_state.compiler.coordinate_ids else -1
        if old_coordinate_index < 0:
            _issue(issues, "payoffs", "payoff.reference_coordinate_missing", (old_position.occurrence_id,), "payoff coordinate has no public reference")
        else:
            old_lift.append(old_state.compiler.reference[old_coordinate_index])
            if valid_legacy:
                new_lift.append(legacy.retained_reference)
            elif new_position.payoff_ref in proposed_state.compiler.coordinate_ids:
                new_lift.append(proposed_state.compiler.reference[proposed_state.compiler.coordinate_ids.index(new_position.payoff_ref)])
            else:
                _issue(issues, "payoffs", "payoff.reference_coordinate_missing", (new_position.occurrence_id,), "new payoff coordinate has no public reference")
    payoff_vectors = tuple(
        tuple(old_payoff_tables[position][i] for position in nonzero if position in old_payoff_tables)
        for i in range(len(arena.covered_support))
    )
    old_in_carrier = bool(old_lift) and in_convex_hull(old_lift, payoff_vectors)
    new_in_carrier = bool(new_lift) and in_convex_hull(new_lift, payoff_vectors)
    if nonzero and not old_in_carrier:
        _issue(issues, "payoffs", "payoff.old_reference_outside_carrier", tuple(nonzero), "old reference lift is outside conv(W_Gamma)")
    if nonzero and not new_in_carrier:
        _issue(issues, "payoffs", "payoff.new_reference_outside_carrier", tuple(nonzero), "new reference lift is outside conv(W_Gamma)")
    coordinate_map = dict(certificate.coordinate_transports)
    old_coordinate_ids = tuple(left for left, _ in certificate.coordinate_transports)
    new_coordinate_ids = tuple(right for _, right in certificate.coordinate_transports)
    if len(old_coordinate_ids) != len(set(old_coordinate_ids)) or len(new_coordinate_ids) != len(set(new_coordinate_ids)):
        _issue(issues, "payoffs", "payoff.duplicate_coordinate_transport", old_coordinate_ids + new_coordinate_ids, "one coordinate transport may contribute to movement only once")
    new_coordinate_holdings: dict[str, Q] = {}
    transported_new = set(coordinate_map.values())
    for coordinate in proposed_state.compiler.coordinate_ids:
        value = Q(proposed_state.force_holdings.get(coordinate, Q(0)))
        if coordinate not in transported_new and value != 0:
            _issue(issues, "payoffs", "payoff.new_coordinate_nonzero_holdings", (coordinate,), "genuinely new coordinate must enter with zero holdings")
        if coordinate not in transported_new:
            new_coordinate_holdings[coordinate] = value
    movement = Q(0)
    movement_components: list[MovementComponent] = []
    for old_coordinate, new_coordinate in certificate.coordinate_transports:
        if old_coordinate not in old_state.compiler.coordinate_ids or new_coordinate not in proposed_state.compiler.coordinate_ids:
            _issue(issues, "payoffs", "payoff.bad_coordinate_transport", (old_coordinate, new_coordinate), "coordinate transport is not defined at both endpoints")
            continue
        holdings = Q(old_state.force_holdings.get(old_coordinate, Q(0)))
        new_holdings = Q(proposed_state.force_holdings.get(new_coordinate, Q(0)))
        if holdings != new_holdings:
            _issue(issues, "payoffs", "payoff.force_holdings_changed", (old_coordinate, new_coordinate), "force holdings changed during atomic transport")
        q_old = old_state.compiler.reference[old_state.compiler.coordinate_ids.index(old_coordinate)]
        q_new = proposed_state.compiler.reference[proposed_state.compiler.coordinate_ids.index(new_coordinate)]
        liability = max(Q(0), -holdings * (q_old - q_new))
        movement += liability
        movement_components.append(MovementComponent(
            old_coordinate, new_coordinate, holdings, q_old, q_new, liability,
        ))
    movement_entry = AnalyticMovementEntry(
        certificate.certificate_id, tuple(movement_components), movement,
    )
    payoff_derivation = PayoffDerivation(
        tuple(nonzero), old_payoff_tables, new_payoff_tables, payoff_vectors,
        tuple(old_lift), tuple(new_lift), old_in_carrier, new_in_carrier,
        holdings_map, new_coordinate_holdings, movement, movement_entry,
    )

    # 7. Suspension, terminal loss, legacy retention, and literal liabilities stay typed.
    loss_semantic_keys: set[tuple[str, str]] = set()
    seen_loss_ids: set[str] = set()
    for loss in certificate.losses:
        key = (loss.source_ref, loss.lost_content)
        if loss.loss_id in seen_loss_ids or key in loss_semantic_keys:
            _issue(issues, "accounting", "accounting.duplicate_loss", (loss.loss_id,) + key, "same semantic loss is entered twice")
        seen_loss_ids.add(loss.loss_id)
        loss_semantic_keys.add(key)
        if not loss.lost_content or not loss.practical_effect:
            _issue(issues, "accounting", "accounting.incomplete_loss_disclosure", (loss.loss_id,), "loss must name exact content and its practical-authority effect")
        if auth is None or loss.authorization_ref != auth.authorization_id or loss.loss_id not in auth.allowed_loss_ids:
            _issue(issues, "accounting", "accounting.unauthorized_loss", (loss.loss_id,), "loss disclosure is not loss authorization")
        if loss.source_ref not in cells and loss.source_ref not in old_edges:
            _issue(issues, "accounting", "accounting.unknown_loss_source", (loss.loss_id, loss.source_ref), "loss must identify its cell or edge")
    terminal_ids = [item.disposition_id for item in certificate.terminal_dispositions]
    if len(terminal_ids) != len(set(terminal_ids)):
        _issue(issues, "accounting", "accounting.duplicate_terminal_disposition", tuple(terminal_ids), "terminal disposition IDs must be unique")
    for disposition in certificate.terminal_dispositions:
        cell = cells.get(disposition.source_cell_id)
        if (cell is None or cell.mode not in (DispositionMode.DISCHARGE, DispositionMode.RETRACT)
                or disposition.authorization_ref not in old_state.authorization_ids
                or not disposition.witness_ref or not disposition.burdens_resolved):
            _issue(issues, "accounting", "accounting.invalid_terminal_disposition", (disposition.disposition_id, disposition.source_cell_id), "terminal disposition needs the matching cell, prior authority, witness, and burden resolution")
    route_ids = set(_index(proposed_state.routes, "route_id"))
    suspended_membership: dict[str, list[str]] = {}
    for suspension in certificate.suspensions:
        if auth is None or suspension.authorization_ref != auth.authorization_id or suspension.suspension_id not in auth.allowed_suspension_ids:
            _issue(issues, "accounting", "accounting.unauthorized_suspension", (suspension.suspension_id,), "suspension lacks an explicit authorization")
        for occurrence_id in suspension.output_occurrence_ids:
            suspended_membership.setdefault(occurrence_id, []).append(suspension.suspension_id)
            occurrence = new_occ.get(occurrence_id)
            if occurrence is None or occurrence.status != OccurrenceStatus.SUSPENDED or occurrence.practical_authority:
                _issue(issues, "accounting", "accounting.invalid_suspension", (suspension.suspension_id, occurrence_id), "suspension must remain live, nonoperative, and typed")
            source_cell = cells.get(suspension.source_ref)
            if source_cell is None or occurrence_id not in source_cell.outputs:
                _issue(issues, "accounting", "accounting.wrong_suspension_source", (suspension.suspension_id, suspension.source_ref, occurrence_id), "suspended output must be produced by its named source cell")
        if not suspension.route_ids or set(suspension.route_ids) - route_ids:
            _issue(issues, "accounting", "accounting.suspension_without_route", (suspension.suspension_id,), "suspension requires a remaining route")
        if not suspension.burdens_remain:
            _issue(issues, "accounting", "accounting.suspension_discharges_burden", (suspension.suspension_id,), "suspension cannot silently discharge the associated burden")
    for occurrence in proposed_state.occurrences:
        if occurrence.status == OccurrenceStatus.SUSPENDED and len(suspended_membership.get(occurrence.occurrence_id, ())) != 1:
            _issue(issues, "accounting", "accounting.suspension_partition", (occurrence.occurrence_id,) + tuple(suspended_membership.get(occurrence.occurrence_id, ())), "each suspended occurrence needs exactly one suspension disposition")
    for legacy in certificate.legacy_retentions:
        if (legacy.old_position_id not in old_positions or auth is None
                or legacy.authorization_ref != auth.authorization_id
                or legacy.legacy_id not in auth.allowed_legacy_ids
                or legacy.output_position_id not in new_positions
                or legacy.carrier_states != arena.covered_support
                or not legacy.settlement_rule):
            _issue(issues, "accounting", "accounting.unauthorized_legacy", (legacy.legacy_id, legacy.old_position_id), "legacy retention must be explicitly authorized and name an old position")
    literal_keys: set[tuple[str, str, str]] = set()
    for liability in certificate.literal_liabilities:
        key = (liability.event_id, liability.kind, liability.obligation_id)
        if key in literal_keys:
            _issue(issues, "accounting", "accounting.duplicate_literal_liability", key, "literal obligation key is duplicated")
        literal_keys.add(key)
        if liability.account_id not in proposed_state.accounts or liability.amount < 0:
            _issue(issues, "accounting", "accounting.invalid_literal_liability", key, "literal liability needs a nonnegative amount and assigned account")

    # 8. Old/new compiler cores and computed eventual route coverage.
    old_compiler_valid = _compiler_valid(old_state)
    endpoint_compiler_valid = _compiler_valid(proposed_state)
    if not old_compiler_valid:
        _issue(issues, "endpoint", "endpoint.invalid_old_compiler", (old_state.compiler.compiler_id,), "old compiler/core cannot be rederived")
    if not endpoint_compiler_valid:
        _issue(issues, "endpoint", "endpoint.invalid_compiler", (proposed_state.compiler.compiler_id,), "endpoint compiler/core cannot be rederived")
    eventual_route_coverage: dict[str, tuple[str, ...]] = {}
    accounts = set(proposed_state.accounts)
    for occurrence in proposed_state.occurrences:
        if occurrence.sort not in (OccurrenceSort.CHALLENGE, OccurrenceSort.BURDEN) or not _active(occurrence):
            continue
        covering = tuple(route.route_id for route in proposed_state.routes
                         if occurrence.occurrence_id in route.covered_occurrences
                         and route.terminal_outcomes
                         and set(route.terminal_outcomes) <= {
                             "respond", "authorized-consuming-repair", "suspension",
                             "explicit-terminal-failure",
                         }
                         and route.account_id in accounts
                         and route.authorization_ref in proposed_state.authorization_ids
                         and 0 < route.consuming_cost <= proposed_state.remaining_consuming_potential)
        eventual_route_coverage[occurrence.occurrence_id] = covering
        if not covering:
            _issue(issues, "endpoint", "endpoint.uncovered_terminal", (occurrence.occurrence_id,), "route graph supplies no funded authorized consuming terminal route")
    if (old_state.noninterference.mechanism_reads_market_fields
            or old_state.noninterference.market_writes_mechanism_fields
            or proposed_state.noninterference.mechanism_reads_market_fields
            or proposed_state.noninterference.market_writes_mechanism_fields):
        _issue(issues, "endpoint", "endpoint.noninterference_failure", (), "market and answerability fields are not separated")

    # 9. External authorization, binding, endpoint recheck, and exact CAS identity.
    authorization_binding = False
    if auth is None:
        _issue(issues, "activation", "authorization.absent", (certificate.certificate_id,), "semantic coupling and compiler success do not authorize adoption")
    else:
        authorization_binding = (
            auth.proposal_id == certificate.proposal_id
            and auth.certificate_id == certificate.certificate_id
            and auth.snapshot_id == certificate.old_snapshot_id == old_state.snapshot_id
            and auth.migration_token_id in old_state.migration_tokens
            and auth.migration_token_id not in proposed_state.migration_tokens
            and auth.authorization_id in old_state.authorization_ids
        )
        if not authorization_binding:
            _issue(issues, "activation", "authorization.binding_mismatch", (auth.authorization_id, certificate.certificate_id), "authorization does not bind proposal, certificate, snapshot, and token")
    recheck = certificate.endpoint_recheck
    if recheck is None or not endpoint_compiler_valid or (
        recheck.certificate_id != certificate.certificate_id
        or recheck.shadow_state_id != certificate.shadow_state_id
        or recheck.compiler_id != proposed_state.compiler.compiler_id
    ):
        _issue(issues, "activation", "activation.endpoint_recheck_failed", (certificate.certificate_id,), "final endpoint recheck is absent, stale, or failed")
    activation = certificate.activation
    if activation.preactivation_force_state_id != old_state.state_id:
        _issue(issues, "activation", "activation.preactivation_force", (activation.preactivation_force_state_id,), "proposal compiler influenced force before activation")
    cas_valid = (
        activation.proposal_id == certificate.proposal_id
        and activation.certificate_id == certificate.certificate_id
        and activation.expected_snapshot_id == activation.observed_snapshot_id == old_state.snapshot_id
        and activation.preactivation_active_state_id == old_state.state_id
        and activation.shadow_state_id == certificate.shadow_state_id == proposed_state.state_id
        and recheck is not None and activation.endpoint_recheck_id == recheck.recheck_id
        and activation.final_active_state_id == proposed_state.state_id
        and authorization_binding and endpoint_compiler_valid
    )
    if not cas_valid:
        _issue(issues, "activation", "activation.partial_or_early_swap", (activation.preactivation_active_state_id, activation.final_active_state_id), "compare-and-swap identities do not describe one certified atomic activation")

    results = {name: CheckResult(name, not issues[name], tuple(issues[name])) for name in CHECKS}
    witnesses = tuple(witness for name in CHECKS for witness in issues[name])
    return VerificationReport(
        not witnesses, results, witnesses, reachable_roots, challenge_frontiers,
        payoff_derivation, eventual_route_coverage, old_compiler_valid,
        endpoint_compiler_valid, authorization_binding, cas_valid,
    )


def _table(states: tuple[str, ...], values: Mapping[str, int | Q]) -> tuple[Q, ...]:
    return tuple(Q(values[state]) for state in states)


def build_harm_migration() -> tuple[MigrationState, MigrationState, MigrationCertificate]:
    """Raw conservative-refinement states and certificate for the canonical trace."""
    gamma = ("none", "physical", "coercion", "frustration")
    old_semantic = ("no-harm", "harm")
    new_semantic = gamma
    old_occurrences = (
        Occurrence("k:harm", OccurrenceSort.COMMITMENT, OccurrenceStatus.LIVE, "harm", ("book:old",), True),
        Occurrence("e:harm", OccurrenceSort.ENTITLEMENT, OccurrenceStatus.LIVE, "harm", ("root:pc", "root:f"), True),
        Occurrence("w:harm-protect", OccurrenceSort.WARRANT, OccurrenceStatus.LIVE, "harm->protect", ("e:harm",), True),
        Occurrence("c:frustration", OccurrenceSort.CHALLENGE, OccurrenceStatus.LIVE, provenance=("edge:f-support",)),
        Occurrence("b:justify-frustration", OccurrenceSort.BURDEN, OccurrenceStatus.LIVE, provenance=("c:frustration",)),
        Occurrence("p:harm", OccurrenceSort.POSITION, OccurrenceStatus.LIVE, "harm", ("contract:harm",), True),
    )
    new_occurrences = (
        Occurrence("k:any-harm", OccurrenceSort.COMMITMENT, OccurrenceStatus.LIVE, "any-harm", ("k:harm", "d:k"), True),
        Occurrence("e:physical-or-coercion", OccurrenceSort.ENTITLEMENT, OccurrenceStatus.LIVE, "physical-or-coercion", ("e:harm", "root:pc+"), True),
        Occurrence("e:frustration-suspended", OccurrenceSort.ENTITLEMENT, OccurrenceStatus.SUSPENDED, "preference-frustration", ("e:harm", "root:f+", "c:frustration+"), False),
        Occurrence("w:physical-or-coercion-protect", OccurrenceSort.WARRANT, OccurrenceStatus.LIVE, "physical-or-coercion->protect", ("w:harm-protect",), True),
        Occurrence("w:frustration-suspended", OccurrenceSort.WARRANT, OccurrenceStatus.SUSPENDED, "frustration->protect", ("w:harm-protect", "c:frustration+"), False),
        Occurrence("c:frustration+", OccurrenceSort.CHALLENGE, OccurrenceStatus.LIVE, provenance=("c:frustration",)),
        Occurrence("b:justify-frustration+", OccurrenceSort.BURDEN, OccurrenceStatus.LIVE, provenance=("b:justify-frustration",)),
        Occurrence("p:any-harm", OccurrenceSort.POSITION, OccurrenceStatus.LIVE, "any-harm", ("p:harm",), True),
        Occurrence("o:preference-frustration", OccurrenceSort.OTHER, OccurrenceStatus.LIVE, "preference-frustration", ("proposal:harm-refinement",), False),
    )
    old_edges = (
        RelationEdge("edge:pc-support", RelationKind.JUSTIFICATION, ("root:pc",), ("e:harm",)),
        RelationEdge("edge:f-support", RelationKind.JUSTIFICATION, ("root:f",), ("e:harm",)),
        RelationEdge("edge:w-premise", RelationKind.WARRANT_PREMISE, ("harm",), ("w:harm-protect",)),
        RelationEdge("edge:w-consequence", RelationKind.WARRANT_CONSEQUENCE, ("w:harm-protect",), ("protect",)),
        RelationEdge("edge:authority", RelationKind.AUTHORITY_CONSEQUENCE, ("w:harm-protect",), ("protect",)),
        RelationEdge("edge:incompatibility", RelationKind.INCOMPATIBILITY, ("protect",), ("ignore",)),
        RelationEdge("edge:provenance", RelationKind.PROVENANCE, ("e:harm",), ("w:harm-protect",)),
        RelationEdge("edge:burden", RelationKind.BURDEN_SCOPE, ("b:justify-frustration",), ("edge:f-support",)),
    )
    new_edges = (
        RelationEdge("edge:pc-support+", RelationKind.JUSTIFICATION, ("root:pc+",), ("e:physical-or-coercion",)),
        RelationEdge("edge:f-support+", RelationKind.JUSTIFICATION, ("root:f+",), ("e:frustration-suspended",)),
        RelationEdge("edge:w-premise-pc+", RelationKind.WARRANT_PREMISE, ("physical-or-coercion",), ("w:physical-or-coercion-protect",)),
        RelationEdge("edge:w-premise-f+", RelationKind.WARRANT_PREMISE, ("preference-frustration",), ("w:frustration-suspended",)),
        RelationEdge("edge:w-consequence-pc+", RelationKind.WARRANT_CONSEQUENCE, ("w:physical-or-coercion-protect",), ("protect",)),
        RelationEdge("edge:w-consequence-f+", RelationKind.WARRANT_CONSEQUENCE, ("w:frustration-suspended",), ("protect",)),
        RelationEdge("edge:authority+", RelationKind.AUTHORITY_CONSEQUENCE, ("w:physical-or-coercion-protect",), ("protect",)),
        RelationEdge("edge:incompatibility+", RelationKind.INCOMPATIBILITY, ("protect",), ("ignore",)),
        RelationEdge("edge:provenance+", RelationKind.PROVENANCE, ("e:physical-or-coercion",), ("w:physical-or-coercion-protect",)),
        RelationEdge("edge:burden+", RelationKind.BURDEN_SCOPE, ("b:justify-frustration+",), ("edge:f-support+",)),
    )
    old_worlds = tuple((Q(h), Q(a)) for h in (0, 1) for a in (0, 1))
    new_worlds = tuple(
        (Q(state != "none"), Q(state in ("physical", "coercion")), Q(a))
        for state in gamma for a in (0, 1)
    )
    old_compiler = CompilerSpec(
        "compiler:old", ("harm", "protect"), old_worlds,
        (
            CompilerEndorsement("endorsement:harm-bound", (Q(1), Q(0)), Q(1, 2), "k:harm", "auth:old-book"),
            CompilerEndorsement("endorsement:protect", (Q(-1), Q(1)), Q(0), "w:harm-protect", "auth:old-book"),
        ), (Q(3, 4), Q(7, 8)), Q(1, 10),
    )
    new_compiler = CompilerSpec(
        "compiler:new", ("any-harm", "physical-or-coercion", "protect"), new_worlds,
        (
            CompilerEndorsement("endorsement:any-harm-bound", (Q(1), Q(0), Q(0)), Q(1, 2), "k:any-harm", "auth:migration"),
            CompilerEndorsement("endorsement:protect-pc", (Q(0), Q(-1), Q(1)), Q(0), "w:physical-or-coercion-protect", "auth:migration"),
        ), (Q(2, 3), Q(1, 2), Q(3, 4)), Q(1, 10),
    )
    old_state = MigrationState(
        "state:old", "snapshot:old-v1", old_semantic,
        {"harm": (Q(0), Q(1))}, {"harm": (Q(0), Q(1))}, old_occurrences,
        (EvidenceRoot("root:pc", "auth:evidence-pc"), EvidenceRoot("root:f", "auth:evidence-f")),
        old_edges,
        (ChallengeSpec("c:frustration", (TypedTarget(TargetKind.ANCESTRY_EDGE, "edge:f-support"),)),),
        (Position("p:harm", "harm", Q(-2)),), old_compiler,
        {"harm": Q(-2), "protect": Q(0)}, (), (), 0,
        ("auth:old-book", "auth:evidence-pc", "auth:evidence-f", "auth:migration"),
        ("token:migration-1",), NoninterferenceSpec(),
    )
    route = ChallengeRoute(
        "route:frustration", ("c:frustration+", "b:justify-frustration+"),
        ("respond", "authorized-consuming-repair", "suspension", "explicit-terminal-failure"),
        "account:procedure", 1, "auth:migration",
    )
    proposed_state = MigrationState(
        "state:shadow-harm-v2", "snapshot:shadow-harm-v2", new_semantic,
        {
            "physical-injury": _table(new_semantic, {s: s == "physical" for s in new_semantic}),
            "coercion": _table(new_semantic, {s: s == "coercion" for s in new_semantic}),
            "preference-frustration": _table(new_semantic, {s: s == "frustration" for s in new_semantic}),
            "any-harm": _table(new_semantic, {s: s != "none" for s in new_semantic}),
        },
        {"any-harm": _table(new_semantic, {s: s != "none" for s in new_semantic})},
        new_occurrences,
        (EvidenceRoot("root:pc+", transported_from="root:pc"), EvidenceRoot("root:f+", transported_from="root:f")),
        new_edges,
        (ChallengeSpec("c:frustration+", (TypedTarget(TargetKind.ANCESTRY_EDGE, "edge:f-support+"),)),),
        (Position("p:any-harm", "any-harm", Q(-2)),), new_compiler,
        {"any-harm": Q(-2), "physical-or-coercion": Q(0), "protect": Q(0)},
        (route,), ("account:procedure",), 1,
        ("auth:migration", "auth:evidence-pc", "auth:evidence-f"), (), NoninterferenceSpec(),
    )
    arena = ComparisonArena(
        gamma,
        {state: "no-harm" if state == "none" else "harm" for state in gamma},
        {state: state for state in gamma}, gamma,
        (SemanticReconstruction("reconstruct:harm", "harm",
                                ("physical-injury", "coercion", "preference-frustration"), "or"),),
    )
    cells = (
        DispositionCell("d:k", OccurrenceSort.COMMITMENT, ("k:harm",), ("k:any-harm",), DispositionMode.PRESERVE, "reconstruct:harm"),
        DispositionCell("d:e", OccurrenceSort.ENTITLEMENT, ("e:harm",), ("e:physical-or-coercion", "e:frustration-suspended"), DispositionMode.REFINE, "reconstruct:harm"),
        DispositionCell("d:w", OccurrenceSort.WARRANT, ("w:harm-protect",), ("w:physical-or-coercion-protect", "w:frustration-suspended"), DispositionMode.REFINE),
        DispositionCell("d:c", OccurrenceSort.CHALLENGE, ("c:frustration",), ("c:frustration+",), DispositionMode.PRESERVE),
        DispositionCell("d:b", OccurrenceSort.BURDEN, ("b:justify-frustration",), ("b:justify-frustration+",), DispositionMode.PRESERVE),
        DispositionCell("d:p", OccurrenceSort.POSITION, ("p:harm",), ("p:any-harm",), DispositionMode.PRESERVE, "reconstruct:harm"),
        DispositionCell("d:o", OccurrenceSort.OTHER, (), ("o:preference-frustration",), DispositionMode.INTRODUCE, "reconstruct:harm"),
    )
    edge_transports = (
        EdgeTransport("edge:pc-support", ("edge:pc-support+",)),
        EdgeTransport("edge:f-support", ("edge:f-support+",)),
        EdgeTransport("edge:w-premise", ("edge:w-premise-pc+", "edge:w-premise-f+")),
        EdgeTransport("edge:w-consequence", ("edge:w-consequence-pc+", "edge:w-consequence-f+")),
        EdgeTransport("edge:authority", ("edge:authority+",), "suspension:frustration-force"),
        EdgeTransport("edge:incompatibility", ("edge:incompatibility+",)),
        EdgeTransport("edge:provenance", ("edge:provenance+",), "suspension:frustration-force"),
        EdgeTransport("edge:burden", ("edge:burden+",)),
    )
    authorization = AuthorizationRecord(
        "auth:migration", "proposal:harm-refinement", "certificate:harm-refinement-v1",
        "snapshot:old-v1", "token:migration-1", (),
        ("suspension:frustration-entitlement", "suspension:frustration-force"), (), (),
    )
    recheck = EndpointRecheck(
        "recheck:endpoint-harm-v2", "certificate:harm-refinement-v1",
        "state:shadow-harm-v2", "compiler:new",
    )
    activation = ActivationRecord(
        "proposal:harm-refinement", "certificate:harm-refinement-v1",
        "snapshot:old-v1", "snapshot:old-v1", "state:old", "state:old",
        "state:shadow-harm-v2", "recheck:endpoint-harm-v2", "state:shadow-harm-v2",
    )
    certificate = MigrationCertificate(
        "certificate:harm-refinement-v1", "proposal:harm-refinement", "snapshot:old-v1",
        "state:shadow-harm-v2", arena, cells, edge_transports,
        (("harm", "any-harm"), ("protect", "protect")),
        (("harm", ("physical-or-coercion", "preference-frustration")),
         ("protect", ("protect",)), ("ignore", ("ignore",))), (), (),
        (SuspensionEntry(
            "suspension:frustration-entitlement", "d:e",
            ("e:frustration-suspended",), ("route:frustration",),
            "auth:migration", True, False,
        ), SuspensionEntry(
            "suspension:frustration-force", "d:w",
            ("w:frustration-suspended",),
            ("route:frustration",), "auth:migration", True, False,
        ),), (), (), (), authorization, recheck, activation,
    )
    return old_state, proposed_state, certificate


def exact_migration_trace() -> Mapping[str, object]:
    old_state, proposed_state, certificate = build_harm_migration()
    return {
        "old_state": old_state,
        "proposed_state": proposed_state,
        "arena": certificate.arena,
        "certificate": certificate,
        "authorization": certificate.authorization,
        "activation": certificate.activation,
        "report": verify_migration(old_state, proposed_state, certificate),
    }


def malformed_harm_migration(case: str) -> tuple[MigrationState, MigrationState, MigrationCertificate]:
    """Make one local raw-field mutation for verifier failure tests."""
    old, new, cert = build_harm_migration()
    if case == "missing-ancestry":
        new = replace(new, relation_edges=tuple(edge for edge in new.relation_edges if edge.edge_id != "edge:pc-support+"))
    elif case == "uncovered-split-challenge":
        old = replace(old, challenges=(ChallengeSpec("c:frustration", (TypedTarget(TargetKind.OCCURRENCE, "e:harm"),)),))
        new = replace(new, challenges=(ChallengeSpec("c:frustration+", (TypedTarget(TargetKind.OCCURRENCE, "e:frustration-suspended"),)),))
    elif case == "hidden-incompatibility":
        def merged_nodes(nodes: tuple[str, ...]) -> tuple[str, ...]:
            return tuple("merged:neutral" if node in ("protect", "ignore") else node for node in nodes)
        new = replace(new, relation_edges=tuple(
            replace(edge, sources=merged_nodes(edge.sources), targets=merged_nodes(edge.targets))
            for edge in new.relation_edges if edge.edge_id != "edge:incompatibility+"
        ))
        node_transports = tuple(
            (old_node, ("merged:neutral",)) if old_node in ("protect", "ignore") else (old_node, images)
            for old_node, images in cert.semantic_node_transports
        )
        cert = replace(cert, semantic_node_transports=node_transports)
    elif case == "changed-payoff":
        table = list(new.payoff_tables["any-harm"])
        table[new.semantic_states.index("frustration")] = Q(0)
        new = replace(new, payoff_tables={**new.payoff_tables, "any-harm": tuple(table)})
    elif case == "preactivation-force":
        cert = replace(cert, activation=replace(cert.activation, preactivation_force_state_id=new.state_id))
    elif case == "inexpressibility-discharge":
        cells = tuple(
            replace(cell, outputs=(), mode=DispositionMode.DISCHARGE, authorization_ref="auth:migration")
            if cell.cell_id == "d:c" else cell for cell in cert.cells
        )
        cert = replace(cert, cells=cells)
    elif case == "duplicate-loss":
        loss = LossEntry("loss:x", "semantic", "d:w", "same lost consequence", "auth:migration", True, "remove force")
        cert = replace(cert, losses=(loss, loss))
    elif case == "coupling-as-authorization":
        cert = replace(cert, authorization=None)
    elif case == "lossless-collapse":
        collapsed_projection = {state: "none" for state in cert.arena.states}
        cert = replace(cert, arena=replace(cert.arena, new_projection=collapsed_projection))
    elif case == "duplicate-consuming-cell":
        duplicate = DispositionCell("d:k-duplicate", OccurrenceSort.COMMITMENT, ("k:harm",), ("k:any-harm",), DispositionMode.PRESERVE)
        cert = replace(cert, cells=cert.cells + (duplicate,))
    elif case == "partial-activation":
        cert = replace(cert, cells=tuple(cell for cell in cert.cells if cell.cell_id != "d:c"))
    elif case == "late-burden-reassignment":
        new = replace(new, challenges=(ChallengeSpec("c:frustration+", (TypedTarget(TargetKind.ANCESTRY_EDGE, "edge:pc-support+"),)),))
    elif case == "uncertified-early-swap":
        cert = replace(cert, activation=replace(cert.activation, preactivation_active_state_id=new.state_id), endpoint_recheck=None)
    elif case == "unauthorized-loss":
        loss = LossEntry("loss:x", "semantic", "d:w", "frustration consequence", "auth:migration", True, "remove force")
        cert = replace(cert, losses=(loss,))
    elif case == "duplicated-authority":
        occurrences = tuple(
            replace(item, practical_authority=True)
            if item.occurrence_id == "e:frustration-suspended" else item
            for item in new.occurrences
        )
        new = replace(new, occurrences=occurrences)
    elif case == "unsupported-terminal-coverage":
        new = replace(new, routes=())
    else:
        raise ValueError(case)
    return old, new, cert


def authorized_legacy_harm_migration() -> tuple[MigrationState, MigrationState, MigrationCertificate]:
    """The changed-payoff variant repaired by retaining the old contract on Gamma."""
    old, new, cert = malformed_harm_migration("changed-payoff")
    legacy_id = "legacy:harm-contract"
    positions = tuple(
        replace(position, payoff_ref=legacy_id)
        if position.occurrence_id == "p:any-harm" else position
        for position in new.positions
    )
    occurrences = tuple(
        replace(occurrence, reference=legacy_id)
        if occurrence.occurrence_id == "p:any-harm" else occurrence
        for occurrence in new.occurrences
    )
    new = replace(new, positions=positions, occurrences=occurrences)
    authorization = replace(
        cert.authorization,
        allowed_legacy_ids=(legacy_id,),
    )
    legacy = LegacyRetention(
        legacy_id, "p:harm", "p:any-harm", cert.arena.covered_support,
        (Q(0), Q(1), Q(1), Q(1)), Q(-2), Q(2, 3),
        "settle the old harm indicator on the retained Gamma carrier",
        authorization.authorization_id,
    )
    cert = replace(cert, authorization=authorization, legacy_retentions=(legacy,))
    return old, new, cert


def constant_on_fibers(states: Sequence[str], quotient: Mapping[str, str],
                       values: Mapping[str, Q]) -> bool:
    return all(quotient[left] != quotient[right] or values[left] == values[right]
               for left in states for right in states)


def local_bridge_has_unique_future_extension() -> bool:
    """A local bridge record does not choose between incompatible later spans."""
    local_record = ("old:a", "current:b")
    left_extension = local_record + ("future:c0",)
    right_extension = local_record + ("future:c1",)
    return left_extension == right_extension
