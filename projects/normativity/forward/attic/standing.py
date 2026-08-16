"""Provenance-sensitive standing transport across a disposition cell.

`CM-N1` in `COMPOSITION_THEORY.md` blocks standing laundering by requiring every
output of a cell to be no stronger than *every* input.  That is sufficient but
universally quantified: it treats a many-to-many cell as if each output
inherited its standing from each input.  This module supplies the finer object —
one typed transport plan per cell, carrying separate semantic, standing,
authority, and burden relations — and the predicate `check_transport_plan` that
decides it.

The plan is deliberately *not* part of `MigrationCertificate`.  Nothing in
`src/migration.py` is changed.  §6 of `STANDING_TRANSPORT.md` states what a
future one-step certificate would have to carry instead.

Everything here is finite and exact.  No verdict is stored: a plan's Boolean
fields are claims to be checked, never sources of truth.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import permutations
from typing import Iterable, Mapping, Sequence

from src.composition import STANDING_ORDER, MigrationHistory
from src.migration import (
    DispositionMode,
    MigrationCertificate,
    MigrationState,
    OccurrenceSort,
    OccurrenceStatus,
)

TRANSPORT_CONDITIONS = (
    "sponsorship",
    "authority",
    "lineage",
    "allocation",
    "burden",
    "separation",
    "hygiene",
)

TERMINATION_KINDS = ("response", "retraction", "legacy", "loss")
GRANT_KINDS = ("introduction", "reinstatement", "authority", "authority-split")
_RESOLVING_KINDS = ("response", "retraction")
_STANDING_GRANTS = ("introduction", "reinstatement")


# --------------------------------------------------------------------------
# Facts and the transport plan
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class OccurrenceFacts:
    """The three deontic bits a transport plan must account for."""

    occurrence_id: str
    status: OccurrenceStatus
    practical_authority: bool = False
    unresolved_burden: bool = False


@dataclass(frozen=True)
class CellFacts:
    cell_id: str
    inputs: tuple[OccurrenceFacts, ...]
    outputs: tuple[OccurrenceFacts, ...]


@dataclass(frozen=True)
class SupportEdge:
    source_id: str
    target_id: str


@dataclass(frozen=True)
class ScopedGrant:
    """A positive warrant, scoped to one cell output.

    A grant is not a disposition.  Terminating an input's burden never supplies
    one; only an authorization record naming this output does.
    """

    grant_id: str
    kind: str
    output_id: str
    basis_ref: str
    authorization_ref: str


@dataclass(frozen=True)
class ScopedTermination:
    """A terminal outcome scoped to one *input dimension*, not to the cell.

    `TerminalDisposition` in the frozen certificate names only a cell, so one
    witness excuses every input of a multi-input terminal cell.  Scoping is the
    repair; see `STANDING_TRANSPORT.md` §4.
    """

    termination_id: str
    input_id: str
    kind: str
    witness_ref: str
    authorization_ref: str
    burden_resolved: bool
    carrier_ref: str | None = None


@dataclass(frozen=True)
class BurdenRoute:
    input_id: str
    carrier_output_id: str | None = None
    termination_id: str | None = None


@dataclass(frozen=True)
class StandingTransportPlan:
    cell_id: str
    semantic_support: tuple[SupportEdge, ...] = ()
    standing_support: tuple[SupportEdge, ...] = ()
    authority_support: tuple[SupportEdge, ...] = ()
    burden_routes: tuple[BurdenRoute, ...] = ()
    terminations: tuple[ScopedTermination, ...] = ()
    grants: tuple[ScopedGrant, ...] = ()


@dataclass(frozen=True)
class TransportCounterwitness:
    condition: str
    code: str
    ids: tuple[str, ...]
    detail: str


@dataclass(frozen=True)
class TransportVerdict:
    cell_id: str
    accepted: bool
    counterwitnesses: tuple[TransportCounterwitness, ...]
    standing_sponsors: Mapping[str, tuple[str, ...]]
    authority_assignment: Mapping[str, str]
    burden_outcomes: Mapping[str, str]


def _issue(store: list[TransportCounterwitness], condition: str, code: str,
           ids: Iterable[str], detail: str) -> None:
    store.append(TransportCounterwitness(condition, code, tuple(ids), detail))


def _order(facts: OccurrenceFacts) -> int:
    return STANDING_ORDER[facts.status]


def _targets(edges: Sequence[SupportEdge], target: str) -> tuple[str, ...]:
    return tuple(edge.source_id for edge in edges if edge.target_id == target)


# --------------------------------------------------------------------------
# The provenance-sensitive predicate
# --------------------------------------------------------------------------


def check_transport_plan(cell: CellFacts, plan: StandingTransportPlan) -> TransportVerdict:
    """Decide one declared transport plan against the seven typed conditions."""
    issues: list[TransportCounterwitness] = []
    inputs = {item.occurrence_id: item for item in cell.inputs}
    outputs = {item.occurrence_id: item for item in cell.outputs}
    terminations = {item.termination_id: item for item in plan.terminations}

    if plan.cell_id != cell.cell_id:
        _issue(issues, "hygiene", "standing.plan_cell_mismatch",
               (plan.cell_id, cell.cell_id), "the plan does not describe this cell")

    # Hygiene: every declared endpoint exists, and no assertion is idle.
    for label, edges in (("semantic", plan.semantic_support),
                         ("standing", plan.standing_support),
                         ("authority", plan.authority_support)):
        for edge in edges:
            if edge.source_id not in inputs or edge.target_id not in outputs:
                _issue(issues, "hygiene", "standing.support_edge_unknown",
                       (label, edge.source_id, edge.target_id),
                       f"{label} support names an endpoint that is not in the cell")
    routed_inputs = [route.input_id for route in plan.burden_routes]
    for route in plan.burden_routes:
        if route.input_id not in inputs:
            _issue(issues, "hygiene", "standing.route_source_unknown", (route.input_id,),
                   "a burden route names an occurrence that is not an input")
        if routed_inputs.count(route.input_id) > 1:
            _issue(issues, "hygiene", "standing.duplicate_burden_route", (route.input_id,),
                   "one input carries at most one burden route")
        if route.carrier_output_id is not None and route.termination_id is not None:
            _issue(issues, "hygiene", "standing.contradictory_burden_route",
                   (route.input_id, route.carrier_output_id, route.termination_id),
                   "a burden cannot both continue on a carrier and terminate")
        if route.carrier_output_id is not None and route.carrier_output_id not in outputs:
            _issue(issues, "hygiene", "standing.route_carrier_unknown",
                   (route.input_id, route.carrier_output_id),
                   "a burden route names a carrier that is not an output")
        if route.termination_id is not None and route.termination_id not in terminations:
            _issue(issues, "hygiene", "standing.route_termination_unknown",
                   (route.input_id, route.termination_id),
                   "a burden route names a termination the plan does not declare")
    used_terminations = {route.termination_id for route in plan.burden_routes}
    for termination in plan.terminations:
        if termination.input_id not in inputs:
            _issue(issues, "hygiene", "standing.termination_source_unknown",
                   (termination.termination_id, termination.input_id),
                   "a termination names an occurrence that is not an input")
        if termination.kind not in TERMINATION_KINDS:
            _issue(issues, "hygiene", "standing.termination_kind_unknown",
                   (termination.termination_id, termination.kind), "unknown termination kind")
        if termination.termination_id not in used_terminations:
            _issue(issues, "hygiene", "standing.unused_assertion",
                   (termination.termination_id,),
                   "a declared termination is not reached by any burden route")
        source = inputs.get(termination.input_id)
        if source is not None and not source.unresolved_burden:
            _issue(issues, "hygiene", "standing.contradictory_assertion",
                   (termination.termination_id, termination.input_id),
                   "a termination resolves a burden the input does not carry")
    used_grants: set[str] = set()

    # 1. Standing sponsorship.  A live or suspended output needs a named input
    #    sponsor at least as strong, or a reinstatement grant scoped to it.
    standing_sponsors: dict[str, tuple[str, ...]] = {}
    for identifier, output in outputs.items():
        if _order(output) <= STANDING_ORDER[OccurrenceStatus.TERMINAL]:
            standing_sponsors[identifier] = ()
            continue
        declared = _targets(plan.standing_support, identifier)
        sufficient = tuple(
            source for source in declared
            if source in inputs and _order(inputs[source]) >= _order(output))
        standing_sponsors[identifier] = sufficient
        if sufficient:
            continue
        reinstatement = tuple(
            grant for grant in plan.grants
            if grant.kind in _STANDING_GRANTS and grant.output_id == identifier)
        for grant in reinstatement:
            if grant.kind == "introduction" and cell.inputs:
                _issue(issues, "lineage", "standing.introduction_with_inputs",
                       (grant.grant_id, identifier),
                       "only a cell with no inputs may ground standing in an introduction")
        if not reinstatement:
            semantic = _targets(plan.semantic_support, identifier)
            if semantic and not declared:
                _issue(issues, "separation", "standing.semantic_support_is_not_sponsorship",
                       (identifier,) + semantic,
                       "semantic contribution does not sponsor entitlement standing")
            else:
                _issue(issues, "sponsorship", "standing.unsponsored_standing",
                       (identifier,) + declared,
                       "a live or suspended output has no input sponsor of sufficient standing")
            continue
        for grant in reinstatement:
            used_grants.add(grant.grant_id)
            if not grant.basis_ref or not grant.authorization_ref:
                _issue(issues, "sponsorship", "standing.reinstatement_without_basis",
                       (grant.grant_id, identifier),
                       "a reinstatement grant needs a named evidential basis and authorization")

    # 2. Practical-authority sponsorship, separate from standing sponsorship.
    authoritative_outputs = tuple(
        identifier for identifier, output in outputs.items() if output.practical_authority)
    authority_assignment: dict[str, str] = {}
    candidates: dict[str, tuple[str, ...]] = {}
    for identifier in authoritative_outputs:
        output = outputs[identifier]
        declared = _targets(plan.authority_support, identifier)
        standing = set(_targets(plan.standing_support, identifier))
        eligible: list[str] = []
        for source in declared:
            item = inputs.get(source)
            if item is None:
                continue
            if source not in standing:
                _issue(issues, "lineage", "standing.authority_without_standing",
                       (identifier, source),
                       "an authority sponsor must also sponsor the output's standing")
                continue
            if not item.practical_authority:
                continue
            if _order(item) < _order(output):
                _issue(issues, "authority", "standing.authority_sponsor_too_weak",
                       (identifier, source),
                       "an authority sponsor cannot be weaker in standing than the output")
                continue
            eligible.append(source)
        candidates[identifier] = tuple(eligible)
    grant_backed = {
        identifier: tuple(
            grant for grant in plan.grants
            if grant.kind in ("authority", "authority-split") and grant.output_id == identifier)
        for identifier in authoritative_outputs
    }
    needs_sponsor = tuple(
        identifier for identifier in authoritative_outputs if not grant_backed[identifier])
    for identifier in authoritative_outputs:
        for grant in grant_backed[identifier]:
            used_grants.add(grant.grant_id)
            if not grant.basis_ref or not grant.authorization_ref:
                _issue(issues, "authority", "standing.authority_grant_without_basis",
                       (grant.grant_id, identifier),
                       "an authority grant needs a named basis and authorization")
            authority_assignment[identifier] = grant.grant_id
            if _injective_assignment(needs_sponsor + (identifier,), candidates) is not None:
                _issue(issues, "hygiene", "standing.unused_assertion",
                       (grant.grant_id, identifier),
                       "an authority grant licenses an output an input sponsor already licenses")

    # 3/4. One authority source licenses at most one authoritative output.
    assignment = _injective_assignment(needs_sponsor, candidates)
    if assignment is None:
        starved = tuple(
            identifier for identifier in needs_sponsor if not candidates[identifier])
        if starved:
            for identifier in starved:
                declared = _targets(plan.authority_support, identifier)
                semantic = _targets(plan.semantic_support, identifier)
                if semantic and not declared:
                    _issue(issues, "separation", "standing.semantic_support_is_not_authority",
                           (identifier,) + semantic,
                           "semantic contribution does not sponsor practical authority")
                else:
                    _issue(issues, "authority", "standing.unsponsored_authority",
                           (identifier,) + declared,
                           "an authoritative output has no authoritative sponsor and no grant")
        else:
            _issue(issues, "allocation", "standing.authority_duplicated",
                   needs_sponsor + tuple(sorted({s for v in candidates.values() for s in v})),
                   "authoritative outputs outnumber the distinct authority sources that license them")
    else:
        authority_assignment.update(assignment)
    for identifier in outputs:
        if identifier not in authoritative_outputs and _targets(plan.authority_support, identifier):
            _issue(issues, "hygiene", "standing.contradictory_assertion",
                   (identifier,) + _targets(plan.authority_support, identifier),
                   "authority support is declared for a nonauthoritative output")
    grant_ids = [grant.grant_id for grant in plan.grants]
    for identifier in outputs:
        for kinds, label in ((_STANDING_GRANTS, "standing"),
                             (("authority", "authority-split"), "authority")):
            licences = [grant.grant_id for grant in plan.grants
                        if grant.kind in kinds and grant.output_id == identifier]
            if len(licences) > 1:
                _issue(issues, "hygiene", "standing.unused_assertion",
                       (identifier,) + tuple(sorted(licences[1:])),
                       f"one output takes at most one {label} licence")
    for grant in plan.grants:
        if grant.kind not in GRANT_KINDS:
            _issue(issues, "hygiene", "standing.grant_kind_unknown",
                   (grant.grant_id, grant.kind), "unknown grant kind")
        if grant.output_id not in outputs:
            _issue(issues, "hygiene", "standing.grant_target_unknown",
                   (grant.grant_id, grant.output_id),
                   "a grant names an output that is not in the cell")
        if grant_ids.count(grant.grant_id) > 1:
            _issue(issues, "allocation", "standing.grant_reused", (grant.grant_id,),
                   "one scoped grant licenses at most one output")
        if grant.grant_id not in used_grants and grant.output_id in outputs:
            _issue(issues, "hygiene", "standing.unused_assertion", (grant.grant_id,),
                   "a declared grant licenses nothing the cell needed")

    # 5. Burden conservation, scoped to the input dimension that carries it.
    burden_outcomes: dict[str, str] = {}
    routes = {route.input_id: route for route in plan.burden_routes}
    for identifier, item in inputs.items():
        if not item.unresolved_burden:
            continue
        route = routes.get(identifier)
        if route is None or (route.carrier_output_id is None and route.termination_id is None):
            burden_outcomes[identifier] = "vanished"
            _issue(issues, "burden", "standing.burden_vanished", (identifier,),
                   "an input with an unresolved burden has no carrier and no termination")
            continue
        if route.carrier_output_id is not None:
            carrier = outputs.get(route.carrier_output_id)
            burden_outcomes[identifier] = f"carried:{route.carrier_output_id}"
            if carrier is None:
                continue
            if (_order(carrier) <= STANDING_ORDER[OccurrenceStatus.TERMINAL]
                    or not carrier.unresolved_burden):
                _issue(issues, "burden", "standing.burden_carrier_does_not_carry",
                       (identifier, route.carrier_output_id),
                       "a continuing burden must land on an active output that still carries it")
                continue
            # Burden-local monotonicity: standing may not strengthen along the
            # lineage that still owes the answer.  This is `CM-N1` restricted to
            # the burden-carrying pairs instead of every input-output pair.
            if _order(carrier) > _order(item):
                _issue(issues, "burden", "standing.burden_carrier_stronger",
                       (identifier, route.carrier_output_id),
                       "an unresolved burden cannot be carried by an output of stronger standing")
            if carrier.practical_authority and not item.practical_authority:
                _issue(issues, "burden", "standing.burden_carrier_authoritative",
                       (identifier, route.carrier_output_id),
                       "an unresolved burden cannot be carried by a newly authoritative output")
            continue
        termination = terminations.get(route.termination_id or "")
        if termination is None:
            burden_outcomes[identifier] = "vanished"
            _issue(issues, "burden", "standing.burden_vanished",
                   (identifier, route.termination_id or ""),
                   "a burden route names a termination the plan does not declare")
            continue
        burden_outcomes[identifier] = f"terminated:{termination.termination_id}"
        if termination.input_id != identifier:
            _issue(issues, "burden", "standing.termination_unscoped",
                   (termination.termination_id, termination.input_id, identifier),
                   "a termination discharges only the input dimension it names")
        if not termination.witness_ref or not termination.authorization_ref:
            _issue(issues, "burden", "standing.termination_unwitnessed",
                   (termination.termination_id, identifier),
                   "a termination needs a public witness and an authorization")
        if termination.burden_resolved and termination.kind not in _RESOLVING_KINDS:
            _issue(issues, "burden", "standing.termination_kind_cannot_resolve",
                   (termination.termination_id, termination.kind),
                   "only a response or a retraction resolves a burden")
        if not termination.burden_resolved and not termination.carrier_ref:
            _issue(issues, "burden", "standing.unresolved_termination_without_carrier",
                   (termination.termination_id, identifier),
                   "an unresolved burden that does not continue needs a retained carrier")

    accepted = not issues
    return TransportVerdict(
        cell.cell_id, accepted, tuple(issues), standing_sponsors,
        authority_assignment, burden_outcomes,
    )


def _injective_assignment(
    targets: Sequence[str], candidates: Mapping[str, Sequence[str]],
) -> dict[str, str] | None:
    """Exact maximum matching by exhaustive search; cells here have at most two outputs."""
    if not targets:
        return {}
    sources = sorted({source for target in targets for source in candidates[target]})
    if len(sources) < len(targets):
        return None
    for choice in permutations(sources, len(targets)):
        if all(source in candidates[target] for target, source in zip(targets, choice)):
            return dict(zip(targets, choice))
    return None


# --------------------------------------------------------------------------
# The canonical plan, and satisfiability
# --------------------------------------------------------------------------


def available_grants(cell: CellFacts, *, basis: str = "basis:record",
                     authorization: str = "auth:transport") -> tuple[ScopedGrant, ...]:
    """One well-formed reinstatement and one authority grant per output.

    This is the *supply* a certificate might make.  The plan constructor may
    attach a supplied record; it may never invent one.
    """
    kind = "introduction" if not cell.inputs else "reinstatement"
    return tuple(
        ScopedGrant(f"grant:reinstate:{target.occurrence_id}", kind,
                    target.occurrence_id, basis, authorization)
        for target in cell.outputs
    ) + tuple(
        ScopedGrant(f"grant:authority:{target.occurrence_id}", "authority",
                    target.occurrence_id, basis, authorization)
        for target in cell.outputs
    )


def available_terminations(cell: CellFacts, *, kind: str = "response",
                           witness: str = "witness:response",
                           authorization: str = "auth:transport",
                           resolved: bool = True) -> tuple[ScopedTermination, ...]:
    """One well-formed scoped termination per burdened input."""
    return tuple(
        ScopedTermination(f"termination:{item.occurrence_id}", item.occurrence_id,
                          kind, witness, authorization, resolved, None)
        for item in cell.inputs if item.unresolved_burden
    )


def canonical_plan(cell: CellFacts, *, grants: Sequence[ScopedGrant] = (),
                   terminations: Sequence[ScopedTermination] = ()) -> StandingTransportPlan:
    """The most permissive plan the cell's facts and the supplied records support.

    Semantic support is total; standing support names every input at least as
    strong as the output; authority support names every authoritative input that
    also sponsors standing; a burden continues on a suspended carrier when one
    exists and otherwise reaches a *supplied* termination.  Records are attached
    only where the cell cannot do without them, so a supplied record that is not
    needed is left off and no assertion is idle.  `STANDING_TRANSPORT.md` §3
    shows this plan is maximally permissive, so satisfiability is decided here.
    """
    semantic = tuple(
        SupportEdge(source.occurrence_id, target.occurrence_id)
        for source in cell.inputs for target in cell.outputs)
    standing: list[SupportEdge] = []
    authority: list[SupportEdge] = []
    attached: list[ScopedGrant] = []
    for target in cell.outputs:
        if _order(target) <= STANDING_ORDER[OccurrenceStatus.TERMINAL]:
            continue
        strong = [item for item in cell.inputs if _order(item) >= _order(target)]
        standing.extend(SupportEdge(item.occurrence_id, target.occurrence_id) for item in strong)
        if target.practical_authority:
            authority.extend(
                SupportEdge(item.occurrence_id, target.occurrence_id)
                for item in strong if item.practical_authority)
        if not strong:
            attached.extend(
                grant for grant in grants
                if grant.kind in _STANDING_GRANTS and grant.output_id == target.occurrence_id)
    authoritative = tuple(t.occurrence_id for t in cell.outputs if t.practical_authority)
    candidates = {
        identifier: _targets(tuple(authority), identifier) for identifier in authoritative}
    for identifier in _minimal_unmatched(authoritative, candidates):
        licences = [grant for grant in grants
                    if grant.kind in ("authority", "authority-split")
                    and grant.output_id == identifier]
        if not licences:
            # No grant is on offer, so the maximal authority support stands and
            # the predicate reports the duplication rather than hiding it.
            continue
        attached.extend(licences)
        authority = [edge for edge in authority if edge.target_id != identifier]
    routes: list[BurdenRoute] = []
    used: list[ScopedTermination] = []
    for item in cell.inputs:
        if not item.unresolved_burden:
            continue
        carrier = next((target for target in cell.outputs
                        if target.unresolved_burden
                        and _order(target) > STANDING_ORDER[OccurrenceStatus.TERMINAL]
                        and _order(target) <= _order(item)
                        and (item.practical_authority or not target.practical_authority)), None)
        if carrier is not None:
            routes.append(BurdenRoute(item.occurrence_id, carrier.occurrence_id, None))
            continue
        supplied = next((t for t in terminations if t.input_id == item.occurrence_id), None)
        if supplied is not None:
            used.append(supplied)
            routes.append(BurdenRoute(item.occurrence_id, None, supplied.termination_id))
        else:
            routes.append(BurdenRoute(item.occurrence_id, None, None))
    return StandingTransportPlan(
        cell.cell_id, semantic, tuple(standing), tuple(authority),
        tuple(routes), tuple(used), tuple(attached),
    )


def _minimal_unmatched(targets: Sequence[str],
                       candidates: Mapping[str, Sequence[str]]) -> tuple[str, ...]:
    """The fewest outputs that must be grant-backed for an injective assignment."""
    ordered = tuple(targets)
    for size in range(len(ordered) + 1):
        for excluded in permutations(ordered, size):
            keep = tuple(t for t in ordered if t not in excluded)
            if _injective_assignment(keep, candidates) is not None:
                return tuple(sorted(set(excluded)))
    return ordered


def transport_accepts(cell: CellFacts, *, allow_grants: bool = False,
                      allow_terminations: bool = False) -> bool:
    """Is any declared plan for this cell accepted, given the permitted records?"""
    plan = canonical_plan(
        cell,
        grants=available_grants(cell) if allow_grants else (),
        terminations=available_terminations(cell) if allow_terminations else (),
    )
    return check_transport_plan(cell, plan).accepted


def cm_n1_accepts(cell: CellFacts, *, cell_has_terminal_disposition: bool = False,
                  granted_outputs: Sequence[str] = ()) -> bool:
    """`CM-N1` exactly as `verify_history` applies it, for comparison."""
    if cell_has_terminal_disposition:
        return True
    for source in cell.inputs:
        for target in cell.outputs:
            if target.occurrence_id in granted_outputs:
                continue
            if _order(target) > _order(source):
                return False
            if target.practical_authority and not source.practical_authority:
                return False
    return True


# --------------------------------------------------------------------------
# Deriving plans from the frozen certificate vocabulary
# --------------------------------------------------------------------------


def occurrence_facts(state: MigrationState,
                     producing_certificate: MigrationCertificate | None) -> dict[str, OccurrenceFacts]:
    """Read the three deontic bits off a raw state and the certificate that made it.

    The unresolved-burden bit is the one datum the state does not carry: it lives
    in the producing certificate's suspension entries.  For the initial state it
    is derived from active burden-sorted occurrences.
    """
    remaining: set[str] = set()
    if producing_certificate is not None:
        for entry in producing_certificate.suspensions:
            if entry.burdens_remain:
                remaining.update(entry.output_occurrence_ids)
    facts: dict[str, OccurrenceFacts] = {}
    for occurrence in state.occurrences:
        burden = occurrence.occurrence_id in remaining or (
            occurrence.sort == OccurrenceSort.BURDEN
            and occurrence.status != OccurrenceStatus.TERMINAL)
        facts[occurrence.occurrence_id] = OccurrenceFacts(
            occurrence.occurrence_id, occurrence.status,
            occurrence.practical_authority, burden)
    return facts


def cell_facts(certificate: MigrationCertificate,
               before: Mapping[str, OccurrenceFacts],
               after: Mapping[str, OccurrenceFacts]) -> tuple[CellFacts, ...]:
    return tuple(
        CellFacts(
            cell.cell_id,
            tuple(before[i] for i in cell.inputs if i in before),
            tuple(after[o] for o in cell.outputs if o in after),
        )
        for cell in certificate.cells
    )


def derive_plans(certificate: MigrationCertificate,
                 before: Mapping[str, OccurrenceFacts],
                 after: Mapping[str, OccurrenceFacts]) -> tuple[StandingTransportPlan, ...]:
    """Canonical transport plans read off the raw certificate, with real records.

    Grants come from `AuthorizationRecord.authority_grants`; terminations come
    from `TerminalDisposition`, which names only a cell — so a multi-input
    terminal cell yields an unscoped termination, which the predicate rejects.
    """
    authorization = certificate.authorization
    granted = set(authorization.authority_grants if authorization else ())
    authorization_id = authorization.authorization_id if authorization else ""
    plans: list[StandingTransportPlan] = []
    for cell, facts in zip(certificate.cells, cell_facts(certificate, before, after)):
        supplied_grants = tuple(
            ScopedGrant(f"grant:{grant_cell}:{output}", "authority", output,
                        f"authority-grant:{grant_cell}", authorization_id)
            for (grant_cell, output) in sorted(granted) if grant_cell == cell.cell_id
        )
        if cell.mode == DispositionMode.INTRODUCE:
            # An introduced occurrence has no ancestry; its standing is grounded
            # in the certificate's own authorization, exactly as `AM-J3`
            # conclusion 3 requires of a newly authorized evidence root.
            supplied_grants += tuple(
                ScopedGrant(f"grant:introduce:{output}", "introduction", output,
                            certificate.proposal_id, authorization_id)
                for output in cell.outputs
            )
        plan = canonical_plan(facts, grants=supplied_grants)
        burdened = tuple(i for i in cell.inputs
                         if i in before and before[i].unresolved_burden)
        carried = {route.input_id for route in plan.burden_routes
                   if route.carrier_output_id is not None}
        loose = tuple(i for i in burdened if i not in carried)
        disposition = next((item for item in certificate.terminal_dispositions
                            if item.source_cell_id == cell.cell_id), None)
        if loose and disposition is not None:
            # `TerminalDisposition` names a cell, not an input dimension.  Only a
            # single-input cell determines its own scope; otherwise the plan
            # inherits an unscoped termination and the predicate says so.
            scope = cell.inputs[0] if len(cell.inputs) == 1 else f"cell-scope:{cell.cell_id}"
            termination = ScopedTermination(
                disposition.disposition_id, scope,
                "response" if disposition.kind == "discharge" else "retraction",
                disposition.witness_ref, disposition.authorization_ref,
                disposition.burdens_resolved, None)
            plan = replace(
                plan,
                terminations=(termination,),
                burden_routes=tuple(
                    route for route in plan.burden_routes if route.input_id not in loose)
                + tuple(BurdenRoute(i, None, termination.termination_id) for i in loose),
            )
        plans.append(plan)
    return tuple(plans)


@dataclass(frozen=True)
class StepTransportReport:
    step_id: str
    accepted: bool
    verdicts: tuple[TransportVerdict, ...]
    counterwitnesses: tuple[TransportCounterwitness, ...]


@dataclass(frozen=True)
class HistoryTransportReport:
    history_id: str
    accepted: bool
    steps: tuple[StepTransportReport, ...]
    counterwitnesses: tuple[TransportCounterwitness, ...]
    cm_n1_rejected_cells: tuple[str, ...]
    transport_rejected_cells: tuple[str, ...]


def verify_history_transport(history: MigrationHistory) -> HistoryTransportReport:
    """Run the provenance-sensitive predicate over every cell of a linear history."""
    steps: list[StepTransportReport] = []
    all_witnesses: list[TransportCounterwitness] = []
    cm_rejected: list[str] = []
    transport_rejected: list[str] = []
    previous: MigrationCertificate | None = None
    for index, step in enumerate(history.steps):
        node_before = history.nodes[index]
        node_after = history.nodes[index + 1]
        state_before = node_before.departure_state
        state_after = node_after.arrival_state
        assert state_before is not None and state_after is not None
        before = occurrence_facts(state_before, previous)
        after = occurrence_facts(state_after, step.certificate)
        facts = cell_facts(step.certificate, before, after)
        plans = derive_plans(step.certificate, before, after)
        verdicts = tuple(check_transport_plan(f, p) for f, p in zip(facts, plans))
        witnesses = tuple(w for verdict in verdicts for w in verdict.counterwitnesses)
        authorization = step.certificate.authorization
        granted = {output for (_, output) in
                   (authorization.authority_grants if authorization else ())}
        disposed = {item.source_cell_id for item in step.certificate.terminal_dispositions}
        for item, verdict in zip(facts, verdicts):
            if not cm_n1_accepts(item, cell_has_terminal_disposition=item.cell_id in disposed,
                                 granted_outputs=tuple(granted)):
                cm_rejected.append(f"{step.step_id}/{item.cell_id}")
            if not verdict.accepted:
                transport_rejected.append(f"{step.step_id}/{item.cell_id}")
        steps.append(StepTransportReport(
            step.step_id, not witnesses, verdicts, witnesses))
        all_witnesses.extend(witnesses)
        previous = step.certificate
    return HistoryTransportReport(
        history.history_id, not all_witnesses, tuple(steps), tuple(all_witnesses),
        tuple(cm_rejected), tuple(transport_rejected),
    )


# --------------------------------------------------------------------------
# The benchmark cells
# --------------------------------------------------------------------------

_LIVE = OccurrenceStatus.LIVE
_SUSP = OccurrenceStatus.SUSPENDED

BENCHMARK_CASES = ("A", "B", "C", "D", "E", "F", "G")


def benchmark_cell(case: str) -> CellFacts:
    """The mandatory benchmark cells of `STANDING_TRANSPORT.md` §5."""
    live_authority = OccurrenceFacts("in:L", _LIVE, True, False)
    suspended_burden = OccurrenceFacts("in:S", _SUSP, False, True)
    if case == "A":
        return CellFacts("cell:A", (live_authority, suspended_burden),
                         (OccurrenceFacts("out:M", _LIVE, True, False),))
    if case == "B":
        return CellFacts("cell:B", (live_authority, suspended_burden),
                         (OccurrenceFacts("out:M", _LIVE, True, False),
                          OccurrenceFacts("out:S", _SUSP, False, True)))
    if case == "C":
        return CellFacts("cell:C", (live_authority, suspended_burden),
                         (OccurrenceFacts("out:M", _LIVE, True, False),))
    if case == "D":
        return CellFacts("cell:D", (live_authority,),
                         (OccurrenceFacts("out:M1", _LIVE, True, False),
                          OccurrenceFacts("out:M2", _LIVE, True, False)))
    if case == "E":
        return CellFacts("cell:E", (live_authority, suspended_burden),
                         (OccurrenceFacts("out:M", _SUSP, False, True),))
    if case == "F":
        return CellFacts("cell:F", (suspended_burden,),
                         (OccurrenceFacts("out:M", _LIVE, True, False),))
    if case == "G":
        return CellFacts("cell:G", (live_authority,
                                    OccurrenceFacts("in:E", _LIVE, False, False)),
                         (OccurrenceFacts("out:M", _LIVE, True, False),))
    raise ValueError(case)


def reinstatement_plan(cell: CellFacts, *, basis: str = "root:new-evidence",
                       authorization: str = "auth:reinstatement",
                       with_termination: bool = True) -> StandingTransportPlan:
    """A cell repaired by a scoped reinstatement basis bound to its output."""
    return canonical_plan(
        cell,
        grants=available_grants(cell, basis=basis, authorization=authorization),
        terminations=available_terminations(cell, authorization=authorization)
        if with_termination else (),
    )


def benchmark_plan(case: str) -> StandingTransportPlan:
    """The plan each benchmark case of `STANDING_TRANSPORT.md` §5 actually declares."""
    cell = benchmark_cell(case)
    if case in ("A", "C", "D"):
        # No response, no residual, no grant: exactly the records the case omits.
        return canonical_plan(cell)
    if case in ("B", "E"):
        return canonical_plan(cell)
    if case == "F":
        return reinstatement_plan(cell)
    if case == "G":
        # Two inputs contribute semantic content; only the entitlement input
        # sponsors standing; a separate scoped grant supplies practical authority.
        return StandingTransportPlan(
            cell.cell_id,
            tuple(SupportEdge(source.occurrence_id, "out:M") for source in cell.inputs),
            (SupportEdge("in:E", "out:M"),),
            (),
            (), (),
            (ScopedGrant("grant:authority:out:M", "authority", "out:M",
                         "basis:standing-grant", "auth:transport"),),
        )
    raise ValueError(case)


# --------------------------------------------------------------------------
# Finite exhaustive enumeration
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class EnumerationScope:
    """The exact finite search space.  Facts outside it are not covered."""

    shapes: tuple[tuple[int, int], ...] = ((1, 1), (1, 2), (2, 1), (2, 2))
    statuses: tuple[OccurrenceStatus, ...] = (
        OccurrenceStatus.TERMINAL, OccurrenceStatus.SUSPENDED, OccurrenceStatus.LIVE)
    authority_bits: tuple[bool, ...] = (False, True)
    burden_bits: tuple[bool, ...] = (False, True)
    record_settings: tuple[tuple[bool, bool], ...] = (
        (False, False), (True, False), (False, True), (True, True))

    @property
    def configurations(self) -> int:
        return len(self.statuses) * len(self.authority_bits) * len(self.burden_bits)


@dataclass(frozen=True)
class Disagreement:
    direction: str
    cell: CellFacts
    codes: tuple[str, ...]


@dataclass(frozen=True)
class EnumerationReport:
    scope: EnumerationScope
    cells_examined: int
    plan_checks: int
    cm_n1_accepted: int
    transport_accepted: tuple[tuple[str, int], ...]
    agreements: int
    cm_n1_only_count: int
    transport_only_count: int
    unsound_count: int
    stricter_count: int
    cm_n1_only: tuple[Disagreement, ...]
    transport_only: tuple[Disagreement, ...]
    unsound: tuple[Disagreement, ...]
    stricter_than_safety: tuple[Disagreement, ...]


def _occurrence_configurations(scope: EnumerationScope) -> tuple[tuple[OccurrenceStatus, bool, bool], ...]:
    return tuple(
        (status, authority, burden)
        for status in scope.statuses
        for authority in scope.authority_bits
        for burden in scope.burden_bits
    )


def enumerate_cells(scope: EnumerationScope = EnumerationScope()) -> Iterable[CellFacts]:
    """Deterministic enumeration of every cell in the scope, in a fixed order."""
    configurations = _occurrence_configurations(scope)
    for width, height in scope.shapes:
        indices = tuple(range(width + height))
        for assignment in _product(configurations, len(indices)):
            inputs = tuple(
                OccurrenceFacts(f"in:{position}", *assignment[position])
                for position in range(width))
            outputs = tuple(
                OccurrenceFacts(f"out:{position - width}", *assignment[position])
                for position in range(width, width + height))
            yield CellFacts(f"cell:{width}x{height}", inputs, outputs)


def _product(items: Sequence[object], repeat: int) -> Iterable[tuple]:
    if repeat == 0:
        yield ()
        return
    for head in items:
        for tail in _product(items, repeat - 1):
            yield (head,) + tail


# The four independently stated safety properties.  These are not a second
# implementation of the predicate: they say directly what must not happen.


def standing_created_without_sponsor(cell: CellFacts, plan: StandingTransportPlan) -> bool:
    for target in cell.outputs:
        if _order(target) <= STANDING_ORDER[OccurrenceStatus.TERMINAL]:
            continue
        if any(_order(item) >= _order(target) for item in cell.inputs):
            continue
        if any(grant.kind in _STANDING_GRANTS and grant.output_id == target.occurrence_id
               and grant.basis_ref and grant.authorization_ref for grant in plan.grants):
            continue
        return True
    return False


def authority_duplicated_or_transferred(cell: CellFacts, plan: StandingTransportPlan) -> bool:
    authoritative = tuple(t.occurrence_id for t in cell.outputs if t.practical_authority)
    granted = {grant.output_id for grant in plan.grants
               if grant.kind in ("authority", "authority-split")
               and grant.basis_ref and grant.authorization_ref}
    outputs = {t.occurrence_id: t for t in cell.outputs}
    candidates = {
        identifier: tuple(
            item.occurrence_id for item in cell.inputs
            if item.practical_authority and _order(item) >= _order(outputs[identifier]))
        for identifier in authoritative if identifier not in granted
    }
    return _injective_assignment(tuple(candidates), candidates) is None


def burden_disappeared(cell: CellFacts, plan: StandingTransportPlan) -> bool:
    routes = {route.input_id: route for route in plan.burden_routes}
    terminations = {item.termination_id: item for item in plan.terminations}
    outputs = {target.occurrence_id: target for target in cell.outputs}
    for item in cell.inputs:
        if not item.unresolved_burden:
            continue
        route = routes.get(item.occurrence_id)
        if route is None:
            return True
        if route.carrier_output_id is not None:
            carrier = outputs.get(route.carrier_output_id)
            if carrier is None or not carrier.unresolved_burden:
                return True
            continue
        termination = terminations.get(route.termination_id or "")
        if (termination is None or not termination.witness_ref
                or not termination.authorization_ref
                or termination.input_id != item.occurrence_id):
            return True
    return False


def suspension_laundered(cell: CellFacts, plan: StandingTransportPlan) -> bool:
    routes = {route.input_id: route for route in plan.burden_routes}
    outputs = {target.occurrence_id: target for target in cell.outputs}
    for item in cell.inputs:
        if item.status != OccurrenceStatus.SUSPENDED or not item.unresolved_burden:
            continue
        route = routes.get(item.occurrence_id)
        carrier = outputs.get(route.carrier_output_id or "") if route else None
        if carrier is not None:
            if _order(carrier) > _order(item):
                return True
            if carrier.practical_authority and not item.practical_authority:
                return True
            continue
        answered = bool(route and route.termination_id)
        if not answered and any(_order(target) > _order(item) for target in cell.outputs):
            return True
    return False


SAFETY_PROPERTIES = (
    ("standing-created", standing_created_without_sponsor),
    ("authority-duplicated", authority_duplicated_or_transferred),
    ("burden-disappeared", burden_disappeared),
    ("suspension-laundered", suspension_laundered),
)


def run_enumeration(scope: EnumerationScope = EnumerationScope()) -> EnumerationReport:
    """Exhaustively classify every cell in the scope.  Deterministic; no sampling."""
    cells = 0
    checks = 0
    cm_accepted = 0
    accepted_by_setting: dict[tuple[bool, bool], int] = {
        setting: 0 for setting in scope.record_settings}
    agreements = 0
    cm_only: list[Disagreement] = []
    transport_only: list[Disagreement] = []
    unsound: list[Disagreement] = []
    stricter: list[Disagreement] = []
    for cell in enumerate_cells(scope):
        cells += 1
        cm = cm_n1_accepts(cell)
        cm_accepted += int(cm)
        bare_plan = canonical_plan(cell)
        bare = check_transport_plan(cell, bare_plan)
        checks += 1
        for allow_grants, allow_terminations in scope.record_settings:
            if (allow_grants, allow_terminations) == (False, False):
                verdict = bare
            else:
                plan = canonical_plan(
                    cell,
                    grants=available_grants(cell) if allow_grants else (),
                    terminations=available_terminations(cell) if allow_terminations else (),
                )
                verdict = check_transport_plan(cell, plan)
                checks += 1
            accepted_by_setting[(allow_grants, allow_terminations)] += int(verdict.accepted)
        codes = tuple(sorted({w.code for w in bare.counterwitnesses}))
        if cm == bare.accepted:
            agreements += 1
        elif cm:
            cm_only.append(Disagreement("cm-n1-only", cell, codes))
        else:
            transport_only.append(Disagreement("transport-only", cell, codes))
        unsafe = tuple(
            name for name, predicate in SAFETY_PROPERTIES if predicate(cell, bare_plan))
        if bare.accepted and unsafe:
            unsound.append(Disagreement("unsound", cell, unsafe))
        if not bare.accepted and not unsafe:
            stricter.append(Disagreement("stricter", cell, codes))
    return EnumerationReport(
        scope, cells, checks, cm_accepted,
        tuple((f"grants={g},terminations={t}", accepted_by_setting[(g, t)])
              for g, t in scope.record_settings),
        agreements, len(cm_only), len(transport_only), len(unsound), len(stricter),
        _minimal(cm_only), _minimal(transport_only),
        _minimal(unsound), _minimal(stricter),
    )


def _minimal(items: Sequence[Disagreement], limit: int = 6) -> tuple[Disagreement, ...]:
    """The smallest witnesses first: fewest occurrences, then weakest statuses."""
    def key(item: Disagreement) -> tuple:
        cell = item.cell
        return (
            len(cell.inputs) + len(cell.outputs),
            sum(_order(o) for o in cell.inputs + cell.outputs),
            sum(o.practical_authority for o in cell.inputs + cell.outputs),
            cell.cell_id,
            tuple(o.occurrence_id for o in cell.inputs + cell.outputs),
        )
    return tuple(sorted(items, key=key)[:limit])


REALIZABLE_STATUSES = (OccurrenceStatus.SUSPENDED, OccurrenceStatus.LIVE)
REALIZABLE_SCOPE = EnumerationScope(statuses=REALIZABLE_STATUSES)
MAXIMALITY_SCOPE = EnumerationScope(shapes=((1, 1), (2, 1)), statuses=REALIZABLE_STATUSES)
INDEPENDENCE_SCOPE = REALIZABLE_SCOPE


def _subsets(items: Sequence[object]) -> Iterable[tuple]:
    if not items:
        yield ()
        return
    head, rest = items[0], items[1:]
    for tail in _subsets(rest):
        yield tail
        yield (head,) + tail


def enumerate_plans(cell: CellFacts, *, allow_grants: bool = True,
                    allow_terminations: bool = True) -> Iterable[StandingTransportPlan]:
    """Every plan in the declared family, in a fixed order.

    Standing and authority support range over all subsets of the inputs; grants
    range over all subsets of the well-formed records on offer; each burdened
    input routes to any output, to its supplied termination, or nowhere.
    Semantic support is held at its total value and varied separately by
    `semantic_independence_report`.
    """
    inputs = tuple(item.occurrence_id for item in cell.inputs)
    outputs = tuple(target.occurrence_id for target in cell.outputs)
    semantic = tuple(SupportEdge(source, target) for source in inputs for target in outputs)
    grant_pool = available_grants(cell) if allow_grants else ()
    termination_pool = ({t.input_id: t for t in available_terminations(cell)}
                        if allow_terminations else {})
    burdened = tuple(item.occurrence_id for item in cell.inputs if item.unresolved_burden)
    route_options = tuple(
        tuple(BurdenRoute(identifier, target, None) for target in outputs)
        + ((BurdenRoute(identifier, None, termination_pool[identifier].termination_id),)
           if identifier in termination_pool else ())
        + (BurdenRoute(identifier, None, None),)
        for identifier in burdened
    )
    for standing_sets in _product(tuple(_subsets(inputs)), len(outputs)):
        standing = tuple(
            SupportEdge(source, target)
            for target, sources in zip(outputs, standing_sets) for source in sources)
        for authority_sets in _product(tuple(_subsets(inputs)), len(outputs)):
            authority = tuple(
                SupportEdge(source, target)
                for target, sources in zip(outputs, authority_sets) for source in sources)
            for grants in _subsets(grant_pool):
                for routes in _product_of(route_options):
                    used = tuple(
                        termination_pool[route.input_id] for route in routes
                        if route.termination_id is not None)
                    yield StandingTransportPlan(
                        cell.cell_id, semantic, standing, authority,
                        tuple(routes), used, tuple(grants))


def _product_of(option_lists: Sequence[Sequence[object]]) -> Iterable[tuple]:
    if not option_lists:
        yield ()
        return
    for head in option_lists[0]:
        for tail in _product_of(option_lists[1:]):
            yield (head,) + tail


@dataclass(frozen=True)
class MaximalityReport:
    scope: EnumerationScope
    record_setting: tuple[bool, bool]
    cells_examined: int
    plans_examined: int
    satisfiable_cells: int
    canonical_accepted_cells: int
    failures: tuple[CellFacts, ...]


def canonical_maximality_report(scope: EnumerationScope = MAXIMALITY_SCOPE, *,
                                allow_grants: bool = False,
                                allow_terminations: bool = False) -> MaximalityReport:
    """Is the canonical plan accepted whenever any plan in the family is?

    Asked at a fixed record setting: the plan family and the canonical plan are
    offered exactly the same records, so the comparison is about provenance
    declarations and not about what the certificate supplies.
    """
    cells = 0
    plans = 0
    satisfiable = 0
    canonical_ok = 0
    failures: list[CellFacts] = []
    for cell in enumerate_cells(scope):
        cells += 1
        best = check_transport_plan(
            cell,
            canonical_plan(
                cell,
                grants=available_grants(cell) if allow_grants else (),
                terminations=available_terminations(cell) if allow_terminations else (),
            ),
        ).accepted
        canonical_ok += int(best)
        found = False
        for plan in enumerate_plans(cell, allow_grants=allow_grants,
                                    allow_terminations=allow_terminations):
            plans += 1
            if check_transport_plan(cell, plan).accepted:
                found = True
                break
        satisfiable += int(found)
        if found and not best:
            failures.append(cell)
    return MaximalityReport(scope, (allow_grants, allow_terminations), cells, plans,
                            satisfiable, canonical_ok, tuple(failures))


@dataclass(frozen=True)
class IndependenceReport:
    scope: EnumerationScope
    cells_examined: int
    variants_examined: int
    invariant_cells: int
    failures: tuple[CellFacts, ...]


def semantic_independence_report(
    scope: EnumerationScope = INDEPENDENCE_SCOPE,
) -> IndependenceReport:
    """Does semantic support ever change the verdict?  It must not."""
    cells = 0
    variants = 0
    invariant = 0
    failures: list[CellFacts] = []
    for cell in enumerate_cells(scope):
        cells += 1
        plan = canonical_plan(cell, grants=available_grants(cell),
                              terminations=available_terminations(cell))
        baseline = check_transport_plan(cell, plan).accepted
        edges = tuple(
            SupportEdge(source.occurrence_id, target.occurrence_id)
            for source in cell.inputs for target in cell.outputs)
        stable = True
        for subset in _subsets(edges):
            variants += 1
            if check_transport_plan(cell, replace(plan, semantic_support=subset)).accepted != baseline:
                stable = False
        invariant += int(stable)
        if not stable:
            failures.append(cell)
    return IndependenceReport(scope, cells, variants, invariant, tuple(failures))


# Public alias: the composer in `src/history.py` must allocate licences with the
# same matching the local predicate uses, never a greedy first fit.
injective_assignment = _injective_assignment
