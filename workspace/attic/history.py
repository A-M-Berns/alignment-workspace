"""End-to-end transport of normative resources across a finite linear history.

`src/standing.py` decides one cell's transport plan.  This module asks the
local-to-global question: if every cell's plan is accepted, do the plans compose
into a valid end-to-end transport object?

The answer is **no**, and the obstruction is sharp.  A transport plan records
whether an occurrence carries *an* unresolved burden — a Boolean bit.  A bit
cannot distinguish one owed answer from two.  A merge may therefore route two
distinct burdens onto one carrier, each hop locally legal, and a later
termination scoped to that carrier discharges both with one witness.  See
`LOCAL_TO_GLOBAL.md`.

The composer here tracks resource *identity* (origin version and occurrence),
which is exactly the datum the local object lacks, so it can see the collision
the local checks cannot.  Nothing in `src/migration.py` is changed and no field
is added to `StandingTransportPlan`.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable, Mapping, Sequence

from src.migration import OccurrenceStatus
from src.standing import (
    STANDING_ORDER,
    BurdenRoute,
    CellFacts,
    OccurrenceFacts,
    ScopedGrant,
    ScopedTermination,
    StandingTransportPlan,
    available_terminations,
    canonical_plan,
    check_transport_plan,
    injective_assignment,
)

RESOURCE_KINDS = ("burden", "authority")


@dataclass(frozen=True)
class StepFacts:
    """One migration's cells with their declared transport plans."""

    cells: tuple[CellFacts, ...]
    plans: tuple[StandingTransportPlan, ...]


@dataclass(frozen=True)
class HistoryFacts:
    history_id: str
    steps: tuple[StepFacts, ...]

    @property
    def depth(self) -> int:
        return len(self.steps)


@dataclass(frozen=True)
class ResourceRoute:
    """One normative resource followed from its origin to its outcome."""

    kind: str
    resource_id: str
    origin_version: int
    origin_occurrence: str
    hops: tuple[tuple[int, str, str], ...]
    outcome: str
    witness: str | None = None


@dataclass(frozen=True)
class GlobalObstruction:
    code: str
    resource_ids: tuple[str, ...]
    version: int
    site: str
    witness: str | None
    detail: str


@dataclass(frozen=True)
class GlobalTransport:
    history_id: str
    accepted: bool
    burden_routes: tuple[ResourceRoute, ...]
    authority_routes: tuple[ResourceRoute, ...]
    accumulated_grants: tuple[tuple[int, str, str], ...]
    obstructions: tuple[GlobalObstruction, ...]
    local_acceptance: tuple[tuple[int, str, bool], ...]


def _issue(store: list[GlobalObstruction], code: str, resources: Iterable[str],
           version: int, site: str, witness: str | None, detail: str) -> None:
    store.append(GlobalObstruction(code, tuple(sorted(resources)), version, site,
                                   witness, detail))


def local_acceptance(history: HistoryFacts) -> tuple[tuple[int, str, bool], ...]:
    """Run the one-cell predicate at every cell of every step."""
    return tuple(
        (index, cell.cell_id, check_transport_plan(cell, plan).accepted)
        for index, step in enumerate(history.steps)
        for cell, plan in zip(step.cells, step.plans)
    )


def compose_transport(history: HistoryFacts) -> GlobalTransport:
    """Compose the per-cell plans into an end-to-end transport object.

    Burdens and authority licences are followed as *identified* resources along
    normalized ancestry.  Paths are never identified with resources: two paths
    may carry one licence, and one path may carry several burdens.
    """
    obstructions: list[GlobalObstruction] = []
    grants: list[tuple[int, str, str]] = []

    burden_sites: dict[str, str] = {}
    burden_hops: dict[str, list[tuple[int, str, str]]] = {}
    burden_origin: dict[str, tuple[int, str]] = {}
    burden_outcome: dict[str, tuple[str, str | None]] = {}

    licence_sites: dict[str, str] = {}
    licence_hops: dict[str, list[tuple[int, str, str]]] = {}
    licence_origin: dict[str, tuple[int, str]] = {}
    licence_outcome: dict[str, tuple[str, str | None]] = {}

    def seed(version: int, occurrences: Iterable[OccurrenceFacts]) -> None:
        for item in occurrences:
            if item.unresolved_burden:
                identifier = f"burden@{version}:{item.occurrence_id}"
                if identifier not in burden_origin:
                    burden_origin[identifier] = (version, item.occurrence_id)
                    burden_sites[identifier] = item.occurrence_id
                    burden_hops[identifier] = []
            if item.practical_authority:
                identifier = f"licence@{version}:{item.occurrence_id}"
                if identifier not in licence_origin:
                    licence_origin[identifier] = (version, item.occurrence_id)
                    licence_sites[identifier] = item.occurrence_id
                    licence_hops[identifier] = []

    if history.steps:
        seed(0, [item for cell in history.steps[0].cells for item in cell.inputs])

    for index, step in enumerate(history.steps):
        outputs_here = [item for cell in step.cells for item in cell.outputs]
        arriving: dict[str, list[str]] = {}
        licence_arriving: dict[str, list[str]] = {}
        for cell, plan in zip(step.cells, step.plans):
            inputs = {item.occurrence_id: item for item in cell.inputs}
            outputs = {item.occurrence_id: item for item in cell.outputs}
            terminations = {item.termination_id: item for item in plan.terminations}
            routes = {route.input_id: route for route in plan.burden_routes}

            # Burden resources follow their input's declared route.
            for identifier, item in sorted(inputs.items()):
                held = sorted(r for r, site in burden_sites.items() if site == identifier)
                if not held:
                    continue
                route = routes.get(identifier)
                if route is None or (route.carrier_output_id is None
                                     and route.termination_id is None):
                    _issue(obstructions, "global.burden_abandoned", held, index,
                           identifier, None,
                           "a resource still owed an answer reaches a cell with no route")
                    for resource in held:
                        burden_outcome[resource] = ("abandoned", None)
                        burden_sites.pop(resource, None)
                    continue
                if route.carrier_output_id is not None:
                    for resource in held:
                        burden_hops[resource].append(
                            (index, identifier, route.carrier_output_id))
                        arriving.setdefault(route.carrier_output_id, []).append(resource)
                        burden_sites.pop(resource, None)
                    continue
                termination = terminations.get(route.termination_id or "")
                if termination is None:
                    _issue(obstructions, "global.burden_abandoned", held, index,
                           identifier, None,
                           "a burden route names a termination the plan does not declare")
                    for resource in held:
                        burden_outcome[resource] = ("abandoned", None)
                        burden_sites.pop(resource, None)
                    continue
                if len(held) > 1:
                    _issue(obstructions, "global.termination_over_scope", held, index,
                           identifier, termination.termination_id,
                           "one witness is asked to discharge several distinct owed answers "
                           "that a merge routed onto the same carrier")
                for resource in held:
                    burden_hops[resource].append((index, identifier, "<terminated>"))
                    burden_outcome[resource] = ("terminated", termination.termination_id)
                    burden_sites.pop(resource, None)

            # Authority licences follow the declared sponsors, allocated by the
            # same injective matching the one-cell predicate uses.  A greedy
            # first fit would reuse one licence and manufacture a false
            # obstruction downstream.
            authoritative = tuple(sorted(
                target for target, item in outputs.items() if item.practical_authority))
            candidates = {
                target: tuple(sorted(
                    resource for edge in plan.authority_support
                    if edge.target_id == target and edge.source_id in inputs
                    for resource, site in licence_sites.items() if site == edge.source_id))
                for target in authoritative
            }
            granted_here = {
                grant.output_id: grant for grant in plan.grants
                if grant.kind in ("authority", "authority-split")
            }
            inherited = tuple(t for t in authoritative if t not in granted_here)
            assignment = injective_assignment(inherited, candidates) or {}
            for target in authoritative:
                if target in granted_here:
                    grant = granted_here[target]
                    grants.append((index, plan.cell_id, target))
                    identifier = f"licence@grant:{index}:{grant.grant_id}"
                    licence_origin[identifier] = (index + 1, target)
                    licence_hops[identifier] = []
                    licence_arriving.setdefault(target, []).append(identifier)
                    continue
                licence = assignment.get(target)
                if licence is None:
                    _issue(obstructions, "global.authority_unsourced", (), index, target,
                           None, "an authoritative output has neither an inherited licence "
                                 "nor a scoped grant")
                    continue
                licence_hops[licence].append((index, licence_sites[licence], target))
                licence_arriving.setdefault(target, []).append(licence)

        for target, resources in sorted(arriving.items()):
            for resource in resources:
                burden_sites[resource] = target
        for target, resources in sorted(licence_arriving.items()):
            for resource in resources:
                licence_sites[resource] = target
        counts: dict[str, list[str]] = {}
        for resource, site in licence_sites.items():
            counts.setdefault(site, []).append(resource)
        for site, resources in sorted(counts.items()):
            if len(resources) > 1:
                _issue(obstructions, "global.licence_pooled", resources, index + 1, site,
                       None, "several independent licences are pooled on one occurrence")
        for item in outputs_here:
            if not item.unresolved_burden:
                continue
            if not any(site == item.occurrence_id for site in burden_sites.values()):
                identifier = f"burden@{index + 1}:{item.occurrence_id}"
                burden_origin[identifier] = (index + 1, item.occurrence_id)
                burden_sites[identifier] = item.occurrence_id
                burden_hops[identifier] = []
        for identifier, site in sorted(burden_sites.items()):
            match = next((o for o in outputs_here if o.occurrence_id == site), None)
            if match is not None and not match.unresolved_burden:
                _issue(obstructions, "global.burden_bit_lost", (identifier,), index + 1,
                       site, None,
                       "a resource still owed an answer sits on an occurrence whose "
                       "declared burden bit is clear")

    for identifier, site in sorted(burden_sites.items()):
        burden_outcome.setdefault(identifier, ("outstanding", None))
    burden_records = tuple(
        ResourceRoute("burden", identifier, *burden_origin[identifier],
                      tuple(burden_hops[identifier]),
                      burden_outcome.get(identifier, ("outstanding", None))[0],
                      burden_outcome.get(identifier, ("outstanding", None))[1])
        for identifier in sorted(burden_origin)
    )
    authority_records = tuple(
        ResourceRoute("authority", identifier, *licence_origin[identifier],
                      tuple(licence_hops[identifier]),
                      "held" if identifier in licence_sites else "released", None)
        for identifier in sorted(licence_origin)
    )
    return GlobalTransport(
        history.history_id, not obstructions, burden_records, authority_records,
        tuple(grants), tuple(obstructions), local_acceptance(history),
    )


def authority_injection(transport: GlobalTransport) -> Mapping[str, str]:
    """Endpoint authority-bearing sites mapped to the licence that licenses them.

    Injectivity of this map is the no-double-authority statement in provenance
    form: distinct authoritative endpoint occurrences need distinct licences,
    drawn from the initial licences or the grants introduced by the history.
    """
    held: dict[str, str] = {}
    for record in transport.authority_routes:
        if record.outcome != "held":
            continue
        site = record.hops[-1][2] if record.hops else record.origin_occurrence
        held[record.resource_id] = site
    return {resource: site for resource, site in sorted(held.items())}


# --------------------------------------------------------------------------
# The minimal local-to-global counterexample, and its repair
# --------------------------------------------------------------------------


def _facts(identifier: str, status: OccurrenceStatus, authority: bool = False,
           burden: bool = False) -> OccurrenceFacts:
    return OccurrenceFacts(identifier, status, authority, burden)


def merge_then_terminate_history() -> HistoryFacts:
    """Two owed answers merged onto one carrier, then closed by one witness.

    Both cells are accepted by the one-cell predicate.  The first merges two
    burdened inputs onto a carrier that still carries a burden; the second
    terminates that carrier with a witness scoped to it.
    """
    suspended = OccurrenceStatus.SUSPENDED
    first = CellFacts(
        "cell:merge",
        (_facts("in:A", suspended, burden=True), _facts("in:B", suspended, burden=True)),
        (_facts("mid:C", suspended, burden=True),))
    first_plan = canonical_plan(first)
    second = CellFacts("cell:close", (_facts("mid:C", suspended, burden=True),), ())
    second_plan = canonical_plan(second, terminations=available_terminations(second))
    return HistoryFacts("history:merge-then-terminate",
                        (StepFacts((first,), (first_plan,)),
                         StepFacts((second,), (second_plan,))))


def burden_ledger(history: HistoryFacts) -> tuple[tuple[str, tuple[str, ...]], ...]:
    """Which owed answers each occurrence bears, at each version.

    This is the datum the one-cell object lacks: a multiset, not a bit.  It is
    computed here from the history rather than stored on a plan, so that nothing
    is added to the frozen one-step interface before the repair is justified.
    """
    transport = compose_transport(history)
    sites: dict[str, list[str]] = {}
    for record in transport.burden_routes:
        site = record.hops[-1][2] if record.hops else record.origin_occurrence
        if record.outcome == "terminated":
            site = f"<terminated:{record.witness}>"
        sites.setdefault(site, []).append(record.resource_id)
    return tuple((site, tuple(sorted(resources))) for site, resources in sorted(sites.items()))


def check_with_burden_ledger(cell: CellFacts, plan: StandingTransportPlan,
                             borne: Mapping[str, Sequence[str]]) -> bool:
    """The repaired local condition: one witness closes exactly one owed answer.

    `borne` supplies, per input occurrence, the owed answers it actually bears.
    This is the smallest additional relation that makes the local check
    sufficient; `LOCAL_TO_GLOBAL.md` §6 argues it is intrinsic to a history and
    not to a single migration.
    """
    if not check_transport_plan(cell, plan).accepted:
        return False
    for route in plan.burden_routes:
        if route.termination_id is None:
            continue
        if len(borne.get(route.input_id, ())) > 1:
            return False
    return True


# --------------------------------------------------------------------------
# Associativity
# --------------------------------------------------------------------------


def restrict(history: HistoryFacts, lower: int, upper: int) -> HistoryFacts:
    return HistoryFacts(f"{history.history_id}[{lower}:{upper}]",
                        history.steps[lower:upper])


def _endpoint_site(record: ResourceRoute) -> str:
    return record.hops[-1][2] if record.hops else record.origin_occurrence


def splice(first: GlobalTransport,
           second: GlobalTransport) -> Mapping[tuple[int, str], tuple[str, str | None]]:
    """Continue each resource of `first` into the resource `second` starts at its site.

    The result is the outcome map — origin occurrence to `(outcome, witness)` —
    which is the invariant content of a transport object.  Resource identifiers
    are not compared, because they encode the bracketing.
    """
    outcomes: dict[tuple[int, str], tuple[str, str | None]] = {}
    later: dict[str, ResourceRoute] = {}
    for record in second.burden_routes:
        later.setdefault(record.origin_occurrence, record)
    for record in first.burden_routes:
        key = (record.origin_version, record.origin_occurrence)
        site = _endpoint_site(record)
        if record.outcome in ("terminated", "abandoned"):
            outcomes[key] = (record.outcome, record.witness)
            continue
        follow = later.get(site)
        outcomes[key] = ((follow.outcome, follow.witness) if follow is not None
                         else (record.outcome, record.witness))
    endpoints = {_endpoint_site(r) for r in first.burden_routes}
    for record in second.burden_routes:
        if record.origin_occurrence not in endpoints:
            outcomes.setdefault((record.origin_version, record.origin_occurrence),
                                (record.outcome, record.witness))
    return dict(sorted(outcomes.items()))


def outcome_map(
    transport: GlobalTransport,
) -> Mapping[tuple[int, str], tuple[str, str | None]]:
    """Keyed by `(origin version, origin occurrence)`.

    Occurrence identifiers may legitimately repeat across versions, so the
    occurrence name alone is not a resource identity.
    """
    return dict(sorted(
        ((record.origin_version, record.origin_occurrence),
         (record.outcome, record.witness))
        for record in transport.burden_routes))


@dataclass(frozen=True)
class AssociativityReport:
    history_id: str
    left: Mapping[tuple[int, str], tuple[str, str | None]]
    right: Mapping[tuple[int, str], tuple[str, str | None]]
    direct: Mapping[tuple[int, str], tuple[str, str | None]]
    associative: bool
    agrees_with_direct: bool


def associativity_report(history: HistoryFacts) -> AssociativityReport:
    """Compare the two bracketings of a three-step history, and the direct fold."""
    if history.depth != 3:
        raise ValueError("associativity is stated for three migrations")
    first = compose_transport(restrict(history, 0, 1))
    second = compose_transport(restrict(history, 1, 2))
    third = compose_transport(restrict(history, 2, 3))
    left_pair = compose_transport(restrict(history, 0, 2))
    right_pair = compose_transport(restrict(history, 1, 3))
    left = splice(left_pair, third)
    right = splice(first, compose_transport(restrict(history, 1, 3)))
    direct = outcome_map(compose_transport(history))
    del second, right_pair
    return AssociativityReport(
        history.history_id, left, right, direct,
        left == right, left == direct and right == direct)


def split_merge_split_history() -> HistoryFacts:
    """Three steps with shared ancestry, an owed answer, a grant, and a lost distinction.

    `V_0` has one authoritative live entitlement and one suspended burdened one.
    Step 1 splits the live one and suspends nothing; step 2 merges the split
    branches back while the burdened branch continues; step 3 splits again and
    introduces one scoped authority grant for the branch the inherited
    licence cannot reach, terminating the owed answer with a
    witness scoped to its own lineage.
    """
    live, suspended = OccurrenceStatus.LIVE, OccurrenceStatus.SUSPENDED
    step_one = CellFacts(
        "cell:split",
        (_facts("v0:auth", live, authority=True),),
        (_facts("v1:a", live, authority=True), _facts("v1:b", live)))
    step_one_burden = CellFacts(
        "cell:carry-1",
        (_facts("v0:owed", suspended, burden=True),),
        (_facts("v1:owed", suspended, burden=True),))
    step_two = CellFacts(
        "cell:merge",
        (_facts("v1:a", live, authority=True), _facts("v1:b", live)),
        (_facts("v2:m", live, authority=True),))
    step_two_burden = CellFacts(
        "cell:carry-2",
        (_facts("v1:owed", suspended, burden=True),),
        (_facts("v2:owed", suspended, burden=True),))
    step_three = CellFacts(
        "cell:respilt",
        (_facts("v2:m", live, authority=True),),
        (_facts("v3:x", live, authority=True), _facts("v3:y", live, authority=True)))
    step_three_burden = CellFacts(
        "cell:answer", (_facts("v2:owed", suspended, burden=True),), ())
    grant = ScopedGrant("grant:v3:x", "authority", "v3:x", "basis:new-evidence",
                        "auth:history")
    third_plan = replace(canonical_plan(step_three, grants=(grant,)))
    return HistoryFacts(
        "history:split-merge-split",
        (StepFacts((step_one, step_one_burden),
                   (canonical_plan(step_one), canonical_plan(step_one_burden))),
         StepFacts((step_two, step_two_burden),
                   (canonical_plan(step_two), canonical_plan(step_two_burden))),
         StepFacts((step_three, step_three_burden),
                   (third_plan,
                    canonical_plan(step_three_burden,
                                   terminations=available_terminations(step_three_burden))))),
    )


# --------------------------------------------------------------------------
# Bounded adversarial search
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SearchScope:
    shapes: tuple[tuple[int, int, int], ...]
    statuses: tuple[OccurrenceStatus, ...]
    vary: str


BURDEN_SCOPE = SearchScope(
    tuple((m, k, n) for m in (1, 2) for k in (1, 2) for n in (0, 1, 2)),
    (OccurrenceStatus.SUSPENDED, OccurrenceStatus.LIVE), "burden")
AUTHORITY_SCOPE = SearchScope(
    tuple((m, k, n) for m in (1, 2) for k in (1, 2) for n in (0, 1, 2)),
    (OccurrenceStatus.SUSPENDED, OccurrenceStatus.LIVE), "authority")


@dataclass(frozen=True)
class SearchReport:
    scope: SearchScope
    histories_examined: int
    plans_examined: int
    local_failures: int
    local_pass_global_pass: int
    local_pass_global_fail: int
    witnesses: tuple[tuple[str, HistoryFacts, tuple[GlobalObstruction, ...]], ...]


def _configurations(scope: SearchScope) -> tuple[tuple[OccurrenceStatus, bool, bool], ...]:
    if scope.vary == "burden":
        return tuple((status, False, burden)
                     for status in scope.statuses for burden in (False, True))
    return tuple((status, authority, False)
                 for status in scope.statuses for authority in (False, True))


def _assignments(items: Sequence[object], repeat: int) -> Iterable[tuple]:
    if repeat == 0:
        yield ()
        return
    for head in items:
        for tail in _assignments(items, repeat - 1):
            yield (head,) + tail


def _route_options(cell: CellFacts) -> tuple[tuple[BurdenRoute, ...], ...]:
    burdened = [item.occurrence_id for item in cell.inputs if item.unresolved_burden]
    if not burdened:
        return ((),)
    per_input = []
    for identifier in burdened:
        options = [BurdenRoute(identifier, target.occurrence_id, None)
                   for target in cell.outputs]
        options.append(BurdenRoute(identifier, None, f"termination:{identifier}"))
        options.append(BurdenRoute(identifier, None, None))
        per_input.append(options)
    return tuple(_assignments_of(per_input))


def _assignments_of(option_lists: Sequence[Sequence[object]]) -> Iterable[tuple]:
    if not option_lists:
        yield ()
        return
    for head in option_lists[0]:
        for tail in _assignments_of(option_lists[1:]):
            yield (head,) + tail


def _plan_for(cell: CellFacts, routes: tuple[BurdenRoute, ...]) -> StandingTransportPlan:
    base = canonical_plan(cell)
    used = tuple(
        ScopedTermination(route.termination_id, route.input_id, "response",
                          "witness:response", "auth:search", True, None)
        for route in routes if route.termination_id is not None)
    return replace(base, burden_routes=routes, terminations=used)


def borne_by_site(transport: GlobalTransport) -> Mapping[str, tuple[str, ...]]:
    """Which owed answers each occurrence bears, keyed by occurrence."""
    sites: dict[str, list[str]] = {}
    for record in transport.burden_routes:
        for _, source, _ in record.hops:
            sites.setdefault(source, []).append(record.resource_id)
        if not record.hops:
            sites.setdefault(record.origin_occurrence, []).append(record.resource_id)
    return {site: tuple(sorted(set(resources))) for site, resources in sorted(sites.items())}


def search_local_to_global(scope: SearchScope = BURDEN_SCOPE,
                           limit: int = 6, *, repaired: bool = False) -> SearchReport:
    """Exhaustively search two-step histories of one cell each, in a fixed order.

    The search separates a failure of local plan acceptance from a genuinely
    global failure in which every local check passes.  It establishes facts only
    about the stated finite space.
    """
    configurations = _configurations(scope)
    histories = plans = local_failures = both = global_only = 0
    witnesses: list[tuple[str, HistoryFacts, tuple[GlobalObstruction, ...]]] = []
    for width, middle, height in scope.shapes:
        for assignment in _assignments(configurations, width + middle + height):
            inputs = tuple(OccurrenceFacts(f"in:{i}", *assignment[i]) for i in range(width))
            mids = tuple(OccurrenceFacts(f"mid:{i}", *assignment[width + i])
                         for i in range(middle))
            outs = tuple(OccurrenceFacts(f"out:{i}", *assignment[width + middle + i])
                         for i in range(height))
            first = CellFacts("cell:1", inputs, mids)
            second = CellFacts("cell:2", mids, outs)
            for first_routes in _route_options(first):
                for second_routes in _route_options(second):
                    histories += 1
                    plans += 2
                    history = HistoryFacts(
                        f"h:{width}{middle}{height}",
                        (StepFacts((first,), (_plan_for(first, first_routes),)),
                         StepFacts((second,), (_plan_for(second, second_routes),))))
                    transport = compose_transport(history)
                    accepted_locally = all(ok for _, _, ok in transport.local_acceptance)
                    if accepted_locally and repaired:
                        borne = borne_by_site(transport)
                        accepted_locally = all(
                            check_with_burden_ledger(cell, plan, borne)
                            for step in history.steps
                            for cell, plan in zip(step.cells, step.plans))
                    if not accepted_locally:
                        local_failures += 1
                        continue
                    if transport.accepted:
                        both += 1
                        continue
                    global_only += 1
                    if len(witnesses) < limit:
                        witnesses.append(
                            (history.history_id, history, transport.obstructions))
    return SearchReport(scope, histories, plans, local_failures, both,
                        global_only, tuple(witnesses))
