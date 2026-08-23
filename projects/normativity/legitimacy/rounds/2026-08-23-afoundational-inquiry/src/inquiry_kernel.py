"""Finite witnesses for the afoundational inquiry interface prosecution.

This is unregistered exploration code.  It uses exact finite objects to test the
candidate authority, accrual, service, and scheduling interfaces in MEMO.md.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from fractions import Fraction
from itertools import combinations
from typing import Callable, Iterable, Mapping, Sequence


class Mode(str, Enum):
    MAY = "may"
    MUST = "must"


class ContentKind(str, Enum):
    HOLD = "hold"
    DO = "do"


@dataclass(frozen=True)
class Commitment:
    ident: str
    kind: ContentKind
    content: str
    service_spec: str | None = None
    origin_due: str | None = None


@dataclass(frozen=True)
class NormativeAct:
    ident: str
    index: int
    kind: str
    seed: bool = False
    grounds: tuple[str, ...] = ()
    license_parents: tuple[str, ...] = ()
    accounts_for: tuple[str, ...] = ()


def authority_errors(acts: Sequence[NormativeAct]) -> tuple[str, ...]:
    """Enforce seed-only roots and strict pre-state normative licensing."""
    by_id: dict[str, NormativeAct] = {}
    errors: list[str] = []
    for act in acts:
        if act.ident in by_id:
            errors.append(f"duplicate:{act.ident}")
            continue
        if act.seed:
            if act.index != 0 or act.license_parents:
                errors.append(f"bad_seed:{act.ident}")
        elif not act.license_parents:
            errors.append(f"new_root:{act.ident}")
        for parent_id in act.license_parents:
            parent = by_id.get(parent_id)
            if parent is None:
                errors.append(f"license_not_prestate:{act.ident}:{parent_id}")
            elif parent.index >= act.index:
                errors.append(f"license_not_earlier:{act.ident}:{parent_id}")
        by_id[act.ident] = act
    return tuple(errors)


def authority_roots(acts: Sequence[NormativeAct], ident: str) -> frozenset[str]:
    by_id = {act.ident: act for act in acts}
    roots: set[str] = set()
    frontier = [ident]
    seen: set[str] = set()
    while frontier:
        current = frontier.pop()
        if current in seen:
            raise ValueError("authorization cycle")
        seen.add(current)
        act = by_id[current]
        if act.seed:
            roots.add(current)
        else:
            frontier.extend(act.license_parents)
    return frozenset(roots)


@dataclass(frozen=True)
class Rule:
    ident: str
    version: str
    mode: Mode
    trigger_kind: str
    task: str
    service_spec: str
    authority_act: str


@dataclass(frozen=True)
class Receipt:
    ident: str
    index: int
    kind: str


@dataclass(frozen=True)
class DueToken:
    ident: str
    rule_version: str
    receipt_id: str
    accrued_at: int
    task: str
    service_spec: str


def accrue(pre_rules: Iterable[Rule], receipt: Receipt) -> tuple[DueToken, ...]:
    """Evaluate Must triggers against the practice standing before the receipt phase."""
    return tuple(
        DueToken(
            ident=f"due:{rule.ident}@{rule.version}:{receipt.ident}",
            rule_version=rule.version,
            receipt_id=receipt.ident,
            accrued_at=receipt.index,
            task=rule.task,
            service_spec=rule.service_spec,
        )
        for rule in pre_rules
        if rule.mode is Mode.MUST and rule.trigger_kind == receipt.kind
    )


@dataclass(frozen=True)
class CoverageView:
    due_tokens: tuple[DueToken, ...] = ()
    liabilities: tuple[Commitment, ...] = ()
    coverage_debts: frozenset[str] = frozenset()
    terminal_accounts: frozenset[str] = frozenset()

    def generate(self, token: DueToken) -> "CoverageView":
        if token.ident in {item.ident for item in self.due_tokens}:
            raise ValueError("due token identities are immutable and unique")
        return replace(
            self,
            due_tokens=self.due_tokens + (token,),
            coverage_debts=self.coverage_debts | {token.ident},
        )

    def docket(self, token_id: str, liability_id: str) -> "CoverageView":
        token = next(item for item in self.due_tokens if item.ident == token_id)
        if token_id not in self.coverage_debts:
            raise ValueError("token is already docketed or explicitly accounted")
        liability = Commitment(
            liability_id, ContentKind.DO, token.task, token.service_spec, token.ident
        )
        return replace(
            self,
            liabilities=self.liabilities + (liability,),
            coverage_debts=self.coverage_debts - {token_id},
        )

    def account_coverage_debt(self, token_id: str) -> "CoverageView":
        if token_id not in self.coverage_debts:
            raise ValueError("no open coverage debt")
        return replace(
            self,
            coverage_debts=self.coverage_debts - {token_id},
            terminal_accounts=self.terminal_accounts | {token_id},
        )

    def complete(self) -> bool:
        represented = {item.origin_due for item in self.liabilities}
        represented |= set(self.coverage_debts) | set(self.terminal_accounts)
        return represented == {item.ident for item in self.due_tokens}


@dataclass(frozen=True)
class ServiceCertificate:
    liability_id: str
    specification_version: str
    evidence: frozenset[str]


def certified_service(
    liability: Commitment,
    certificate: ServiceCertificate,
    specifications: Mapping[str, frozenset[str]],
) -> bool:
    if liability.service_spec is None:
        return False
    return (
        certificate.liability_id == liability.ident
        and certificate.specification_version == liability.service_spec
        and certificate.evidence >= specifications[liability.service_spec]
    )


def service_spec_revision_errors(
    old: Commitment, new: Commitment, licensed: bool, lineage: bool
) -> tuple[str, ...]:
    if old.service_spec == new.service_spec:
        return ()
    errors = []
    if not licensed:
        errors.append("spec_revision.unlicensed")
    if not lineage:
        errors.append("spec_revision.unaccounted")
    return tuple(errors)


def per_input_service_edges(
    liabilities: Iterable[Commitment], certificates: Iterable[ServiceCertificate]
) -> bool:
    covered = {certificate.liability_id for certificate in certificates}
    return covered == {liability.ident for liability in liabilities}


@dataclass(frozen=True)
class InquiryAction:
    ident: str
    covers: frozenset[str]
    cost: Fraction


@dataclass(frozen=True)
class InquiryRequest:
    ident: str
    element: str
    arrival: int
    delay: Callable[[int], Fraction]


def service_times(
    purchases: Sequence[tuple[int, InquiryAction]], requests: Iterable[InquiryRequest]
) -> dict[str, int | None]:
    return {
        request.ident: next(
            (
                time
                for time, action in purchases
                if time >= request.arrival and request.element in action.covers
            ),
            None,
        )
        for request in requests
    }


def inquiry_delay_objective(
    purchases: Sequence[tuple[int, InquiryAction]],
    requests: Sequence[InquiryRequest],
    horizon: int,
) -> Fraction:
    bought = sum((action.cost for _time, action in purchases), Fraction(0))
    served = service_times(purchases, requests)
    delay = sum(
        (
            request.delay(served[request.ident] - request.arrival)
            if served[request.ident] is not None
            else request.delay(horizon - request.arrival)
        )
        for request in requests
    )
    return bought + delay


def scd_objective(
    purchases: Sequence[tuple[int, InquiryAction]],
    requests: Sequence[InquiryRequest],
    horizon: int,
) -> Fraction:
    """The restricted SCD objective after the identity translation in MEMO.md."""
    return inquiry_delay_objective(purchases, requests, horizon)


def starvation_despite_two_competitiveness(horizon: int) -> tuple[Fraction, Fraction]:
    """Background load makes global competitiveness compatible with starvation."""
    if horizon < 1:
        raise ValueError("positive horizon required")
    # One focal liability is never served and has delay t.  Background work costs
    # one per date under both policies.  OPT pays one extra unit for the focal task.
    algorithm = Fraction(2 * horizon)
    optimum = Fraction(horizon + 1)
    return algorithm, optimum


Progress = Callable[[frozenset[str]], Fraction]


def cover_time(order: Sequence[str], progress: Progress) -> int | None:
    seen: set[str] = set()
    for time, action in enumerate(order, 1):
        seen.add(action)
        if progress(frozenset(seen)) == 1:
            return time
    return None


def fixed_docket_latency(order: Sequence[str], objectives: Sequence[Progress]) -> int:
    times = [cover_time(order, objective) for objective in objectives]
    if any(time is None for time in times):
        raise ValueError("order does not cover every objective")
    return sum(time for time in times if time is not None)


def mlsc_unit_metric_objective(order: Sequence[str], objectives: Sequence[Progress]) -> int:
    """MLSC on the unit path metric: distance traveled equals list position."""
    return fixed_docket_latency(order, objectives)


def monotone_submodular(ground: Sequence[str], progress: Progress) -> bool:
    subsets = [
        frozenset(combo)
        for size in range(len(ground) + 1)
        for combo in combinations(ground, size)
    ]
    monotone = all(
        not left <= right or progress(left) <= progress(right)
        for left in subsets
        for right in subsets
    )
    submodular = all(
        progress(left) + progress(right)
        >= progress(left | right) + progress(left & right)
        for left in subsets
        for right in subsets
    )
    return monotone and submodular


def complementarity_progress(chosen: frozenset[str]) -> Fraction:
    return Fraction(1) if {"a", "b"} <= chosen else Fraction(0)


def overloaded_backlog(arrivals_per_step: int, capacity_per_step: int, steps: int) -> int:
    return max(0, (arrivals_per_step - capacity_per_step) * steps)


def evaluator_internal_disagreement() -> tuple[bool, bool]:
    """The external benchmark and inherited Must rule are independent predicates."""
    external_due = True
    internally_generated = False
    return external_due, internally_generated
