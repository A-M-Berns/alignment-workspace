"""Fixed semantic actions and audited lawful programs for item 29.

The theorem-facing action is one of eight semantic labels.  Occasion-local
ledger identifiers are introduced only by ``decode_action``.  The comparator
class is data interpreted by this module, rather than a caller-supplied Python
callback.  Exact charges remain in the preparation round's model.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from enum import Enum
from fractions import Fraction as Q
import inspect
from typing import Mapping, Sequence

from online_interface import PreActionReader, induced_action_map, sealed_legality_state
from src.certificates import (
    ADMITTED,
    DEFAULT_POLICY,
    LawfulEditCertificate,
    PolicySuite,
    address_by_basis,
    authority_declared,
    bears_on_by_subject,
    check,
    magnitude_by_impediment,
    reasons_compatible,
)
from src.model import (
    BASIS_DECLINE,
    BASIS_DEFAULT,
    BASIS_MERITS,
    CERTIFIER_FOOTPRINT,
    Accounting,
    ActualHistory,
    Occasion,
    ReasonRecord,
    Response,
    Schedule,
    response_for,
)
from src.replay import Comparator, FILINGS_FROZEN, charge_of, replay


class SemanticAction(Enum):
    """The fixed theorem-facing alphabet Λ; values carry no local identity."""

    MERITS_POSITIVE = "merits:positive"
    MERITS_NEGATIVE = "merits:negative"
    DEFAULT = "default"
    DECLINE_0 = "decline:0"
    DECLINE_1 = "decline:1"
    DECLINE_2 = "decline:2"
    DECLINE_3 = "decline:3"
    DECLINE_4 = "decline:4"


LAMBDA: tuple[SemanticAction, ...] = tuple(SemanticAction)
_DECLINE_BY_TOLL = {
    0: SemanticAction.DECLINE_0,
    1: SemanticAction.DECLINE_1,
    2: SemanticAction.DECLINE_2,
    3: SemanticAction.DECLINE_3,
    4: SemanticAction.DECLINE_4,
}


def validate_frozen_occasion(occasion: Occasion) -> None:
    """Check exactly the schedule facts on which the eight-label bijection rests."""
    schedule = occasion.schedule
    if schedule.service_window != 4:
        raise ValueError("the frozen bridge requires service_window = 4")
    if schedule.positive_verdict == schedule.negative_verdict:
        raise ValueError("positive and negative merits labels must be distinct")


def decode_action(occasion: Occasion, label: SemanticAction) -> Response:
    """Instantiate one semantic label with this occasion's canonical ledger effect."""
    validate_frozen_occasion(occasion)
    if label is SemanticAction.MERITS_POSITIVE:
        return response_for(occasion, BASIS_MERITS,
                            verdict=occasion.schedule.positive_verdict)
    if label is SemanticAction.MERITS_NEGATIVE:
        return response_for(occasion, BASIS_MERITS,
                            verdict=occasion.schedule.negative_verdict)
    if label is SemanticAction.DEFAULT:
        return response_for(occasion, BASIS_DEFAULT)
    toll = int(label.value.split(":", 1)[1])
    return response_for(occasion, BASIS_DECLINE, tolled=toll)


def encode_response(occasion: Occasion, response: Response) -> SemanticAction:
    """Inverse of ``decode_action`` on the eight canonical repository responses."""
    for label in LAMBDA:
        if decode_action(occasion, label) == response:
            return label
    raise ValueError("response is outside the frozen canonical response set")


def canonical_responses(occasion: Occasion) -> tuple[Response, ...]:
    return tuple(decode_action(occasion, label) for label in LAMBDA)


def label_loss(occasion: Occasion, label: SemanticAction) -> Q:
    return Q(charge_of(occasion, decode_action(occasion, label)))


@dataclass(frozen=True)
class ReasonView:
    """The reason fields read by the nine programs; no charge-bearing state."""

    reason_id: str
    kind: str
    subject: str
    live: bool
    lower: Q | None = None
    upper: Q | None = None
    dates: int | None = None


@dataclass(frozen=True)
class RuleContext:
    """The complete capability supplied to the declarative program interpreter."""

    occasion_id: str
    occasion_index: int
    date: int
    target: str
    threshold: Q
    reasons: tuple[ReasonView, ...]


def _occasion_index(identifier: str) -> int:
    prefix, separator, suffix = identifier.partition(":")
    if prefix != "o" or not separator or not suffix.isdigit():
        raise ValueError("item-30 occasion identifiers must have form o:<natural>")
    return int(suffix)


def _reason_view(reason: ReasonRecord, date: int) -> ReasonView:
    lower = Q(reason.payload["lower"]) if "lower" in reason.payload else None
    upper = Q(reason.payload["upper"]) if "upper" in reason.payload else None
    dates = int(reason.payload["dates"]) if "dates" in reason.payload else None
    return ReasonView(reason.reason_id, reason.kind, reason.subject,
                      reason.live_at(date), lower, upper, dates)


def public_context(reader: PreActionReader, occasion: Occasion) -> RuleContext:
    """Project a strict prefix onto the fields the finite program class can read."""
    reasons = tuple(_reason_view(reason, reader.date)
                    for reason in reader.reasons())
    return RuleContext(occasion.occasion_id, _occasion_index(occasion.occasion_id),
                       occasion.date, occasion.target,
                       Q(occasion.schedule.threshold), reasons)


class ProgramKind(Enum):
    IDENTITY = "identity"
    REPAIR_DECLINES = "repair_declines"
    TOLL_DECLINES = "toll_declines"
    DEFAULT_DECLINES = "default_declines"
    WITHDRAW_MERITS = "withdraw_merits"


@dataclass(frozen=True)
class LawfulProgram:
    """A comparator specification containing data only, never executable callbacks."""

    program_id: str
    kind: ProgramKind
    amount: int = 0
    parity: int | None = None


AUDITED_PROGRAMS: tuple[LawfulProgram, ...] = (
    LawfulProgram("identity", ProgramKind.IDENTITY),
    LawfulProgram("repair_declines", ProgramKind.REPAIR_DECLINES),
    LawfulProgram("repair_declines_even", ProgramKind.REPAIR_DECLINES, parity=0),
    LawfulProgram("repair_declines_odd", ProgramKind.REPAIR_DECLINES, parity=1),
    LawfulProgram("toll_declines_1", ProgramKind.TOLL_DECLINES, amount=1),
    LawfulProgram("toll_declines_2", ProgramKind.TOLL_DECLINES, amount=2),
    LawfulProgram("toll_declines_4", ProgramKind.TOLL_DECLINES, amount=4),
    LawfulProgram("default_declines", ProgramKind.DEFAULT_DECLINES),
    LawfulProgram("withdraw_merits", ProgramKind.WITHDRAW_MERITS),
)


PROGRAM_DESCRIPTIONS: Mapping[str, str] = {
    "identity": "leave every response unchanged",
    "repair_declines": "replace a decline by the merits direction certified by a live separating interval",
    "repair_declines_even": "the same interval repair on even-indexed occasions",
    "repair_declines_odd": "the same interval repair on odd-indexed occasions",
    "toll_declines_1": "claim one tolled date on a decline supported by a live impediment",
    "toll_declines_2": "claim two tolled dates on a decline supported by live impediments",
    "toll_declines_4": "claim four tolled dates where live impediments license that endpoint",
    "default_declines": "replace a decline by scheduled default on a live ripeness ground",
    "withdraw_merits": "withdraw a merits response to decline on a live ripeness ground",
}


def _live(context: RuleContext, kind: str) -> tuple[ReasonView, ...]:
    return tuple(reason for reason in context.reasons
                 if reason.live and reason.kind == kind
                 and reason.subject == context.target)


def rule_proposal(program: LawfulProgram, context: RuleContext,
                  source: SemanticAction
                  ) -> tuple[SemanticAction, tuple[str, ...], str] | None:
    """Interpret one fixed program using only ``RuleContext`` and the source label."""
    if program.kind is ProgramKind.IDENTITY:
        return None
    if program.parity is not None and context.occasion_index % 2 != program.parity:
        return None

    if program.kind is ProgramKind.REPAIR_DECLINES:
        if source not in _DECLINE_BY_TOLL.values():
            return None
        for reason in _live(context, "interval"):
            if reason.lower is not None and reason.lower >= context.threshold:
                return SemanticAction.MERITS_POSITIVE, (reason.reason_id,), "auth:review"
            if reason.upper is not None and reason.upper < context.threshold:
                return SemanticAction.MERITS_NEGATIVE, (reason.reason_id,), "auth:review"
        return None

    if program.kind is ProgramKind.TOLL_DECLINES:
        if source not in _DECLINE_BY_TOLL.values():
            return None
        grounds = tuple(reason.reason_id for reason in _live(context, "impediment"))
        if not grounds:
            return None
        return _DECLINE_BY_TOLL[program.amount], grounds, "auth:review"

    ripe = _live(context, "ripeness")
    if not ripe:
        return None
    ground = (ripe[0].reason_id,)
    if program.kind is ProgramKind.DEFAULT_DECLINES:
        if source not in _DECLINE_BY_TOLL.values():
            return None
        return SemanticAction.DEFAULT, ground, "auth:review"
    if program.kind is ProgramKind.WITHDRAW_MERITS:
        if source not in (SemanticAction.MERITS_POSITIVE,
                          SemanticAction.MERITS_NEGATIVE):
            return None
        return SemanticAction.DECLINE_0, ground, "auth:review"
    raise AssertionError(f"unknown program kind {program.kind!r}")


def compile_label_map(history: ActualHistory, occasion: Occasion,
                      program: LawfulProgram, *,
                      policy: PolicySuite = DEFAULT_POLICY
                      ) -> Mapping[SemanticAction, SemanticAction]:
    """Compile a lawful program into a total transformation Λ → Λ at one round."""
    legal_history = sealed_legality_state(history, occasion.date)
    legal_occasions = legal_history.actual_occasions()
    legal_occasion = next(item for item in legal_occasions
                          if item.occasion_id == occasion.occasion_id)
    context_reader = PreActionReader(legal_history, occasion.date,
                                     CERTIFIER_FOOTPRINT,
                                     responses=legal_history.responses,
                                     occasions=legal_occasions)
    context = public_context(context_reader, legal_occasion)
    result: dict[SemanticAction, SemanticAction] = {}
    for source in LAMBDA:
        proposal = rule_proposal(program, context, source)
        if proposal is None:
            result[source] = source
            continue
        target, grounds, authority = proposal
        certificate = LawfulEditCertificate(
            f"label:{program.program_id}:{occasion.occasion_id}",
            occasion.occasion_id, occasion.date,
            decode_action(legal_occasion, source),
            decode_action(legal_occasion, target), grounds, authority)
        certifier = PreActionReader(legal_history, occasion.date,
                                    CERTIFIER_FOOTPRINT,
                                    responses=legal_history.responses,
                                    occasions=legal_occasions)
        verdict = check(certificate, certifier, policy=policy)
        result[source] = target if verdict.status == ADMITTED else source
    return result


def as_repository_comparator(program: LawfulProgram) -> Comparator:
    """Adapter for the preparation replay; closures capture only ``program`` data."""
    def guard(reader: PreActionReader, occasion: Occasion, actual: Response) -> bool:
        label = encode_response(occasion, actual)
        return rule_proposal(program, public_context(reader, occasion), label) is not None

    def propose(reader: PreActionReader, occasion: Occasion, actual: Response):
        label = encode_response(occasion, actual)
        proposal = rule_proposal(program, public_context(reader, occasion), label)
        if proposal is None:
            return None
        target, grounds, authority = proposal
        return decode_action(occasion, target), grounds, authority

    return Comparator(f"phi:{program.program_id}", guard, propose,
                      description=PROGRAM_DESCRIPTIONS[program.program_id])


def repository_action_map(history: ActualHistory, occasion: Occasion,
                          program: LawfulProgram) -> Mapping[Response, Response]:
    actions = canonical_responses(occasion)
    return induced_action_map(history, occasion,
                              as_repository_comparator(program), actions)


def commuting_square_holds(history: ActualHistory, occasion: Occasion,
                           program: LawfulProgram) -> bool:
    label_map = compile_label_map(history, occasion, program)
    repo_map = repository_action_map(history, occasion, program)
    return all(decode_action(occasion, label_map[label])
               == repo_map[decode_action(occasion, label)] for label in LAMBDA)


def label_counterfactual_loss(history: ActualHistory,
                              program: LawfulProgram) -> Q:
    """Additive counterfactual charge in the fixed-label representation."""
    total = Q(0)
    for occasion in history.actual_occasions():
        actual = encode_response(occasion, history.responses[occasion.occasion_id])
        transformed = compile_label_map(history, occasion, program)[actual]
        total += label_loss(occasion, transformed)
    return total


def label_actual_loss(history: ActualHistory) -> Q:
    return sum((label_loss(occasion,
                           encode_response(occasion,
                                           history.responses[occasion.occasion_id]))
                for occasion in history.actual_occasions()), Q(0))


def label_regret(history: ActualHistory, program: LawfulProgram) -> Q:
    return label_actual_loss(history) - label_counterfactual_loss(history, program)


def repository_regret(history: ActualHistory, program: LawfulProgram) -> Q:
    actual = replay(history, as_repository_comparator(AUDITED_PROGRAMS[0]),
                    filings=FILINGS_FROZEN).total_charge
    changed = replay(history, as_repository_comparator(program),
                     filings=FILINGS_FROZEN).total_charge
    return actual - changed


def frozen_environment_violations(history: ActualHistory) -> tuple[str, ...]:
    """The exact assumptions under which repository replay is additive here."""
    problems: list[str] = list(history.well_formed())
    occasions = history.actual_occasions()
    if history.accounting.suspends:
        problems.append("solvency/suspension coupling is enabled")
    if history.filings:
        problems.append("the item-30 bridge requires no endogenous filing source")
    dates = [occasion.date for occasion in occasions]
    if len(dates) != len(set(dates)):
        problems.append("more than one occasion occurs at a date")
    if any(occasion.schedule.service_window != 4 for occasion in occasions):
        problems.append("an occasion has a non-frozen service window")
    if any(occasion.schedule.max_charge > Q(2) for occasion in occasions):
        problems.append("a per-round charge exceeds ell_max = 2")
    for occasion in occasions:
        response = history.responses.get(occasion.occasion_id)
        try:
            if response is None:
                raise ValueError
            encode_response(occasion, response)
        except ValueError:
            problems.append(f"noncanonical actual response at {occasion.occasion_id}")
    maximum_work = max((history.costs.merits_work, history.costs.default_work,
                        history.costs.decline_work), default=Q(0))
    if maximum_work > history.costs.per_date_work:
        problems.append("a single response can exceed per-date service work")
    return tuple(problems)


_EXPECTED_POLICY = (
    bears_on_by_subject,
    magnitude_by_impediment,
    address_by_basis,
    authority_declared,
    reasons_compatible,
)


def non_capture_audit(programs: Sequence[LawfulProgram] = AUDITED_PROGRAMS,
                      policy: PolicySuite = DEFAULT_POLICY) -> tuple[str, ...]:
    """Finite audit of the nine data programs and the five fixed policy functions.

    This certifies this declared finite class, not arbitrary Python callables.
    It assumes the audited modules are not monkey-patched after the audit.
    """
    problems: list[str] = []
    if tuple(programs) != AUDITED_PROGRAMS:
        problems.append("the comparator class differs from the audited nine")
    if len({program.program_id for program in programs}) != 9:
        problems.append("the comparator identifiers are not nine distinct values")
    for program in programs:
        for field_info in fields(program):
            if callable(getattr(program, field_info.name)):
                problems.append(f"{program.program_id} stores executable code")
        if program.parity not in (None, 0, 1):
            problems.append(f"{program.program_id} has an invalid parity")
        if program.kind is ProgramKind.TOLL_DECLINES and program.amount not in (1, 2, 4):
            problems.append(f"{program.program_id} has an unaudited toll amount")

        adapter = as_repository_comparator(program)
        for callback in (adapter.guard, adapter.propose):
            closure = inspect.getclosurevars(callback)
            if set(closure.nonlocals) != {"program"} or closure.nonlocals["program"] != program:
                problems.append(f"{program.program_id} adapter captures non-program state")
            captured = tuple(closure.nonlocals.values()) + tuple(closure.globals.values())
            if any(isinstance(value, (ActualHistory, Occasion, Schedule, Accounting))
                   for value in captured):
                problems.append(f"{program.program_id} adapter captures environment state")

    actual_policy = (policy.bears_on, policy.magnitude_ok, policy.address_ok,
                     policy.authority_ok, policy.reason_compatible)
    if actual_policy != _EXPECTED_POLICY:
        problems.append("the policy suite differs from the audited defaults")
    for function in actual_policy:
        closure = inspect.getclosurevars(function)
        if closure.nonlocals:
            problems.append(f"policy {function.__name__} has a nonlocal capture")
        captured = tuple(closure.nonlocals.values()) + tuple(closure.globals.values())
        if any(isinstance(value, (ActualHistory, Occasion, Schedule, Accounting))
               for value in captured):
            problems.append(f"policy {function.__name__} captures environment state")

    forbidden_context = {"charge", "tariff", "account", "balance", "horizon",
                         "future", "profit", "saving", "response", "ledger",
                         "service_cost"}
    context_names = {field_info.name for field_info in fields(RuleContext)}
    if context_names & forbidden_context:
        problems.append("the rule context exposes a prohibited field")
    return tuple(problems)


def recurrent_failure_lower_bound(failure_mass: Q, saving: Q, transient: Q) -> Q:
    """Finite bound ``failure_mass*δ-B`` for counts or expected mixed mass."""
    if failure_mass < 0 or saving <= 0 or transient < 0:
        raise ValueError("mass, saving, and transient must satisfy m>=0, δ>0, B>=0")
    return Q(failure_mass) * Q(saving) - Q(transient)
