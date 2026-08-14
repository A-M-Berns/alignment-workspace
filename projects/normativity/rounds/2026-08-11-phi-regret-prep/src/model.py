"""The finite substrate: occasions, responses, reason records, and the reader.

Everything here is exact: charges are `fractions.Fraction`, dates are integers,
and no quantity is sampled or approximated.

The one structural commitment worth stating up front is the **reader**. A
lawful-edit certificate is checked through `PrefixReader`, which logs every
table it is asked for and refuses names outside a declared footprint. The
certifier's footprint does not contain the charge table, so a certificate cannot
be a function of what an edit costs even by accident. This is the mechanism the
objection grammar already uses to keep a judge inside its declaration
(`GR-J1`, `projects/leverage/consolidation-aug9/THEORY_7_OBJECTION_GRAMMAR.md`);
it is reused here for a different purpose, which is keeping profitability out of
legitimacy.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from fractions import Fraction as Q
from typing import Mapping, Sequence

# ---------------------------------------------------------------------------
# Responses
# ---------------------------------------------------------------------------

BASIS_MERITS = "merits"
BASIS_DEFAULT = "default"
BASIS_DECLINE = "decline"
BASES = (BASIS_MERITS, BASIS_DEFAULT, BASIS_DECLINE)

CLOSURE_DISCHARGE = "discharge"
CLOSURE_PROCEDURAL = "procedural"
CLOSURE_WITHDRAWAL = "withdrawal"


@dataclass(frozen=True)
class LedgerEffect:
    """What a response does to the answerability record.

    An adapter over the obligation algebra of
    `projects/leverage/forward/src/answerability.py`, narrowed to the fields a
    lawful-edit check needs: which obligations close and how, which are
    retargeted, and which disappear. `drops` exists so that laundering has a
    representable shape; nothing licensed ever populates it.
    """

    closes: tuple[tuple[str, str], ...] = ()
    retargets: tuple[tuple[str, str], ...] = ()
    drops: tuple[str, ...] = ()


@dataclass(frozen=True)
class Response:
    """One local disposition of one occasion.

    `tolled` is the number of dates the response claims are excluded from the
    refusal clock. It is the magnitude coordinate of this substrate: a recorded
    impediment supports tolling in the direction of *some* exclusion without
    thereby supporting any particular amount (`CD-J9`).
    """

    basis: str
    verdict: str | None = None
    tolled: int = 0
    ledger: LedgerEffect = field(default_factory=LedgerEffect)

    def well_formed(self) -> bool:
        if self.basis not in BASES:
            return False
        if self.basis == BASIS_MERITS and not self.verdict:
            return False
        if self.basis != BASIS_DECLINE and self.tolled:
            return False
        return self.tolled >= 0

    @property
    def fields(self) -> frozenset[str]:
        return frozenset(("basis", "verdict", "tolled", "ledger"))


def changed_fields(old: Response, new: Response) -> frozenset[str]:
    """Which coordinates an edit moves. Scope discipline is stated over these."""
    moved = set()
    if old.basis != new.basis:
        moved.add("basis")
    if old.verdict != new.verdict:
        moved.add("verdict")
    if old.tolled != new.tolled:
        moved.add("tolled")
    if old.ledger != new.ledger:
        moved.add("ledger")
    return frozenset(moved)


# ---------------------------------------------------------------------------
# Occasions and the schedule bound at arrival
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Schedule:
    """Procedural content bound to an occasion when it arrives, and frozen.

    `service_window` is the declared number of dates over which refusal accrues
    for an undisposed occasion. It exists so that per-occasion loss is bounded,
    which the intended online-learning machinery needs; the accrual rule itself
    is the clock rule of `CD-J8` with horizon set to admission plus the window.
    """

    schedule_id: str
    claim_type: str
    threshold: Q
    positive_verdict: str
    negative_verdict: str
    fallback_verdict: str
    default_tariff: Q
    refusal_tariff: Q
    service_window: int

    def well_formed(self) -> bool:
        return (Q(0) < Q(self.threshold) < Q(1)
                and Q(self.default_tariff) >= 0 and Q(self.refusal_tariff) >= 0
                and self.service_window >= 0
                and len({self.positive_verdict, self.negative_verdict,
                         self.fallback_verdict}) >= 2)

    @property
    def max_charge(self) -> Q:
        return max(Q(self.default_tariff),
                   Q(self.refusal_tariff) * self.service_window)


@dataclass(frozen=True)
class Occasion:
    """One admitted question the learner must dispose of.

    `account` names the stream the occasion's charges land in. Under a declared
    fence the streams are separate; a pooled system declares one account for
    everything, which is `CS-J5` read as a configuration rather than as an
    objection.
    """

    occasion_id: str
    date: int
    target: str
    account: str
    schedule: Schedule


# ---------------------------------------------------------------------------
# The reason state
# ---------------------------------------------------------------------------

KIND_INTERVAL = "interval"
KIND_IMPEDIMENT = "impediment"
KIND_RIPENESS = "ripeness"
KIND_AUTHORITY = "authority"
KIND_RATIFICATION = "ratification"
REASON_KINDS = (KIND_INTERVAL, KIND_IMPEDIMENT, KIND_RIPENESS, KIND_AUTHORITY,
                KIND_RATIFICATION)


@dataclass(frozen=True)
class ReasonRecord:
    """A ground an edit may cite, with everything a check needs to reject it.

    `filed_at` is the date from which the ground is on the record; `defeated_at`
    and `suspended_at` are the dates from which it stops being live.
    `licenses` is the set of response coordinates this ground can move, which is
    what scope discipline is checked against.
    """

    reason_id: str
    kind: str
    subject: str
    filed_at: int
    licenses: tuple[str, ...] = ()
    payload: Mapping[str, object] = field(default_factory=dict)
    defeated_at: int | None = None
    suspended_at: int | None = None

    def live_at(self, date: int) -> bool:
        if self.filed_at > date:
            return False
        for stop in (self.defeated_at, self.suspended_at):
            if stop is not None and stop <= date:
                return False
        return True


@dataclass(frozen=True)
class ObligationRecord:
    """An answerability obligation, as much of one as this substrate needs.

    `lineage` non-empty marks an inherited obligation: one filed by an earlier
    occasion or carried across a boundary. Burden discipline turns on the
    distinction, because closing your own decision obligation is the ordinary
    thing a disposition does, and closing someone else's is laundering.
    """

    obligation_id: str
    owner_occasion: str | None
    filed_at: int
    lineage: tuple[str, ...] = ()


def decision_obligation(occasion: Occasion) -> ObligationRecord:
    return ObligationRecord(f"d:{occasion.occasion_id}", occasion.occasion_id,
                            occasion.date)


# ---------------------------------------------------------------------------
# Contingent filings — the object frozen replay freezes
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ContingentFiling:
    """Occasions that arrive only because an earlier occasion went a certain way.

    Under v1 replay these are frozen to what the *actual* history produced. The
    alternative — recomputing them from the replayed responses — is implemented
    so the cost of the freeze is measurable rather than asserted.
    """

    filing_id: str
    trigger_occasion: str
    fires_when_basis: str
    occasions: tuple[Occasion, ...]


# ---------------------------------------------------------------------------
# Resources, accounts, and the run configuration
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ServiceCosts:
    """Declared work per date and per disposition. Never converted to charge."""

    per_date_work: Q
    merits_work: Q
    default_work: Q
    decline_work: Q = Q(0)

    def work_of(self, response: Response) -> Q:
        if response.basis == BASIS_MERITS:
            return Q(self.merits_work)
        if response.basis == BASIS_DEFAULT:
            return Q(self.default_work)
        return Q(self.decline_work)


@dataclass(frozen=True)
class Accounting:
    """Where charges land and what happens when an account is exhausted.

    A fenced configuration gives each account its own reserve; a pooled one puts
    every occasion in a single account. `suspends` says whether exhausting a
    reserve withdraws merits service from that account's later occasions — the
    coupling that makes one local edit able to move a suspension date.
    """

    reserves: Mapping[str, Q]
    pooled_account: str | None = None
    suspends: bool = True

    def account_of(self, occasion: Occasion) -> str:
        return self.pooled_account or occasion.account

    @property
    def fenced(self) -> bool:
        return self.pooled_account is None


@dataclass(frozen=True)
class ActualHistory:
    """A finite actual run: what arrived, what the learner did, what was on the
    record when it did it."""

    history_id: str
    horizon: int
    base_occasions: tuple[Occasion, ...]
    responses: Mapping[str, Response]
    reasons: tuple[ReasonRecord, ...]
    obligations: tuple[ObligationRecord, ...]
    costs: ServiceCosts
    accounting: Accounting
    filings: tuple[ContingentFiling, ...] = ()

    def actual_occasions(self) -> tuple[Occasion, ...]:
        """Base arrivals plus whatever the actual responses caused to be filed."""
        live = list(self.base_occasions)
        for filing in self.filings:
            actual = self.responses.get(filing.trigger_occasion)
            if actual is not None and actual.basis == filing.fires_when_basis:
                live.extend(filing.occasions)
        return tuple(sorted(live, key=lambda o: (o.date, o.occasion_id)))

    def reason(self, reason_id: str) -> ReasonRecord | None:
        for record in self.reasons:
            if record.reason_id == reason_id:
                return record
        return None

    def well_formed(self) -> list[str]:
        problems: list[str] = []
        seen: set[str] = set()
        for occasion in self.actual_occasions():
            if occasion.occasion_id in seen:
                problems.append(f"duplicate occasion {occasion.occasion_id!r}")
            seen.add(occasion.occasion_id)
            if not occasion.schedule.well_formed():
                problems.append(f"malformed schedule on {occasion.occasion_id!r}")
            if occasion.date >= self.horizon:
                problems.append(f"occasion {occasion.occasion_id!r} past the horizon")
            response = self.responses.get(occasion.occasion_id)
            if response is None:
                problems.append(f"no actual response for {occasion.occasion_id!r}")
            elif not response.well_formed():
                problems.append(f"malformed response on {occasion.occasion_id!r}")
        for record in self.reasons:
            if record.kind not in REASON_KINDS:
                problems.append(f"unknown reason kind {record.kind!r}")
        return problems


# ---------------------------------------------------------------------------
# The access-logged reader
# ---------------------------------------------------------------------------

TABLES = ("occasions", "responses", "reasons", "obligations", "charges", "accounts")

#: What a certifier may read. The absence of `charges` and `accounts` is the
#: whole of the no-cost-laundering guarantee, and it is structural.
CERTIFIER_FOOTPRINT = ("occasions", "responses", "reasons", "obligations")

#: What a comparator guard may read. The same restriction, for the same reason:
#: a guard that could see charges would select edits by profitability.
GUARD_FOOTPRINT = ("occasions", "responses", "reasons", "obligations")


class FootprintViolation(RuntimeError):
    """Raised when a reader is asked for a table outside its declaration."""


class PrefixReader:
    """A view of the record up to a date, logging every table it is asked for.

    The log is appended to before the value is returned, including on a
    membership probe, so it is a superset of what the caller used. A name
    outside the declaration raises rather than returning, which makes the
    footprint a precondition on the check rather than a report about it.
    """

    def __init__(self, history: ActualHistory, date: int,
                 footprint: Sequence[str],
                 responses: Mapping[str, Response] | None = None,
                 occasions: Sequence[Occasion] | None = None) -> None:
        unknown = [name for name in footprint if name not in TABLES]
        if unknown:
            raise FootprintViolation(f"unregistered tables declared: {unknown}")
        self._history = history
        self._date = date
        self._footprint = tuple(footprint)
        self._responses = responses if responses is not None else history.responses
        self._occasions = tuple(occasions if occasions is not None
                                else history.actual_occasions())
        self.log: list[str] = []

    @property
    def date(self) -> int:
        return self._date

    @property
    def footprint(self) -> tuple[str, ...]:
        return self._footprint

    def _read(self, table: str):
        self.log.append(table)
        if table not in self._footprint:
            raise FootprintViolation(
                f"{table!r} is not in the declared footprint {self._footprint}")
        return table

    def occasions(self) -> tuple[Occasion, ...]:
        self._read("occasions")
        return tuple(o for o in self._occasions if o.date <= self._date)

    def occasion(self, occasion_id: str) -> Occasion | None:
        self._read("occasions")
        for occasion in self._occasions:
            if occasion.occasion_id == occasion_id and occasion.date <= self._date:
                return occasion
        return None

    def response(self, occasion_id: str) -> Response | None:
        self._read("responses")
        occasion = next((o for o in self._occasions
                         if o.occasion_id == occasion_id), None)
        if occasion is None or occasion.date > self._date:
            return None
        return self._responses.get(occasion_id)

    def reasons(self) -> tuple[ReasonRecord, ...]:
        self._read("reasons")
        return tuple(r for r in self._history.reasons if r.filed_at <= self._date)

    def reason(self, reason_id: str) -> ReasonRecord | None:
        """A ground filed after the prefix is invisible, not merely inadmissible.

        Returning `None` rather than the future record is what makes historical
        availability a property of the view instead of a rule a checker could
        forget to apply.
        """
        self._read("reasons")
        record = self._history.reason(reason_id)
        if record is None or record.filed_at > self._date:
            return None
        return record

    def obligations(self) -> tuple[ObligationRecord, ...]:
        self._read("obligations")
        inherited = tuple(o for o in self._history.obligations
                          if o.filed_at <= self._date)
        derived = tuple(decision_obligation(o) for o in self._occasions
                        if o.date <= self._date)
        return inherited + derived

    def outside_footprint(self) -> tuple[str, ...]:
        return tuple(sorted({name for name in self.log
                             if name not in self._footprint}))


def reader_at(history: ActualHistory, date: int, footprint: Sequence[str],
              responses: Mapping[str, Response] | None = None,
              occasions: Sequence[Occasion] | None = None) -> PrefixReader:
    return PrefixReader(history, date, footprint, responses, occasions)


def derived_ledger_effect(occasion: Occasion, basis: str) -> LedgerEffect:
    """The closure a basis licenses on its own decision obligation, and nothing else.

    Merits discharges; a scheduled default closes procedurally; a decline leaves
    the obligation open. These are the only ledger effects any response of this
    substrate is entitled to, which is what makes any other effect visible.
    """
    identifier = f"d:{occasion.occasion_id}"
    if basis == BASIS_MERITS:
        return LedgerEffect(closes=((identifier, CLOSURE_DISCHARGE),))
    if basis == BASIS_DEFAULT:
        return LedgerEffect(closes=((identifier, CLOSURE_PROCEDURAL),))
    return LedgerEffect()


def response_for(occasion: Occasion, basis: str, *, verdict: str | None = None,
                 tolled: int = 0) -> Response:
    """The canonical response of a basis, with its derived ledger effect."""
    return Response(basis, verdict, tolled, derived_ledger_effect(occasion, basis))


def with_ledger(response: Response, effect: LedgerEffect) -> Response:
    return replace(response, ledger=effect)
