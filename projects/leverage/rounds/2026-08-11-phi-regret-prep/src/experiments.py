"""The thirteen finite experiments, each with its history, its comparators, and
the verdict it is supposed to produce.

Every experiment is a function returning an `Experiment`. The tests assert the
verdicts; the runner prints them. Nothing here is sampled, and every number is an
exact rational.

The suite is organised around one distinction. E1, E2, E6, E7 and E8 are about
**legality** — an edit that would help and is not licensed. E3, E4 and E5 are
about **advantage** — an edit that is licensed, and how much and how often it
helps. E9 through E12 are about **semantics** — what the replay convention
decides, and what it costs. E13 is about **feasibility**, which is neither.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Q
from typing import Callable, Mapping, Sequence

from src.certificates import DEFAULT_POLICY, PolicySuite
from src.model import (
    BASIS_DECLINE,
    BASIS_DEFAULT,
    BASIS_MERITS,
    Accounting,
    ActualHistory,
    ContingentFiling,
    KIND_IMPEDIMENT,
    KIND_INTERVAL,
    KIND_RATIFICATION,
    KIND_RIPENESS,
    LedgerEffect,
    Occasion,
    ObligationRecord,
    PrefixReader,
    ReasonRecord,
    Response,
    Schedule,
    ServiceCosts,
    response_for,
)
from src.replay import (
    FILINGS_ENDOGENOUS,
    FILINGS_FROZEN,
    GUARD_ON_ACTUAL,
    GUARD_ON_REPLAY,
    Comparator,
)

# ---------------------------------------------------------------------------
# Fixture vocabulary
# ---------------------------------------------------------------------------

UPHOLD, DENY, NO_RULING = "uphold", "deny", "no-ruling"

SCHEDULE = Schedule("sch:v1", "claim:standing", Q(1, 2), UPHOLD, DENY, NO_RULING,
                    default_tariff=Q(1), refusal_tariff=Q(1, 2), service_window=4)

COSTS = ServiceCosts(per_date_work=Q(3), merits_work=Q(1), default_work=Q(1, 2))

DECLINE_CHARGE = Q(1, 2) * 4  # 2
DEFAULT_CHARGE = Q(1)


def occasion(index: int, *, date: int | None = None, account: str = "acct:main",
             schedule: Schedule = SCHEDULE) -> Occasion:
    return Occasion(f"o:{index}", date if date is not None else index,
                    f"q:{index}", account, schedule)


def clearing_interval(index: int, *, filed_at: int = 0, lower: Q = Q(3, 5),
                      upper: Q = Q(4, 5), **extra) -> ReasonRecord:
    """An interval that separates the threshold upward: a positive merits ruling
    is available from `filed_at` onward."""
    return ReasonRecord(f"r:interval:{index}", KIND_INTERVAL, f"q:{index}", filed_at,
                        ("basis", "verdict"), {"lower": lower, "upper": upper},
                        **extra)


def straddling_interval(index: int, *, filed_at: int = 0) -> ReasonRecord:
    """An interval containing the threshold: no merits direction is available."""
    return ReasonRecord(f"r:interval:{index}", KIND_INTERVAL, f"q:{index}", filed_at,
                        ("basis", "verdict"), {"lower": Q(2, 5), "upper": Q(3, 5)})


def impediment(index: int, dates: int, *, filed_at: int = 0,
               defeated_at: int | None = None,
               subject: str | None = None) -> ReasonRecord:
    return ReasonRecord(f"r:imped:{index}", KIND_IMPEDIMENT,
                        subject or f"q:{index}", filed_at, ("tolled",),
                        {"dates": dates}, defeated_at=defeated_at)


def ripeness(index: int, *, filed_at: int = 0) -> ReasonRecord:
    """A ground licensing withdrawal of a disposition to a decline: the question
    is not ripe on the record available."""
    return ReasonRecord(f"r:ripe:{index}", KIND_RIPENESS, f"q:{index}", filed_at,
                        ("basis",), {})


def ratification(index: int, *, filed_at: int, ratifies: tuple[str, ...]
                 ) -> ReasonRecord:
    return ReasonRecord(f"r:ratify:{index}", KIND_RATIFICATION, f"q:{index}",
                        filed_at, ("basis", "verdict"), {"ratifies": ratifies})


def declines(occasions: Sequence[Occasion]) -> dict[str, Response]:
    return {o.occasion_id: response_for(o, BASIS_DECLINE) for o in occasions}


def history(history_id: str, occasions: Sequence[Occasion],
            responses: Mapping[str, Response],
            reasons: Sequence[ReasonRecord] = (), *,
            horizon: int | None = None,
            obligations: Sequence[ObligationRecord] = (),
            costs: ServiceCosts = COSTS,
            accounting: Accounting | None = None,
            filings: Sequence[ContingentFiling] = ()) -> ActualHistory:
    limit = horizon if horizon is not None else max(o.date for o in occasions) + 1
    return ActualHistory(history_id, limit, tuple(occasions), dict(responses),
                         tuple(reasons), tuple(obligations), costs,
                         accounting or Accounting({}, suspends=False),
                         tuple(filings))


# ---------------------------------------------------------------------------
# Comparator constructors
# ---------------------------------------------------------------------------


def repair_declines(phi_id: str, *, targets: Sequence[str] | None = None,
                    once: bool = False, guard_on: str = GUARD_ON_ACTUAL,
                    description: str = "") -> Comparator:
    """Rule on the merits wherever the learner declined and a live interval
    separating the bound threshold is on the record.

    The canonical repair of this substrate, and the one the recurrence witness
    uses. It cites exactly the interval it relies on.
    """
    allowed = set(targets) if targets is not None else None

    def guard(reader: PrefixReader, occ: Occasion, actual: Response) -> bool:
        if allowed is not None and occ.occasion_id not in allowed:
            return False
        if actual.basis != BASIS_DECLINE:
            return False
        return any(r.kind == KIND_INTERVAL and r.subject == occ.target
                   and r.live_at(reader.date) for r in reader.reasons())

    def propose(reader: PrefixReader, occ: Occasion, actual: Response):
        grounds = tuple(r.reason_id for r in reader.reasons()
                        if r.kind == KIND_INTERVAL and r.subject == occ.target)
        return (response_for(occ, BASIS_MERITS, verdict=UPHOLD), grounds,
                "auth:review")

    return Comparator(phi_id, guard, propose, once, guard_on,
                      description or "decline to merits where the interval clears")


def toll_declines(phi_id: str, amount: int, *,
                  targets: Sequence[str] | None = None) -> Comparator:
    """Claim `amount` tolled dates on a declined occasion, citing the impediments
    on the record for its target."""
    allowed = set(targets) if targets is not None else None

    def guard(reader: PrefixReader, occ: Occasion, actual: Response) -> bool:
        if allowed is not None and occ.occasion_id not in allowed:
            return False
        return actual.basis == BASIS_DECLINE and any(
            r.kind == KIND_IMPEDIMENT and r.subject == occ.target
            for r in reader.reasons())

    def propose(reader: PrefixReader, occ: Occasion, actual: Response):
        grounds = tuple(r.reason_id for r in reader.reasons()
                        if r.kind == KIND_IMPEDIMENT and r.subject == occ.target)
        return (response_for(occ, BASIS_DECLINE, tolled=amount), grounds,
                "auth:review")

    return Comparator(phi_id, guard, propose, False, GUARD_ON_ACTUAL,
                      f"claim {amount} tolled dates on a declined occasion")


def fixed_edit(phi_id: str, occasion_id: str,
               replacement: Callable[[Occasion], Response],
               grounds: Sequence[str], *, once: bool = True,
               description: str = "") -> Comparator:
    """A comparator that edits one named occasion, citing named grounds."""

    def guard(reader: PrefixReader, occ: Occasion, actual: Response) -> bool:
        return occ.occasion_id == occasion_id

    def propose(reader: PrefixReader, occ: Occasion, actual: Response):
        return (replacement(occ), tuple(grounds), "auth:review")

    return Comparator(phi_id, guard, propose, once, GUARD_ON_ACTUAL, description)


# ---------------------------------------------------------------------------
# The experiment record
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Experiment:
    label: str
    title: str
    history: ActualHistory
    comparators: tuple[Comparator, ...]
    expectation: str
    policy: PolicySuite = DEFAULT_POLICY
    filings: str = FILINGS_FROZEN
    notes: str = ""


# ---------------------------------------------------------------------------
# E1 — profitable but unlawful
# ---------------------------------------------------------------------------


def e1_profitable_but_unlawful() -> Experiment:
    occasions = [occasion(i) for i in range(4)]
    reasons = [straddling_interval(1)]
    phi = fixed_edit("phi:e1", "o:1",
                     lambda o: response_for(o, BASIS_MERITS, verdict=UPHOLD),
                     ("r:interval:1",),
                     description="rule on the merits with an interval that does "
                                 "not separate the threshold")
    return Experiment(
        "E1", "profitable but unlawful",
        history("h:e1", occasions, declines(occasions), reasons),
        (phi,),
        "rejected as certificate.replacement_unsupported; the run is unchanged "
        f"though the edit would have saved {DECLINE_CHARGE}")


# ---------------------------------------------------------------------------
# E2 — successor ratification
# ---------------------------------------------------------------------------


def e2_successor_ratification() -> Experiment:
    occasions = [occasion(i) for i in range(4)]
    reasons = [straddling_interval(1),
               ReasonRecord("r:interval:late", KIND_INTERVAL, "q:1", 3,
                            ("basis", "verdict"),
                            {"lower": Q(3, 5), "upper": Q(4, 5)}),
               ReasonRecord("r:ratify:early", KIND_RATIFICATION, "q:1", 0,
                            ("basis", "verdict"), {"ratifies": ("o:1",)})]
    later = fixed_edit("phi:e2-later", "o:1",
                       lambda o: response_for(o, BASIS_MERITS, verdict=UPHOLD),
                       ("r:interval:late",),
                       description="cite an interval that only exists later")
    endorsed = fixed_edit("phi:e2-endorsed", "o:1",
                          lambda o: response_for(o, BASIS_MERITS, verdict=UPHOLD),
                          ("r:ratify:early",),
                          description="cite an endorsement present in the prefix")
    return Experiment(
        "E2", "successor ratification",
        history("h:e2", occasions, declines(occasions), reasons),
        (later, endorsed),
        "the later interval is not on the record at the edit's date; the "
        "endorsement is on it and is still not a ground")


# ---------------------------------------------------------------------------
# E3 — lawful one-shot repair
# ---------------------------------------------------------------------------


def e3_lawful_one_shot() -> Experiment:
    occasions = [occasion(i) for i in range(4)]
    reasons = [clearing_interval(1)]
    phi = repair_declines("phi:e3", targets=("o:1",), once=True)
    return Experiment(
        "E3", "lawful one-shot repair",
        history("h:e3", occasions, declines(occasions), reasons),
        (phi,),
        f"admitted; the replay charge falls by exactly {DECLINE_CHARGE} and no "
        "other occasion moves")


# ---------------------------------------------------------------------------
# E4 — recurrent remediable failure
# ---------------------------------------------------------------------------


def e4_recurrent(horizon: int = 24, stride: int = 3) -> Experiment:
    occasions = [occasion(i) for i in range(horizon)]
    recognised = [f"o:{i}" for i in range(0, horizon, stride)]
    reasons = [clearing_interval(i) for i in range(0, horizon, stride)]
    phi = repair_declines("phi:e4")
    return Experiment(
        "E4", "recurrent remediable failure",
        history("h:e4", occasions, declines(occasions), reasons),
        (phi,),
        f"admitted on every one of the {len(recognised)} recognised occasions, "
        f"saving {DECLINE_CHARGE} each; the advantage is linear in the horizon",
        notes=f"recognised: {len(recognised)} of {horizon}")


# ---------------------------------------------------------------------------
# E5 — non-recurrent improvement
# ---------------------------------------------------------------------------


def e5_non_recurrent(horizon: int = 24, occurrences: int = 4) -> Experiment:
    occasions = [occasion(i) for i in range(horizon)]
    reasons = [clearing_interval(i) for i in range(occurrences)]
    phi = repair_declines("phi:e5")
    return Experiment(
        "E5", "non-recurrent improvement",
        history("h:e5", occasions, declines(occasions), reasons),
        (phi,),
        f"admitted {occurrences} times whatever the horizon; the advantage is "
        "constant and the normalized regret falls to zero")


# ---------------------------------------------------------------------------
# E6 — magnitude overreach
# ---------------------------------------------------------------------------


def e6_magnitude() -> Experiment:
    occasions = [occasion(i) for i in range(3)]
    reasons = [impediment(1, dates=2)]
    within = toll_declines("phi:e6-within", 2, targets=("o:1",))
    beyond = toll_declines("phi:e6-beyond", 4, targets=("o:1",))
    return Experiment(
        "E6", "magnitude overreach",
        history("h:e6", occasions, declines(occasions), reasons),
        (within, beyond),
        "two tolled dates are licensed and admitted; four are directionally "
        "supported and left unresolved by the magnitude predicate")


# ---------------------------------------------------------------------------
# E7 — defeated reason
# ---------------------------------------------------------------------------


def e7_defeated() -> Experiment:
    shared = Schedule("sch:v1", "claim:standing", Q(1, 2), UPHOLD, DENY, NO_RULING,
                      Q(1), Q(1, 2), 4)
    early = Occasion("o:early", 3, "q:supply", "acct:main", shared)
    late = Occasion("o:late", 9, "q:supply", "acct:main", shared)
    occasions = [early, late]
    reasons = [impediment(0, dates=2, filed_at=0, defeated_at=6,
                          subject="q:supply")]
    phi = toll_declines("phi:e7", 2)
    return Experiment(
        "E7", "defeated reason",
        history("h:e7", occasions, declines(occasions), reasons, horizon=12),
        (phi,),
        "the same edit is admitted at date 3 and refused at date 9, because the "
        "ground it cites stops being live at date 6")


# ---------------------------------------------------------------------------
# E8 — burden laundering
# ---------------------------------------------------------------------------


def e8_burden_laundering() -> Experiment:
    occasions = [occasion(i) for i in range(3)]
    inherited = ObligationRecord("d:inherited", None, 0, lineage=("d:origin",))
    reasons = [clearing_interval(1), ripeness(1)]
    erase = fixed_edit(
        "phi:e8-erase", "o:1",
        lambda o: Response(BASIS_DECLINE, None, 0,
                           LedgerEffect(drops=("d:o:1",))),
        ("r:ripe:1",),
        description="strike the occasion's own obligation from the record")
    annex = fixed_edit(
        "phi:e8-annex", "o:1",
        lambda o: Response(BASIS_MERITS, UPHOLD, 0,
                           LedgerEffect(closes=(("d:o:1", "discharge"),
                                                ("d:inherited", "discharge")))),
        ("r:interval:1",),
        description="discharge an inherited obligation alongside its own")
    return Experiment(
        "E8", "burden laundering",
        history("h:e8", occasions, declines(occasions), reasons,
                obligations=(inherited,)),
        (erase, annex),
        "striking the obligation would zero the charge and is refused as "
        "burden.dropped; annexing the inherited obligation is refused as "
        "burden.foreign_closure")


# ---------------------------------------------------------------------------
# E9 / E10 — one history, three accounting configurations
# ---------------------------------------------------------------------------


def _divergence_history(history_id: str, horizon: int,
                        accounting: Accounting) -> ActualHistory:
    """One lawful edit at date 0, and a long tail the edit does not touch.

    The actual run rules on the merits throughout and is charged nothing. The
    edit withdraws the first disposition to a decline on a ripeness ground, which
    is licensed and costs two. What that two does to the rest of the run is
    entirely a question about the accounting configuration, which is the point.
    """
    first = occasion(0, account="acct:edited")
    tail = [occasion(i, account="acct:rest") for i in range(1, horizon)]
    occasions = [first] + tail
    responses = {o.occasion_id: response_for(o, BASIS_MERITS, verdict=UPHOLD)
                 for o in occasions}
    reasons = [ripeness(0)] + [clearing_interval(i) for i in range(horizon)]
    return history(history_id, occasions, responses, reasons,
                   accounting=accounting)


def _withdraw_first() -> Comparator:
    return fixed_edit("phi:withdraw", "o:0",
                      lambda o: response_for(o, BASIS_DECLINE),
                      ("r:ripe:0",),
                      description="withdraw the first merits ruling as unripe")


def e9_fenced_locality(horizon: int = 12) -> Experiment:
    accounting = Accounting({"acct:edited": Q(1), "acct:rest": Q(10) ** 6},
                            suspends=True)
    return Experiment(
        "E9", "fenced locality",
        _divergence_history("h:e9", horizon, accounting),
        (_withdraw_first(),),
        "the edit exhausts its own account's reserve and suspends nothing else; "
        f"divergence is exactly {DECLINE_CHARGE} at every horizon")


def e10_pooled_divergence(horizon: int = 12) -> Experiment:
    accounting = Accounting({"acct:pool": Q(1)}, pooled_account="acct:pool",
                            suspends=True)
    return Experiment(
        "E10", "pooled divergence",
        _divergence_history("h:e10", horizon, accounting),
        (_withdraw_first(),),
        "the same edit exhausts the shared reserve, service is withdrawn from "
        "every later occasion, and divergence grows linearly in the horizon")


def e10b_fenced_but_shared(horizon: int = 12) -> Experiment:
    """The fenced bound is attained: one fence containing the whole run."""
    first = occasion(0, account="acct:one")
    tail = [occasion(i, account="acct:one") for i in range(1, horizon)]
    occasions = [first] + tail
    responses = {o.occasion_id: response_for(o, BASIS_MERITS, verdict=UPHOLD)
                 for o in occasions}
    reasons = [ripeness(0)] + [clearing_interval(i) for i in range(horizon)]
    accounting = Accounting({"acct:one": Q(1)}, suspends=True)
    return Experiment(
        "E10b", "fencing alone does not bound divergence",
        history("h:e10b", occasions, responses, reasons, accounting=accounting),
        (_withdraw_first(),),
        "a fence containing the whole run gives a horizon-sized bound, and the "
        "witness attains it")


def e10c_no_solvency_coupling(horizon: int = 12) -> Experiment:
    accounting = Accounting({"acct:edited": Q(1), "acct:rest": Q(1)},
                            suspends=False)
    return Experiment(
        "E10c", "locality under no solvency coupling",
        _divergence_history("h:e10c", horizon, accounting),
        (_withdraw_first(),),
        "with the coupling switched off, divergence is the per-occasion charge "
        "difference of the occasions the comparator fired on, and nothing else")


# ---------------------------------------------------------------------------
# E11 — guard on the actual prefix versus the replayed prefix
# ---------------------------------------------------------------------------


def _cascade_guard(phi_id: str, guard_on: str) -> Comparator:
    """Fire at the first occasion unconditionally, and afterwards only where the
    declared prefix still shows a decline."""

    def guard(reader: PrefixReader, occ: Occasion, actual: Response) -> bool:
        if actual.basis != BASIS_DECLINE:
            return False
        if occ.occasion_id == "o:0":
            return True
        return any(r is not None and r.basis == BASIS_DECLINE
                   for r in (reader.response(o.occasion_id)
                             for o in reader.occasions()
                             if o.date < occ.date))

    def propose(reader: PrefixReader, occ: Occasion, actual: Response):
        grounds = tuple(r.reason_id for r in reader.reasons()
                        if r.kind == KIND_INTERVAL and r.subject == occ.target)
        return (response_for(occ, BASIS_MERITS, verdict=UPHOLD), grounds,
                "auth:review")

    return Comparator(phi_id, guard, propose, False, guard_on,
                      f"cascade, guarded on the {guard_on} prefix")


def e11_guard_convention() -> Experiment:
    occasions = [occasion(i) for i in range(3)]
    reasons = [clearing_interval(i) for i in range(3)]
    return Experiment(
        "E11", "guard on the actual prefix versus the replayed prefix",
        history("h:e11", occasions, declines(occasions), reasons),
        (_cascade_guard("phi:e11-actual", GUARD_ON_ACTUAL),
         _cascade_guard("phi:e11-replay", GUARD_ON_REPLAY)),
        "the actual-prefix guard fires at all three occasions; the "
        "replayed-prefix guard skips the second, because the first edit removes "
        "the decline its condition reads, and fires again at the third once the "
        "unedited second occasion restores it")


# ---------------------------------------------------------------------------
# E12 — frozen filings
# ---------------------------------------------------------------------------


def e12_frozen_filings() -> Experiment:
    trigger = occasion(0)
    consequent = [occasion(i, date=i) for i in range(1, 4)]
    filing = ContingentFiling("f:persistence", "o:0", BASIS_DECLINE,
                              tuple(consequent))
    responses = declines([trigger] + consequent)
    reasons = [clearing_interval(0)]
    phi = repair_declines("phi:e12", targets=("o:0",), once=True)
    return Experiment(
        "E12", "frozen filings",
        history("h:e12", [trigger], responses, reasons, horizon=4,
                filings=(filing,)),
        (phi,),
        "under frozen filings the comparator's advantage is the trigger's own "
        "charge; recomputing the filings from the replayed responses shows the "
        "freeze undercounts it by the whole consequent stream")


# ---------------------------------------------------------------------------
# E13 — a lawful comparator the declared service work cannot afford
# ---------------------------------------------------------------------------


def e13_resource_infeasible() -> Experiment:
    occasions = [occasion(i, date=0) for i in range(3)]
    reasons = [clearing_interval(i) for i in range(3)]
    costs = ServiceCosts(per_date_work=Q(2), merits_work=Q(1), default_work=Q(1, 2))
    every = repair_declines("phi:e13-all")
    two = repair_declines("phi:e13-two", targets=("o:0", "o:1"))
    return Experiment(
        "E13", "a lawful comparator the service work cannot afford",
        history("h:e13", occasions, declines(occasions), reasons, horizon=1,
                costs=costs),
        (every, two),
        "both comparators are licensed; the one that rules three times in a date "
        "overruns the declared work and is inadmissible, and its advantage is "
        "reported rather than netted against anything")


# ---------------------------------------------------------------------------


ALL: tuple[Callable[[], Experiment], ...] = (
    e1_profitable_but_unlawful,
    e2_successor_ratification,
    e3_lawful_one_shot,
    e4_recurrent,
    e5_non_recurrent,
    e6_magnitude,
    e7_defeated,
    e8_burden_laundering,
    e9_fenced_locality,
    e10_pooled_divergence,
    e10b_fenced_but_shared,
    e10c_no_solvency_coupling,
    e11_guard_convention,
    e12_frozen_filings,
    e13_resource_infeasible,
)
