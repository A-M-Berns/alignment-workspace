"""Cumulative charge, comparator advantage, and the locality bound.

Sign convention, fixed once: `R_T(phi) = L_T(H) - L_T(H^phi)`. Positive regret
means the learner paid more than the lawful comparator would have. A comparator
that is worse than the learner has negative regret. Nothing here reads a
certificate: admissibility has already been decided by the time a charge is
compared, and the two are kept apart so that neither can quietly define the
other.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.certificates import DEFAULT_POLICY, PolicySuite
from src.model import ActualHistory, Occasion
from src.replay import Comparator, ReplayRun, actual_run, replay


@dataclass(frozen=True)
class ComparatorResult:
    phi_id: str
    admissible: bool
    inadmissible_because: str
    actual_charge: Q
    replay_charge: Q
    firings: tuple[str, ...]
    rejections: tuple[tuple[str, str], ...]
    run: ReplayRun

    @property
    def regret(self) -> Q:
        return self.actual_charge - self.replay_charge

    @property
    def fired(self) -> int:
        return len(self.firings)


def evaluate(history: ActualHistory, comparator: Comparator, *,
             policy: PolicySuite = DEFAULT_POLICY,
             baseline: ReplayRun | None = None,
             filings: str = "frozen") -> ComparatorResult:
    """Run one comparator against one actual history.

    A comparator whose replay overruns the declared per-date service work is
    **inadmissible**, and its charge advantage is reported rather than suppressed
    so that a reader can see what the resource constraint cost. It is not netted
    against the charge, and no exchange rate between work and charge is invented.
    """
    base = baseline or actual_run(history, policy=policy, filings=filings)
    run = replay(history, comparator, policy=policy, filings=filings)
    reason = "" if run.feasible else f"service work overrun at dates {run.overrun_dates}"
    return ComparatorResult(comparator.phi_id, run.feasible, reason,
                            base.total_charge, run.total_charge, run.firings,
                            run.rejections, run)


@dataclass(frozen=True)
class RegretReport:
    history_id: str
    horizon: int
    occasions: int
    actual_charge: Q
    results: tuple[ComparatorResult, ...]

    @property
    def admissible(self) -> tuple[ComparatorResult, ...]:
        return tuple(r for r in self.results if r.admissible)

    @property
    def sup_regret(self) -> Q:
        candidates = [r.regret for r in self.admissible]
        return max(candidates) if candidates else Q(0)

    @property
    def best(self) -> ComparatorResult | None:
        admissible = self.admissible
        if not admissible:
            return None
        return max(admissible, key=lambda r: r.regret)

    def normalized(self) -> Q:
        return self.sup_regret / self.occasions if self.occasions else Q(0)


def evaluate_class(history: ActualHistory, comparators: Sequence[Comparator], *,
                   policy: PolicySuite = DEFAULT_POLICY,
                   filings: str = "frozen") -> RegretReport:
    base = actual_run(history, policy=policy, filings=filings)
    results = tuple(evaluate(history, phi, policy=policy, baseline=base,
                             filings=filings)
                    for phi in comparators)
    return RegretReport(history.history_id, history.horizon, len(base.outcomes),
                        base.total_charge, results)


# ---------------------------------------------------------------------------
# Locality
# ---------------------------------------------------------------------------


def account_liability_cap(history: ActualHistory, account: str,
                          run: ReplayRun) -> Q:
    """The most an account can be charged over the run: the sum of the maximum
    per-occasion charge of every occasion that lands in it."""
    total = Q(0)
    for outcome in run.outcomes:
        if outcome.account != account:
            continue
        occasion = next(o for o in _all_occasions(history)
                        if o.occasion_id == outcome.occasion_id)
        total += occasion.schedule.max_charge
    return total


def _all_occasions(history: ActualHistory) -> tuple[Occasion, ...]:
    live = list(history.base_occasions)
    for filing in history.filings:
        live.extend(filing.occasions)
    return tuple(live)


@dataclass(frozen=True)
class LocalityCheck:
    """The fenced-locality bound, evaluated on one actual run and one comparator.

    `bound` is the sum of the admitted lifetime liability of the accounts the
    comparator touched. `untouched_identical` records the other half of the
    argument: outside those accounts the two runs agree occasion by occasion,
    which is what makes the bound a statement about locality rather than a
    restatement of the horizon.
    """

    phi_id: str
    touched: tuple[str, ...]
    divergence: Q
    bound: Q
    untouched_identical: bool

    @property
    def holds(self) -> bool:
        return self.untouched_identical and abs(self.divergence) <= self.bound


def locality(history: ActualHistory, result: ComparatorResult, *,
             baseline: ReplayRun | None = None,
             policy: PolicySuite = DEFAULT_POLICY) -> LocalityCheck:
    base = baseline or actual_run(history, policy=policy)
    touched = result.run.touched_accounts
    bound = sum((account_liability_cap(history, account, result.run)
                 for account in touched), Q(0))
    by_id = {o.occasion_id: o for o in base.outcomes}
    identical = True
    for outcome in result.run.outcomes:
        if outcome.account in touched:
            continue
        other = by_id.get(outcome.occasion_id)
        if other is None or other.charge != outcome.charge or \
                other.response != outcome.response:
            identical = False
            break
    return LocalityCheck(result.phi_id, touched,
                         result.replay_charge - result.actual_charge, bound,
                         identical)


# ---------------------------------------------------------------------------
# Remediable patterns
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RemediablePattern:
    """A represented failure with a fixed lawful repair.

    The five parts are the ones the intended consequence theorem quantifies over:
    which occasions the pattern is recognised on, which comparator repairs it,
    how often it fired, the charge it saved per firing, and whether that saving
    is uniform. `uniform_saving` is what a positive-rate statement needs; a
    pattern whose saving varies is still a pattern, and the report says so rather
    than dropping it.
    """

    pattern_id: str
    phi_id: str
    occurrences: int
    firings: int
    savings: tuple[Q, ...]

    @property
    def total_saving(self) -> Q:
        return sum(self.savings, Q(0))

    @property
    def uniform_saving(self) -> Q | None:
        distinct = set(self.savings)
        return next(iter(distinct)) if len(distinct) == 1 else None

    @property
    def rate(self) -> Q:
        return Q(self.firings, self.occurrences) if self.occurrences else Q(0)


def pattern_of(history: ActualHistory, result: ComparatorResult,
               recognised: Sequence[str], pattern_id: str, *,
               baseline: ReplayRun | None = None,
               policy: PolicySuite = DEFAULT_POLICY) -> RemediablePattern:
    base = baseline or actual_run(history, policy=policy)
    actual_by_id = {o.occasion_id: o.charge for o in base.outcomes}
    savings = tuple(actual_by_id[identifier] - result.run.charge_at(identifier)
                    for identifier in result.firings)
    return RemediablePattern(pattern_id, result.phi_id, len(recognised),
                             len(result.firings), savings)
