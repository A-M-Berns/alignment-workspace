"""A finite account out of which operative normative force is purchased.

The preservation theorem needs a hypothesis it cannot supply for itself:

    for every horizon n and every world assessed at n,
        sum_{t <= n} E_t(omega)  >=  -B .

Asserting that inequality is not a mechanism. This module asks whether a
protocol built only from quantities known **at or before the moment force is
emitted** can guarantee it, and answers yes, at a stated price.

Three findings shape the design.

**Per-endorsement caps do not aggregate.** Bounding each endorsement's lifetime
outflow separately leaves `sum_e B_e` unbounded, and a source can walk that gap
with fresh endorsements while obeying finite gating at every date. The account
must therefore be global, or decomposed into a *summable* allocation; a family
of individually finite budgets is neither.

**The charge is conservative and computable in advance.** The declared-quantity
ceiling `(eps_t + C_t) * ||d_t||_1 / delta_t` upper-bounds the date's worst-case
liability, uses no realized price, and is therefore available before the trade
is emitted. It is *not* the realized loss: it maximizes over live worlds
separately at each date, whereas the criterion's quantifier picks one world and
follows it. `charge_is_conservative` records that gap rather than hiding it.

**Tolerance is what the account buys.** Solving the charge inequality for the
tolerance gives the pass's central relation: with a per-date allowance `b_t`,

    delta_t  >=  (eps_t + C_t) * ||d_t||_1 / b_t .

Force is not free and not independently promisable. A source may have arbitrarily
tight conformance, or a finite lifetime account, and may have both only when
`(eps_t + C_t) * ||d_t||_1` decays summably against the tolerance it wants.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence

from contract import declared_liability_bound
from market import ONE, ZERO


class Insufficient(Exception):
    """Raised when a force request cannot be funded out of remaining capital."""


def charge(slack: Fraction, volume: Fraction, tolerance: Fraction,
           deficits: Sequence[Fraction]) -> Fraction:
    """What one date's force costs the account.

    Exactly the declared-quantity liability ceiling. Naming it a *charge* is the
    whole move: the same number that the safety analysis could only report after
    the fact becomes a price paid in advance.
    """
    return declared_liability_bound(slack, volume, tolerance, deficits)


def affordable_tolerance(slack: Fraction, volume: Fraction,
                         deficits: Sequence[Fraction],
                         allowance: Fraction) -> Fraction | None:
    """The tightest conformance an allowance buys: `(eps + C)*||d||_1 / b`.

    `None` when the date is free — no live world is excluded, so no tolerance is
    unaffordable and the caller may promise whatever it likes. The returned value
    can exceed `1`, and a caller that needs `delta <= 1` for the promise to say
    anything must then treat the date as unaffordable rather than round down.
    """
    allowance = Fraction(allowance)
    if allowance <= 0:
        raise ValueError("an allowance is positive")
    total = sum((Fraction(d) for d in deficits), ZERO)
    if total == 0:
        return None
    return (Fraction(slack) + Fraction(volume)) * total / allowance


class OutflowAccount:
    """Finite lifetime capital, spent down as force is emitted.

    The account is **global over the whole enforcement channel**, not per source
    and not per endorsement. `allocate` carves a summable decomposition out of it
    for sources that want modular budgets, and refuses an allocation the capital
    cannot cover — which is the operative content of summability, imposed at
    admission rather than checked in the limit.
    """

    def __init__(self, capital: Fraction) -> None:
        capital = Fraction(capital)
        if capital < 0:
            raise ValueError("capital is nonnegative")
        self.capital = capital
        self.spent = ZERO
        self.ledger: list[tuple[str, Fraction]] = []
        self.allocations: dict[str, Fraction] = {}

    @property
    def remaining(self) -> Fraction:
        return self.capital - self.spent

    # --- modular allocation -------------------------------------------------

    def allocate(self, endorsement: str, budget: Fraction) -> None:
        """Reserve `budget` for one endorsement, refusing if capital is short.

        This is where the fresh-endorsement counterexample is stopped. Each
        admission consumes global capital, so admissions are finitely many at any
        positive budget, and `sum_e B_e <= B` holds because it is checked rather
        than hoped for.
        """
        budget = Fraction(budget)
        if budget < 0:
            raise ValueError("a budget is nonnegative")
        reserved = sum(self.allocations.values(), ZERO)
        if reserved + budget > self.capital:
            raise Insufficient(
                f"allocating {budget} to {endorsement} would reserve "
                f"{reserved + budget} against capital {self.capital}")
        self.allocations[endorsement] = (
            self.allocations.get(endorsement, ZERO) + budget)

    # --- spending -----------------------------------------------------------

    def afford(self, slack: Fraction, volume: Fraction,
               deficits: Sequence[Fraction],
               allowance: Fraction | None = None) -> Fraction | None:
        """The tolerance this date can be granted, against remaining capital."""
        return affordable_tolerance(
            slack, volume, deficits,
            self.remaining if allowance is None else allowance)

    def spend(self, slack: Fraction, volume: Fraction, tolerance: Fraction,
              deficits: Sequence[Fraction], label: str = "") -> Fraction:
        """Charge a date's force to the account, or refuse it.

        Refusal is the guarantee. An account that overdrafts certifies nothing,
        so `spend` raises rather than emitting force it cannot fund, and the
        caller must choose an exhaustion behaviour.
        """
        cost = charge(slack, volume, tolerance, deficits)
        if cost > self.remaining:
            raise Insufficient(
                f"force costing {cost} against remaining {self.remaining}")
        self.spent += cost
        self.ledger.append((label, cost))
        return cost


# --- exhaustion behaviours ---------------------------------------------------

def quarantine(account: OutflowAccount, slack: Fraction, volume: Fraction,
               tolerance: Fraction, deficits: Sequence[Fraction],
               label: str = "") -> Fraction | None:
    """Emit the requested force, or none at all.

    The endorsement keeps its normative standing and loses operative force. It
    is the behaviour that changes the fewest other clauses, because withholding
    force is already something the architecture has a name for.
    """
    try:
        account.spend(slack, volume, tolerance, deficits, label)
        return tolerance
    except Insufficient:
        return None


def relax(account: OutflowAccount, slack: Fraction, volume: Fraction,
          deficits: Sequence[Fraction], label: str = "",
          ceiling: Fraction = ONE,
          allowance: Fraction | None = None) -> Fraction | None:
    """Loosen the tolerance until the force fits, or withhold it.

    Returns the tightest affordable tolerance, or `None` when even the ceiling
    is unaffordable — a date at which the only affordable promise is one that
    says nothing.

    `allowance` is this date's share. Omitting it lets the date draw on the
    entire remaining account, which is a legitimate policy and a bad one: the
    first excluded world empties the capital and every later date is quarantined.
    A schedule, or `proportional` below, is what keeps force available.
    """
    needed = account.afford(slack, volume, deficits, allowance)
    if needed is None:                       # nothing excluded: force is free
        account.ledger.append((label, ZERO))
        return ceiling
    if needed > ceiling:
        return None
    account.spend(slack, volume, needed, deficits, label)
    return needed


def proportional(account: OutflowAccount, slack: Fraction, volume: Fraction,
                 deficits: Sequence[Fraction], share: Fraction = ONE / 2,
                 label: str = "", ceiling: Fraction = ONE) -> Fraction | None:
    """Spend at most a fixed share of what remains, and never exhaust.

    The policy worth preferring, because it needs no schedule declared in
    advance. Spending share `rho` of the remaining capital each date leaves
    `R_t = R_0 (1 - rho)^t`, so the spend sequence is summable *by construction*
    and totals at most `R_0` — the schedule is derived from the account rather
    than guessed ahead of it, and no date is ever refused for exhaustion.

    What it costs is force: the affordable tolerance loosens geometrically, so
    a source facing a non-decaying deficit is not refused for lack of capital —
    it is answered with a promise that says progressively less, and past a point
    with one that says nothing at all. `meaningful_dates_are_finite` proves that
    no policy can do better, so this is not a defect of the policy.
    """
    share = Fraction(share)
    if not (ZERO < share <= ONE):
        raise ValueError("a share lies in (0, 1]")
    return relax(account, slack, volume, deficits, label, ceiling,
                 allowance=account.remaining * share)


# --- the safety theorem, as a checkable certificate --------------------------

def meaningful_dates_are_finite(capital: Fraction, deficit_floor: Fraction,
                                ceiling: Fraction = ONE) -> int:
    """How many dates a finite account can fund at a nonvacuous tolerance.

    The limitative theorem, and it holds against **every** protocol rather than
    against this module's policies. Meaningful conformance needs `delta_t <=
    ceiling`, so each such date costs at least

        (eps_t + C_t) * D_t / ceiling  >=  D_t / ceiling  >=  floor / ceiling ,

    a positive quantity bounded away from zero whenever the exclusion deficit
    does not vanish. Finitely many such charges fit in finite capital, so:

    **an endorsement whose deficit does not decay to zero receives meaningful
    operative force at only finitely many dates, under any finite account.**

    Persistent unresolved disagreement is therefore not something a safety
    account can subsidize indefinitely. What it can subsidize indefinitely is
    disagreement whose depth decays — the endorsement need never be *settled*,
    but the gap between what it demands and what the assessed worlds deliver
    must close. That is a substantially weaker demand than deductive resolution
    and it is the honest content of the safe fixture.
    """
    deficit_floor, ceiling = Fraction(deficit_floor), Fraction(ceiling)
    if deficit_floor <= 0:
        raise ValueError("the theorem needs a positive floor on the deficit")
    if ceiling <= 0:
        raise ValueError("a ceiling is positive")
    least = deficit_floor / ceiling
    return int(Fraction(capital) / least)


def cumulative_certificate(dates: Iterable[dict]) -> Fraction:
    """`sum_t charge_t`: the certificate the preservation theorem consumes.

    Sufficient for the criterion's quantifier and strictly stronger than it: it
    maximizes over the live worlds independently at every date, where the
    criterion follows a single world across dates. See `charge_is_conservative`.
    """
    return sum((charge(**d) for d in dates), ZERO)


def charge_is_conservative(dates: Sequence[dict],
                           trajectory: Sequence[Fraction]) -> bool:
    """Whether the per-date charge dominates one world's realized cumulative loss.

    `trajectory[t]` is the enforcement position's realized value at the followed
    world on date `t`. The certificate bounds the worst per-date loss, so it
    bounds any single world's cumulative loss; equality is not expected and the
    gap is the price of a certificate computable before the trade.
    """
    running = ZERO
    for t in range(len(trajectory)):
        running += Fraction(trajectory[t])
        if -running > sum((charge(**d) for d in dates[:t + 1]), ZERO):
            return False
    return True
