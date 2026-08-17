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

**The cost is a product of three factors, and no one of them is privileged.**

    q_t  =  (eps_t + C_t) * D_t / delta_t ,     sum_t q_t < infinity

is the whole condition. Ordinary aggregate pressure, normative exclusion depth,
and tolerated error each appear once, and indefinite force stays affordable if
*any* combination of them makes the product summable — the depth decaying is one
route among three, not a requirement. An earlier version of this module asserted
that persistent positive depth alone made indefinite force unaffordable. That is
false: `D_t = 1/2` and `delta_t = 1` forever against `eps_t + C_t = 2^-t` sums to
under `1`. `NoDepthOnlyImpossibility` pins it, and `positive_floor_dates` carries
the corrected limitative statement, which needs floors on **two** factors and a
ceiling on the third.

Solving for the tolerance still gives the affordability relation
`delta_t >= (eps_t + C_t) * D_t / b_t`; what changed is that it is one of three
readings of the same equation rather than the canonical one.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence

from contract import declared_liability_bound
from deduction import world_deficit
from enforcement import Region
from market import ONE, ZERO


class Insufficient(Exception):
    """Raised when a force request cannot be funded out of remaining capital."""


class LiveDeficitCertificate:
    """`D_t`, and what establishes that it covers every live world.

    The account is only as sound as this number. A charge computed from deficits
    a caller happened to pass in certifies nothing: the preservation theorem
    quantifies over **all** worlds live at the date, so the aggregate must
    dominate

        D_t  =  sup over live omega of  sum_j d_{t,j}(omega) ,

    and a certificate records how that supremum was established rather than
    asserting the number bare.

    Two aggregates are available and they are not equal. The **sharp** one is the
    supremum of the row sum; the **rowwise** one sums each row's own worst world.
    The second is larger whenever different rows are worst at different worlds —
    `p >= 1/2` and `p <= 1/2` over the two worlds of one sentence give `1/2`
    against `1`, a clean factor of two — and using it where the sharp one is
    available overcharges the account and buys nothing.
    """

    def __init__(self, date: int, aggregate: Fraction, basis: str,
                 rowwise: Fraction | None = None, verified: bool = True) -> None:
        self.date = date
        self.aggregate = Fraction(aggregate)
        self.rowwise = self.aggregate if rowwise is None else Fraction(rowwise)
        self.basis = basis
        self.verified = verified
        if self.aggregate < 0:
            raise ValueError("an aggregate deficit is nonnegative")

    @classmethod
    def by_enumeration(cls, date: int, region: Region,
                       live_worlds: Sequence[Sequence[Fraction]]
                       ) -> "LiveDeficitCertificate":
        """Compute both aggregates exactly, by walking the live worlds.

        Available whenever the live process is finitely presented at the date,
        which is what `(L2)` effective finite restriction buys. This is the only
        constructor that produces a `verified` certificate.
        """
        rows = list(region.rows)
        worlds = [tuple(Fraction(x) for x in w) for w in live_worlds]
        if not worlds:
            return cls(date, ZERO, "no live worlds", ZERO, True)
        deficits = [world_deficit(region, w) for w in worlds]
        sharp = max(sum(d, ZERO) for d in deficits)
        rowwise = sum((max(d[j] for d in deficits) for j in range(len(rows))),
                      ZERO)
        return cls(date, sharp, f"enumeration over {len(worlds)} live worlds",
                   rowwise, True)

    @classmethod
    def asserted(cls, date: int, bound: Fraction, reason: str
                 ) -> "LiveDeficitCertificate":
        """An upper bound the caller takes responsibility for.

        Legitimate — a caller may have a proof the account cannot reproduce — and
        marked `verified = False` so that nothing downstream can mistake an
        obligation for a discharge. `reason` is required, because an unexplained
        number is exactly what this type exists to prevent.
        """
        if not reason:
            raise ValueError("an asserted bound states what establishes it")
        return cls(date, bound, f"asserted: {reason}", None, False)


def charge(slack: Fraction, volume: Fraction, tolerance: Fraction,
           certificate: LiveDeficitCertificate, sharp: bool = True) -> Fraction:
    """What one date's force costs the account.

    The declared-quantity liability ceiling, renamed. Naming it a *charge* is the
    whole move: the same number the safety analysis could previously only report
    after the fact becomes a price paid in advance.

    `sharp` selects which aggregate is billed. The sharp one is correct and the
    rowwise one is conservative; both are sound, and the option exists so a
    per-row account can bill the second while a global account bills the first.
    """
    total = certificate.aggregate if sharp else certificate.rowwise
    return declared_liability_bound(slack, volume, tolerance, (total,))


def raw_charge(slack: Fraction, volume: Fraction, tolerance: Fraction,
               deficits: Sequence[Fraction]) -> Fraction:
    """The same arithmetic on numbers nobody has certified.

    **This is not a safety quantity.** It is the low-level ceiling formula, for
    callers computing what force *would* cost before they have a live-world
    certificate. Paying an account with it proves nothing about any world.
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

    def __init__(self, capital: Fraction,
                 lifetime_ceiling: Fraction | None = None) -> None:
        capital = Fraction(capital)
        if capital < 0:
            raise ValueError("capital is nonnegative")
        self.capital = capital
        self.lifetime_ceiling = (capital if lifetime_ceiling is None
                                 else Fraction(lifetime_ceiling))
        if self.lifetime_ceiling < capital:
            raise ValueError("the lifetime ceiling is at least the initial capital")
        self.spent = ZERO
        self.ledger: list[tuple[str, Fraction]] = []
        self.allocations: dict[str, Fraction] = {}
        self.charged: dict[str, Fraction] = {}

    @property
    def remaining(self) -> Fraction:
        return self.capital - self.spent

    # --- replenishment ------------------------------------------------------

    def replenish(self, amount: Fraction) -> None:
        """Top the account up, against a ceiling declared at construction.

        There is deliberately no unrestricted `add_capital`. A finite account
        proves nothing if an outside source may refill it without limit, and
        unbounded refilling is exactly the failure `NL-SI-P1` names — an outside
        source replenishing every paid loss while only current positions are
        tracked. The preservation theorem then uses `lifetime_ceiling`, not the
        initial capital, so the bound a caller may quote is the ceiling.

        Default behaviour is **no replenishment**: `lifetime_ceiling` defaults to
        the initial capital, so the first call raises. A caller wanting a new
        allowance under a new constitutional era constructs a new account and
        accounts for the transition, rather than pretending the old lifetime
        bound survived.
        """
        amount = Fraction(amount)
        if amount < 0:
            raise ValueError("a replenishment is nonnegative")
        if self.capital + amount > self.lifetime_ceiling:
            raise Insufficient(
                f"replenishing by {amount} would raise total capital to "
                f"{self.capital + amount} above the declared lifetime ceiling "
                f"{self.lifetime_ceiling}")
        self.capital += amount

    # --- modular allocation -------------------------------------------------

    def allocate(self, endorsement: str, budget: Fraction) -> None:
        """Reserve `budget` for one endorsement, refusing if capital is short.

        Two things at once, and they are worth separating. As **admission
        control** it stops the fresh-endorsement counterexample: each admission
        consumes global capital, so admissions are finitely many at any positive
        budget and `sum_e B_e <= B` holds because it is checked. As a
        **subaccount** it caps what that endorsement may spend — enforced in
        `spend`, which refuses a labelled charge that would take an endorsement
        past its own reservation.

        An endorsement with no allocation is not forbidden; it simply spends
        against global capital only.
        """
        budget = Fraction(budget)
        if budget < 0:
            raise ValueError("a budget is nonnegative")
        reserved = sum(self.allocations.values(), ZERO)
        if reserved + budget > self.lifetime_ceiling:
            raise Insufficient(
                f"allocating {budget} to {endorsement} would reserve "
                f"{reserved + budget} against capital {self.lifetime_ceiling}")
        self.allocations[endorsement] = (
            self.allocations.get(endorsement, ZERO) + budget)

    def reserved(self) -> Fraction:
        return sum(self.allocations.values(), ZERO)

    def remaining_for(self, endorsement: str) -> Fraction:
        """What an endorsement may still spend: its own reservation, and global."""
        spent = self.charged.get(endorsement, ZERO)
        if endorsement in self.allocations:
            return min(self.allocations[endorsement] - spent, self.remaining)
        return self.remaining

    # --- spending -----------------------------------------------------------

    def afford(self, slack: Fraction, volume: Fraction,
               certificate: "LiveDeficitCertificate",
               allowance: Fraction | None = None,
               sharp: bool = True) -> Fraction | None:
        """The tolerance this date can be granted, against remaining capital."""
        total = certificate.aggregate if sharp else certificate.rowwise
        return affordable_tolerance(
            slack, volume, (total,),
            self.remaining if allowance is None else allowance)

    def spend(self, slack: Fraction, volume: Fraction, tolerance: Fraction,
              certificate: "LiveDeficitCertificate", label: str = "",
              sharp: bool = True) -> Fraction:
        """Charge a date's force to the account, or refuse it.

        Refusal is the guarantee. An account that overdrafts certifies nothing,
        so this raises rather than emitting force it cannot fund, and the caller
        must choose an exhaustion behaviour. When `label` names an endorsement
        holding a reservation, the charge is checked against that reservation as
        well as against global capital.
        """
        cost = charge(slack, volume, tolerance, certificate, sharp)
        if cost > self.remaining:
            raise Insufficient(
                f"force costing {cost} against remaining {self.remaining}")
        if label in self.allocations:
            already = self.charged.get(label, ZERO)
            if already + cost > self.allocations[label]:
                raise Insufficient(
                    f"{label} would spend {already + cost} against its "
                    f"reservation {self.allocations[label]}")
        self.spent += cost
        self.charged[label] = self.charged.get(label, ZERO) + cost
        self.ledger.append((label, cost))
        return cost


# --- exhaustion behaviours ---------------------------------------------------

def quarantine(account: OutflowAccount, slack: Fraction, volume: Fraction,
               tolerance: Fraction, certificate: LiveDeficitCertificate,
               label: str = "") -> Fraction | None:
    """Emit the requested force, or none at all.

    The endorsement keeps its normative standing and loses operative force. It
    is the behaviour that changes the fewest other clauses, because withholding
    force is already something the architecture has a name for.
    """
    try:
        account.spend(slack, volume, tolerance, certificate, label)
        return tolerance
    except Insufficient:
        return None


def relax(account: OutflowAccount, slack: Fraction, volume: Fraction,
          certificate: LiveDeficitCertificate, label: str = "",
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
    needed = account.afford(slack, volume, certificate, allowance)
    if needed is None:                       # nothing excluded: force is free
        account.ledger.append((label, ZERO))
        return ceiling
    if needed > ceiling:
        return None
    account.spend(slack, volume, needed, certificate, label)
    return needed


def proportional(account: OutflowAccount, slack: Fraction, volume: Fraction,
                 certificate: LiveDeficitCertificate, share: Fraction = ONE / 2,
                 label: str = "", ceiling: Fraction = ONE) -> Fraction | None:
    """Spend at most a fixed share of what remains, and never exhaust.

    The policy worth preferring, because it needs no schedule declared in
    advance. Spending share `rho` of the remaining capital each date leaves
    `R_t = R_0 (1 - rho)^t`, so the spend sequence is summable *by construction*
    and totals at most `R_0` — the schedule is derived from the account rather
    than guessed ahead of it, and no date is ever refused for exhaustion.

    What it costs is force: the affordable tolerance loosens geometrically. When
    depth and pressure both stay pinned that means a promise saying progressively
    less, and `positive_floor_dates` says no policy does better under those two
    floors. When either factor decays, the same policy funds nonvacuous force
    indefinitely — the policy is not what decides which case obtains.
    """
    share = Fraction(share)
    if not (ZERO < share <= ONE):
        raise ValueError("a share lies in (0, 1]")
    return relax(account, slack, volume, certificate, label, ceiling,
                 allowance=account.remaining * share)


# --- the safety theorem, as a checkable certificate --------------------------

def meaningful_dates_are_finite(*args, **kwargs):
    """**Withdrawn — this theorem was false.** Use `positive_floor_dates`.

    It computed the least cost of a nonvacuous date as `deficit_floor / ceiling`,
    dropping the `(eps_t + C_t)` factor entirely, and concluded that a deficit
    bounded away from zero made indefinite force unaffordable. The dropped factor
    is not bounded below: with `eps_t + C_t = 2^-t` a fixed deficit of `1/2` at
    tolerance `1` costs `2^-(t+1)` and sums to under `1`, so force is affordable
    forever while the normative distance never closes at all.

    Kept as a raising stub rather than deleted, because the claim reached the
    round's README, the interface note and the theorem map, and a silent deletion
    would leave no marker where a reader might remember it.
    """
    raise NotImplementedError(
        "withdrawn: persistent positive depth does not by itself make indefinite "
        "force unaffordable; see positive_floor_dates")


def maximum_violation(region: Region) -> Fraction:
    """The largest violation a row of `region` can take anywhere in the cube.

    The scale against which a tolerance means something. For `<c, P> >= r` over
    `[0,1]^n` the price minimizing the left side puts `1` on every negative
    coefficient and `0` on every positive one, so the worst violation is
    `r - sum_i min(c_i, 0)`.

    This exists because `delta <= 1` is **not** a presentation-independent notion
    of meaningful force. Scaling a row by `lambda` scales its violations by
    `lambda`, so the same `delta` promises `lambda` times more or less depending
    on how the row was written. A promise says something only relative to what
    the row could have done.
    """
    worst = ZERO
    for row in region.rows:
        floor = sum((c for c in row.c if c < 0), ZERO)
        worst = max(worst, Fraction(row.r) - floor)
    return worst


def is_nonvacuous(region: Region, tolerance: Fraction,
                  share: Fraction = ONE / 2) -> bool:
    """Whether a promised tolerance constrains the price at all, to scale.

    `delta <= share * V_max`. A tolerance at or above the maximum attainable
    violation promises nothing — every price already satisfies it — and one just
    under it promises almost nothing. `share` is where a caller draws the line,
    and it is a declared judgement rather than a theorem.
    """
    ceiling = maximum_violation(region)
    if ceiling == 0:
        return True                      # nothing to violate: force is free
    return Fraction(tolerance) <= Fraction(share) * ceiling


def positive_floor_dates(capital: Fraction, deficit_floor: Fraction,
                         pressure_floor: Fraction,
                         tolerance_ceiling: Fraction) -> int:
    """How many dates a finite account funds when **all three** factors are pinned.

    The corrected limitative theorem. A date costs
    `(eps_t + C_t) * D_t / delta_t`, so bounding it below needs a floor on the
    ordinary aggregate pressure *and* a floor on the exclusion depth *and* a
    ceiling on the tolerance:

        D_t >= d > 0,   eps_t + C_t >= c > 0,   delta_t <= delta_bar

    give `q_t >= c*d/delta_bar > 0`, and finitely many such charges fit in finite
    capital. All three hypotheses are load-bearing: drop the pressure floor and
    the counterexample above applies; drop the tolerance ceiling and force can be
    kept affordable by promising less and less.

    What this does **not** say is that any of the three must decay. It says that
    if none of them moves, the account runs out.
    """
    d, c = Fraction(deficit_floor), Fraction(pressure_floor)
    bar = Fraction(tolerance_ceiling)
    if d <= 0 or c <= 0:
        raise ValueError("the corollary needs positive floors on depth and pressure")
    if bar <= 0:
        raise ValueError("a tolerance ceiling is positive")
    return int(Fraction(capital) * bar / (c * d))


def cumulative_certificate(dates: Iterable[dict]) -> Fraction:  # noqa: D401
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
