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


def _exact(x: Fraction) -> tuple[int, int]:
    """A rational as an immutable, hashable, exact pair. No floats anywhere."""
    f = Fraction(x)
    return (f.numerator, f.denominator)


def presentation_key(region: Region) -> tuple:
    """The exact identity of a **row presentation**, not of an admissible set.

    The round chose Option A — the presentation is part of the force request —
    so this is what a safety certificate must bind to. Duplicates are preserved
    because duplicates change the emitted position; row order is preserved
    because the compiler walks the rows in order and nothing has been proved
    about reordering.

    Transparent rather than hashed: a reader can see what was bound, and a
    mismatch reports which field differs. A digest would buy nothing here — the
    threat is a caller wiring the wrong object, not an adversary forging bytes.
    """
    return (region.dimension,
            tuple((tuple(_exact(c) for c in row.c), _exact(row.r))
                  for row in region.rows))


def support_key(support: Sequence[str]) -> tuple:
    """Which sentence occupies which coordinate.

    A valuation `(0,1,0)` means nothing without this. Two fragments over the
    same names in a different order give different keys, because they give
    different worlds.
    """
    return tuple(str(s) for s in support)


def live_world_key(date: int, support: Sequence[str],
                   worlds: Sequence[Sequence[Fraction]]) -> tuple:
    """The exact assessment state a certificate was computed against.

    Date alone is not enough: two assessment processes can disagree at the same
    date, and the live set shrinks over time, so a later certificate is cheaper
    and must not fund earlier force. Sorting makes the key independent of the
    order the caller happened to enumerate in, which is not operative.
    """
    return (int(date), support_key(support),
            tuple(sorted(tuple(_exact(x) for x in w) for w in worlds)))


_VERIFIED = object()          # module-private witness; not exported


class LiveDeficitClaim:
    """An aggregate deficit a caller takes responsibility for.

    Legitimate — a caller may have a proof the account cannot reproduce — and a
    **different type** from a certificate, because the difference is exactly
    whether anything checked it. A claim can price a request and cannot produce
    a safety-certified position; `compile_funded_force` refuses it.

    A reason string is not a proof and this type does not pretend otherwise. It
    is a claim with an author.
    """

    verified = False

    def __init__(self, date: int, aggregate: Fraction, reason: str) -> None:
        if not reason:
            raise ValueError("a claim states who is making it and why")
        self.date = int(date)
        self.aggregate = Fraction(aggregate)
        self.rowwise = self.aggregate
        self.reason = reason
        if self.aggregate < 0:
            raise ValueError("an aggregate deficit is nonnegative")

    @property
    def basis(self) -> str:
        return f"claimed: {self.reason}"


class LiveDeficitCertificate:
    """`D_t` for **one exact force request**, and what establishes it.

    The proposition it certifies is

        for every omega live at date t,  sum_j d_{t,j}(omega)  <=  aggregate ,

    where `d_{t,j}` are the deficits of *these* rows, over *these* worlds, with
    *these* sentences in *these* coordinates, at *this* date. All four are
    carried, because a certificate that binds only a number can be paid against
    a different force request — and before this type existed, one could be: a
    certificate for `p >= 0` (aggregate zero) funded enforcement of `p >= 1/2`
    for nothing, while the emitted position really lost at a live world.

    Only `by_enumeration` constructs one. The initializer requires a
    module-private witness, so a caller cannot assert the verified state by
    filling in fields.
    """

    verified = True

    def __init__(self, witness, date, aggregate, rowwise, presentation,
                 support, live_worlds, basis) -> None:
        if witness is not _VERIFIED:
            raise TypeError(
                "a verified certificate is constructed by enumeration; use "
                "LiveDeficitCertificate.by_enumeration, or LiveDeficitClaim "
                "for a bound you are asserting")
        self.date = int(date)
        self.aggregate = Fraction(aggregate)
        self.rowwise = Fraction(rowwise)
        self.presentation = presentation
        self.support = support
        self.live_worlds = live_worlds
        self.basis = basis

    @classmethod
    def by_enumeration(cls, date: int, region: Region,
                       support: Sequence[str],
                       live_worlds: Sequence[Sequence[Fraction]]
                       ) -> "LiveDeficitCertificate":
        """Compute both aggregates exactly, by walking the live worlds.

        Available whenever the live process is finitely presented at the date,
        which is what `(L2)` effective finite restriction buys.

        The **sharp** aggregate is the supremum of the row sum; the **rowwise**
        one sums each row's own worst world and is larger whenever different
        rows are worst at different worlds — `p >= 1/2` and `p <= 1/2` over the
        two worlds of one sentence give `1/2` against `1`. The sharp one is
        billed; the rowwise one is kept because a per-row account must use it.
        """
        worlds = [tuple(Fraction(x) for x in w) for w in live_worlds]
        if any(len(w) != region.dimension for w in worlds):
            raise ValueError("a world carries one value per priced coordinate")
        if len(support) != region.dimension:
            raise ValueError("the support names one sentence per coordinate")
        if not worlds:
            sharp = rowwise = ZERO
            basis = "no live worlds"
        else:
            deficits = [world_deficit(region, w) for w in worlds]
            sharp = max(sum(d, ZERO) for d in deficits)
            rowwise = sum((max(d[j] for d in deficits)
                           for j in range(len(region.rows))), ZERO)
            basis = f"enumeration over {len(worlds)} live worlds"
        return cls(_VERIFIED, date, sharp, rowwise, presentation_key(region),
                   support_key(support), live_world_key(date, support, worlds),
                   basis)

    def binds(self, date: int, region: Region,
              support: Sequence[str]) -> str | None:
        """`None` when this certificate is about that exact request; else why not.

        Returns the mismatching field rather than a bare boolean, because the
        useful failure message names what was wired wrong.
        """
        if int(date) != self.date:
            return f"date {date} against certified date {self.date}"
        if support_key(support) != self.support:
            return f"support {support_key(support)} against {self.support}"
        if presentation_key(region) != self.presentation:
            return "row presentation"
        return None


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


class OutflowEntry:
    """One debit, with enough provenance to audit what consumed the account.

    A constitutional mechanism whose ledger says only `(label, cost)` cannot
    answer *which force request spent this*. These fields can.
    """

    __slots__ = ("label", "cost", "date", "presentation", "assessment",
                 "basis", "verified", "remaining")

    def __init__(self, label, cost, date, presentation, assessment, basis,
                 verified, remaining) -> None:
        self.label = label
        self.cost = cost
        self.date = date
        self.presentation = presentation
        self.assessment = assessment
        self.basis = basis
        self.verified = verified
        self.remaining = remaining

    def __repr__(self) -> str:
        mark = "verified" if self.verified else "claimed"
        return (f"OutflowEntry({self.label!r}, cost={self.cost}, "
                f"date={self.date}, {mark}, remaining={self.remaining})")


class OutflowAccount:
    """Finite lifetime capital, spent down as force is emitted.

    The account is **global over the whole enforcement channel**, not per source
    and not per endorsement. `cap` carves a summable decomposition out of it for
    sources that want modular budgets, and refuses one the capital cannot cover —
    which is the operative content of summability, imposed at admission rather
    than checked in the limit.

    Endorsement budgets are **caps, not reserves**. `sum_e B_e <= B` and
    `spent_e <= B_e` both hold, which is everything the safety theorem needs, but
    an unallocated charge may still spend capital an endorsement has been
    promised and not yet used. Ring-fencing would be a different and stricter
    discipline; the prose says cap because the behaviour is a cap.
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
        self.ledger: list[OutflowEntry] = []
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

    def cap(self, endorsement: str, budget: Fraction) -> None:
        """Cap one endorsement's lifetime spending, refusing if capital is short.

        Two things at once. As **admission control** it stops the
        fresh-endorsement counterexample: each admission consumes global capital,
        so admissions are finitely many at any positive budget and
        `sum_e B_e <= B` holds because it is checked. As a **spending cap** it
        bounds what that endorsement may ever spend, enforced in `spend`.

        It does **not** ring-fence: capital promised here and not yet spent
        remains available to unallocated charges. An endorsement with no cap
        spends against global capital only.
        """
        budget = Fraction(budget)
        if budget < 0:
            raise ValueError("a budget is nonnegative")
        promised = sum(self.allocations.values(), ZERO)
        if promised + budget > self.lifetime_ceiling:
            raise Insufficient(
                f"capping {endorsement} at {budget} would promise "
                f"{promised + budget} against capital {self.lifetime_ceiling}")
        self.allocations[endorsement] = (
            self.allocations.get(endorsement, ZERO) + budget)

    def capped(self) -> Fraction:
        """Total capital promised to named endorsements."""
        return sum(self.allocations.values(), ZERO)

    def remaining_for(self, endorsement: str) -> Fraction:
        """What an endorsement may still spend: its own cap, and global capital."""
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
                    f"{label} would spend {already + cost} against its cap "
                    f"{self.allocations[label]}")
        self.spent += cost
        self.charged[label] = self.charged.get(label, ZERO) + cost
        self.ledger.append(OutflowEntry(
            label, cost, certificate.date,
            getattr(certificate, "presentation", None),
            getattr(certificate, "live_worlds", None),
            certificate.basis, certificate.verified, self.remaining))
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
          certificate, requested: Fraction, label: str = "",
          ceiling: Fraction = ONE,
          allowance: Fraction | None = None) -> Fraction | None:
    """Emit the requested tolerance if affordable; otherwise loosen it.

    **Relaxing must not strengthen.** An earlier version computed the tightest
    tolerance the allowance could buy and emitted that, so a caller asking for
    `1/2` against an account that could afford `1/10` got `1/10` — force five
    times stronger than requested, and the whole allowance spent on it. The
    policy is *relax if necessary*, and it moves tolerance in one direction
    only.

    Returns the tolerance granted, or `None` when even `ceiling` is unaffordable
    — a date at which the only affordable promise is one that says nothing.
    """
    requested = Fraction(requested)
    room = account.remaining if allowance is None else Fraction(allowance)
    wanted = charge(slack, volume, requested, certificate)
    if wanted <= room:
        account.spend(slack, volume, requested, certificate, label)
        return requested
    needed = account.afford(slack, volume, certificate, room)
    if needed is None:                       # nothing excluded: force is free
        account.spend(slack, volume, requested, certificate, label)
        return requested
    if needed < requested:                   # cannot happen; guard the invariant
        raise AssertionError("relaxation would strengthen the request")
    if needed > ceiling:
        return None
    account.spend(slack, volume, needed, certificate, label)
    return needed


def proportional(account: OutflowAccount, slack: Fraction, volume: Fraction,
                 certificate, requested: Fraction, share: Fraction = ONE / 2,
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
    return relax(account, slack, volume, certificate, requested, label, ceiling,
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


def automatically_satisfied(region: Region) -> bool:
    """Whether no price in the cube can violate any row.

    Distinct from a tolerance being meaningful, and previously conflated with
    it: `is_nonvacuous` returned `True` here, which said an unviolatable region
    was meaningfully constraining. It is the opposite — enforcement is
    unnecessary, and a caller should skip it rather than promise anything.
    """
    return maximum_violation(region) == 0


def is_nonvacuous(region: Region, tolerance: Fraction,
                  share: Fraction = ONE / 2) -> bool:
    """Whether a promised tolerance constrains the price beyond what is automatic.

    `delta <= share * V_max`. A tolerance at or above the maximum attainable
    violation promises nothing — every price already satisfies it — and one just
    under it promises almost nothing. `share` is where a caller draws the line,
    and it is a declared judgement rather than a theorem.

    `False` when the region is automatically satisfied: there the promise is
    true and empty, which is exactly the case this predicate exists to catch.
    Ask `automatically_satisfied` for that condition by name.
    """
    ceiling = maximum_violation(region)
    if ceiling == 0:
        return False
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
