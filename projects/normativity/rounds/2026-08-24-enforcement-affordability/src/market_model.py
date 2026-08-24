"""Exact finite market model for the enforcement-affordability prosecution.

Unregistered exploration code. One model, every fixture: finite sentence
support, [0,1]-rational prices, the MarketMaker guarantee as a fixed-point
postulate (verified exactly on every run), budgeted component traders with the
per-component scaling semantics of the pinned Budgeter (shutoff test plus
lossCap scaling over the day's live payout tables), and the projection
enforcer of skeleton Definitions 2.2/3.6. Exact rational arithmetic
throughout; no floats anywhere.

Semantics sources (verified in the round's G1 gate):
- lossCap(available, current) = (max 1 (-current/available))^-1, i.e. 1 when
  the day trade cannot lose more than the available capital at that table,
  else available/(-current)  [source Budgeter.lean:783; lift
  AssessmentProcess.lean:370].
- Scale = min over the day's live tables of the per-table lossCap with
  available = budget + realized prior worth at that table
  [Budgeter.lean:727,735; AssessmentProcess.lean:358,392].
- Shutoff: some earlier day's realized worth is <= -budget at some table live
  on that earlier day [Budgeter.lean:600; AssessmentProcess.lean:399].
- Per-component: each budgeted trader scales its own trade from its own
  realized history; the firm only sums components
  [AssessmentFirm.lean:78,127].
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from typing import Callable, Dict, List, Optional, Sequence, Tuple

ZERO = Q(0)
ONE = Q(1)

Price = Dict[str, Q]
Shares = Dict[str, Q]
Pattern = Tuple[Q, ...]  # aligned with the model's support tuple


def value_of(shares: Shares, prices: Price, support: Sequence[str], table: Pattern) -> Q:
    """Day-trade value at a payout table: sum of shares * (payout - price)."""
    total = ZERO
    for i, phi in enumerate(support):
        c = shares.get(phi, ZERO)
        if c != 0:
            total += c * (table[i] - prices[phi])
    return total


# ---------------------------------------------------------------------------
# Constraint regions with exact Euclidean projection.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Box:
    """Product of rational intervals; projection is coordinatewise clamping."""

    bounds: Tuple[Tuple[Q, Q], ...]  # (lo, hi) per support coordinate

    def project(self, p: Sequence[Q]) -> Tuple[Q, ...]:
        out = []
        for x, (lo, hi) in zip(p, self.bounds):
            out.append(lo if x < lo else hi if x > hi else x)
        return tuple(out)

    def dist2(self, p: Sequence[Q]) -> Q:
        q = self.project(p)
        return sum((x - y) ** 2 for x, y in zip(p, q))


@dataclass(frozen=True)
class Segment:
    """Rational segment [a, b]; exact projection via the clamped parameter."""

    a: Tuple[Q, ...]
    b: Tuple[Q, ...]

    def project(self, p: Sequence[Q]) -> Tuple[Q, ...]:
        d = tuple(y - x for x, y in zip(self.a, self.b))
        dd = sum(x * x for x in d)
        if dd == 0:
            return self.a
        t = sum((x - y) * z for x, y, z in zip(p, self.a, d)) / dd
        t = ZERO if t < 0 else ONE if t > 1 else t
        return tuple(x + t * z for x, z in zip(self.a, d))

    def dist2(self, p: Sequence[Q]) -> Q:
        q = self.project(p)
        return sum((x - y) ** 2 for x, y in zip(p, q))


# ---------------------------------------------------------------------------
# Traders.
# ---------------------------------------------------------------------------


def loss_cap(available: Q, current: Q) -> Q:
    """The pinned Budgeter's per-table scalar: min(1, available/(-current))
    for a losing trade, 1 otherwise. Requires available > 0 at call sites the
    way the source does (non-shutoff days)."""
    if current >= 0:
        return ONE
    ratio = available / (-current)
    return ratio if ratio < 1 else ONE


class Ledger:
    """Realized trade history: (day, shares, execution prices)."""

    def __init__(self, support: Sequence[str]) -> None:
        self.support = tuple(support)
        self.trades: List[Tuple[int, Shares, Price]] = []

    def execute(self, day: int, shares: Shares, prices: Price) -> None:
        self.trades.append((day, dict(shares), dict(prices)))

    def worth(self, table: Pattern, through_day: Optional[int] = None) -> Q:
        total = ZERO
        for day, shares, prices in self.trades:
            if through_day is not None and day > through_day:
                continue
            total += value_of(shares, prices, self.support, table)
        return total

    def day_shares(self, day: int) -> Shares:
        for d, shares, _ in self.trades:
            if d == day:
                return shares
        return {}


class BudgetedTrader:
    """A firm component: raw day strategy, positive budget, and the pinned
    Budgeter discipline against the model's live-table schedule."""

    def __init__(
        self,
        name: str,
        support: Sequence[str],
        base: Callable[[int, Price], Shares],
        budget: Q,
        live: Callable[[int], Sequence[Pattern]],
    ) -> None:
        if budget <= 0:
            raise ValueError("budgets are positive")
        self.name = name
        self.base = base
        self.budget = budget
        self.live = live
        self.ledger = Ledger(support)
        self.support = tuple(support)
        self._cache_key: Optional[Tuple[int, int]] = None
        self._cache_shutoff = False
        self._cache_prior: Dict[Pattern, Q] = {}

    def _day_data(self, day: int) -> Tuple[bool, Dict[Pattern, Q]]:
        """Shutoff flag and per-table prior worth. Both read only the
        executed ledger, never candidate prices, so they are cached per
        (day, ledger length)."""
        key = (day, len(self.ledger.trades))
        if self._cache_key != key:
            shutoff = False
            for m in range(day):
                for table in self.live(m):
                    if self.ledger.worth(table, through_day=m) <= -self.budget:
                        shutoff = True
                        break
                if shutoff:
                    break
            prior = {t: self.ledger.worth(t) for t in self.live(day)}
            self._cache_key = key
            self._cache_shutoff = shutoff
            self._cache_prior = prior
        return self._cache_shutoff, self._cache_prior

    def shut_off(self, day: int) -> bool:
        return self._day_data(day)[0]

    def scale(self, day: int, prices: Price) -> Q:
        _, prior = self._day_data(day)
        raw = self.base(day, prices)
        s = ONE
        for table in self.live(day):
            available = self.budget + prior[table]
            current = value_of(raw, prices, self.support, table)
            cap = loss_cap(available, current)
            if cap < s:
                s = cap
        return s

    def day_trade(self, day: int, prices: Price) -> Shares:
        if self.shut_off(day):
            return {}
        raw = self.base(day, prices)
        s = self.scale(day, prices)
        return {phi: s * c for phi, c in raw.items() if s * c != 0}

    def available(self, day: int, table: Pattern) -> Q:
        """Capital available against a table at the start of the day."""
        _, prior = self._day_data(day)
        return self.budget + prior.get(table, self.ledger.worth(table))


class Enforcer:
    """The projection enforcement trader of Definitions 2.2/3.6: share vector
    lambda * (proj_K(p) - p) on the day's fragment."""

    def __init__(
        self,
        support: Sequence[str],
        schedule: Callable[[int], Tuple[object, Q]],  # day -> (region, lambda)
    ) -> None:
        self.schedule = schedule
        self.ledger = Ledger(support)
        self.support = tuple(support)

    def day_trade(self, day: int, prices: Price) -> Shares:
        region, lam = self.schedule(day)
        p = tuple(prices[phi] for phi in self.support)
        q = region.project(p)
        return {
            phi: lam * (qi - pi)
            for phi, qi, pi in zip(self.support, q, p)
            if lam * (qi - pi) != 0
        }


class UnbudgetedTrader:
    """A raw strategy with no budgeter, for deliberately broken controls."""

    def __init__(self, name: str, support: Sequence[str],
                 base: Callable[[int, Price], Shares]) -> None:
        self.name = name
        self.base = base
        self.ledger = Ledger(support)
        self.support = tuple(support)

    def day_trade(self, day: int, prices: Price) -> Shares:
        return self.base(day, prices)


# ---------------------------------------------------------------------------
# The MarketMaker: per-coordinate verified search plus the full-cube check.
#
# The model requires every trader's day trade at a coordinate to depend on the
# candidate prices only through that coordinate (the fixtures satisfy this by
# construction: box regions project coordinatewise, budgeted components trade
# one coordinate or a constant vector, and scaling reads the candidate trade's
# value at fixed tables). The postulate itself is then verified exactly over
# every vertex of the support cube; a failed verification raises.
# ---------------------------------------------------------------------------


class MarketMakerError(Exception):
    pass


def _combined_coord(traders, day: int, phi: str, x: Q, prices_base: Price) -> Q:
    prices = dict(prices_base)
    prices[phi] = x
    total = ZERO
    for t in traders:
        total += t.day_trade(day, prices).get(phi, ZERO)
    return total


def solve_day(
    traders,
    day: int,
    support: Sequence[str],
    eps: Q,
    max_iter: int = 400,
) -> Price:
    """Find a price state satisfying the MarketMaker guarantee for the
    combined day strategy, then verify the guarantee exactly on every cube
    vertex of the support."""
    share = eps / len(support)
    prices: Price = {phi: Q(1, 2) for phi in support}

    def ok_coord(a: Q, x: Q) -> bool:
        up = a * (ONE - x)
        down = -a * x
        return up <= share and down <= share

    def settle(phi: str) -> Q:
        f = lambda x: _combined_coord(traders, day, phi, x, prices)
        lo, hi = ZERO, ONE
        flo, fhi = f(lo), f(hi)
        if ok_coord(flo, lo):
            return lo
        if ok_coord(fhi, hi):
            return hi
        # After the boundary checks, excess buying pressure at 0 and excess
        # selling pressure at 1 remain: flo > 0 > fhi, so a verified interior
        # point exists on any continuous path.
        for _ in range(max_iter):
            mid = (lo + hi) / 2
            fm = f(mid)
            if ok_coord(fm, mid):
                return mid
            if fm > 0:
                lo = mid
            else:
                hi = mid
        raise MarketMakerError(f"day {day}, {phi}: bisection did not verify")

    # Gauss-Seidel sweeps for cross-coordinate throttles; the exact full-cube
    # verification below is the soundness gate, not the sweep count.
    for _ in range(6):
        previous = dict(prices)
        for phi in support:
            prices[phi] = settle(phi)
        if prices == previous:
            break

    # The postulate, checked exactly: combined day value <= eps at every
    # vertex of the support cube.
    combined: Shares = {}
    for t in traders:
        for k, v in t.day_trade(day, prices).items():
            combined[k] = combined.get(k, ZERO) + v
    for vertex in product((ZERO, ONE), repeat=len(support)):
        val = value_of(combined, prices, support, vertex)
        if val > eps:
            raise MarketMakerError(
                f"day {day}: guarantee violated at {vertex}: {val} > {eps}"
            )
    return prices


def run_market(
    traders,
    days: int,
    support: Sequence[str],
    eps_fn: Callable[[int], Q] = lambda n: Q(1, 2 ** n),
) -> List[Price]:
    """Run the traderized recursion day by day, executing every trader's
    realized trade at the returned price state."""
    history: List[Price] = []
    for day in range(1, days + 1):
        prices = solve_day(traders, day, support, eps_fn(day))
        # Every day strategy is a function of the same pre-day state and the
        # returned price state: compute all realized trades before executing
        # any, so no trader's execution changes what another (or its own
        # schedule) reads for the same day.
        realized = [(t, t.day_trade(day, prices)) for t in traders]
        for t, shares in realized:
            t.ledger.execute(day, shares, prices)
        history.append(prices)
    return history


# ---------------------------------------------------------------------------
# Measurements.
# ---------------------------------------------------------------------------


def lifetime_liability(ledger: Ledger, tables: Sequence[Pattern]) -> Q:
    """max(0, -min over the given payout tables of cumulative worth): the B
    of skeleton Definition 4.1 realized at this horizon against this table
    set."""
    worst = min(ledger.worth(t) for t in tables)
    return -worst if worst < 0 else ZERO


def all_patterns(width: int) -> List[Pattern]:
    return [tuple(Q(b) for b in bits) for bits in product((0, 1), repeat=width)]


def intensity(A_n: Q, day: int, delta: Q) -> Q:
    """Skeleton Definition 3.3: rho_n = A_n + 2^-n, lambda_n = rho_n/delta^2."""
    rho = A_n + Q(1, 2 ** day)
    return rho / (delta * delta)


def geometric_slack(days: int) -> Q:
    return sum(Q(1, 2 ** n) for n in range(1, days + 1))
