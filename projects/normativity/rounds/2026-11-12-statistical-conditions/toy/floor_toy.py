#!/usr/bin/env python3
"""EXPLORATION. A finite floor market in exact rationals. No theorem depends on this file.

One fresh sentence per day with realized truth x_n, a floor c on its price, settlement
the next day. Each trader has a firm weight, a wealth, and a position on the day's
sentence that is piecewise linear in the posted price p in [c, 1]. The day's price is the
least p in [c, 1] at which the weighted net position D(p) is not positive, found exactly:
p = c with multiplier mu = -D(c) when D(c) <= 0 (the floor binds), otherwise the least
root of D on (c, 1], or 1. The account is Q_N = sum mu_n (x_n - c). At an exact root the
firm's day value is -mu_n (x_n - c), so the firm's cumulative gain is -Q_N.

Run: python3 floor_toy.py            (prints the tables recorded in THEOREM.md, section 5)
     python3 floor_toy.py --check    (asserts the recorded exact values)
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr


# ---------------------------------------------------------------- truth sequences

def all_true(n: int) -> bool:
    return True


def periodic(n: int) -> bool:
    """False on days 0 mod 4: frequency 3/4."""
    return n % 4 != 0


def scrambled(n: int) -> bool:
    """False on about a quarter of the days, by a fixed integer hash; no listed trader
    other than a table reads the hash."""
    h = (n * 2654435761 + 40503) % 4294967296
    h ^= h >> 15
    h = (h * 2246822519) % 4294967296
    h ^= h >> 13
    return h % 4 != 0


# ---------------------------------------------------------------- traders

class Trader:
    """position(day, p) is linear between consecutive breakpoints(day)."""

    def __init__(self, name: str, weight: Fr, budget: Fr = Fr(1)):
        self.name, self.weight, self.budget, self.wealth = name, weight, budget, budget

    def breakpoints(self, day: int) -> list[Fr]:
        return []

    def position(self, day: int, p: Fr) -> Fr:
        raise NotImplementedError


class ConstantSeller(Trader):
    """Sells one share a day while it can cover the loss at the floor."""

    def __init__(self, name, weight, c, on=lambda day: True):
        super().__init__(name, weight)
        self.c, self.on = c, on

    def position(self, day, p):
        if not self.on(day):
            return Fr(0)
        return -min(Fr(1), self.wealth / (1 - self.c))


class TableSeller(Trader):
    """Stakes its whole wealth, at the floor's odds, on each day of a finite table."""

    def __init__(self, name, weight, c, table, off=Fr(0)):
        super().__init__(name, weight)
        self.c, self.table, self.off = c, frozenset(table), off

    def position(self, day, p):
        """Off its table it stakes the fraction `off` of its wealth."""
        frac = Fr(1) if day in self.table else self.off
        return -frac * self.wealth / (1 - self.c)


class Buyer(Trader):
    """Buys lam * wealth * (b - p)^+ / (b - c) shares: lam * wealth at the floor, none at
    its belief b."""

    def __init__(self, name, weight, c, b, lam):
        super().__init__(name, weight)
        self.c, self.b, self.lam = c, b, lam

    def breakpoints(self, day):
        return [self.b]

    def position(self, day, p):
        return self.lam * self.wealth * max(Fr(0), self.b - p) / (self.b - self.c)


class Follower(Trader):
    """Sells when the price is within delta of the floor: lam * wealth shares at
    p <= c + delta/2, none at p >= c + delta, linear between."""

    def __init__(self, name, weight, c, delta, lam):
        super().__init__(name, weight)
        self.c, self.delta, self.lam = c, delta, lam

    def breakpoints(self, day):
        return [self.c + self.delta / 2, self.c + self.delta]

    def position(self, day, p):
        t = (self.c + self.delta - p) / (self.delta / 2)
        return -self.lam * self.wealth * min(Fr(1), max(Fr(0), t))


# ---------------------------------------------------------------- the market

def clear(traders, day, c):
    """Least p in [c, 1] with net position <= 0, and the multiplier."""
    def net(p):
        return sum((t.weight * t.position(day, p) for t in traders), Fr(0))

    d = net(c)
    if d <= 0:
        return c, -d
    pts = sorted({c, Fr(1)} | {b for t in traders for b in t.breakpoints(day) if c < b < 1})
    for lo, hi in zip(pts, pts[1:]):
        dlo, dhi = net(lo), net(hi)
        if dhi <= 0:
            return lo + (hi - lo) * dlo / (dlo - dhi), Fr(0)
    return Fr(1), Fr(0)


def run(traders, truth, c, days):
    """Returns per-day rows (day, x, p, mu, account, normalized weighting)."""
    U = sum((t.weight * t.budget for t in traders), Fr(0))
    account, rows = Fr(0), []
    for day in range(days):
        p, mu = clear(traders, day, c)
        x = Fr(1) if truth(day) else Fr(0)
        ratio = mu * (1 - c) / (U - account)        # stake over headroom, in [0, 1]
        pos = [t.position(day, p) for t in traders]
        for t, s in zip(traders, pos):
            t.wealth += s * (x - p)
            assert t.wealth >= 0, (t.name, day)
        account += mu * (x - c)
        firm = sum((t.weight * (t.wealth - t.budget) for t in traders), Fr(0))
        assert firm == -account
        assert 0 <= ratio <= 1
        rows.append((day, int(x), p, mu, account, ratio))
    return rows


def failing_days(truth, days):
    return [n for n in range(days) if not truth(n)]


def table_family(c, theta, truth, days, off=Fr(0)):
    """T_R knows the first R failing days of `truth`; weight theta^R. Truncated at the
    number of failing days in the horizon plus a tail trader carrying the weight of
    every longer table, which is exact through the horizon."""
    fails = failing_days(truth, days)
    fam = [TableSeller(f"table{R}", theta ** R, c, fails[:R], off) for R in range(1, len(fails) + 1)]
    tail = theta ** (len(fails) + 1) / (1 - theta)
    fam.append(TableSeller("table-tail", tail, c, fails, off))
    return fam


# ---------------------------------------------------------------- experiments

C = Fr(3, 5)
DAYS = 60           # tables alone: every price is the floor, denominators stay small
SHORT = 20          # with interior prices each day's root squares the denominators
MID = 32


def natural_firm():
    return [ConstantSeller("seller", Fr(1, 4), C),
            ConstantSeller("seller-0mod4", Fr(1, 4), C, on=lambda d: d % 4 == 0),
            Buyer("buyer", Fr(1, 4), C, Fr(7, 10), Fr(1, 2))]


def experiments():
    out = {}
    # E1: the listed firm on each sequence.
    for name, truth in (("all-true", all_true), ("periodic", periodic), ("scrambled", scrambled)):
        out[f"E1 natural firm, {name}"] = run(natural_firm(), truth, C, SHORT)
    # E2: tables alone, at a weight ratio on each side of 1 - c = 2/5.
    for theta in (Fr(1, 2), Fr(3, 10)):
        out[f"E2 tables theta={theta}, scrambled"] = run(
            table_family(C, theta, scrambled, DAYS), scrambled, C, DAYS)
    # E3: tables at theta = 1/2 against a buyer and a follower.
    firm = table_family(C, Fr(1, 2), scrambled, MID) + [
        Buyer("buyer", Fr(1), C, Fr(7, 10), Fr(1, 2)),
        Follower("follower", Fr(1, 4), C, Fr(1, 20), Fr(1, 2))]
    out["E3 tables theta=1/2 + buyer + follower, scrambled"] = run(firm, scrambled, C, MID)
    out["E3 traders"] = firm
    # E4: the same firm without the tables.
    firm = [Buyer("buyer", Fr(1), C, Fr(7, 10), Fr(1, 2)),
            Follower("follower", Fr(1, 4), C, Fr(1, 20), Fr(1, 2))]
    out["E4 buyer + follower, scrambled"] = run(firm, scrambled, C, MID)
    # E5: tables at theta = 4/5 that also stake 1/20 of their wealth off their table,
    # against that buyer at weight 1/8.
    buyer = Buyer("buyer", Fr(1, 8), C, Fr(7, 10), Fr(1, 2))
    firm = table_family(C, Fr(4, 5), scrambled, MID, off=Fr(1, 20)) + [buyer]
    out["E5 tables theta=4/5 staking 1/20 off-table + buyer, scrambled"] = run(
        firm, scrambled, C, MID)
    out["E5 buyer wealth"] = buyer.wealth
    return out


def summarize(rows):
    floor_days = [r for r in rows if r[3] > 0]
    floor_false = sum(1 for r in floor_days if r[1] == 0)
    return {
        "false": sum(1 for r in rows if r[1] == 0),
        "floor-binding days": len(floor_days),
        "of which false": floor_false,
        "min account": min(r[4] for r in rows),
        "final account": rows[-1][4],
        "sum ratio": sum(r[5] for r in rows),
    }


def main(argv):
    out = experiments()
    traders = out.pop("E3 traders")
    buyer_wealth = out.pop("E5 buyer wealth")
    for name, rows in out.items():
        s = summarize(rows)
        print(name)
        for k, v in s.items():
            if isinstance(v, Fr) and len(str(v.denominator)) > 30:
                v = f"~{float(v):.6g}  (exact value has a {len(str(v.denominator))}-digit denominator)"
            elif isinstance(v, Fr):
                v = f"{v}  (~{float(v):.6g})"
            print(f"    {k}: {v}")
    print("E3 final wealth by trader (weight * wealth), largest five:")
    for t in sorted(traders, key=lambda t: -t.weight * t.wealth)[:5]:
        print(f"    {t.name}: ~{float(t.weight * t.wealth):.6g}")
    print(f"E5 buyer's final wealth: ~{float(buyer_wealth):.6g}")
    if "--check" in argv:
        check(out)
        print("check: ok")
    return 0


def check(out):
    c, K = C, sum(1 for n in range(DAYS) if not scrambled(n))
    # E2 closed form (TableMixture in StatisticalConditions.lean): after K failures the
    # account is -c * sum_{k<K} r^(k+1) / (1 - theta), r = theta / (1 - c).
    for theta in (Fr(1, 2), Fr(3, 10)):
        r = theta / (1 - c)
        want = -c * sum(r ** (k + 1) for k in range(K)) / (1 - theta)
        assert out[f"E2 tables theta={theta}, scrambled"][-1][4] == want
    # Every multiplier in E2 sits on a failing day.
    for theta in (Fr(1, 2), Fr(3, 10)):
        assert all(r[1] == 0 for r in out[f"E2 tables theta={theta}, scrambled"] if r[3] > 0)
    # In E5 the floor binds on every day, so the posted price is the constant c.
    assert all(r[2] == c and r[3] > 0
               for r in out["E5 tables theta=4/5 staking 1/20 off-table + buyer, scrambled"])
    # The all-true sequence costs nothing.
    assert min(r[4] for r in out["E1 natural firm, all-true"]) >= 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
