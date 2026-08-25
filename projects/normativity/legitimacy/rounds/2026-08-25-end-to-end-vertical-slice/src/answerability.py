"""Theorem scout: does answerable succession already bound cumulative liability?

The target is modest and precise. Write `c_t` for the canonical certified
charge the slice's own path produces at date `t`. Ask whether

    sum_t c_t  <  infinity

follows from *local* invariants on the succession structure Reflective
Integrity already has, rather than from any claim that the per-date deficit
falls — which `trajectories.mesh_counterexample` refutes.

The route is a potential-function argument, and it needs two things the
architecture supplies and one lemma.

**The carrier.** Allowance sits on the **live answerability episode of a
force-bearing standing** — an `AnsRoot`, not a `StandingId`. Two reasons, both
structural. Episode Uniqueness gives at most one current episode per standing,
so the two are interchangeable *while a standing lives*; but only the root has a
succession relation, `succ_t(q) = { q' in MINT(a) | Disposes(a, q) }`, and
succession is exactly the transition at which responsibility moves. Putting
allowance on the standing would leave supersession — which terminates one
standing and creates another — with nothing to carry the balance across.

**The lemma.** `D` is subadditive over any partition of the rows:

    D(union_i G_i) = max_w sum_i sum_{j in G_i} d_j(w)
                  <= sum_i max_w sum_{j in G_i} d_j(w)
                   = sum_i D(G_i)

because a maximum of a sum is at most the sum of the maxima. So charging each
force-bearing episode the solo charge of *its own* rows, over the joint support
and the joint live worlds, over-covers the actual joint charge. That is what
turns a charge computed from all rows at once into something a per-episode
ledger can account for.

**What is not assumed.** Not that `D_t` falls, not that the live worlds shrink,
not that any source is handed enough budget to cover its future. The hypotheses
are `Phi_0 < infinity` — a fact about the seed — and a grant channel whose total
is finite, with the degenerate and cleanest case being no grants at all.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Iterable, Optional, Sequence

import safety

ZERO = Fraction(0)


class LiabilityViolation(Exception):
    """A transition that would create allowance out of nothing."""


# ------------------------------------------------------- the allocation lemma


def allocate(compiled, live_worlds: Sequence, date: int,
             slack: Fraction, volume: Fraction,
             tolerance: Fraction) -> dict:
    """The per-standing solo charge, over the joint support and assessment.

    Each group is a genuine `ForceRequest` in its own right: same date, same
    support, same live worlds, a sub-presentation of the rows. So each number
    here is the canonical charge of a real request, not a share invented by an
    accounting convention.
    """
    groups: dict = {}
    for row in compiled.rows:
        groups.setdefault(row.standing_id, []).append(row)
    out = {}
    for standing_id, rows in groups.items():
        sub = _SubPresentation(compiled.coords, tuple(rows))
        cert = safety.certify(sub, live_worlds, date)
        out[standing_id] = safety.charge(slack, volume, tolerance, cert)
    return out


@dataclass(frozen=True)
class _SubPresentation:
    """A `Compiled` restricted to one standing's rows, on the joint fragment."""

    coords: tuple
    rows: tuple


def subadditivity_gap(joint_charge: Fraction, allocation: dict) -> Fraction:
    """`sum_i alloc_i - c_t`, which the lemma says is nonnegative."""
    return sum(allocation.values(), ZERO) - Fraction(joint_charge)


# ------------------------------------------------------------- the ledger


@dataclass
class AllowanceLedger:
    """`B_t : AnsRootId -> Q>=0` over live episodes, and the laws on it.

    Every mutation goes through one of four typed transitions. There is no
    method that raises an allowance without recording a grant, which is what
    makes "no silent creation" a property of the type rather than a discipline.
    """

    balances: dict = field(default_factory=dict)
    granted: Fraction = ZERO           # cumulative eta
    charged: Fraction = ZERO           # cumulative allocated charge
    log: list = field(default_factory=list)

    # -- the potential -------------------------------------------------

    def potential(self) -> Fraction:
        """`Phi_t = sum over live episodes of B_t(e)`."""
        return sum(self.balances.values(), ZERO)

    # -- the four transitions ------------------------------------------

    def grant(self, root: str, amount: Fraction, reason: str) -> None:
        """L3. New capacity enters here and nowhere else, and is counted.

        `reason` is required because a grant is an act someone is answerable
        for; nothing here checks who, and the field exists so that the future
        inquiry layer has something to read.
        """
        amount = Fraction(amount)
        if amount < ZERO:
            raise LiabilityViolation("a grant is nonnegative")
        self.balances[root] = self.balances.get(root, ZERO) + amount
        self.granted += amount
        self.log.append(("grant", root, amount, reason))

    def spend(self, root: str, amount: Fraction) -> bool:
        """L1. Charge the episode answerable for the force being exercised.

        Returns `False` when the episode cannot afford it, which is the
        accounting counterpart of the force layer's `quarantine`: the demand
        stands, nothing is spent, and no force is emitted.
        """
        amount = Fraction(amount)
        if amount < ZERO:
            raise LiabilityViolation("a charge is nonnegative")
        if self.balances.get(root, ZERO) < amount:
            return False
        self.balances[root] -= amount
        self.charged += amount
        self.log.append(("spend", root, amount, ""))
        return True

    def succeed(self, q: str, successors: Iterable[str],
                grants: Optional[dict] = None) -> None:
        """L2. Allowance may flow to successors; it may not grow on the way.

        `sum_{q' in succ(q)} B(q')  <=  B(q) + explicit grant`

        Many-to-many is handled by calling this once per disposed predecessor;
        a successor of two predecessors accumulates from both, and the bound is
        still respected because each call only adds what its own predecessor
        released. Splitting, merging and plain replacement are all this one
        transition.
        """
        grants = dict(grants or {})
        available = self.balances.pop(q, ZERO)
        successors = list(successors)
        if not successors:
            # the episode is discharged; its allowance leaves the system.
            self.log.append(("discharge", q, available, ""))
            return
        share = available / len(successors)
        for q_prime in successors:
            self.balances[q_prime] = self.balances.get(q_prime, ZERO) + share
        for q_prime, amount in grants.items():
            self.grant(q_prime, amount, f"granted at succession from {q}")
        self.log.append(("succeed", q, available, tuple(successors)))

    def transfer(self, q: str, q_prime: str) -> None:
        """L4. A custodial move carries the balance and creates nothing.

        `applyEffect` is the identity on a `Transfer`, and the episode's
        successor differs only in its debtor. So this is `succeed` with one
        successor and no grant, and it is named separately only because a reader
        looking for the conservation-under-relabelling law should find one.
        """
        self.succeed(q, [q_prime])

    def retire(self, q: str) -> Fraction:
        """An episode ends with no successor; its allowance leaves the system."""
        amount = self.balances.pop(q, ZERO)
        self.log.append(("discharge", q, amount, ""))
        return amount


# --------------------------------------------------- the one-step inequality


@dataclass(frozen=True)
class Step:
    """One date's accounting, and the inequality it is supposed to satisfy."""

    date: int
    charge: Fraction                   # c_t, the joint canonical charge
    allocated: Fraction                # sum_i alloc_i, what the ledger debited
    granted: Fraction                  # eta_t
    potential_before: Fraction
    potential_after: Fraction
    withheld: tuple = ()

    @property
    def holds(self) -> bool:
        """`c_t + Phi_{t+1} <= Phi_t + eta_t`."""
        return (self.charge + self.potential_after
                <= self.potential_before + self.granted)


def telescopes(steps: Sequence[Step]) -> bool:
    """`sum_{t<T} c_t + Phi_T <= Phi_0 + sum_{t<T} eta_t`.

    Checked directly rather than inferred from the one-step inequalities, so a
    failure of the induction shows up here rather than being assumed away.
    """
    if not steps:
        return True
    total = sum((s.charge for s in steps), ZERO)
    grants = sum((s.granted for s in steps), ZERO)
    return total + steps[-1].potential_after <= steps[0].potential_before + grants


def bound(steps: Sequence[Step]) -> Fraction:
    """`Phi_0 + sum eta_t`, the ceiling the telescoping gives on `sum_t c_t`."""
    if not steps:
        return ZERO
    return steps[0].potential_before + sum((s.granted for s in steps), ZERO)


# ------------------------------------------------------------ a driven run


def run_accounted(days: Sequence[int], stage_at, view_at,
                  ledger: AllowanceLedger, episode_of,
                  slack: Fraction = Fraction(1, 100),
                  volume: Fraction = Fraction(1),
                  tolerance: Fraction = Fraction(1, 10)) -> list:
    """Drive the slice's own pipeline and account for each date.

    `episode_of(standing_id)` names the answerability episode currently
    answerable for that standing's force. `stage_at(n)` and `view_at(n)` are the
    epistemic and normative states.

    A date whose episode cannot afford its allocation is *withheld*: nothing is
    spent and that date contributes no charge, which is the accounting-side
    image of the force layer's `quarantine`.
    """
    from pipeline import run_day

    steps = []
    for n in days:
        before = ledger.potential()
        granted_before = ledger.granted
        run = run_day(n, stage_at(n), view_at(n), slack=slack, volume=volume,
                      tolerance=tolerance, observe=True)
        if run.conflict.blocking:
            steps.append(Step(n, ZERO, ZERO, ledger.granted - granted_before,
                              before, ledger.potential()))
            continue
        alloc = allocate(run.compiled, run.live_worlds, n, slack, volume,
                         tolerance)
        withheld, spent = [], ZERO
        for standing_id, amount in sorted(alloc.items()):
            episode = episode_of(standing_id)
            if ledger.spend(episode, amount):
                spent += amount
            else:
                withheld.append(standing_id)
        charge = ZERO if withheld else Fraction(run.charge)
        steps.append(Step(n, charge, spent, ledger.granted - granted_before,
                          before, ledger.potential(), tuple(withheld)))
    return steps


class LaunderingLedger(AllowanceLedger):
    """L2 removed: succession refreshes the balance instead of carrying it.

    The necessity witness. With it, one standing superseded by an equivalent
    successor every date drives the cumulative charge past any bound while every
    individual date looks locally unremarkable.
    """

    def __init__(self, refresh: Fraction) -> None:
        super().__init__()
        self.refresh = Fraction(refresh)

    def succeed(self, q, successors, grants=None) -> None:
        self.balances.pop(q, None)
        for q_prime in successors:
            self.balances[q_prime] = self.refresh
        self.log.append(("laundered", q, self.refresh, tuple(successors)))


class SilentCreationLedger(AllowanceLedger):
    """L3 removed: a fresh episode starts funded, with no grant recorded."""

    def __init__(self, default: Fraction) -> None:
        super().__init__()
        self.default = Fraction(default)

    def spend(self, root: str, amount: Fraction) -> bool:
        if root not in self.balances:
            self.balances[root] = self.default      # no grant is counted
        return super().spend(root, amount)
