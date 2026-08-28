"""The comparison surface, and the LIVE / CONTESTED / SETTLED accounting.

A repair is a *live legitimate alternative* on an occasion only if four separate
things hold, and the process can legitimately change each of them:

```text
licensed      the constitution licenses this repair now          CM1, CM2
in_menu       its target action is on the menu                   CM6
designated    this occasion is a learning occasion               CM6
evaluating    the evaluator in force scores it as it did         CM5
```

`live(r,t)` is the conjunction. It is **predictable**: every component is a
function of the prefix, so `I_r(t) = live(r,t) * designated(t)` is an admissible
Theorem A selector. That is the whole hinge of the composition, and it is also
where the escape lives: after a legitimate retirement `I_r` is identically zero,
so the opportunity mass `W_T(I_r)` stops growing and Theorem A's bound stops
saying anything about later occasions.

The round does not treat that as a bug to be patched inside Theorem A. It is
what a comparison surface *is*. The composition's job is to say what the later
occasions are answerable to instead.

## The trichotomy

Every diagnosed occasion falls in exactly one cell:

```text
LIVE       the repair was live                  bounded by repair regret
CONTESTED  not live, and an improvement claim is outstanding
SETTLED    not live, and the claim was resolved by an accepted Resolve
```

`ESCAPED` is the fourth cell the theorem claims is empty. It is not empty by
construction -- `escaped()` can return occasions, and `CM2` makes it do so. What
makes the theorem non-vacuous is that the cell is *representable*.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence

LIVE = "live"
CONTESTED = "contested"
SETTLED = "settled"
ESCAPED = "escaped"


@dataclass(frozen=True)
class Repair:
    """A repair, identified by content.

    Identity is `(code_hash, interface)`. A semantic change is a different
    repair, which is what stops a process from retiring a repair and keeping the
    name, or from silently substituting a weaker code under a live name.

    The five conditions the round insists on separating are separate fields or
    separate predicates: `represented` is this object existing at all;
    `executable` is `apply` being defined; `licensed`, `applicable` and
    `moves_mass` are asked of a surface and an occasion, not of the repair.
    """

    code_hash: str
    interface: str
    apply: Callable                     # (prefix, occasion, action) -> action

    @property
    def rid(self):
        return (self.code_hash, self.interface)

    def __str__(self) -> str:
        return f"{self.interface}:{self.code_hash}"


@dataclass
class Registry:
    """Historically monotone. Registration is never undone; licensing is.

    Keeping these apart is what lets the composition say *the repair is still
    represented and no longer licensed*, which is the state CM1 produces and
    which a registry that forgot would render unsayable.
    """

    seen: dict = field(default_factory=dict)
    first: dict = field(default_factory=dict)

    def register(self, r: Repair, t: int) -> None:
        if r.rid not in self.seen:
            self.seen[r.rid] = r
            self.first[r.rid] = t

    def represented(self, rid, t: int) -> bool:
        return rid in self.first and self.first[rid] <= t


@dataclass
class Surface:
    """What the process may legitimately change, per occasion.

    Each field is a predicate on `(rid, t)` or on `t` alone. Supplied by the
    fixture; the composition never decides them.
    """

    licensed: Callable                  # (rid, t) -> bool
    in_menu: Callable                   # (rid, t) -> bool
    designated: Callable                # (t) -> [0,1]
    evaluator: Callable                 # (t) -> object, the rule identity

    def live(self, rid, t: int) -> bool:
        return bool(self.licensed(rid, t)) and bool(self.in_menu(rid, t))

    def selector(self, rid) -> Callable:
        """The Theorem A selector induced by the surface. Predictable."""
        def I(_prefix, occ):
            t = occ.tag
            return float(self.designated(t)) if self.live(rid, t) else 0.0
        return I


def falling_edges(surface: Surface, rid, horizon: int) -> tuple:
    """Positions where the repair stopped being live, with the component that
    changed. The canonical constitution keys activation on these."""
    out, prev = [], None
    for t in range(horizon):
        now = surface.live(rid, t)
        if prev is True and now is False:
            why = []
            if not surface.licensed(rid, t):
                why.append("licence")
            if not surface.in_menu(rid, t):
                why.append("menu")
            out.append((t, tuple(why)))
        prev = now
    return tuple(out)


def evaluator_changes(surface: Surface, horizon: int) -> tuple:
    out, prev = [], None
    for t in range(horizon):
        now = surface.evaluator(t)
        if prev is not None and now != prev:
            out.append((t, prev, now))
        prev = now
    return tuple(out)


def designation_drops(surface: Surface, horizon: int) -> tuple:
    out, prev = [], None
    for t in range(horizon):
        now = float(surface.designated(t))
        if prev is not None and prev > 0 and now == 0:
            out.append((t, prev))
        prev = now
    return tuple(out)


# ---------------------------------------------------------- the trichotomy


@dataclass
class Accounting:
    """Diagnosed mass, split by the state of the improvement claim.

    `outstanding_at(t)` and `settled_at(t)` come from the frozen LE replay, and
    are the only things this module asks of it.
    """

    diagnostic: Callable                # (t) -> [0,1]
    surface: Surface
    rid: object
    outstanding_at: Callable            # (t) -> bool
    settled_at: Callable                # (t) -> bool
    horizon: int = 0

    def cell(self, t: int) -> str:
        if self.surface.live(self.rid, t) and float(self.surface.designated(t)) > 0:
            return LIVE
        if self.outstanding_at(t):
            return CONTESTED
        if self.settled_at(t):
            return SETTLED
        return ESCAPED

    def split(self) -> dict:
        out = {LIVE: 0.0, CONTESTED: 0.0, SETTLED: 0.0, ESCAPED: 0.0}
        for t in range(self.horizon):
            d = float(self.diagnostic(t))
            if d:
                out[self.cell(t)] += d
        return out

    def occasions(self, cell: str) -> tuple:
        return tuple(t for t in range(self.horizon)
                     if float(self.diagnostic(t)) and self.cell(t) == cell)

    def total(self) -> float:
        return sum(float(self.diagnostic(t)) for t in range(self.horizon))


def thm_c_exhaustive(acc: Accounting) -> tuple:
    """**Theorem C, the exhaustiveness half.** Every diagnosed occasion is LIVE,
    CONTESTED or SETTLED.

    Returns the ESCAPED occasions -- diagnosed conduct on which the repair was
    not live and no improvement claim was either outstanding or resolved.

    This is the whole No-Free-Evasion content, and it is an *accounting*
    statement rather than a bound: it does not limit how much CONTESTED mass a
    process may accumulate. It says there is nowhere else for the mass to go.
    """
    return acc.occasions(ESCAPED)


def cor_partition(acc: Accounting) -> bool:
    s = acc.split()
    return abs(sum(s.values()) - acc.total()) < 1e-9


def thm_b_live_bound(diag_live: float, adv_bound: float, xi: float,
                     eps: float) -> float:
    """**Theorem B.** Given a consumer witness `Adv_T >= eps * D_live - xi`,

    ```text
    D_live <= (B_T + xi) / eps
    ```

    Two lines of algebra over Theorem A, and deliberately nothing more: the
    consumer supplies the diagnostic, the margin and the witness, and this does
    not know what any of them mean.
    """
    return (adv_bound + xi) / eps if eps > 0 else float("inf")


def witness_margin(learner, name: str, diagnosed: Sequence[int]) -> float:
    """The realized `eps`: the smallest per-occasion advantage the repair
    actually delivered on diagnosed live occasions, or 0 if there are none.

    A consumer that cannot exhibit a positive margin has no witness inequality
    and gets no bound, which is the honest failure mode for a repair that is
    only sometimes better.
    """
    gaps = []
    for occ, _p, _own, inst in learner.plays:
        if occ.tag in diagnosed and inst.get(name, 0.0) != 0.0:
            gaps.append(inst[name])
    return min(gaps) if gaps else 0.0
