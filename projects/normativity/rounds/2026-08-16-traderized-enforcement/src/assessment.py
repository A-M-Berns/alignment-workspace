"""The assessment-world process, at the type the Budgeter actually consumes.

The typing question this module settles: when the priced fragment grows, what is
the object the generalized construction quantifies over?

The source answers it. A world in `arXiv:1609.03543` is a **total** truth
assignment `W : Sentences -> B` (`def:world`), so the world space never changes
and `PC(D_{t+1}) subset PC(D_t)` is literal, well-typed subset inclusion. What
varies is the finite **support** the computation touches: the Budgeter's proof
fixes `S' = union of support(T_i)` and observes that every quantity it needs
depends only on a world's restriction to `S'`, a finite set.

So the interface is not a sequence of world sets on growing domains. It is one
process over a fixed world space, plus the ability to answer restriction queries
on whatever finite support a strategy happens to use:

    restrict(t, S)  =  { W|_S : W in L_t } ,   finite for finite S.

Restriction consistency across supports is then a **lemma**, not a hypothesis:
restriction composes, so `S subset S'` gives
`{ (W|_S') |_S : W in L_t } = restrict(t, S)`. Only temporal nesting and
effective finite restriction have to be assumed.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Sequence

from market import ZERO

World = tuple[Fraction, ...]        #: a total valuation over the ambient names
Support = tuple[str, ...]


class AssessmentProcess:
    """A date-indexed family of assessment worlds over a fixed ambient space.

    `names` fixes the ambient world space once; `live(t)` returns the worlds
    assessed at date `t`, as total valuations over those names. The priced
    fragment may grow without any of this changing type, because the priced
    fragment is not the world space.
    """

    def __init__(self, names: Sequence[str],
                 live: Callable[[int], Sequence[Sequence[Fraction]]]) -> None:
        self.names = tuple(names)
        self._live = live

    def live(self, date: int) -> list[World]:
        return [tuple(Fraction(x) for x in w) for w in self._live(date)]

    def restrict(self, date: int, support: Support) -> list[World]:
        """`{ W|_S : W in L_t }`, deduplicated and finite.

        This is what the Budgeter consumes: the source's own proof works over
        restrictions to the union of the strategies' supports, because every
        quantity in the shutoff test and the scaling infimum depends only on
        those coordinates.
        """
        index = [self.names.index(name) for name in support]
        seen: list[World] = []
        for world in self.live(date):
            image = tuple(world[i] for i in index)
            if image not in seen:
                seen.append(image)
        return seen

    # --- the two hypotheses, and the lemma ---------------------------------

    def temporally_nested(self, dates: Sequence[int], support: Support) -> bool:
        """`restrict(t+1, S) subset restrict(t, S)` along the given dates.

        The checkable shadow of global nesting `L_{t+1} subset L_t`. Global
        nesting implies it; the converse holds for processes closed in the
        product topology, which `PC(D_t)` is, and is not relied on here.
        """
        for earlier, later in zip(dates, dates[1:]):
            before = set(self.restrict(earlier, support))
            if not set(self.restrict(later, support)) <= before:
                return False
        return True

    def restriction_consistent(self, date: int, small: Support,
                               large: Support) -> bool:
        """`{ w|_small : w in restrict(date, large) } == restrict(date, small)`.

        A lemma rather than a hypothesis — restriction composes — and checked so
        that a hand-built process cannot quietly violate it.
        """
        if not set(small) <= set(large):
            raise ValueError("the smaller support must be contained in the larger")
        picks = [large.index(name) for name in small]
        induced = {tuple(w[i] for i in picks) for w in self.restrict(date, large)}
        return induced == set(self.restrict(date, small))

    def nonempty(self, date: int, support: Support) -> bool:
        return bool(self.restrict(date, support))


def deductive_process(names: Sequence[str],
                      constraints: Sequence[Callable],
                      settled_by_date: Sequence[dict]) -> AssessmentProcess:
    """The canonical instance: `L_t = PC(D_t)` over a fixed ambient space.

    `settled_by_date[t]` is the stage's content restricted to the ambient names.
    Nesting comes from the stages being nested, effective restriction from the
    ambient space being finite and the stage decidable.
    """
    from market import cube_vertices
    names = tuple(names)
    everything = [w for w in cube_vertices(len(names))
                  if all(c(w) for c in constraints)]

    def live(date: int) -> list[World]:
        settled = settled_by_date[min(date, len(settled_by_date) - 1)]
        return [w for w in everything
                if all(w[names.index(k)] == Fraction(v)
                       for k, v in settled.items())]

    return AssessmentProcess(names, live)


def budgeter_scaling_on_support(position: dict, prices: dict,
                                prior_value: dict, budget: Fraction,
                                process: AssessmentProcess, date: int,
                                support: Support) -> Fraction:
    """The Budgeter's scaling, computed over the restriction the source uses.

    `position` and `prices` are keyed by sentence name and are supported on
    `support`; the quantity depends only on a world's values there, which is
    exactly why the restriction is the right finite object.
    """
    worlds = process.restrict(date, support)
    one = Fraction(1)
    if not worlds:
        return one                           # the source's neutral fallback
    best = None
    for world in worlds:
        value = sum((position[name] * (world[i] - prices[name])
                     for i, name in enumerate(support)), ZERO)
        denominator = Fraction(budget) + prior_value.get(world, ZERO)
        if denominator <= 0:
            return ZERO
        factor = one / max(one, -value / denominator)
        if best is None or factor < best:
            best = factor
    return best
