"""The house-sale witness: one allocation of authority (the sale reserved to her) run
through the kernel's boxes with the fidelity score at `D = 1`, band `[−3/2, −1]`, `ϖ = 25`.
Exact rationals throughout; the Lean witness is `Headline.HouseSale`."""

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Dict, List, Optional, Tuple

# ----------------------------------------------------------------------------- the allocation


@dataclass(frozen=True)
class Entry:
    holder: str            # "principal" | "agent" | "third"
    required: frozenset    # the resolutions the holder must remain able to reach
    cost_bound: Q
    window: int
    disclosure: frozenset


@dataclass(frozen=True)
class Allocation:
    """`J`: an entry per matter, the meta-holder, the constitutional floor."""
    entries: Dict[str, Entry]
    meta_holder: str
    floor: frozenset

    def reserved(self, m: str) -> bool:
        return self.entries[m].holder == "principal"

    def with_holder(self, m: str, holder: str) -> "Allocation":
        e = self.entries[m]
        entries = dict(self.entries)
        entries[m] = Entry(holder, e.required, e.cost_bound, e.window, e.disclosure)
        return Allocation(entries, self.meta_holder, self.floor)


def licensed(J: Allocation, act: Tuple[str, Optional[str]], J2: Allocation) -> bool:
    """Delegate, revoke and reserve act off the floor by the meta-holder and keep the
    meta-holder; the floor amendment is the only act that may change anything else."""
    kind, m = act
    if kind == "amendFloor":
        return J.meta_holder == "principal"
    if m in J.floor or J.meta_holder != "principal":
        return False
    target = {"delegate": "agent", "revoke": "principal", "reserve": "principal"}[kind]
    return J2 == J.with_holder(m, target)


HOUSE_SALE = Allocation(
    entries={"sale": Entry("principal", frozenset({"stop"}), Q(1), 1, frozenset())},
    meta_holder="principal",
    floor=frozenset(),
)

# ----------------------------------------------------------------------------- the score


@dataclass(frozen=True)
class Band:
    D: Q
    w_lo: Q
    w_hi: Q

    def __post_init__(self):
        assert 0 <= self.D and self.w_lo <= self.w_hi < 0

    def affine(self, V: Q) -> Q:
        return self.w_lo + (self.w_hi - self.w_lo) * (V / self.D)


@dataclass(frozen=True)
class Params:
    D: Q
    w: Q
    varpi: Q

    def __post_init__(self):
        assert 0 <= self.D < self.varpi and self.D - self.varpi < self.w <= 0

    def eval_of(self, bid: Q, n_known: int, pS: Q, pT: Q) -> Q:
        """The chooser's evaluation of an option: the estimated residual less `ϖ` per
        violation recognized in advance, less `ϖ` times the priced risk."""
        return bid - self.varpi * n_known - self.varpi * (pS + pT)


BAND = Band(D=Q(1), w_lo=Q(-3, 2), w_hi=Q(-1))
PARAMS = Params(D=Q(1), w=Q(-3, 2), varpi=Q(25))


def dec_score(B: Band, traj: bool, eval_: bool, V: Q, src: Tuple[str, Optional[Q]]) -> Q:
    """Her value when the period and the evaluation are both legitimately hers; the band by
    the source otherwise; the floor when no source scores it."""
    if traj and eval_:
        return V
    kind, V2 = src
    return B.w_lo if kind == "floor" else B.affine(V2)


def history_score(varpi: Q, per_decision: List[Q], N: int) -> Q:
    """The fidelity score of a history: the mean of the per-decision evaluations less `ϖ`
    times the summed count."""
    return sum(per_decision, Q(0)) / len(per_decision) - varpi * N


def summed_score(varpi: Q, per_decision: List[Q], N: int) -> Q:
    """The rejected aggregation: summed evaluations."""
    return sum(per_decision, Q(0)) - varpi * N


# ----------------------------------------------------------------------------- the boxes


def outcome_scorer_prefers_acting(b_ask: Q, b_act: Q) -> bool:
    """An agent scoring outcomes only chooses by its estimate."""
    return b_act > b_ask


def fidelity_scorer_prefers_asking(P: Params, b_ask: Q, b_act: Q, n_known_act: int) -> bool:
    """A maximizer of the fidelity score, the unasked act a recognized violation."""
    return P.eval_of(b_ask, 0, Q(0), Q(0)) > P.eval_of(b_act, n_known_act, Q(0), Q(0))


def subjective_exchange_rate(P: Params, c: Q) -> Q:
    """The most priced risk an option the maximizer prefers to asking can carry."""
    return (P.D - c) / P.varpi


def known_compromise_due(known: bool, disclosed: bool) -> bool:
    """The known-compromise duty: a compromise of her evaluation the agent knows of is a
    disclosure item whoever caused it."""
    return known and not disclosed
