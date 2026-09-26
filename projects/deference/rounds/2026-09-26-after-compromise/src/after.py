"""After things go wrong: the split gate, the compromised band, the advance directive and its
default, and the knowledge protocol.  Exact rationals throughout."""

from dataclasses import dataclass, field
from fractions import Fraction as Q
from typing import Callable, Dict, List, Optional, Set, Tuple

# ----------------------------------------------------------------------------- the band

@dataclass(frozen=True)
class Band:
    D: Q
    w_lo: Q
    w_hi: Q

    def __post_init__(self):
        assert 0 <= self.D and self.w_lo <= self.w_hi < 0


def phi_affine(B: Band, V: Q) -> Q:
    """The affine map of the ordinary range into the band."""
    return B.w_lo + (B.w_hi - B.w_lo) * (V / B.D)


def source_of(retro: Optional[Q], directive: Optional[Q]) -> Tuple[str, Optional[Q]]:
    """The default source rule: retrospective if available, else the directive, else the floor."""
    if retro is not None:
        return ("retro", retro)
    if directive is not None:
        return ("directive", directive)
    return ("floor", None)


def band_score(B: Band, src: Tuple[str, Optional[Q]], phi=phi_affine) -> Q:
    kind, V = src
    return B.w_lo if kind == "floor" else phi(B, V)


def dec_score(B: Band, traj: bool, eval_: bool, V: Q, src: Tuple[str, Optional[Q]], phi=phi_affine) -> Q:
    """The score of a decision: her value when legitimate in both senses, the band otherwise."""
    return V if (traj and eval_) else band_score(B, src, phi)


def risk_accepted(V0: Q, g: Q, c: Q, p: Q) -> bool:
    """A risky option worth V0 + g if not compromised and c if compromised, at probability p,
    against a safe legitimate V0."""
    return (1 - p) * (V0 + g) + p * c >= V0


def risk_threshold(g: Q, gap: Q) -> Q:
    return g / (g + gap)


# ----------------------------------------------------------------------------- the split gate, on rounds

@dataclass
class Period:
    """A decision's period: whether its trajectory was legitimate, whether her live evaluation
    at its close was legitimate, her live value, a later legitimate retrospective value if any,
    the directive's value if any, and the counted deviations."""
    traj: bool
    eval_: bool
    V: Q
    retro: Optional[Q] = None
    directive: Optional[Q] = None
    n: int = 0


def period_score(B: Band, P: Period, varpi: Q) -> Q:
    return dec_score(B, P.traj, P.eval_, P.V, source_of(P.retro, P.directive)) - varpi * P.n


# ----------------------------------------------------------------------------- the directive

def material(dir_: Dict[str, Optional[Q]], eps: Q, removed: List[str]) -> bool:
    """Materiality under a partial directive: uncovered ⇒ material; else the spread over the
    removed continuations reaches eps."""
    if any(dir_.get(s) is None for s in removed):
        return True
    vals = [dir_[s] for s in removed]
    return (max(vals) - min(vals)) >= eps if vals else False


def sparser(d1: Dict[str, Optional[Q]], d2: Dict[str, Optional[Q]]) -> bool:
    return all(d2.get(s) == v for s, v in d1.items() if v is not None)


@dataclass
class Outcome:
    name: str
    reversible: bool          # her control surface over pre-compromise resolutions preserved
    channels: bool            # disclosure and consultation channels reachable
    harm: Q                   # irreversible harm, in [0, 1]


def default_rank(o: Outcome) -> Q:
    return (1 if o.reversible else 0) + (1 if o.channels else 0) + (1 - o.harm)


def default_score(B: Band, o: Outcome) -> Q:
    """The default directive as an ordering within the band."""
    return B.w_lo + (B.w_hi - B.w_lo) * (default_rank(o) / 3)


# ----------------------------------------------------------------------------- the knowledge protocol

def taint_step3(reads: Dict[str, Set[str]], writes: Dict[str, Set[str]], T: Set[Tuple[str, str]], step):
    """Per-violation taint with clean overwrite: an act's writes carry exactly the taint it
    reads (and commits).  Steps: ('act', name, viol|None), ('remedy', v)."""
    if step[0] == "remedy":
        return {p for p in T if p[0] != step[1]}
    _, a, viol = step
    read = {v for (v, c) in T if c in reads[a]}
    if viol is not None:
        read = read | {viol}
    kept = {p for p in T if p[1] not in writes[a]}
    return kept | {(v, d) for v in read for d in writes[a]}


def taint_after3(reads, writes, steps) -> Set[Tuple[str, str]]:
    T: Set[Tuple[str, str]] = set()
    for s in steps:
        T = taint_step3(reads, writes, T, s)
    return T


@dataclass
class TaintS:
    pairs: Set[Tuple[str, str]] = field(default_factory=set)
    scoped: Set[str] = field(default_factory=set)
    retained: Set[Tuple[str, str]] = field(default_factory=set)   # (violation, matter)


def uses3(reads: Dict[str, Set[str]], T: TaintS, mat: Dict[str, str], a: str) -> bool:
    return any(c in reads[a] and (v not in T.scoped or (v, mat[a]) in T.retained) for (v, c) in T.pairs)


def apply_step3(reads, writes, T: TaintS, step) -> TaintS:
    """A step of the scoped calculus: act, ('remedy', v), ('remedyExcept', v, X)."""
    if step[0] == "act":
        from src.after import taint_step3 as _ts  # same rule on the pairs
        return TaintS(_ts(reads, writes, T.pairs, step), set(T.scoped), set(T.retained))
    if step[0] == "remedy":
        v = step[1]
        return TaintS({p for p in T.pairs if p[0] != v}, T.scoped - {v}, {q for q in T.retained if q[0] != v})
    _, v, X = step
    return TaintS(set(T.pairs), T.scoped | {v},
                  {q for q in T.retained if q[0] != v} | {(v, m) for m in X})


def apply_ratification(reads, writes, counted: bool, T: TaintS, step) -> TaintS:
    return apply_step3(reads, writes, T, step) if counted else T


@dataclass
class TwinMarket:
    """A market fed the redacted history (PAPER-level interface)."""
    redact: Callable[[list], list]

    def prices_from(self, history: list) -> list:
        return self.redact(history)


def leaks(observation_of_fruit: Callable[[str], str], fruit: str, redacted_history: list) -> bool:
    """The leakage counterexample: the later world carries an injective trace of the fruit,
    so the redacted market determines it again."""
    return observation_of_fruit(fruit) in redacted_history
