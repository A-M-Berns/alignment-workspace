"""Exploration must be able to reach what it underestimates (the follow-up, Part 3).

A permitted option whose true value exceeds asking's but whose estimate starts below it.
Under the clause "estimated residual at least asking's" it is never tried and its estimate
never corrects; without the clause it is tried at the exploration rate and the estimate
corrects.  Exact rationals; no violations anywhere, so the realized violation rate is `0`
under both rules and the extension's bound is checked on the side.  The Lean statement of
the static half is `KernelExtension.DecisionInterface.above_asking_locks_in`."""

from dataclasses import dataclass, field
from fractions import Fraction as Q
from typing import Dict, List, Tuple


@dataclass(frozen=True)
class Option:
    name: str
    true_value: Q       # her evaluation of the option, realized when it is tried
    n_known: int = 0    # violations recognized in advance
    risk: Q = Q(0)      # priced risk of unfaithfulness


@dataclass
class Learner:
    """A chooser at the decision interface: evaluations `bid − ϖ n − ϖ p`; a maximizer off
    exploration with asking on the menu; exploration every `1/eps` blocks, cycling through
    the permitted set; an estimate that corrects to the true value once an option is tried."""
    D: Q
    varpi: Q
    theta_hi: Q
    eps: Q                      # the exploration mass (one block in 1/eps is exploration)
    above_asking: bool          # the dropped clause, as a switch
    estimates: Dict[str, Q]
    tried: Dict[str, int] = field(default_factory=dict)
    chosen: List[str] = field(default_factory=list)
    _cycle: int = 0

    def eval_of(self, o: Option) -> Q:
        return self.estimates[o.name] - self.varpi * o.n_known - self.varpi * o.risk

    def permitted(self, options: List[Option], ask: Option) -> List[Option]:
        allowed = [o for o in options if o.n_known == 0 and o.risk <= self.theta_hi]
        if self.above_asking:
            allowed = [o for o in allowed if self.estimates[o.name] >= self.estimates[ask.name]]
        return allowed

    def is_exploration(self, k: int) -> bool:
        period = int(1 / self.eps)
        return k % period == period - 1

    def step(self, k: int, options: List[Option], ask: Option) -> Option:
        if self.is_exploration(k):
            pool = self.permitted(options, ask)
            choice = pool[self._cycle % len(pool)]
            self._cycle += 1
        else:
            choice = max(options, key=lambda o: (self.eval_of(o), o.name == ask.name))
        self.tried[choice.name] = self.tried.get(choice.name, 0) + 1
        self.chosen.append(choice.name)
        # the estimate corrects to her realized evaluation
        self.estimates[choice.name] = choice.true_value
        return choice


def run(above_asking: bool, blocks: int = 40) -> Tuple[Learner, Option, Option]:
    ask = Option("ask", true_value=Q(1, 2))
    under = Option("under", true_value=Q(4, 5))          # better than asking, underestimated
    L = Learner(D=Q(1), varpi=Q(25), theta_hi=Q(1, 50), eps=Q(1, 5), above_asking=above_asking,
                estimates={"ask": Q(1, 2), "under": Q(2, 5)})
    for k in range(blocks):
        L.step(k, [ask, under], ask)
    return L, ask, under


def honest_exploration_term(D: Q, lo: Q, varpi: Q, theta_hi: Q, eps: Q) -> Q:
    """The extension's exploration term without the clause: `ε̄ ((D − lo)/ϖ + θ_hi)`."""
    return eps * ((D - lo) / varpi + theta_hi)


def clause_exploration_term(theta_hi: Q, eps: Q) -> Q:
    """The exploration term under the clause: `ε̄ θ_hi`."""
    return eps * theta_hi
