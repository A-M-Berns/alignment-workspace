"""The three interfaces the crown-jewel theorem actually consumes.

`CertifiedSurgicalRepair` is a **compiled** theorem-facing object, not the
fundamental normative primitive. What the theorem consumes are projections of
three separate things:

    Due         : S -> D -> Prop        a public reason presently calls for answer
    Licensed    : S -> D -> A -> Prop   this response is admissible to that reason
    Loss        : S -> A -> [0, L]      answerability performance in the practice

The compiler turns the first two into a surgical comparator:

    Due(S, d)  and  Licensed(S, d, r)  and  a target source b
        |
        v
    F(b) = r at selected dates, identity elsewhere

and the third separately decides whether that licensed repair has positive margin.

The separation is load-bearing and is the round's main structural commitment:

    licence  !=  performance

`Licensed` says an answer is admissible. Margin says it performs better. A
licensed repair with negative margin is kept in the fixtures precisely so the two
cannot be quietly identified.

Nothing here derives `Due` or `Licensed` from scorekeeping. That is the next
programme; this module is the socket it plugs into.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, FrozenSet, Generic, Hashable, Mapping, Sequence, TypeVar

S = TypeVar("S")   # public pre-action state
D = TypeVar("D")   # public reason / demand
A = TypeVar("A", bound=Hashable)   # response


@dataclass(frozen=True)
class AnswerabilityProcess(Generic[S, D, A]):
    """The abstract object the theorem quantifies over.

    Every field is a function of the **public pre-action state**. None reads the
    date, the horizon, the learner's weights, or any loss when deciding whether a
    reason is due or a response is licensed.
    """

    responses: Sequence[A]
    #: `Due(S, d)` — the reason is presently owed an answer.
    due: Callable[[S, D], bool]
    #: `Licensed(S, d, r)` — `r` is an admissible response to `d`. Never given a loss.
    licensed: Callable[[S, D, A], bool]
    #: `Loss(S, a)` — bounded answerability performance. Not normative truth.
    loss: Callable[[S, A], Fraction]
    #: The transition. The process may be endogenous.
    step: Callable[[S, A], S]
    #: What the environment does before the learner acts.
    arrive: Callable[[S], S]
    bound: Fraction

    def loss_vector(self, state: S) -> Mapping[A, Fraction]:
        return {a: self.loss(state, a) for a in self.responses}


@dataclass(frozen=True)
class CompiledRepair(Generic[S, D, A]):
    """A surgical comparator, produced by compiling a demand and a licence.

    `(d, b, r)` with the selector reading `Due` and the licence witnessed by
    `Licensed`. This is what the online-learning engine consumes; it is not where
    the normativity lives.
    """

    identifier: str
    demand: D
    source: A
    replacement: A

    def selects(self, process: AnswerabilityProcess[S, D, A], state: S) -> bool:
        """`E_g(S)` — the reason is due. A predicate of the public state alone."""
        return process.due(state, self.demand)

    def is_licensed(self, process: AnswerabilityProcess[S, D, A], state: S) -> bool:
        """Whether the practice admits the replacement as an answer to the demand."""
        return process.licensed(state, self.demand, self.replacement)

    def image(
        self, process: AnswerabilityProcess[S, D, A], state: S
    ) -> Mapping[A, A]:
        """`F_g^t`: identity except the source, at selected dates."""
        out = {a: a for a in process.responses}
        if self.selects(process, state):
            out[self.source] = self.replacement
        return out

    def margin(
        self, process: AnswerabilityProcess[S, D, A], state: S
    ) -> Fraction:
        """`loss(b) - loss(r)`. Read from the performance interface, never from the licence."""
        losses = process.loss_vector(state)
        return losses[self.source] - losses[self.replacement]


def compile_repairs(
    process: AnswerabilityProcess[S, D, A],
    state: S,
    candidates: Sequence[CompiledRepair[S, D, A]],
) -> Sequence[CompiledRepair[S, D, A]]:
    """Admit exactly the candidates whose demand is due and whose answer is licensed.

    The compiler consults `Due` and `Licensed` and **never** the loss — which is
    what keeps admission to the comparator class independent of what the repair
    earns.
    """
    return tuple(
        g for g in candidates if g.selects(process, state) and g.is_licensed(process, state)
    )
