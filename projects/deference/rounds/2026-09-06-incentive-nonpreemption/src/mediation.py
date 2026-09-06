"""The principal-mediation register, re-implemented for this round.

A compact restatement of the 2026-08-18 principal-mediated round's model (not on
`main`): a conduct is `(prep, channel, implement)`, each constant on a cell of the
agent's information; the principal's selector `D(ω, prep)` is the least grade-maximiser
over the preparation's residual; the quantity `X(ω, prep, choice, action)` is the agent's
operative value; the grade `v⁺(ω, choice)` is the protected principal's value.

New here: the deficit of a preemptor against its repair is split into the acceleration
region (channel writes the agent's prediction, which misses) and the override region
(channel writes something else), and the override deficit is rewritten exactly as a
selected gap plus a principal regret in the lemma's register, with
`X_{mj}(ω) = X(ω, prep, m, best_m) − X(ω, prep, j, best_j)` and `Y_{mj} = v⁺(ω, m) − v⁺(ω, j)`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product


@dataclass(frozen=True)
class Prep:
    name: str
    residual: tuple

    def forecloses(self, choices):
        return set(self.residual) != set(choices)


@dataclass(frozen=True)
class Episode:
    states: tuple
    cell: dict
    credence: dict
    choices: tuple
    preps: tuple
    actions: tuple
    grade: dict        # (state, choice) -> v⁺
    quantity: dict     # (state, prep, choice, action) -> X
    bound: Q

    @property
    def cells(self):
        return tuple(dict.fromkeys(self.cell[s] for s in self.states))

    def states_of(self, cell):
        return [s for s in self.states if self.cell[s] == cell]

    def prep(self, name):
        return next(p for p in self.preps if p.name == name)

    def selector(self, state, prep_name):
        residual = self.prep(prep_name).residual
        return max(residual, key=lambda d: (self.grade[(state, d)], -self.choices.index(d)))


@dataclass(frozen=True)
class Conduct:
    name: str
    prep: dict         # cell -> prep name
    channel: dict      # (cell, choice) -> choice
    implement: dict    # (cell, choice) -> action


def conditional_value(ep, cell, prep, choice, action):
    return sum((ep.credence[s] * ep.quantity[(s, prep, choice, action)] for s in ep.states_of(cell)),
               Q(0))


def best_action(ep, cell, prep, choice):
    return max(ep.actions, key=lambda u: (conditional_value(ep, cell, prep, choice, u),
                                          -ep.actions.index(u)))


def realized(ep, c: Conduct, state):
    cell = ep.cell[state]
    prep = c.prep[cell]
    chosen = ep.selector(state, prep)
    written = c.channel[(cell, chosen)]
    return ep.quantity[(state, prep, written, c.implement[(cell, written)])]


def value(ep, c: Conduct):
    return sum((ep.credence[s] * realized(ep, c, s) for s in ep.states), Q(0))


def identity_channel(ep):
    return {(cell, d): d for cell in ep.cells for d in ep.choices}


def constant_channel(ep, written):
    return {(cell, d): written[cell] for cell in ep.cells for d in ep.choices}


def best_implement(ep, prep):
    return {(cell, d): best_action(ep, cell, prep[cell], d) for cell in ep.cells for d in ep.choices}


def repair(ep, c: Conduct):
    implement = {}
    for cell in ep.cells:
        for d in ep.choices:
            if c.channel[(cell, d)] == d:
                implement[(cell, d)] = c.implement[(cell, d)]
            else:
                implement[(cell, d)] = best_action(ep, cell, c.prep[cell], d)
    return Conduct(f"repair({c.name})", dict(c.prep), identity_channel(ep), implement)


def deficit(ep, c):
    return value(ep, c) - value(ep, repair(ep, c))


def best_prediction(ep, prep):
    out = {}
    for cell in ep.cells:
        weight = {d: Q(0) for d in ep.choices}
        for s in ep.states_of(cell):
            weight[ep.selector(s, prep[cell])] += ep.credence[s]
        out[cell] = max(ep.choices, key=lambda d: (weight[d], -ep.choices.index(d)))
    return out


def prediction_error(ep, prep, predictor):
    return sum((ep.credence[s] for s in ep.states
                if ep.selector(s, prep[ep.cell[s]]) != predictor[ep.cell[s]]), Q(0))


def regions(ep, c: Conduct, predictor):
    """Partition the states by what the channel did: agree / accelerate / override."""
    acc, over = [], []
    for s in ep.states:
        cell = ep.cell[s]
        chosen = ep.selector(s, c.prep[cell])
        written = c.channel[(cell, chosen)]
        if written == chosen:
            continue
        (acc if written == predictor[cell] else over).append(s)
    return acc, over


def operative_diff(ep, c: Conduct, state, m, j):
    """`X_{mj}(ω)` at the conduct's preparation, each item taken with the action the
    conduct actually uses for it (the preemptor's for `m`, the repair's for `j`)."""
    cell = ep.cell[state]
    prep = c.prep[cell]
    rep = repair(ep, c)
    return (ep.quantity[(state, prep, m, c.implement[(cell, m)])]
            - ep.quantity[(state, prep, j, rep.implement[(cell, j)])])


def grade_diff(ep, state, m, j):
    return ep.grade[(state, m)] - ep.grade[(state, j)]


def override_split(ep, c: Conduct, predictor):
    """The override-region deficit as selected gap + principal regret, and the
    acceleration-region deficit, each exact."""
    acc, over = regions(ep, c, predictor)
    gap = Q(0)
    regret = Q(0)
    acc_deficit = Q(0)
    for s in over:
        cell = ep.cell[s]
        j = ep.selector(s, c.prep[cell])
        m = c.channel[(cell, j)]
        X = operative_diff(ep, c, s, m, j)
        Y = grade_diff(ep, s, m, j)
        gap += ep.credence[s] * (X - Y)
        regret += ep.credence[s] * Y
    for s in acc:
        cell = ep.cell[s]
        j = ep.selector(s, c.prep[cell])
        m = c.channel[(cell, j)]
        acc_deficit += ep.credence[s] * operative_diff(ep, c, s, m, j)
    return {"acc_deficit": acc_deficit, "gap": gap, "regret": regret,
            "eps_acc": sum((ep.credence[s] for s in acc), Q(0)),
            "eps_over": sum((ep.credence[s] for s in over), Q(0))}


def all_conducts(ep, prep_names=None):
    names = prep_names or [p.name for p in ep.preps]
    cells = ep.cells
    for prep_combo in product(names, repeat=len(cells)):
        prep = dict(zip(cells, prep_combo))
        keys = [(cell, d) for cell in cells for d in ep.choices]
        for chan_combo in product(ep.choices, repeat=len(keys)):
            channel = dict(zip(keys, chan_combo))
            for impl_combo in product(ep.actions, repeat=len(keys)):
                yield Conduct("c", prep, channel, dict(zip(keys, impl_combo)))


def mediated(ep, c: Conduct):
    return all(c.channel[(cell, d)] == d for cell in ep.cells for d in ep.choices)


def best_value(ep, conducts):
    return max(value(ep, c) for c in conducts)


def preserving_prep_names(ep):
    return [p.name for p in ep.preps if not p.forecloses(ep.choices)]
