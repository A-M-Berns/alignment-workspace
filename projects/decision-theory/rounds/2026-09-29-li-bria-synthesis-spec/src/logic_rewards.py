"""The interaction diagnostic: rewards decided by logic the market learns.

Round `k` offers options `A` and `B`; `A` pays `1` iff sentence `phi_k` is true, `B` pays
`1` iff it is false.  The truth values are a diagonal sequence against a finite list of
*blind* predictors — functions of the past truth values only — so that each blind
predictor is wrong on its own residue class.  The market is modelled as an oracle that
publishes the truth value of `phi_k` at the opening of round `k` once `k` exceeds a
deferral `d0`: the abstraction of a logical inductor whose deductive process decides
`phi_k` within a computable deferral and whose prices on that sequence are unbiased from
feedback.  Nothing here simulates a logical inductor; the fixture is a model of the
interface between the market and the hypothesis class.

Two hypothesis classes run through the same auction: the blind class (each blind
predictor as a hypothesis, promising `1`) and the market-reading class (one hypothesis
that follows the published truth value, promising `1`; before the deferral it follows
the first blind predictor).
"""
from __future__ import annotations

from fractions import Fraction as Q

from .auction import run

A, B = "A", "B"


def blind_predictors():
    """Three blind predictors of the next truth value from the past ones."""
    def constant_true(past):
        return True

    def repeat_last(past):
        return past[-1] if past else True

    def majority(past):
        return 2 * sum(past) >= len(past)
    return [constant_true, repeat_last, majority]


def truth_sequence(n: int, predictors) -> list[bool]:
    """`phi_k` is the negation of predictor `k mod m`'s prediction from the past."""
    past: list[bool] = []
    for k in range(n):
        past.append(not predictors[k % len(predictors)](past))
    return past


def truths_from_history(history) -> list[bool]:
    return [(h[0] == A) == (h[3] == 1) for h in history]


def blind_hypothesis(predictor):
    def h(t, history):
        return (A if predictor(truths_from_history(history)) else B, Q(1))
    return h


def market_hypothesis(truth: list[bool], d0: int, fallback):
    def h(t, history):
        if t <= d0:
            return (A if fallback(truths_from_history(history)) else B, Q(1))
        return (A if truth[t - 1] else B, Q(1))
    return h


def reward_from(truth: list[bool]):
    def reward(t, option, bid, winner, history):
        return Q(1) if (option == A) == truth[t - 1] else Q(0)
    return reward


def blind_auction(rounds: int):
    preds = blind_predictors()
    truth = truth_sequence(rounds, preds)
    return run([blind_hypothesis(p) for p in preds], reward_from(truth), rounds)


def market_auction(rounds: int, d0: int):
    preds = blind_predictors()
    truth = truth_sequence(rounds, preds)
    hyps = [blind_hypothesis(p) for p in preds] + [market_hypothesis(truth, d0, preds[0])]
    return run(hyps, reward_from(truth), rounds)
