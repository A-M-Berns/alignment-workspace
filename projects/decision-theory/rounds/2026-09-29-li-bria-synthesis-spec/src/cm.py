"""Repeated counterfactual mugging under three scorings.

Rounds alternate: odd `t` is a heads round with the single option `noop`, paying `1` if
the predictor predicts that the agent pays on tails and `0` otherwise; even `t` is a
tails round with options `pay` (reward `0`) and `refuse` (reward `1/2`).  Per-round
scoring is the paper's setting with unit rounds.  Block scoring pairs each heads round
with the following tails round and scores the block by the average of the two.

The predictor is a parameter.  `"policy"` reads the agent's policy (the limiting choice
on tails); `"lease"` reads the published block continuation; `"lagging"` reads the
previous block's realized tails choice.
"""
from __future__ import annotations

from fractions import Fraction as Q

from .auction import run

PAY, REFUSE, NOOP = "pay", "refuse", "noop"


def tails(t: int) -> bool:
    return t % 2 == 0


def sparse(t: int) -> bool:
    """A density-zero set of tails rounds: `t = 2^j`, `j >= 2`."""
    return tails(t) and (t & (t - 1)) == 0 and t >= 4


def per_round_agent(T: int, claims: str, predictor_predicts_pay: bool = True):
    """The paying agent with per-round scoring: pays on every tails round except the
    sparse set, where it refuses.  `claims="subsidy"` estimates `1/2` on tails and `0`
    on heads; `claims="belief"` estimates the realized reward of the chosen option, the
    limit of a market unbiased on the tails subsequence.  Returns the round list
    `(t, option, estimate, reward)`."""
    rounds = []
    for t in range(1, T + 1):
        if not tails(t):
            r = Q(1) if predictor_predicts_pay else Q(0)
            est = Q(0) if claims == "subsidy" else r
            rounds.append((t, NOOP, est, r))
            continue
        option = REFUSE if sparse(t) else PAY
        r = Q(1, 2) if option == REFUSE else Q(0)
        est = Q(1, 2) if claims == "subsidy" else r
        rounds.append((t, option, est, r))
    return rounds


def overestimation(rounds) -> Q:
    return sum((est - r for _, _, est, r in rounds), Q(0))


def rejections_and_record(rounds, promise: Q):
    """For the hypothesis `(refuse on tails, promise)` and `(noop, 0)` on heads: the
    number of rounds at which it outpromises the agent, and its record on the rounds the
    agent refused (its test set)."""
    rejections = 0
    rec = Q(0)
    for _, option, est, r in rounds:
        if option == NOOP:
            continue
        if promise > est:
            rejections += 1
        if option == REFUSE:
            rec += r - promise
    return rejections, rec


def average(rounds) -> Q:
    return sum((r for *_, r in rounds), Q(0)) / len(rounds)


# -- block scoring through the auction ---------------------------------------------

def block_reward(predictor: str):
    """Block score of a continuation, with the predictor named."""
    def reward(t, option, bid, winner, history):
        if predictor == "lease":
            heads = Q(1) if option == PAY else Q(0)
        elif predictor == "lagging":
            prev = history[-1][0] if history else REFUSE
            heads = Q(1) if prev == PAY else Q(0)
        else:
            raise ValueError(predictor)
        tails_r = Q(0) if option == PAY else Q(1, 2)
        return (heads + tails_r) / 2
    return reward


def h_pay(t, history):
    return (PAY, Q(1, 2))


def h_refuse(t, history):
    return (REFUSE, Q(1, 4))


def h_refuse_lagging(t, history):
    """Under the lagging predictor, refusing after a paying block scores `3/4`; the
    hypothesis claims contextually."""
    prev = history[-1][0] if history else REFUSE
    return (REFUSE, Q(3, 4) if prev == PAY else Q(1, 4))


def block_auction(predictor: str, blocks: int):
    hyps = [h_pay, h_refuse if predictor == "lease" else h_refuse_lagging]
    return run(hyps, block_reward(predictor), blocks)
