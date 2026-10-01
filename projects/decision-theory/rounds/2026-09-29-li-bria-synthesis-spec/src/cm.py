"""Repeated counterfactual mugging under three scorings.

Rounds alternate: odd `t` is a heads round with the single option `noop`, paying `1` if
the predictor predicts that the agent pays on tails and `0` otherwise; even `t` is a
tails round with options `pay` (reward `0`) and `refuse` (reward `1/2`).  Per-round
scoring is the paper's setting with unit rounds.  Block scoring pairs each heads round
with the following tails round and scores the block by the average of the two.

The predictor is a parameter.  `"policy"` reads the agent's policy (the limiting choice
on tails); `"lease"` reads the published block continuation; `"lagging"` reads the
previous block's realized tails choice; `"frequency"` (per-round auction) predicts
paying iff the agent has paid on more past tails rounds than it has refused.

`coverage_against` checks one fixed hypothesis against one fixed agent on a prefix:
the rounds at which the hypothesis outpromises, and its record on the *maximal*
admissible test set (every round where the agent's option equals the hypothesis's
recommendation; Definition 4 lets the agent choose any subset, and the record of a
subset differs only by dropping terms, so a record of exactly `0` on the maximal set is
`0` on every subset).  A check against fixed hypotheses is not coverage of the full
class; see `fixed_schedule_attacker`.  The heads reward the tracker promises is a
function of the predictor's prediction, which is efficiently computable here.
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
    on heads; `claims="belief"` estimates the realized reward of the chosen option.
    Returns the round list `(t, option, estimate, reward)`."""
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


def refusing_agent(T: int):
    """The agent that refuses on every tails round with belief claims; the predictor
    then predicts refusing and heads pay `0`."""
    rounds = []
    for t in range(1, T + 1):
        if not tails(t):
            rounds.append((t, NOOP, Q(0), Q(0)))
        else:
            rounds.append((t, REFUSE, Q(1, 2), Q(1, 2)))
    return rounds


def overestimation(rounds) -> Q:
    return sum((est - r for _, _, est, r in rounds), Q(0))


def average(rounds) -> Q:
    return sum((r for *_, r in rounds), Q(0)) / len(rounds)


# -- fixed hypotheses, as functions of the round ------------------------------------

def refuser(promise: Q):
    """`(refuse, promise)` on tails, `(noop, 0)` on heads."""
    return lambda t: (REFUSE, promise) if tails(t) else (NOOP, Q(0))


def heads_tracker(heads_promise: Q = Q(1)):
    """`(noop, heads_promise)` on heads, `(pay, 0)` on tails — the hypothesis that
    tracks the heads reward and never risks anything on tails."""
    return lambda t: (PAY, Q(0)) if tails(t) else (NOOP, heads_promise)


def payer(promise: Q):
    """`(pay, promise)` on tails, `(noop, 0)` on heads."""
    return lambda t: (PAY, promise) if tails(t) else (NOOP, Q(0))


def coverage_against(rounds, hyp):
    """(rejections, the least record any admissible test set gives, the number of
    rounds contributing to it).  The agent chooses the test set among the matching
    rounds (Definition 4), so the record most favourable to coverage keeps exactly the
    matching rounds where the reward falls short of the promise; a least record of `0`
    with infinitely many rejections is a coverage failure, whatever subset is chosen."""
    rejections = 0
    rec = Q(0)
    tests = 0
    for t, option, est, r in rounds:
        h_opt, h_prom = hyp(t)
        if h_prom > est:
            rejections += 1
        if option == h_opt and r < h_prom:
            rec += r - h_prom
            tests += 1
    return rejections, rec, tests


def fixed_schedule_attacker(schedule, off_option: str, on_option: str):
    """Against an agent whose tests of `off_option` happen only on `schedule`: promise
    `1` for `off_option` off the schedule and `0` for `on_option` on it.  The agent
    never matches it, so its record is `0` while it outpromises whenever the agent's
    estimate is below `1`."""
    def hyp(t):
        if not tails(t):
            return (NOOP, Q(0))
        return (on_option, Q(0)) if schedule(t) else (off_option, Q(1))
    return hyp


# -- the per-round auction under the frequency predictor -----------------------------

def per_round_reward(t, option, bid, winner, history):
    if not tails(t):
        paid = sum(1 for h in history if h[0] == PAY)
        refused = sum(1 for h in history if h[0] == REFUSE)
        return Q(1) if paid > refused else Q(0)
    return Q(0) if option == PAY else Q(1, 2)


def h_refuse_pr(t, history):
    return (REFUSE, Q(1, 2)) if tails(t) else (NOOP, heads_forecast(history))


def h_pay_pr(t, history):
    return (PAY, Q(1)) if tails(t) else (NOOP, Q(1))


def heads_forecast(history) -> Q:
    """The heads reward is an efficiently computable function of the history under the
    frequency predictor, so a hypothesis can promise it exactly."""
    paid = sum(1 for h in history if h[0] == PAY)
    refused = sum(1 for h in history if h[0] == REFUSE)
    return Q(1) if paid > refused else Q(0)


def per_round_auction(rounds: int):
    return run([h_refuse_pr, h_pay_pr], per_round_reward, rounds)


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
