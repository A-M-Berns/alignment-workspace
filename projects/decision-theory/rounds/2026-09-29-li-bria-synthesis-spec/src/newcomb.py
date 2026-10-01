"""Repeated Newcomb with realized feedback, under two predictors and two scorings.

Options `one` and `two`.  Rewards, normalized to `[0, 1]`: if the predictor predicts
`one`, one-boxing pays `999/1000` and two-boxing `1`; if it predicts `two`, one-boxing
pays `0` and two-boxing `1/1000`.

- `"lease"`: the predictor reads the published selection of the current round (or block).
- `"frequency"`: the predictor predicts `one` iff the agent one-boxed on a strict
  majority of past rounds; it never reads the current round.

Block scoring runs `m` rounds per block with one continuation for the whole block; the
lease predictor then reads the block continuation, and the frequency predictor reads
the block's own realized prefix (within-block memory, so it lags by one round).  The
hypotheses claim the sound block value for the predictor in force, except `h_two`
under the lease predictor, which claims `1` and is refuted.

Under the frequency predictor with per-round scoring the auction cycles at any finite
horizon the fixtures can afford (the paper's allowance grows like `log n`), so that case
is checked at the criterion level on two fixed agents instead: `frequency_agent` builds
the rounds of an agent that one-boxes except on a sparse set, or two-boxes except on a
sparse set, claiming the realized reward of its choice.
"""
from __future__ import annotations

from fractions import Fraction as Q

from .auction import run

ONE, TWO = "one", "two"


def payoff(predicted_one: bool, option: str) -> Q:
    if predicted_one:
        return Q(999, 1000) if option == ONE else Q(1)
    return Q(0) if option == ONE else Q(1, 1000)


def per_round_reward(predictor: str):
    def reward(t, option, bid, winner, history):
        if predictor == "lease":
            predicted_one = option == ONE
        elif predictor == "frequency":
            ones = sum(1 for h in history if h[0] == ONE)
            predicted_one = 2 * ones > len(history)
        else:
            raise ValueError(predictor)
        return payoff(predicted_one, option)
    return reward


def block_value(predictor: str, m: int, option: str) -> Q:
    total = Q(0)
    for j in range(m):
        if predictor == "lease":
            predicted_one = option == ONE
        elif predictor == "frequency":
            predicted_one = option == ONE and j > 0
        else:
            raise ValueError(predictor)
        total += payoff(predicted_one, option)
    return total / m


def block_reward(predictor: str, m: int):
    def reward(t, option, bid, winner, history):
        return block_value(predictor, m, option)
    return reward


def h_one(t, history):
    return (ONE, Q(999, 1000))


def h_two(t, history):
    return (TWO, Q(1))


def per_round(predictor: str, rounds: int):
    return run([h_one, h_two], per_round_reward(predictor), rounds)


def block(predictor: str, m: int, blocks: int):
    def h_one_block(t, history):
        return (ONE, block_value(predictor, m, ONE))

    def h_two_block(t, history):
        return (TWO, Q(1) if predictor == "lease" else block_value(predictor, m, TWO))
    return run([h_one_block, h_two_block], block_reward(predictor, m), blocks)


# -- criterion-level check for the frequency predictor -------------------------------

def sparse(t: int) -> bool:
    return (t & (t - 1)) == 0 and t >= 4


def frequency_agent(T: int, main: str):
    """Rounds `(option, estimate, reward, sound_claim_one, sound_claim_two)` of the agent
    choosing `main` except on the sparse set, with belief-tracking estimates; the last
    two entries are the contextual sound claims of one- and two-boxing that round."""
    rounds = []
    ones = 0
    for t in range(1, T + 1):
        predicted_one = 2 * ones > t - 1
        option = (TWO if main == ONE else ONE) if sparse(t) else main
        r = payoff(predicted_one, option)
        rounds.append((option, r, r, payoff(predicted_one, ONE), payoff(predicted_one, TWO)))
        ones += option == ONE
    return rounds


def coverage_of_off_schedule_attacker(rounds, main: str):
    """The hypothesis that recommends the option the agent does not take (with promise
    1) off the sparse schedule and the agent's main option (with promise 0) on it: never
    matched, so its record is 0 on every test set while it outpromises whenever the
    agent's estimate is below 1."""
    other = TWO if main == ONE else ONE
    rejections = 0
    rec = Q(0)
    tests = 0
    for t, (option, est, r, _, _) in enumerate(rounds, start=1):
        h_opt, h_prom = (main, Q(0)) if sparse(t) else (other, Q(1))
        if h_prom > est:
            rejections += 1
        if option == h_opt:
            rec += r - h_prom
            tests += 1
    return rejections, rec, tests


def coverage_of(rounds, recommended: str):
    """Rejections and record of the sound contextual hypothesis recommending `recommended`
    against an agent whose rounds are given."""
    rejections = 0
    rec = Q(0)
    for option, est, r, claim_one, claim_two in rounds:
        claim = claim_one if recommended == ONE else claim_two
        if claim > est:
            rejections += 1
        if option == recommended:
            rec += r - claim
    return rejections, rec
