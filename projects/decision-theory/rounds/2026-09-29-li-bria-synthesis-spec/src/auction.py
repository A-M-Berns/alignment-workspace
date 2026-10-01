"""The first-price sealed-bid BRIA auction (Oesterheld, Demski and Conitzer, TARK 2023,
Theorem 1), with unit rounds and exact arithmetic.

A hypothesis is a callable `h(t, history) -> (option, promise)`; `history` is the list of
past rounds, each `(option, bid, promise, reward, winner_index)`.  The environment is a
callable `reward(t, option, bid, winner_index, history) -> Fraction`; letting it read
the published estimate (the bid) and the winning index is what the troll fixtures need,
and the paper's setting (reward a function of the option and the history only) is the
case where it ignores them.

Allowance `A(n, i) = 1/(n i^2)` for `i < n`, credited after the round (settlement timing,
as in the paper).  Ties go to the lowest index.  `bid_rule="capped"` is the paper's bid
`min(promise, wealth)`; `bid_rule="full"` is the variant in which a hypothesis bids its
promise once its wealth covers it and nothing before — a construction the spec's troll
family discriminates, not the paper's.
"""
from __future__ import annotations

from fractions import Fraction as Q


def allowance(n: int, i: int) -> Q:
    return Q(1, n * i * i) if i < n else Q(0)


def run(hypotheses, reward, rounds: int, bid_rule: str = "capped"):
    """Run the auction for `rounds` rounds; return the history and the final wealths."""
    wealth = [Q(0) for _ in hypotheses]
    history = []
    for t in range(1, rounds + 1):
        proposals = [h(t, history) for h in hypotheses]
        if bid_rule == "capped":
            bids = [min(p[1], wealth[i]) for i, p in enumerate(proposals)]
        elif bid_rule == "full":
            bids = [p[1] if wealth[i] >= p[1] else Q(0) for i, p in enumerate(proposals)]
        else:
            raise ValueError(bid_rule)
        best = max(bids)
        winner = bids.index(best)
        option, promise = proposals[winner]
        r = reward(t, option, best, winner, history)
        assert Q(0) <= r <= Q(1)
        for i in range(len(hypotheses)):
            wealth[i] += allowance(t, i + 1)
        wealth[winner] += r - best
        history.append((option, best, promise, r, winner))
    return history, wealth


def average_reward(history, start: int = 0) -> Q:
    part = history[start:]
    return sum((h[3] for h in part), Q(0)) / len(part)


def cumulative_overestimation(history) -> Q:
    """`L_T = sum_t (estimate_t - r_t)` (Definition 1), the estimate being the bid."""
    return sum((h[1] - h[3] for h in history), Q(0))


def record(history, hypothesis: int) -> Q:
    """`l_T = sum_{t in M, t <= T} (r_t - h^e_t)` on the rounds `hypothesis` won
    (Definition 5 with the auction's test set); the promise, not the bid, is charged."""
    return sum((h[3] - h[2] for h in history if h[4] == hypothesis), Q(0))


def total_allowance(rounds: int, n_hypotheses: int) -> Q:
    """The paper's bound on `L_T`: the allowance credited through round `T`."""
    return sum((allowance(n, i + 1) for n in range(1, rounds + 1)
                for i in range(n_hypotheses)), Q(0))


def wins(history, hypothesis: int) -> int:
    return sum(1 for h in history if h[4] == hypothesis)
