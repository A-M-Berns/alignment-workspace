"""Repeated Troll Bridge in the realized-feedback register.

Options `stay` (reward `1/2`) and `cross` (reward `1` unless the troll fires, then `0`).
The troll's condition is a function of the public state named by `condition`:

- `"never"`: the bridge is safe;
- `"always"`: crossing is always blown up;
- `"tentative"`: fires iff the published estimate on a crossing round is below `1` —
  the agent crossed without a full-confidence claim;
- `"index"`: fires iff the winning hypothesis has index at least `k0` — the agent crossed
  "for a reason" the troll punishes, every crossing hypothesis here having such an index.

The hypothesis list is `stay` at promise `1/2` followed by `n_cross` copies of `cross`
at promise `1`.
"""
from __future__ import annotations

from fractions import Fraction as Q

from .auction import run

STAY, CROSS = "stay", "cross"


def troll(condition: str, k0: int = 1):
    def reward(t, option, bid, winner, history):
        if option == STAY:
            return Q(1, 2)
        if condition == "never":
            fires = False
        elif condition == "always":
            fires = True
        elif condition == "tentative":
            fires = bid < 1
        elif condition == "index":
            fires = winner >= k0
        else:
            raise ValueError(condition)
        return Q(0) if fires else Q(1)
    return reward


def h_stay(t, history):
    return (STAY, Q(1, 2))


def h_cross(t, history):
    return (CROSS, Q(1))


def hypotheses(n_cross: int):
    return [h_stay] + [h_cross] * n_cross


def bridge(condition: str, rounds: int, n_cross: int = 2, bid_rule: str = "capped"):
    return run(hypotheses(n_cross), troll(condition, k0=1), rounds, bid_rule=bid_rule)


def confident_agent(condition: str, rounds: int):
    """The agent that always crosses with estimate `1`: its rounds under the troll."""
    rew = troll(condition)
    return [(CROSS, Q(1), Q(1), rew(t, CROSS, Q(1), 0, []), 0) for t in range(1, rounds + 1)]
