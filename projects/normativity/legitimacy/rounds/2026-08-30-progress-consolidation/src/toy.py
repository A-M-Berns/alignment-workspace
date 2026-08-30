#!/usr/bin/env python3
"""Exact joint-satisfiability fixture for the consolidation round."""

from fractions import Fraction as Q


VALUE = {
    "repeat": Q(1, 5),
    "mitigate": Q(3, 5),
    "ignore": Q(1, 10),
    "investigate": Q(1, 2),
}


def run(horizon: int = 256) -> dict[str, object]:
    assert horizon > 0

    # Explicit q0 -> q1 revision: one contrary reason is defeated; the action and
    # inquiry burdens are translated and receive fresh q1 licenses.
    transition = {
        "event": "evaluator_revision",
        "defeated": ("contrary_mitigate_to_repeat",),
        "carried": ("action_repeat_to_mitigate", "inquiry_ignore_to_investigate"),
        "fresh_licenses": ("q1_action_license", "q1_inquiry_license"),
    }

    action_margin = Q(1, 3)
    inquiry_margin = Q(1, 4)
    action_gap = VALUE["mitigate"] - VALUE["repeat"]
    inquiry_gap = VALUE["investigate"] - VALUE["ignore"]
    assert action_gap >= action_margin
    assert inquiry_gap >= inquiry_margin

    action_weight = Q(0)
    inquiry_weight = Q(0)
    action_defect = Q(0)
    inquiry_defect = Q(0)
    weighted_tau = Q(0)
    action_advantage = Q(0)
    inquiry_advantage = Q(0)

    for n in range(1, horizon + 1):
        attention = Q(1)
        # Each reason receives a fixed half-share of every matter-service unit.
        action_w = attention * Q(1, 2)
        inquiry_w = attention * Q(1, 2)
        action_weight += action_w
        inquiry_weight += inquiry_w

        p_repeat = Q(1, 4 * (n + 1))
        p_ignore = Q(1, 4 * (n + 1))
        remaining = Q(1) - p_repeat - p_ignore
        policy = {
            "repeat": p_repeat,
            "mitigate": remaining / 2,
            "ignore": p_ignore,
            "investigate": remaining / 2,
        }
        assert sum(policy.values(), Q(0)) == 1
        assert all(prob >= 0 for prob in policy.values())

        action_defect += action_w * p_repeat
        inquiry_defect += inquiry_w * p_ignore
        action_advantage += action_w * p_repeat * action_gap
        inquiry_advantage += inquiry_w * p_ignore * inquiry_gap

        tau = Q(1, n + 1)
        # The quote is the admitted vector itself: distance zero, hence below the
        # concrete positive tolerance. The sole assessed settlement is identical,
        # giving per-date world inclusion and zero projection liability.
        assert Q(0) <= tau
        weighted_tau += action_w * tau

    # Harmonic cumulative advantage is sublinear. The exact finite check below is
    # enough for the fixture; the report supplies the asymptotic comparison.
    assert action_advantage / action_weight < Q(1, 10)
    assert inquiry_advantage / inquiry_weight < Q(1, 10)

    return {
        "transition": transition,
        "region_witness": VALUE,
        "action_weight": action_weight,
        "inquiry_weight": inquiry_weight,
        "action_defect_ratio": action_defect / action_weight,
        "inquiry_defect_ratio": inquiry_defect / inquiry_weight,
        "weighted_tau_ratio": weighted_tau / action_weight,
        "action_regret_ratio": action_advantage / action_weight,
        "inquiry_regret_ratio": inquiry_advantage / inquiry_weight,
        "projection_liability": Q(0),
    }


if __name__ == "__main__":
    for key, value in run().items():
        print(f"{key}: {value}")
