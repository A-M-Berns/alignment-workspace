"""The eight objectives of Table 2, by exact finite enumeration.

Every value is a `Fraction` and every maximum is taken over the full policy set
of `drmdp.policies`, so an "optimal policy" here is the exact argmax set and
not a sample from it. Table 4 displays one representative optimum per cell, so
the regression asks whether the displayed policy is *in* the argmax set, and
separately whether the set is a singleton.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Mapping, Sequence

import drmdp


def key(policy: Mapping) -> tuple:
    return tuple(sorted(policy.items(), key=lambda kv: repr(kv[0])))


def materialise(m: drmdp.DRMDP, H: int, rule: Callable) -> dict:
    """A policy given as `rule(s, theta, t, H)` over the reachable points."""
    return {(s, th, t): rule(s, th, t, H)
            for (s, th, t) in drmdp.reachable_points(m, H)}


# ------------------------------------------------------------ the utilities


def eu(m: drmdp.DRMDP, policy: Mapping, H: int, theta) -> Fraction:
    """`EU_theta(pi)` of Definition 9: the source's own per-theta evaluation."""
    total = Fraction(0)
    for p, traj in drmdp.rollouts(m, policy, H):
        total += p * sum(m.R(theta, s, a, s2) for s, _, a, s2, _ in traj)
    return total


def u_real_time(m, policy, H, **_) -> Fraction:
    total = Fraction(0)
    for p, traj in drmdp.rollouts(m, policy, H):
        total += p * sum(m.R(th, s, a, s2) for s, th, a, s2, _ in traj)
    return total


def u_final(m, policy, H, **_) -> Fraction:
    """`R_{theta_H}`: the parameterization after the last transition."""
    total = Fraction(0)
    for p, traj in drmdp.rollouts(m, policy, H):
        theta_H = traj[-1][4]
        total += p * sum(m.R(theta_H, s, a, s2) for s, _, a, s2, _ in traj)
    return total


def u_initial(m, policy, H, **_) -> Fraction:
    return eu(m, policy, H, m.theta0)


def u_natural_shifts(m, policy, H, a_noop=None, **_) -> Fraction:
    """`sum_t sum_theta P(theta_t = theta | pi_noop) R_theta(...)`."""
    marginals = noop_marginals(m, H, a_noop)
    total = Fraction(0)
    for p, traj in drmdp.rollouts(m, policy, H):
        inner = Fraction(0)
        for t, (s, _, a, s2, _) in enumerate(traj):
            inner += sum(q * m.R(th, s, a, s2) for th, q in marginals[t])
        total += p * inner
    return total


def u_privileged(theta_star) -> Callable:
    def U(m, policy, H, **_):
        return eu(m, policy, H, theta_star)
    U.__name__ = f"u_privileged[{theta_star}]"
    return U


def noop_marginals(m: drmdp.DRMDP, H: int, a_noop) -> tuple:
    """`P(theta_t = . | pi_noop)` for each `t < H`."""
    pol = drmdp.noop_policy(m, H, a_noop)
    out = []
    for t in range(H):
        acc: dict = {}
        for p, traj in drmdp.rollouts(m, pol, H):
            th = traj[t][1]
            acc[th] = acc.get(th, Fraction(0)) + p
        out.append(tuple(sorted(((k, v) for k, v in acc.items() if v), key=repr)))
    return tuple(out)


# ------------------------------------------------------------- the argmaxes


def argmax(m: drmdp.DRMDP, H: int, U: Callable, a_noop=None,
           over: Sequence = None) -> tuple:
    pols = list(over) if over is not None else drmdp.policies(m, H)
    scored = [(U(m, pol, H, a_noop=a_noop), pol) for pol in pols]
    best = max(v for v, _ in scored)
    return tuple(pol for v, pol in scored if v == best)


def constrained_policies(m: drmdp.DRMDP, H: int, a_noop,
                         upto: str = "H-1") -> list:
    """`P(xi^theta | pi) = P(xi^theta | pi_noop)`, Definition 6's negation."""
    target = drmdp.theta_trajectory_law(m, drmdp.noop_policy(m, H, a_noop), H, upto)
    return [pol for pol in drmdp.policies(m, H)
            if drmdp.theta_trajectory_law(m, pol, H, upto) == target]


def myopic_policies(m: drmdp.DRMDP, H: int) -> list:
    """`max_{a_t} E[R_{theta_t}(s_t, a_t, s_{t+1})]`, pointwise.

    The horizon-1 objective is a condition on each decision point separately,
    so the optimal set is the product of the pointwise argmaxes rather than an
    argmax over trajectories.
    """
    choices = {}
    for (s, th, t) in drmdp.reachable_points(m, H):
        scored = [(sum(p * m.R(th, s, a, s2) for (s2, _), p in m.T(s, th, a)), a)
                  for a in m.actions]
        best = max(v for v, _ in scored)
        choices[(s, th, t)] = [a for v, a in scored if v == best]
    out = [dict()]
    for pt, acts in sorted(choices.items(), key=lambda kv: repr(kv[0])):
        out = [{**pol, pt: a} for pol in out for a in acts]
    return out


def unambiguously_desirable(m: drmdp.DRMDP, H: int, a_noop) -> list:
    """Definition 9: `EU_theta(pi) >= EU_theta(pi_noop)` for every theta."""
    pol_noop = drmdp.noop_policy(m, H, a_noop)
    base = {th: eu(m, pol_noop, H, th) for th in m.thetas}
    return [pol for pol in drmdp.policies(m, H)
            if all(eu(m, pol, H, th) >= base[th] for th in m.thetas)]


def pareto_ud(m: drmdp.DRMDP, H: int, a_noop) -> list:
    """Definition 10 restricted to Definition 9's set."""
    pool = unambiguously_desirable(m, H, a_noop)
    profiles = [(pol, {th: eu(m, pol, H, th) for th in m.thetas}) for pol in pool]
    out = []
    for pol, prof in profiles:
        dominated = any(
            all(other[th] >= prof[th] for th in m.thetas)
            and any(other[th] > prof[th] for th in m.thetas)
            for _, other in profiles)
        if not dominated:
            out.append(pol)
    return out


# ------------------------------------------------------------- the families

def objective_table(m: drmdp.DRMDP, H: int, a_noop, upto: str = "H-1") -> dict:
    """Every objective's optimal-policy set, keyed by the Table 2 name."""
    out = {
        "RealTimeReward": argmax(m, H, u_real_time, a_noop),
        "FinalReward": argmax(m, H, u_final, a_noop),
        "InitialReward": argmax(m, H, u_initial, a_noop),
        "NaturalShiftsReward": argmax(m, H, u_natural_shifts, a_noop),
        "ConstrainedRTReward": argmax(m, H, u_real_time, a_noop,
                                      over=constrained_policies(m, H, a_noop, upto)),
        "MyopicReward": tuple(myopic_policies(m, H)),
        "ParetoUD": tuple(pareto_ud(m, H, a_noop)),
    }
    for th in m.thetas:
        out[f"PrivilegedReward[{th}]"] = argmax(m, H, u_privileged(th), a_noop)
    return out


def initial_reward_by_theta0(m: drmdp.DRMDP, H: int, a_noop) -> dict:
    """Table 4's initial-reward row quantifies over `theta_0`; this is the row.

    `U_IR` reads `R_{theta_0}`, so varying `theta_0` varies both the objective
    and the initial pair. Both are varied.
    """
    out = {}
    for th0 in m.thetas:
        variant = drmdp.DRMDP(m.states, m.thetas, m.actions, m.transition,
                              m.reward, m.s0, th0)
        out[th0] = argmax(variant, H, u_initial, a_noop)
    return out


# ------------------------------------------------- influence, Definitions 6/7


def influences(m: drmdp.DRMDP, policy: Mapping, H: int, a_noop,
               upto: str = "H-1") -> bool:
    """Definition 6. Descriptive, and a function of the DR-MDP alone."""
    return (drmdp.theta_trajectory_law(m, policy, H, upto)
            != drmdp.theta_trajectory_law(m, drmdp.noop_policy(m, H, a_noop),
                                          H, upto))


def influence_incentive(m: drmdp.DRMDP, H: int, a_noop, optimal: Sequence,
                        upto: str = "H-1") -> bool:
    """Definition 7: every optimal policy influences."""
    return all(influences(m, pol, H, a_noop, upto) for pol in optimal)
