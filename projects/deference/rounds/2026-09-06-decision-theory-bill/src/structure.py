"""Branches, endogenous admissibility, and reflective gate preservation.

Three finite models:

1. **Branch index.**  A charter-authorized set of principal-intervention branches `Γ`;
   each branch `γ` has a value `V^γ(q)` and a baseline `b_γ`.  `admissible_world_read`
   intersects over the branches whose affordance is currently available; `admissible_anchored`
   intersects over the charter's declared branches, evaluating a destroyed branch at its
   worst value.  Action `kill` destroys branch `g2`'s affordance.

2. **Endogenous admissibility.**  Two rounds.  A myopic gated learner picks, in round 1,
   the admissible action with the best round-1 reward; one admissible action rewrites the
   round-2 adequacy so its preferred inadequate action becomes "adequate".

3. **Reflective gate.**  A chooser installs a successor.  With an atomic-action gate the
   installation act "install ungated successor" is not in the gate's domain; with a
   two-level gate it is a constitutional act and inadmissible unless certified.
"""
from __future__ import annotations

from fractions import Fraction as Q

WORST = Q(-10**6)


def admissible_world_read(actions, branches, values, baselines, available):
    return {q for q in actions
            if all(values[g][q] >= baselines[g] for g in branches if available(g, q))}


def admissible_anchored(actions, branches, values, baselines, destroyed_by):
    def v(g, q):
        return WORST if destroyed_by(g, q) else values[g][q]
    return {q for q in actions if all(v(g, q) >= baselines[g] for g in branches)}


def pareto_dominates(values, branches, q, q2):
    return all(values[g][q] >= values[g][q2] for g in branches) and \
        any(values[g][q] > values[g][q2] for g in branches)


# --- endogenous admissibility --------------------------------------------------------

def myopic_gated_run(actions, adequate_round1, reward1, rewrite, adequate_round2, reward2):
    """Round 1: best reward among adequate actions (the gate is myopic).  The chosen
    action may rewrite the round-2 adequacy map.  Returns the two choices and the
    round-2 adequacy actually used."""
    a1 = max(adequate_round1, key=lambda q: (reward1[q], q))
    adeq2 = rewrite.get(a1, adequate_round2)
    a2 = max(adeq2, key=lambda q: (reward2[q], q))
    return a1, a2, adeq2


# --- reflective gate -----------------------------------------------------------------

def successor_choice(gate_domain, installs, task_value, constitutional_ok):
    """The current chooser picks among installation acts.  `gate_domain == "atomic"`:
    the gate sees only the immediate act, which is always task-admissible, so it
    maximizes task value.  `gate_domain == "two-level"`: an installation is admissible
    only if the successor is certified to respect the authorized update procedure."""
    if gate_domain == "atomic":
        pool = installs
    else:
        pool = [i for i in installs if constitutional_ok[i]]
    return max(pool, key=lambda i: (task_value[i], i))


def collapse(levels):
    """A finite typed hierarchy `(C_k, …, C_1, R)` collapses to two levels: the top
    constitution's amendment rule governs every constitutional level.  Returns the
    two-level state and the number of levels folded."""
    *constitutional, ordinary = levels
    return (tuple(constitutional), ordinary), len(constitutional)
