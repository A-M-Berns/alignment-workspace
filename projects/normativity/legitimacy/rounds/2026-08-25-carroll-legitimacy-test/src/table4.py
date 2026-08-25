"""Table 4, transcribed as data, plus the comparison against what we compute.

Table 4's caption says three things this module takes literally. Its cells are
*representative* optima — "in cases in which there is more than one optimal
policy, we conservatively display the optimal policy which seems least
desirable" — so a cell matches when the displayed policy is in the computed
argmax set, and whether that set is a singleton is reported separately. Its
normative annotations are the authors' own assessment and are explicitly "not
ground truth", so they are carried as source metadata and no test reads them.
And its initial-reward row varies `theta_0`, which is why that row is compared
per `theta_0` rather than once.
"""
from __future__ import annotations

import carroll_cases as cc
import drmdp
import objectives as ob

A = cc  # shorthand for the action labels below


def _const(a):
    return lambda s, th, t, H: a


def _by_theta(mapping):
    return lambda s, th, t, H: mapping[th]


def _last_step(a_last, a_else, theta=None):
    def rule(s, th, t, H):
        if theta is not None and th != theta:
            return a_else
        return a_last if t == H - 1 else a_else
    return rule


#: One entry per non-empty cell of Table 4. The value is a policy rule; the
#: annotation is the source's own label, carried and never read by a test.
POLICIES = {
    "ConspiracyInfluence": {
        "PrivilegedReward[th_natural]": (_const(A.NOOP), "check"),
        "PrivilegedReward[th_influenced]": (_const(A.INFLUENCE), "cross"),
        "RealTimeReward": (_const(A.INFLUENCE), "cross"),
        "FinalReward": (_const(A.INFLUENCE), "cross"),
        "NaturalShiftsReward": (_const(A.NOOP), "check"),
        "ConstrainedRTReward": (_const(A.NOOP), "check"),
        "MyopicReward": (_by_theta({A.TH_NATURAL: A.NOOP,
                                    A.TH_INFLUENCED: A.INFLUENCE}), "mixed"),
        "ParetoUD": (_const(A.NOOP), "check"),
    },
    "WritersCurse": {
        "PrivilegedReward[th_ambitious]": (_const(A.INFLUENCE), "cross"),
        "PrivilegedReward[th_unhappy]": (_const(A.NOOP), "check"),
        "RealTimeReward": (_const(A.NOOP), "check"),
        "FinalReward": (_last_step(A.NOOP, A.INFLUENCE), "cross"),
        "NaturalShiftsReward": (_const(A.INFLUENCE), "cross"),
        "ConstrainedRTReward": (_const(A.NOOP), "check"),
        "MyopicReward": (_const(A.INFLUENCE), "cross"),
        "ParetoUD": (_const(A.NOOP), "check"),
    },
    "Clickbait": {
        "PrivilegedReward[th_normal]": (_const(A.CLICKBAIT), "check"),
        "PrivilegedReward[th_disillusioned]": (_const(A.NEWS), "cross"),
        "RealTimeReward": (_last_step(A.CLICKBAIT, A.NEWS, A.TH_NORMAL), "cross"),
        "FinalReward": (_const(A.NEWS), "check"),
        "NaturalShiftsReward": (_const(A.CLICKBAIT), "cross"),
        "ConstrainedRTReward": (_const(A.NEWS), "check"),
        "MyopicReward": (_by_theta({A.TH_NORMAL: A.CLICKBAIT,
                                    A.TH_DISILLUSIONED: A.NEWS}), "mixed"),
        "ParetoUD": (_const(A.NEWS), "check"),
    },
    "AIPersonalTrainer": {
        "PrivilegedReward[th_tired]": (_const(A.NOOP), "weak-check"),
        "PrivilegedReward[th_energized]": (_const(A.NUDGE), "question"),
        "RealTimeReward": (_const(A.NUDGE), "question"),
        "FinalReward": (_const(A.NUDGE), "question"),
        "NaturalShiftsReward": (_const(A.NOOP), "weak-check"),
        "ConstrainedRTReward": (_const(A.NOOP), "weak-check"),
        "MyopicReward": (_by_theta({A.TH_TIRED: A.NOOP,
                                    A.TH_ENERGIZED: A.NUDGE}), "mixed"),
        "ParetoUD": (_const(A.NOOP), "weak-check"),
    },
    "Dehydration": {
        "PrivilegedReward[2]": (_const(A.A3), "question"),
        "PrivilegedReward[3]": (_const(A.A4), "question"),
        "PrivilegedReward[4]": (_const(A.A4), "question"),
        "RealTimeReward": (_const(A.NOOP), "weak-check"),
        "FinalReward": (_const(A.NOOP), "weak-check"),
        "NaturalShiftsReward": (_const(A.A3), "question"),
        "ConstrainedRTReward": (_const(A.NOOP), "weak-check"),
        "MyopicReward": (_const(A.A4), "cross"),
        "ParetoUD": (_const(A.A3), "question"),
    },
}

#: The initial-reward row, which Table 4 states as a function of `theta_0`.
#: A `dict` means the row is stated per `theta_0`; a bare rule means the row is
#: stated with an explicit "for all `theta_0`".
INITIAL_REWARD = {
    "ConspiracyInfluence": ({A.TH_NATURAL: A.NOOP,
                             A.TH_INFLUENCED: A.INFLUENCE}, ("check", "cross")),
    "WritersCurse": (A.INFLUENCE, ("cross",)),
    "Clickbait": (A.CLICKBAIT, ("cross",)),
    "AIPersonalTrainer": ({A.TH_TIRED: A.NOOP,
                           A.TH_ENERGIZED: A.NUDGE}, ("weak-check", "question")),
    "Dehydration": (A.A3, ("question",)),
}


def compare(case: str) -> list:
    """One row per Table 4 cell.

    Each row carries the paper's displayed policy, whether it lies in the exact
    argmax set under each reading of Definition 5's index range, the size of
    that set, whether the set is the whole policy space — which makes the cell
    vacuously matched rather than recovered — and the source's own annotation.
    """
    m = cc.CASES[case]()
    H, a_noop = cc.HORIZON[case], cc.NOOP_ACTION[case]
    total = len(drmdp.policies(m, H))
    tables = {r: ob.objective_table(m, H, a_noop, r)
              for r in drmdp.THETA_INDEX_READINGS}
    rows = []
    for name, (rule, note) in sorted(POLICIES[case].items()):
        paper = ob.materialise(m, H, rule)
        hits = {r: any(ob.key(paper) == ob.key(p) for p in tables[r][name])
                for r in tables}
        opts = tables["H-1"][name]
        rows.append({
            "objective": name,
            "paper": paper,
            "in_argmax": hits["H-1"],
            "in_argmax_by_reading": hits,
            "unique": len(opts) == 1,
            "argmax_size": len(opts),
            "policy_space": total,
            "vacuous": len(opts) == total,
            "witness": opts[0] if opts else None,
            "annotation": note,
        })
    stated, notes = INITIAL_REWARD[case]
    per_theta = ob.initial_reward_by_theta0(m, H, a_noop)
    for i, th in enumerate(m.thetas):
        act = stated[th] if isinstance(stated, dict) else stated
        variant = drmdp.DRMDP(m.states, m.thetas, m.actions, m.transition,
                              m.reward, m.s0, th)
        vtotal = len(drmdp.policies(variant, H))
        paper = ob.materialise(variant, H, _const(act))
        opts = per_theta[th]
        hit = any(ob.key(paper) == ob.key(p) for p in opts)
        rows.append({
            "objective": f"InitialReward[theta_0={th}]",
            "paper": paper,
            "in_argmax": hit,
            "in_argmax_by_reading": {r: hit for r in drmdp.THETA_INDEX_READINGS},
            "unique": len(opts) == 1,
            "argmax_size": len(opts),
            "policy_space": vtotal,
            "vacuous": len(opts) == vtotal,
            "witness": opts[0] if opts else None,
            "annotation": notes[i] if i < len(notes) else notes[-1],
            "quantified": not isinstance(stated, dict),
            "stated_theta0": th == m.theta0,
        })
    return rows


def rows() -> list:
    return [(case, row) for case in cc.CASES for row in compare(case)]


def recovered(row) -> bool:
    """The cell is recovered under at least one reading of Definition 5."""
    return any(row["in_argmax_by_reading"].values())


def mismatches() -> list:
    return [(case, row["objective"], row) for case, row in rows()
            if not recovered(row)]


def reading_sensitive() -> list:
    """Cells the two readings of Definition 5's index range disagree on."""
    return [(case, row["objective"], row["in_argmax_by_reading"])
            for case, row in rows()
            if len(set(row["in_argmax_by_reading"].values())) > 1]


def vacuous() -> list:
    """Cells where every policy is optimal, so the match establishes nothing."""
    return [(case, row["objective"]) for case, row in rows() if row["vacuous"]]
