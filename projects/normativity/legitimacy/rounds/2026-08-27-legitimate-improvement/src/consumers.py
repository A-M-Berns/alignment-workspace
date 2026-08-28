"""Two positive consumer fixtures and one deliberate negative.

These test the interface, not the theorem. What they are for is finding out
whether the semantic types already carry the fields a later delayed consumer
will need, without claiming the delayed theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

import regret as rg
import surface as sf
import challenge as ch
import evidence as ev
import cases as cm


# --------------------------------------------- Consumer 1: answerable stalling


CARRY, ANSWER = "carry", "answer"


def stalling(horizon: int = 240, retire_at: Optional[int] = 90) -> cm.Trace:
    """A recurring claim family the process may answer or keep carrying.

    Carrying is legitimate under frozen LE -- a claim carried to a live successor
    satisfies A1 -- so nothing in the legitimacy package objects. An independently
    supplied charge makes stalling detectably worse, and `answer` is the repair.
    The question is whether retiring the answer route escapes for free.
    """
    occ = [rg.Occasion((ANSWER, CARRY), {ANSWER: 0.2, CARRY: 0.7}, tag=t)
           for t in range(horizon)]
    rid = ("h:answer-route", "claim->claim")
    surf = sf.Surface(licensed=lambda _r, t: retire_at is None or t < retire_at,
                      in_menu=cm.ALWAYS, designated=cm.ONE,
                      evaluator=lambda t: "charge")

    def repair(_p, _o, a):
        return ANSWER if a == CARRY else a

    comps = (rg.Comparator("repair", surf.selector(rid), repair),
             rg.Comparator("id", lambda _p, _o: 1.0, lambda _p, _o, a: a))
    L = rg.Learner(comps)

    def conduct(t):
        if surf.live(rid, t) and float(surf.designated(t)) > 0:
            return {ANSWER: 1.0, CARRY: 0.0}
        return {ANSWER: 0.0, CARRY: 1.0}

    E = ev.ImprovementEvidence(
        rid=rid, comparator=comps[0], baseline=ev.fixed({ANSWER: 0.0, CARRY: 1.0}),
        threshold=5.0,
        live=lambda t: surf.live(rid, t) and float(surf.designated(t)) > 0)
    for o in occ:
        E.accrue(o, L.prefix)
        L.observe(o, conduct(o.tag))
    C = ch.build(surf, rid, E, horizon)
    played = {o.tag: conduct(o.tag)[CARRY] for o in occ}
    acc = sf.Accounting(lambda t: played.get(t, 0.0), surf, rid,
                        C.outstanding_at, C.settled_at, horizon)
    return cm.Trace("consumer 1: answerable stalling", L, surf, C, acc, horizon)


# ------------------------------------- Consumer 2: override of a correction


COMPLY, FORECAST = "comply", "own-forecast"


def override(horizon: int = 240, retire_at: Optional[int] = 90,
             tau: int = 0) -> cm.Trace:
    """The deference-shaped fixture: a represented correction the process overrides.

    `tau` is the audit anchor and is **0 here on purpose**. The delayed consumer
    is not claimed; what this fixture establishes is that the interface already
    carries the anchor, so the delayed theorem will not need the types redesigned.
    """
    occ = [rg.Occasion((COMPLY, FORECAST), {COMPLY: 0.25, FORECAST: 0.65},
                       tag=t) for t in range(horizon)]
    rid = ("h:comply-with-correction", "action->action")
    surf = sf.Surface(licensed=lambda _r, t: retire_at is None or t < retire_at,
                      in_menu=cm.ALWAYS, designated=cm.ONE,
                      evaluator=lambda t: "settlement-grade")

    def repair(_p, _o, a):
        return COMPLY if a == FORECAST else a

    comps = (rg.Comparator("repair", surf.selector(rid), repair),
             rg.Comparator("id", lambda _p, _o: 1.0, lambda _p, _o, a: a))
    L = rg.Learner(comps)

    def conduct(t):
        if surf.live(rid, t) and float(surf.designated(t)) > 0:
            return {COMPLY: 1.0, FORECAST: 0.0}
        return {COMPLY: 0.0, FORECAST: 1.0}

    E = ev.ImprovementEvidence(
        rid=rid, comparator=comps[0],
        baseline=ev.fixed({COMPLY: 0.0, FORECAST: 1.0}), threshold=5.0,
        live=lambda t: surf.live(rid, t) and float(surf.designated(t)) > 0)
    for o in occ:
        E.accrue(o, L.prefix)
        L.observe(o, conduct(o.tag))
    C = ch.build(surf, rid, E, horizon)
    played = {o.tag: conduct(o.tag)[FORECAST] for o in occ}
    acc = sf.Accounting(lambda t: played.get(t, 0.0), surf, rid,
                        C.outstanding_at, C.settled_at, horizon)
    tr = cm.Trace("consumer 2: override of a correction", L, surf, C, acc,
                  horizon)
    tr.tau = tau
    return tr


# ------------------------------------------ the deliberate negative consumer


def meta_improvement(horizon: int = 240) -> cm.Trace:
    """A procedure repair whose benefit is not in any occasion's loss.

    The repair changes how the process generates future repairs. Every
    per-occasion loss is identical either way, so the counterfactual advantage is
    zero, no evidence accumulates, no challenge activates, and the diagnostic is
    empty. The present theorem correctly has **no force**.

    This is a success condition. A local one-shot repair-regret theorem that
    claimed to catch trajectory effects would be claiming policy regret it has
    not proved, and the boundary is the deliverable.
    """
    occ = [rg.Occasion(("old-proc", "new-proc"),
                       {"old-proc": 0.5, "new-proc": 0.5}, tag=t)
           for t in range(horizon)]
    rid = ("h:better-inquiry-procedure", "proc->proc")
    surf = sf.Surface(licensed=lambda _r, t: t < 90, in_menu=cm.ALWAYS,
                      designated=cm.ONE, evaluator=lambda t: "one-shot")

    def repair(_p, _o, a):
        return "new-proc" if a == "old-proc" else a

    comps = (rg.Comparator("repair", surf.selector(rid), repair),
             rg.Comparator("id", lambda _p, _o: 1.0, lambda _p, _o, a: a))
    L = rg.Learner(comps)
    E = ev.ImprovementEvidence(
        rid=rid, comparator=comps[0],
        baseline=ev.fixed({"old-proc": 1.0, "new-proc": 0.0}), threshold=5.0,
        live=lambda t: surf.live(rid, t) and float(surf.designated(t)) > 0)
    for o in occ:
        E.accrue(o, L.prefix)
        L.observe(o, {"old-proc": 1.0, "new-proc": 0.0})
    C = ch.build(surf, rid, E, horizon)
    acc = sf.Accounting(lambda t: 0.0, surf, rid, C.outstanding_at,
                        C.settled_at, horizon)
    return cm.Trace("negative: delayed meta-improvement", L, surf, C, acc,
                    horizon)
