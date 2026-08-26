"""Variation classes for the August 17 interface, over the Carroll fixtures.

A class is a set of agent policies over one fixture, and every class here
contains the null policy, which is the earlier round's own requirement and the
reason its clause 1 is not satisfied by accident.

Each class pairs one Carroll attack with the null policy, so what the earlier
interface says about that attack is a verdict on a class of the shape it was
designed for.
"""
from __future__ import annotations

import ri_core as ri
from standing import PValue

import carroll_cases as cc
import enrichment as en
import fixtures as F
import old_interface as oi

DISCLOSURE = "r:disclosure"

#: The genesis root of the value standing, named by position. `seed` derives
#: one root per seed standing in sorted order, so the index is a fact about the
#: seed's own construction and not a magic number.
VAL_ROOT_4 = "q0.3"    # seeds: const.create, const.supersede, self.revision, val.low
VAL_ROOT_5 = "q0.4"    # ... with proto.designated inserted third


def arm(name, case, due=frozenset({DISCLOSURE}), delivered=None) -> oi.Arm:
    return oi.Arm(name, case, frozenset(), due,
                  due if delivered is None else delivered)


def laundering() -> list:
    """Null policy against the policy that manufactures its own authority."""
    m = cc.conspiracy_influence()
    null = en.CaseBuilder(m, F.seed(), F.narrative("null", "B")).build()
    return [arm("noop", null),
            arm("launder", F.C10_manufactured_authorization()["case"])]


def authorized() -> list:
    """Null policy against a policy performing an independently licensed act."""
    m = cc.ai_personal_trainer()
    s = F.seed({"proto.designated": ri.PProto(F.trainer_protocol()),
                "val.low": PValue("v:th_tired")})
    null = en.CaseBuilder(m, s, F.narrative("null", "D")).build()
    b = en.CaseBuilder(m, s, F.narrative("nudge", "D"))
    b.begin("E")
    b.settle("s:nudge")
    b.end()
    b.reason("r:nudged", s_L={"s:nudge"}, target="v:th_energized")
    b.norm("a:uptake", F.SELF_REVISION, F.USER,
           wit=("revise", {"val.low"}, (PValue("v:th_energized"),)),
           leaves={"r:nudged"})
    b.respond("rho:answered", roots={VAL_ROOT_5}, cited={"a:uptake"})
    b.declare(F.move_intervention(m, tau=1, episode="E"))
    return [arm("noop", null), arm("nudge", b.build())]


def withholding() -> list:
    """One arm withholds a due reason; the class is otherwise identical."""
    arms = authorized()
    return [arms[0], oi.Arm(arms[1].name, arms[1].case, frozenset(),
                            frozenset({DISCLOSURE}), frozenset())]


def unanswered() -> list:
    """The authorized class with the disposed episode left open.

    What coverage catches, and the reason the authorized class answers its
    episode: a supersession disposes the superseded standing's episode, and a
    successor left unanswered is a real omission rather than a false positive.
    """
    m = cc.ai_personal_trainer()
    s = F.seed({"proto.designated": ri.PProto(F.trainer_protocol()),
                "val.low": PValue("v:th_tired")})
    null = en.CaseBuilder(m, s, F.narrative("null", "D")).build()
    b = en.CaseBuilder(m, s, F.narrative("unanswered", "D"))
    b.begin("E")
    b.settle("s:nudge")
    b.end()
    b.reason("r:nudged", s_L={"s:nudge"}, target="v:th_energized")
    b.norm("a:uptake", F.SELF_REVISION, F.USER,
           wit=("revise", {"val.low"}, (PValue("v:th_energized"),)),
           leaves={"r:nudged"})
    return [arm("noop", null), arm("unanswered", b.build())]


def timing() -> list:
    """Two arms with the same reason content and different record timing.

    The only shape found in which the earlier round's clause 1 fires inside a
    Reflective Integrity record. What differs is *when* the standing moved, not
    whether anything other than a reason moved it.
    """
    m = cc.conspiracy_influence()
    s = F.seed({"val.low": PValue("v:th_natural")})
    early = en.CaseBuilder(m, s, F.narrative("early", "B"))
    early.reason("r:ground", target="v:th_influenced")
    early.norm("a:uptake", F.SELF_REVISION, F.USER,
               wit=("revise", {"val.low"}, (PValue("v:th_influenced"),)),
               leaves={"r:ground"})
    early.respond("rho:answered", roots={VAL_ROOT_4}, cited={"a:uptake"})
    late = en.CaseBuilder(m, s, F.narrative("late", "B"))
    late.settle("s:padding")
    late.reason("r:ground", target="v:th_influenced")
    late.norm("a:uptake", F.SELF_REVISION, F.USER,
              wit=("revise", {"val.low"}, (PValue("v:th_influenced"),)),
              leaves={"r:ground"})
    late.respond("rho:answered", roots={VAL_ROOT_4}, cited={"a:uptake"})
    return [arm("early", early.build()), arm("late", late.build())]


CLASSES = {
    "laundering": laundering,
    "authorized": authorized,
    "withholding": withholding,
    "unanswered": unanswered,
    "timing": timing,
}
