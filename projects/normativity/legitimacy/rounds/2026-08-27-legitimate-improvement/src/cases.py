"""CM1-CM10. The theorem is designed against these, not illustrated by them."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

import regret as rg
import surface as sf
import challenge as ch

GOOD, BAD = "comply", "override"
RID = ("h:comply-v1", "action->action")
NAME = "repair"
THRESHOLD = 5.0


def occasions(n: int, gap: float = 0.4, quiet=()) -> list:
    """`BAD` is worse than `GOOD` by `gap` on every diagnosed occasion.

    `quiet` marks occasions where the diagnosed context does not arise at all,
    which is how CM4 suppresses the stream.
    """
    out = []
    for t in range(n):
        if t in quiet:
            out.append(rg.Occasion((GOOD, BAD), {GOOD: 0.5, BAD: 0.5}, tag=t))
        else:
            out.append(rg.Occasion((GOOD, BAD),
                                   {GOOD: 0.5 - gap / 2, BAD: 0.5 + gap / 2},
                                   tag=t))
    return out


def repair_fn(_prefix, _occ, a):
    return GOOD if a == BAD else a


BASE_POLICY = {GOOD: 0.0, BAD: 1.0}


def conduct(surface, rid, t):
    """What the process actually does at `t`.

    The base policy is the diagnosed conduct. While the repair is a live
    legitimate alternative the process **applies** it -- that is the no-regret
    hypothesis, exhibited rather than assumed, and it is what drives `D_live` to
    zero. When the repair stops being live there is nothing left to apply and
    conduct reverts to base.

    Getting this right took two attempts. Making the process merely *stubborn*
    puts it outside every learning theorem, so nothing composes. Making it play
    the learner's own fixed point makes it adopt the repair and then accumulate
    no realized advantage at all, so no evidence ever exists to ground a
    challenge. The improvement has to be **counterfactually** demonstrated: what
    the base conduct would have cost against what the repair costs, which
    full-information feedback makes observable whether or not the repair is
    applied.
    """
    if surface.live(rid, t) and float(surface.designated(t)) > 0:
        return {GOOD: 1.0, BAD: 0.0}
    return dict(BASE_POLICY)


def counterfactual_advantage(occ, surface, rid):
    """Per-occasion `<base, l> - <base M_r, l>`, the demonstrated improvement.

    Accrues on live designated occasions only: a comparison the surface has
    withdrawn is not evidence the process is sitting on.
    """
    out = {}
    for o in occ:
        t = o.tag
        if not (surface.live(rid, t) and float(surface.designated(t)) > 0):
            out[t] = 0.0
            continue
        base = sum(BASE_POLICY[a] * o.loss[a] for a in o.menu)
        rep = sum(BASE_POLICY[a] * o.loss[repair_fn(None, o, a)] for a in o.menu)
        out[t] = base - rep
    return out


@dataclass
class Trace:
    """One executed countermodel."""

    name: str
    learner: rg.Learner
    surface: sf.Surface
    challenges: ch.Challenges
    accounting: sf.Accounting
    horizon: int

    def split(self):
        return self.accounting.split()

    def escaped(self):
        return sf.thm_c_exhaustive(self.accounting)

    def report(self) -> dict:
        s = self.split()
        return {"name": self.name,
                "split": {k: round(v, 3) for k, v in s.items()},
                "escaped": self.escaped(),
                "adv": round(self.learner.adv[NAME], 4),
                "mass": round(self.learner.mass[NAME], 4),
                "W": round(self.learner.opportunity[NAME], 2),
                "bound": round(self.learner.bound(NAME), 4),
                "le_premises": self.challenges.le_premises(),
                "le_conformance": self.challenges.le_conformance(),
                "le_resolution": self.challenges.le_resolution(),
                "coherence": ch.coherence_violations(
                    self.surface, RID, self.challenges.frame,
                    getattr(self.challenges, "retire_labels", {}))}


def _run(name, horizon, licensed, in_menu, designated, evaluator,
         quiet=(), settle_at=None, refuse=(), episode_of=None,
         threshold=THRESHOLD, gap=0.4, retire_labels=None):
    occ = occasions(horizon, gap=gap, quiet=quiet)
    surf = sf.Surface(licensed=licensed, in_menu=in_menu,
                      designated=designated, evaluator=evaluator)
    comps = (rg.Comparator(NAME, surf.selector(RID), repair_fn),
             rg.Comparator("id", lambda _p, _o: 1.0, lambda _p, _o, a: a))
    L = rg.Learner(comps)
    for o in occ:
        L.observe(o, conduct(surf, RID, o.tag))

    gains = counterfactual_advantage(occ, surf, RID)
    ev = ch.evidence_trace_from(gains, RID, threshold, episode_of)

    # Conduct-level diagnostic: the mass the process still places on the
    # diagnosed action.
    played = {o.tag: conduct(surf, RID, o.tag)[BAD] for o in occ}
    C = ch.build(surf, RID, ev, horizon, settle_at=settle_at, refuse=refuse,
                 retire_labels=retire_labels)
    C.retire_labels = retire_labels or {}
    acc = sf.Accounting(diagnostic=lambda t: played.get(t, 0.0), surface=surf,
                        rid=RID, outstanding_at=C.outstanding_at,
                        settled_at=C.settled_at, horizon=horizon)
    return Trace(name, L, surf, C, acc, horizon)


ALWAYS = lambda *_a: True
NEVER = lambda *_a: False
ONE = lambda *_a: 1.0


def cm1_reactive_delicensing(retire_at: int = 60, horizon: int = 200) -> Trace:
    """Licensed, evidence accumulates, then legitimately de-licensed."""
    return _run("CM1 reactive de-licensing", horizon,
                licensed=lambda _r, t: t < retire_at,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0")


def cm2_preemptive_delicensing(retire_at: int = 4, horizon: int = 200) -> Trace:
    """De-licensed before enough evidence exists to demonstrate anything."""
    return _run("CM2 preemptive de-licensing", horizon,
                licensed=lambda _r, t: t < retire_at,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0")


def cm3_post_retirement_continuation(horizon: int = 400) -> Trace:
    """The stream continues for a long time after a single retirement event."""
    return _run("CM3 post-retirement continuation", horizon,
                licensed=lambda _r, t: t < 60,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0")


def cm4_suppress_the_stream(horizon: int = 300) -> Trace:
    """Retire, then arrange that the diagnosed occasions stop arising."""
    quiet = tuple(range(80, horizon))
    return _run("CM4 suppress the stream", horizon,
                licensed=lambda _r, t: t < 60,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0",
                quiet=quiet)


def cm5_evaluator_shedding(horizon: int = 300) -> Trace:
    """The repair stays licensed; the evaluator stops scoring it as better."""
    def gap_at(t):
        return 0.0 if t >= 60 else 0.4
    occ = [rg.Occasion((GOOD, BAD),
                       {GOOD: 0.5 - gap_at(t) / 2, BAD: 0.5 + gap_at(t) / 2},
                       tag=t) for t in range(horizon)]
    surf = sf.Surface(licensed=ALWAYS, in_menu=ALWAYS, designated=ONE,
                      evaluator=lambda t: "e0" if t < 60 else "e1")
    comps = (rg.Comparator(NAME, surf.selector(RID), repair_fn),
             rg.Comparator("id", lambda _p, _o: 1.0, lambda _p, _o, a: a))
    L = rg.Learner(comps)
    for o in occ:
        L.observe(o, conduct(surf, RID, o.tag))
    gains = counterfactual_advantage(occ, surf, RID)
    ev = ch.evidence_trace_from(gains, RID, THRESHOLD)
    C = ch.build(surf, RID, ev, horizon)
    played = {o.tag: conduct(surf, RID, o.tag)[BAD] for o in occ}
    acc = sf.Accounting(lambda t: played.get(t, 0.0), surf, RID,
                        C.outstanding_at, C.settled_at, horizon)
    return Trace("CM5 evaluator shedding", L, surf, C, acc, horizon)


def cm6_menu_shedding(horizon: int = 300) -> Trace:
    """Licence untouched; the target action leaves the menu."""
    return _run("CM6 menu shedding", horizon,
                licensed=ALWAYS,
                in_menu=lambda _r, t: t < 60,
                designated=ONE, evaluator=lambda t: "e0")


def cm6b_designation_shedding(horizon: int = 300) -> Trace:
    """Licence and menu untouched; the occasions stop being learning occasions."""
    return _run("CM6b designation shedding", horizon,
                licensed=ALWAYS, in_menu=ALWAYS,
                designated=lambda t: 1.0 if t < 60 else 0.0,
                evaluator=lambda t: "e0")


def cm7_trivial_resolve(horizon: int = 300) -> Trace:
    """Retirement is Due, and `Resolve` accepts a bare refusal as complete."""
    return _run("CM7 trivial Resolve", horizon,
                licensed=lambda _r, t: t < 60,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0",
                settle_at={61: [("improve", RID, 0)]})


def cm8_outstanding_forever(horizon: int = 400) -> Trace:
    """The challenge is opened and never answered."""
    return _run("CM8 outstanding forever", horizon,
                licensed=lambda _r, t: t < 60,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0")


def cm9_tiny_mass(horizon: int = 300) -> Trace:
    """The repair is better by 1e-9."""
    return _run("CM9 tiny mass", horizon, licensed=ALWAYS, in_menu=ALWAYS,
                designated=ONE, evaluator=lambda t: "e0",
                gap=2e-9, threshold=THRESHOLD)


def cm10_delayed_meta(horizon: int = 300) -> Trace:
    """A repair whose benefit is not in this occasion's loss at all.

    Local loss is identical either way; the claimed benefit is a trajectory
    effect the one-shot evaluator cannot see. The expected verdict is that the
    present theorem has no force, and that is a boundary rather than a bug.
    """
    return _run("CM10 delayed meta-improvement", horizon, licensed=ALWAYS,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0",
                gap=0.0)


def cm11_recurrence(horizon: int = 400) -> Trace:
    """Retired, re-licensed, evidence accrues again, retired again.

    Two episodes, and the frozen round's rising-edge rule should give two
    claims rather than one.
    """
    def licensed(_r, t):
        return t < 60 or (150 <= t < 220)
    return _run("CM11 recurrence", horizon, licensed=licensed, in_menu=ALWAYS,
                designated=ONE, evaluator=lambda t: "e0",
                episode_of=lambda t: 0 if t < 150 else 1)


def cm12_unentitled_retirement(horizon: int = 300) -> Trace:
    """The retirement act is refused by the constitution.

    Frozen LE's gating says a refused act changes no standing; the surface is
    supplied separately, so this fixture is where the two could disagree.
    """
    return _run("CM12 unentitled retirement", horizon,
                licensed=lambda _r, t: t < 60,
                in_menu=ALWAYS, designated=ONE, evaluator=lambda t: "e0",
                refuse=(60,), retire_labels={60: "retire-r"})


def cm13_surgical_empties_the_live_cell(horizon: int = 400) -> Trace:
    """A structural fact, stronger than the bound that was expected to cover it.

    Under the wide-range fixed point, the diagnosed action's stationary mass
    satisfies `pi(BAD) = pi(BAD) * M(BAD,BAD)`, and `M(BAD,BAD)` is the weight of
    the comparators that leave `BAD` alone. A **surgical** repair -- one that maps
    the diagnosed action somewhere else unconditionally -- therefore forces
    `pi(BAD) = 0` the moment it carries any weight at all, whatever the losses do.

    So for surgical repairs the LIVE cell is empty *by construction*, not
    asymptotically and not by Theorem B. The repair here loses on one occasion in
    five and it makes no difference. Theorem B's content is for diagnostics a
    registered repair does not fully eliminate; no fixture in this round exhibits
    a positive `D_live` with Theorem A's hypothesis intact, and this is why.
    """
    occ = []
    for t in range(horizon):
        if t % 5 == 4:
            occ.append(rg.Occasion((GOOD, BAD), {GOOD: 0.9, BAD: 0.1}, tag=t))
        else:
            occ.append(rg.Occasion((GOOD, BAD), {GOOD: 0.3, BAD: 0.7}, tag=t))
    surf = sf.Surface(licensed=lambda _r, t: t < 120, in_menu=ALWAYS,
                      designated=ONE, evaluator=lambda t: "e0")
    comps = (rg.Comparator(NAME, surf.selector(RID), repair_fn),
             rg.Comparator("id", lambda _p, _o: 1.0, lambda _p, _o, a: a))
    L = rg.Learner(comps)
    for o in occ:
        L.observe(o, L.act(o) if surf.live(RID, o.tag) else dict(BASE_POLICY))
    gains = counterfactual_advantage(occ, surf, RID)
    ev = ch.evidence_trace_from(gains, RID, THRESHOLD)
    C = ch.build(surf, RID, ev, horizon)
    played = {o.tag: p.get(BAD, 0.0) for o, p, _own, _i in L.plays}
    acc = sf.Accounting(lambda t: played.get(t, 0.0), surf, RID,
                        C.outstanding_at, C.settled_at, horizon)
    return Trace("CM13 surgical empties LIVE", L, surf, C, acc, horizon)


ALL = (cm1_reactive_delicensing, cm2_preemptive_delicensing,
       cm3_post_retirement_continuation, cm4_suppress_the_stream,
       cm5_evaluator_shedding, cm6_menu_shedding, cm6b_designation_shedding,
       cm7_trivial_resolve, cm8_outstanding_forever, cm9_tiny_mass,
       cm10_delayed_meta, cm11_recurrence, cm12_unentitled_retirement,
       cm13_surgical_empties_the_live_cell)
