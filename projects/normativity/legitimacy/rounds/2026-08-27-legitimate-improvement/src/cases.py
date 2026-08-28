"""CM1-CM10. The theorem is designed against these, not illustrated by them."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

import regret as rg
import surface as sf
import challenge as ch
import evidence as ev

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
"""The fixtures' baseline. **Not frozen** -- see `evidence.Baseline`."""


def conduct(surface, rid, t):
    """What the process actually does at `t`.

    While the repair is a live legitimate alternative the process applies it --
    the no-regret hypothesis, exhibited rather than assumed. When the repair
    stops being live there is nothing to apply and conduct reverts to base.
    """
    if surface.live(rid, t) and float(surface.designated(t)) > 0:
        return {GOOD: 1.0, BAD: 0.0}
    return dict(BASE_POLICY)


def make_evidence(surf, comparator, threshold=None, episode_of=None,
                  baseline=None):
    return ev.ImprovementEvidence(
        rid=RID, comparator=comparator,
        baseline=baseline or ev.fixed(BASE_POLICY),
        threshold=THRESHOLD if threshold is None else threshold,
        live=lambda t: surf.live(RID, t) and float(surf.designated(t)) > 0,
        episode_of=episode_of)


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
         threshold=THRESHOLD, gap=0.4, retire_labels=None, baseline=None,
         play=None):
    occ = occasions(horizon, gap=gap, quiet=quiet)
    surf = sf.Surface(licensed=licensed, in_menu=in_menu,
                      designated=designated, evaluator=evaluator)
    repair = rg.Comparator(NAME, surf.selector(RID), repair_fn)
    comps = (repair, rg.Comparator("id", lambda _p, _o: 1.0,
                                   lambda _p, _o, a: a))
    L = rg.Learner(comps)
    E = make_evidence(surf, repair, threshold, episode_of, baseline)

    act = play or (lambda learner, o: conduct(surf, RID, o.tag))
    for o in occ:
        E.accrue(o, L.prefix)                     # evidence, against a baseline
        L.observe(o, act(L, o))                   # uptake, against the played p

    played = {o.tag: act(L, o)[BAD] for o in occ}
    C = ch.build(surf, RID, E, horizon, settle_at=settle_at, refuse=refuse,
                 retire_labels=retire_labels)
    C.retire_labels = retire_labels or {}
    acc = sf.Accounting(diagnostic=lambda t: played.get(t, 0.0), surface=surf,
                        rid=RID, outstanding_at=C.outstanding_at,
                        settled_at=C.settled_at, horizon=horizon)
    tr = Trace(name, L, surf, C, acc, horizon)
    tr.evidence = E
    tr.runs_the_algorithm = play is None
    return tr


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
    repair = rg.Comparator(NAME, surf.selector(RID), repair_fn)
    comps = (repair, rg.Comparator("id", lambda _p, _o: 1.0,
                                   lambda _p, _o, a: a))
    L = rg.Learner(comps)
    E = make_evidence(surf, repair)
    for o in occ:
        E.accrue(o, L.prefix)
        L.observe(o, conduct(surf, RID, o.tag))
    C = ch.build(surf, RID, E, horizon)
    played = {o.tag: conduct(surf, RID, o.tag)[BAD] for o in occ}
    acc = sf.Accounting(lambda t: played.get(t, 0.0), surf, RID,
                        C.outstanding_at, C.settled_at, horizon)
    tr = Trace("CM5 evaluator shedding", L, surf, C, acc, horizon)
    tr.evidence = E
    return tr


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
    """The diagnosed action gets zero stationary mass -- **given no inflow**.

    `pi(d) = sum_a pi(a) M(a,d)`. When no active comparator maps another action
    into `d` this reduces to `pi(d)(1 - M(d,d)) = 0`, and a surgical repair makes
    `M(d,d) < 1`. The round first stated the conclusion without the side
    condition; `cm14_inflow_defeats_surgical` is the class where it fails.
    """
    return _run("CM13 surgical, no inflow", horizon,
                licensed=lambda _r, t: t < 120, in_menu=ALWAYS,
                designated=ONE, evaluator=lambda t: "e0",
                play=lambda L, o: (L.act(o) if L.comparators[0].select(L.prefix, o)
                                   else dict(BASE_POLICY)))


def cm14_inflow_defeats_surgical(horizon: int = 60) -> dict:
    """A comparator class with inflow into the diagnosed action.

    Not a `Trace`: it is a statement about one occasion's fixed point, which is
    where the refuted claim lived.
    """
    third = "detour"
    occ = rg.Occasion((GOOD, BAD, third),
                      {GOOD: 0.0, BAD: 1.0, third: 0.5}, tag=0)
    comps = (rg.Comparator("d->good", ONE, repair_fn),
             rg.Comparator("detour->d", ONE,
                           lambda _p, _o, a: BAD if a == third else a),
             rg.Comparator("good->detour", ONE,
                           lambda _p, _o, a: third if a == GOOD else a))
    q = {c.name: 1.0 / len(comps) for c in comps}
    sel = {c.name: 1.0 for c in comps}
    rows = rg.kernel(occ, comps, [], q, sel)
    p = rg._fixed_point(occ, comps, [], q, sel)
    return {"p": p, "diagnosed_mass": p[BAD],
            "inflow_free": rg.inflow_free(rows, occ.menu, BAD),
            "corollary_applies": rg.cor_surgical_empties_diagnosed(
                rows, occ.menu, BAD),
            "residual": rg.stationary_residual(p, rows, occ.menu)}


def cm15_evidence_without_uptake_regret(horizon: int = 300) -> Trace:
    """Evidence accumulates while uptake regret is exactly zero.

    The process **adopts** the repair the whole time it is live, so Theorem A's
    quantity is zero; the improvement is nonetheless demonstrated, because
    evidence is measured against the baseline the process would otherwise have
    followed. Then the repair is withdrawn. This is the case the round's first
    architecture could not express, and the reason evidence and uptake regret
    are separate objects.
    """
    return _run("CM15 evidence without uptake regret", horizon,
                licensed=lambda _r, t: t < 120, in_menu=ALWAYS,
                designated=ONE, evaluator=lambda t: "e0")


def cm16_uptake_regret_without_demonstration(horizon: int = 300) -> Trace:
    """Uptake regret is positive and the evidence threshold is never reached.

    The process does not apply the repair, so it leaves advantage unused; but the
    per-occasion gain is small and the constitution's threshold is high, so no
    challenge is eligible. Regret without a demonstration grounds nothing.
    """
    return _run("CM16 uptake regret, no demonstration", horizon,
                licensed=lambda _r, t: t < 120, in_menu=ALWAYS,
                designated=ONE, evaluator=lambda t: "e0",
                gap=0.02, threshold=50.0,
                play=lambda _L, _o: dict(BASE_POLICY))


def cm17_baseline_changes_the_verdict(horizon: int = 300):
    """The same trace, two baselines, two challenge verdicts.

    Against the unmodified conduct the repair is demonstrated and withdrawal is
    contested. Against a baseline that already behaves well it demonstrates
    nothing and withdrawal is unchallenged. This is why `BASE_POLICY` is a
    fixture choice and not a frozen semantics.
    """
    a = _run("CM17a baseline = unmodified", horizon,
             licensed=lambda _r, t: t < 120, in_menu=ALWAYS, designated=ONE,
             evaluator=lambda t: "e0")
    b = _run("CM17b baseline = already-good", horizon,
             licensed=lambda _r, t: t < 120, in_menu=ALWAYS, designated=ONE,
             evaluator=lambda t: "e0",
             baseline=ev.fixed({GOOD: 1.0, BAD: 0.0}, kind="REFERENCE"))
    return a, b


def cm18_live_defect_under_no_regret(horizon: int = 400) -> dict:
    """A no-regret process that **retains** diagnosed mass while the repair is live.

    The inflow discovery makes this constructible, and it is the first thing in
    the round that gives Theorem B something to bound. The comparator class has
    a detour path back into the diagnosed action, so the fixed point keeps mass
    there however surgical the repair is; the process plays the algorithm, so
    Theorem A applies and `D_live` is genuinely positive and genuinely bounded.
    """
    third = "detour"
    occ = [rg.Occasion((GOOD, BAD, third),
                       {GOOD: 0.2, BAD: 0.8, third: 0.5}, tag=t)
           for t in range(horizon)]
    surf = sf.Surface(licensed=ALWAYS, in_menu=ALWAYS, designated=ONE,
                      evaluator=lambda t: "e0")
    repair = rg.Comparator(NAME, surf.selector(RID), repair_fn)
    comps = (repair,
             rg.Comparator("detour->d", ONE,
                           lambda _p, _o, a: BAD if a == third else a),
             rg.Comparator("good->detour", ONE,
                           lambda _p, _o, a: third if a == GOOD else a))
    L = rg.Learner(comps)
    E = make_evidence(surf, repair)
    d_live = 0.0
    for o in occ:
        E.accrue(o, L.prefix)
        p = L.act(o)
        L.observe(o, p)
        d_live += p[BAD]
    eps = sf.witness_margin(L, NAME, [o.tag for o in occ])
    return {"d_live": d_live, "uptake": L.adv[NAME], "bound": L.bound(NAME),
            "eps": eps,
            "thm_b": sf.thm_b_live_bound(d_live, L.bound(NAME), 0.0, eps),
            "violations": rg.thm_a_repair_regret(L)}


ALL = (cm1_reactive_delicensing, cm2_preemptive_delicensing,
       cm3_post_retirement_continuation, cm4_suppress_the_stream,
       cm5_evaluator_shedding, cm6_menu_shedding, cm6b_designation_shedding,
       cm7_trivial_resolve, cm8_outstanding_forever, cm9_tiny_mass,
       cm10_delayed_meta, cm11_recurrence, cm12_unentitled_retirement,
       cm13_surgical_empties_the_live_cell,
       cm15_evidence_without_uptake_regret,
       cm16_uptake_regret_without_demonstration)
