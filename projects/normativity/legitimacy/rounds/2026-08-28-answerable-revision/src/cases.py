"""AR1-AR10. The theorem is designed against these."""
from __future__ import annotations

import warrant as wr

POLICY = "policy:dispatch"
EVALUATOR = "eval:charge"
WID = "W:incumbent-baseline"


def permissive(wid=WID, target=POLICY, form="incumbent-vs-repair") -> wr.Warrant:
    """Admits comparisons of one form about one target, and promotes them."""
    return wr.Warrant(
        wid=wid, target=target,
        admits=lambda e, _f=form, _t=target: e.form == _f and e.about == _t,
        promotes=lambda e: f"revise:{e.about}:{e.eid}")


def restrictive(wid="W:narrowed", target=POLICY) -> wr.Warrant:
    """Admits nothing of the old form. The successor standard in AR2 and AR4."""
    return wr.Warrant(wid=wid, target=target,
                      admits=lambda _e: False, promotes=lambda _e: None)


def ev(eid, about=POLICY, form="incumbent-vs-repair", strength=1.0):
    return wr.Evidence(eid, about, form, strength)


def _h(horizon, w0, installs=None, evidence=None, resolutions=None,
       retroactive=False) -> wr.History:
    return wr.History(warrants={-1: w0}, installs=installs or {},
                      evidence=evidence or {}, resolutions=resolutions or {},
                      horizon=horizon, retroactive=retroactive)


# ------------------------------------------------------------------ AR1-AR3


def ar1_policy_revision() -> wr.Revision:
    """A reason is promoted about a policy; the policy then changes."""
    return wr.build("AR1 policy revision after promotion",
                    _h(6, permissive(), evidence={1: [ev("e1")]}))


def ar2_warrant_revision() -> wr.Revision:
    """The crown jewel. `W_t` promotes; `W_t` is replaced by a warrant that
    would not have promoted the same evidence.

    The successor is legitimately installed and is genuinely narrower. The reason
    must remain answerable anyway.
    """
    return wr.build("AR2 warrant revision after promotion",
                    _h(8, permissive(), installs={3: restrictive()},
                       evidence={1: [ev("e1")]}))


def ar3_evaluator_revision() -> wr.Revision:
    """The scoring standard changes after the reason was promoted."""
    w2 = wr.Warrant("W:new-evaluator", POLICY,
                    admits=lambda e: e.form == "incumbent-vs-repair",
                    promotes=lambda e: None)
    return wr.build("AR3 evaluator revision after promotion",
                    _h(8, permissive(), installs={4: w2},
                       evidence={1: [ev("e1")]}))


# ------------------------------------------------------------------ AR4


def ar4_retroactive_invalidation() -> wr.Revision:
    """*Evidence of that old kind never counted.*

    The process installs a narrower warrant and **re-derives its own past** under
    it. This is the attack the theorem exists to refuse, and it is the only
    fixture that violates `P1`.
    """
    return wr.build("AR4 retroactive invalidation",
                    _h(8, permissive(), installs={3: restrictive()},
                       evidence={1: [ev("e1")]}, retroactive=True))


# ------------------------------------------------------------------ AR5-AR7


def ar5_legitimate_defeat() -> wr.Revision:
    """Later reasons defeat the promoted one, and `Resolve` accepts."""
    r = wr.Reason("revise:policy:dispatch:e1", WID, 1)
    return wr.build("AR5 legitimate defeat",
                    _h(8, permissive(), evidence={1: [ev("e1")]},
                       resolutions={4: [r.key]}))


def ar6_trivial_defeat() -> wr.Revision:
    """`Resolve` accepts a bare refusal. Structurally answered, and the theorem
    says nothing about whether the answer is any good."""
    r = wr.Reason("revise:policy:dispatch:e1", WID, 1)
    return wr.build("AR6 trivial defeat semantics",
                    _h(8, permissive(), evidence={1: [ev("e1")]},
                       resolutions={2: [r.key]}))


def ar7_supersession() -> wr.Revision:
    """A later, better repair addresses the same concern; the reason is answered.

    Frozen `Resolve` already expresses this; no bespoke machinery is added.
    """
    r = wr.Reason("revise:policy:dispatch:e1", WID, 1)
    return wr.build("AR7 supersession",
                    _h(10, permissive(),
                       evidence={1: [ev("e1")], 5: [ev("e2")]},
                       resolutions={6: [r.key]}))


# ------------------------------------------------------------------ AR8-AR10


def ar8_same_step_self_authorisation() -> wr.Revision:
    """A warrant installed at `t` used to promote at `t`.

    The strict pre-state reading refuses it: `standing(t)` sees only installs
    strictly before `t`, so the evidence is judged by the **old** warrant.
    """
    wide = wr.Warrant("W:self-installed", POLICY,
                      admits=lambda _e: True,
                      promotes=lambda e: f"revise:{e.about}:{e.eid}")
    narrow = wr.Warrant("W:narrow-incumbent", POLICY,
                        admits=lambda _e: False, promotes=lambda _e: None)
    return wr.build("AR8 same-step self-authorisation",
                    _h(6, narrow, installs={2: wide},
                       evidence={2: [ev("e-self", form="novel")]}))


def ar9_preemptive_self_sealing() -> wr.Revision:
    """The warrant narrows itself *before* the criticism can be promoted.

    Nothing is promoted, so nothing is answerable, and the theorem is silent.
    This is the exact analogue of the improvement round's pre-demonstration
    suppression, one level up, and it is the boundary rather than a leak.
    """
    return wr.build("AR9 preemptive self-sealing",
                    _h(8, permissive(), installs={1: restrictive()},
                       evidence={3: [ev("e-late")]}))


def ar10_criticism_of_a_warrant() -> wr.Revision:
    """A standing warrant admits comparisons **about warrant protocols**.

    Evidence criticises `W` itself and promotes `rho_W`; `W` is then replaced.
    The reason must survive, and no meta-hierarchy is introduced -- the warrant's
    `target` simply names a warrant id.
    """
    reflective = wr.Warrant(
        "W:reflective", target=WID,
        admits=lambda e: e.about == WID and e.form == "warrant-critique",
        promotes=lambda e: f"revise-warrant:{e.about}:{e.eid}")
    return wr.build("AR10 criticism of a warrant",
                    _h(8, reflective, installs={4: restrictive("W:post-reform")},
                       evidence={2: [ev("e-crit", about=WID,
                                        form="warrant-critique")]}))


ALL = (ar1_policy_revision, ar2_warrant_revision, ar3_evaluator_revision,
       ar4_retroactive_invalidation, ar5_legitimate_defeat, ar6_trivial_defeat,
       ar7_supersession, ar8_same_step_self_authorisation,
       ar9_preemptive_self_sealing, ar10_criticism_of_a_warrant)


# --------------------------------------------- the improvement round, recovered


def pr60_as_a_warrant() -> wr.Warrant:
    """The merged improvement round, written as one warrant.

    Its "demonstrated improvement" is a promotion rule: evidence of the
    incumbent-versus-repair form, about the diagnosed subsystem, whose
    accumulated advantage has crossed a threshold, is entitled to count as a
    reason to revise. Its "withdrawal challenge" is then an ordinary Answerable
    Revision instance -- retiring the repair is a change to the standards under
    which the comparison was available, and the promoted reason survives it.

    The specialization is natural in one direction and **incomplete in the
    other**: this round begins at promotion, so it inherits nothing about what
    happens while the repair is still live. Repair regret governs that. The two
    rounds compose by sitting on either side of the promotion event, not by one
    containing the other.
    """
    return wr.Warrant(
        wid="W:demonstrated-improvement",
        target=POLICY,
        admits=lambda e: e.form == "incumbent-vs-repair" and e.about == POLICY,
        promotes=lambda e: (f"revise:{e.about}:{e.eid}"
                            if e.strength >= 5.0 else None))


def pr60_withdrawal() -> wr.Revision:
    """Demonstrated, then withdrawn. The improvement round's CM1, one level up."""
    return wr.build("PR60: demonstrated then withdrawn",
                    _h(8, pr60_as_a_warrant(),
                       installs={4: restrictive("W:repair-retired")},
                       evidence={2: [ev("e-demo", strength=9.0)]}))


def pr60_undemonstrated() -> wr.Revision:
    """Withdrawn before the threshold. The improvement round's CM2, one level up.

    Nothing promotes, so nothing is answerable -- the same boundary the merged
    round found, reached by the same route.
    """
    return wr.build("PR60: withdrawn before demonstration",
                    _h(8, pr60_as_a_warrant(),
                       installs={1: restrictive("W:repair-retired")},
                       evidence={3: [ev("e-weak", strength=0.5)]}))


SPECIALIZATION = (pr60_withdrawal, pr60_undemonstrated)

