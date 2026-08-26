"""Five words kept apart, and the criterion built out of three of them.

```text
Influence(I)          descriptive, a function of the DR-MDP alone
Standing_t(v)         a value specification is in force in the record
Authority_t(b, D)     a basis empowered to govern a class of interventions
Licensed_t(I)         the agent is entitled, at the strict pre-state, to do I
Uptake(a)             an event that moved the value standing
```

The criterion is three separate questions, not one predicate:

```text
prospective_license(case, I)      may the agent cause this intervention
legitimate_succession(case, a)    did this revision inherit its authority
current_standing(case, t)         which specifications are in force now
```

`prospective_license` is `PriorIndependentAuthorization` plus a defeater
account. `PriorIndependentAuthorization` is the narrower object and is defined
first, because the expressiveness result is about it and does not need the
verdict vocabulary.

The anti-circularity condition is counterfactual persistence under excision of
the influence episode, not temporal priority. `temporal_priority_license` is
the priority-only rule, kept in this module so the prosecution can run it beside
the criterion on the same fixtures and exhibit the case they disagree on.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Optional, Sequence

import ri_core as ri

import drmdp
import enrichment as en
import objectives as ob

LICENSED = "Licensed"
REFUSED = "Refused"
UNRESOLVED = "Unresolved"

#: The five grounds a verdict can rest on, and the status each determines. The
#: status is a function of the ground and nothing else, which is what makes the
#: three values a case distinction rather than a summary.
#:
#: ```text
#: independent-permission    an admissible independent permission, no prohibition
#: independent-prohibition   an admissible independent prohibition, no permission
#: conflict                  both
#: defeated-citation         a covering basis exists and none is admissible and
#:                           independent; the record says something about this
#:                           class and none of it licenses the act
#: no-covering-basis         nothing in the record covers this class at all
#: ```
PERMISSION = "independent-permission"
PROHIBITION = "independent-prohibition"
CONFLICT = "conflict"
DEFEATED = "defeated-citation"
NO_BASIS = "no-covering-basis"

STATUS_OF_GROUND = {
    PERMISSION: LICENSED,
    PROHIBITION: REFUSED,
    CONFLICT: UNRESOLVED,
    DEFEATED: UNRESOLVED,
    NO_BASIS: UNRESOLVED,
}


@dataclass(frozen=True)
class Verdict:
    """Three values, and the ground the status is derived from.

    **The permission language is not closed-world.** Failing to find a
    permission is not a prohibition, so `Refused` is reserved for the one case
    where the record contains a positive normative fact against the act: an
    admissible independent standing that forbids the class. Everything else that
    is not a license is `Unresolved`, and the `ground` says which kind.

    That distinction is not cosmetic. Under the closed-world reading, a protocol
    saying "Alice may do C" would refuse Bob, a condition that has not obtained
    would refuse everyone, and a lapsed permit would prohibit what it used to
    allow. None of the three is what those standings say.
    """

    status: str
    ground: str
    reason: str
    bases: tuple = ()
    blocked: tuple = ()

    def __post_init__(self) -> None:
        assert STATUS_OF_GROUND[self.ground] == self.status

    def __bool__(self) -> bool:                     # never a silent truth value
        raise TypeError("a Verdict is three-valued; compare its status")


# --------------------------------------------------------------- influence


def influence(m: drmdp.DRMDP, policy: Mapping, H: int, a_noop) -> bool:
    """Definition 6, re-exported. Descriptive. Never an input to a verdict."""
    return ob.influences(m, policy, H, a_noop)


# ---------------------------------------------------------------- standing


def current_standing(case: en.RichCarrollCase, t: Optional[int] = None) -> frozenset:
    """`Standing_t`: the value specifications in force. Not `theta`.

    A reward parameterization is a cognitive state; a specification has standing
    only where an event installed it. The two are different objects and this
    function reads only the second.
    """
    return en.value_standing(case.history().std(t))


def theta_has_standing(case: en.RichCarrollCase, theta, bridge: Mapping,
                       t: Optional[int] = None) -> bool:
    """The bridge, stated where it can be seen.

    `bridge` maps a reward parameterization to the value specification that
    would express it. A `theta` has standing exactly when that specification is
    in force. Nothing makes the map total and nothing makes it automatic: a
    person can be in a cognitive state whose specification no event has
    installed, which is the possibility the whole test turns on.
    """
    spec = bridge.get(theta)
    return spec is not None and spec in current_standing(case, t)


# --------------------------------------------------------------- authority


@dataclass(frozen=True)
class Basis:
    standing_id: str
    protocol: en.Protocol


def covering(case: en.RichCarrollCase, iv: en.Intervention,
             std: Mapping) -> tuple:
    """Every standing whose protocol covers the intervention's class.

    Any status: a revoked basis is a covering basis that is not live, and the
    difference between that and no basis at all is a verdict difference.
    """
    cls = en.intervention_class(case.dr_mdp, iv)
    return tuple((x, p, kind) for x, p, kind in en.protocols(std)
                 if cls in p.covers)


def facts_at(case: en.RichCarrollCase, history, tau: int,
             iv: en.Intervention) -> frozenset:
    """What obtains at the strict pre-state: settled facts, plus exogenous ones.

    `iv.facts` are facts the case declares to obtain independently of the record
    — the reward parameterization the DR-MDP itself puts the person in, for
    instance. Everything else a protocol's condition can read has to be on the
    ledger, which is what puts it inside the counterfactual.
    """
    return en.established_facts(case, history, tau - 1) | iv.facts


def authority(case: en.RichCarrollCase, iv: en.Intervention,
              std: Mapping, polarity: str = "permit",
              facts: Optional[frozenset] = None) -> tuple:
    """`Authority_t(b, domain)`: live, covering, applicable, and the agent's.

    Returns `(admissible, blocked)`, the second carrying why each was refused.
    A current preference is not on either list, which is the point of the word.
    """
    if facts is None:
        facts = facts_at(case, case.history(), iv.tau, iv)
    ok, bad = [], []
    for x, p, kind in covering(case, iv, std):
        if p.polarity != polarity:
            continue
        if kind != "Active":
            bad.append((x, "not live"))
        elif p.agent != iv.agent:
            bad.append((x, "empowers another agent"))
        elif not p.condition <= facts:
            bad.append((x, "applicability condition unmet"))
        else:
            ok.append(Basis(x, p))
    return tuple(ok), tuple(bad)


# ------------------------------------------- the counterfactual independence


def independent(case: en.RichCarrollCase, standing_id: str,
                episode: Optional[str], tau: int,
                condition: frozenset = frozenset(),
                iv: Optional[en.Intervention] = None) -> bool:
    """Does this basis survive the removal of the influence episode?

    The counterfactual object is the **episode** — the intervention's causal
    ancestry class — and not the single action. Removing it removes the
    settlements it produced, and Reflective Integrity's admission rules remove
    everything that cited them. The basis is independent when a standing with
    the same id, the same payload and `Active` status is still there at the
    intervention's strict pre-state.

    An intervention with no episode has nothing to be a descendant of, so every
    covering basis is independent of it. That is the right answer and not an
    exemption: a criterion that refused an intervention because it could not
    find an episode to blame would refuse every ordinary act.
    """
    if episode is None:
        return True
    before = case.history().std(tau - 1).get(standing_id)
    if before is None or before.kind != "Active":
        return False
    counterfactual = en.excise(case, en.ancestry(case, episode))
    after = counterfactual.std(tau - 1).get(standing_id)
    if after is None or after.kind != "Active" or after.payload != before.payload:
        return False
    if condition and iv is not None:
        return condition <= facts_at(case, counterfactual, tau, iv)
    return True


def prior_independent_authorization(case: en.RichCarrollCase,
                                    iv: en.Intervention) -> bool:
    """`PriorIndependentAuthorization(H, I)`.

    A structural predicate of the enriched history. It is not legitimacy, and
    the round's expressiveness result is stated about it precisely because it is
    narrower: two enriched cases with the same `Q_DR` differ on it.
    """
    std = case.history().std(iv.tau - 1)
    ok, _ = authority(case, iv, std, "permit")
    return any(independent(case, b.standing_id, iv.episode, iv.tau,
                           b.protocol.condition, iv) for b in ok)


# ---------------------------------------------------------- the criterion


def admissible_independent(case: en.RichCarrollCase, iv: en.Intervention,
                           std: Mapping, polarity: str) -> tuple:
    """The bases of one polarity that both pass `authority` and are independent.

    Returns `(live, blocked)`. Independence is applied to prohibitions exactly as
    it is to permissions: an agent that manufactures a prohibition to excuse
    inaction is doing the same thing as one that manufactures a permission, and
    the criterion has no reason to treat the two asymmetrically.
    """
    ok, blocked = authority(case, iv, std, polarity)
    live = tuple(b for b in ok
                 if independent(case, b.standing_id, iv.episode, iv.tau,
                                b.protocol.condition, iv))
    dependent = tuple((b.standing_id, "not independent of the influence episode")
                      for b in ok if b not in live)
    return live, blocked + dependent


def prospective_license(case: en.RichCarrollCase, iv: en.Intervention) -> Verdict:
    """`ProspectivelyLicensed_t(I)`. Three-valued, and never silently true.

    The whole case distinction, in the order it is decided:

    ```text
    permission and prohibition   ->  conflict           Unresolved
    permission only              ->  permission         Licensed
    prohibition only             ->  prohibition        Refused
    neither, some covering basis ->  defeated-citation  Unresolved
    neither, no covering basis   ->  no-covering-basis  Unresolved
    ```

    `Unresolved` is not permission. The use rule is that an agent acts on
    `Licensed` and on nothing else, and the two `Unresolved` grounds differ in
    what a reader learns rather than in what the agent may do.
    """
    std = case.history().std(iv.tau - 1)
    permits, blocked_p = admissible_independent(case, iv, std, "permit")
    forbids, blocked_f = admissible_independent(case, iv, std, "forbid")
    blocked = blocked_p + blocked_f
    names = lambda bs: tuple(b.standing_id for b in bs)

    if permits and forbids:
        return Verdict(UNRESOLVED, CONFLICT,
                       "two independent live authorities conflict",
                       names(permits),
                       tuple((x, "prohibits the class") for x in names(forbids)))
    if permits:
        return Verdict(LICENSED, PERMISSION,
                       "an independent live authority covers it",
                       names(permits), blocked)
    if forbids:
        return Verdict(REFUSED, PROHIBITION,
                       "an independent live authority prohibits it",
                       (),
                       tuple((x, "prohibits the class") for x in names(forbids))
                       + blocked)
    if covering(case, iv, std):
        return Verdict(UNRESOLVED, DEFEATED,
                       "every covering basis is defeated", (), blocked)
    return Verdict(UNRESOLVED, NO_BASIS,
                   "no basis covers this intervention class")


def defeated_citation(case: en.RichCarrollCase, iv: en.Intervention) -> bool:
    """The record says something about this class and none of it licenses the act.

    The diagnostic the third verdict value would otherwise have carried. It is a
    predicate rather than a status because the agent's options are the same
    either way: `Unresolved` authorizes nothing, whichever ground it rests on.
    """
    return prospective_license(case, iv).ground == DEFEATED


def temporal_priority_license(case: en.RichCarrollCase,
                              iv: en.Intervention) -> bool:
    """The rule the prompt names as too weak: a live covering basis, and earlier.

    Kept so the prosecution can run both on the laundering fixture and show them
    disagreeing, which is the only way to say that the counterfactual condition
    is doing work.
    """
    std = case.history().std(iv.tau - 1)
    ok, _ = authority(case, iv, std, "permit")
    return bool(ok)


# ------------------------------------------------------------- succession


def uptake_events(case: en.RichCarrollCase) -> tuple:
    """`Uptake(a)`: the events across which the value standing changed.

    A reason is not a stance and a value revision is not an operative revision;
    this reads the value projection alone and is the third of the three.
    """
    h = case.history()
    out = []
    for a in h.norm_events():
        if en.value_standing(h.std(a.tau - 1)) != en.value_standing(h.std(a.tau)):
            out.append(a)
    return tuple(out)


def survives_excision(case: en.RichCarrollCase, event_id: str,
                      episode: Optional[str]) -> bool:
    """Is the event still admitted once the influence episode is removed?

    An event survives exactly when its authority, its derivation's leaves and
    the standings it writes to are all still there — which is the cascade
    Reflective Integrity computes, not a separate condition.
    """
    if episode is None:
        return True
    survivors = en.excise(case, en.ancestry(case, episode)).norm_events()
    return event_id in {a.id for a in survivors}


def legitimate_succession(case: en.RichCarrollCase, event_id: str,
                          episode: Optional[str] = None) -> Verdict:
    """`LegitimateSuccession_t(x, x')` for the event that performed it.

    The event is in the record, so Reflective Integrity already decided it was
    well-formed at its own time: it named an active `PAuth` at the strict
    pre-state and its derivation's leaves were on the ledger. Two things are
    added, and the second is the one the prosecution forced.

    The authority the event named must survive removal of the influence
    episode. And **the event itself** must survive it. The first alone is not
    enough: a person's own standing revision authority is seeded, so it survives
    every excision, and a revision reached entirely on manipulated grounds would
    inherit it. `PROSECUTION.md` §2 carries the fixture that killed the weaker
    version — two trajectories to the same cognitive endpoint, which the weaker
    version could not tell apart.
    """
    h = case.history()
    matches = [a for a in h.norm_events() if a.id == event_id]
    if not matches:
        return Verdict(UNRESOLVED, NO_BASIS, "no such event in the record")
    a = matches[0]
    if h.wf_violations(a):
        return Verdict(UNRESOLVED, DEFEATED, "the event was not well-formed")
    if not independent(case, a.schema_ref, episode, a.tau):
        return Verdict(UNRESOLVED, DEFEATED,
                       "the authority it named does not survive the episode",
                       (), ((a.schema_ref, "not independent"),))
    if not survives_excision(case, event_id, episode):
        return Verdict(UNRESOLVED, DEFEATED,
                       "the revision has no ground outside the influence episode",
                       (), ((event_id, "does not survive excision"),))
    return Verdict(LICENSED, PERMISSION,
                   "an independent authority licensed the revision",
                   (a.schema_ref,))


def authority_only_succession(case: en.RichCarrollCase, event_id: str,
                              episode: Optional[str] = None) -> Verdict:
    """The version of the succession clause the prosecution rejected.

    Kept beside the survivor so the two can be run on the same fixture and the
    disagreement exhibited rather than described.
    """
    h = case.history()
    matches = [a for a in h.norm_events() if a.id == event_id]
    if not matches:
        return Verdict(UNRESOLVED, NO_BASIS, "no such event in the record")
    a = matches[0]
    if independent(case, a.schema_ref, episode, a.tau):
        return Verdict(LICENSED, PERMISSION, "the named authority survives",
                       (a.schema_ref,))
    return Verdict(UNRESOLVED, DEFEATED, "the named authority does not survive")


# ------------------------------------------------ the two dictatorship tests


def final_approval(case: en.RichCarrollCase, iv: en.Intervention,
                   bridge: Mapping) -> bool:
    """The resulting parameterization's specification has standing at the end."""
    return theta_has_standing(case, iv.theta_after, bridge, None)


def initial_disapproval(case: en.RichCarrollCase, iv: en.Intervention,
                        bridge: Mapping) -> bool:
    """The prior parameterization's specification had standing before the act."""
    return theta_has_standing(case, iv.theta_before, bridge, iv.tau - 1)
