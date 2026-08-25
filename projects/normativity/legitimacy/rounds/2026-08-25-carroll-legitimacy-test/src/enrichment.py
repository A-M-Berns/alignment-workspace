"""The enriched case, the projection that forgets it, and the excision.

An enriched case is a DR-MDP together with a Reflective Integrity record and one
bridge object. The bridge is the *authenticated interaction provenance* of the
settlements: which settlements were produced by interactions an AI influence
episode caused. It is declared at the settlement level and nowhere else — every
further consequence of an excision is computed by Reflective Integrity's own
admission rules rather than annotated.

```text
Q_DR : RichCarrollCase -> DRMDP          returns the field, unchanged
```

Adding history cannot change `S`, `Theta`, `A`, `T` or `R`, because the DR-MDP
is a field and no operation in this module writes it. Two enriched cases can
therefore hold the same `DRMDP` value, which is what `test_projection.py`
asserts.

Nothing here introduces a historical event kind. `Settlement`, `ReasonOcc`,
`NormEvent` and `Response` are Reflective Integrity's, imported; a protocol is a
`PProto` payload, which the core already has; a value specification is the
vertical slice's `PValue`, imported.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Mapping, Optional, Sequence

import ri_core as ri
from standing import PValue, values_projection

import drmdp


# ------------------------------------------------------------- the protocol


@dataclass(frozen=True)
class Protocol:
    """A standing basis empowering an agent over a class of interventions.

    `covers` holds **structural intervention classes** — index triples into the
    DR-MDP's own declaration order — and never a label. A protocol therefore
    cannot say "exercise is good"; it can only say "this agent may move the
    reward parameterization along this edge of this DR-MDP under this
    condition". Relabelling the DR-MDP leaves every `covers` entry fixed, which
    is what makes the relabelling test a test rather than a restatement.
    """

    id: str
    agent: str
    covers: frozenset
    condition: frozenset = frozenset()
    polarity: str = "permit"          # "permit" | "forbid"
    domain: str = "reward-parameterisation"

    def __post_init__(self) -> None:
        assert self.polarity in ("permit", "forbid")


@dataclass(frozen=True)
class Intervention:
    """A candidate AI act, described by what it does in the DR-MDP.

    `tau` is the Reflective Integrity time at which it is performed, so the
    strict pre-state a license is read against is `tau - 1`. `episode` names the
    influence episode it belongs to — its causal ancestry class — and is what
    the counterfactual removes.
    """

    id: str
    agent: str
    action: object
    theta_before: object
    theta_after: object
    tau: int
    episode: Optional[str] = None
    facts: frozenset = frozenset()


def intervention_class(m: drmdp.DRMDP, iv: Intervention) -> tuple:
    """The structural fingerprint an authority can cover.

    Indices into `m.actions` and `m.thetas`, so the class survives relabelling
    and carries no narrative content.
    """
    return (m.actions.index(iv.action),
            m.thetas.index(iv.theta_before),
            m.thetas.index(iv.theta_after))


# ------------------------------------------------------------ the rich case


@dataclass(frozen=True)
class Narrative:
    """Labels. Read by report rendering and by nothing that returns a verdict."""

    name: str
    subject: str
    gloss: tuple = ()


@dataclass(frozen=True)
class RichCarrollCase:
    dr_mdp: drmdp.DRMDP
    steps: tuple                     # the RI steps, in order
    seed: ri.Seed
    narrative: Narrative
    settlement_episodes: tuple       # (settlement id, episode id) — the bridge
    interventions: tuple = ()
    fact_settlements: tuple = ()     # (settlement id, frozenset of fact tokens)

    def history(self) -> ri.History:
        h = ri.History(self.seed)
        for step in self.steps:
            h.append(step)
        return h

    def intervention(self, iid: str) -> Intervention:
        for iv in self.interventions:
            if iv.id == iid:
                return iv
        raise KeyError(iid)

    def episode_seeds(self, episode: str) -> frozenset:
        return frozenset(sid for sid, eid in self.settlement_episodes
                         if eid == episode)

    def episode_of(self, settlement_id: str):
        for sid, eid in self.settlement_episodes:
            if sid == settlement_id:
                return eid
        return None

    def refs_of(self, settlement_id: str) -> frozenset:
        for step in self.steps:
            if isinstance(step, ri.Settle) and step.s.id == settlement_id:
                return frozenset(step.s.refs)
        return frozenset()


def Q_DR(case: RichCarrollCase) -> drmdp.DRMDP:
    """The projection. It forgets the record and returns the field."""
    return case.dr_mdp


# ---------------------------------------------------------------- builder


class CaseBuilder:
    """Appends steps and records settlement provenance as it goes.

    Provenance is a fact about the act of appending inside an episode, not an
    annotation a caller adds afterwards, which is the same discipline the
    vertical slice's authenticated interaction provenance is under.
    """

    def __init__(self, dr_mdp: drmdp.DRMDP, seed: ri.Seed, narrative: Narrative):
        self.dr_mdp = dr_mdp
        self.seed = seed
        self.narrative = narrative
        self.steps: list = []
        self.settlement_episodes: list = []
        self.interventions: list = []
        self.fact_settlements: list = []
        self._episode: Optional[str] = None
        self._history = ri.History(seed)

    # -- episodes ---------------------------------------------------------

    def begin(self, episode: str) -> "CaseBuilder":
        self._episode = episode
        return self

    def end(self) -> "CaseBuilder":
        self._episode = None
        return self

    # -- the four record kinds -------------------------------------------

    def settle(self, sid: str, refs=frozenset(),
               establishes=frozenset()) -> "CaseBuilder":
        """`establishes` is what the settlement puts on the record as obtaining.

        A protocol's applicability condition is discharged from this set, so a
        condition an influence episode brought about is removed with it.
        """
        self._append(ri.Settle(ri.Settlement(sid, frozenset(refs))))
        self.settlement_episodes.append((sid, self._episode))
        if establishes:
            self.fact_settlements.append((sid, frozenset(establishes)))
        return self

    def reason(self, eid: str, s_V=frozenset(), s_L=frozenset(),
               target=None) -> "CaseBuilder":
        self._append(ri.Reason(ri.ReasonOcc(eid, frozenset(s_V), frozenset(s_L),
                                            target)))
        return self

    def norm(self, aid: str, schema_ref: str, author: str, wit=None,
             leaves=frozenset(), steps=frozenset(), concl="c") -> "CaseBuilder":
        d = ri.Derivation(concl=concl, leaves=frozenset(leaves),
                          steps=frozenset(steps))
        self._append(ri.Norm(ri.NormEvent(aid, d, schema_ref, wit, author)))
        return self

    def respond(self, rid: str, roots, cited=frozenset()) -> "CaseBuilder":
        self._append(ri.Respond(ri.Response(rid, frozenset(roots),
                                            frozenset(cited))))
        return self

    def declare(self, iv: Intervention) -> "CaseBuilder":
        self.interventions.append(iv)
        return self

    def _append(self, step) -> None:
        self._history.append(step)
        self.steps.append(step)

    # -- output ------------------------------------------------------------

    @property
    def now(self) -> int:
        return self._history.now

    def build(self) -> RichCarrollCase:
        return RichCarrollCase(self.dr_mdp, tuple(self.steps), self.seed,
                               self.narrative,
                               tuple(self.settlement_episodes),
                               tuple(self.interventions),
                               tuple(self.fact_settlements))


# ---------------------------------------------------------------- excision


VOID = "@@void"


def ancestry(case: RichCarrollCase, episode: Optional[str]) -> frozenset:
    """The intervention's causal ancestry class, as episodes.

    The counterfactual object is not one declared episode. An agent that runs
    its campaign as two episodes and cites the second would otherwise keep
    whatever the first installed. The closure is over the record's own
    settlement references: an episode is in the class when a settlement already
    in it refers to one of that episode's settlements.

    **The hypothesis this makes explicit.** The class is only as wide as the
    record's provenance. A second episode whose settlements record no reference
    to the first is, as far as the record can tell, causally unrelated to it,
    and the criterion will treat a basis installed in the first as independent.
    That is a completeness condition on the record, stated here rather than
    assumed: every settlement an episode caused refers to the settlement that
    caused it.
    """
    if episode is None:
        return frozenset()
    out, frontier = {episode}, [episode]
    while frontier:
        eid = frontier.pop()
        for sid in case.episode_seeds(eid):
            for ref in case.refs_of(sid):
                other = case.episode_of(ref)
                if other is not None and other not in out:
                    out.add(other)
                    frontier.append(other)
    return frozenset(out)


def established_facts(case: RichCarrollCase, history: ri.History,
                      t=None) -> frozenset:
    """What the record says obtains, read off the settlements it still holds."""
    present = {s.id for s in history.settlements(t)}
    return frozenset().union(frozenset(), *[toks for sid, toks
                                            in case.fact_settlements
                                            if sid in present])


def excise(case: RichCarrollCase, episodes) -> ri.History:
    """Replay the record with an influence episode's settlements removed.

    Each removed step is replaced by an inert settlement rather than deleted, so
    every surviving step keeps its `tau` and every minted standing id is
    unchanged — which is what makes "the same standing is still active" a
    statement one can check by identity.

    **The cascade is Reflective Integrity's, not ours.** Only the episode's own
    settlements are removed by declaration. A reason citing a removed settlement
    fails `WFStep(Reason)`; an event whose derivation cites that reason fails
    `G2`; an event naming a standing that event would have created fails `G4` or
    `G6`. Each such step is replaced in turn. Nothing decides what descends from
    what except the admission rules the record was written under.
    """
    drop = frozenset().union(*[case.episode_seeds(e) for e in episodes]) \
        if episodes else frozenset()
    out = ri.History(case.seed)
    removed = []
    for step in case.steps:
        tau = out.now + 1
        if isinstance(step, ri.Settle) and step.s.id in drop:
            out.append(ri.Settle(ri.Settlement(f"{VOID}{tau}", frozenset())))
            removed.append(step)
            continue
        try:
            out.append(_restamp(step))
        except ri.WFError:
            out.append(ri.Settle(ri.Settlement(f"{VOID}{tau}", frozenset())))
            removed.append(step)
    out.removed = tuple(removed)
    return out


def _restamp(step):
    """A step's `tau` is assigned by `append`; the record carries the payload."""
    if isinstance(step, ri.Settle):
        return ri.Settle(ri.Settlement(step.s.id, step.s.refs))
    if isinstance(step, ri.Reason):
        e = step.e
        return ri.Reason(ri.ReasonOcc(e.id, e.s_V, e.s_L, e.target))
    if isinstance(step, ri.Norm):
        a = step.a
        return ri.Norm(ri.NormEvent(a.id, a.derivation, a.schema_ref, a.wit,
                                    a.author))
    r = step.rho
    return ri.Respond(ri.Response(r.id, r.roots, r.cited))


# ------------------------------------------------------------ derived views


def protocols(std: Mapping) -> tuple:
    """`(standing id, Protocol, status)` for every standing carrying one."""
    return tuple((x, st.payload.term, st.kind)
                 for x, st in sorted(std.items())
                 if isinstance(st.payload, ri.PProto)
                 and isinstance(st.payload.term, Protocol))


def active_protocols(std: Mapping) -> tuple:
    return tuple((x, p) for x, p, kind in protocols(std) if kind == "Active")


def value_standing(std: Mapping) -> frozenset:
    """The value specifications with normative standing. Not `theta`."""
    return frozenset(spec for _, spec in values_projection(std))


def relabel_case(case: RichCarrollCase, smap, thmap, amap,
                 narrative: Narrative = None) -> RichCarrollCase:
    """Rename the DR-MDP's alphabets and the narrative. The record is untouched.

    Intervention classes are index triples, so they survive; the interventions'
    own `action` and `theta` fields are renamed with the DR-MDP.
    """
    m = drmdp.relabel(case.dr_mdp, smap, thmap, amap)
    ivs = tuple(replace(iv, action=amap[iv.action],
                        theta_before=thmap[iv.theta_before],
                        theta_after=thmap[iv.theta_after])
                for iv in case.interventions)
    return RichCarrollCase(m, case.steps, case.seed,
                           narrative or case.narrative,
                           case.settlement_episodes, ivs)
