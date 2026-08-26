"""The realization: a Reflective Integrity record is a succession frame.

```text
abstract               realized by
---------------------  -----------------------------------------------------
authority              StandingId
exercise               a NormEvent, under one of two identities (below)
affected               targetsN(effect) — what the event acts on
parents                the Supersede targets where it issues, a Transfer's
                       subject, and nothing for a Create
tgt                    the fresh ids, or a Transfer's subject
lic                    schemaRef
rank / when            tau
base                   dom(Std_0) — the seed
live[s]                the Active standings at s
challenge              an influence episode's ancestry class
Chal(q)                the events whose derivation reasons from a challenged
                       settlement, read off the reason ledger, not off the replay
q |= x                 the standing arises in the excised replay carrying the
                       payload the original gives it
q |= t                 see below
account                AnsRoot        ends/opens  Disposes/MINT   answered  Closed
```

**`Chal` is read forward off the reason ledger and stability backward off the
replay.** Defining `Chal(q)` as the non-survivors would make **L4** true by
stipulation and establish nothing about the challenge operator.

## Two exercise identities, and why the choice does not remove a hypothesis

```text
identity = "event"    q |= t  iff the event id is admitted in the excised replay
identity = "effect"   q |= t  iff it is admitted *and produces the same effect*
```

The first pass used `"event"` and found that **L3** then needs the record's
schemas to be pre-state-blind — an event can survive and mint the same
identifier carrying a different payload, which is the Carroll round's `C28`.

Prosecuting the map rather than the axiom shows the hypothesis **moves rather
than vanishing**. Under `"effect"` a differently-acting event is a different
exercise, so L3 holds outright; but an event whose effect changes in *one* of its
components can leave another component's authority untouched, and then the
authority survives while no exercise of the frame does — which refutes **L3'**.
`cases.partial_effect_case` is that record.

Both hypotheses are discharged by the same record-level condition, so
pre-state-blindness is **not** an artefact of a coarse realization map: it is
what makes the challenge operator's action on effects determinate, and it is
needed under either identity. The identity is therefore chosen on semantics
rather than to shed a hypothesis, and `"effect"` is the default because an act
that does something else is not the same exercise.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Mapping, Optional

import ri_core as ri
from standing import PValue

import enrichment as en
import legitimacy as lg

import frame as fr


EVENT = "event"
EFFECT = "effect"


@dataclass(frozen=True)
class Exercise:
    """An authority-changing act. `effect` is `None` under event identity."""

    event_id: str
    effect: object = None

    def __str__(self) -> str:
        return self.event_id if self.effect is None else \
            f"{self.event_id}/{_effect_key(self.effect)}"


def _effect_key(eff) -> str:
    if isinstance(eff, ri.Transfer):
        return f"transfer({eff.x}->{eff.to})"
    alpha = eff.alpha
    if isinstance(alpha, ri.Create):
        return f"create{tuple(map(_payload_key, alpha.K))}"
    if isinstance(alpha, ri.Supersede):
        return (f"supersede({tuple(sorted(alpha.X))}"
                f"->{tuple(map(_payload_key, alpha.K))})")
    return f"setstatus({tuple(sorted(alpha.X))},{alpha.s[0]})"


def _payload_key(p) -> str:
    if isinstance(p, PValue):
        return f"value:{p.spec_id}"
    if isinstance(p, ri.PCmt):
        return f"cmt:{p.role}:{p.content}"
    if isinstance(p, ri.PAuth):
        return f"auth:{p.code.name}"
    if isinstance(p, ri.PProto):
        return f"proto:{getattr(p.term, 'id', p.term)}"
    return repr(p)


def _roles(history: ri.History, a: ri.NormEvent):
    """`(affected, parents, tgt)` for one event, in the abstract sense.

    `parents` is where the entitlement is inherited, and it is not
    `targetsN(effect)`. A `Supersede` that issues inherits from what it
    supersedes; a `Supersede` with no payloads issues nothing and so has nothing
    to inherit; a `Create` inherits from its licence alone; a `Transfer` re-issues
    the object it acts on and so has it as a parent.

    That last distinction is what lets a record express a cleanup: revoking an
    illegitimate standing and separately creating a replacement is two events,
    and the `Create` has no parents at all.
    """
    eff = history.effect(a)
    ctx = ri.ctx_of(a)
    if isinstance(eff, ri.Transfer):
        one = frozenset({eff.x})
        return one, one, one
    alpha = eff.alpha
    fresh = frozenset(ri.fresh_n(ctx, eff))
    if isinstance(alpha, ri.Supersede):
        X = frozenset(alpha.X)
        return X, (X if fresh else frozenset()), fresh
    if isinstance(alpha, ri.Create):
        return frozenset(), frozenset(), fresh
    return frozenset(alpha.X), frozenset(), frozenset()


def challenged_exercises(case: en.RichCarrollCase, episode: str) -> frozenset:
    """`Chal(q)`: the event ids whose derivation reasons from a challenged
    settlement.

    Read forward off the reason ledger rather than backward off the replay. An
    event can be in `Chal(q)` and still be admitted by a defective operator;
    **L4** is the claim that this one is not.
    """
    sett = en.settlement_ancestors(case, case.episode_seeds(episode))
    for other in en.ancestry(case, episode):
        sett |= en.settlement_ancestors(case, case.episode_seeds(other))
    h = case.history()
    by_id = {e.id: e for e in h.reasons()}
    out = set()
    for a in h.norm_events():
        for leaf in a.derivation.leaves:
            r = by_id.get(leaf)
            if r is not None and frozenset(r.s_L) & sett:
                out.add(a.id)
    return frozenset(out)


def _payload_at_birth(history: ri.History, x: str):
    for t in range(history.now + 1):
        st = history.std(t).get(x)
        if st is not None:
            return st.payload
    return None


def build(case: en.RichCarrollCase, base: Optional[frozenset] = None,
          identity: str = EFFECT):
    """The frame and the account layer a record realizes.

    `base` defaults to the seed; a recognizing process that accepts more passes
    its own set, which is the whole of what "recognized base" means here.
    `identity` selects the exercise individuation the module docstring
    prosecutes.
    """
    h = case.history()
    events = {a.id: a for a in h.norm_events()}
    token = {aid: Exercise(aid, h.effect(a) if identity == EFFECT else None)
             for aid, a in events.items()}

    affected, parents, tgt, lic, rank, when = {}, {}, {}, {}, {}, {}
    authorities = set(h.seed.std0)
    for aid, a in events.items():
        t = token[aid]
        af, pa, tg = _roles(h, a)
        affected[t], parents[t], tgt[t], lic[t] = af, pa, tg, a.schema_ref
        rank[t], when[t] = 2 * a.tau - 1, a.tau
        authorities |= af | pa | tg
    for x in h.seed.std0:
        rank[x] = 0
    for aid, a in events.items():
        for y in tgt[token[aid]] - affected[token[aid]]:
            rank[y] = 2 * a.tau
    for x in authorities:
        rank.setdefault(x, 0)

    episodes = tuple(sorted({e for _, e in case.settlement_episodes
                             if e is not None}))
    by_episode = {q: challenged_exercises(case, q) for q in episodes}
    chal = {q: frozenset(token[aid] for aid in ids if aid in token)
            for q, ids in by_episode.items()}
    born = {x: _payload_at_birth(h, x) for x in authorities}
    replays = {q: en.excise(case, en.ancestry(case, q)) for q in episodes}

    def stable(q, u) -> bool:
        ex = replays[q]
        if isinstance(u, Exercise):
            survivors = {b.id: b for b in ex.norm_events()}
            b = survivors.get(u.event_id)
            if b is None:
                return False
            if u.effect is None:
                return True
            try:
                return ex.effect(b) == u.effect
            except ri.WFError:
                return False
        if u in h.seed.std0:
            return True
        for t in range(ex.now + 1):
            st = ex.std(t).get(u)
            if st is not None:
                return st.payload == born[u]
        return False

    times = tuple(range(h.now + 1))
    live = {s: frozenset(x for x, st in h.std(s).items() if st.kind == "Active")
            for s in times}

    f = fr.Frame(frozenset(authorities), frozenset(token.values()), affected,
                 parents, tgt, lic, rank,
                 base if base is not None else frozenset(h.seed.std0),
                 episodes, chal, stable, when, live, times)

    roots = {q.id: q for q in h.roots()}
    ends = {token[aid]: frozenset(q.id for q in h.roots(a.tau - 1)
                                  if h.disposes(a, q))
            for aid, a in events.items()}
    opens = {token[aid]: frozenset(q.id for q in h.mint(a))
             for aid, a in events.items()}
    acc = fr.Accounts(frozenset(roots),
                      {qid: q.debtor for qid, q in roots.items()},
                      ends, opens,
                      {qid: q.subject for qid, q in roots.items()},
                      lambda qid: h.closed(roots[qid]))
    return f, acc


# ------------------------------------------------- the realization theorems


def prestate_blind(case: en.RichCarrollCase) -> bool:
    """Does every event's effect depend on its witness alone?

    Checked rather than declared: each schema is rerun against a truncated
    pre-state and the effects compared. This is the condition that discharges
    **L3** under event identity and **L3'** under effect identity — the same
    condition either way, which is the round's answer to whether
    pre-state-blindness is an artefact of the map.
    """
    h = case.history()
    for a in h.norm_events():
        st = h.std(a.tau - 1).get(a.schema_ref)
        if st is None or not isinstance(st.payload, ri.PAuth):
            return False
        real = h.prestate(a.tau)
        thin = ri.PreState((), (), (), a.tau)
        try:
            if st.payload.code.run(a.wit, real) != st.payload.code.run(a.wit, thin):
                return False
        except Exception:
            return False
    return True


def threat_from_episodes(case: en.RichCarrollCase) -> fr.ThreatModel:
    """The threat model a record's own declared episodes generate.

    One influence per episode, depending on the events the reason ledger says it
    brought about. **This is the honest ceiling of what a record can supply**:
    it makes coverage true by construction, and a recognizing process worried
    about an influence the record does not record must supply its own threat
    model, against which the record may fail. `COUNTERMODELS.md` §4.
    """
    episodes = tuple(sorted({e for _, e in case.settlement_episodes
                             if e is not None}))
    f, _ = build(case)
    return fr.ThreatModel(tuple(f"xi:{e}" for e in episodes),
                          {f"xi:{e}": f.chal[e] for e in episodes})


def content(history: ri.History, x: str, t: Optional[int] = None):
    """The object-level content a standing carries. Read by no clause of `|-`."""
    st = history.std(t).get(x)
    if st is None:
        return None
    p = st.payload
    if isinstance(p, ri.PCmt):
        return p.content
    if isinstance(p, PValue):
        return p.spec_id
    if isinstance(p, ri.PProto):
        return p.term
    return None


def content_map(case: en.RichCarrollCase) -> dict:
    h = case.history()
    return {x: content(h, x) for x in h.std()}


def classify(case: en.RichCarrollCase):
    """A consumer-supplied split of the frontier into authorities and norms.

    `PAuth` and `PProto` standings are what govern; `PValue` and `PForce`
    standings are what is governed by. The frame does not know the difference and
    is handed this by whoever wants a projection.
    """
    h = case.history()

    def kind(x: str) -> str:
        st = h.std().get(x) or h.std(0).get(x)
        if st is None:
            return "unknown"
        return "authority" if isinstance(st.payload, (ri.PAuth, ri.PProto)) \
            else "norm"
    return kind


def relabel_content(case: en.RichCarrollCase, sigma: Mapping) -> en.RichCarrollCase:
    """Rename object-level content everywhere it can be written, record included.

    Seed payloads and the witnesses of the record's own events, because a
    `PValue` reaching standing does so through the witness a `Supersede` schema
    reads. Ids, `tau`, authorship, schema references and settlement provenance
    are untouched, so the only thing that moves is what the standings say.
    """
    def m(payload):
        if isinstance(payload, PValue) and payload.spec_id in sigma:
            return PValue(sigma[payload.spec_id])
        if isinstance(payload, ri.PCmt) and payload.content in sigma:
            return ri.PCmt(payload.role, sigma[payload.content])
        return payload

    std0 = {k: replace(v, payload=m(v.payload))
            for k, v in case.seed.std0.items()}
    seed = ri.Seed(case.seed.p0, std0, case.seed.roots0)
    steps = []
    for step in case.steps:
        if isinstance(step, ri.Norm):
            steps.append(ri.Norm(replace(step.a, wit=_map_wit(step.a.wit, m))))
        else:
            steps.append(step)
    return en.RichCarrollCase(case.dr_mdp, tuple(steps), seed, case.narrative,
                              case.settlement_episodes, case.interventions,
                              case.fact_settlements)


def _map_wit(wit, m):
    if isinstance(wit, tuple):
        return tuple(_map_wit(w, m) for w in wit)
    if isinstance(wit, (set, frozenset)):
        return frozenset(_map_wit(w, m) for w in wit)
    return m(wit)
