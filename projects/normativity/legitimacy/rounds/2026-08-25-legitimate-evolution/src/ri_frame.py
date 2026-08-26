"""The realization: a Reflective Integrity record is a succession frame.

```text
abstract               realized by
---------------------  -----------------------------------------------------
authority              StandingId
exercise               NormEvent
src                    the Supersede targets, or a Transfer's subject
tgt                    the fresh ids, or a Transfer's subject
lic                    schemaRef
rank                   tau
base                   dom(Std_0) — the seed
challenge              an influence episode's ancestry class
Chal(q)                the events whose derivation reasons from a challenged
                       settlement, read off the reason ledger and not off the
                       replay
q |= x                 the standing arises in the excised replay carrying the
                       payload the original gives it
q |= a                 the event is admitted in the excised replay
account                AnsRoot
ends / opens           Disposes / MINT
answered               Closed
```

**`Chal` is read off the reason ledger and stability off the replay**, which are
two different computations over the record. That is deliberate: if `Chal(q)` were
defined as the non-survivors, **L4** would be true by stipulation and would
establish nothing about the challenge operator.

The realization satisfies **L3** only where the record's practical schemas are
pre-state-blind. `COUNTERMODELS.md` §2 carries the record that refutes it
otherwise, and it is the Carroll round's `C28` read as a statement about the
interface rather than about the criterion.
"""
from __future__ import annotations

from dataclasses import replace
from typing import Mapping, Optional

import ri_core as ri
from standing import PValue

import enrichment as en
import legitimacy as lg

import frame as fr


def _effect_kinds(history: ri.History, a: ri.NormEvent):
    """`(src, tgt)` for one event, in the abstract sense."""
    eff = history.effect(a)
    if isinstance(eff, ri.Transfer):
        return frozenset({eff.x}), frozenset({eff.x})
    if isinstance(eff, ri.Standing):
        alpha = eff.alpha
        fresh = frozenset(ri.fresh_n(ri.ctx_of(a), eff))
        if isinstance(alpha, ri.Supersede):
            return frozenset(alpha.X), fresh
        if isinstance(alpha, ri.Create):
            return frozenset(), fresh
    return frozenset(), frozenset()


def challenged_exercises(case: en.RichCarrollCase, episode: str) -> frozenset:
    """`Chal(q)`: the events whose derivation reasons from a challenged settlement.

    Read forward off the reason ledger — a leaf of the event's derivation draws
    on a settlement in the challenge's ancestry class — rather than backward off
    the replay. An event can be in `Chal(q)` and still be admitted by a defective
    operator; **L4** is the claim that this one is not.
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
    """The payload `x` carries when it first appears in a record."""
    for t in range(history.now + 1):
        st = history.std(t).get(x)
        if st is not None:
            return st.payload
    return None


def build(case: en.RichCarrollCase, base: Optional[frozenset] = None):
    """The frame and the account layer a record realizes.

    `base` defaults to the seed. A recognizing process that accepts more than
    the seed passes its own set, which is the whole of what "recognized base"
    means here.
    """
    h = case.history()
    events = {a.id: a for a in h.norm_events()}
    src, tgt, lic, rank = {}, {}, {}, {}
    authorities = set(h.seed.std0)
    for aid, a in events.items():
        s, g = _effect_kinds(h, a)
        src[aid], tgt[aid], lic[aid] = s, g, a.schema_ref
        rank[aid] = 2 * a.tau - 1
        authorities |= s | g
    for x in h.seed.std0:
        rank[x] = 0
    for aid, a in events.items():
        for y in tgt[aid] - src[aid]:
            rank[y] = 2 * a.tau

    episodes = tuple(sorted({e for _, e in case.settlement_episodes
                             if e is not None}))
    chal = {q: challenged_exercises(case, q) for q in episodes}
    born = {x: _payload_at_birth(h, x) for x in authorities}

    def stable(q, u) -> bool:
        if u in events:
            return lg.survives_excision(case, u, q)
        if u in h.seed.std0:
            return True
        ex = en.excise(case, en.ancestry(case, q))
        for t in range(ex.now + 1):
            st = ex.std(t).get(u)
            if st is not None:
                return st.payload == born[u]
        return False

    current = frozenset(x for x, st in h.std().items() if st.kind == "Active")
    f = fr.Frame(frozenset(authorities), frozenset(events), src, tgt, lic, rank,
                 base if base is not None else frozenset(h.seed.std0),
                 current, episodes, chal, stable)

    roots = {q.id: q for q in h.roots()}
    ends = {aid: frozenset(q.id for q in h.roots(a.tau - 1) if h.disposes(a, q))
            for aid, a in events.items()}
    opens = {aid: frozenset(q.id for q in h.mint(a)) for aid, a in events.items()}
    acc = fr.Accounts(frozenset(roots),
                      {qid: q.debtor for qid, q in roots.items()},
                      ends, opens,
                      {qid: q.subject for qid, q in roots.items()},
                      lambda qid: h.closed(roots[qid]))
    return f, acc


# ------------------------------------------------- the realization theorems


def prestate_blind(case: en.RichCarrollCase) -> bool:
    """Does every event's effect depend on its witness alone?

    Checked rather than declared: each event's schema is rerun against a
    truncated pre-state and the effects compared. A schema that reads the
    strict pre-state is exactly what refutes **L3**, and this is the hypothesis
    under which the realization theorem holds.
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


def content(history: ri.History, x: str, t: Optional[int] = None):
    """The object-level content a standing carries, or `None` where it carries none.

    Read for the non-lock-in witnesses and for the relabelling test, and by no
    clause of `LegitSucc`.
    """
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


def content_map(case: en.RichCarrollCase) -> dict:
    """What each standing says, for the relabelling check. Read by no clause."""
    h = case.history()
    return {x: content(h, x) for x in h.std()}
