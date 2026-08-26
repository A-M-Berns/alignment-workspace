"""The realization: a Reflective Integrity record proposes an edit sequence.

```text
abstract               realized by
---------------------  -----------------------------------------------------
occurrence             a standing id — a seed id, or `@s{tau}.{i}`
occurrence index       tau, which the id already carries
sort                   PAuth and PProto are authority; PValue, PForce and PCmt
                       are norm
edit                   a NormEvent, frozen with its effect
grounds                schemaRef, plus the authority-sorted Supersede targets
                       where the event issues
dispose                targetsN(effect)
issue                  the fresh ids, with their payloads
input        I         the settlements the event's reason leaves draw on
exercise     X         the author and the derivation's leaves
scope                  a PProto ground's `covers`, where there is one
alpha                  the episodes currently doubted
```

**The challenge operator is gone from the headline.** Where the previous pass
asked whether an event survives a replay of the record with an episode's
settlements voided, this asks whether the event's *declared input* draws on a
doubted episode. Two consequences, and both are improvements.

The pathologies go with it. Excision was neither monotone nor composable because
it re-evaluated an evolving state; a declared-input test is evaluated once, at
the edit, and the earlier surprise reappears in an intelligible place — a
stricter audit context can leave *more* in force, because the edit it
invalidates was a revocation.

And a real over-refusal goes with it. Under challenge survival, an edit that
would not have happened but for an argument was scored dependent on that
argument. Under the declared-input test it is valid if prior authority permitted
it given that input, which is what `office.persuasion` is about.

**Where the realization is thin, and it is named rather than hidden.** `PAuth`
carries a `SchemaCode` and no domain, so the RI realization's `permit` is the
identity except where a `PProto` ground supplies a `covers` set. A record whose
authority is a bare `PAuth` therefore satisfies **H4** vacuously, and
`office.unauthorized_scope` is where the hypothesis has teeth.
"""
from __future__ import annotations

from dataclasses import replace
from typing import Mapping, Optional

import ri_core as ri
from standing import PValue

import enrichment as en

import replay as rp


def sort_of(payload) -> str:
    """`PAuth` and `PProto` govern; `PValue`, `PForce` and `PCmt` are governed."""
    return rp.AUTHORITY if isinstance(payload, (ri.PAuth, ri.PProto)) else rp.NORM


def occ_of(history: ri.History, x: str, seed_index: Mapping) -> rp.Occ:
    """The occurrence a standing id names.

    A seed id is a base occurrence; `@s{tau}.{i}` is the occurrence the edit at
    `tau` issued at index `i`. The identifier scheme already carries occurrence
    identity, which is why no side condition is needed for freshness.
    """
    if x in seed_index:
        i, payload = seed_index[x]
        return rp.Occ(rp.BASE_TIME, i, sort_of(payload))
    tau, idx = _parse(x)
    st = history.std(tau).get(x)
    return rp.Occ(tau, idx, sort_of(st.payload) if st else rp.AUTHORITY)


def _parse(x: str) -> tuple:
    body = x[len(ri.MINTED_PREFIX) + 1:]
    tau, idx = body.split(".")
    return int(tau), int(idx)


def _roles(history: ri.History, a: ri.NormEvent, seed_index):
    """`(grounds, dispose, issue)` for one event."""
    eff = history.effect(a)
    ctx = ri.ctx_of(a)
    occ = lambda x: occ_of(history, x, seed_index)
    lic = frozenset({occ(a.schema_ref)})
    if isinstance(eff, ri.Transfer):
        # Custody, not authority: `applyEffect` is the identity on a Transfer and
        # the abstract state has no holder field. Who is answerable is the
        # accountability interface's question and is deliberately not this one.
        return lic, frozenset(), ()
    alpha = eff.alpha
    fresh = tuple(ri.fresh_n(ctx, eff))
    issue = tuple((sort_of(p), p) for p in _payloads(alpha))
    if isinstance(alpha, ri.Supersede):
        targets = frozenset(occ(x) for x in alpha.X)
        parents = frozenset(o for o in targets if o.sort == rp.AUTHORITY) \
            if fresh else frozenset()
        return lic | parents, targets, issue
    if isinstance(alpha, ri.Create):
        return lic, frozenset(), issue
    return lic, frozenset(), ()


def _payloads(alpha) -> tuple:
    if isinstance(alpha, (ri.Create, ri.Supersede)):
        return tuple(alpha.K)
    return ()


def declared_input(case: en.RichCarrollCase, a: ri.NormEvent) -> frozenset:
    """The settlements this event's reasons draw on. Its `I`.

    Read forward off the reason ledger. What makes this a *declared* input is
    that the record says it: an event whose authorization actually turned on
    something its derivation does not cite is a record that fails **H5**, not a
    case the interface silently accepts.
    """
    h = case.history()
    by_id = {e.id: e for e in h.reasons()}
    out = set()
    for leaf in a.derivation.leaves:
        r = by_id.get(leaf)
        if r is not None:
            out |= set(r.s_L)
    return frozenset(out)


def episode_settlements(case: en.RichCarrollCase, episode: str) -> frozenset:
    """Every settlement in an episode's ancestry class."""
    out = en.settlement_ancestors(case, case.episode_seeds(episode))
    for other in en.ancestry(case, episode):
        out |= en.settlement_ancestors(case, case.episode_seeds(other))
    return out


def build(case: en.RichCarrollCase, base: Optional[frozenset] = None,
          doubted: Optional[Mapping] = None) -> rp.Process:
    """The proposal a record makes.

    `doubted` maps an audit context to the episodes it doubts; the default gives
    one context doubting every declared episode, and one doubting none.
    """
    h = case.history()
    seed_index = {x: (i, st.payload)
                  for i, (x, st) in enumerate(sorted(h.seed.std0.items()))}
    occ = lambda x: occ_of(h, x, seed_index)

    base_occs = frozenset(occ(x) for x in h.seed.std0)
    content = {occ(x): st.payload for x, st in h.seed.std0.items()}

    episodes = tuple(sorted({e for _, e in case.settlement_episodes
                             if e is not None}))
    if doubted is None:
        doubted = {"alpha:trusting": frozenset(),
                   "alpha:audited": frozenset(episodes)}
    doubted = {k: frozenset(v) for k, v in doubted.items()}
    tainted = {k: frozenset().union(frozenset(),
                                    *[episode_settlements(case, e) for e in v])
               for k, v in doubted.items()}

    edits = []
    for a in h.norm_events():
        grounds, dispose, issue = _roles(h, a, seed_index)
        edits.append(rp.Edit(
            at=a.tau, grounds=grounds, dispose=dispose, issue=issue,
            input=declared_input(case, a),
            exercise=(a.author, frozenset(a.derivation.leaves)),
            scope=_scope(h, a, seed_index, content),
            request=(a.schema_ref, _freeze(a.wit)),
            label=a.id))

    def covers_of(o):
        payload = content.get(o)
        term = getattr(payload, "term", None)
        return frozenset(getattr(term, "covers", ())) if term is not None else None

    def permit(state, e) -> bool:
        """`PAuth` carries no domain, so this bites only on a `PProto` ground."""
        for g in e.grounds:
            c = covers_of(g)
            if c is not None and e.scope and not (e.scope <= c):
                return False
        return True

    def prov_ok(alpha, e) -> bool:
        return not (frozenset(e.input) & tainted.get(alpha, frozenset()))

    def valid(alpha, state, e) -> bool:
        return (e.grounds <= rp.auth(state) and permit(state, e)
                and prov_ok(alpha, e))

    def view(alpha, i):
        return (base_occs, tuple(e.declared() for e in edits[:i]),
                tainted.get(alpha, frozenset()))

    for e in edits:
        content.update(e.content())

    return rp.Process(base_occs, tuple(edits), valid, tuple(sorted(doubted)),
                      permit, prov_ok, view, content)


def _freeze(w):
    if isinstance(w, (set, frozenset)):
        return frozenset(_freeze(x) for x in w)
    if isinstance(w, (list, tuple)):
        return tuple(_freeze(x) for x in w)
    return w


def _scope(history, a, seed_index, content) -> frozenset:
    """The intervention class an event purports to act in, where it declares one.

    A record whose authorities are bare `PAuth` declares none, and the permit
    relation is then vacuous on it — stated in the module docstring rather than
    papered over.
    """
    return frozenset()


def threat(case: en.RichCarrollCase, alpha: str,
           doubted: Optional[Mapping] = None) -> dict:
    """The influences an audit context is asked to see.

    One per doubted episode, reaching the edits whose declared input draws on it.
    A record's own episodes make coverage true by construction, which is the
    ceiling on self-certification: a recognizer worried about an influence the
    record does not record must supply its own threat class, against which the
    record may simply fail.
    """
    p = build(case, doubted=doubted)
    eps = doubted[alpha] if doubted else \
        ({e for _, e in case.settlement_episodes if e is not None}
         if alpha.endswith("audited") else set())
    out = {}
    for e in eps:
        sett = episode_settlements(case, e)
        out[f"xi:{e}"] = frozenset(
            ed.at for ed in p.edits if frozenset(ed.input) & sett)
    return out


def content_of(p: rp.Process, o: rp.Occ):
    return p.contents().get(o)


def relabel(case: en.RichCarrollCase, sigma: Mapping) -> en.RichCarrollCase:
    """Rename object-level content everywhere it can be written, record included."""
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
