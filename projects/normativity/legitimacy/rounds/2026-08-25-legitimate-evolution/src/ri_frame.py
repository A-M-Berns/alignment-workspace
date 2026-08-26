"""Extraction: a Reflective Integrity record yields a trace and a semantics.

```text
raw record  --extract_alpha-->  (base, trace, auth, Valid)  --replay-->  L_t
```

The extraction is the realization boundary, and it is where the substantive
factorization claim now lives. The kernel's own determinism — same base, same
trace, same validity relation, same replay — is a fold congruence and is
definitional. What is not definitional is that **the raw record determines the
trace and the semantics through what it declares**, and a record can fail it two
ways: by producing a different trace, or by producing a different validity
relation. `cases.partial_effect_pair` is the first and `office.hidden_reading_pair`
the second.

```text
occurrence   a seed standing, or the standing `@s{tau}.{i}` an event minted
position     the event's index in tau order — identity, not tau itself
grounds      schemaRef, plus the authority-sorted Supersede targets where it issues
dispose      targetsN(effect)                slots   how many fresh ids
auth         PAuth and PProto                (a predicate; see below)
input        the settlements the event's reason leaves draw on
alpha        the episodes currently doubted
```

**`auth` is a predicate and not a partition.** Reflective Integrity happens to
make the two disjoint — a payload is one constructor or another — so no record
here exhibits an occurrence that both governs and is governed. That is a fact
about the architecture, not a requirement of the interface, and
`office.content_sensitive_jurisdiction` is where a norm participates in a
permission judgment without being an authority.

**Permission is thin here and the round says so.** `PAuth` carries a
`SchemaCode` and no domain, so jurisdiction bites only where a `PProto` ground
supplies `covers`. `PRIORITIES.md` item 67 is the repair and this pass does not
attempt it.
"""
from __future__ import annotations

from dataclasses import replace
from typing import Mapping, Optional

import ri_core as ri
from standing import PValue

import enrichment as en

import replay as rp


def is_authority(payload) -> bool:
    return isinstance(payload, (ri.PAuth, ri.PProto))


def declared_input(case: en.RichCarrollCase, a: ri.NormEvent) -> frozenset:
    """The settlements this event's reasons draw on: its descriptive provenance.

    Read forward off the reason ledger. An event whose authorization actually
    turned on something its derivation does not cite is a record that fails
    extraction factorization, not a case the interface silently accepts.
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
    out = en.settlement_ancestors(case, case.episode_seeds(episode))
    for other in en.ancestry(case, episode):
        out |= en.settlement_ancestors(case, case.episode_seeds(other))
    return out


def episodes(case: en.RichCarrollCase) -> tuple:
    return tuple(sorted({e for _, e in case.settlement_episodes if e is not None}))


def contexts(case: en.RichCarrollCase) -> tuple:
    return ("alpha:audited", "alpha:trusting")


def build(case: en.RichCarrollCase, alpha: str = "alpha:audited",
          doubted: Optional[frozenset] = None) -> rp.Frame:
    """Extract a frame from a record at one audit context."""
    h = case.history()
    if doubted is None:
        doubted = frozenset(episodes(case)) if alpha.endswith("audited") \
            else frozenset()
    tainted = frozenset().union(frozenset(),
                                *[episode_settlements(case, e) for e in doubted])

    seed = sorted(h.seed.std0.items())
    occ_of, content = {}, {}
    base = []
    for i, (x, st) in enumerate(seed):
        o = rp.Occ(rp.BASE, i)
        occ_of[x], content[o] = o, st.payload
        base.append(o)

    events = list(h.norm_events())
    trace = []
    for t, a in enumerate(events):
        eff = h.effect(a)
        ctx = ri.ctx_of(a)
        fresh = tuple(ri.fresh_n(ctx, eff))
        lic = frozenset({occ_of[a.schema_ref]}) if a.schema_ref in occ_of \
            else frozenset()
        if isinstance(eff, ri.Transfer):
            grounds, dispose, payloads = lic, frozenset(), ()
        else:
            alpha_eff = eff.alpha
            payloads = tuple(alpha_eff.K) if isinstance(
                alpha_eff, (ri.Create, ri.Supersede)) else ()
            if isinstance(alpha_eff, ri.Supersede):
                targets = frozenset(occ_of[x] for x in alpha_eff.X
                                    if x in occ_of)
                parents = frozenset(o for o in targets
                                    if is_authority(content.get(o))) \
                    if fresh else frozenset()
                grounds, dispose = lic | parents, targets
            elif isinstance(alpha_eff, ri.Create):
                grounds, dispose = lic, frozenset()
            else:
                grounds = lic
                dispose = frozenset()
        for j, p in enumerate(payloads):
            o = rp.Occ(t, j)
            occ_of[fresh[j]] = o
            content[o] = p
        trace.append(rp.Edit(
            grounds=grounds, dispose=dispose, issues=tuple(payloads),
            declared=(declared_input(case, a), a.author, _freeze(a.wit),
                      a.schema_ref),
            label=a.id))
    trace = tuple(trace)

    def auth(o) -> bool:
        return is_authority(content.get(o))

    def covers_of(o):
        term = getattr(content.get(o), "term", None)
        return frozenset(getattr(term, "covers", ())) if term is not None else None

    def permit(state, e) -> bool:
        """Jurisdiction where a `PProto` ground declares one, and nothing else."""
        for g in e.grounds:
            c = covers_of(g)
            if c is not None and c == frozenset():
                return False
        return True

    def valid(state, e) -> bool:
        if not e.grounds <= frozenset(o for o in state if auth(o)):
            return False
        alters = bool(e.dispose & state) or bool(e.issues)
        if alters and not e.grounds:
            return False
        if frozenset(e.declared[0]) & tainted:
            return False
        return permit(state, e)

    f = rp.Frame(frozenset(base), trace, auth, valid)
    object.__setattr__(f, "content", content)
    object.__setattr__(f, "occ_of", occ_of)
    return f


def norms(f: rp.Frame, state) -> frozenset:
    """The enforcement projection: what is governed rather than what governs."""
    return frozenset(o for o in state if not f.auth(o))


def names(f: rp.Frame, occs) -> set:
    out = set()
    for o in occs:
        p = f.content.get(o)
        if isinstance(p, PValue):
            out.add(p.spec_id)
        elif isinstance(p, ri.PProto):
            out.add(getattr(p.term, "id", str(p.term)))
        elif isinstance(p, ri.PAuth):
            out.add(p.code.name)
        elif isinstance(p, ri.PForce):
            out.add(str(p.clause))
        else:
            out.add(str(p))
    return out


def _freeze(w):
    if isinstance(w, (set, frozenset)):
        return frozenset(_freeze(x) for x in w)
    if isinstance(w, (list, tuple)):
        return tuple(_freeze(x) for x in w)
    return w


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


def extraction_agrees(a: en.RichCarrollCase, b: en.RichCarrollCase,
                      alpha: str = "alpha:trusting") -> tuple:
    """**Extraction factorization**, checked between two records.

    Same declared data must give the same trace. Returns the first position at
    which the extracted edits differ, or the empty tuple.

    This is where hidden-state noninterference actually lives. The kernel's own
    determinism is a fold congruence; what can fail is that a record's effect or
    verdict turns on something the record does not declare.
    """
    fa, fb = build(a, alpha), build(b, alpha)
    if fa.base != fb.base:
        return (("different bases",),)
    if len(fa.trace) != len(fb.trace):
        return (("different lengths", len(fa.trace), len(fb.trace)),)
    for t, (x, y) in enumerate(zip(fa.trace, fb.trace)):
        if x.declared != y.declared:
            return ()
        if (x.grounds, x.dispose, x.issues) != (y.grounds, y.dispose, y.issues):
            return (("effect differs on equal declarations", t),)
    return ()


def declared_data(case: en.RichCarrollCase, alpha: str = "alpha:trusting") -> tuple:
    """What extraction is allowed to read: per event, its declared part."""
    f = build(case, alpha)
    return tuple((e.grounds, e.declared) for e in f.trace)
