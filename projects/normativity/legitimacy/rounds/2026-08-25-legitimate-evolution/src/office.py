"""The semantic layer, and a realization with no normative record in it.

A constitution charters offices; a gazette records acts. This module supplies
what `replay.py` deliberately does not: a **definition** of semantic validity,
built from a descriptive provenance view and a normative permission relation.

```text
ProvView_alpha(e)        what descriptively happened: which findings entered,
                         whether a signature was forged, whether the actor was
                         coerced
ProvComplete_alpha(e)    the view exposes every Xi-relevant dependency
Permit(L, e, r)          what those facts mean normatively: jurisdiction, scope,
                         whether forgery counts as an exercise, whether coercion
                         invalidates
```

```text
Valid_alpha(L, e)  :=  grounds(e) subset Auth(L)
                   and (changes(L,e) -> grounds(e) != {})
                   and ProvComplete_alpha(e)
                   and Permit(L, e, ProvView_alpha(e))
```

Validity is **defined**, not constrained. The previous formulation kept it
primitive and assumed three implications about it, leaving it free to reject an
edit that was grounded, permitted and provenance-adequate for no stated reason.
Nothing needed that freedom.

The split between the last two clauses is the point. Provenance is descriptive —
*did Bob argue, was this forged, was Alice coerced*. Permission is normative —
*is persuasion allowed, does forgery count as an exercise, may this office act on
this subject*. A constitution that permits persuasion records Bob's argument in
the view and permits the edit; the previous `ProvOK` could only refuse an
influence, which is why persuasion had to be an exception.

**This module imports `replay` and the standard library and nothing else.**
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Callable, Mapping, Optional

import replay as rp


ALL = frozenset({"d:all"})
FISCAL = frozenset({"d:fiscal"})
SAFETY = frozenset({"d:safety"})


@dataclass(frozen=True)
class Warrant:
    """An occurrence of authority: who holds it, over what."""

    name: str
    domain: frozenset = frozenset()
    holder: str = "Assembly"

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Policy:
    """An occurrence of norm. Its `bans` are read by `Permit`, never by the kernel."""

    name: str
    bans: frozenset = frozenset()

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Prov:
    """The descriptive provenance view of one act. No normative content."""

    findings: frozenset = frozenset()
    forged: bool = False
    coerced: bool = False
    complete: bool = True


@dataclass(frozen=True)
class Act:
    """One entry in the gazette.

    `inherits` defaults to the authority-sorted things it revokes; an act that
    cleans up rather than inheriting passes an explicit empty tuple.
    """

    under: Optional[str]
    revokes: tuple = ()
    grants: tuple = ()                 # ((name, domain-or-None, bans), ...)
    inherits: Optional[tuple] = None
    scope: frozenset = frozenset()
    prov: Prov = Prov()
    label: str = ""


@dataclass(frozen=True)
class Constitution:
    chartered: tuple                   # (name, domain-or-None, holder)
    acts: tuple
    doubted: Mapping = field(default_factory=dict)
    coercion_invalidates: bool = True
    hidden: object = None
    reads_hidden: bool = False


def contexts(c: Constitution) -> tuple:
    return tuple(sorted(c.doubted)) or ("alpha:0",)


def build(c: Constitution, alpha: Optional[str] = None) -> rp.Frame:
    """The frame a constitution and its gazette make, at one audit context."""
    alpha = alpha or contexts(c)[0]
    doubted = frozenset(c.doubted.get(alpha, ()))

    base, content, by_name = [], {}, {}
    for i, (name, domain, holder) in enumerate(c.chartered):
        o = rp.Occ(rp.BASE, i)
        base.append(o)
        content[o] = Warrant(name, frozenset(domain), holder) \
            if domain is not None else Policy(name)
        by_name[name] = o

    is_auth = {name: domain is not None for name, domain, _ in c.chartered}
    for a in c.acts:
        for name, domain, _ in a.grants:
            is_auth[name] = domain is not None

    trace = []
    for t, a in enumerate(c.acts):
        parents = a.inherits if a.inherits is not None else \
            tuple(w for w in a.revokes if is_auth.get(w))
        grounds = frozenset(
            ([by_name[a.under]] if a.under else [])
            + [by_name[w] for w in parents if w in by_name])
        dispose = frozenset(by_name[w] for w in a.revokes if w in by_name)
        for j, (name, domain, bans) in enumerate(a.grants):
            o = rp.Occ(t, j)
            content[o] = Warrant(name, frozenset(domain), _holder(c, a)) \
                if domain is not None else Policy(name, frozenset(bans))
            by_name[name] = o
        trace.append(rp.Edit(
            grounds=grounds, dispose=dispose,
            issues=tuple(content[rp.Occ(t, j)] for j in range(len(a.grants))),
            declared=(frozenset(a.scope), a.prov),
            label=a.label or f"act{t}"))
    trace = tuple(trace)

    def auth(o) -> bool:
        return isinstance(content.get(o), Warrant)

    def permit(state, e) -> bool:
        """What the descriptive facts mean here.

        Persuasion is permitted: a finding entering the act is not a defect.
        Forgery is not an exercise. Coercion invalidates or not, as the
        constitution declares. Jurisdiction is the intersection of the grounds'
        domains, and a live policy may ban a scope outright — which is where
        permission reads content, and why content invariance is withdrawn.
        """
        scope, prov = e.declared
        if prov.forged:
            return False
        if prov.coerced and c.coercion_invalidates:
            return False
        if doubted & prov.findings:
            return False
        domains = None
        for g in e.grounds:
            w = content.get(g)
            d = w.domain if isinstance(w, Warrant) else frozenset()
            domains = d if domains is None else (domains & d)
        if not scope or not scope <= (domains or frozenset()):
            return False
        for o in state:
            p = content.get(o)
            if isinstance(p, Policy) and p.bans & scope:
                return False
        return True

    def valid(state, e) -> bool:
        if c.reads_hidden and c.hidden:
            return False
        if not e.grounds <= frozenset(o for o in state if auth(o)):
            return False
        alters = bool(e.dispose & state) or bool(e.issues)
        if alters and not e.grounds:
            return False
        return e.declared[1].complete and permit(state, e)

    f = rp.Frame(frozenset(base), trace, auth, valid)
    object.__setattr__(f, "content", content)
    object.__setattr__(f, "permit", permit)
    return f


def _holder(c: Constitution, a: Act) -> str:
    for name, _, holder in c.chartered:
        if name == a.under:
            return holder
    return "Delegate"


def names(f: rp.Frame, occs) -> set:
    return {str(f.content[o]) for o in occs}


def norms(f: rp.Frame, state) -> frozenset:
    """The enforcement projection. A predicate, not the complement of `auth`."""
    return frozenset(o for o in state if isinstance(f.content.get(o), Policy))


def myopic(f: rp.Frame, skip: str) -> Callable:
    """A checker that declines one edit, to prosecute what soundness buys."""
    def check(state, e):
        return str(e) != skip and f.valid(state, e)
    return check


# ------------------------------------------------------------ the processes


def ex_nihilo() -> Constitution:
    """An act with no grounds, issuing a fresh authority.

    The previous formulation's prior-grounding hypothesis holds vacuously and its
    grounding theorem is false here: the occurrence's only tree is itself, with a
    leaf outside the base. **S2** refuses it.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(Act(None, grants=(("w:from-nowhere", ALL, ()),), scope=ALL,
                  label="ex-nihilo"),),
    )


def rogue_revocation() -> Constitution:
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("n:standard", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="issue"),
            Act("w:charter", grants=(("w:rogue", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:planted"})), label="plant"),
            Act("w:rogue", revokes=("n:standard",), inherits=(), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})),
                label="rogue-revoke"),
        ),
        doubted={"alpha:audited": ("f:planted",)},
    )


def unauthorized_scope() -> Constitution:
    """A grounded warrant used outside its domain."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("w:fiscal", FISCAL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="delegate"),
            Act("w:fiscal", grants=(("n:budget", None, ()),), scope=FISCAL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="in-scope"),
            Act("w:fiscal", grants=(("n:safety-rule", None, ()),), scope=SAFETY,
                prov=Prov(findings=frozenset({"f:ordinary"})),
                label="out-of-scope"),
        ),
    )


def content_sensitive_jurisdiction() -> Constitution:
    """A live policy bans a scope, and permission reads what it says."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),
                   ("n:moratorium", None, "Assembly")),
        acts=(
            Act("w:charter", grants=(("n:safety-change", None, ()),),
                scope=SAFETY, prov=Prov(findings=frozenset({"f:ordinary"})),
                label="touch-safety"),
        ),
    )


def persuasion() -> Constitution:
    """An argument changes a policy, and provenance records it."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"), ("n:old", None, "Assembly")),
        acts=(
            Act("w:charter", revokes=("n:old",), inherits=("w:charter",),
                grants=(("n:new", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:bobs-argument"})),
                label="revise"),
        ),
    )


def laundering() -> Constitution:
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("w:planted", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:planted"})), label="plant"),
            Act("w:planted", grants=(("w:second", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="use"),
            Act("w:second", grants=(("w:third", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="use-again"),
            Act("w:third", grants=(("n:permit", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="cash-out"),
        ),
        doubted={"alpha:audited": ("f:planted",)},
    )


def readoption() -> Constitution:
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("w:planted", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:planted"})), label="plant"),
            Act("w:planted", grants=(("n:P", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="illicit-P"),
            Act("w:charter", grants=(("n:P", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:deliberation"})),
                label="clean-P"),
        ),
        doubted={"alpha:audited": ("f:planted",)},
    )


def audit_discovery() -> Constitution:
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("w:deputy", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:vacancy"})), label="appoint"),
            Act("w:deputy", grants=(("n:rule", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="legislate"),
        ),
        doubted={"alpha:trusting": (), "alpha:informed": ("f:vacancy",)},
    )


def audit_restores() -> Constitution:
    """Doubting a repeal's finding puts its target back in force."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"), ("n:old", None, "Assembly")),
        acts=(
            Act("w:charter", revokes=("n:old",), inherits=("w:charter",),
                scope=ALL, prov=Prov(findings=frozenset({"f:petition"})),
                label="repeal"),
        ),
        doubted={"alpha:trusting": (), "alpha:informed": ("f:petition",)},
    )


def forged_input() -> Constitution:
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(Act("w:charter", grants=(("n:rule", None, ()),), scope=ALL,
                  prov=Prov(findings=frozenset({"f:letter"}), forged=True),
                  label="on-forgery"),),
    )


def coerced_exercise(invalidates: bool = True) -> Constitution:
    """The view records duress; whether it invalidates is the constitution's."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(Act("w:charter", grants=(("n:rule", None, ()),), scope=ALL,
                  prov=Prov(findings=frozenset({"f:letter"}), coerced=True),
                  label="under-duress"),),
        coercion_invalidates=invalidates,
    )


def incomplete_provenance() -> Constitution:
    """A view that does not expose every relevant dependency."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(Act("w:charter", grants=(("n:rule", None, ()),), scope=ALL,
                  prov=Prov(findings=frozenset({"f:ordinary"}), complete=False),
                  label="opaque"),),
    )


def missed_revocation() -> Constitution:
    """A valid revocation of an authority, and a later use of it."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"), ("w:deputy", ALL, "Deputy")),
        acts=(
            Act("w:charter", revokes=("w:deputy",), inherits=("w:charter",),
                scope=ALL, prov=Prov(findings=frozenset({"f:misconduct"})),
                label="strip"),
            Act("w:deputy", grants=(("n:by-deputy", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="stale-use"),
        ),
    )


def lineage_versus_current() -> Constitution:
    """Validly issued, validly used, validly revoked."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("w:a", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="appoint"),
            Act("w:a", grants=(("n:b", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="use"),
            Act("w:charter", revokes=("w:a",), inherits=("w:charter",),
                scope=ALL, prov=Prov(findings=frozenset({"f:review"})),
                label="revoke"),
        ),
    )


def repealable() -> Constitution:
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("n:obsolete", None, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:ordinary"})), label="enact"),
            Act("w:charter", revokes=("n:obsolete",), inherits=("w:charter",),
                scope=ALL, prov=Prov(findings=frozenset({"f:review"})),
                label="repeal"),
        ),
    )


def hidden_pair() -> tuple:
    """Two constitutions, one gazette, different hidden state."""
    base = Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(Act("w:charter", grants=(("n:rule", None, ()),), scope=ALL,
                  prov=Prov(findings=frozenset({"f:ordinary"})),
                  label="legislate"),),
    )
    return base, replace(base, hidden="another world")


def hidden_reading_pair() -> tuple:
    a, b = hidden_pair()
    return replace(a, reads_hidden=True), replace(b, reads_hidden=True)


ALL_CONSTITUTIONS = (
    rogue_revocation(), unauthorized_scope(), persuasion(), laundering(),
    readoption(), audit_discovery(), audit_restores(), forged_input(),
    coerced_exercise(), incomplete_provenance(), missed_revocation(),
    lineage_versus_current(), repealable(), content_sensitive_jurisdiction(),
)
