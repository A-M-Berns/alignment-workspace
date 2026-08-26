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


FISCAL = frozenset({"d:fiscal"})
SAFETY = frozenset({"d:safety"})
INSPECT = frozenset({"d:safety-inspect"})
ADJUDICATE = frozenset({"d:adjudicate"})

#: Plenary authority. A capability is a set of scope tokens and containment is
#: ordinary subset, so the widest one has to *contain* the others rather than
#: being a token that stands for them.
ALL = FISCAL | SAFETY | INSPECT | ADJUDICATE | frozenset({"d:general"})


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
    #: what the act does to the outstanding set, as the semantics declares it
    opens: tuple = ()                  # (name, weight), ...
    discharges: tuple = ()             # names
    transfers: tuple = ()              # ((old, (new, ...)), ...)
    drops: tuple = ()                  # names removed with no route: A1 bait
    #: `ActiveDue` here: the claim keys the semantics holds active at this
    #: step, as a level rather than an event. A rising edge with no matching
    #: opening is the D1 bait.
    owes: tuple = ()                   # names


AMEND = "d:amend"                      #: a constitution's own token for
                                       #: authority over authority. Nothing in
                                       #: the kernel knows it exists.


@dataclass(frozen=True)
class Constitution:
    chartered: tuple                   # (name, domain-or-None, holder)
    acts: tuple
    doubted: Mapping = field(default_factory=dict)
    coercion_invalidates: bool = True
    quorum: int = 1                    # how many grounds an act needs
    base_duties: tuple = ()            # (name, weight), outstanding at the start
    #: obligation name -> claim key, when several occurrences realize one key.
    #: Two episodes of a recurring claim share a key and are distinct claims.
    claim_keys: dict = field(default_factory=dict)
    checks_issued: bool = True         # does permission read what is issued
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
        # what it acts on is resolved against the pre-state...
        dispose = frozenset(by_name[w] for w in a.revokes if w in by_name)
        # ...and then its own issuances are named, so that an act citing
        # something it is about to create resolves to that occurrence rather
        # than to nothing. `self_amendment(False)` is why: the ground is then in
        # `issue_t(e_t)`, the strict pre-state does not contain it, and the act
        # is refused rather than being unrepresentable.
        for j, (name, domain, bans) in enumerate(a.grants):
            o = rp.Occ(t, j)
            content[o] = Warrant(name, frozenset(domain), _holder(c, a)) \
                if domain is not None else Policy(name, frozenset(bans))
            by_name[name] = o
        grounds = frozenset(
            ([by_name[a.under]] if a.under else [])
            + [by_name[w] for w in parents if w in by_name])
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
        held = None
        voters = 0
        for g in e.grounds:
            w = content.get(g)
            if not isinstance(w, Warrant):
                continue
            voters += 1
            held = w.domain if held is None else (held & w.domain)
        held = held or frozenset()

        if voters < c.quorum:
            return False
        if not scope or not scope <= held:
            return False

        # a live policy may forbid a scope outright: permission reads content
        for o in state:
            pol = content.get(o)
            if isinstance(pol, Policy) and pol.bans & scope:
                return False

        # what the act puts in force is part of the act, so permission sees it.
        # widening beyond the basis needs authority over authority.
        if c.checks_issued and AMEND not in held:
            for issued in e.issues:
                if isinstance(issued, Warrant) and not issued.domain <= held:
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


def content_sensitive_jurisdiction(moratorium: bool = True) -> Constitution:
    """A live policy bans a scope, and permission reads what it says.

    The moratorium is a **norm**, not an authority: it grounds nothing and
    appears in no grounding tree, and it decides the verdict anyway. Relabel it
    so that it bans nothing and the same act is permitted, which is why content
    invariance is withdrawn.
    """
    bans = tuple(SAFETY) if moratorium else ()
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly"),),
        acts=(
            Act("w:charter", grants=(("n:moratorium", None, bans),), scope=ALL,
                prov=Prov(findings=frozenset({"f:convention"})),
                label="declare-moratorium"),
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


# ------------------------------------------- proper exercise: the separations


def _charter(*extra) -> tuple:
    return (("w:charter", ALL, "Assembly"),) + extra


def fiscal_in_scope() -> Constitution:
    """**A.** A fiscal warrant legislating on fiscal policy."""
    return Constitution(
        chartered=_charter(("w:fiscal", FISCAL, "Treasury")),
        acts=(Act("w:fiscal", grants=(("n:budget", None, ()),), scope=FISCAL,
                  prov=Prov(findings=frozenset({"f:ordinary"})), label="budget"),),
    )


def fiscal_out_of_scope() -> Constitution:
    """**B.** The same warrant legislating on safety."""
    return Constitution(
        chartered=_charter(("w:fiscal", FISCAL, "Treasury")),
        acts=(Act("w:fiscal", grants=(("n:safety-rule", None, ()),), scope=SAFETY,
                  prov=Prov(findings=frozenset({"f:ordinary"})), label="overreach"),),
    )


def delegation(kind: str) -> Constitution:
    """**C, D and the two remaining cases.** A safety warrant delegating.

    ```text
    narrower       a strict subset of what it holds
    equal          the same
    broader        fiscal as well as safety
    incomparable   fiscal instead of safety
    ```
    """
    inner = INSPECT
    domains = {"narrower": inner, "equal": SAFETY,
               "broader": SAFETY | FISCAL, "incomparable": FISCAL}
    return Constitution(
        chartered=_charter(("w:safety", SAFETY | inner, "Inspector")),
        acts=(Act("w:safety", grants=(("w:deputy", domains[kind], ()),),
                  scope=SAFETY, prov=Prov(findings=frozenset({"f:ordinary"})),
                  label=f"delegate-{kind}"),),
    )


def self_expansion() -> Constitution:
    """**E.** An ordinary authority granting itself a wider successor.

    The base is **not** plenary. That is not decoration: with a plenary charter
    live, the reach of the state is already everything and no act can grow it, so
    escalation would be unmeasurable and the example would prove nothing.
    """
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        acts=(Act("w:fiscal", grants=(("w:fiscal-2", FISCAL | SAFETY, ()),),
                  scope=FISCAL, prov=Prov(findings=frozenset({"f:ordinary"})),
                  label="self-expand"),),
    )


def constitutional_widening() -> Constitution:
    """**F.** An amendment authority widening another office.

    The amender holds `d:amend` and is otherwise **narrow**, so the capability it
    confers really does exceed what the basis held and the reach of the state
    really does grow. Nothing in the kernel knows the token exists; it is this
    constitution's own vocabulary, and that is the point.
    """
    return Constitution(
        chartered=(("w:convention", FISCAL | frozenset({AMEND}), "Convention"),
                   ("w:fiscal", FISCAL, "Treasury")),
        acts=(Act("w:convention", revokes=("w:fiscal",),
                  inherits=("w:convention",),
                  grants=(("w:fiscal-2", FISCAL | SAFETY, ()),),
                  scope=FISCAL,
                  prov=Prov(findings=frozenset({"f:amendment-carried"})),
                  label="widen-treasury"),),
    )


def self_amendment(honest: bool = True) -> Constitution:
    """**G.** The amendment rule amending itself.

    `honest`: the act is grounded in the **old** rule, which is live at the strict
    pre-state, and issues the new one. `honest=False` grounds the act in the rule
    it is about to create, which the pre-state does not contain.
    """
    old_rule = ("w:rule-R", ALL | frozenset({AMEND}), "Assembly")
    return Constitution(
        chartered=(old_rule,),
        acts=(Act("w:rule-R" if honest else "w:rule-R2",
                  revokes=("w:rule-R",), inherits=("w:rule-R",),
                  grants=(("w:rule-R2", ALL | frozenset({AMEND}), ()),),
                  scope=ALL, prov=Prov(findings=frozenset({"f:convention"})),
                  label="amend-the-rule"),),
    )


def constitutional_replacement() -> Constitution:
    """A prior rule authorizing replacement of the whole structure.

    The successors' capabilities are unrelated to the predecessors'. Nothing here
    imposes scope conservativity, which is the point.
    """
    return Constitution(
        chartered=(("w:old-order", FISCAL | frozenset({AMEND}), "Convention"),
                   ("w:ministry", FISCAL, "Ministry")),
        acts=(Act("w:old-order", revokes=("w:old-order", "w:ministry"),
                  inherits=("w:old-order",),
                  grants=(("w:assembly", SAFETY | frozenset({AMEND}), ()),
                          ("w:tribunal", ADJUDICATE, ())),
                  scope=FISCAL,
                  prov=Prov(findings=frozenset({"f:referendum"})),
                  label="refound"),),
    )


def threshold(votes: int) -> Constitution:
    """A two-of-three board. The act names the members it actually invoked."""
    members = tuple((f"w:member-{i}", SAFETY, f"Member {i}") for i in range(3))
    invoked = tuple(name for name, _, _ in members[:votes])
    return Constitution(
        chartered=_charter(*members),
        acts=(Act(invoked[0], inherits=invoked[1:],
                  grants=(("n:resolution", None, ()),), scope=SAFETY,
                  prov=Prov(findings=frozenset({"f:minutes"})),
                  label=f"resolve-{votes}"),),
        quorum=2,
    )


def veto(active: bool) -> Constitution:
    """A negative side condition. A live veto forbids the scope.

    The veto is **not** a ground: permission consults the state, and the
    grounding tree follows `grounds`. So a fact that decided the verdict does not
    thereby become an ancestor, which is the typing test.
    """
    acts = ()
    if active:
        acts += (Act("w:charter", grants=(("n:veto", None, tuple(SAFETY)),),
                     scope=ALL, prov=Prov(findings=frozenset({"f:objection"})),
                     label="lodge-veto"),)
    acts += (Act("w:board", grants=(("n:measure", None, ()),), scope=SAFETY,
                 prov=Prov(findings=frozenset({"f:ordinary"})), label="measure"),)
    return Constitution(chartered=_charter(("w:board", SAFETY, "Board")),
                        acts=acts)


def ex_post_rationalisation() -> Constitution:
    """An act invoking a basis that does not authorize it, beside one that would.

    `w:safety` is live and would authorize the measure. The act does not invoke
    it: it invokes `w:fiscal`. The act is refused, and it stays refused, because
    invoking the other basis would be a different act at a different position.
    """
    return Constitution(
        chartered=_charter(("w:fiscal", FISCAL, "Treasury"),
                           ("w:safety", SAFETY, "Inspector")),
        acts=(Act("w:fiscal", grants=(("n:measure", None, ()),), scope=SAFETY,
                  prov=Prov(findings=frozenset({"f:ordinary"})),
                  label="wrong-basis"),),
    )


def blind_permit() -> Constitution:
    """A constitution whose permission does not read what the act puts in force.

    Everything else is the self-expansion case. With `checks_issued` false the
    fiscal warrant issues a safety-capable successor and the state gains a power
    nobody licensed — which is what the permission being able to see the effect
    is worth.
    """
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        acts=(Act("w:fiscal", grants=(("w:fiscal-2", FISCAL | SAFETY, ()),),
                  scope=FISCAL, prov=Prov(findings=frozenset({"f:ordinary"})),
                  label="unseen-expand"),),
        checks_issued=False,
    )


def capability(c) -> frozenset:
    """`Cap` for this realization: a warrant's domain; a policy has none."""
    return c.domain if isinstance(c, Warrant) else frozenset()


def probe_edits(f) -> tuple:
    """A fixed candidate set for measuring power: one act per domain."""
    import replay as rp
    return tuple(
        rp.Edit(grounds=frozenset({o}), issues=(Policy("probe"),),
                declared=(d, Prov(findings=frozenset({"f:ordinary"}))),
                label=f"probe:{sorted(d)[0]}@{o}")
        for o in sorted(f.base | {rp.Occ(t, j) for t in range(len(f.trace))
                                  for j in range(len(f.trace[t].issues))},
                        key=str)
        for d in (FISCAL, SAFETY))


EXERCISE_CONSTITUTIONS = (
    fiscal_in_scope(), fiscal_out_of_scope(),
    delegation("narrower"), delegation("equal"), delegation("broader"),
    delegation("incomparable"), self_expansion(), constitutional_widening(),
    self_amendment(True), self_amendment(False), constitutional_replacement(),
    threshold(2), threshold(1), veto(True), veto(False),
    ex_post_rationalisation(),
)


# --------------------------------------------------- the answerability side


def duties(c: Constitution):
    """The answerability lifecycle a constitution declares.

    `Due` and `Resolve` have already been consulted: an act's `owes` is the set
    of claim keys the semantics holds **active** there, and its `opens`, `discharges`
    and `transfers` are what `Resolve` judged. Two channels exist so the two
    obligations of the package can fail -- `drops` for **A1**, and an `owes`
    naming a key the act does not open for **D1**.

    A claim key is the name. An occurrence realizing it is minted at the position
    that incurs it, so the same key opened twice would be two occurrences, and
    `newly_due` refuses the second.
    """
    import answer as an

    by_name, base, weight, key = {}, [], {}, {}
    for i, (name, w) in enumerate(c.base_duties):
        q = an.Ob(an.BASE, i)
        by_name[name] = q
        base.append(q)
        weight[q] = w
        key[q] = c.claim_keys.get(name, name)

    opens, discharges, transfers, drops, due = {}, {}, {}, {}, {}
    for t, a in enumerate(c.acts):
        made = []
        for j, (name, w) in enumerate(a.opens):
            q = an.Ob(t, j)
            by_name[name] = q
            weight[q] = w
            key[q] = c.claim_keys.get(name, name)
            made.append(q)
        if made:
            opens[t] = frozenset(made)
        if a.owes:
            due[t] = frozenset(a.owes)
    for t, a in enumerate(c.acts):
        gone = frozenset(by_name[n] for n in a.discharges if n in by_name)
        if gone:
            discharges[t] = gone
        dropped = frozenset(by_name[n] for n in a.drops if n in by_name)
        if dropped:
            drops[t] = dropped
        if a.transfers:
            transfers[t] = {by_name[old]: frozenset(by_name[n] for n in new
                                                    if n in by_name)
                            for old, new in a.transfers if old in by_name}
    d = an.Duties(frozenset(base), opens, discharges, transfers, drops, due, key)
    object.__setattr__(d, "weight", weight)
    object.__setattr__(d, "names", {q: n for n, q in by_name.items()})
    return d


def burden(d):
    return lambda q: d.weight.get(q, 0.0)


def duty_names(d, obs) -> set:
    return {d.names.get(q, str(q)) for q in obs}


def _one(under="w:charter", **kw):
    return Act(under, scope=ALL, prov=Prov(findings=frozenset({"f:ordinary"})),
               **kw)


CHARTER = (("w:charter", ALL, "Assembly"),)


def answered() -> Constitution:
    """A due issue, legitimately answered."""
    return Constitution(chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
                        acts=(_one(discharges=("q:complaint",), label="answer"),))


def defeated() -> Constitution:
    """A due issue the process's own semantics recognises as defeated.

    An external observer may think the answer is terrible. That is not this
    theorem's business.
    """
    return Constitution(chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
                        acts=(_one(discharges=("q:complaint",), label="reject"),))


def silently_deleted() -> Constitution:
    """A due issue removed with no declared route. **A1** must catch it."""
    return Constitution(chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
                        acts=(_one(drops=("q:complaint",), label="quietly-drop"),))


def transferred_once() -> Constitution:
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:referred", 1.0),),
                   transfers=(("q:complaint", ("q:referred",)),),
                   label="refer"),))


def transfer_chain(n: int = 3, decay: float = 1.0) -> Constitution:
    """`n` successive referrals. With `decay < 1` each one weighs less."""
    acts, w, prev = [], 1.0, "q:complaint"
    for i in range(n):
        w = w * decay
        nxt = f"q:step{i}"
        acts.append(_one(opens=((nxt, w),), transfers=((prev, (nxt,)),),
                         label=f"refer{i}"))
        prev = nxt
    return Constitution(chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
                        acts=tuple(acts))


def transfer_to_nowhere() -> Constitution:
    """A transfer naming no successor. **A1** must catch it."""
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(transfers=(("q:complaint", ()),), label="refer-to-nothing"),))


def split(share: float = 0.5) -> Constitution:
    """One obligation into two. `share` each; `0.5` conserves, less dilutes."""
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:left", share), ("q:right", share)),
                   transfers=(("q:complaint", ("q:left", "q:right")),),
                   label="split"),))


def merge(w: float = 2.0) -> Constitution:
    """Two obligations into one. `w = 2` conserves; less dilutes."""
    return Constitution(
        chartered=CHARTER,
        base_duties=(("q:a", 1.0), ("q:b", 1.0)),
        acts=(_one(opens=(("q:joint", w),),
                   transfers=(("q:a", ("q:joint",)), ("q:b", ("q:joint",))),
                   label="consolidate"),))


def merge_lenient() -> Constitution:
    """Two obligations of weight 1 into one of weight 1.5.

    Passes per-parent accounting and fails total accounting, which is how the
    two notions are separated.
    """
    return merge(1.5)


def diluted_to_nothing() -> Constitution:
    """Nominal persistence: named successors all the way down, weighing zero."""
    return transfer_chain(4, decay=0.0)


def rogue_discharge() -> Constitution:
    """An unentitled act claiming to discharge an outstanding obligation.

    The act is refused on the entitlement side — it acts under a warrant granted
    on a doubted finding — so it discharges nothing. Under two replays with two
    acceptance predicates it would.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(
            Act("w:charter", grants=(("w:rogue", ALL, ()),), scope=ALL,
                prov=Prov(findings=frozenset({"f:planted"})), label="plant"),
            Act("w:rogue", scope=ALL, discharges=("q:complaint",),
                prov=Prov(findings=frozenset({"f:ordinary"})),
                label="rogue-discharge"),
        ),
        doubted={"alpha:audited": ("f:planted",)},
    )


def unauthorized_with_clean_answerability() -> Constitution:
    """Entitlement fails; answerability is impeccable. Case 13."""
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        base_duties=(("q:complaint", 1.0),),
        acts=(Act("w:fiscal", grants=(("n:safety-rule", None, ()),),
                  scope=SAFETY, prov=Prov(findings=frozenset({"f:ordinary"})),
                  opens=(("q:new", 1.0),), label="overreach"),),
    )


def entitled_with_laundered_obligation() -> Constitution:
    """Entitlement is impeccable; an obligation is dropped. Case 14."""
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(grants=(("n:rule", None, ()),), drops=("q:complaint",),
                   label="legislate-and-forget"),))


def revoked_but_grounded() -> Constitution:
    """A validly issued authority validly revoked; its tree survives. Case 15."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(grants=(("w:deputy", ALL, ()),), label="appoint"),
              _one(revokes=("w:deputy",), inherits=("w:charter",),
                   label="dismiss")),
    )


def high_regret() -> Constitution:
    """The same bad choice, three times, every issue faithfully recorded."""
    acts = tuple(_one(opens=((f"q:same-{i}", 1.0),),
                      grants=((f"n:same-{i}", None, ()),),
                      label=f"repeat{i}") for i in range(3))
    return Constitution(chartered=CHARTER, acts=acts)


def unobservant() -> Constitution:
    """Nothing ever becomes due, because nothing is ever noticed."""
    return Constitution(chartered=CHARTER,
                        acts=(_one(grants=(("n:rule", None, ()),),
                                   label="legislate"),))


def refoundation_with_clean_answerability() -> Constitution:
    """Radical constitutional change carrying its outstanding issue forward."""
    return Constitution(
        chartered=(("w:old-order", FISCAL | frozenset({AMEND}), "Convention"),),
        base_duties=(("q:pending", 1.0),),
        acts=(Act("w:old-order", revokes=("w:old-order",),
                  inherits=("w:old-order",),
                  grants=(("w:assembly", SAFETY | frozenset({AMEND}), ()),),
                  scope=FISCAL,
                  prov=Prov(findings=frozenset({"f:referendum"})),
                  opens=(("q:inherited", 1.0),),
                  transfers=(("q:pending", ("q:inherited",)),),
                  label="refound"),),
    )


ANSWER_CONSTITUTIONS = (
    answered(), defeated(), transferred_once(), transfer_chain(3),
    split(0.5), merge(2.0), rogue_discharge(),
    unauthorized_with_clean_answerability(), revoked_but_grounded(),
    high_regret(), unobservant(), refoundation_with_clean_answerability(),
)

BROKEN_CONSTITUTIONS = (
    silently_deleted(), transfer_to_nowhere(),
    entitled_with_laundered_obligation(),
)

# ---------------------------------------- the resolve-after-transfer family
# The cases that refuted the previous pass's conclusion. Every one of them has
# clean premises; the old statement reported four of them as violations because
# it looked for the discharge of the root rather than of its descendants.


def transfer_then_discharge() -> Constitution:
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:referred", 1.0),),
                   transfers=(("q:complaint", ("q:referred",)),), label="refer"),
              _one(discharges=("q:referred",), label="answer")))


def split_then_discharge_one() -> Constitution:
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:left", 0.5), ("q:right", 0.5)),
                   transfers=(("q:complaint", ("q:left", "q:right")),),
                   label="split"),
              _one(discharges=("q:left",), label="answer-left")))


def split_then_discharge_both() -> Constitution:
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:left", 0.5), ("q:right", 0.5)),
                   transfers=(("q:complaint", ("q:left", "q:right")),),
                   label="split"),
              _one(discharges=("q:left", "q:right"), label="answer-both")))


def merge_then_discharge() -> Constitution:
    return Constitution(
        chartered=CHARTER, base_duties=(("q:a", 1.0), ("q:b", 1.0)),
        acts=(_one(opens=(("q:joint", 2.0),),
                   transfers=(("q:a", ("q:joint",)), ("q:b", ("q:joint",))),
                   label="consolidate"),
              _one(discharges=("q:joint",), label="answer-joint")))


def reconverging_split() -> Constitution:
    """A split whose branches transfer back into one obligation.

    Succession is a DAG here and the derivation is still a tree: the reconverged
    obligation appears as two distinct leaves of the root's unfolding.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:left", 0.5), ("q:right", 0.5)),
                   transfers=(("q:complaint", ("q:left", "q:right")),),
                   label="split"),
              _one(opens=(("q:rejoined", 1.0),),
                   transfers=(("q:left", ("q:rejoined",)),
                              ("q:right", ("q:rejoined",))),
                   label="rejoin")))


# ------------------------------------------------------ Due, and its failure


def recognized_due_but_never_entered() -> Constitution:
    """The semantics says a represented reason is owed an answer; nothing opens.

    Entitlement is impeccable and no outstanding obligation is ever removed, so
    the previous package passed this. **D1** is what refuses it.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(grants=(("n:rule", None, ()),),
                   owes=("q:recognized",), label="notice-and-ignore"),))


def recognized_due_and_entered() -> Constitution:
    """The same reason, entered. The obligation may stay open forever."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(grants=(("n:rule", None, ()),),
                   opens=(("q:recognized", 1.0),),
                   owes=("q:recognized",), label="notice-and-enter"),))


def due_arrives_later() -> Constitution:
    """A reason represented at one act becomes owed at a later one.

    `Due` reads the normative state, so what a represented reason requires can
    change without any new reason arriving. D1 is indexed by position for this.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(grants=(("n:duty-rule", None, ()),), label="legislate"),
              _one(opens=(("q:late", 1.0),), owes=("q:late",),
                   label="now-it-is-owed")))


def due_entered_then_closed_same_act() -> Constitution:
    """An act that opens what it owes and purports to discharge it at once.

    Openings are unioned last, so the obligation is outstanding afterwards and
    the discharge is refused as disposing of something not open. A resolution
    cannot use an obligation it creates to certify that it has already handled it.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:instant", 1.0),), owes=("q:instant",),
                   discharges=("q:instant",), label="open-and-close"),))


# ----------------------------------------- the unauthorized act and its wake


def unauthorized_act_opens_complaint() -> Constitution:
    """Alice acts without entitlement; the act is refused; a complaint opens.

    The case the shared gate could not represent. The normative effect is a
    no-op — the fiscal warrant cannot legislate on safety — and the process is
    answerable for the fact that the attempt occurred.
    """
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        acts=(Act("w:fiscal", grants=(("n:safety-rule", None, ()),),
                  scope=SAFETY, prov=Prov(findings=frozenset({"f:ordinary"})),
                  opens=(("q:complaint-about-alice", 1.0),),
                  owes=("q:complaint-about-alice",),
                  label="overreach-noticed"),))


def unauthorized_act_attempts_discharge() -> Constitution:
    """The same act also purports to answer a standing complaint. It cannot.

    Opening is not gated by entitlement; discharging is. One act exercises both
    channels and only one of them takes effect.
    """
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        base_duties=(("q:standing", 1.0),),
        acts=(Act("w:fiscal", grants=(("n:safety-rule", None, ()),),
                  scope=SAFETY, prov=Prov(findings=frozenset({"f:ordinary"})),
                  opens=(("q:complaint-about-alice", 1.0),),
                  owes=("q:complaint-about-alice",),
                  discharges=("q:standing",),
                  label="overreach-and-claim-to-answer"),))


def rejected_edit_with_descriptive_consequences() -> Constitution:
    """A normative edit refused on provenance, whose occurrence is still owed for.

    The refusal is on a coerced exercise rather than on scope, so the act is a
    normative no-op for a different reason and the obligation still opens.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(Act("w:charter", grants=(("n:rule", None, ()),), scope=ALL,
                  prov=Prov(findings=frozenset({"f:ordinary"}), coerced=True),
                  opens=(("q:coercion-complaint", 1.0),),
                  owes=("q:coercion-complaint",),
                  label="coerced-then-owed"),),
        coercion_invalidates=True,
    )


def self_ratifying_resolution() -> Constitution:
    """A transfer naming a successor and claiming the successor discharges it.

    The successor is opened by the same act that transfers into it, which A1
    requires; what it cannot also do is count as already resolved. The discharge
    of the successor at the same position disposes of something not yet open.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:complaint", 1.0),),
        acts=(_one(opens=(("q:successor", 1.0),),
                   transfers=(("q:complaint", ("q:successor",)),),
                   discharges=("q:successor",),
                   label="carry-and-claim-done"),))


ANSWER_CONSTITUTIONS = ANSWER_CONSTITUTIONS + (
    transfer_then_discharge(), split_then_discharge_one(),
    split_then_discharge_both(), merge_then_discharge(), reconverging_split(),
    recognized_due_and_entered(), due_arrives_later(),
    unauthorized_act_opens_complaint(), unauthorized_act_attempts_discharge(),
    rejected_edit_with_descriptive_consequences(),
)

D1_BROKEN = (recognized_due_but_never_entered(),)

A1_BROKEN = BROKEN_CONSTITUTIONS

REFUSED_RESOLUTIONS = (due_entered_then_closed_same_act(),
                       self_ratifying_resolution())

# ------------------------------------------- Due as an activation generator


def resolved_stays_resolved() -> Constitution:
    """A claim opened, answered, and whose reasons stay represented afterwards.

    The act at t=1 answers it. The acts after that represent the same material
    and activate the same key, which is **not** newly due because the key is
    already incurred. A persistent `Due` predicate would force the claim back
    open forever and make the discharge at t=1 illegitimate.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:claim", 1.0),), owes=("q:claim",), label="notice"),
              _one(owes=("q:claim",), discharges=("q:claim",), label="answer"),
              _one(owes=("q:claim",), label="still-represented"),
              _one(owes=("q:claim",), label="still-represented-again")))


def old_reason_becomes_newly_due() -> Constitution:
    """Material represented at t=0 that only the later state makes owed.

    Nothing arrives at t=2. What changed is the normative context, and `Due` is
    evaluated against it, so minting on reason arrival would miss this entirely.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(label="represent-the-material"),
              _one(grants=(("n:new-standard", None, ()),), label="raise-standard"),
              _one(opens=(("q:under-new-standard", 1.0),),
                   owes=("q:under-new-standard",), label="now-owed"),
              _one(owes=("q:under-new-standard",), label="still-owed")))


def joint_reasons_one_claim() -> Constitution:
    """Neither piece of material alone is owed; together they are.

    `Due` reads the whole represented state, so no support-set machinery is
    needed on the obligation: the activation simply does not fire until t=2.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(label="first-material"),
              _one(label="second-material"),
              _one(opens=(("q:joint-claim", 1.0),), owes=("q:joint-claim",),
                   label="together-they-are-owed")))


def one_reason_many_claims() -> Constitution:
    """One represented failure owing both a repair and an explanation."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:repair", 1.0), ("q:explain", 1.0)),
                   owes=("q:repair", "q:explain"), label="one-failure"),))


def due_and_resolved_in_one_step() -> Constitution:
    """An event that reveals a problem and completely answers it at once.

    The claim is incurred and discharged without ever being outstanding. The
    theorem still speaks about it, because the theorem quantifies over incurred.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:instant", 1.0),), owes=("q:instant",),
                   discharges=("q:instant",), label="reveal-and-answer"),))


def due_and_ignored_in_one_step() -> Constitution:
    """The loophole the case above must not open: activated, and nothing done."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(owes=("q:instant",), label="reveal-and-shrug"),))


# ------------------------------------------------ the relaxed carry law


def carry_into_existing_claim() -> Constitution:
    """Consolidation into a claim that is already outstanding.

    The previous version's fresh-successor clause refused this while the
    derivation handled it correctly.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:minor", 1.0), ("q:major", 1.0)),
        acts=(_one(transfers=(("q:minor", ("q:major",)),), label="consolidate"),))


def carry_into_shared_successor() -> Constitution:
    """Two claims carried into one preexisting third."""
    return Constitution(
        chartered=CHARTER,
        base_duties=(("q:a", 1.0), ("q:b", 1.0), ("q:omnibus", 2.0)),
        acts=(_one(transfers=(("q:a", ("q:omnibus",)), ("q:b", ("q:omnibus",))),
                   label="fold-in"),))


def carry_into_something_resolved() -> Constitution:
    """A carry naming a successor the same event discharges.

    Refused: the successor is not outstanding after the step, so the predecessor
    would be resolved into nothing. This is the strict-pre-state protection on
    the resolution side and needs no premise of its own.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:claim", 1.0), ("q:sink", 1.0)),
        acts=(_one(transfers=(("q:claim", ("q:sink",)),), discharges=("q:sink",),
                   label="carry-into-a-hole"),))


def split_one_branch_lost() -> Constitution:
    """A split, one branch of which is silently dropped.

    No existential escape: the surviving branch does not rescue the derivation.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:claim", 1.0),),
        acts=(_one(opens=(("q:kept", 0.5), ("q:lost", 0.5)),
                   transfers=(("q:claim", ("q:kept", "q:lost")),), label="split"),
              _one(drops=("q:lost",), label="lose-one-branch")))


# ------------------------------------- the three gates acting independently


def response_without_normative_change() -> Constitution:
    """An ordinary answer: resolves a claim, changes no standing."""
    return Constitution(
        chartered=CHARTER, base_duties=(("q:claim", 1.0),),
        acts=(_one(discharges=("q:claim",), label="just-answer"),))


def amendment_without_answerability() -> Constitution:
    """An ordinary amendment: changes standing, touches no claim."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(grants=(("n:rule", None, ()),), label="just-legislate"),))


def evidence_opens_without_norm_event() -> Constitution:
    """Represented material incurring a claim while enacting nothing."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:from-evidence", 1.0),), owes=("q:from-evidence",),
                   label="observe"),))


def self_authorize_then_discharge() -> Constitution:
    """An act granting itself the standing it then uses to resolve a claim.

    Refused on the entitlement side at the strict pre-state, so it resolves
    nothing -- the resolution gate reads the legitimate pre-state, not the
    post-state the act would have created.
    """
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        base_duties=(("q:safety-claim", 1.0),),
        acts=(Act("w:fiscal", grants=(("w:self", SAFETY, ()),), scope=SAFETY,
                  prov=Prov(findings=frozenset({"f:ordinary"})),
                  discharges=("q:safety-claim",), label="self-authorize"),))


ANSWER_CONSTITUTIONS = ANSWER_CONSTITUTIONS + (
    resolved_stays_resolved(), old_reason_becomes_newly_due(),
    joint_reasons_one_claim(), one_reason_many_claims(),
    due_and_resolved_in_one_step(), carry_into_existing_claim(),
    carry_into_shared_successor(), response_without_normative_change(),
    amendment_without_answerability(), evidence_opens_without_norm_event(),
    self_authorize_then_discharge(),
)

D1_BROKEN = (recognized_due_but_never_entered(), due_and_ignored_in_one_step())

A1_BROKEN = BROKEN_CONSTITUTIONS + (carry_into_something_resolved(),
                                    split_one_branch_lost())

# --------------------------------------------------- activation episodes


def recurrence() -> Constitution:
    """The same claim kind, twice, as two episodes.

    Active, incurred, resolved; the level falls; it rises again. The second
    rising edge is a genuinely new occasion and incurs a **second** occurrence.
    Memoizing on content forbids this, which is why the previous version could
    not express a recurring obligation at all.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:lapse-1", 1.0),), owes=("q:lapse",),
                   label="first-lapse"),
              _one(owes=("q:lapse",), discharges=("q:lapse-1",),
                   label="fix-it"),
              _one(label="quiet"),
              _one(opens=(("q:lapse-2", 1.0),), owes=("q:lapse",),
                   label="second-lapse")),
        claim_keys={"q:lapse-1": "q:lapse", "q:lapse-2": "q:lapse"})


def recurrence_ignored() -> Constitution:
    """The second episode arrives and nothing is taken on. D1 must catch it."""
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:lapse-1", 1.0),), owes=("q:lapse",),
                   label="first-lapse"),
              _one(owes=("q:lapse",), discharges=("q:lapse-1",),
                   label="fix-it"),
              _one(label="quiet"),
              _one(owes=("q:lapse",), label="second-lapse-ignored")),
        claim_keys={"q:lapse-1": "q:lapse"})


def falling_edge_is_not_resolution() -> Constitution:
    """`Due` going quiet does not resolve anything.

    The claim was incurred and stays outstanding: what stops being owed is
    decided by `Resolve`, not by the reasons ceasing to be represented.
    """
    return Constitution(
        chartered=CHARTER,
        acts=(_one(opens=(("q:claim", 1.0),), owes=("q:claim",), label="notice"),
              _one(label="reasons-no-longer-represented")))


def same_step_activation_unauthorized_resolution() -> Constitution:
    """Activated and answered at once, by an actor without the standing.

    The claim is incurred because incurrence is ungated; the resolution is
    refused because resolution is not.
    """
    return Constitution(
        chartered=(("w:fiscal", FISCAL, "Treasury"),),
        acts=(Act("w:fiscal", grants=(("n:safety-rule", None, ()),),
                  scope=SAFETY, prov=Prov(findings=frozenset({"f:ordinary"})),
                  opens=(("q:revealed", 1.0),), owes=("q:revealed",),
                  discharges=("q:revealed",), label="reveal-and-overreach"),))


def refoundation_activates_an_old_reason() -> Constitution:
    """Radical constitutional change makes long-standing material newly owed.

    Nothing is represented at t=2 that was not represented at t=0. The successor
    constitution simply owes an answer for it, which is what a `Due` reading only
    reason arrivals cannot see.
    """
    return Constitution(
        chartered=(("w:old-order", FISCAL | frozenset({AMEND}), "Convention"),),
        acts=(Act("w:old-order", scope=FISCAL,
                  prov=Prov(findings=frozenset({"f:longstanding"})),
                  label="represent-the-practice"),
              Act("w:old-order", revokes=("w:old-order",),
                  inherits=("w:old-order",),
                  grants=(("w:assembly", SAFETY | frozenset({AMEND}), ()),),
                  scope=FISCAL,
                  prov=Prov(findings=frozenset({"f:referendum"})),
                  label="refound"),
              Act("w:assembly", scope=SAFETY,
                  prov=Prov(findings=frozenset({"f:longstanding"})),
                  opens=(("q:account-for-the-practice", 1.0),),
                  owes=("q:account-for-the-practice",),
                  label="now-it-is-owed")))


def succession_incurs_without_due() -> Constitution:
    """A claim incurred as a carried successor, which `Due` never activates.

    The reason D1 is an inclusion rather than an equality: succession is a second
    and legitimate genesis for answerability.
    """
    return Constitution(
        chartered=CHARTER, base_duties=(("q:original", 1.0),),
        acts=(_one(opens=(("q:successor", 1.0),),
                   transfers=(("q:original", ("q:successor",)),),
                   label="refer"),))


ACTIVATION_CONSTITUTIONS = (
    resolved_stays_resolved(), recurrence(), falling_edge_is_not_resolution(),
    old_reason_becomes_newly_due(), joint_reasons_one_claim(),
    one_reason_many_claims(), due_and_resolved_in_one_step(),
    same_step_activation_unauthorized_resolution(),
    unauthorized_act_opens_complaint(), succession_incurs_without_due(),
    refoundation_activates_an_old_reason(), unobservant(),
)

ANSWER_CONSTITUTIONS = ANSWER_CONSTITUTIONS + (
    recurrence(), falling_edge_is_not_resolution(),
    same_step_activation_unauthorized_resolution(),
    succession_incurs_without_due(), refoundation_activates_an_old_reason(),
)

D1_BROKEN = D1_BROKEN + (recurrence_ignored(),)
