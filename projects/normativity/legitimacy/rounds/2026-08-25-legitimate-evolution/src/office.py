"""A realization with no normative record anywhere in it.

A constitution charters some offices; a gazette records the acts they perform.
An act names the warrant it acts under, the warrants it inherits from, what it
revokes, what it grants, the domain it purports to act in, and the findings of
fact it relies on. An audit context is the set of findings currently doubted.

**This module imports `replay` and the standard library and nothing else.**
`tests/test_replay.py` checks that by parsing its imports. It exists so the
hypotheses and theorems of `replay.py` can be run against a system that is not
this repository's architecture, and it decides the questions Reflective Integrity
cannot see because its admission preconditions make the alternatives
indistinguishable inside a record.

Two things are deliberately outside the declared view. `hidden` is a field the
constitution carries and the gazette does not report; `reads_hidden` says whether
the validity rules consult it. That pair is what makes the factorization
hypothesis falsifiable rather than true by construction.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Iterable, Mapping, Optional, Sequence

import replay as rp


@dataclass(frozen=True)
class Warrant:
    """What an occurrence of authority says: who holds it and over what."""

    name: str
    domain: frozenset = frozenset()
    holder: str = "Assembly"

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Policy:
    """What an occurrence of norm says. Read by nothing that decides validity."""

    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Act:
    """One entry in the gazette.

    `inherits` defaults to what the act revokes, which is ordinary supersession;
    an act that cleans something up passes an explicit empty tuple. `forged` and
    `coerced` are declared defects of the input and of the exercise, kept apart
    because they are two different failures.
    """

    at: int
    under: str
    revokes: tuple = ()
    grants: tuple = ()                 # ((sort, content), ...)
    inherits: Optional[tuple] = None
    scope: frozenset = frozenset()
    findings: frozenset = frozenset()
    forged: bool = False
    coerced: bool = False
    label: str = ""

    def parents(self, sort_of) -> tuple:
        """The authorities this act's grant inherits entitlement from.

        Defaulting to the **authority-sorted** things it revokes: superseding an
        authority inherits from it, and superseding a norm does not — a norm's
        entitlement comes from the authority that issued it, never from the norm
        it replaces. An act that cleans up rather than inheriting passes an
        explicit empty tuple, which is what `unauthorized_scope`'s sibling
        register and `COUNTERMODELS.md` §3 turn on.
        """
        if self.inherits is not None:
            return self.inherits
        return tuple(w for w in self.revokes if sort_of(w) == rp.AUTHORITY)


@dataclass(frozen=True)
class Constitution:
    chartered: tuple                   # (name, domain, holder, sort)
    acts: tuple
    contexts: tuple = ("alpha:0",)
    doubted: Mapping = field(default_factory=dict)   # context -> findings doubted
    hidden: object = None              # not reported in the gazette
    reads_hidden: str = ""             # "", "admission" or "effect"


# ------------------------------------------------------------- construction


def build(c: Constitution) -> rp.Process:
    """The proposal a constitution and its gazette make."""
    base, content, by_name = [], {}, {}
    for i, (name, domain, holder, sort) in enumerate(c.chartered):
        o = rp.Occ(rp.BASE_TIME, i, sort)
        base.append(o)
        content[o] = Warrant(name, frozenset(domain), holder) \
            if sort == rp.AUTHORITY else Policy(name)
        by_name[name] = o

    sorts = {name: sort for name, _, _, sort in c.chartered}
    for a in c.acts:
        for sort, name, _ in a.grants:
            sorts[name] = sort

    edits = []
    for a in c.acts:
        issued_at = {}
        grants = []
        for j, (sort, name, domain) in enumerate(a.grants):
            grants.append((sort, Warrant(name, frozenset(domain),
                                         _holder(c, a))
                           if sort == rp.AUTHORITY else Policy(name)))
            issued_at[name] = rp.Occ(a.at, j, sort)
        e = rp.Edit(
            at=a.at,
            grounds=frozenset(
                [by_name[a.under]]
                + [by_name[w] for w in a.parents(lambda n: sorts.get(n))]),
            dispose=frozenset(by_name[w] for w in a.revokes),
            issue=tuple(grants),
            input=(frozenset(a.findings), a.forged),
            exercise=(a.coerced,),
            scope=frozenset(a.scope),
            request=(tuple(a.revokes), tuple(n for _, n, _ in a.grants)),
            label=a.label or f"act@{a.at}",
        )
        edits.append(e)
        by_name.update(issued_at)

    contents = dict(content)
    for e in edits:
        contents.update(e.content())

    def domains(state, e):
        out = None
        for g in e.grounds:
            w = contents.get(g)
            d = w.domain if isinstance(w, Warrant) else frozenset()
            out = d if out is None else (out & d)
        return out or frozenset()

    def permit(state, e) -> bool:
        """Jurisdiction: the edit's scope lies inside every ground's domain."""
        return bool(e.scope) and e.scope <= domains(state, e)

    def input_ok(alpha, e) -> bool:
        findings, forged = e.input
        return not forged and not (findings & frozenset(c.doubted.get(alpha, ())))

    def exercise_ok(alpha, e) -> bool:
        return not e.exercise[0]

    def prov_ok(alpha, e) -> bool:
        return input_ok(alpha, e) and exercise_ok(alpha, e)

    def valid(alpha, state, e) -> bool:
        if c.reads_hidden == "admission" and c.hidden:
            return False
        return (e.grounds <= rp.auth(state) and permit(state, e)
                and prov_ok(alpha, e))

    def view(alpha, i):
        return (frozenset(base), tuple(e.declared() for e in edits[:i]),
                frozenset(c.doubted.get(alpha, ())))

    return rp.Process(frozenset(base), tuple(edits), valid, tuple(c.contexts),
                      permit, prov_ok, view, content)


def _holder(c: Constitution, a: Act) -> str:
    for name, _, holder, _ in c.chartered:
        if name == a.under:
            return holder
    return "Delegate"


def input_ok_of(c: Constitution):
    p = build(c)
    return lambda alpha, e: not e.input[1] and not (
        e.input[0] & frozenset(c.doubted.get(alpha, ())))


def exercise_ok_of(c: Constitution):
    return lambda alpha, e: not e.exercise[0]


AUTH = rp.AUTHORITY
NORM = rp.NORM
ALL = frozenset({"d:all"})
FISCAL = frozenset({"d:fiscal"})
SAFETY = frozenset({"d:safety"})


# ------------------------------------------------------------ the processes


def rogue_revocation() -> Constitution:
    """A legitimate norm, and an ungrounded act that revokes it.

    `act:plant` relies on a finding the audit doubts, so the authority it grants
    is never legitimate; `act:rogue-revoke` acts under that authority and is
    therefore rejected. The norm it purports to revoke stays in force.

    Under the round's previous object — the raw lifecycle intersected with a
    derivability set — the norm left the frontier anyway, because something in
    the raw process had removed it. `COUNTERMODELS.md` §1.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((NORM, "n:standard", ()),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="issue"),
            Act(1, "w:charter", grants=((AUTH, "w:rogue", ALL),),
                scope=ALL, findings=frozenset({"f:planted"}), label="plant"),
            Act(2, "w:rogue", revokes=("n:standard",), inherits=(),
                scope=ALL, findings=frozenset({"f:ordinary"}),
                label="rogue-revoke"),
        ),
        contexts=("alpha:audited",),
        doubted={"alpha:audited": ("f:planted",)},
    )


def unauthorized_scope() -> Constitution:
    """A perfectly grounded authority acting outside its domain.

    `w:fiscal` is granted cleanly and holds only over fiscal matters. The act
    that uses it to legislate on safety has impeccable provenance and impeccable
    grounding, and is refused by the permit relation alone.

    The round's previous succession calculus admitted it: it checked that the
    licence was derivable and never what the licence was for.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((AUTH, "w:fiscal", FISCAL),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="delegate"),
            Act(1, "w:fiscal", grants=((NORM, "n:budget", ()),),
                scope=FISCAL, findings=frozenset({"f:ordinary"}), label="in-scope"),
            Act(2, "w:fiscal", grants=((NORM, "n:safety-rule", ()),),
                scope=SAFETY, findings=frozenset({"f:ordinary"}),
                label="out-of-scope"),
        ),
    )


def persuasion() -> Constitution:
    """An argument changes a policy, and the change is legitimate.

    The revising act relies on a finding nobody doubts. Remove that finding from
    the world and the act would not have been performed — which the round's
    earlier challenge-survival criterion would have counted against it. Here it
    counts for nothing: the question is whether prior legitimate authority
    permitted this edit given this declared input, and it did.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),
                   ("n:old", (), "Assembly", NORM)),
        acts=(
            Act(0, "w:charter", revokes=("n:old",),
                grants=((NORM, "n:new", ()),), scope=ALL,
                findings=frozenset({"f:bobs-argument"}), label="revise"),
        ),
    )


def laundering() -> Constitution:
    """A doubted grant, used downstream three times, never becoming legitimate."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((AUTH, "w:planted", ALL),),
                scope=ALL, findings=frozenset({"f:planted"}), label="plant"),
            Act(1, "w:planted", grants=((AUTH, "w:second", ALL),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="use"),
            Act(2, "w:second", grants=((AUTH, "w:third", ALL),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="use-again"),
            Act(3, "w:third", grants=((NORM, "n:permit", ()),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="cash-out"),
        ),
        contexts=("alpha:audited",),
        doubted={"alpha:audited": ("f:planted",)},
    )


def readoption() -> Constitution:
    """The content a rejected act proposed, later adopted by a clean one.

    Two occurrences, one content. The first lineage is refused and the second is
    legitimate, and nothing about the policy itself is poisoned.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((AUTH, "w:planted", ALL),),
                scope=ALL, findings=frozenset({"f:planted"}), label="plant"),
            Act(1, "w:planted", grants=((NORM, "n:P", ()),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="illicit-P"),
            Act(2, "w:charter", grants=((NORM, "n:P", ()),),
                scope=ALL, findings=frozenset({"f:deliberation"}),
                label="clean-P"),
        ),
        contexts=("alpha:audited",),
        doubted={"alpha:audited": ("f:planted",)},
    )


def audit_discovery() -> Constitution:
    """One gazette, two audit contexts.

    Under `alpha:trusting` every finding stands and the delegated authority and
    everything under it are legitimate. Under `alpha:informed` the appointment's
    finding is doubted, and the appointment, the authority it granted and the
    norm granted under that authority all fall — without any of the historical
    rules changing.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((AUTH, "w:deputy", ALL),),
                scope=ALL, findings=frozenset({"f:vacancy"}), label="appoint"),
            Act(1, "w:deputy", grants=((NORM, "n:rule", ()),),
                scope=ALL, findings=frozenset({"f:ordinary"}), label="legislate"),
        ),
        contexts=("alpha:trusting", "alpha:informed"),
        doubted={"alpha:trusting": (), "alpha:informed": ("f:vacancy",)},
    )


def audit_restores() -> Constitution:
    """Doubting a finding can put *more* in force, not less.

    The doubted act was a revocation. Invalidating it leaves its target standing,
    so a stricter audit context is not a smaller legitimate state.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),
                   ("n:old", (), "Assembly", NORM)),
        acts=(
            Act(0, "w:charter", revokes=("n:old",), inherits=(),
                scope=ALL, findings=frozenset({"f:petition"}), label="repeal"),
        ),
        contexts=("alpha:trusting", "alpha:informed"),
        doubted={"alpha:trusting": (), "alpha:informed": ("f:petition",)},
    )


def forged_input() -> Constitution:
    """The declared input is a forgery: `InputOK` fails and `ExerciseOK` holds."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((NORM, "n:rule", ()),), scope=ALL,
                findings=frozenset({"f:letter"}), forged=True, label="on-forgery"),
        ),
    )


def coerced_exercise() -> Constitution:
    """The input is authentic and the exercise is not: `ExerciseOK` fails."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((NORM, "n:rule", ()),), scope=ALL,
                findings=frozenset({"f:letter"}), coerced=True, label="under-duress"),
        ),
    )


def clean_pair() -> tuple:
    """Two constitutions with one gazette and different hidden state.

    The declared views agree at every step. With `reads_hidden` empty the
    legitimate replays agree, which is the positive case for noninterference;
    the negative case is `hidden_admission_pair`.
    """
    base = Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((NORM, "n:rule", ()),), scope=ALL,
                findings=frozenset({"f:ordinary"}), label="legislate"),
        ),
    )
    return base, replace(base, hidden="a different internal world")


def hidden_admission_pair() -> tuple:
    """The same gazette, and a hidden variable that decides admission.

    Nothing in the declared view differs, and one replay admits the act while the
    other refuses it. The factorization hypothesis rejects the pair, and it is
    the general form of the pre-state condition the previous pass isolated.
    """
    a, b = clean_pair()
    return replace(a, reads_hidden="admission"), \
        replace(b, reads_hidden="admission")


def cleanup() -> Constitution:
    """A regulator revokes a doubted grant and issues a replacement.

    `act:cleanup` revokes the doubted warrant and inherits from nothing, so its
    grant is grounded in the charter alone and is legitimate. `act:relaunder` is
    the control: same shape, inheriting from the doubted warrant, and refused.

    The distinction survives compression, narrowed: grounds are always
    authorities, and what an act *revokes* constrains nothing.
    """
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((AUTH, "w:tainted", ALL),),
                scope=ALL, findings=frozenset({"f:planted"}), label="plant"),
            Act(1, "w:charter", revokes=("w:tainted",), inherits=(),
                grants=((AUTH, "w:proper", ALL),), scope=ALL,
                findings=frozenset({"f:audit"}), label="cleanup"),
            Act(2, "w:charter", inherits=("w:tainted",),
                grants=((AUTH, "w:carried", ALL),), scope=ALL,
                findings=frozenset({"f:audit"}), label="relaunder"),
        ),
        contexts=("alpha:audited",),
        doubted={"alpha:audited": ("f:planted",)},
    )


def repealable() -> Constitution:
    """A norm and a valid repeal of it, for the checker fixtures."""
    return Constitution(
        chartered=(("w:charter", ALL, "Assembly", AUTH),),
        acts=(
            Act(0, "w:charter", grants=((NORM, "n:obsolete", ()),), scope=ALL,
                findings=frozenset({"f:ordinary"}), label="enact"),
            Act(1, "w:charter", revokes=("n:obsolete",), inherits=(), scope=ALL,
                findings=frozenset({"f:review"}), label="repeal"),
        ),
    )


def myopic(p, skip: str):
    """A checker that refuses one valid edit — sound, and not complete.

    Sound because it only ever accepts what `valid` accepts. Incomplete because
    it declines the edit labelled `skip`. When that edit is a repeal the missed
    edit is a **disposal**, and the obsolete norm stays in the replay the checker
    drives, which is the asymmetry the two consumers do not share.
    """
    def verify(alpha, state, e):
        return str(e) != skip and p.valid(alpha, state, e)
    return verify
