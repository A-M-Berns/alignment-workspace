"""A realization with no normative record anywhere in it.

A register of warrants and the acts that granted them: an office issues a
warrant, a warrant-holder issues another, warrants are revoked, superseded and
reassigned. The challenge is "suppose this finding of fact had never been made",
and an act stands when none of the findings it relied on is void.

**This module imports `frame` and the standard library and nothing else.**
`tests/test_frame.py` checks that by parsing its imports. It exists so the axioms
and theorems of `frame.py` can be run against a system that is not this
repository's architecture, which is the only evidence the interface is about
legitimacy rather than about a ledger.

It also decides three questions our own architecture cannot see, because
Reflective Integrity's admission preconditions make the alternatives
indistinguishable there: whether a licence must be legitimately grounded, whether
an exercise's legitimacy parents are the objects it acts on, and whether lineage
existence needs unique issuance.

An `Act` therefore carries `revokes` and `inherits` separately. Ordinary
supersession sets both; a cleanup revokes without inheriting.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping, Optional, Sequence

import frame as fr


@dataclass(frozen=True)
class Act:
    """One act on the register.

    `revokes` are the warrants it takes away — the positions it acts on.
    `inherits` are the warrants its grant draws its entitlement from; where it is
    `None` the act inherits from exactly what it revokes, which is the ordinary
    case. `under` is the warrant the actor held. `relies_on` are the findings of
    fact the act was made on. `reassigns` moves a warrant to a new holder and
    changes nothing else.
    """

    id: str
    at: int
    under: str
    revokes: tuple = ()
    grants: tuple = ()
    inherits: Optional[tuple] = None
    reassigns: Optional[str] = None
    to: Optional[str] = None
    relies_on: frozenset = frozenset()

    @property
    def parents(self) -> tuple:
        if self.reassigns:
            return (self.reassigns,)
        return self.revokes if self.inherits is None else self.inherits


@dataclass(frozen=True)
class Register:
    chartered: tuple
    holder0: Mapping
    acts: tuple
    findings: Mapping                # finding -> the act that established it, or None
    challenges: tuple = ()
    voids: Mapping = field(default_factory=dict)
    unanswered: tuple = ()           # acts whose ended accounts nobody answers


def void_findings(reg: Register, q) -> frozenset:
    out, frontier = set(reg.voids.get(q, ())), list(reg.voids.get(q, ()))
    by_act = {}
    for fnd, act in reg.findings.items():
        by_act.setdefault(act, set()).add(fnd)
    while frontier:
        fnd = frontier.pop()
        act = reg.findings.get(fnd)
        if act is None:
            continue
        for other in by_act.get(act, ()) - out:
            out.add(other)
            frontier.append(other)
    return frozenset(out)


def act_stands(reg: Register, q, act: Act) -> bool:
    """An act stands unless something it relied on is void, transitively.

    The recursion runs through the act that granted the warrant it was made
    under, which is what makes `L3'` hold in this model rather than be
    stipulated. It does **not** run through what the act revokes: whether the
    thing you are cancelling was properly granted has no bearing on whether your
    cancelling of it happened.
    """
    if act.relies_on & void_findings(reg, q):
        return False
    granting = _granting_acts(reg, act.under)
    return not granting or any(act_stands(reg, q, g) for g in granting)


def _granting_act(reg: Register, warrant: str) -> Optional[Act]:
    for a in reg.acts:
        if warrant in a.grants:
            return a
    return None


def _granting_acts(reg: Register, warrant: str) -> tuple:
    return tuple(a for a in reg.acts if warrant in a.grants)


def build(reg: Register):
    """The frame and the account layer the register realizes."""
    warrants = set(reg.chartered)
    for a in reg.acts:
        warrants |= set(a.grants) | set(a.revokes) | set(a.parents)
        if a.reassigns:
            warrants.add(a.reassigns)

    affected, parents, tgt, lic, rank, when = {}, {}, {}, {}, {}, {}
    for a in reg.acts:
        if a.reassigns:
            affected[a.id] = tgt[a.id] = frozenset({a.reassigns})
        else:
            affected[a.id] = frozenset(a.revokes)
            tgt[a.id] = frozenset(a.grants)
        parents[a.id] = frozenset(a.parents)
        lic[a.id] = a.under
        rank[a.id] = 2 * a.at - 1
        when[a.id] = a.at
        for w in tgt[a.id] - affected[a.id]:
            rank[w] = 2 * a.at
    for w in reg.chartered:
        rank[w] = 0
    for w in warrants:
        rank.setdefault(w, 0)

    chal = {q: frozenset(a.id for a in reg.acts
                         if a.relies_on & void_findings(reg, q))
            for q in reg.challenges}
    by_id = {a.id: a for a in reg.acts}

    def stable(q, u) -> bool:
        if u in by_id:
            return act_stands(reg, q, by_id[u])
        if u in reg.chartered:
            return True
        granting = _granting_acts(reg, u)
        return any(act_stands(reg, q, g) for g in granting)

    times = tuple(sorted({0} | {a.at for a in reg.acts}))
    live, current = {}, set(reg.chartered)
    live[0] = frozenset(current)
    for s in times[1:]:
        for a in reg.acts:
            if a.at != s or a.reassigns:
                continue
            current -= set(a.revokes)
            current |= set(a.grants)
        live[s] = frozenset(current)

    f = fr.Frame(frozenset(warrants), frozenset(by_id), affected, parents, tgt,
                 lic, rank, frozenset(reg.chartered), tuple(reg.challenges),
                 chal, stable, when, live, times)

    accounts, holder, subject = {}, {}, {}
    for w in reg.chartered:
        key = f"acct:{w}@0"
        accounts[key] = None
        holder[key] = reg.holder0.get(w, "charter")
        subject[key] = w
    ends, opens = {}, {}
    alive = {w: f"acct:{w}@0" for w in reg.chartered}
    answered = set()
    for a in reg.acts:
        ends[a.id] = frozenset(alive[w] for w in affected[a.id] if w in alive)
        made = set()
        for w in sorted(tgt[a.id]):
            key = f"acct:{w}@{a.at}"
            accounts[key] = None
            holder[key] = a.to if a.reassigns else _actor(reg, a)
            subject[key] = w
            alive[w] = key
            made.add(key)
        opens[a.id] = frozenset(made)
        if a.id not in reg.unanswered:
            answered |= ends[a.id]
    acc = fr.Accounts(frozenset(accounts), holder, ends, opens, subject,
                      lambda k: k in answered)
    return f, acc


def _actor(reg: Register, a: Act) -> str:
    granting = _granting_act(reg, a.under)
    if granting is not None and granting.to:
        return granting.to
    return reg.holder0.get(a.under, "charter")


# ----------------------------------------------------------------- registers


def clean_register() -> Register:
    """A charter, a delegated warrant, a revision of it, and a reassignment.

    The second warrant's scope differs from the first's, and every act relies on
    findings the challenge leaves alone.
    """
    return Register(
        chartered=("w:charter", "w:seal"),
        holder0={"w:charter": "Assembly", "w:seal": "Assembly"},
        acts=(
            Act("act:appoint", 1, "w:charter", grants=("w:inspector",),
                relies_on=frozenset({"f:vacancy"})),
            Act("act:widen", 2, "w:charter", revokes=("w:inspector",),
                grants=("w:inspector-2",), relies_on=frozenset({"f:report"})),
            Act("act:handover", 3, "w:seal", reassigns="w:inspector-2",
                to="Delegate", relies_on=frozenset({"f:resignation"})),
        ),
        findings={"f:vacancy": None, "f:report": None, "f:resignation": None,
                  "f:rumour": "act:appoint"},
        challenges=("q:rumour",),
        voids={"q:rumour": ("f:rumour",)},
    )


def laundered_register() -> Register:
    """The warrant an inspector cites was granted on the finding now challenged."""
    return Register(
        chartered=("w:charter",),
        holder0={"w:charter": "Assembly"},
        acts=(
            Act("act:manufacture", 1, "w:charter", grants=("w:special",),
                relies_on=frozenset({"f:planted"})),
            Act("act:exercise", 2, "w:special", grants=("w:permit",),
                relies_on=frozenset({"f:ordinary"})),
        ),
        findings={"f:planted": None, "f:ordinary": None},
        challenges=("q:campaign",),
        voids={"q:campaign": ("f:planted",)},
    )


def stable_but_illegitimate_register() -> Register:
    """The attack that refuted the first pass's no-bootstrap theorem.

    ```text
    act:plant     challenged; grants w:tainted
    act:launder   clean findings, under the charter; supersedes w:tainted by w:m
    act:use       under w:m; grants w:y
    ```

    `w:m` **survives** the challenge — the act that granted it relies on nothing
    void — and is **not** derivable, because it inherits from `w:tainted`. Under
    the first pass's rule a licence had only to be stable, so `w:y` was derivable
    while a challenged act sat in its ancestry. Under the repaired rule the
    licence must itself be derivable and `w:y` is refused.

    This is the register on which the difference between *surviving a
    counterfactual* and *being entitled* is a fact rather than a slogan.
    """
    return Register(
        chartered=("w:charter",),
        holder0={"w:charter": "Assembly"},
        acts=(
            Act("act:plant", 1, "w:charter", grants=("w:tainted",),
                relies_on=frozenset({"f:planted"})),
            Act("act:launder", 2, "w:charter", revokes=("w:tainted",),
                grants=("w:m",), relies_on=frozenset({"f:ordinary"})),
            Act("act:use", 3, "w:m", grants=("w:y",),
                relies_on=frozenset({"f:ordinary"})),
        ),
        findings={"f:planted": None, "f:ordinary": None},
        challenges=("q:campaign",),
        voids={"q:campaign": ("f:planted",)},
    )


def cleanup_register() -> Register:
    """A regulator revokes a fraudulent warrant and grants a proper one.

    `act:cleanup` acts on `w:tainted` and inherits from the charter, not from it.
    The successor is derivable, which is the answer this round gives to *must a
    legitimate cleanup of an illegitimate standing produce an illegitimate
    successor?* — no, and the register is why `affected` and `parents` are two
    fields.

    `act:relaunder` is the control: same shape, but it inherits from the tainted
    warrant, and its successor is refused.
    """
    return Register(
        chartered=("w:charter",),
        holder0={"w:charter": "Assembly"},
        acts=(
            Act("act:plant", 1, "w:charter", grants=("w:tainted",),
                relies_on=frozenset({"f:planted"})),
            Act("act:cleanup", 2, "w:charter", revokes=("w:tainted",),
                grants=("w:proper",), inherits=(),
                relies_on=frozenset({"f:audit"})),
            Act("act:relaunder", 3, "w:charter", grants=("w:carried",),
                inherits=("w:tainted",), relies_on=frozenset({"f:audit"})),
        ),
        findings={"f:planted": None, "f:audit": None},
        challenges=("q:campaign",),
        voids={"q:campaign": ("f:planted",)},
    )


def merge_register() -> Register:
    """An act inheriting from two warrants, one manufactured, one earned.

    The act relies only on clean findings and holds the power over both.
    Requiring **all** of `parents(t)` refuses the successor; requiring one of
    them admits it. The two rules disagree here and nowhere in the Reflective
    Integrity realization, whose preconditions make a supersession with an absent
    target inadmissible anyway.
    """
    return Register(
        chartered=("w:charter",),
        holder0={"w:charter": "Assembly"},
        acts=(
            Act("act:plant", 1, "w:charter", grants=("w:planted",),
                relies_on=frozenset({"f:planted"})),
            Act("act:earn", 2, "w:charter", grants=("w:earned",),
                relies_on=frozenset({"f:ordinary"})),
            Act("act:merge", 3, "w:charter",
                revokes=("w:planted", "w:earned"), grants=("w:merged",),
                relies_on=frozenset({"f:ordinary"})),
        ),
        findings={"f:planted": None, "f:ordinary": None},
        challenges=("q:campaign",),
        voids={"q:campaign": ("f:planted",)},
    )


def two_issuers_register() -> Register:
    """One warrant granted twice — once on a challenged finding, once cleanly.

    A register with two chanceries and no central roll: the same warrant is
    entered by each. Unique issuance fails, lineage existence does not, and the
    warrant is derivable by the clean route while the challenged route sits in
    its route-blind provenance.

    This is what decides that the no-bootstrap theorem must be stated over a
    derivation rather than over the union of every ancestor.
    """
    return Register(
        chartered=("w:charter",),
        holder0={"w:charter": "Assembly"},
        acts=(
            Act("act:chancery-a", 1, "w:charter", grants=("w:dual",),
                relies_on=frozenset({"f:planted"})),
            Act("act:chancery-b", 2, "w:charter", grants=("w:dual",),
                relies_on=frozenset({"f:ordinary"})),
            Act("act:act-on-it", 3, "w:dual", grants=("w:downstream",),
                relies_on=frozenset({"f:ordinary"})),
        ),
        findings={"f:planted": None, "f:ordinary": None},
        challenges=("q:campaign",),
        voids={"q:campaign": ("f:planted",)},
    )


def undercovered_register() -> Register:
    """A structurally perfect register that challenges nothing.

    Every axiom of the spine holds vacuously, everything is derivable, and the
    influence anyone would worry about is not in `Q` at all. The threat model in
    `undercovered_threat` is what refuses it.
    """
    return Register(
        chartered=("w:charter",),
        holder0={"w:charter": "Assembly"},
        acts=(
            Act("act:capture", 1, "w:charter", grants=("w:captured",),
                relies_on=frozenset({"f:planted"})),
            Act("act:exercise", 2, "w:captured", grants=("w:permit",),
                relies_on=frozenset({"f:ordinary"})),
        ),
        findings={"f:planted": None, "f:ordinary": None},
        challenges=(),
        voids={},
    )


def undercovered_threat() -> fr.ThreatModel:
    """The influence the undercovered register does not challenge."""
    return fr.ThreatModel(("xi:capture",),
                          {"xi:capture": frozenset({"act:capture"})})


def covered_threat() -> fr.ThreatModel:
    """The same influence, against a register that does challenge it."""
    return fr.ThreatModel(("xi:capture",),
                          {"xi:capture": frozenset({"act:manufacture"})})


def unanswered_delegation_register() -> Register:
    """A reassignment nobody answers for: a clean spine and an open account."""
    reg = clean_register()
    return Register(reg.chartered, reg.holder0, reg.acts, reg.findings,
                    reg.challenges, reg.voids, unanswered=("act:handover",))
