"""A second realization, with no normative record anywhere in it.

A register of warrants and the acts that granted them: an office issues a
warrant, a warrant-holder issues another, warrants are revoked and reassigned.
The challenge is "suppose this finding of fact had never been made", and an act
is stable when none of the findings it relied on is void.

**This module imports nothing from `ri_core`, `enrichment` or `legitimacy`.** It
exists so that the axioms and the theorems of `frame.py` can be run against a
system that is not this repository's architecture, which is the only evidence
that the interface is about legitimacy rather than about a ledger.

The register is deliberately mundane. Nothing in it is a reason occurrence, a
standing view or a replay; `grant` is an ordinary act, `finding` is an ordinary
fact, and the counterfactual is set subtraction over a dependency graph rather
than a re-evaluation of an evolving state. That difference is itself a result:
**L3 is free in a monotone dependency model and is a real hypothesis in a replay
model**, and `THEOREM_MAP.md` entry 6 is where it is recorded.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping, Optional, Sequence

import frame as fr


@dataclass(frozen=True)
class Act:
    """One act on the register.

    `revokes` are the warrants it takes away and `grants` the ones it creates;
    `under` is the warrant the actor held; `relies_on` are the findings of fact
    the act was made on. An act that revokes and grants nothing is a
    reassignment: it moves `to` and leaves the warrant alone.
    """

    id: str
    at: int
    under: str
    revokes: tuple = ()
    grants: tuple = ()
    reassigns: Optional[str] = None
    to: Optional[str] = None
    relies_on: frozenset = frozenset()


@dataclass(frozen=True)
class Register:
    chartered: tuple                 # warrants in force at the outset
    holder0: Mapping                 # warrant -> party, at the outset
    acts: tuple
    findings: Mapping                # finding -> the act that established it, or None
    challenges: tuple = ()           # challenge id -> the findings it voids
    voids: Mapping = field(default_factory=dict)


def void_findings(reg: Register, q) -> frozenset:
    """The findings the challenge voids, closed under the acts that made them."""
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

    The recursion is over the act that granted the warrant it was made under,
    which is what makes the model's `L3'` hold rather than be stipulated.
    """
    if act.relies_on & void_findings(reg, q):
        return False
    granting = _granting_act(reg, act.under)
    return granting is None or act_stands(reg, q, granting)


def _granting_act(reg: Register, warrant: str) -> Optional[Act]:
    for a in reg.acts:
        if warrant in a.grants:
            return a
    return None


def build(reg: Register):
    """The frame and account layer the register realizes."""
    warrants = set(reg.chartered)
    for a in reg.acts:
        warrants |= set(a.grants) | set(a.revokes)
        if a.reassigns:
            warrants.add(a.reassigns)

    src, tgt, lic, rank = {}, {}, {}, {}
    for a in reg.acts:
        if a.reassigns:
            src[a.id] = tgt[a.id] = frozenset({a.reassigns})
        else:
            src[a.id] = frozenset(a.revokes)
            tgt[a.id] = frozenset(a.grants)
        lic[a.id] = a.under
        rank[a.id] = 2 * a.at - 1
        for w in tgt[a.id] - src[a.id]:
            rank[w] = 2 * a.at
    for w in reg.chartered:
        rank[w] = 0

    by_id = {a.id: a for a in reg.acts}
    chal = {q: frozenset(a.id for a in reg.acts
                         if a.relies_on & void_findings(reg, q))
            for q in reg.challenges}

    def stable(q, u) -> bool:
        if u in by_id:
            return act_stands(reg, q, by_id[u])
        if u in reg.chartered:
            return True
        granting = _granting_act(reg, u)
        return granting is not None and act_stands(reg, q, granting)

    revoked = frozenset().union(frozenset(), *[src[a.id] for a in reg.acts
                                               if not a.reassigns])
    f = fr.Frame(frozenset(warrants), frozenset(by_id), src, tgt, lic, rank,
                 frozenset(reg.chartered), frozenset(warrants) - revoked,
                 tuple(reg.challenges), chal, stable)

    # one account per warrant per custody spell; ended by revocation or reassignment
    accounts, holder, subject = {}, {}, {}
    for w in reg.chartered:
        accounts[f"acct:{w}@0"] = None
        holder[f"acct:{w}@0"] = reg.holder0.get(w, "charter")
        subject[f"acct:{w}@0"] = w
    ends, opens = {}, {}
    live = {w: f"acct:{w}@0" for w in reg.chartered}
    answered = set()
    for a in reg.acts:
        ends[a.id] = frozenset(live[w] for w in src[a.id] if w in live)
        made = set()
        for w in sorted(tgt[a.id]):
            key = f"acct:{w}@{a.at}"
            accounts[key] = None
            holder[key] = a.to if a.reassigns else _actor(reg, a)
            subject[key] = w
            live[w] = key
            made.add(key)
        opens[a.id] = frozenset(made)
        if a.id not in reg.voids.get("__unanswered__", ()):
            answered |= ends[a.id]
    acc = fr.Accounts(frozenset(accounts), holder, ends, opens, subject,
                      lambda k: k in answered)
    return f, acc


def _actor(reg: Register, a: Act) -> str:
    granting = _granting_act(reg, a.under)
    if granting is not None and granting.to:
        return granting.to
    return reg.holder0.get(a.under, "charter")


# ----------------------------------------------------------------- examples


def clean_register() -> Register:
    """A charter, a delegated warrant, a revision of it, and a reassignment.

    The second warrant's content differs from the first's — a different scope —
    and every act relies on findings the challenge leaves alone.
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
    """The warrant an inspector cites was granted on the finding now challenged.

    Nothing about this register is a normative record, and the interface refuses
    it for the same reason it refuses the manufactured-authority record: the
    licensing warrant does not survive its own challenge.
    """
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


def merge_register() -> Register:
    """An act revoking two warrants, one manufactured, and issuing one successor.

    The act relies only on findings the challenge leaves alone and holds the
    power to revoke both. Requiring **all** of `src(t)` to be derivable refuses
    the successor; requiring one of them accepts it. The two rules disagree here
    and nowhere in the Reflective Integrity realization, whose preconditions make
    a supersession inadmissible as soon as one of its targets is absent — so the
    choice is visible in this model and invisible in that one.
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
