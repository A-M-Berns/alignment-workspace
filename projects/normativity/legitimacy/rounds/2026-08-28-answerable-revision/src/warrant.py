"""Answerable Revision: standards may change; reasons incurred under them remain.

The round above `2026-08-27-legitimate-improvement`. That round asked what happens
when a *repair* is withdrawn after it has been demonstrated. This one asks what
happens when the **standards deciding what counts as a reason for revision** are
themselves revised.

```text
P_t       the substantive policy or procedure
Lambda_t  the evaluator or audit standard
W_t       the comparison warrant: what evidence is entitled to count as a reason
```

All three may legitimately change. The candidate invariant is not a fixed target:

> A reason legitimately generated under the standards then in force cannot be
> retroactively erased merely because those standards later change.

## The four things that must not collapse

```text
a true counterfactual comparison   epistemic validity
admissible evidence                what a standing warrant will look at
a revision reason                  what promotion produces
a Due obligation                   what a supplied Due semantics may then say
```

`Promote(W_t, E) = rho` is the hinge, and it reads `W` at the **strict
pre-state**: the warrant standing *before* this event's own revision takes
effect. Without that, a revision installs a warrant and uses it to license its own
installation, which is `AR8`.

## Where the content actually is

Most of the theorem is inherited. Frozen `A1` already says an incurred claim
leaves the outstanding set only through an accepted `Resolve`, and frozen
`Incurred` never shrinks. So if promotion *incurs*, warrant revision cannot remove
what was promoted -- a warrant change is not a resolution.

The real requirement is that the promotion record is **write-once**. If a later
warrant may recompute what was promoted earlier, `Incurred` is no longer a
historical fact and the whole thing collapses. That is `P1`, it is the premise
that can fail, and `AR4` is the process that violates it.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence

import replay as rp
import answer as an


# ------------------------------------------------------------- the warrant


@dataclass(frozen=True)
class Warrant:
    """What evidence is entitled to count as a reason, concerning what.

    `target` may name a policy, an evaluator, **or another warrant** -- including
    this one. That is what makes the machinery reflective without a meta
    hierarchy: a warrant criticising a warrant is an ordinary instance, and
    `AR10` is the fixture.
    """

    wid: str
    target: str
    admits: Callable                   # (evidence) -> bool
    promotes: Callable                 # (evidence) -> reason payload or None

    def promote(self, ev):
        """`Promote(W, E)`. Admissibility first, then the promotion rule.

        Both are the warrant's own content and neither is decided here. The
        generic theorem is parametric over legitimately standing warrants and
        takes no view on which admissibility rule is correct.
        """
        if not self.admits(ev):
            return None
        return self.promotes(ev)


@dataclass(frozen=True)
class Evidence:
    """A represented comparative finding. Carries no normative force by itself."""

    eid: str
    about: str                         # the subsystem it concerns
    form: str                          # the comparative form
    strength: float = 1.0


@dataclass(frozen=True)
class Reason:
    """A promoted revision reason. Identity records *where it came from*.

    The warrant and the position are part of the identity because the claim the
    theorem makes is historical: this reason was promoted **under that warrant, at
    that time**. A later warrant cannot make it a different reason, and cannot
    make it not have happened.
    """

    payload: str
    under: str                         # the warrant that promoted it
    at: int                            # the position at which it was promoted

    @property
    def key(self):
        return ("reason", self.payload, self.under, self.at)


# ------------------------------------------------------- the revisable state


@dataclass
class History:
    """A trace of events. Each may revise the warrant, and each may promote.

    `standing` is the warrant in force at the **strict pre-state** of each
    position: `standing[t]` is what was in force *before* the event at `t` did
    anything. That is the whole of the non-circularity discipline, and
    `self_authorising` is the check.
    """

    warrants: dict = field(default_factory=dict)      # position -> Warrant
    installs: dict = field(default_factory=dict)      # position -> Warrant
    evidence: dict = field(default_factory=dict)      # position -> [Evidence]
    resolutions: dict = field(default_factory=dict)   # position -> [reason keys]
    horizon: int = 0
    #: a fixture may set this to recompute history under the current warrant,
    #: which is the P1 violation.
    retroactive: bool = False

    def standing(self, t: int) -> Optional[Warrant]:
        """The warrant in force at the strict pre-state of `t`."""
        cur = self.warrants.get(-1)
        for u in range(t):
            if u in self.installs:
                cur = self.installs[u]
        return cur

    def promoted_at(self, t: int) -> tuple:
        """The reasons promoted at `t`, as recorded then.

        With `retroactive` set, the record is recomputed under the **latest**
        warrant instead of the one that was standing. That is exactly the
        laundering move -- *our standards changed, so that was never a reason* --
        and it is representable so that `P1` is a premise rather than a fact
        about the type.
        """
        w = self.standing(self.horizon) if self.retroactive else self.standing(t)
        if w is None:
            return ()
        out = []
        for ev in self.evidence.get(t, ()):
            payload = w.promote(ev)
            if payload is not None:
                out.append(Reason(payload, w.wid, t))
        return tuple(out)

    def all_promoted(self) -> dict:
        return {t: self.promoted_at(t) for t in range(self.horizon)}


# ------------------------------------------------------------- the premises


def p1_promotion_permanence(h: History) -> tuple:
    """**P1.** What was promoted at `t` is a function of the state at `t`.

    Compare the record as it stands against the record each position would have
    produced under the warrant that was actually standing there. A process that
    re-derives its own past under present standards fails this, and nothing in
    frozen Legitimate Evolution would notice: its premises are about how claims
    *leave* the outstanding set, and this attack never lets them arrive.

    Returns the positions where the two disagree.
    """
    bad = []
    for t in range(h.horizon):
        w = h.standing(t)
        honest = []
        if w is not None:
            for ev in h.evidence.get(t, ()):
                payload = w.promote(ev)
                if payload is not None:
                    honest.append(Reason(payload, w.wid, t))
        if tuple(honest) != h.promoted_at(t):
            bad.append((t, tuple(r.key for r in honest),
                        tuple(r.key for r in h.promoted_at(t))))
    return tuple(bad)


def self_authorising(h: History) -> tuple:
    """**Strict pre-state.** No event may promote under a warrant it installs.

    `AR8`. `standing(t)` reads only installs strictly before `t`, so this is
    structural rather than a clause -- the check exists to show the model can
    express the attack and refuses it, not to do the refusing.
    """
    bad = []
    for t in range(h.horizon):
        if t not in h.installs:
            continue
        new = h.installs[t]
        for r in h.promoted_at(t):
            if r.under == new.wid:
                bad.append(("promoted under the warrant it installed", t, r.key))
    return tuple(bad)


PREMISES = (("P1", p1_promotion_permanence),)
DISCIPLINE = (("strict-prestate", self_authorising),)


def violations(h: History) -> dict:
    return {n: c(h) for n, c in PREMISES + DISCIPLINE if c(h)}


# ------------------------------------------------ the frozen-LE construction


def frame(h: History) -> rp.Frame:
    base = rp.Occ(rp.BASE, 0)
    trace = tuple(rp.Edit(grounds=frozenset({base}), dispose=frozenset(),
                          issues=(), declared=None, label=f"e{t}")
                  for t in range(h.horizon))
    return rp.Frame(base=frozenset({base}), trace=trace, auth=lambda o: True,
                    valid=lambda _s, _e: True)


def duties(h: History) -> an.Duties:
    """Promotion becomes `opens`; resolution becomes `discharges`.

    Nothing else is wired. The theorem below is then read off frozen LE, which is
    the point: the new content is the promotion semantics, not a new replay.
    """
    opens, key, by_key = {}, {}, {}
    for t in range(h.horizon):
        made = h.promoted_at(t)
        if not made:
            continue
        obs = []
        for i, r in enumerate(made):
            q = an.Ob(t, i)
            key[q] = r.key
            by_key[r.key] = q
            obs.append(q)
        opens[t] = frozenset(obs)
    dis = {}
    for t, keys in h.resolutions.items():
        got = frozenset(by_key[k] for k in keys if k in by_key)
        if got:
            dis[t] = got
    return an.Duties(base=frozenset(), opens=opens, discharges=dis,
                     transfers={}, drops={}, due={}, key=key)


# ------------------------------------------------------------- the theorem


@dataclass
class Revision:
    """One executed history, with frozen LE's verdicts available."""

    name: str
    history: History
    frame: rp.Frame
    duties: an.Duties

    def incurred_keys(self, t: Optional[int] = None) -> set:
        return {self.duties.key_of(q)
                for q in an.incurred(self.frame, self.duties, t)}

    def outstanding_keys(self, t: Optional[int] = None) -> set:
        return {self.duties.key_of(q)
                for q in an.outstanding(self.frame, self.duties, t)}

    def occurred_legitimately(self, key) -> bool:
        """**Historical validity.** Was this promoted under a then-standing
        warrant? A fact about the past, and nothing later can change it."""
        for t in range(self.history.horizon):
            w = self.history.standing(t)
            if w is None:
                continue
            for ev in self.history.evidence.get(t, ()):
                payload = w.promote(ev)
                if payload is not None and Reason(payload, w.wid, t).key == key:
                    return True
        return False

    def currently_endorsed(self, key) -> bool:
        """**Current endorsement.** Would the warrant standing now promote it?

        Deliberately a different predicate. §13 of the dispatch is the whole
        point: these may diverge, and the theorem depends on the first only.
        """
        w = self.history.standing(self.history.horizon)
        if w is None:
            return False
        for t in range(self.history.horizon):
            for ev in self.history.evidence.get(t, ()):
                payload = w.promote(ev)
                if payload is not None and payload == key[1]:
                    return True
        return False

    def answered(self, key, t: Optional[int] = None) -> bool:
        return key in self.incurred_keys(t) and key not in self.outstanding_keys(t)


def build(name: str, h: History) -> Revision:
    return Revision(name, h, frame(h), duties(h))


def thm_answerable_revision(rev: Revision) -> tuple:
    """**Answerable Revision.** Under `P1` and frozen `A1`: if a reason was
    promoted at `t` under the warrant then standing, then at every later `s` it
    is incurred, and it is either outstanding at `s` or was resolved by an
    accepted resolution in `(t, s]`.

    *Proof.* Promotion at `t` puts the reason in `opens_t`, so by frozen
    `Incurred_{t+1} = Incurred_t u opens_t` it is incurred from `t+1` on, and
    `Incurred` never shrinks. By frozen `A1` it leaves the outstanding set only
    through a `Resolve` the process accepted. A warrant revision is not a
    resolution and appears nowhere in either fold. Hence at every later `s` it is
    outstanding or resolved. ∎

    The proof is short because it is nearly all inherited. What is **not**
    inherited is `P1`: without it the reason never enters `opens_t` in the first
    place, and frozen LE has nothing to say, because its premises govern how
    claims leave rather than whether they arrive.

    Returns `(key, s)` pairs that are neither outstanding nor answered.
    """
    bad = []
    for t in range(rev.history.horizon):
        for r in rev.history.promoted_at(t):
            for s in range(t + 1, rev.history.horizon + 1):
                if r.key in rev.outstanding_keys(s):
                    continue
                if rev.answered(r.key, s):
                    continue
                bad.append((r.key, s))
                break
    return tuple(bad)


def cor_no_retroactive_erasure(rev: Revision) -> tuple:
    """**Corollary.** A reason that occurred legitimately is incurred at the end,
    whatever the warrant now says.

    This is the laundering attack refused: *`W_t` no longer stands, therefore
    `rho` was never a reason*. Returns the keys that occurred legitimately and
    are nonetheless absent from the final incurred set.
    """
    bad = []
    for t in range(rev.history.horizon):
        w = rev.history.standing(t)
        if w is None:
            continue
        for ev in rev.history.evidence.get(t, ()):
            payload = w.promote(ev)
            if payload is None:
                continue
            k = Reason(payload, w.wid, t).key
            if k not in rev.incurred_keys():
                bad.append(k)
    return tuple(bad)


def divergences(rev: Revision) -> tuple:
    """Keys that occurred legitimately and are not currently endorsed.

    Not a violation. It is the state the round exists to make expressible: *this
    really was a reason we incurred under our then-legitimate standards, and we
    now reject its force*. A process saying that is revising; a process saying
    the reason never existed is laundering.
    """
    return tuple(k for k in sorted(rev.incurred_keys(), key=str)
                 if rev.occurred_legitimately(k) and not rev.currently_endorsed(k))
