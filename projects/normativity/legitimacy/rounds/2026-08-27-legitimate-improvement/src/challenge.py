"""Improvement challenges, as a canonical instance of frozen `Due` / `Resolve`.

Nothing in the frozen Legitimate Evolution package is edited here. This module
builds an `rp.Frame` and an `an.Duties` out of a learning trace and a comparison
surface, and everything it claims is then read off LE's own functions.

## What the challenge attaches to

Four candidates were prosecuted (`CHALLENGE.md` §3). The one adopted:

```text
the claim key is (repair identity, the evidence episode that supports it)
```

Not the repair alone: a repair retired twice, with evidence accumulated afresh
each time, owes two answers, and keying on the repair alone makes the second
invisible -- the same failure the frozen round found when activation memoized on
content. Not the diagnosed conduct alone: conduct recurs every occasion and
would mint an unbounded stream of claims, which is the "counting retirement
events cannot be enough" problem in its dual form. Not accumulated evidence
alone: evidence without a named alternative owes nothing anyone can act on.

## The activation rule is substantive, and is declared as such

```text
Due activates (r, e) at t  iff  the surface stopped r being an available
                                comparison at t -- by licence, by menu, or by
                                designation -- and comparative evidence for r
                                was demonstrated immediately before
```

**Designation is inside the surface, and that was a decision.** `CM6b` retires
nothing and de-lists nothing: it simply stops calling these occasions learning
occasions. An earlier version keyed activation on `licence and menu` only, and
`CM6b` escaped the trichotomy outright -- 240 diagnosed occasions with no claim
of any kind. Treating designation as a fourth component of the surface closes
that, at the cost of saying that ceasing to treat a recurring context as a
learning context is itself the kind of change that owes an answer. That is
substantive, and a constitution may decline it; `challenge.NARROW_SURFACE`
exhibits what is lost.

This is **not** the syntactic rule *every falling edge is Due*. A falling edge
with no accumulated evidence activates nothing, and `CM2` is exactly that case.
Whether that is right is a normative question this round does not settle; it is
recorded as the canonical constitution's content, and a different constitution
is free to be stricter.

`Due` is a **level**, as the frozen round requires, and `an.newly_due` takes the
rising edge. A challenge stays active while the repair remains retired and the
evidence remains represented, so re-retiring the same repair after a genuine new
evidence episode is a second rising edge and a second claim.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence

import replay as rp
import answer as an

import surface as sf


def demonstrated_map(ev) -> dict:
    """`t -> (episode key, demonstrated?)` from an `ImprovementEvidence`."""
    return {t: (("improve", ev.rid, e), d) for t, (e, _r, d) in ev.trace().items()}


# ------------------------------------------------------- the LE construction


def _noop_edit(label: str) -> rp.Edit:
    """An edit that changes no standing. The learning trace is not a normative
    trace, and the composition must not pretend otherwise: standing changes come
    from the constitution's own acts, and these are the occasions between them.
    """
    return rp.Edit(grounds=frozenset(), dispose=frozenset(), issues=(),
                   declared=None, label=label)


def frame(horizon: int, retirements: Mapping = None,
          refuse: Sequence[int] = ()) -> rp.Frame:
    """A frozen-LE frame over the learning horizon.

    One position per occasion. A retirement is an edit grounded in the base
    authority; `refuse` marks positions the semantics declines, which is how a
    fixture builds an *unentitled* retirement.
    """
    retirements = retirements or {}
    base_occ = rp.Occ(rp.BASE, 0)
    trace = []
    for t in range(horizon):
        if t in retirements:
            trace.append(rp.Edit(grounds=frozenset({base_occ}),
                                 dispose=frozenset(), issues=(),
                                 declared=retirements[t],
                                 label=f"retire@{t}"))
        else:
            trace.append(_noop_edit(f"occasion@{t}"))
    bad = set(refuse)
    return rp.Frame(base=frozenset({base_occ}), trace=tuple(trace),
                    auth=lambda o: True,
                    valid=lambda state, e, _bad=bad:
                        e.label.split("@")[-1].isdigit()
                        and int(e.label.split("@")[-1]) not in _bad)


def duties(f: rp.Frame, active: Mapping, opens: Mapping,
           discharges: Mapping = None) -> an.Duties:
    """Frozen-LE duties over the same horizon.

    `active[t]` is `ActiveDue_t`, the level. `opens[t]` maps a claim key to the
    occurrence that realizes it. `discharges[t]` is what `Resolve` judged done.
    """
    discharges = discharges or {}
    op, key, dis = {}, {}, {}
    for t, made in opens.items():
        obs = frozenset(an.Ob(t, i) for i in range(len(made)))
        op[t] = obs
        for i, k in enumerate(made):
            key[an.Ob(t, i)] = k
    by_key = {v: k for k, v in key.items()}
    for t, keys in discharges.items():
        got = frozenset(by_key[k] for k in keys if k in by_key)
        if got:
            dis[t] = got
    return an.Duties(base=frozenset(), opens=op, discharges=dis, transfers={},
                     drops={}, due=dict(active), key=key)


@dataclass
class Challenges:
    """The canonical constitution, executed.

    Built from a surface, an evidence trace and a horizon; exposes exactly the
    two predicates the trichotomy needs, both computed by frozen LE.
    """

    frame: rp.Frame
    duties: an.Duties
    keys: tuple

    def outstanding_keys(self, t: int) -> set:
        out = an.outstanding(self.frame, self.duties, t)
        return {self.duties.key_of(q) for q in out}

    def ever_keys(self, t: int) -> set:
        inc = an.incurred(self.frame, self.duties, t)
        return {self.duties.key_of(q) for q in inc}

    def outstanding_at(self, t: int) -> bool:
        return bool(self.outstanding_keys(t + 1) & set(self.keys))

    def settled_at(self, t: int) -> bool:
        ever = self.ever_keys(t + 1) & set(self.keys)
        return bool(ever) and not (self.outstanding_keys(t + 1) & set(self.keys))

    # ---- the frozen package's own verdicts, quoted rather than re-proved ----

    def le_premises(self) -> dict:
        return an.violations(self.frame, self.duties)

    def le_conformance(self) -> dict:
        return an.nonconformance(self.frame, self.duties)

    def le_resolution(self) -> tuple:
        return an.thm_answerability_resolution(self.frame, self.duties)

    def le_grounded(self) -> tuple:
        return rp.thm_grounded_replay(self.frame)


def build(surface: sf.Surface, rid, ev, horizon: int,
          settle_at: Mapping = None, refuse: Sequence[int] = (),
          retire_labels: Mapping = None) -> Challenges:
    """Assemble the canonical constitution from an `ImprovementEvidence`.

    `ActiveDue_t` holds a challenge key active exactly while the repair has been
    withdrawn **and** the evidence episode supporting it was demonstrated
    immediately before the withdrawal. It does **not** consult uptake regret: the
    challenge is grounded by the demonstration, not by the process having failed
    to act on it. A process that adopted the repair and then withdrew it owes the
    same answer as one that never adopted it.
    """
    settle_at = settle_at or {}
    f = frame(horizon, retire_labels or {}, refuse)
    dm = demonstrated_map(ev)

    active, opens, keys = {}, {}, []
    hot = {}
    for t in range(horizon):
        live = surface.live(rid, t) and float(surface.designated(t)) > 0
        if t not in dm:
            continue
        key, _d = dm[t]
        if not live:
            was = (t > 0 and surface.live(rid, t - 1)
                   and float(surface.designated(t - 1)) > 0)
            if was and t - 1 in dm:
                hot[key] = dm[t - 1][1]
            if hot.get(key, False):
                active[t] = frozenset({key})
                if key not in keys:
                    keys.append(key)
    for t in range(horizon):
        new = an.newly_due(an.Duties(frozenset(), {}, {}, {}, {}, active, {}), t)
        if new:
            opens[t] = tuple(sorted(new, key=str))
    d = duties(f, active, opens, settle_at)
    return Challenges(f, d, tuple(keys))


NARROW_SURFACE = """A constitution keying activation on licence and menu only.

Kept as a named alternative rather than deleted, because the difference is a
normative choice and not a bug: under it `CM6b` produces diagnosed conduct with
no live comparison and no challenge, which is the ESCAPED cell."""


def coherence_violations(surface: sf.Surface, rid, f: rp.Frame,
                         retire_labels: Mapping) -> tuple:
    """The surface must be a function of the legitimate state, not an oracle.

    Frozen LE says a refused edit changes no standing. If a fixture refuses a
    retirement while the surface de-licenses anyway, the two disagree and the
    composition is incoherent -- the process would be getting the benefit of a
    change the constitution declined.
    """
    accepted = set(rp.accepted(f))
    bad = []
    for t in sorted(retire_labels or {}):
        if t in accepted:
            continue
        after = [u for u in range(t, len(f.trace)) if not surface.licensed(rid, u)]
        if after:
            bad.append(("surface changed on a refused retirement", t))
    return tuple(bad)

