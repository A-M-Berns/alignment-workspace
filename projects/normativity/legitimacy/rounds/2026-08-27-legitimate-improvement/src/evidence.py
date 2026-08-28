"""Improvement evidence: the first of the three mechanisms, kept separate.

```text
evidence        why is r an improvement, and relative to what
uptake regret   while r is live, is the played policy leaving that unused
answerability   after r is withdrawn, what remains normatively live
```

The round's first version ran the second and called it the first. They are the
same functional `<d,l> - <d M_r,l>` against different distributions, and the
difference is not cosmetic: a process that has **adopted** a repair has zero
uptake regret and may still have large evidence, because evidence is measured
against what it would otherwise have done. Only uptake regret is bounded by
Theorem A, and nothing bounds evidence.

## The baseline is a supplied interface, not a privileged policy

Five candidates were prosecuted (`LEGITIMATE_IMPROVEMENT.md` §5). None is
privileged, so `Baseline` is a parameter with two conditions on it, and both are
checkable:

```text
predictable   b_t is a function of the prefix and the menu, never of l_t
recorded      b_t is committed before the loss is revealed
```

Predictability is what stops hindsight construction of an embarrassing baseline:
without it a consumer can pick, after the fact, whatever reference makes the
repair look best, and "demonstrated improvement" stops meaning anything.
`regret.predictability_violations` checks baselines with the same probe it uses
for selectors and repairs.

**`BASE_POLICY` is not frozen.** The fixtures use a stipulated unmodified-conduct
baseline because it is the clearest one to read, not because the round settled
that it is the right one.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence

import regret as rg


@dataclass(frozen=True)
class Baseline:
    """What the improvement is an improvement *over*.

    ```text
    UNMODIFIED   what the underlying procedure would do without the repair
    RECORDED     the pre-repair recommendation, as recorded at the time
    REFERENCE    a policy the consumer supplies
    SHADOW       an explicit shadow execution of the unmodified procedure
    ```

    All four are the same type here -- a predictable map from prefix and occasion
    to a distribution -- which is the round's answer to "which baseline is
    right": the theorem does not need to know. What it needs is that the choice
    is fixed in advance and scoreable, and full-information feedback scores both
    `b_t` and `b_t M_r` from the one revealed loss vector.
    """

    kind: str
    of: Callable                       # (prefix, occasion) -> distribution

    def __call__(self, prefix, occ):
        return self.of(prefix, occ)


def fixed(dist: Mapping, kind: str = "UNMODIFIED") -> Baseline:
    return Baseline(kind, lambda _p, _o, d=dict(dist): dict(d))


def played(kind: str = "RECORDED") -> Baseline:
    """The previous occasion's played distribution. Predictable by construction."""
    def of(prefix, occ):
        if not prefix:
            return {a: 1.0 / len(occ.menu) for a in occ.menu}
        return dict(prefix[-1][1])
    return Baseline(kind, of)


@dataclass
class ImprovementEvidence:
    """Accumulated demonstrated advantage of one repair over one baseline.

    Accrues only on occasions where the repair is a live designated comparison:
    evidence the surface has already withdrawn is not something the process is
    sitting on, and counting it would make the withdrawal generate its own
    justification.
    """

    rid: object
    comparator: rg.Comparator
    baseline: Baseline
    threshold: float
    live: Callable                     # (t) -> bool
    episode_of: Callable = None
    gains: dict = field(default_factory=dict)
    running: dict = field(default_factory=dict)

    def accrue(self, occ: rg.Occasion, prefix) -> float:
        t = occ.tag
        if not self.live(t):
            self.gains[t] = 0.0
        else:
            self.gains[t] = rg.advantage(occ, prefix, self.comparator,
                                         self.baseline(prefix, occ))
        ep = (self.episode_of or (lambda _t: 0))(t)
        run = self.running.get(ep, 0.0) + max(self.gains[t], 0.0)
        self.running[ep] = run
        return run

    def episode(self, t: int) -> int:
        return (self.episode_of or (lambda _t: 0))(t)

    def demonstrated_at(self, t: int) -> bool:
        return self.running.get(self.episode(t), 0.0) >= self.threshold

    def key(self, t: int):
        return ("improve", self.rid, self.episode(t))

    def trace(self) -> dict:
        """Per-occasion `(episode, accumulated, demonstrated)`."""
        out, run, cur = {}, 0.0, None
        for t in sorted(self.gains):
            ep = self.episode(t)
            if ep != cur:
                cur, run = ep, 0.0
            run += max(self.gains[t], 0.0)
            out[t] = (ep, run, run >= self.threshold)
        return out


def independence_report(learner: rg.Learner, ev: ImprovementEvidence,
                        name: str) -> dict:
    """The two quantities side by side, which is the point of the split.

    `uptake` is what Theorem A bounds; `evidence` is what grounds a challenge.
    A well-behaved process drives the first to zero and the second up.
    """
    return {"uptake": learner.adv.get(name, 0.0),
            "uptake_bound": learner.bound(name),
            "evidence": sum(max(g, 0.0) for g in ev.gains.values()),
            "demonstrated": any(d for _e, _r, d in ev.trace().values())}
