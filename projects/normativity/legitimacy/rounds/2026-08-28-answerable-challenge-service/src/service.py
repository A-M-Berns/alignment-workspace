"""Answerable challenge service: the layer below promotion.

Two rounds sit above this one. `2026-08-28-answerable-revision` says a *promoted*
reason survives revision of the standards that promoted it, and stops there;
`2026-08-27-legitimate-improvement` says a *demonstrated* repair cannot be escaped
by withdrawing the comparison, and stops there. Both found the same boundary from
different directions: change the machinery **before** anything is promoted or
demonstrated and there is nothing yet for either theorem to preserve.

This round asks whether one intermediate object closes that gap.

```text
potential criticism      may exist and be wholly unrepresented
REGISTERED CHALLENGE     has procedural standing in the process
adjudicated evidence     accumulated under the challenge
promoted reason          evidence promoted under a warrant     -> the round above
Due claim                supplied semantics says a response is owed
```

A registered challenge is **not yet a reason for revision**. It may be wrong,
duplicative, unsafe to test or already answered. The thesis is only that
non-address requires an answer too.

## What is inherited and what is new

Challenge continuity is almost entirely frozen Legitimate Evolution again:
registration opens a claim, `A1` lets it leave only by an accepted resolution,
and `Incurred` never shrinks. Saying that plainly is a condition of the round,
since two rounds in a row have now had short closure arguments and long premise
sections.

The new content is in two places and neither is a closure theorem:

```text
episode pinning   an open challenge's adjudication terms are fixed at
                  registration; changing them for that challenge needs an
                  explicit transfer, not a silent reinterpretation
service           an open undefeated challenge cannot be starved of
                  adjudicative opportunity forever
```

Service is the genuinely new mathematical burden. Frozen `A1` is perfectly happy
with a claim that stays outstanding forever while nothing is ever done about it.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence

import replay as rp
import answer as an


# ------------------------------------------------------------- the objects


@dataclass(frozen=True)
class Terms:
    """The adjudication terms of one challenge episode.

    Pinned at registration. A global change to any of these applies to **new**
    registrations; applying it to an open episode requires an explicit transfer.
    """

    threshold: float
    evaluator: str
    protocol: str

    def __str__(self) -> str:
        return f"{self.protocol}/{self.evaluator}@{self.threshold:g}"


@dataclass(frozen=True)
class Challenge:
    """A criticism with procedural standing.

    Identity carries the registration position and the terms in force then, for
    the same reason the round above put the warrant into a reason's identity:
    the claim being made is historical.
    """

    cid: str
    target: str
    at: int
    terms: Terms

    @property
    def key(self):
        return ("challenge", self.cid, self.at)


@dataclass(frozen=True)
class Defeater:
    """A represented reason for not addressing a challenge.

    `installed` is when the rule permitting it entered the record, and `defeats`
    is the supplied normative relation. Both are needed: see
    `d1_temporal_integrity` and `d2_inferential_integrity`.
    """

    did: str
    installed: int
    defeats: Callable                  # (challenge) -> bool


@dataclass
class Docket:
    """The whole record: registrations, terms, service, disposals.

    ```text
    register[t]   challenges registered at t
    global_terms  position -> the terms in force for NEW registrations
    opportunity   (cid, t) -> adjudicative opportunity in [0,1]
    served        (cid, t) -> service delivered, <= opportunity
    defeated[t]   cid -> Defeater cited at t
    transfers[t]  cid -> successor cid
    addressed[t]  cids the process actually adjudicated to a conclusion
    ```
    """

    horizon: int
    register: Mapping = field(default_factory=dict)
    global_terms: Mapping = field(default_factory=dict)
    opportunity: Mapping = field(default_factory=dict)
    served: Mapping = field(default_factory=dict)
    defeated: Mapping = field(default_factory=dict)
    transfers: Mapping = field(default_factory=dict)
    addressed: Mapping = field(default_factory=dict)
    evidence_rate: float = 1.0
    #: a fixture may set this to read an open episode's terms from the *current*
    #: global terms instead of the pinned ones -- the moving-goalpost move.
    unpinned: bool = False
    #: a fixture may set this to recompute whether a registration ever happened
    #: under present admission standards -- the C1 violation.
    retroactive_admission: Optional[Callable] = None

    # ------------------------------------------------------------- registry

    def terms_in_force(self, t: int) -> Terms:
        cur = self.global_terms.get(-1)
        for u in range(t + 1):
            if u in self.global_terms:
                cur = self.global_terms[u]
        return cur

    def registered_at(self, t: int) -> tuple:
        """Registrations recorded at `t`.

        With `retroactive_admission` set, whether a registration ever happened is
        recomputed under a present standard. That is the laundering move at this
        layer and it is representable so `C1` can fail.
        """
        out = []
        for c in self.register.get(t, ()):
            if self.retroactive_admission is not None:
                if not self.retroactive_admission(c):
                    continue
            out.append(c)
        return tuple(out)

    def all_registered(self) -> tuple:
        return tuple(c for t in range(self.horizon)
                     for c in self.registered_at(t))

    def episode_terms(self, c: Challenge, t: int) -> Terms:
        """The terms this challenge is adjudicated under at `t`.

        Pinned to registration by default. `unpinned` reads the current global
        terms instead, which is `ACS3`.
        """
        return self.terms_in_force(t) if self.unpinned else c.terms

    # ------------------------------------------------------------- lifecycle

    def defeat_at(self, c: Challenge) -> Optional[int]:
        for t in range(self.horizon):
            d = self.defeated.get(t, {}).get(c.cid)
            if d is not None:
                return t
        return None

    def transfer_at(self, c: Challenge) -> Optional[int]:
        for t in range(self.horizon):
            if c.cid in self.transfers.get(t, {}):
                return t
        return None

    def address_at(self, c: Challenge) -> Optional[int]:
        for t in range(self.horizon):
            if c.cid in self.addressed.get(t, ()):
                return t
        return None

    def closed_at(self, c: Challenge) -> Optional[int]:
        ends = [x for x in (self.defeat_at(c), self.transfer_at(c),
                            self.address_at(c)) if x is not None]
        return min(ends) if ends else None

    def open_at(self, c: Challenge, t: int) -> bool:
        if t < c.at:
            return False
        end = self.closed_at(c)
        return end is None or t <= end

    # ------------------------------------------------------------- service

    def opp(self, c: Challenge, t: int) -> float:
        return float(self.opportunity.get((c.cid, t), 0.0))

    def svc(self, c: Challenge, t: int) -> float:
        return float(self.served.get((c.cid, t), 0.0))

    def cumulative_opportunity(self, c: Challenge, upto=None) -> float:
        upto = self.horizon if upto is None else upto
        return sum(self.opp(c, t) for t in range(upto) if self.open_at(c, t))

    def cumulative_service(self, c: Challenge, upto=None) -> float:
        upto = self.horizon if upto is None else upto
        return sum(self.svc(c, t) for t in range(upto) if self.open_at(c, t))

    def starvation_debt(self, c: Challenge, upto=None) -> float:
        """`sum_t (o_t - u_t)` over positions where the challenge is open and
        not legitimately defeated. Not claimed to be the right quantity; it is
        the one the fixtures report so the alternatives can be compared."""
        upto = self.horizon if upto is None else upto
        return sum(self.opp(c, t) - self.svc(c, t) for t in range(upto)
                   if self.open_at(c, t))

    def evidence(self, c: Challenge, upto=None) -> float:
        """Service converts to evidence at a supplied rate. The consumer lemma's
        only substantive assumption."""
        return self.evidence_rate * self.cumulative_service(c, upto)

    def promoted_at(self, c: Challenge) -> Optional[int]:
        """The first position at which accumulated evidence meets the episode's
        terms. Reads `episode_terms`, which is where pinning bites."""
        for t in range(c.at, self.horizon + 1):
            if not self.open_at(c, min(t, self.horizon - 1)):
                break
            if self.evidence(c, t) >= self.episode_terms(c, t).threshold:
                return t
        return None


# ---------------------------------------------------------- the premises


def c1_registration_permanence(d: Docket) -> tuple:
    """**C1.** A registration that occurred at `t` stays a historical event.

    The exact analogue one layer down of the round above's promotion permanence,
    and it is **event-history integrity rather than a deep theorem**. It is
    stated separately because without it every other guarantee here is vacuous,
    and because frozen Legitimate Evolution cannot see its violation: its
    premises govern how claims leave, and this attack stops them arriving.
    """
    bad = []
    for t in range(d.horizon):
        honest = tuple(d.register.get(t, ()))
        if honest != d.registered_at(t):
            bad.append((t, tuple(c.cid for c in honest),
                        tuple(c.cid for c in d.registered_at(t))))
    return tuple(bad)


def e1_episode_pinning(d: Docket) -> tuple:
    """**E1.** An open challenge is adjudicated under the terms pinned at its
    registration.

    Prospective revision is allowed: a global change applies to everything
    registered afterwards. What it may not do is silently re-decide an episode
    already under way. To move an open challenge onto new terms the process must
    **transfer** it, which is explicit and answerable.

    Returns the positions where an open episode was read under terms other than
    its own.
    """
    bad = []
    for c in d.all_registered():
        for t in range(c.at, d.horizon):
            if not d.open_at(c, t):
                break
            if d.episode_terms(c, t) != c.terms:
                bad.append((c.cid, t, str(c.terms), str(d.episode_terms(c, t))))
    return tuple(bad)


def d1_temporal_integrity(d: Docket) -> tuple:
    """**D1.** A defeater is not created after the challenge it defeats.

    `ACS8`: a challenge starts succeeding and the process writes a bespoke rule
    to stop it. A rule installed after registration and cited against that same
    challenge fails this.

    Note what it does **not** exclude: a general rule that predates every
    challenge it will ever defeat. `ACS9` is exactly that, and it passes.
    """
    bad = []
    for c in d.all_registered():
        for t, m in sorted(d.defeated.items()):
            dd = m.get(c.cid)
            if dd is not None and dd.installed > c.at:
                bad.append(("defeater postdates the challenge", c.cid, dd.did,
                            c.at, dd.installed))
    return tuple(bad)


def d2_inferential_integrity(d: Docket) -> tuple:
    """**D2.** A cited defeater actually stands in the supplied defeat relation.

    `ACS7`: an unrelated represented reason is cited. A token is not a defeater.
    """
    bad = []
    for c in d.all_registered():
        for t, m in sorted(d.defeated.items()):
            dd = m.get(c.cid)
            if dd is not None and not dd.defeats(c):
                bad.append(("cited defeater does not defeat", c.cid, dd.did))
    return tuple(bad)


PREMISES = (("C1", c1_registration_permanence),
            ("E1", e1_episode_pinning),
            ("D1", d1_temporal_integrity),
            ("D2", d2_inferential_integrity))


def violations(d: Docket) -> dict:
    return {n: f(d) for n, f in PREMISES if f(d)}


# ------------------------------------------------ the frozen-LE construction


def frame(d: Docket) -> rp.Frame:
    base = rp.Occ(rp.BASE, 0)
    trace = tuple(rp.Edit(grounds=frozenset({base}), dispose=frozenset(),
                          issues=(), declared=None, label=f"e{t}")
                  for t in range(d.horizon))
    return rp.Frame(base=frozenset({base}), trace=trace, auth=lambda o: True,
                    valid=lambda _s, _e: True)


def duties(d: Docket) -> an.Duties:
    """Registration opens a consideration claim; disposal closes or carries it.

    **This is a canonical constitution, and the round above was corrected for
    not saying so.** Wiring registration straight into `opens` adopts the
    substantive bridge `registered(c) -> ConsiderationDue(c)`. Registration
    Persistence (`C1`) holds without it; only the continuity statement needs it,
    and needs it as a supplied premise rather than a definition.
    """
    opens, key, by_key, dis, trans = {}, {}, {}, {}, {}
    for t in range(d.horizon):
        made = d.registered_at(t)
        if not made:
            continue
        obs = []
        for i, c in enumerate(made):
            q = an.Ob(t, i)
            key[q] = c.key
            by_key[c.key] = q
            obs.append(q)
        opens[t] = frozenset(obs)
    for c in d.all_registered():
        q = by_key.get(c.key)
        if q is None:
            continue
        at = d.defeat_at(c)
        ad = d.address_at(c)
        end = min([x for x in (at, ad) if x is not None], default=None)
        if end is not None:
            dis.setdefault(end, set()).add(q)
        tr = d.transfer_at(c)
        if tr is not None and (end is None or tr < end):
            succ = d.transfers[tr][c.cid]
            sq = next((by_key[k] for k in by_key if k[1] == succ), None)
            if sq is not None:
                trans.setdefault(tr, {})[q] = frozenset({sq})
    return an.Duties(base=frozenset(), opens=opens,
                     discharges={t: frozenset(v) for t, v in dis.items()},
                     transfers=trans, drops={}, due={}, key=key)


@dataclass
class Record:
    name: str
    docket: Docket
    frame: rp.Frame
    duties: an.Duties

    def outstanding_keys(self, t=None) -> set:
        return {self.duties.key_of(q)
                for q in an.outstanding(self.frame, self.duties, t)}

    def incurred_keys(self, t=None) -> set:
        return {self.duties.key_of(q)
                for q in an.incurred(self.frame, self.duties, t)}


def build(name: str, d: Docket) -> Record:
    return Record(name, d, frame(d), duties(d))


# --------------------------------------------------------------- theorems


def thm_challenge_continuity(rec: Record) -> tuple:
    """**Challenge Continuity.** Under `C1` and frozen `A1`, a registered
    challenge is, at every later position, addressed, defeated by a cited
    defeater, transferred to a successor, or still outstanding.

    *Proof.* Registration puts the claim in `opens`; frozen `Incurred` never
    shrinks; frozen `A1` lets it leave the outstanding set only through an
    accepted discharge or a carry. ∎

    **Two lines, and almost all of it inherited.** This is the third round in a
    row whose closure argument is a restatement of `A1`, and the pattern is worth
    naming rather than re-presenting as discovery: once a claim is incurred, the
    frozen package already does this work. The content of each round has been in
    what makes claims *arrive* and what happens to them *while* they are open.

    Returns the keys neither outstanding nor accounted for at the end.
    """
    bad = []
    for c in rec.docket.all_registered():
        if c.key in rec.outstanding_keys():
            continue
        if c.key not in rec.incurred_keys():
            bad.append((c.key, "never incurred"))
    return tuple(bad)


def s1_service(rec: Record, floor: float = 1.0) -> tuple:
    """**S1.** An open, undefeated challenge with unbounded adjudicative
    opportunity receives unbounded service.

    The weakest condition the promotion consumer needs, and deliberately not a
    rate: no fraction of opportunity is demanded, no fairness, no deadline. Only
    that cumulative service does not stall while opportunity keeps arriving.

    Returns the challenges whose opportunity exceeded `floor` while their
    cumulative service stayed at zero -- the starvation the qualitative theorem
    permits.
    """
    bad = []
    for c in rec.docket.all_registered():
        if rec.docket.defeat_at(c) is not None:
            continue
        o = rec.docket.cumulative_opportunity(c)
        u = rec.docket.cumulative_service(c)
        if o > floor and u <= 0.0:
            bad.append((c.cid, o, u, rec.docket.starvation_debt(c)))
    return tuple(bad)


def cor_service_yields_promotion(rec: Record) -> dict:
    """**Consumer lemma.** Service, a persistent signal, and an open episode give
    promotion.

    Each unit of service yields at least `evidence_rate` of evidence; the episode
    promotes once cumulative evidence meets its pinned threshold. So the pipeline
    composes: registration, service, promotion, and then the round above.

    Returns per-challenge `(promoted_at, evidence, threshold)`.
    """
    out = {}
    for c in rec.docket.all_registered():
        out[c.cid] = (rec.docket.promoted_at(c),
                      rec.docket.evidence(c),
                      rec.docket.episode_terms(c, rec.docket.horizon - 1).threshold)
    return out
