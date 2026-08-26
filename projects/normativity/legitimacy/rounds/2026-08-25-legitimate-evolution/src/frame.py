"""The succession frame: legitimacy stated without a ledger.

A frame is data about a granting practice and a challenge relation on it. Nothing
in it is a normative event, a reason occurrence, an answerability root or a
replay; those are one way to produce a frame. `ri_frame.py` builds one from a
Reflective Integrity record and `warrant.py` builds one from a register of
offices and appointments that imports nothing from the normative architecture.
Both run the axiom checkers and the theorems below unchanged.

```text
A               authorities     opaque tokens that may govern something
T               exercises       acts that act on, inherit from, and put in force
affected(t)     the positions the exercise acts on
parents(t)      the authorities its successors inherit entitlement from
tgt(t)          what it leaves in force
lic(t)          the authority under which it was performed
rank            a well-founded precedence
when(t)         the lifecycle index at which it happened
G               the base        authorities a recognizing process accepts
live[s]         the lifecycle view at index s, externally supplied
Q               challenges      "suppose this influence had not occurred"
Chal(q)         the exercises the challenged influence brought about
q |= u          stability       u still stands when q is granted
```

Three separations the round's first pass did not have, each forced by a
countermodel in `COUNTERMODELS.md`:

**`affected` is not `parents`.** Acting on an authority is not inheriting from
it, and a legitimate cleanup of an illegitimate standing is the case that
separates them (§7).

**Being stable is not being legitimate.** `q |= x` says `x` survives the
challenge. It does not say `x` is entitled, and a licence is now required to be
*derivable*, not merely stable (§2).

**Coverage is not form.** The axioms constrain the shape of a legitimacy
calculus. Whether its challenge set reaches the influences anyone cares about is
`ThreatModel` and `coverage`, and it is a separate hypothesis (§6).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Iterable, Mapping, Optional, Sequence


# ----------------------------------------------------------------- the frame


@dataclass(frozen=True)
class Frame:
    """A succession frame. Finite here; nothing in the theorems needs that.

    `rank` is any function into a well-order — calendar time, `tau`, a proof-tree
    height, a gazette numbering. `when` is the separate lifecycle index, because
    the order in which entitlement is inherited and the times at which things are
    in force are different questions and a realization may answer them with
    different objects.
    """

    authorities: frozenset
    exercises: frozenset
    affected: Mapping                   # exercise -> frozenset[authority]
    parents: Mapping                    # exercise -> frozenset[authority]
    tgt: Mapping                        # exercise -> frozenset[authority]
    lic: Mapping                        # exercise -> authority
    rank: Mapping                       # authority | exercise -> int
    base: frozenset                     # G
    challenges: tuple
    chal: Mapping                       # challenge -> frozenset[exercise]
    stable: Callable                    # (challenge, authority | exercise) -> bool
    when: Mapping = field(default_factory=dict)     # exercise -> lifecycle index
    live: Mapping = field(default_factory=dict)     # index -> frozenset[authority]
    times: tuple = ()

    def issued(self, t) -> frozenset:
        """What an exercise puts in force that it was not already acting on.

        The gap between `tgt` and `issued` is what makes delegation a case rather
        than a degeneracy: an exercise handing the same authority to a new holder
        has `tgt(t) = affected(t)`, issues nothing, and opens no second origin.
        """
        return self.tgt[t] - self.affected[t]

    def grounds(self, t) -> frozenset:
        """Everything an exercise's issue inherits its entitlement from.

        The licence is one of them. That it is — rather than being separately
        required only to survive the challenge — is this pass's central repair.
        """
        return self.parents[t] | {self.lic[t]}

    def issuers(self, y) -> tuple:
        """Every exercise that issued `y`. A tuple, because L2' may not hold."""
        return tuple(t for t in sorted(self.exercises, key=str) if y in self.issued(t))

    def minted_by(self, y):
        """The issuer of `y` under L2', or `None` for a base authority.

        Returns the first issuer when L2' fails rather than raising: the
        existential theorems must not be able to lean on uniqueness, and a
        function that raised would let them. `l2_unique_issuance` is what reports
        the failure.
        """
        found = self.issuers(y)
        return found[0] if found else None


@dataclass(frozen=True)
class ThreatModel:
    """The influences a recognizing process wants ruled out, supplied externally.

    `depends(xi)` is the exercises influence `xi` actually brought about. It is a
    fact about the world and about the process's own provenance discipline, and
    the frame does not compute it — no counterfactual over a record can. What the
    frame can do is state the hypothesis that its challenge set reaches it.
    """

    influences: tuple
    depends: Mapping                    # influence -> frozenset[exercise]


# ------------------------------------------------------------- the spine


def l0_base_stability(f: Frame) -> tuple:
    """**L0.** Every base authority survives every challenge.

    *Reading.* What the recognizing process already accepts is not something the
    challenged influence produced. The round's one unavoidable substantive input
    on the legitimacy side, and an axiom rather than a fact inside a definition.
    """
    return tuple((q, g) for q in f.challenges for g in sorted(f.base, key=str)
                 if not f.stable(q, g))


def l1_precedence(f: Frame) -> tuple:
    """**L1.** An exercise is preceded by everything it acts on or inherits from,
    and precedes what it issues.

    *Reading.* You cannot supersede what does not yet exist, inherit from what has
    not been granted, act under a warrant you have not been given, or be licensed
    by what your own act creates. Well-foundedness is what makes derivations
    finite.
    """
    bad = []
    for t in sorted(f.exercises, key=str):
        for x in sorted(f.affected[t] | f.grounds(t), key=str):
            if not f.rank[x] < f.rank[t]:
                bad.append(("before", t, x))
        for y in sorted(f.issued(t), key=str):
            if not f.rank[t] < f.rank[y]:
                bad.append(("issued", t, y))
    return tuple(bad)


def l2_no_ex_nihilo(f: Frame) -> tuple:
    """**L2.** Every authority is in the base or is issued by some exercise.

    *Reading.* Authority does not appear from nowhere.
    """
    issued = frozenset().union(frozenset(), *[f.issued(t) for t in f.exercises])
    return tuple(sorted(f.authorities - f.base - issued, key=str))


def l2_unique_issuance(f: Frame) -> tuple:
    """**L2'.** No authority is issued twice, and no base authority is issued.

    *Reading.* An authority has one origin. **Optional**: every theorem below
    except `thm_canonical_provenance` is proved without it, and
    `warrant.two_issuers_register` is the frame that shows the two really come
    apart.
    """
    bad = []
    for y in sorted(f.authorities, key=str):
        issuers = f.issuers(y)
        if len(issuers) > 1 or (issuers and y in f.base):
            bad.append((y, issuers))
    return tuple(bad)


def l3_issuance_stability(f: Frame) -> tuple:
    """**L3.** If an exercise survives a challenge, so does everything it leaves
    in force.

    *Reading.* If the act would still have been performed without the challenged
    influence, what it put in force would still be in force. Whether this holds
    turns on what counts as *the same exercise surviving*: `ri_frame.py` prosecutes
    that, and under an exercise identity that carries the act's effect the axiom
    needs no side condition.
    """
    return tuple((q, t, y) for q in f.challenges
                 for t in sorted(f.exercises, key=str) if f.stable(q, t)
                 for y in sorted(f.tgt[t], key=str) if not f.stable(q, y))


def l3p_origin_necessity(f: Frame) -> tuple:
    """**L3'.** A non-base authority survives a challenge only if some issuer of
    it does.

    *Reading.* The only way this authority could be there is that it was granted;
    if every granting act is void under the challenge, so is the authority. The
    converse of L3 and the half that does the anti-laundering work. Stated over
    `issuers` rather than over a unique issuer, so that it does not smuggle L2'.
    """
    bad = []
    for q in f.challenges:
        for y in sorted(f.authorities - f.base, key=str):
            ts = f.issuers(y)
            if ts and f.stable(q, y) and not any(f.stable(q, t) for t in ts):
                bad.append((q, y, ts))
    return tuple(bad)


def l4_challenge_bite(f: Frame) -> tuple:
    """**L4.** A challenge voids the exercises it challenges.

    *Reading.* The counterfactual is about something. An operator that named an
    influence and left the acts it produced standing would satisfy every other
    axiom and establish nothing.
    """
    return tuple((q, t) for q in f.challenges
                 for t in sorted(f.chal[q], key=str) if f.stable(q, t))


SPINE = (("L0", l0_base_stability), ("L1", l1_precedence),
         ("L2", l2_no_ex_nihilo),
         ("L3", l3_issuance_stability), ("L3'", l3p_origin_necessity),
         ("L4", l4_challenge_bite))


def violations(f: Frame, axioms=SPINE) -> dict:
    """The spine's failures. **L2' is not in `SPINE`** — it is optional, and
    `l2_unique_issuance` is called by name where a theorem wants it."""
    return {name: check(f) for name, check in axioms if check(f)}


# ------------------------------------------------------- certified succession


def derivable(f: Frame, q) -> frozenset:
    """`G |-_q y`: the least set containing `G` and closed under certified
    exercises.

    ```text
    G |-_q y   iff   y in G,  or
                     exists t.  parents(t) union {lic(t)}  subset  { z : G |-_q z }
                            and y in tgt(t)
                            and q |= t
    ```

    **The licence is a ground, not a side condition.** Requiring only `q |= lic(t)`
    lets an exercise inherit recognition from an authority that survives the
    challenge without being entitled to anything, and
    `warrant.stable_but_illegitimate_register` is the frame on which that made
    the no-bootstrap theorem false. `COUNTERMODELS.md` §1.

    **All** of `parents(t)`, not one of them — but `affected(t)` is not consulted
    at all. An exercise inherits from what it inherits from; acting on an
    illegitimate standing in order to end it is not inheriting from it.
    """
    out = set(f.base)
    changed = True
    while changed:
        changed = False
        for t in sorted(f.exercises, key=str):
            if not f.stable(q, t) or not f.grounds(t) <= out:
                continue
            new = f.tgt[t] - out
            if new:
                out |= new
                changed = True
    return frozenset(out)


def derivable_stable_licence(f: Frame, q) -> frozenset:
    """The rule this pass rejected, kept so the two can be run side by side.

    The licence had only to survive the challenge:

    ```text
    ... and q |= lic(t)   rather than   lic(t) in Derivable_q
    ```

    On `warrant.stable_but_illegitimate_register` this admits an authority whose
    licence inherits from a warrant the challenge voids, and the no-bootstrap
    theorem is then **false** rather than unproved. `COUNTERMODELS.md` §1 runs
    both.
    """
    out = set(f.base)
    changed = True
    while changed:
        changed = False
        for t in sorted(f.exercises, key=str):
            if not f.stable(q, t) or not f.stable(q, f.lic[t]):
                continue
            if not f.parents[t] <= out:
                continue
            new = f.tgt[t] - out
            if new:
                out |= new
                changed = True
    return frozenset(out)


def bootstrapped_under(f: Frame, q, reach: frozenset) -> tuple:
    """Route-blind ancestors of `reach` whose every issuer is challenged.

    The predicate `thm_no_bootstrap` asserts to be empty. Exposed separately so
    a rejected rule's `reach` can be tested against the same standard.
    """
    bad = []
    for y in sorted(reach, key=str):
        for z in sorted(provenance(f, y) - f.base, key=str):
            ts = f.issuers(z)
            if ts and all(t in f.chal[q] for t in ts):
                bad.append((y, z, ts))
    return tuple(bad)


def certified(f: Frame, q, t) -> bool:
    """The exercise survives the challenge and everything it inherits from is
    derivable."""
    return f.stable(q, t) and f.grounds(t) <= derivable(f, q)


def derivable_everywhere(f: Frame) -> frozenset:
    """Derivable against every challenge the frame carries.

    Quantifying over challenges rather than composing them keeps a realization's
    challenge operator out of the definition: each judgment is taken at one
    challenge and no verdict is assembled across two, which matters because the
    Reflective Integrity operator is neither monotone nor composable.

    **This is not yet certification against a threat model.** See `certified_against`.
    """
    if not f.challenges:
        return frozenset(f.authorities)
    out = derivable(f, f.challenges[0])
    for q in f.challenges[1:]:
        out &= derivable(f, q)
    return out


# ------------------------------------------------------------- derivations


@dataclass(frozen=True)
class Step:
    exercise: object
    grounds: tuple
    issued: object


def derivation(f: Frame, q, y) -> Optional[tuple]:
    """A certified derivation of `y` from `G` under `q`, or `None`.

    Returned in `rank` order, so it reads as a history. The derivation records
    *which* exercise it used at each authority, which is what lets the
    no-bootstrap theorem be stated without unique issuance: without L2' the route
    is a choice, and the theorem is about the route the certificate exhibits.
    """
    if y in f.base:
        return ()
    reach = derivable(f, q)
    if y not in reach:
        return None
    steps, frontier, seen = [], [y], set()
    while frontier:
        z = frontier.pop()
        if z in seen or z in f.base:
            continue
        seen.add(z)
        used = None
        for t in f.issuers(z):
            if f.stable(q, t) and f.grounds(t) <= reach:
                used = t
                break
        if used is None:
            return None
        steps.append(Step(used, tuple(sorted(f.grounds(used), key=str)), z))
        frontier.extend(f.grounds(used))
    return tuple(sorted(steps, key=lambda s: f.rank[s.exercise]))


def ancestors(f: Frame, steps: Sequence[Step]) -> frozenset:
    """The authorities a derivation actually leans on, route included."""
    return frozenset().union(frozenset(), *[frozenset(s.grounds) for s in steps]) \
        | frozenset(s.issued for s in steps)


def provenance(f: Frame, y) -> frozenset:
    """Everything `y`'s existence could rest on, over **every** issuer.

    An over-approximation of any one derivation's ancestry, and the object
    `thm_finite_lineage` is about. It is deliberately route-blind: T2 is the
    claim that the whole graph is well founded, which is a fact about L1 and L2
    and not about any choice.
    """
    out, frontier = {y}, [y]
    while frontier:
        z = frontier.pop()
        for t in f.issuers(z):
            for p in f.grounds(t) - out:
                out.add(p)
                frontier.append(p)
    return frozenset(out)


# --------------------------------------------------------------- theorems


def thm_finite_lineage(f: Frame) -> tuple:
    """**T1.** Under L1 and L2, every authority has a finite provenance whose
    minimal elements lie in the base.

    No legitimacy clause takes part and **L2' is not used**: the closure runs
    over every issuer, so a branching origin costs the theorem nothing. This is
    why the theory is not a restatement of a recursive definition — *having* a
    lineage is earned from the local rules and *having a certified one* is the
    extra content, and the two come apart on a record where a manufactured
    authority is in force, reaches the base, and is not derivable.

    Returns the authorities that violate it.
    """
    return tuple(y for y in sorted(f.authorities, key=str)
                 if not _minimal(f, provenance(f, y)) <= f.base)


def _minimal(f: Frame, s: Iterable) -> frozenset:
    return frozenset(z for z in s if not f.issuers(z))


def thm_canonical_provenance(f: Frame) -> bool:
    """**T1'.** Under L2' the provenance is determined by the target.

    What unique issuance buys, and the whole of it: without it a process may
    exhibit whichever route flatters it, and a recipient checking one derivation
    learns nothing about the others.
    """
    return not l2_unique_issuance(f)


def thm_stability_of_derivable(f: Frame, q) -> tuple:
    """**T2a.** L0 + L3 give `G |-_q y => q |= y`.

    Induction on the derivation: the base is L0 and each step is L3. With the
    repaired rule this also yields `q |= lic(t)` for every certified `t`, so the
    old side condition on licences is now a consequence rather than a hypothesis.
    """
    return tuple(y for y in sorted(derivable(f, q), key=str) if not f.stable(q, y))


def thm_no_bootstrap(f: Frame, q) -> tuple:
    """**T2, no self-ratifying authority.** L0 + L3 + L3' + L4 give: for every
    derivable `y` there is a certified derivation none of whose exercises is
    challenged and each of whose authorities has an unchallenged issuer.

    ```text
    G |-_q y  =>  exists a derivation D of y such that
                  for every step s of D,  s.exercise notin Chal(q),
                  and for every z in ancestors(D) \\ G,
                      some issuer of z is not in Chal(q)
    ```

    *Proof.* Take the derivation the fixed point produces. Every step is stable,
    so L4 puts it outside `Chal(q)`. Every `z` in its ancestry is derivable, so
    T2a gives `q |= z`; L3' gives a stable issuer; L4 puts that issuer outside
    `Chal(q)`. ∎

    The step-local obligation is stability of one exercise and derivability of
    what it inherits from; the conclusion is about every ancestor of the result
    at every depth. **Under L2' the existential over issuers collapses** and the
    statement becomes one about the target's determined provenance.

    Returns the violating `(y, z, t)` triples.
    """
    bad = []
    for y in sorted(derivable(f, q), key=str):
        steps = derivation(f, q, y)
        if steps is None:
            bad.append((y, None, None))
            continue
        for s in steps:
            if s.exercise in f.chal[q]:
                bad.append((y, s.issued, s.exercise))
        for z in sorted(ancestors(f, steps) - f.base, key=str):
            ts = f.issuers(z)
            if ts and all(t in f.chal[q] for t in ts):
                bad.append((y, z, ts))
    return tuple(bad)


def thm_content_is_unconstrained(f: Frame, content: Mapping,
                                 sigma: Mapping) -> bool:
    """**T3, content independence.** No relabelling of content changes what is
    derivable.

    The frame has no content field, so this holds by the type. Its force is that
    it becomes a falsifiable condition on a realization: a representation whose
    succession clauses inspected what an authority says would map onto no frame.
    """
    before = {q: derivable(f, q) for q in f.challenges}
    relabelled = {a: sigma.get(content.get(a), content.get(a))
                  for a in f.authorities}
    return relabelled is not None and all(
        derivable(f, q) == before[q] for q in f.challenges)


# ------------------------------------------------------- the threat model


def coverage(f: Frame, threat: ThreatModel) -> tuple:
    """**C, challenge coverage.** Every influence in the threat model is
    challenged by some challenge the frame carries.

    ```text
    forall xi in Xi.  exists q in Q.  depends(xi) subset Chal(q)
    ```

    *Reading.* The calculus actually asks about the influences anyone is worried
    about. This is the hypothesis the round's first pass carried as a prose
    caveat, and it is not derivable from anything: `depends` is a fact about the
    world and about the process's provenance discipline, and no counterfactual
    over a record computes it.

    Returns the uncovered influences.
    """
    return tuple(xi for xi in threat.influences
                 if not any(threat.depends[xi] <= f.chal[q] for q in f.challenges))


def certified_against(f: Frame, threat: ThreatModel) -> frozenset:
    """What is legitimate **relative to a stated threat model**.

    Empty when coverage fails, whatever the structural axioms say. That is the
    point: a frame with no challenges satisfies L0-L4 vacuously and certifies
    everything, and `warrant.undercovered_register` is the countermodel.
    """
    return derivable_everywhere(f) if not coverage(f, threat) else frozenset()


# ---------------------------------------------------------- the lifecycle


def frontier(f: Frame, q, s) -> frozenset:
    """`F^leg_s`: what is both in force at `s` and derivable under `q`.

    The lifecycle view is supplied by the realization and is not computed here.
    A legitimacy calculus says which authorities are entitled; which are in force
    is a different question with a different answer, and conflating them is how
    a theory ends up unable to tell a consumer what to enforce.
    """
    return f.live.get(s, frozenset()) & derivable(f, q)


def l7_lifecycle_entry(f: Frame) -> tuple:
    """**L5.** An authority enters the live view only at the base or by being
    issued.

    *Reading.* Nothing comes into force without an act putting it there.
    """
    bad = []
    for i, s in enumerate(f.times):
        before = f.live.get(f.times[i - 1], frozenset()) if i else frozenset()
        for x in sorted(f.live.get(s, frozenset()) - before, key=str):
            if x in f.base:
                continue
            if not any(f.when.get(t) == s and x in f.issued(t) for t in f.exercises):
                bad.append(("entry", s, x))
    return tuple(bad)


def l8_lifecycle_exit(f: Frame) -> tuple:
    """**L6.** An authority leaves the live view only by being acted on.

    *Reading.* Nothing falls out of force on its own. This is the axiom the
    persistence theorem consumes, and it is where a realization that quietly
    expires things would be caught.
    """
    bad = []
    for i, s in enumerate(f.times):
        if not i:
            continue
        before = f.live.get(f.times[i - 1], frozenset())
        for x in sorted(before - f.live.get(s, frozenset()), key=str):
            if not any(f.when.get(t) == s and x in f.affected[t]
                       for t in f.exercises):
                bad.append(("exit", s, x))
    return tuple(bad)


LIFECYCLE = (("L5", l7_lifecycle_entry), ("L6", l8_lifecycle_exit))


def lifecycle_violations(f: Frame) -> dict:
    return {n: c(f) for n, c in LIFECYCLE if c(f)}


def thm_persistence(f: Frame, q) -> tuple:
    """**T4, persistent until legitimately changed.** Under L6, an authority in
    the legitimate frontier stays there until an exercise acts on it.

    ```text
    x in F^leg_s  and  no t with when(t) in (s, u] and x in affected(t)
        =>  x in F^leg_u
    ```

    *Proof.* Derivability is a property of the frame and does not move with the
    lifecycle index, so only the live view can change; by L6 it changes only
    through an exercise acting on `x`. ∎

    Not *once legitimate, always legitimate*: an exercise acting on `x` may end
    it, and `thm_legitimacy_is_antitone_in_challenges` is the second exit route.

    Returns the violating `(x, s, u)` triples.
    """
    bad = []
    for i, s in enumerate(f.times):
        for x in sorted(frontier(f, q, s), key=str):
            for u in f.times[i + 1:]:
                window = [t for t in f.exercises
                          if f.when.get(t) in _between(f.times, s, u)]
                if any(x in f.affected[t] for t in window):
                    break
                if x not in frontier(f, q, u):
                    bad.append((x, s, u))
                    break
    return tuple(bad)


def _between(times: Sequence, s, u) -> tuple:
    lo, hi = times.index(s), times.index(u)
    return tuple(times[lo + 1:hi + 1])


def thm_legitimacy_is_antitone_in_challenges(f: Frame, more: Frame) -> bool:
    """**T4', the second exit route.** Adding challenges can only shrink what is
    derivable.

    A frame's legitimacy verdict is relative to the challenges it carries, so an
    authority can leave the legitimate frontier without any exercise touching it
    — by the arrival of a challenge that reaches its lineage. That is a feature
    and it is the reason `F^leg` is not a monotone object: a recognizing process
    that learns of an influence it did not know about revises downwards, which is
    what one would want it to do.
    """
    return derivable_everywhere(more) <= derivable_everywhere(f)


def project(f: Frame, q, s, classify: Callable, kind: str) -> frozenset:
    """`AuthorityView_s` and `NormView_s`, as projections of one frontier.

    `classify` is supplied by the consumer. The frame does not know what a norm
    is, and the two consumers of this interface want different halves of the same
    object rather than two objects.
    """
    return frozenset(x for x in frontier(f, q, s) if classify(x) == kind)


# ------------------------------------------------------ the account layer


@dataclass(frozen=True)
class Accounts:
    """Answerability, kept out of the spine because no theorem above reads it.

    Two things the authority graph cannot express, and this can. **Delegation**
    is an exercise with `affected(t) = tgt(t)`: it issues nothing, so on the
    authority graph it is a self-loop carrying no lineage and on the account
    graph it is an edge between two holders. **Disposal** is an exercise with
    `tgt(t) = {}`: the authority graph records no edge at all.
    """

    accounts: frozenset
    holder: Mapping                    # account -> party
    ends: Mapping                      # exercise -> frozenset[account]
    opens: Mapping                     # exercise -> frozenset[account]
    subject: Mapping                   # account -> authority
    answered: Callable                 # account -> bool


def l9_account_carriage(f: Frame, acc: Accounts) -> tuple:
    """**L7.** An exercise ends the accounts of what it acts on and opens one for
    each thing it leaves in force."""
    bad = []
    for t in sorted(f.exercises, key=str):
        ended = frozenset(acc.subject[a] for a in acc.ends[t])
        opened = frozenset(acc.subject[a] for a in acc.opens[t])
        if ended != f.affected[t]:
            bad.append(("ends", t, ended, f.affected[t]))
        if opened != f.tgt[t]:
            bad.append(("opens", t, opened, f.tgt[t]))
    return tuple(bad)


def l10_account_trichotomy(f: Frame, acc: Accounts) -> tuple:
    """**L8.** An account is open, outstanding or answered, and none is removed.

    *Reading.* An account cannot be answered before it ends, and answering does
    not un-end it.
    """
    ended = frozenset().union(frozenset(), *[acc.ends[t] for t in f.exercises])
    return tuple(a for a in sorted(acc.accounts, key=str)
                 if acc.answered(a) and a not in ended)


def condition(f: Frame, acc: Accounts, a) -> str:
    ended = frozenset().union(frozenset(), *[acc.ends[t] for t in f.exercises])
    if a not in ended:
        return "open"
    return "answered" if acc.answered(a) else "outstanding"


def successors(f: Frame, acc: Accounts, a) -> frozenset:
    return frozenset().union(frozenset(), *[acc.opens[t] for t in f.exercises
                                            if a in acc.ends[t]]) or frozenset()


def continuous(f: Frame, acc: Accounts, a) -> bool:
    c = condition(f, acc, a)
    if c == "open":
        return True
    if c == "outstanding":
        return False
    return all(continuous(f, acc, b) for b in successors(f, acc, a))


def descendants(f: Frame, acc: Accounts, a) -> frozenset:
    out, frontier_ = {a}, [a]
    while frontier_:
        b = frontier_.pop()
        for c in successors(f, acc, b) - out:
            out.add(c)
            frontier_.append(c)
    return frozenset(out)


def outstanding_below(f: Frame, acc: Accounts, a) -> tuple:
    return tuple(sorted((b for b in descendants(f, acc, a)
                         if condition(f, acc, b) == "outstanding"), key=str))


def thm_visible_discontinuity(f: Frame, acc: Accounts) -> tuple:
    """**T5.** Under L7 and L8, an account fails continuity exactly when one
    beneath it is outstanding.

    Well-founded induction along `opens`. The only clause of the whole interface
    that can fail with the authority side clean, which is what a recognizing
    process reads to find out whether an evolution left an end dangling.
    """
    return tuple(a for a in sorted(acc.accounts, key=str)
                 if continuous(f, acc, a) == bool(outstanding_below(f, acc, a)))


def thm_delegation_is_invisible_on_authorities(f: Frame, acc: Accounts) -> tuple:
    return tuple((t, tuple(sorted({acc.holder[a] for a in acc.ends[t]}, key=str)),
                  tuple(sorted({acc.holder[a] for a in acc.opens[t]}, key=str)))
                 for t in sorted(f.exercises, key=str)
                 if f.affected[t] and f.affected[t] == f.tgt[t])


def thm_disposal_is_invisible_on_authorities(f: Frame, acc: Accounts) -> tuple:
    return tuple((t, tuple(sorted(f.affected[t], key=str)),
                  tuple(sorted(acc.ends[t], key=str)))
                 for t in sorted(f.exercises, key=str)
                 if f.affected[t] and not f.tgt[t])


ACCOUNT_AXIOMS = (("L7", l9_account_carriage), ("L8", l10_account_trichotomy))


def account_violations(f: Frame, acc: Accounts) -> dict:
    return {n: c(f, acc) for n, c in ACCOUNT_AXIOMS if c(f, acc)}


# ------------------------------------------------------------- certificate


@dataclass(frozen=True)
class Cert:
    """What one process hands another, and what it costs.

    `steps` is finite in the size of the target's ancestry and is checkable by
    anyone holding it. `stability` is a list of judgments about a counterfactual,
    and whether those compress is a fact about the realization rather than about
    legitimacy. `coverage_claim` is the threat model the certificate is relative
    to, and a certificate that omits it is a certificate against nothing.
    """

    base: frozenset
    target: object
    steps: tuple
    challenges: tuple
    stability: tuple                   # (challenge, exercise, verdict)
    coverage_claim: tuple = ()         # the influences claimed covered
    accounts: tuple = ()


def certify(f: Frame, y, threat: Optional[ThreatModel] = None,
            accounts=None, root=None) -> Optional[Cert]:
    """The certificate for `y`, or `None` where `y` is not derivable everywhere.

    Returns `None` when a threat model is supplied and coverage fails: a
    certificate whose challenge set does not reach the influences it is offered
    against is not a weaker certificate, it is not one.
    """
    if y not in derivable_everywhere(f):
        return None
    if threat is not None and coverage(f, threat):
        return None
    steps = derivation(f, f.challenges[0], y) if f.challenges else ()
    if steps is None:
        return None
    judgments = tuple((q, s.exercise, f.stable(q, s.exercise))
                      for q in f.challenges for s in steps)
    outstanding = ()
    if accounts is not None and root is not None:
        outstanding = outstanding_below(f, accounts, root)
    return Cert(f.base, y, steps, f.challenges, judgments,
                tuple(threat.influences) if threat else (), outstanding)


def verify(f: Frame, cert: Cert, threat: Optional[ThreatModel] = None) -> bool:
    """`verifyLegit`. Sound by re-derivation rather than by reading the verdicts.

    A recipient that cannot evaluate `stable` cannot check the certificate at
    all, and a verifier reading the certificate's own stability judgments would
    be checking a signature rather than a fact.
    """
    if cert.base != f.base or cert.challenges != f.challenges:
        return False
    if threat is not None and coverage(f, threat):
        return False
    if cert.target not in derivable_everywhere(f):
        return False
    return all(verdict == f.stable(q, u) for q, u, verdict in cert.stability)
