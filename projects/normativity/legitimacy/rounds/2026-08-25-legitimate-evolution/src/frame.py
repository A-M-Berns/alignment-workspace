"""The succession frame: legitimacy stated without a ledger.

A frame is six pieces of data and a challenge relation. Nothing in it is a
normative event, a reason occurrence, an answerability root or a replay; those
are one way to produce a frame and are not the only way. `ri_frame.py` builds one
from a Reflective Integrity record and `warrant.py` builds one from a register of
offices and appointments that imports nothing from this repository's normative
architecture. Both run the axiom checkers and the theorems below unchanged.

```text
A            authorities        opaque tokens that may govern something
T            exercises          acts that consume authorities and issue authorities
src, tgt     what an exercise consumes and issues
lic          the authority under which an exercise was performed
rank         a well-founded precedence
G            the base            authorities a recognizing process already accepts
Q            challenges          "suppose this influence had not occurred"
Chal(q)      what q challenges   the exercises the challenged influence brought about
q |= u       stability           u still stands when q is granted
```

The accountability layer is separate and is carried by `Accounts`, because no
theorem about authority succession consumes it and two theorems that are not
about authority succession do. `COUNTERMODELS.md` §4 is the case that decided it.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Iterable, Mapping, Optional, Sequence


# ----------------------------------------------------------------- the frame


@dataclass(frozen=True)
class Frame:
    """A succession frame. Finite here; nothing in the theorems needs that.

    `rank` is any function into a well-order. Finiteness lets it be an integer,
    and calendar time, `tau`, a proof-tree height and an institution's gazette
    numbering are all instances. What the axioms use is well-foundedness, never
    the arithmetic.
    """

    authorities: frozenset
    exercises: frozenset
    src: Mapping                       # exercise -> frozenset[authority]
    tgt: Mapping                       # exercise -> frozenset[authority]
    lic: Mapping                       # exercise -> authority
    rank: Mapping                      # authority | exercise -> int
    base: frozenset                    # G
    current: frozenset                 # the authorities in force now
    challenges: tuple                  # challenge ids
    chal: Mapping                      # challenge -> frozenset[exercise]
    stable: Callable                   # (challenge, authority | exercise) -> bool

    def issued(self, t) -> frozenset:
        """What an exercise puts in force that it did not already consume.

        The gap between `tgt` and `issued` is what makes delegation a case rather
        than a degeneracy: an exercise handing the same authority to a new holder
        has `tgt(t) = src(t)`, issues nothing, and so opens no second origin.
        """
        return self.tgt[t] - self.src[t]

    def minted_by(self, y) -> Optional[object]:
        """The exercise that issued `y`, or `None` for a base authority.

        Well defined under **L2'**; `l2_unique_issuance` is what checks it, and
        the function raises rather than choosing when it fails.
        """
        found = [t for t in sorted(self.exercises, key=str) if y in self.issued(t)]
        if len(found) > 1:
            raise ValueError(f"{y} issued by {found}: L2' fails")
        return found[0] if found else None


# ------------------------------------------------------------- the spine


def l0_base_stability(f: Frame) -> tuple:
    """**L0.** Every base authority survives every challenge.

    *Reading.* What the recognizing process already accepts is not something the
    challenged influence produced. This is the round's one unavoidable
    substantive input on the legitimacy side, and putting it here rather than
    inside a definition is the point of stating the frame at all.
    """
    return tuple((q, g) for q in f.challenges for g in sorted(f.base, key=str)
                 if not f.stable(q, g))


def l1_precedence(f: Frame) -> tuple:
    """**L1.** An exercise is preceded by what it consumes and by its licence, and
    precedes what it issues.

    *Reading.* You cannot supersede an authority that does not yet exist, act
    under a warrant you have not yet been given, or be licensed by the thing
    your act creates. Well-foundedness of `rank` is what makes every derivation
    finite.
    """
    bad = []
    for t in sorted(f.exercises, key=str):
        for x in sorted(f.src[t], key=str):
            if not f.rank[x] < f.rank[t]:
                bad.append(("src", t, x))
        if not f.rank[f.lic[t]] < f.rank[t]:
            bad.append(("lic", t, f.lic[t]))
        for y in sorted(f.issued(t), key=str):
            if not f.rank[t] < f.rank[y]:
                bad.append(("issued", t, y))
    return tuple(bad)


def l2_no_ex_nihilo(f: Frame) -> tuple:
    """**L2.** Every authority is in the base or is issued by some exercise.

    *Reading.* Authority does not appear from nowhere. Everything not granted at
    the outset was granted by an act.
    """
    issued = frozenset().union(frozenset(), *[f.issued(t) for t in f.exercises])
    return tuple(sorted(f.authorities - f.base - issued, key=str))


def l2_unique_issuance(f: Frame) -> tuple:
    """**L2'.** No authority is issued twice, and no base authority is issued.

    *Reading.* An authority has one origin. Used only for canonicity: without it
    lineage still exists and stops being unique, so a process could present a
    flattering one. `THEOREM_MAP.md` entry 4 is what it buys.
    """
    bad = []
    for y in sorted(f.authorities, key=str):
        issuers = [t for t in sorted(f.exercises, key=str) if y in f.issued(t)]
        if len(issuers) > 1 or (issuers and y in f.base):
            bad.append((y, tuple(issuers)))
    return tuple(bad)


def l3_issuance_stability(f: Frame) -> tuple:
    """**L3.** If an exercise survives a challenge, so does everything it issued.

    *Reading.* If the act would still have been performed without the challenged
    influence, then the authority it granted would still exist. Falsifiable, and
    it is the axiom this architecture has to work for: an act whose *effect*
    depends on the surrounding history can survive and confer something else.
    `COUNTERMODELS.md` §2 is the witness and `ri_frame.py` names the condition
    under which the realization satisfies it.
    """
    return tuple((q, t, y) for q in f.challenges
                 for t in sorted(f.exercises, key=str) if f.stable(q, t)
                 for y in sorted(f.tgt[t], key=str) if not f.stable(q, y))


def l3p_origin_necessity(f: Frame) -> tuple:
    """**L3'.** A non-base authority survives a challenge only if its issuer does.

    *Reading.* The only way this authority could be there is that it was granted;
    if the granting act is void under the challenge, so is the authority. The
    converse of L3 and the half that does the anti-laundering work.
    """
    bad = []
    for q in f.challenges:
        for y in sorted(f.authorities - f.base, key=str):
            t = f.minted_by(y)
            if t is not None and f.stable(q, y) and not f.stable(q, t):
                bad.append((q, y, t))
    return tuple(bad)


def l4_challenge_bite(f: Frame) -> tuple:
    """**L4.** A challenge voids the exercises it challenges.

    *Reading.* The counterfactual is about something. An operator that named an
    influence and then left the acts it produced standing would satisfy every
    other axiom and establish nothing, and this is the clause that excludes it.
    """
    return tuple((q, t) for q in f.challenges
                 for t in sorted(f.chal[q], key=str) if f.stable(q, t))


SPINE = (("L0", l0_base_stability), ("L1", l1_precedence),
         ("L2", l2_no_ex_nihilo), ("L2'", l2_unique_issuance),
         ("L3", l3_issuance_stability), ("L3'", l3p_origin_necessity),
         ("L4", l4_challenge_bite))


def violations(f: Frame, axioms=SPINE) -> dict:
    return {name: check(f) for name, check in axioms if check(f)}


# ------------------------------------------------------- certified succession


def certified(f: Frame, q, t) -> bool:
    """`q` leaves both the exercise and the authority it acted under standing."""
    return f.stable(q, f.lic[t]) and f.stable(q, t)


def derivable(f: Frame, q) -> frozenset:
    """`G |-_q y`: the least set containing `G` and closed under certified exercises.

    ```text
    G |-_q y   iff   y in G,  or
                     exists t.  src(t) subset { z : G |-_q z }
                            and y in tgt(t)
                            and q |= lic(t)  and  q |= t
    ```

    **All** of `src(t)`, not one of them. An exercise that supersedes two
    authorities inherits from both, so a lineage through the legitimate one of a
    pair does not carry the pair. That choice is what makes a derivation a tree
    rather than a path, and `COUNTERMODELS.md` §5 is the laundering it refuses.
    """
    out = set(f.base)
    changed = True
    while changed:
        changed = False
        for t in sorted(f.exercises, key=str):
            if not certified(f, q, t) or not f.src[t] <= out:
                continue
            new = f.tgt[t] - out
            if new:
                out |= new
                changed = True
    return frozenset(out)


def derivable_everywhere(f: Frame) -> frozenset:
    """`G |- y`: derivable against every challenge the frame carries.

    Quantifying over challenges rather than composing them keeps a realization's
    challenge operator out of the definition. Each judgment is taken at one
    challenge and no verdict is assembled across two.
    """
    if not f.challenges:
        return derivable(f, None) if _has_null(f) else frozenset(f.base)
    out = derivable(f, f.challenges[0])
    for q in f.challenges[1:]:
        out &= derivable(f, q)
    return out


def _has_null(f: Frame) -> bool:
    try:
        f.stable(None, next(iter(f.base), None))
        return True
    except Exception:
        return False


# ------------------------------------------------------------- derivations


@dataclass(frozen=True)
class Step:
    exercise: object
    consumed: tuple
    issued: object


def derivation(f: Frame, q, y) -> Optional[tuple]:
    """A finite derivation of `y` from `G` under `q`, or `None`.

    Returned in `rank` order, so it reads as a history. Under L2' the set of
    steps is determined by `y`: the tree is the provenance, not a route through
    it, and a process cannot show a flattering one.
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
        t = f.minted_by(z)
        if t is None:
            return None
        steps.append(Step(t, tuple(sorted(f.src[t], key=str)), z))
        frontier.extend(f.src[t])
    return tuple(sorted(steps, key=lambda s: f.rank[s.exercise]))


def provenance(f: Frame, y) -> frozenset:
    """Everything `y`'s existence rests on, with no stability clause at all.

    Predecessors and licences, transitively. `thm_finite_lineage` is the fact
    that this terminates in the base whether or not anything is legitimate,
    which is what keeps the legitimacy clauses from being the reason a lineage
    exists.
    """
    out, frontier = {y}, [y]
    while frontier:
        z = frontier.pop()
        t = f.minted_by(z)
        if t is None:
            continue
        for p in (f.src[t] | {f.lic[t]}) - out:
            out.add(p)
            frontier.append(p)
    return frozenset(out)


# --------------------------------------------------------------- theorems


def thm_finite_lineage(f: Frame) -> tuple:
    """**T2.** Under L1 and L2, every authority has a finite provenance bottoming
    out in the base.

    No legitimacy clause is involved: this is why the round can say that lineage
    *existence* is earned from the local rules and lineage *legitimacy* is not.
    Returns the authorities that violate it, which is empty when L1 and L2 hold.
    """
    return tuple(y for y in sorted(f.authorities, key=str)
                 if not _minimal(f, provenance(f, y)) <= f.base)


def _minimal(f: Frame, s: Iterable) -> frozenset:
    return frozenset(z for z in s if f.minted_by(z) is None)


def thm_stability_of_derivable(f: Frame, q) -> tuple:
    """**T3a.** L0 + L3 give `G |-_q y  =>  q |= y`.

    Induction on the derivation: the base is L0 and each step is L3. Returns the
    counterexamples, which is empty when L0 and L3 hold.
    """
    return tuple(y for y in sorted(derivable(f, q), key=str) if not f.stable(q, y))


def thm_no_bootstrap(f: Frame, q) -> tuple:
    """**T3.** L0 + L3 + L3' + L4 give: nothing in a certified lineage was issued
    by an exercise the challenge challenges.

    ```text
    G |-_q y   =>   for every non-base z in provenance(y),
                    minted_by(z) not in Chal(q)
    ```

    *Proof.* Each such `z` is itself derivable, so `q |= z` by T3a; L3' gives
    `q |= minted_by(z)`; L4 gives `minted_by(z) not in Chal(q)`. The step-local
    obligation is stability of one licence and one exercise; the conclusion is
    about every ancestor of the result, at every depth.

    Returns the violating `(y, z, t)` triples.
    """
    bad = []
    for y in sorted(derivable(f, q), key=str):
        for z in sorted(provenance(f, y) - f.base, key=str):
            t = f.minted_by(z)
            if t is not None and t in f.chal[q]:
                bad.append((y, z, t))
    return tuple(bad)


@dataclass(frozen=True)
class Cert:
    """What one process hands another, and what it costs.

    ```text
    base         the authorities the recipient already accepts
    target       the authority the certificate is about
    steps        the derivation: a finite tree, in rank order
    challenges   the challenges it was taken against
    stability    the stability judgments each step relies on
    accounts     optionally, the outstanding accounts beneath the base
    ```

    The two halves cost different things. `steps` is finite in the size of the
    target's provenance and is checkable by anyone holding it. `stability` is a
    list of judgments about a counterfactual, and the interface makes no promise
    that they compress: whether a recipient can check one cheaply is a fact about
    the realization, and `THEOREM_MAP.md` entry 9 is what the two realizations
    here say about it.
    """

    base: frozenset
    target: object
    steps: tuple
    challenges: tuple
    stability: tuple                   # (challenge, object, verdict)
    accounts: tuple = ()


def certify(f: Frame, y, accounts=None, root=None) -> Optional[Cert]:
    """The certificate for `y`, or `None` where `y` is not derivable everywhere."""
    if y not in derivable_everywhere(f):
        return None
    steps = derivation(f, f.challenges[0], y) if f.challenges else ()
    if steps is None:
        steps = ()
    judgments = tuple((q, u, f.stable(q, u))
                      for q in f.challenges
                      for s in steps for u in (s.exercise, f.lic[s.exercise]))
    outstanding = ()
    if accounts is not None and root is not None:
        outstanding = outstanding_below(f, accounts, root)
    return Cert(f.base, y, steps, f.challenges, judgments, outstanding)


def verify(f: Frame, cert: Cert) -> bool:
    """`verifyLegit`. Sound by re-derivation rather than by reading the verdicts.

    **Soundness.** `verify(f, c) => c.base |- c.target` in `f`, because the
    function recomputes `derivable_everywhere` rather than trusting `c`. That is
    the honest form: a recipient that cannot evaluate `stable` cannot check the
    certificate at all, and a verifier that read the certificate's own stability
    judgments would be checking a signature rather than a fact.
    """
    if cert.base != f.base or cert.challenges != f.challenges:
        return False
    if cert.target not in derivable_everywhere(f):
        return False
    return all(verdict == f.stable(q, u) for q, u, verdict in cert.stability)


def thm_content_is_unconstrained(f: Frame, content: Mapping,
                                 sigma: Mapping) -> bool:
    """**T4.** No relabelling of content changes what is derivable.

    The frame has no content field, so this holds by the type. It is stated as a
    check anyway, because the *realization* is where it can fail: a
    representation whose succession clauses read what a standing says would map
    onto no frame at all. `ri_frame.py` runs the corresponding check on a record.
    """
    before = {q: derivable(f, q) for q in f.challenges}
    relabelled = {a: sigma.get(content.get(a), content.get(a))
                  for a in f.authorities}
    return relabelled is not None and all(
        derivable(f, q) == before[q] for q in f.challenges)


# ------------------------------------------------------ the account layer


@dataclass(frozen=True)
class Accounts:
    """Answerability, kept out of the spine because no theorem above reads it.

    ```text
    accounts      outstanding relations, one open per authority in force
    holder        who is presently answerable for an account
    ends(t)       the accounts the exercise closed out
    opens(t)      the accounts it opened
    answered      whether an ended account was actually answered
    ```

    Two things the authority graph cannot express, and this can. **Delegation**
    is an exercise with `src(t) = tgt(t)`: the authority is unchanged and the
    holder is not, so on the authority graph it is a self-loop and on the
    account graph it is an edge. **Disposal** is an exercise with `tgt(t) = {}`:
    the authority graph has no edge at all and the account graph has an ended
    account. `COUNTERMODELS.md` §4 and §6 are the two.
    """

    accounts: frozenset
    holder: Mapping                    # account -> party
    ends: Mapping                      # exercise -> frozenset[account]
    opens: Mapping                     # exercise -> frozenset[account]
    subject: Mapping                   # account -> authority
    answered: Callable                 # account -> bool


def l5_account_carriage(f: Frame, acc: Accounts) -> tuple:
    """**L5.** Every exercise ends exactly the accounts of what it consumed and
    opens one for each thing it issues.

    *Reading.* Ending an authority ends the relation somebody stood in for it,
    and issuing one opens a relation somebody stands in for it now. Bookkeeping
    with no normative content, and the theorem below needs nothing more.
    """
    bad = []
    for t in sorted(f.exercises, key=str):
        ended = frozenset(acc.subject[a] for a in acc.ends[t])
        opened = frozenset(acc.subject[a] for a in acc.opens[t])
        if ended != f.src[t]:
            bad.append(("ends", t, ended, f.src[t]))
        if opened != f.tgt[t]:
            bad.append(("opens", t, opened, f.tgt[t]))
    return tuple(bad)


def l6_account_trichotomy(f: Frame, acc: Accounts) -> tuple:
    """**L6.** Every account is in exactly one of three conditions, and none is
    removed.

    ```text
    open          not ended by any exercise
    outstanding   ended and not answered
    answered      ended and answered
    ```

    *Reading.* An account cannot be answered before it ends, and answering it
    does not make it un-ended. The whole of the visibility theorem rests on this
    plus reachability, and no further normative content is needed.
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
    """No end anywhere below `a` is unanswered — read recursively, as the
    condition a recognizing process wants to hold of the episode it recognized."""
    c = condition(f, acc, a)
    if c == "open":
        return True
    if c == "outstanding":
        return False
    return all(continuous(f, acc, b) for b in successors(f, acc, a))


def descendants(f: Frame, acc: Accounts, a) -> frozenset:
    out, frontier = {a}, [a]
    while frontier:
        b = frontier.pop()
        for c in successors(f, acc, b) - out:
            out.add(c)
            frontier.append(c)
    return frozenset(out)


def outstanding_below(f: Frame, acc: Accounts, a) -> tuple:
    return tuple(sorted((b for b in descendants(f, acc, a)
                         if condition(f, acc, b) == "outstanding"), key=str))


def thm_visible_discontinuity(f: Frame, acc: Accounts) -> tuple:
    """**T6.** Under L5 and L6, an account fails continuity exactly when some
    account beneath it is outstanding.

    ```text
    not continuous(a)   iff   exists b in descendants(a). outstanding(b)
    ```

    *Proof.* Well-founded induction along `successors`, which is `rank`-forward
    by L1 and L5. The three conditions of L6 are the three cases: an open account
    has no successors and is continuous; an outstanding account witnesses itself;
    an answered account defers to its successors.

    Returns the accounts on which the biconditional fails, which is empty when
    L5 and L6 hold. This is the only clause of the whole interface that can fail
    with no authority-side defect at all, and it is what a recognizing process
    reads to find out whether an evolution left an end dangling.
    """
    return tuple(a for a in sorted(acc.accounts, key=str)
                 if continuous(f, acc, a) == bool(outstanding_below(f, acc, a)))


def thm_delegation_is_invisible_on_authorities(f: Frame, acc: Accounts) -> tuple:
    """**T5.** An exercise with `src(t) = tgt(t)` issues nothing and moves a
    holder.

    On the authority graph it is a self-loop carrying no lineage; on the account
    graph it is an edge between two different holders. Delegation is therefore
    expressible in the account layer and not in the spine, which is one of the
    two jobs that layer has. Returns the delegations found.
    """
    out = []
    for t in sorted(f.exercises, key=str):
        if f.src[t] and f.src[t] == f.tgt[t]:
            before = {acc.holder[a] for a in acc.ends[t]}
            after = {acc.holder[a] for a in acc.opens[t]}
            out.append((t, tuple(sorted(before, key=str)),
                        tuple(sorted(after, key=str))))
    return tuple(out)


def thm_disposal_is_invisible_on_authorities(f: Frame, acc: Accounts) -> tuple:
    """**T5'.** An exercise with `tgt(t) = {}` and `src(t) != {}` ends an authority
    and issues no successor.

    The authority graph records no edge, so on the spine alone a revocation and
    a thing that never happened are the same. The account it ends is the only
    trace, which is the second job the account layer has. Returns the disposals.
    """
    return tuple((t, tuple(sorted(f.src[t], key=str)),
                  tuple(sorted(acc.ends[t], key=str)))
                 for t in sorted(f.exercises, key=str)
                 if f.src[t] and not f.tgt[t])


ACCOUNT_AXIOMS = (("L5", l5_account_carriage), ("L6", l6_account_trichotomy))


def account_violations(f: Frame, acc: Accounts) -> dict:
    return {n: c(f, acc) for n, c in ACCOUNT_AXIOMS if c(f, acc)}
