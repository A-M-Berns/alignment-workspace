"""Grounded Replay: the structural kernel.

```text
L_0     = G
L_{t+1} = (L_t \\ dispose(e_t)) union issue_t(e_t)   if Valid(L_t, e_t)
          L_t                                        otherwise
```

Everything here is structural. `Valid` is a parameter and no theorem below
assumes it is any good; `office.py` supplies a semantic one and `ri_frame.py` one
derived from a record. Nothing here mentions provenance, threat classes,
permission, reasons, settlements, answerability, prices or raw histories, and
`tests/test_replay.py` checks that by reading the module.

Three things were deleted rather than repaired.

**Historical time as identity.** An edit's identity used to be its historical
index, so two edits at one time issued the *same* occurrence. The trace is a
list; position is identity and order at once; freshness is a fact about lists
rather than a premise.

**The declared/effect split.** The effect is part of the proposal, so `apply` is a
function of the state and the edit and a fold over a trace is deterministic. A
raw process doing something else has not executed this edit, which is a
realization-level conformance question.

**Content invariance.** Withdrawn: it was checked vacuously and it is false once
permission reads content. What is true is that this module never inspects
content, so it imposes no conservativity on it.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional


BASE = -1                              #: the position of a base occurrence


@dataclass(frozen=True)
class Occ:
    """An occurrence: what one act put in force.

    `pos` is the position in the trace of the edit that issued it, or `BASE`.
    Identity, not time — a realization that wants to record *when* an act
    happened carries that as data, and two acts at one moment still issue
    distinct occurrences.
    """

    pos: int
    slot: int

    def __str__(self) -> str:
        return f"o{'G' if self.pos == BASE else self.pos}.{self.slot}"


@dataclass(frozen=True)
class Edit:
    """A proposal, with its effect frozen into it.

    ```text
    grounds   the occurrences invoked as the authority for this act
    dispose   the occurrences it ends
    issues    the contents it puts in force, one per issued occurrence
    declared  what the semantics may read; never read here
    ```

    **The whole effect is in the edit.** `dispose` and `issues` say exactly what
    the act does, so `apply` is a function of the state and the edit and a fold
    over a trace is deterministic. A raw process that produces a different effect
    has not executed this edit: that is a conformance question at the extraction
    boundary, and `ri_frame.extraction_agrees` is where it is checked.
    """

    grounds: frozenset = frozenset()
    dispose: frozenset = frozenset()
    issues: tuple = ()
    declared: object = None
    label: str = ""

    @property
    def slots(self) -> int:
        return len(self.issues)

    def issued(self, pos: int) -> frozenset:
        return frozenset(Occ(pos, i) for i in range(len(self.issues)))

    def __str__(self) -> str:
        return self.label or "e"


@dataclass(frozen=True)
class Frame:
    """A base, a trace, an authority predicate, and a validity relation.

    `auth` is a **predicate**, not half of a partition. The kernel needs to know
    which occurrences can ground an edit; whether an occurrence is also
    substantively normative is a separate predicate, and nothing here requires
    the two to be disjoint or exhaustive.
    """

    base: frozenset
    trace: tuple
    auth: Callable                     # Occ -> bool
    valid: Callable                    # (state, Edit) -> bool

    def issued(self, t: int) -> frozenset:
        return self.trace[t].issued(t)

    def authorities(self, state: frozenset) -> frozenset:
        return frozenset(o for o in state if self.auth(o))


def apply_edit(f: Frame, state: frozenset, t: int) -> frozenset:
    e = f.trace[t]
    return (state - e.dispose) | e.issued(t)


def changes(f: Frame, state: frozenset, t: int) -> bool:
    return apply_edit(f, state, t) != state


def replay(f: Frame, upto: Optional[int] = None) -> frozenset:
    """`L_t`."""
    upto = len(f.trace) if upto is None else upto
    state = f.base
    for t in range(upto):
        if f.valid(state, f.trace[t]):
            state = apply_edit(f, state, t)
    return state


def accepted(f: Frame, upto: Optional[int] = None) -> tuple:
    """The positions the replay applied."""
    upto = len(f.trace) if upto is None else upto
    state, out = f.base, []
    for t in range(upto):
        if f.valid(state, f.trace[t]):
            out.append(t)
            state = apply_edit(f, state, t)
    return tuple(out)


def admitted(f: Frame, upto: Optional[int] = None) -> frozenset:
    """`Adm_t = G union { issue_s(e_s) : s accepted, s < t }`.

    What legitimate replay has ever put in force. **This is what the grounding
    theorem is about**, and it is not what is in force now: an occurrence validly
    issued and validly disposed stays admitted and stops being live. Conflating
    the two let the previous formulation's certificate claim more than it proved.
    """
    upto = len(f.trace) if upto is None else upto
    out = set(f.base)
    for t in accepted(f, upto):
        out |= f.issued(t)
    return frozenset(out)


# ------------------------------------------------------ structural premises


def s1_prior_grounding(f: Frame) -> tuple:
    """**S1.** An accepted edit's grounds are authorities of the strict pre-state.

    *You act under authority you already have.*
    """
    bad, state = [], f.base
    for t in range(len(f.trace)):
        e = f.trace[t]
        if f.valid(state, e):
            missing = e.grounds - f.authorities(state)
            if missing:
                bad.append(("ungrounded", t, tuple(sorted(missing, key=str))))
            state = apply_edit(f, state, t)
    return tuple(bad)


def s2_no_ex_nihilo(f: Frame) -> tuple:
    """**S2.** An accepted edit that changes the state has a non-empty ground set.

    *Nothing enters or leaves legitimate normative state without some prior
    authority premise.* Roots that are wanted belong in `G`, which is what `G`
    is for.

    The previous formulation lacked this and its grounding theorem was **false**:
    an edit with no grounds satisfies prior grounding vacuously and issues an
    occurrence whose only tree is itself, with a leaf outside the base.

    The two halves are consumed by different results. Grounding needs it of edits
    that **issue**; persistence needs it of edits that **dispose**, which is the
    unauthorized-repeal attack. Stating it over any state-changing edit is the
    union of the two and is why it is one premise rather than two.
    """
    bad, state = [], f.base
    for t in range(len(f.trace)):
        e = f.trace[t]
        if f.valid(state, e):
            if changes(f, state, t) and not e.grounds:
                bad.append(("ex nihilo", t))
            state = apply_edit(f, state, t)
    return tuple(bad)


PREMISES = (("S1", s1_prior_grounding), ("S2", s2_no_ex_nihilo))


def violations(f: Frame) -> dict:
    return {n: c(f) for n, c in PREMISES if c(f)}


def fresh_by_construction(f: Frame) -> tuple:
    """Freshness, as a fact rather than a premise.

    Two edits at one position cannot exist, because the trace is a list. Checked
    anyway so the claim is exercised, and so a realization that manufactures its
    own occurrences is caught.
    """
    seen, bad = set(f.base), []
    for t in range(len(f.trace)):
        for o in f.issued(t):
            if o.pos != t:
                bad.append(("mis-positioned", t, o))
            if o in seen:
                bad.append(("reissued", t, o))
            seen.add(o)
    return tuple(bad)


# ------------------------------------------------------------- the theorem


@dataclass(frozen=True)
class Tree:
    occ: Occ
    edit: Optional[int]
    children: tuple


def tree(f: Frame, o: Occ, upto: Optional[int] = None) -> Optional[Tree]:
    """A grounding tree for `o`, or `None` if replay never admitted it.

    **Ranges over `admitted`, not over the live state.** Whether `o` is still in
    force is a different question; `CROSS_PROCESS_INTERFACE.md` §3 is what that
    costs.
    """
    upto = len(f.trace) if upto is None else upto
    if o in f.base:
        return Tree(o, None, ())
    if o not in admitted(f, upto) or o.pos not in accepted(f, upto):
        return None
    kids = []
    for g in sorted(f.trace[o.pos].grounds, key=str):
        sub = tree(f, g, o.pos)
        if sub is None:
            return None
        kids.append(sub)
    return Tree(o, o.pos, tuple(kids))


def leaves(t: Tree) -> frozenset:
    if not t.children:
        return frozenset({t.occ})
    return frozenset().union(frozenset(), *[leaves(k) for k in t.children])


def edits_of(t: Tree) -> frozenset:
    out = frozenset() if t.edit is None else frozenset({t.edit})
    for k in t.children:
        out |= edits_of(k)
    return out


def descends(t: Tree) -> bool:
    for k in t.children:
        if not (k.occ.pos < t.occ.pos or k.occ.pos == BASE):
            return False
        if not descends(k):
            return False
    return True


def thm_grounded_replay(f: Frame) -> tuple:
    """**Grounded Replay.** Under **S1** and **S2**, every admitted occurrence has
    a finite grounding tree: leaves in `G`, internal nodes accepted edits,
    children the grounds that edit invoked, child positions strictly smaller.

    *Proof.* Induction on trace position. `Adm_0 = G`, and a base occurrence is
    its own tree. An accepted edit at `t` has `grounds ⊆ Auth(L_t)` by **S1** and
    `L_t ⊆ Adm_t`, so each ground is admitted; every admitted occurrence lies in
    `G` or was issued at a position `< t`, so the induction hypothesis gives each
    a tree; **S2** makes the ground set non-empty for any edit that issues, so no
    issued occurrence is a leaf outside `G`. Hanging the grounds' trees under `t`
    gives one for each occurrence `t` issues. ∎

    A short induction, and the round does not pretend otherwise. What it earns is
    that neither of the two previous objects admitted it.
    """
    bad = []
    for o in sorted(admitted(f), key=str):
        pi = tree(f, o)
        if pi is None:
            bad.append(("no tree", o))
            continue
        if not leaves(pi) <= f.base:
            bad.append(("leaf outside the base", o))
        if not descends(pi):
            bad.append(("no strict descent", o))
    return tuple(bad)


def cor_no_self_ratification(f: Frame) -> tuple:
    """**Corollary 1.** No accepted edit is grounded in what it issues.

    By **S1** its grounds are in the pre-state, and every occurrence it issues
    carries its own position, which nothing in the pre-state does.
    """
    return tuple((t, tuple(sorted(f.trace[t].grounds & f.issued(t), key=str)))
                 for t in accepted(f)
                 if f.trace[t].grounds & f.issued(t))


def cor_no_laundering(f: Frame) -> tuple:
    """**Corollary 2.** An occurrence a rejected edit proposed is never admitted.

    A rejected edit is a no-op, and every occurrence any other edit issues carries
    that other edit's position. Downstream use cannot help: an edit invoking such
    an occurrence as a ground fails **S1**.

    About occurrence identity, not content. `office.readoption` is where the same
    content enters later through a different occurrence and is admitted.
    """
    taken = set(accepted(f))
    adm = admitted(f)
    return tuple((t, tuple(sorted(f.trace[t].issued(t) & adm, key=str)))
                 for t in range(len(f.trace))
                 if t not in taken and f.trace[t].issued(t) & adm)


def cor_persistence(f: Frame) -> tuple:
    """**Corollary 3.** Live until an accepted edit disposes it.

    ```text
    o in L_s  and no accepted u in [s, t) disposes o  =>  o in L_t
    ```

    Two lines: a rejected edit is a no-op and an accepted edit that does not
    dispose `o` keeps it. What earns it is that the previous object's persistence
    was about the raw process, and an unauthorized revocation defeated it.
    """
    bad = []
    for s in range(len(f.trace) + 1):
        state = replay(f, s)
        for o in sorted(state, key=str):
            for t in range(s + 1, len(f.trace) + 1):
                if any(o in f.trace[u].dispose
                       for u in accepted(f, t) if s <= u < t):
                    break
                if o not in replay(f, t):
                    bad.append((o, s, t))
                    break
    return tuple(bad)


# -------------------------------------------------- lineage and currentness


def live(f: Frame, t: Optional[int] = None) -> frozenset:
    return replay(f, t)


def grounded(f: Frame, o: Occ, t: Optional[int] = None) -> bool:
    return tree(f, o, t) is not None


def relations(f: Frame, t: Optional[int] = None) -> dict:
    """`Live ⊆ Admitted`, and on a fixed trace **Grounded = Admitted**.

    The third notion is not independent: a lineage is built from the accepted
    edits of *this* trace, so having one and having been issued by one coincide.
    What is independent, and what the previous formulation conflated, is
    **admitted** against **live**.
    """
    t = len(f.trace) if t is None else t
    adm, lv = admitted(f, t), live(f, t)
    return {
        "live": lv,
        "admitted": adm,
        "grounded": frozenset(o for o in adm if grounded(f, o, t)),
        "live_subset_admitted": lv <= adm,
        "admitted_not_live": adm - lv,
    }


# ------------------------------------------------------- checkers, exactly


def with_checker(f: Frame, check: Callable) -> Frame:
    return Frame(f.base, f.trace, f.auth, check)


def agrees_on_trace(f: Frame, check: Callable) -> tuple:
    """**The exact condition.** The checker matches the semantic relation at each
    state the *semantic* replay actually reaches.

    ```text
    for every t:  Check(L_t, e_t)  <->  Valid(L_t, e_t)
    ```

    Weaker than global extensional equality — it says nothing about states the
    trace never reaches — and strictly stronger than one-sided soundness.
    """
    bad, state = [], f.base
    for t in range(len(f.trace)):
        e = f.trace[t]
        v, c = f.valid(state, e), check(state, e)
        if v != c:
            bad.append(("disagrees", t, v, c))
        if v:
            state = apply_edit(f, state, t)
    return tuple(bad)


def thm_simulation(f: Frame, check: Callable) -> bool:
    """**Simulation.** Agreement along the trace gives `Lhat_t = L_t` for every `t`.

    Induction: the states are equal at 0, and equal states with equal verdicts
    have equal successors. Both projections then agree, so a recognizer reading
    either gets the semantic answer. ∎
    """
    if agrees_on_trace(f, check):
        return False
    g = with_checker(f, check)
    return all(replay(f, t) == replay(g, t) for t in range(len(f.trace) + 1))


def sound_at_own_state(f: Frame, check: Callable) -> tuple:
    """The **rejected** notion, kept so the two run side by side.

    `Check(Lhat, e) -> Valid(Lhat, e)`, evaluated at the checker's own state. It
    is what the previous pass called soundness and it is worth nothing: a checker
    missing a valid revocation keeps an authority the semantic replay removed, and
    every later verdict it takes is evaluated against a state that never
    legitimately existed. `COUNTERMODELS.md` §3.
    """
    bad, state = [], f.base
    for t in range(len(f.trace)):
        e = f.trace[t]
        if check(state, e):
            if not f.valid(state, e):
                bad.append(("accepted an invalid edit", t))
            state = apply_edit(f, state, t)
    return tuple(bad)


def divergence(f: Frame, check: Callable) -> dict:
    """What a checker's replay gets wrong, split by direction."""
    g = with_checker(f, check)
    lv, lhat = live(f), live(g)
    return {"missing": lv - lhat, "spurious": lhat - lv,
            "agrees": agrees_on_trace(f, check)}
