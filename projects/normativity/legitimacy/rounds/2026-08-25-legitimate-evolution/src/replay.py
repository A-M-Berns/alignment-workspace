"""Legitimate replay: the legitimate state is reconstructed, not filtered.

A process proposes a finite sequence of **edits**. The legitimate state is built
by replaying them and applying exactly the valid ones:

```text
L(alpha, 0)    = G
L(alpha, s+1)  = apply(L(alpha, s), e_s)   if Valid_alpha(L(alpha, s), e_s)
                 L(alpha, s)               otherwise
```

The raw process may diverge from this arbitrarily. What it does is a fact about
the raw process; what is legitimately in force is `L`.

Nothing here is a normative event, a reason occurrence, a settlement, an
answerability root, a replay of a record, or a price. `office.py` builds edit
sequences from a constitution and its gazette; `ri_frame.py` builds them from a
Reflective Integrity record. Both run the hypothesis checkers and the theorems
below unchanged.

```text
Occ                 an occurrence: what a particular act put in force
Edit                a frozen proposal: grounds, input, exercise, dispose, issue
G                   the base a recognizing process accepts
alpha               the audit context — what is currently believed about the past
Valid_alpha         the semantic legitimacy relation, a parameter
Permit              the authorization relation, a parameter
ProvOK              provenance and exercise adequacy, a parameter
Xi                  the threat class the recognizer cares about
```

**Occurrences, not contents.** An occurrence is *this* grant, tagged by when it
was made. Two acts issuing the same policy issue two occurrences. That choice is
what makes the no-laundering theorem true and what lets a later clean act adopt
the very content a rejected act proposed.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Iterable, Mapping, Optional, Sequence


AUTHORITY = "authority"
NORM = "norm"

BASE_TIME = -1


@dataclass(frozen=True)
class Occ:
    """An occurrence. `at` is the historical index of the act that issued it.

    Base occurrences carry `BASE_TIME`. Everything else carries the index of its
    issuing edit, which is what makes freshness a fact about the type rather than
    a condition anyone has to check.
    """

    at: int
    index: int
    sort: str = AUTHORITY

    def __str__(self) -> str:
        where = "G" if self.at == BASE_TIME else str(self.at)
        return f"{self.sort[0]}{where}.{self.index}"


@dataclass(frozen=True)
class Edit:
    """A frozen proposal. Everything a legitimacy judgment is allowed to read.

    ```text
    grounds   B   the occurrences invoked as the authority for this act
    input     I   the authorization-relevant information declared for it
    exercise  X   the evidence that this was an authentic exercise
    dispose       the occurrences it proposes to end
    issue         (sort, content) per occurrence it proposes to put in force
    scope         the domain it purports to act in
    ```

    `content` is carried but never read by `apply`, which is why unrestricted
    substantive revision is a property of the type rather than a theorem.
    """

    at: int
    grounds: frozenset
    dispose: frozenset = frozenset()
    issue: tuple = ()                  # ((sort, content), ...)
    input: object = None
    exercise: object = None
    scope: object = None
    request: object = None
    label: str = ""

    def declared(self) -> tuple:
        """The part a legitimacy judgment is allowed to read *before* the effect.

        `dispose` and `issue` are what the act turned out to do; `request` is
        what it asked for. Keeping them apart is what gives the factorization
        hypothesis content: same declared view, same effect is a claim, and it is
        false of a realization whose effect reads state nobody declared.
        """
        return (frozenset(self.grounds), self.input, self.exercise,
                self.scope, self.request)

    def issued(self) -> tuple:
        return tuple(Occ(self.at, i, sort)
                     for i, (sort, _) in enumerate(self.issue))

    def content(self) -> dict:
        return {Occ(self.at, i, sort): c
                for i, (sort, c) in enumerate(self.issue)}

    def __str__(self) -> str:
        return self.label or f"e{self.at}"


def apply_edit(state: frozenset, e: Edit) -> frozenset:
    """`apply`. Ends what it disposes, adds what it issues. Reads no content."""
    return (state - e.dispose) | frozenset(e.issued())


# --------------------------------------------------------------- the process


@dataclass(frozen=True)
class Process:
    """A finite proposed history, a base, and the parameters of legitimacy.

    `valid(alpha, state, edit)` is the semantic legitimacy relation and is a
    **parameter**: none of the theorems below assumes it is any good. What they
    assume is stated as `H1`-`H6`, each of which a realization can fail.
    """

    base: frozenset
    edits: tuple
    valid: Callable                    # (alpha, frozenset, Edit) -> bool
    contexts: tuple = ()               # the audit contexts in view
    permit: Optional[Callable] = None  # (state, edit) -> bool
    prov_ok: Optional[Callable] = None # (alpha, edit) -> bool
    view: Optional[Callable] = None    # (alpha, prefix) -> the declared view
    content: Mapping = field(default_factory=dict)   # base occurrence contents

    def at(self, s: int) -> Optional[Edit]:
        for e in self.edits:
            if e.at == s:
                return e
        return None

    def times(self) -> tuple:
        return tuple(sorted(e.at for e in self.edits))

    def horizon(self) -> int:
        return max([e.at for e in self.edits], default=BASE_TIME) + 1

    def contents(self) -> dict:
        out = dict(self.content)
        for e in self.edits:
            out.update(e.content())
        return out


def replay(p: Process, alpha, upto: Optional[int] = None) -> frozenset:
    """`L(alpha, t)`. The legitimate state after replaying the proposal."""
    upto = p.horizon() if upto is None else upto
    state = p.base
    for s in sorted(e.at for e in p.edits):
        if s >= upto:
            break
        e = p.at(s)
        if p.valid(alpha, state, e):
            state = apply_edit(state, e)
    return state


def accepted(p: Process, alpha, upto: Optional[int] = None) -> tuple:
    """The edits the replay actually applied."""
    upto = p.horizon() if upto is None else upto
    state, out = p.base, []
    for s in sorted(e.at for e in p.edits):
        if s >= upto:
            break
        e = p.at(s)
        if p.valid(alpha, state, e):
            out.append(e)
            state = apply_edit(state, e)
    return tuple(out)


def auth(state: frozenset) -> frozenset:
    """`Auth(L)` — what the deference consumer reads."""
    return frozenset(o for o in state if o.sort == AUTHORITY)


def norms(state: frozenset) -> frozenset:
    """`Norm(L)` — what the enforcement consumer reads."""
    return frozenset(o for o in state if o.sort == NORM)


# ------------------------------------------------------------ the hypotheses


def h1_mediated_mutation(p: Process) -> tuple:
    """**H1.** The legitimate state changes only by applying an edit.

    *Reading.* Nothing comes into or out of force except by an act on the
    record. Architectural: it is how `replay` is written, and it is listed
    because a realization that let state drift between edits would not be
    modelled by this object at all. Checked by re-deriving each step.
    """
    bad = []
    state = p.base
    for s in p.times():
        e = p.at(s)
        expect = apply_edit(state, e) if p.valid(None if not p.contexts
                                                 else p.contexts[0], state, e) \
            else state
        got = replay(p, p.contexts[0] if p.contexts else None, s + 1)
        if got != expect:
            bad.append((s, e))
        state = expect
    return tuple(bad)


def h2_fresh_occurrence(p: Process) -> tuple:
    """**H2.** An edit issues occurrences nobody has issued and nothing holds.

    *Reading.* A grant is a new thing, not a re-entry of an old one. Free from
    the type — an occurrence carries the index of its issuing edit — and it is
    what the no-laundering and finite-grounding theorems actually consume.
    """
    seen, bad = set(p.base), []
    for s in p.times():
        for o in p.at(s).issued():
            if o.at != s:
                bad.append(("mis-tagged", s, o))
            if o in seen:
                bad.append(("reissued", s, o))
            seen.add(o)
    return tuple(bad)


def h3_prestate_grounding(p: Process, alpha) -> tuple:
    """**H3.** A valid edit's grounds are authorities of the strict pre-state.

    *Reading.* You act under authority you already have. A hypothesis on the
    parameter `valid`, and the one that makes finite grounding an induction
    rather than a definition.
    """
    bad, state = [], p.base
    for s in p.times():
        e = p.at(s)
        if p.valid(alpha, state, e):
            missing = e.grounds - auth(state)
            if missing:
                bad.append((s, e, tuple(sorted(missing, key=str))))
            state = apply_edit(state, e)
    return tuple(bad)


def h4_permit_soundness(p: Process, alpha) -> tuple:
    """**H4.** A valid edit is one its grounds permit, for this exact edit.

    *Reading.* Holding a warrant is not doing whatever you like with it.
    Jurisdiction, scope, consent conditions, amendment rules and procedural
    conditions all live in `permit`, which is a parameter: the interface
    requires that some such relation be consulted, not what it says.

    `office.unauthorized_scope` is the process where a perfectly grounded
    authority acts outside its domain, and the round's previous succession
    calculus admitted it.
    """
    if p.permit is None:
        return (("no permit relation supplied",),)
    bad, state = [], p.base
    for s in p.times():
        e = p.at(s)
        if p.valid(alpha, state, e):
            if not p.permit(state, e):
                bad.append((s, e))
            state = apply_edit(state, e)
    return tuple(bad)


def h5_declared_factorization(p: Process, q: Process, alpha) -> tuple:
    """**H5.** Two proposals with the same declared view have the same verdicts
    and the same effects.

    *Reading.* Whatever the legitimacy rules read, they read through the
    interface. Hidden implementation state may differ arbitrarily and must not
    change what is valid or what an edit does.

    This is the general form of the pre-state condition the previous pass
    isolated. It is checked between two processes rather than inside one,
    because the content of the hypothesis is a comparison.
    """
    if p.view is None or q.view is None:
        return (("no view supplied",),)
    if p.base != q.base:
        return (("different bases",),)
    bad = []
    ps, qs = p.base, q.base
    for i, s in enumerate(p.times()):
        if p.view(alpha, i) != q.view(alpha, i):
            break
        pe, qe = p.at(s), q.at(s)
        if pe is None or qe is None or pe.declared() != qe.declared():
            break
        if (pe.dispose, pe.issue) != (qe.dispose, qe.issue):
            bad.append(("effect differs", s))
            break
        pv, qv = p.valid(alpha, ps, pe), q.valid(alpha, qs, qe)
        if pv != qv:
            bad.append(("verdict differs", s))
            break
        ps = apply_edit(ps, pe) if pv else ps
        qs = apply_edit(qs, qe) if qv else qs
        if ps != qs:
            bad.append(("state diverges", s))
            break
    return tuple(bad)


def h6_provenance_adequacy(p: Process, alpha, threat) -> tuple:
    """**H6.** A valid edit's declared input and exercise pass provenance, and
    provenance is adequate to the stated threat class.

    ```text
    Valid_alpha(L, e)  =>  ProvOK_alpha(e)
    every influence in Xi is one ProvOK can see
    ```

    *Reading.* The calculus actually asks about the influences anyone is worried
    about. `depends` is a fact about the world; nothing here computes it, and
    the hypothesis is what keeps a process that checks nothing from certifying
    everything.
    """
    if p.prov_ok is None:
        return (("no provenance relation supplied",),)
    bad, state = [], p.base
    for s in p.times():
        e = p.at(s)
        if p.valid(alpha, state, e):
            if not p.prov_ok(alpha, e):
                bad.append(("valid but provenance fails", s, e))
            state = apply_edit(state, e)
    for xi, reach in threat.items():
        if not reach <= _visible(p, alpha):
            bad.append(("uncovered influence", xi,
                        tuple(sorted(reach - _visible(p, alpha), key=str))))
    return tuple(bad)


def _visible(p: Process, alpha) -> frozenset:
    """The edits provenance can refuse. An influence outside it is invisible."""
    if p.prov_ok is None:
        return frozenset()
    return frozenset(e.at for e in p.edits if not p.prov_ok(alpha, e))


HYPOTHESES = ("H1", "H2", "H3", "H4", "H5", "H6")


def structural_violations(p: Process, alpha) -> dict:
    """H1-H4, the ones checkable inside one process."""
    out = {}
    for name, check in (("H1", lambda: h1_mediated_mutation(p)),
                        ("H2", lambda: h2_fresh_occurrence(p)),
                        ("H3", lambda: h3_prestate_grounding(p, alpha)),
                        ("H4", lambda: h4_permit_soundness(p, alpha))):
        bad = check()
        if bad:
            out[name] = bad
    return out


# --------------------------------------------------------------- theorems


@dataclass(frozen=True)
class Ground:
    """A node of a grounding certificate."""

    occ: Occ
    edit: Optional[int]                # the historical index that issued it
    children: tuple


def certificate(p: Process, alpha, o: Occ,
                upto: Optional[int] = None) -> Optional[Ground]:
    """A finite grounding tree for `o`, or `None` if it is not legitimate.

    Leaves are base occurrences; internal nodes are edits the replay accepted;
    children are the grounds that edit invoked. Historical time strictly
    decreases downwards, which is what makes the recursion terminate and what
    `thm_finite_grounding` reports on.

    No unique issuance is needed: if several accepted edits issued `o` the tree
    names one, and the theorem is about the route the certificate exhibits.
    """
    upto = p.horizon() if upto is None else upto
    if o not in replay(p, alpha, upto):
        return None
    if o.at == BASE_TIME:
        return Ground(o, None, ())
    taken = {e.at for e in accepted(p, alpha, upto)}
    if o.at not in taken:
        return None
    e = p.at(o.at)
    kids = []
    for g in sorted(e.grounds, key=str):
        sub = certificate(p, alpha, g, o.at)
        if sub is None:
            return None
        kids.append(sub)
    return Ground(o, o.at, tuple(kids))


def tree_edits(g: Ground) -> frozenset:
    out = frozenset() if g.edit is None else frozenset({g.edit})
    for k in g.children:
        out |= tree_edits(k)
    return out


def tree_leaves(g: Ground) -> frozenset:
    if not g.children:
        return frozenset({g.occ})
    return frozenset().union(frozenset(), *[tree_leaves(k) for k in g.children])


def thm_finite_grounding(p: Process, alpha) -> tuple:
    """**G1.** Every legitimate occurrence has a finite grounding tree whose
    leaves lie in the base, whose internal nodes are accepted edits, and whose
    historical index strictly decreases downwards.

    *Proof.* Induction on the historical index. The base holds at `L(alpha,0)=G`.
    An accepted edit at `s` has `grounds ⊆ Auth(L(alpha,s))` by **H3**, and by
    **H2** every occurrence of `L(alpha,s)` was issued strictly before `s` or is
    a base occurrence; so each ground has a tree of strictly smaller index, and
    hanging them under `s` gives one for what `s` issued. ∎

    Returns the occurrences with no such tree, or whose tree fails descent.
    """
    bad = []
    state = replay(p, alpha)
    for o in sorted(state, key=str):
        g = certificate(p, alpha, o)
        if g is None:
            bad.append(("no tree", o))
            continue
        if not tree_leaves(g) <= p.base:
            bad.append(("leaves outside the base", o))
        if not _descends(p, g):
            bad.append(("no strict descent", o))
    return tuple(bad)


def _descends(p: Process, g: Ground) -> bool:
    for k in g.children:
        if not (k.occ.at < g.occ.at or k.occ.at == BASE_TIME):
            return False
        if not _descends(p, k):
            return False
    return True


def thm_no_self_ratification(p: Process, alpha) -> tuple:
    """**G2.** No accepted edit is grounded in what it issues.

    *Proof.* By **H3** its grounds are in the pre-state; by **H2** what it
    issues is not. ∎
    """
    return tuple((e.at, tuple(sorted(e.grounds & frozenset(e.issued()), key=str)))
                 for e in accepted(p, alpha)
                 if e.grounds & frozenset(e.issued()))


def thm_no_laundering(p: Process, alpha) -> tuple:
    """**G3.** An occurrence a rejected edit proposed never becomes legitimate.

    ```text
    not Valid_alpha(L(alpha,s), e_s)  =>  for all u > s,
        no occurrence e_s proposed lies in L(alpha, u)
    ```

    *Proof.* The rejected edit is a no-op, so its occurrences are absent at
    `s+1`; and by **H2** every later edit issues occurrences tagged with its own
    later index, so none of them is one of these. Downstream use cannot help: a
    later edit invoking a rejected occurrence as a ground fails **H3**. ∎

    The work is done by the choice of occurrence identity rather than by the
    induction, and that is the point of the choice: `office.readoption` is the
    process where a later clean act adopts the very content a rejected act
    proposed, and it is legitimate.
    """
    taken = {e.at for e in accepted(p, alpha)}
    rejected = [e for e in p.edits if e.at not in taken]
    final = replay(p, alpha)
    bad = []
    for e in rejected:
        leaked = frozenset(e.issued()) & final
        if leaked:
            bad.append((e.at, tuple(sorted(leaked, key=str))))
    return tuple(bad)


def thm_noninterference(p: Process, q: Process, alpha) -> bool:
    """**G4.** Two proposals with the same declared view have the same legitimate
    state.

    *Proof.* Induction on the step, from **H5**: the view determines the edit and
    the verdict, and the state at each step is a function of the previous state
    and those. ∎

    Raw histories may differ arbitrarily outside the declared view. Authorized
    influence is not excluded: an influence that changes the declared input
    changes the view, and the two sides are then allowed to differ.
    """
    if h5_declared_factorization(p, q, alpha):
        return False
    return replay(p, alpha) == replay(q, alpha)


def thm_persistence(p: Process, alpha) -> tuple:
    """**G5.** Persistent until a **valid** edit disposes it.

    ```text
    o in L(alpha, s)  and no accepted edit in (s, u] disposes o
        =>  o in L(alpha, u)
    ```

    *Proof.* A rejected edit is a no-op and an accepted edit that does not
    dispose `o` keeps it. ∎

    The previous formulation took the raw lifecycle and intersected it with a
    derivability set, and so lost an occurrence whenever *anything* in the raw
    process removed it — including an act with no legitimate authority at all.
    `office.rogue_revocation` is that attack and `COUNTERMODELS.md` §1 runs it
    against both.
    """
    bad = []
    times = list(p.times()) + [p.horizon()]
    for i, s in enumerate(times):
        state = replay(p, alpha, s)
        for o in sorted(state, key=str):
            for u in times[i + 1:]:
                disposed = any(o in e.dispose
                               for e in accepted(p, alpha, u) if s <= e.at < u)
                if disposed:
                    break
                if o not in replay(p, alpha, u):
                    bad.append((o, s, u))
                    break
    return tuple(bad)


def thm_content_unconstrained(p: Process, alpha, sigma: Mapping) -> bool:
    """**G6.** Relabelling what occurrences say changes nothing legitimate.

    `apply` reads no content and `Occ` carries none, so this holds by the type.
    Its force is as a condition on a realization: one whose validity rules
    inspected what an occurrence says would not map onto a process at all.
    """
    before = replay(p, alpha)
    relabelled = {o: sigma.get(c, c) for o, c in p.contents().items()}
    return relabelled is not None and replay(p, alpha) == before


# ------------------------------------------------------- audit contexts


def retracted(p: Process, alpha, beta) -> frozenset:
    """What leaves the legitimate state when the audit context tightens."""
    return replay(p, alpha) - replay(p, beta)


def restored(p: Process, alpha, beta) -> frozenset:
    """What **enters** it. Not empty in general, and that is a result.

    Invalidating an edit that was a *revocation* leaves its target standing. So
    a stricter audit context is not a smaller legitimate state, and the earlier
    surprise that the challenge operator was neither monotone nor composable is
    this fact seen through a harder-to-read object.
    """
    return replay(p, beta) - replay(p, alpha)


# ---------------------------------------------- verifiers, and what they cost


def with_verifier(p: Process, verify: Callable) -> Process:
    """The same proposal replayed by a checker instead of by the semantic
    relation."""
    return Process(p.base, p.edits, verify, p.contexts, p.permit, p.prov_ok,
                   p.view, p.content)


def verifier_sound(p: Process, verify: Callable, alpha) -> tuple:
    """`Verify(L,e) => Valid(L,e)` along the replay the verifier itself drives."""
    bad, state = [], p.base
    for s in p.times():
        e = p.at(s)
        if verify(alpha, state, e):
            if not p.valid(alpha, state, e):
                bad.append(("accepted an invalid edit", s))
            state = apply_edit(state, e)
    return tuple(bad)


def verifier_complete(p: Process, verify: Callable, alpha) -> tuple:
    """`Valid(L,e) => Verify(L,e)` along the same replay.

    **The asymmetry the consumers care about.** A sound but incomplete checker
    under-approximates: it misses valid edits. For an occurrence entering force
    that is conservative and the deference consumer can live with it. For an
    occurrence *leaving* force it is not: a missed valid revocation leaves an
    obsolete norm in the enforcement target.
    """
    bad, state = [], p.base
    for s in p.times():
        e = p.at(s)
        if p.valid(alpha, state, e) and not verify(alpha, state, e):
            bad.append(("missed a valid edit", s, bool(e.dispose)))
        state = apply_edit(state, e) if verify(alpha, state, e) else state
    return tuple(bad)


def missed_disposals(p: Process, verify: Callable, alpha) -> tuple:
    """The valid disposals a checker misses — the ones enforcement cannot afford."""
    return tuple(b for b in verifier_complete(p, verify, alpha) if b[2])
