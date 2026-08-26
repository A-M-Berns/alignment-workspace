"""Answerability: required entry, controlled resolution.

Grounded Replay controls **creation of standing**: nothing acquires normative
standing without licensed ancestry. This module controls the obligation side, and
after this pass it controls *two* things rather than one:

```text
D1  what the process's own semantics makes due must enter the outstanding set
A1  what is outstanding leaves it only by a declared discharge or a declared
    succession
```

The previous pass had only the second, and called the pair a duality. It is not
one, and `ANSWERABILITY.md` §6 says so: entitlement is controlled creation,
answerability is *required* creation plus controlled resolution.

```text
O_0     = the base obligations
O_{t+1} = (O_t \\ (disch_t u moved_t)) u opens_t     if Valid(L_t, e_t)
        = O_t u opens_t                              otherwise
```

**The fold is gated asymmetrically, and that is the correction this pass makes.**
Removing an obligation is an exercise of authority and needs entitlement.
Acquiring one is not: a process becomes answerable for what happened, including
for an act it refused. An unauthorized act discharges nothing and may still open
a complaint about itself.

```text
Due       which represented reasons the semantics says are owed an answer
Resolve   which acts discharge an obligation, and which carry it to successors
```

Two parameters, not four. `Disposes` and `Transfers` were two names for the two
answers `Resolve` can give, and are folded together.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional

import replay as rp


BASE = rp.BASE

OPEN = "open"
DISCHARGED = "discharged"


@dataclass(frozen=True)
class Ob:
    """An obligation occurrence: this issue, become outstanding at this act."""

    pos: int
    slot: int

    def __str__(self) -> str:
        return f"q{'G' if self.pos == BASE else self.pos}.{self.slot}"


@dataclass(frozen=True)
class Duties:
    """What each edit does to the outstanding set, as the semantics declares it.

    ```text
    opens[t]       obligations the event at t makes outstanding
    discharges[t]  outstanding obligations it disposes of
    transfers[t]   {old: successors}, the successors being among opens[t]
    due[t]         what the semantics says is owed, given what is represented
    ```

    `Due` and `Resolve` have already been consulted by the time this is read;
    this module never re-decides them.
    """

    base: frozenset
    opens: Mapping                     # position -> frozenset[Ob]
    discharges: Mapping                # position -> frozenset[Ob]
    transfers: Mapping                 # position -> {Ob: frozenset[Ob]}
    drops: Mapping = field(default_factory=dict)   # removed by neither route
    due: Mapping = field(default_factory=dict)     # position -> frozenset[Ob]

    def opened(self, t: int) -> frozenset:
        return self.opens.get(t, frozenset())

    def discharged(self, t: int) -> frozenset:
        return self.discharges.get(t, frozenset())

    def moved(self, t: int) -> frozenset:
        return frozenset(self.transfers.get(t, {}))

    def successors(self, t: int, q: Ob) -> frozenset:
        return self.transfers.get(t, {}).get(q, frozenset())

    def dropped(self, t: int) -> frozenset:
        """Removals the semantics declared neither a discharge nor a transfer.

        A well-formed process has none. The channel exists so that **A1** is a
        premise that can fail rather than a fact about the type.
        """
        return self.drops.get(t, frozenset())

    def owed(self, t: int) -> frozenset:
        """What `Due` says is owed at `t`, given everything represented by then.

        Indexed by position rather than attached to a reason, because a reason
        represented at `u` can become owed later as the normative state changes.
        """
        return self.due.get(t, frozenset())


def step(d: Duties, out: frozenset, t: int, accepted: bool) -> frozenset:
    """One step of the obligation fold, gated asymmetrically.

    Openings apply whether or not the edit was accepted; removals do not.
    Openings are unioned **last**, so an obligation opened and discharged by one
    event is still outstanding afterwards — an event cannot use an obligation it
    creates to certify that it has already dealt with it.
    """
    if not accepted:
        return out | d.opened(t)
    return (out - d.discharged(t) - d.moved(t) - d.dropped(t)) | d.opened(t)


def outstanding(f: rp.Frame, d: Duties, upto: Optional[int] = None) -> frozenset:
    upto = len(f.trace) if upto is None else upto
    acc = set(rp.accepted(f, upto))
    out = d.base
    for t in range(upto):
        out = step(d, out, t, t in acc)
    return out


def ever_open(f: rp.Frame, d: Duties, upto: Optional[int] = None) -> frozenset:
    upto = len(f.trace) if upto is None else upto
    out = set(d.base)
    for t in range(upto):
        out |= d.opened(t)
    return frozenset(out)


# ------------------------------------------------------ structural premises


def d1_due_realization(f: rp.Frame, d: Duties) -> tuple:
    """**D1.** What the semantics says is owed at `t` is outstanding after `t`.

    *A recognized reason cannot be left out of the answerability dynamics.* Not a
    coverage requirement: `Due` speaks only about what is already represented, so
    a process that notices nothing owes nothing and satisfies this vacuously. Not
    a progress requirement either: it forces an obligation to be **entered**, and
    says nothing about its ever being closed.

    The obligation may already have been outstanding; D1 asks only that it be
    outstanding at `t+1`, which is what rules out both never entering it and
    entering and closing it in the same breath.
    """
    bad, out = [], d.base
    acc = set(rp.accepted(f))
    for t in range(len(f.trace)):
        after = step(d, out, t, t in acc)
        for q in sorted(d.owed(t) - after, key=str):
            bad.append(("recognized as due and not outstanding", t, q))
        out = after
    return tuple(bad)


def a1_controlled_resolution(f: rp.Frame, d: Duties) -> tuple:
    """**A1.** An accepted edit removes an outstanding obligation only by
    discharging it or by transferring it, and every successor it names is one it
    opens.

    *Nothing stops being owed by accident.* A rejected edit removes nothing at
    all, which is now structural rather than a clause: `step` does not consult
    its disposals.
    """
    bad, out = [], d.base
    acc = set(rp.accepted(f))
    for t in range(len(f.trace)):
        if t in acc:
            gone = out - step(d, out, t, True)
            for q in sorted(gone, key=str):
                if q not in d.discharged(t) and q not in d.moved(t):
                    bad.append(("vanished", t, q))
            for q in sorted(d.moved(t), key=str):
                if q not in out:
                    bad.append(("transferred what was not open", t, q))
                missing = d.successors(t, q) - d.opened(t)
                if missing:
                    bad.append(("successor not opened", t, q,
                                tuple(sorted(missing, key=str))))
                if not d.successors(t, q):
                    bad.append(("transferred to nothing", t, q))
            for q in sorted(d.discharged(t), key=str):
                if q not in out:
                    bad.append(("discharged what was not open", t, q))
            for q in sorted(d.dropped(t) & out, key=str):
                bad.append(("removed with no declared route", t, q))
        out = step(d, out, t, t in acc)
    return tuple(bad)


def fresh_by_construction(f: rp.Frame, d: Duties) -> tuple:
    """Obligation occurrences are born once, because `Ob(pos, slot)` says so.

    The previous pass shipped this as a premise **A2** and used it to argue that
    transfer chains terminate. It is not needed for that and it is not needed for
    anything else: see `ANSWERABILITY.md` §3. It is retained as a hygiene check on
    the *encoding*, so a `Duties` built by hand cannot claim an event opened
    something at another event's position.
    """
    seen, bad = set(d.base), []
    for t in range(len(f.trace)):
        for q in sorted(d.opened(t), key=str):
            if q.pos != t:
                bad.append(("mis-positioned", t, q))
            if q in seen:
                bad.append(("reopened", t, q))
            seen.add(q)
    return tuple(bad)


PREMISES = (("D1", d1_due_realization), ("A1", a1_controlled_resolution))

HYGIENE = (("fresh", fresh_by_construction),)


def violations(f: rp.Frame, d: Duties) -> dict:
    return {n: c(f, d) for n, c in PREMISES if c(f, d)}


# ------------------------------------------------------------- the theorem


def resolution(f: rp.Frame, d: Duties, q: Ob, s: int,
               t: Optional[int] = None) -> dict:
    """The finite resolution derivation of `q` between `s` and `t`.

    A node is `{"ob", "at", "verdict", "children"}`. The verdict is `OPEN` at a
    leaf still outstanding at `t`, `DISCHARGED` at a leaf an accepted edit
    disposed of, and `"carried"` at an internal node whose children are the
    successors an accepted edit named.

    Unfolds to a **tree** even though succession is in general a DAG: a split
    whose branches later transfer into one obligation gives that obligation two
    distinct leaves here. The unfolding is finite because each child starts at a
    strictly later trace position, so depth is bounded by `t - s`, and because
    every node has finitely many successors.

    Returns `None` for the cases the premises exclude: `q` left the outstanding
    set by neither route, or was carried to no successor at all. The second is
    why the conclusion asks for a **non-empty** frontier -- a node with no
    children is laundering wearing a derivation's shape, and an empty frontier
    would satisfy "every leaf is open or discharged" vacuously.
    """
    t = len(f.trace) if t is None else t
    acc = set(rp.accepted(f, t))
    for u in range(s, t):
        if u not in acc:
            continue
        if q in d.discharged(u):
            return {"ob": q, "at": u, "verdict": DISCHARGED, "children": ()}
        if q in d.moved(u):
            succ = sorted(d.successors(u, q), key=str)
            if not succ:
                return None            # carried to nothing is not a resolution
            kids = tuple(resolution(f, d, x, u + 1, t) for x in succ)
            if any(k is None for k in kids):
                return None
            return {"ob": q, "at": u, "verdict": "carried", "children": kids}
        if q in d.dropped(u):
            return None
    if q in outstanding(f, d, t):
        return {"ob": q, "at": t, "verdict": OPEN, "children": ()}
    return None


def frontier(node) -> tuple:
    """The leaves of a resolution derivation, in order."""
    if node is None:
        return ()
    if not node["children"]:
        return (node,)
    return tuple(x for k in node["children"] for x in frontier(k))


def thm_answerability_continuity(f: rp.Frame, d: Duties) -> tuple:
    """**Answerability Continuity.** Under **A1**, every obligation outstanding at
    `s` has, at every later `t`, a finite resolution derivation whose frontier is
    non-empty and consists only of obligations still outstanding at `t` and
    obligations an accepted edit discharged before `t`.

    *Proof.* Induction on `t - s`. If no accepted edit in `[s,t)` discharges,
    transfers or drops `q`, then by **A1** nothing removes it, so `q` is
    outstanding at `t` and the derivation is a leaf. Otherwise take the first such
    edit at `u`. A drop is excluded by **A1**. A discharge gives a leaf. A
    transfer gives children, each a successor that **A1** requires the same edit to
    open, hence outstanding at `u+1`, each with a derivation over the strictly
    shorter interval `[u+1, t)`; **A1** also forbids transferring to no successor,
    so the node has at least one child and the frontier stays non-empty. Finite
    branching and bounded depth make the tree finite. ∎

    **A2 is not used.** Termination comes from the interval shrinking, which the
    trace being a list already supplies; freshness of opened obligations is not
    consulted anywhere in the argument.

    Returns the `(q, s, t)` triples with no derivation.
    """
    bad = []
    for s in range(len(f.trace) + 1):
        for q in sorted(outstanding(f, d, s), key=str):
            for t in range(s + 1, len(f.trace) + 1):
                if resolution(f, d, q, s, t) is None:
                    bad.append((q, s, t))
                    break
    return tuple(bad)


def cor_no_silent_loss(f: rp.Frame, d: Duties) -> tuple:
    """**Corollary.** Every obligation ever outstanding has, at the end, a
    resolution derivation: nothing leaves the outstanding set unaccounted for."""
    end = len(f.trace)
    bad = []
    for q in sorted(ever_open(f, d), key=str):
        s = 0 if q.pos == BASE else q.pos + 1
        if resolution(f, d, q, s, end) is None:
            bad.append(q)
    return tuple(bad)


def cor_recognized_is_entered(f: rp.Frame, d: Duties) -> tuple:
    """**Corollary.** Every obligation the semantics ever made due has a
    resolution derivation from the position at which it became due.

    D1 plus the theorem. This is the clause the previous package lacked: without
    D1 a process satisfying everything else can recognize a reason as owing an
    answer and never enter it, and nothing in the obligation dynamics notices,
    because the dynamics only ever constrained departures.
    """
    end = len(f.trace)
    bad = []
    for t in range(len(f.trace)):
        for q in sorted(d.owed(t), key=str):
            if resolution(f, d, q, t + 1, end) is None:
                bad.append((q, t))
    return tuple(bad)


# ------------------------------------------------------------ the coupling


def ungated(d: Duties, trace_len: int, upto: Optional[int] = None) -> frozenset:
    """The outstanding set if every edit's disposals took effect, entitled or not."""
    upto = trace_len if upto is None else upto
    out = d.base
    for t in range(upto):
        out = step(d, out, t, True)
    return out


def cor_discharge_requires_entitlement(f: rp.Frame, d: Duties) -> frozenset:
    """**Coupling, one direction.** An act the process was not entitled to perform
    discharges nothing.

    Returns what an ungated fold would have lost.
    """
    return outstanding(f, d) - ungated(d, len(f.trace))


def cor_opening_needs_no_entitlement(f: rp.Frame, d: Duties) -> frozenset:
    """**Coupling, the other direction.** An obligation may open at an edit the
    process refused.

    Returns the obligations outstanding at the end that a **rejected** edit
    opened. Non-empty exactly when the process became answerable for something it
    declined to do — which is the case the previous pass's shared gate could not
    represent at all.
    """
    acc = set(rp.accepted(f))
    from_rejected = frozenset(
        q for t in range(len(f.trace)) if t not in acc for q in d.opened(t))
    return from_rejected & outstanding(f, d)


# ------------------------------------------------- the quantitative question


def potential(f: rp.Frame, d: Duties, weight: Callable,
              upto: Optional[int] = None) -> float:
    """A supplied burden, summed over what is outstanding. Not part of the kernel."""
    return sum(weight(q) for q in outstanding(f, d, upto))


def potential_trace(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    return tuple(potential(f, d, weight, t) for t in range(len(f.trace) + 1))


def diluting_edits(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    """Accepted transfers whose successors weigh less than the parent replaced.

    **Per-parent accounting**, and it is not a weaker form of the total but a
    wrong one. See `diluting_edits_total`. Kept only to exhibit that.
    """
    bad, out = [], d.base
    acc = set(rp.accepted(f))
    for t in range(len(f.trace)):
        if t in acc:
            for q in sorted(d.moved(t), key=str):
                before = weight(q)
                after = sum(weight(x) for x in d.successors(t, q))
                if after < before:
                    bad.append((t, q, before, after))
        out = step(d, out, t, t in acc)
    return tuple(bad)


def diluting_edits_total(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    """Accepted edits whose transferred successors weigh less **in total** than the
    obligations they replaced.

    The two notions come apart on a **merge**. Two parents of weight 1 mapping to
    one successor of weight 1.5 passes per-parent — each parent sees 1.5, which is
    more than its own 1 — and fails in total, since 2 became 1.5. So the total is
    the accounting a conservation claim needs.
    """
    bad, out = [], d.base
    acc = set(rp.accepted(f))
    for t in range(len(f.trace)):
        if t in acc:
            moved = d.moved(t) & out
            if moved:
                before = sum(weight(q) for q in moved)
                targets = frozenset().union(
                    frozenset(), *[d.successors(t, q) for q in moved])
                after = sum(weight(x) for x in targets)
                if after < before - 1e-9:
                    bad.append((t, tuple(sorted(map(str, moved))), before, after))
        out = step(d, out, t, t in acc)
    return tuple(bad)


def unheralded_openings(f: rp.Frame, d: Duties) -> tuple:
    """Obligations opened by an edit that no transfer of that edit names.

    The hypothesis the previous pass's quantitative claim silently omitted: a
    fresh obligation raises the burden without any transfer having diluted
    anything, so no condition on transfers alone can bound the potential.
    """
    bad = []
    for t in range(len(f.trace)):
        named = frozenset().union(
            frozenset(), *[d.successors(t, q) for q in d.moved(t)])
        for q in sorted(d.opened(t) - named, key=str):
            bad.append((t, q))
    return tuple(bad)


def thm_conserving_transfers_give_monotone_potential(
        f: rp.Frame, d: Duties, weight: Callable) -> bool:
    """**Conditional.** If no accepted edit dilutes in total, and every opened
    obligation is a successor named by a transfer of the edit that opens it, then
    the potential is non-increasing.

    Both hypotheses are needed and the previous pass's version stated neither
    correctly: it checked per-parent rather than total dilution, and it ignored
    that a fresh obligation raises the potential no matter what the transfers do.
    Its discharge escape clause made it unfalsifiable on any trace containing a
    discharge. It is withdrawn and replaced by this.

    This is a claim about a class of `Resolve` semantics, not a structural fact.
    """
    if diluting_edits_total(f, d, weight) or unheralded_openings(f, d):
        return True                    # the hypotheses do not apply
    trace = potential_trace(f, d, weight)
    return all(b <= a + 1e-9 for a, b in zip(trace, trace[1:]))
