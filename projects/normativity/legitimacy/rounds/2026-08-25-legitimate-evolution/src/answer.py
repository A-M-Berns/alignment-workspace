"""Answerability: what becomes owed, and how it may stop being owed.

Two sets, not one, and the distinction is the entitlement side's `Admitted` /
`Live` in another costume:

```text
Incurred_t     every claim the process has ever taken on
Outstanding_t  those not yet resolved
```

The theorem quantifies over **incurred**. Quantifying over what happens to be
outstanding at a chosen start time was the previous version's shape, and it cannot
say anything at all about a claim incurred and resolved between two observations.

```text
I_{t+1} = I_t u opens_t
O_{t+1} = (O_t u opens_t) \\ (disch_t u moved_t)      if Valid(L_t, e_t)
        = O_t u opens_t                                otherwise
```

Openings are ungated and removals are gated: a process is answerable for what
happened, including for an act it refused, and removing a claim is an exercise of
authority. Openings are unioned **before** the removals, so a claim may be
incurred and resolved by one event without ever being outstanding -- see
`ANSWERABILITY.md` §5.

```text
Due      the represented material, read against the strict pre-state, activates
         these claim keys.  Newly due = activated and not already incurred.
Resolve  done, or carry(S).
```

Two semantic parameters. `Due` is an **activation generator** over the whole
represented state, not a predicate on a reason occurrence: a claim key already
incurred is not newly due however long its reasons stay represented, which is what
stops a resolved claim from reopening forever.

**One structural premise, A1.** `D1` is a conformance condition at the
realization boundary and is not used by the induction; `ANSWERABILITY.md` §7 is
the argument, and it corrects the previous pass, which shipped it as a premise.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional

import replay as rp


BASE = rp.BASE

OPEN = "open"
DISCHARGED = "discharged"
CARRIED = "carried"


@dataclass(frozen=True)
class Ob:
    """A claim occurrence: this claim, incurred at this position.

    Minted whether or not the claim survives the step, so the theorem can say
    *this claim was handled* about one incurred and resolved at once. The
    entitlement side needed the same move to talk about an occurrence that was
    admitted and later disposed of.
    """

    pos: int
    slot: int

    def __str__(self) -> str:
        return f"q{'G' if self.pos == BASE else self.pos}.{self.slot}"


@dataclass(frozen=True)
class Duties:
    """What each event does to the answerability state, as the semantics says.

    ```text
    opens[t]       claims incurred at t
    discharges[t]  claims Resolve judged done
    transfers[t]   {q: S}, Resolve judged carry(S)
    drops[t]       removed by neither route -- the A1 bait
    due[t]         claim keys Due activates at t, before newness is applied
    key[q]         which claim key an occurrence realizes
    ```
    """

    base: frozenset
    opens: Mapping
    discharges: Mapping
    transfers: Mapping
    drops: Mapping = field(default_factory=dict)
    due: Mapping = field(default_factory=dict)
    key: Mapping = field(default_factory=dict)

    def opened(self, t: int) -> frozenset:
        return self.opens.get(t, frozenset())

    def discharged(self, t: int) -> frozenset:
        return self.discharges.get(t, frozenset())

    def moved(self, t: int) -> frozenset:
        return frozenset(self.transfers.get(t, {}))

    def successors(self, t: int, q: Ob) -> frozenset:
        return self.transfers.get(t, {}).get(q, frozenset())

    def dropped(self, t: int) -> frozenset:
        return self.drops.get(t, frozenset())

    def activated(self, t: int) -> frozenset:
        """Claim keys `Due` activates at `t`. Not yet filtered for newness."""
        return self.due.get(t, frozenset())

    def key_of(self, q: Ob):
        return self.key.get(q, q)


def step(d: Duties, out: frozenset, t: int, accepted: bool) -> frozenset:
    """One step of the outstanding fold.

    Openings are applied **first**, so an event may incur and resolve a claim in
    one step. What stops that from being a loophole is not the union order but
    that `Resolve` reads the strict pre-state: `ANSWERABILITY.md` §6.
    """
    grown = out | d.opened(t)
    if not accepted:
        return grown
    return grown - d.discharged(t) - d.moved(t) - d.dropped(t)


def incurred(f: rp.Frame, d: Duties, upto: Optional[int] = None) -> frozenset:
    """`I_t`. Ungated: a claim incurred at a refused event is still incurred."""
    upto = len(f.trace) if upto is None else upto
    out = set(d.base)
    for t in range(upto):
        out |= d.opened(t)
    return frozenset(out)


def outstanding(f: rp.Frame, d: Duties, upto: Optional[int] = None) -> frozenset:
    upto = len(f.trace) if upto is None else upto
    acc = set(rp.accepted(f, upto))
    out = d.base
    for t in range(upto):
        out = step(d, out, t, t in acc)
    return out


def newly_due(d: Duties, t: int) -> frozenset:
    """Claim keys `Due` activates at `t` that no earlier claim already realizes.

    *Already incurred is not newly due.* Without this, a claim whose reasons stay
    represented is re-activated at every later position and can never be
    legitimately resolved -- `ANSWERABILITY.md` §4 builds that countermodel.
    """
    before = {d.key_of(q) for q in d.base}
    for u in range(t):
        before |= {d.key_of(q) for q in d.opened(u)}
    return frozenset(d.activated(t) - before)


# ---------------------------------------------------- the structural premise


def a1_controlled_resolution(f: rp.Frame, d: Duties) -> tuple:
    """**A1.** An accepted event removes an outstanding claim only by a `Resolve`
    judgment: `done`, or `carry(S)` with `S` non-empty and `S subset O_{t+1}`.

    *Nothing stops being owed without a resolution witness.* `S` is **not**
    required to be fresh. Carrying a claim into one already outstanding is
    ordinary consolidation, and the previous version's fresh-successor clause
    refused it while the derivation handled it correctly.

    A rejected event removes nothing, which is structural rather than a clause:
    `step` does not consult its disposals.
    """
    bad, out = [], d.base
    acc = set(rp.accepted(f))
    for t in range(len(f.trace)):
        after = step(d, out, t, t in acc)
        if t in acc:
            grown = out | d.opened(t)
            for q in sorted(grown - after, key=str):
                if q not in d.discharged(t) and q not in d.moved(t):
                    bad.append(("vanished", t, q))
            for q in sorted(d.moved(t), key=str):
                if q not in grown:
                    bad.append(("carried what was not outstanding", t, q))
                succ = d.successors(t, q)
                if not succ:
                    bad.append(("carried to nothing", t, q))
                elif succ - after:
                    bad.append(("successor not outstanding after the step", t, q,
                                tuple(sorted(succ - after, key=str))))
            for q in sorted(d.discharged(t), key=str):
                if q not in grown:
                    bad.append(("discharged what was not outstanding", t, q))
            for q in sorted(d.dropped(t) & grown, key=str):
                bad.append(("removed with no resolution", t, q))
        out = after
    return tuple(bad)


PREMISES = (("A1", a1_controlled_resolution),)


def violations(f: rp.Frame, d: Duties) -> dict:
    return {n: c(f, d) for n, c in PREMISES if c(f, d)}


# --------------------------------------------- the realization-boundary check


def d1_due_realization(f: rp.Frame, d: Duties) -> tuple:
    """**D1.** Every newly due claim key is realized by a claim incurred there.

    **Not a premise of the theorem below**, which never consults it. It is a
    conformance condition relating the semantics to what the process recorded.
    Dropping it does not make the induction fail; it makes the conclusion
    quantify over a smaller set, which is exactly how a process can satisfy
    everything structural and still ignore what it has recognized as owed.

    Kept in the package because Legitimate Evolution is the *composition*, and
    `ANSWERABILITY.md` §7 argues that is the honest layering.
    """
    bad = []
    for t in range(len(f.trace)):
        realized = {d.key_of(q) for q in d.opened(t)}
        for k in sorted(newly_due(d, t) - realized, key=str):
            bad.append(("activated and not incurred", t, k))
    return tuple(bad)


CONFORMANCE = (("D1", d1_due_realization),)


def nonconformance(f: rp.Frame, d: Duties) -> dict:
    return {n: c(f, d) for n, c in CONFORMANCE if c(f, d)}


# ------------------------------------------------------------- the theorem


def resolution(f: rp.Frame, d: Duties, q: Ob, s: int,
               t: Optional[int] = None) -> Optional[dict]:
    """The finite resolution derivation of `q` over `[s, t)`.

    Leaves are `OPEN` or `DISCHARGED`; internal nodes are `CARRIED`. Returns
    `None` when no derivation exists -- `q` left by neither route, or was carried
    to nothing -- so a broken process is reported rather than silently resolved.

    Finite because each child begins at a strictly later position and positions
    are bounded by `t`. Nothing about occurrence identity is used, which is why
    the previous pass's freshness premise was inert.
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
                return None
            kids = tuple(resolution(f, d, x, u + 1, t) for x in succ)
            if any(k is None for k in kids):
                return None
            return {"ob": q, "at": u, "verdict": CARRIED, "children": kids}
        if q in d.dropped(u):
            return None
    if q in outstanding(f, d, t):
        return {"ob": q, "at": t, "verdict": OPEN, "children": ()}
    return None


def frontier(node) -> tuple:
    if node is None:
        return ()
    if not node["children"]:
        return (node,)
    return tuple(x for k in node["children"] for x in frontier(k))


def born(q: Ob) -> int:
    return 0 if q.pos == BASE else q.pos


def thm_answerability_resolution(f: rp.Frame, d: Duties) -> tuple:
    """**Answerability Resolution.** Under **A1**, every claim incurred by `t` has
    a finite resolution derivation rooted at it whose frontier is non-empty and
    every branch of which is either a claim outstanding at `t` or a claim an
    accepted event discharged before `t`.

    *Proof.* Induction on `t - s`. If no accepted event in `[s,t)` resolves `q`
    then by **A1** nothing removes it, so `q` is outstanding at `t` and the
    derivation is a leaf. Otherwise take the first that does. `done` gives a
    discharged leaf. `carry(S)` gives children: **A1** makes `S` non-empty and
    puts every member in `O_{u+1}`, so each child is a claim outstanding at a
    strictly later position with a derivation over the shorter interval. Finite
    branching, bounded depth. ∎

    **Every branch is accounted for.** There is no surviving-descendant escape: a
    split one of whose branches is silently lost has no derivation, because the
    lost branch's own subderivation is `None`.

    Returns the `(q, t)` pairs with no derivation.
    """
    bad = []
    for t in range(len(f.trace) + 1):
        for q in sorted(incurred(f, d, t), key=str):
            if resolution(f, d, q, born(q), t) is None:
                bad.append((q, t))
    return tuple(bad)


def cor_no_silent_loss(f: rp.Frame, d: Duties) -> tuple:
    end = len(f.trace)
    return tuple(q for q in sorted(incurred(f, d), key=str)
                 if resolution(f, d, q, born(q), end) is None)


def cor_recognized_is_resolved(f: rp.Frame, d: Duties) -> tuple:
    """**Legitimate Evolution, answerability half.** D1 composed with the theorem:
    every claim the semantics newly made due has a resolution derivation.

    Returns the newly-due keys with no such derivation -- whether because the
    process never incurred them, or because what it incurred was lost.
    """
    end = len(f.trace)
    bad = []
    for t in range(len(f.trace)):
        realized = {d.key_of(q): q for q in d.opened(t)}
        for k in sorted(newly_due(d, t), key=str):
            q = realized.get(k)
            if q is None or resolution(f, d, q, born(q), end) is None:
                bad.append((k, t))
    return tuple(bad)


# ------------------------------------------------------------ the gating


def ungated(d: Duties, trace_len: int, upto: Optional[int] = None) -> frozenset:
    upto = trace_len if upto is None else upto
    out = d.base
    for t in range(upto):
        out = step(d, out, t, True)
    return out


def cor_discharge_requires_entitlement(f: rp.Frame, d: Duties) -> frozenset:
    """An event the process was not entitled to perform resolves nothing."""
    return outstanding(f, d) - ungated(d, len(f.trace))


def cor_opening_needs_no_entitlement(f: rp.Frame, d: Duties) -> frozenset:
    """A claim may be incurred at an event the process refused."""
    acc = set(rp.accepted(f))
    return frozenset(q for t in range(len(f.trace)) if t not in acc
                     for q in d.opened(t)) & incurred(f, d)


# ------------------------------------------------- the quantitative question


def potential(f: rp.Frame, d: Duties, weight: Callable,
              upto: Optional[int] = None) -> float:
    return sum(weight(q) for q in outstanding(f, d, upto))


def potential_trace(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    return tuple(potential(f, d, weight, t) for t in range(len(f.trace) + 1))


def diluting_edits(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    """Per-parent accounting. Not a weaker form of the total but a wrong one."""
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
    """Total accounting, which is what any later quantitative law must use.

    Two parents of weight 1 carried to one successor of weight 1.5 passes
    per-parent and fails here.
    """
    bad, out = [], d.base
    acc = set(rp.accepted(f))
    for t in range(len(f.trace)):
        if t in acc:
            moved = d.moved(t) & (out | d.opened(t))
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
    """Claims incurred without being a named successor: they raise the burden
    however well transfers behave, which is the hypothesis a conservation claim
    must state and the withdrawn version omitted."""
    bad = []
    for t in range(len(f.trace)):
        named = frozenset().union(
            frozenset(), *[d.successors(t, q) for q in d.moved(t)])
        for q in sorted(d.opened(t) - named, key=str):
            bad.append((t, q))
    return tuple(bad)
