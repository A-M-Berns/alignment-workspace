"""Answerability Continuity: the second replay, over outstanding obligations.

Grounded Replay controls **creation**: nothing acquires standing without licensed
ancestry. This controls **destruction**: nothing stops being owed except through a
declared discharge or a succession.

```text
O_0     = the base obligations
O_{t+1} = O_t                                            if e_t is rejected
        = (O_t \\ (discharges_t union transferred_t)) union opens_t   if accepted
```

**The same acceptance predicate drives both replays.** That is the only place the
two halves touch, and it is the only thing packaging them together earns: an act
the process was not entitled to perform discharges nothing.

Nothing here is imported by `replay.py`. Obligation identity is `(pos, slot)`
again, so unique birth is free and no premise has to ask for it.

```text
Due        which reasons place something under obligation      semantic
Disposes   which acts count as discharging one                 semantic
Transfers  which successions carry one                         semantic
```

Those three are parameters in exactly the sense `Permit` turned out to be. What
is structural is that an obligation cannot leave the open set by any other route.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional

import replay as rp


BASE = rp.BASE


@dataclass(frozen=True)
class Ob:
    """An obligation occurrence: this issue, become outstanding at this act."""

    pos: int
    slot: int

    def __str__(self) -> str:
        return f"q{'G' if self.pos == BASE else self.pos}.{self.slot}"


@dataclass(frozen=True)
class Duties:
    """What each edit does to the outstanding set, as declared by the semantics.

    ```text
    opens[t]       obligations the act at t makes outstanding
    discharges[t]  outstanding obligations it disposes of
    transfers[t]   {old: successors}, the successors being among opens[t]
    ```

    `discharges` and `transfers` are where `Disposes` and `Transfers` have already
    been consulted; this module never re-decides them.
    """

    base: frozenset
    opens: Mapping                     # position -> frozenset[Ob]
    discharges: Mapping                # position -> frozenset[Ob]
    transfers: Mapping                 # position -> {Ob: frozenset[Ob]}
    drops: Mapping = field(default_factory=dict)   # removed by neither route

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
        premise that can fail rather than a fact about the type: a realization
        that quietly loses an issue is representable here and is caught.
        """
        return self.drops.get(t, frozenset())


def step(d: Duties, out: frozenset, t: int) -> frozenset:
    return (out - d.discharged(t) - d.moved(t) - d.dropped(t)) | d.opened(t)


def outstanding(f: rp.Frame, d: Duties, upto: Optional[int] = None) -> frozenset:
    """`O_t`. Rejected edits are no-ops here too, and that is the interaction."""
    upto = len(f.trace) if upto is None else upto
    acc = set(rp.accepted(f, upto))
    out = d.base
    for t in range(upto):
        if t in acc:
            out = step(d, out, t)
    return out


def ever_open(f: rp.Frame, d: Duties, upto: Optional[int] = None) -> frozenset:
    upto = len(f.trace) if upto is None else upto
    out = set(d.base)
    for t in rp.accepted(f, upto):
        out |= d.opened(t)
    return frozenset(out)


# ------------------------------------------------------ structural premises


def a1_controlled_destruction(f: rp.Frame, d: Duties) -> tuple:
    """**A1.** An accepted edit removes an outstanding obligation only by
    discharging it or by transferring it, and every successor it names is one it
    opens.

    *Nothing stops being owed by accident.* The dual of prior grounding: that one
    says what a new item needs behind it, this says what a departing item needs
    in front of it.
    """
    bad, out = [], d.base
    for t in rp.accepted(f):
        gone = out - step(d, out, t)
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
        out = step(d, out, t)
    return tuple(bad)


def a2_fresh_obligations(f: rp.Frame, d: Duties) -> tuple:
    """**A2.** An act opens obligations nobody has opened. Free from the type."""
    seen, bad = set(d.base), []
    for t in range(len(f.trace)):
        for q in d.opened(t):
            if q.pos != t:
                bad.append(("mis-positioned", t, q))
            if q in seen:
                bad.append(("reopened", t, q))
            seen.add(q)
    return tuple(bad)


PREMISES = (("A1", a1_controlled_destruction), ("A2", a2_fresh_obligations))


def violations(f: rp.Frame, d: Duties) -> dict:
    return {n: c(f, d) for n, c in PREMISES if c(f, d)}


# ------------------------------------------------------------- the theorem


def carries(f: rp.Frame, d: Duties, q: Ob, s: int, t: int) -> tuple:
    """A transfer chain from `q` at `s` to something outstanding at `t`, or ().

    Follows successors through accepted edits only. Returns the chain, so the
    theorem's witness is exhibited rather than asserted.
    """
    frontier = [(q, s, (q,))]
    seen = set()
    while frontier:
        cur, at, chain = frontier.pop()
        if (cur, at) in seen:
            continue
        seen.add((cur, at))
        if cur in outstanding(f, d, t):
            return chain
        for u in rp.accepted(f, t):
            if u < at:
                continue
            for nxt in d.successors(u, cur):
                frontier.append((nxt, u + 1, chain + (nxt,)))
    return ()


def discharged_between(f: rp.Frame, d: Duties, q: Ob, s: int, t: int) -> Optional[int]:
    for u in rp.accepted(f, t):
        if u >= s and q in d.discharged(u):
            return u
    return None


def thm_answerability_continuity(f: rp.Frame, d: Duties) -> tuple:
    """**Answerability Continuity.** Under A1 and A2, an obligation outstanding at
    `s` is, at every later `t`, either discharged by an accepted edit in `[s,t)`
    or connected by a finite chain of accepted transfers to one outstanding at
    `t`.

    *Proof.* Induction on `t - s`. A rejected edit is a no-op. An accepted edit
    either leaves `q` alone, discharges it, or transfers it — by **A1** there is
    no fourth case — and in the last case every successor it names is opened by
    that same edit, so the chain extends by one and the obligation index strictly
    increases, which by **A2** makes the chain finite. ∎

    Returns the `(q, s, t)` triples with neither a discharge nor a carrier.
    """
    bad = []
    for s in range(len(f.trace) + 1):
        for q in sorted(outstanding(f, d, s), key=str):
            for t in range(s + 1, len(f.trace) + 1):
                if discharged_between(f, d, q, s, t) is not None:
                    continue
                if not carries(f, d, q, s, t):
                    bad.append((q, s, t))
                    break
    return tuple(bad)


def cor_no_silent_loss(f: rp.Frame, d: Duties) -> tuple:
    """**Corollary.** Every obligation ever outstanding is, at the end, discharged
    or represented by an outstanding descendant."""
    end = len(f.trace)
    bad = []
    for q in sorted(ever_open(f, d), key=str):
        s = 0 if q.pos == BASE else q.pos + 1
        if discharged_between(f, d, q, s, end) is not None:
            continue
        if not carries(f, d, q, s, end):
            bad.append(q)
    return tuple(bad)


def ungated(d: Duties, trace_len: int, upto: Optional[int] = None) -> frozenset:
    """The outstanding set if every edit acted, entitled or not.

    The comparison object for the interaction below: it is what a second replay
    would compute if it had its own acceptance predicate instead of sharing the
    entitlement one.
    """
    upto = trace_len if upto is None else upto
    out = d.base
    for t in range(upto):
        out = step(d, out, t)
    return out


def cor_discharge_requires_entitlement(f: rp.Frame, d: Duties) -> frozenset:
    """**The interaction.** An act the process was not entitled to perform
    discharges nothing.

    The only place the two replays touch: both are driven by the same acceptance
    predicate, so a rejected edit is a no-op on the outstanding set as well.

    Returns what an ungated replay would have lost — non-empty exactly when some
    rejected edit claimed a discharge or a transfer. `office.rogue_discharge` is
    the constitution where that happens, and it is the whole of what packaging
    the two halves together earns.
    """
    return outstanding(f, d) - ungated(d, len(f.trace))


# ------------------------------------------------- the quantitative question


def potential(f: rp.Frame, d: Duties, weight: Callable,
              upto: Optional[int] = None) -> float:
    """A supplied burden, summed over what is outstanding. Not part of the kernel."""
    return sum(weight(q) for q in outstanding(f, d, upto))


def potential_trace(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    return tuple(potential(f, d, weight, t) for t in range(len(f.trace) + 1))


def diluting_edits(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    """Accepted transfers whose successors weigh less than the parent replaced.

    **Per-parent accounting**, and it is the lenient one. See
    `diluting_edits_total`.
    """
    bad, out = [], d.base
    for t in rp.accepted(f):
        for q in sorted(d.moved(t), key=str):
            before = weight(q)
            after = sum(weight(x) for x in d.successors(t, q))
            if after < before:
                bad.append((t, q, before, after))
        out = step(d, out, t)
    return tuple(bad)


def diluting_edits_total(f: rp.Frame, d: Duties, weight: Callable) -> tuple:
    """Accepted edits whose transferred successors weigh less **in total** than
    the obligations they replaced.

    The two notions come apart on a **merge**. Two parents of weight 1 mapping to
    one successor of weight 1.5 passes per-parent — each parent sees 1.5, which is
    more than its own 1 — and fails in total, since 2 became 1.5. So the total is
    the accounting a conservation claim needs, and the per-parent reading is not a
    weaker version of it but a wrong one.
    """
    bad, out = [], d.base
    for t in rp.accepted(f):
        moved = d.moved(t) & out
        if moved:
            before = sum(weight(q) for q in moved)
            targets = frozenset().union(frozenset(),
                                        *[d.successors(t, q) for q in moved])
            after = sum(weight(x) for x in targets)
            if after < before - 1e-9:
                bad.append((t, tuple(sorted(map(str, moved))), before, after))
        out = step(d, out, t)
    return tuple(bad)


def thm_no_dilution_gives_monotone_potential(f: rp.Frame, d: Duties,
                                             weight: Callable) -> bool:
    """**Conditional.** If no accepted transfer reduces the summed weight, the
    potential is non-increasing except by discharge.

    The exact dual of the capability result: a theorem about a class of
    `Transfers` semantics, not a constraint on all of them. Nothing structural
    excludes dilution, because the kernel is blind to what an obligation *says*
    and a diluted successor is a content change — the same reason radical
    normative revision is permitted.
    """
    if diluting_edits(f, d, weight):
        return True                    # the hypothesis does not apply
    trace = potential_trace(f, d, weight)
    discharged_any = any(d.discharged(t) for t in rp.accepted(f))
    return discharged_any or all(b <= a + 1e-9 for a, b in zip(trace, trace[1:]))
