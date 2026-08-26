"""Proper Exercise, analysed over a frozen kernel.

Grounded Replay says an authority has legitimate ancestry. It says nothing about
whether the authority was entitled to do the particular thing it did. This module
asks what mathematics is available for that question. It is an **analysis of
frames**, not an extension of `replay.py`: the kernel does not import it and is
unchanged.

```text
Cap(o)      what an authority occurrence may license — supplied by the semantics
Reach(L)    the union of what the live authorities may license
```

`Reach` rather than "the set of permitted edits": creating any new authority adds
new edits that can name it, so an edit-indexed notion counts a narrower
delegation as growth. What matters is whether the **capability** available in the
state grew.

The finding this module records: **the anti-escalation properties come from the
kernel's typing, not from any structure on the permission relation**, and even
then only two of the three are theorems.

```text
strict pre-state evaluation   ->  no jurisdictional self-ratification   theorem
fresh occurrences             ->  a rejected capability never enters     theorem
the effect is inside the edit  ->  the capability is *available* to be
                                   checked — and a permission that does not
                                   read it admits escalation anyway       not a theorem
```
"""
from __future__ import annotations

from typing import Callable, Optional

import replay as rp


def reach(f: rp.Frame, cap: Callable, state: frozenset) -> frozenset:
    """`Reach(L)`: the union of the capabilities the live authorities carry."""
    out = frozenset()
    for o in f.authorities(state):
        out |= cap(f.content.get(o))
    return out


def reach_trace(f: rp.Frame, cap: Callable) -> tuple:
    return tuple(reach(f, cap, rp.replay(f, t)) for t in range(len(f.trace) + 1))


def gained(f: rp.Frame, cap: Callable) -> tuple:
    """The steps at which capability entered the state that was not there before."""
    r = reach_trace(f, cap)
    return tuple((t, tuple(sorted(r[t + 1] - r[t])))
                 for t in range(len(r) - 1) if r[t + 1] - r[t])


def lost(f: rp.Frame, cap: Callable) -> tuple:
    r = reach_trace(f, cap)
    return tuple((t, tuple(sorted(r[t] - r[t + 1])))
                 for t in range(len(r) - 1) if r[t] - r[t + 1])


def widens(f: rp.Frame, cap: Callable, t: int) -> frozenset:
    """What `e_t` issues beyond the intersection of its grounds' capabilities.

    Descriptive, not a verdict: whether widening is permitted is the semantics'
    business, and `office.constitutional_widening` is a constitution that allows
    it.
    """
    held = None
    for g in f.trace[t].grounds:
        c = cap(f.content.get(g))
        held = c if held is None else (held & c)
    held = held or frozenset()
    issued = frozenset()
    for c in f.trace[t].issues:
        issued |= cap(c)
    return issued - held


def widening_edits(f: rp.Frame, cap: Callable) -> tuple:
    return tuple((t, tuple(sorted(widens(f, cap, t))))
                 for t in rp.accepted(f) if widens(f, cap, t))


# ------------------------------------------------------------- the results


def thm_mediated_change(f: rp.Frame, cap: Callable) -> tuple:
    """**E1.** Reach changes only at an accepted edit.

    A corollary of the replay: a rejected edit is a no-op, so the state is
    unchanged and so is anything computed from it. Recorded because it is the
    whole of what an **opaque** permission relation earns, and it is worth
    knowing that this is the whole of it.
    """
    acc = set(rp.accepted(f))
    return tuple((t, d) for t, d in gained(f, cap) + lost(f, cap)
                 if t not in acc)


def thm_no_jurisdictional_self_ratification(f: rp.Frame) -> tuple:
    """**E2.** No edit's permission can rest on a capability it creates.

    The permission is evaluated at `L_t`, and by freshness `L_t` is disjoint from
    `issue_t(e_t)`. So for **any** capability assignment whatever — the statement
    quantifies over `Cap` and never inspects it — an act cannot widen the
    authority that licenses it by widening it.

    `office.self_amendment(False)` is the attempt: an act citing the rule it is
    about to create. The ground is in `issue_t`, the pre-state does not contain
    it, and the act is refused.
    """
    return tuple((t, tuple(sorted(f.trace[t].grounds & f.issued(t), key=str)))
                 for t in rp.accepted(f)
                 if f.trace[t].grounds & f.issued(t))


def capability_is_available(f: rp.Frame, cap: Callable) -> bool:
    """**E3, and it is not a theorem.**

    Because `issues(e)` is part of `e`, the permission judgment at `L_t` has the
    issued capabilities in front of it. That makes the check *possible*. It does
    not make it happen: `office.blind_permit` is a constitution whose permission
    declines to read them, and its state gains a capability nobody licensed.

    So the third typing decision buys availability, and the rest is semantics.
    Returns whether what enters the state is what the edit carries.
    """
    for t in rp.accepted(f):
        declared = frozenset().union(frozenset(),
                                     *[cap(c) for c in f.trace[t].issues]) \
            if f.trace[t].issues else frozenset()
        entered = frozenset().union(frozenset(),
                                    *[cap(f.content[o]) for o in f.issued(t)]) \
            if f.issued(t) else frozenset()
        if declared != entered:
            return False
    return True


def thm_no_widening_gives_monotone_reach(f: rp.Frame, cap: Callable) -> bool:
    """**E4.** If no accepted edit widens, `Reach` is non-increasing.

    Each accepted edit's issued capability lies inside the intersection of its
    grounds' capabilities, which lies inside `Reach(L_t)`; disposal only removes.
    So `Reach(L_{t+1}) subset Reach(L_t)`. ∎

    A theorem about a **class** of permission relations, not a constraint on all
    of them. The naive subset rule for delegation wanted to be an axiom; it is
    this conditional, and a constitution that licenses widening simply declines
    the hypothesis. That is the whole difference between delegation and
    amendment.
    """
    if widening_edits(f, cap):
        return True                    # the hypothesis does not apply
    return not gained(f, cap)


def report(f: rp.Frame, cap: Callable) -> dict:
    return {
        "reach": reach_trace(f, cap),
        "gained": gained(f, cap),
        "widening": widening_edits(f, cap),
        "self_ratification": thm_no_jurisdictional_self_ratification(f),
        "mediated": thm_mediated_change(f, cap),
        "capability_available": capability_is_available(f, cap),
        "monotone_under_no_widening": thm_no_widening_gives_monotone_reach(f, cap),
    }


# ------------------------------------------- what the grounding tree follows


def tree_mentions(f: rp.Frame, o: rp.Occ) -> frozenset:
    """The occurrences a grounding tree names.

    Used to check that a fact the permission consulted does not become an
    ancestor: the recursion follows `grounds`, and a negative side condition is
    not a ground.
    """
    t = rp.tree(f, o)
    return frozenset() if t is None else _nodes(t)


def _nodes(t: rp.Tree) -> frozenset:
    out = frozenset({t.occ})
    for k in t.children:
        out |= _nodes(k)
    return out
