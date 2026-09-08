"""Exact finite model of the three-fate account calculus, as far as activation reads it.

An account is a tree: a leaf is `live` (at a port), `answered` (with the event
whose payload is the value vector) or `closed` (with a settlement item); an
internal node is a local law over children.  `activated` is `fates == {answered}`
as a multiset; `subst` replaces live leaves only, mirroring
`OccurrenceIntegrity.Program.subst`.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Optional, Tuple


@dataclass(frozen=True)
class Leaf:
    fate: str  # "live" | "answered" | "closed"
    port: Optional[int] = None
    event: Optional[int] = None


@dataclass(frozen=True)
class Law:
    children: Tuple
    label: str = "carry"


def fates(t) -> Counter:
    if isinstance(t, Leaf):
        return Counter({t.fate: 1})
    c = Counter()
    for ch in t.children:
        c += fates(ch)
    return c


def live_ports(t):
    if isinstance(t, Leaf):
        return [t.port] if t.fate == "live" else []
    out = []
    for ch in t.children:
        out += live_ports(ch)
    return out


def activated(t) -> bool:
    return fates(t) == Counter({"answered": 1})


def answer_event(t):
    """The event of the unique answer receipt of an activated account."""
    assert activated(t)
    if isinstance(t, Leaf):
        return t.event
    for ch in t.children:
        if fates(ch)["answered"] == 1:
            return answer_event(ch)
    raise AssertionError


def subst(t, replacement: dict):
    """Replace each live leaf at port p by replacement[p]; receipts are carried unchanged."""
    if isinstance(t, Leaf):
        return replacement[t.port] if t.fate == "live" else t
    return Law(tuple(subst(ch, replacement) for ch in t.children), t.label)


def activation(history_payloads: dict, t):
    """`(C, V)`: activation bit and, when activated, the payload read from the
    authenticated history at the receipt's event."""
    if not activated(t):
        return 0, None
    return 1, history_payloads[answer_event(t)]
