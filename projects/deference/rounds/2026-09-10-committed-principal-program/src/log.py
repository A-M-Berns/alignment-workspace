"""The authenticated append-only event log (E1), extended by the committed-principal-program
round: `REVOKE`, `REQUEST`, `JAM` kinds; the mandate carries the principal's program and
the commit carries its process receipt (see `ecosystem.py`).

An event carries an author key, its index (its position in the log), a kind, a typed
payload, an optional warrant, and references to earlier events where the theory needs
grounds.  The log is a list; a prefix is a list slice.

**The model's one authentication assumption.**  The `author` field of every event is
authentic: the party named produced the event, and no party can append an event under
another party's key.  Every "authenticated" fact below (receipt authenticity, payload
authenticity, principal-exclusive binding) is this assumption read at one event; none
of them is derived from anything else, and nothing else in the model authenticates.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional, Tuple

# Parties.  `P` the principal, `A` the advisor, `T` a third party who raises concerns,
# `S` the system: sessions, the route registrar / scheduler, the settlement engine.
P, A, T, S = "P", "A", "T", "S"

# Event kinds.
ISSUE = "ISSUE"                  # evaluation mandate; anchors the occurrence
SESSION_OPEN = "SESSION_OPEN"    # the designated slot opens
SESSION_CLOSE = "SESSION_CLOSE"
REASON = "REASON"                # advisor reason (proof, argument, report)
WITHDRAW = "WITHDRAW"            # advisor withdraws a reason
DELIB = "DELIB"                  # principal deliberation event
RAISE = "RAISE"                  # a concern is raised (enters the docket)
ROUTE_OPEN = "ROUTE_OPEN"        # a route for concerns is registered
ROUTE_DESTROY = "ROUTE_DESTROY"
ROUTE = "ROUTE"                  # route exercise: the concern is represented
DISPOSE = "DISPOSE"              # a concern is disposed of with grounds
SETTLE = "SETTLE"                # a settlement write
COMMIT = "COMMIT"                # the commitment event carrying (V, key, proc)
CLOSE = "CLOSE"                  # closure of the occurrence by settlement
DELEGATE = "DELEGATE"            # the binding warrant is extended to a second party/key
REVOKE = "REVOKE"                # a delegation is withdrawn
REQUEST = "REQUEST"              # a party asks the engine to settle a sentence
JAM = "JAM"                      # an intervention on the route registrar (declared class J)
MARKET = "MARKET"                # the market publishes the advisor's selection
DIRECT_WRITE = "DIRECT_WRITE"    # prohibited: a write to the principal's disposition
COERCE = "COERCE"                # prohibited: a coercive move
SIDE = "SIDE"                    # prohibited: a side channel outside the reason interface

# The declared prohibited class `P` of event kinds (E4).
PROHIBITED = frozenset({DIRECT_WRITE, COERCE, SIDE})

# The declared intervention kinds of the openness class `J`: acts on the infrastructure
# whose counterfactual effect Robust Openness must survive.
INTERVENTIONS = frozenset({JAM})

# The declared admitted-deliberative-input kinds: the reason trace `R` keeps exactly
# these (E4).  `COMMIT`, sessions, warrants and route registration are not reasons.
ADMITTED = frozenset({REASON, WITHDRAW, DELIB, RAISE, ROUTE, DISPOSE, SETTLE})

# Warrants.
BIND = "bind:P"      # the principal role's binding warrant
CLOSE_W = "close:S"  # the settlement engine's closure warrant
DISPOSE_W = "dispose:P"


@dataclass(frozen=True)
class Event:
    index: int
    time: int
    author: str
    kind: str
    payload: Any = None
    warrant: Optional[str] = None
    refs: Tuple[int, ...] = ()


class Log:
    """Append-only.  `prefix(k)` is the first `k` events; `history(k)` the index list."""

    def __init__(self, events=None):
        self.events = list(events or [])

    def append(self, time, author, kind, payload=None, warrant=None, refs=()):
        e = Event(len(self.events), time, author, kind, payload, warrant, tuple(refs))
        self.events.append(e)
        return e

    def __len__(self):
        return len(self.events)

    def __iter__(self):
        return iter(self.events)

    def __getitem__(self, i):
        return self.events[i]

    def prefix(self, k):
        return Log(self.events[:k])

    def history(self, k=None):
        n = len(self.events) if k is None else k
        return list(range(n))

    def kinds(self):
        return [e.kind for e in self.events]

    def first(self, pred):
        for e in self.events:
            if pred(e):
                return e
        return None

    def all(self, pred):
        return [e for e in self.events if pred(e)]

    def signature(self):
        """Canonical hashable form (payloads must be hashable)."""
        return tuple((e.time, e.author, e.kind, _freeze(e.payload), e.warrant, e.refs)
                     for e in self.events)


def _freeze(x):
    if isinstance(x, dict):
        return tuple(sorted((k, _freeze(v)) for k, v in x.items()))
    if isinstance(x, (list, tuple)):
        return tuple(_freeze(v) for v in x)
    if isinstance(x, (set, frozenset)):
        return tuple(sorted(_freeze(v) for v in x))
    return x
