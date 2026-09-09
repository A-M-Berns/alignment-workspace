"""The declared reason trace `R_{n:m}`: the projection of a log prefix onto the admitted
kinds, as `(author, kind, content)` triples, grounds by content."""
from __future__ import annotations

from .log import ADMITTED, DISPOSE, REASON, ROUTE, SESSION_OPEN, SETTLE, WITHDRAW, _freeze


def trace_content(e, log):
    if e.kind == ROUTE:
        return (e.payload["concern"], e.payload["route"])
    if e.kind == SETTLE:
        return (e.payload["sentence"], e.payload.get("about"))
    if e.kind == DISPOSE:
        grounds = tuple((log[g].author, log[g].kind, trace_content(log[g], log)) for g in e.refs)
        return (e.payload, grounds)
    return _freeze(e.payload)


def reason_trace(log, upto):
    """The admitted events with index below `upto`, in order."""
    return tuple((e.author, e.kind, trace_content(e, log)) for e in log
                 if e.kind in ADMITTED and e.index < upto)


def session_trace(log, upto, slot):
    opened = None
    for e in log:
        if e.kind == SESSION_OPEN and e.payload == slot:
            opened = e.index
    if opened is None:
        return ()
    return tuple((e.author, e.kind, trace_content(e, log)) for e in log
                 if e.kind in ADMITTED and opened < e.index < upto)


def final_reason_state(log, upto):
    present = set()
    for e in log:
        if e.index >= upto:
            break
        if e.kind == REASON:
            present.add(e.payload)
        if e.kind == WITHDRAW:
            present.discard(e.payload)
    return frozenset(present)
