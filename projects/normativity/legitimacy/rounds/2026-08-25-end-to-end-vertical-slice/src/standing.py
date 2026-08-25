"""How the two waists install into the frozen Reflective Integrity core.

Neither installation edits `ri_core.py`, and that is the substantive claim of
this file rather than an implementation convenience.

**The operative waist is not an extension.** `PForce (commitRef, schemaRef,
compiledClause : Clause)` is already a payload of the core, `Clause` is already
opaque, and `O_t` is already its projection. An injunction is a `Clause`. So
where the prompt for this round proposed a new `PInjunction` constructor, the
round uses `PForce` and declares the deviation: adding one would have duplicated
a payload that exists, and would have made `O_t` read two constructors where it
reads one.

`PForce`'s two reference fields are inert here. Compilation reads `clause` and
nothing else, so the justification an injunction carries is recovered through
its standing's own custody episode and the event that created it, not from the
payload.

**The value waist is a conservative extension.** `PValue` is a new payload
constructor, and Meta-Stability licenses exactly that: "a new constructor gets a
new clause, and every existing term keeps its clauses verbatim". It costs
nothing to the interpreter, because `delta`'s three clauses write `K_i` into a
fresh standing state without inspecting it — `Create` and `Supersede` are
payload-polymorphic — so no clause of `applyEffect` changes, no existing term
changes, and the core's tests are unaffected. The projection `Values_t` below is
the value-side counterpart of `O_t`, and like `O_t` it is a read of the fold.

A value specification is not a commitment and is deliberately not carried as
`PCmt`. `PCmt`'s `content` is object-level and opaque by the stratification of
§3, and a projection that had to inspect content to tell a value specification
from any other commitment would be reading object-level content at meta level.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from waist import Injunction


@dataclass(frozen=True)
class PValue:
    """Standing carrying a frozen historical value specification.

    `spec_id` is a code, not the specification: the specification lives in the
    append-only `ValueRegistry`, and standing says which one is in force. That
    split is what makes supersession of value standing cheap and makes an old
    quantity's meaning independent of it.
    """

    spec_id: str


def values_projection(std: dict) -> tuple:
    """`Values_n = {(i, v) : i is active standing carrying PValue(v)}`.

    Paired with the standing id for the same reason the operative projection is:
    two active specifications may be distinct standings, and which one an event
    superseded has to remain answerable.

    Several active value specifications are permitted. Nothing in the pipeline
    consults this projection — a compiled LUV names its specification directly —
    so plurality here costs the downstream layer nothing.
    """
    return tuple((x, state.payload.spec_id)
                 for x, state in sorted(std.items())
                 if state.kind == "Active" and isinstance(state.payload, PValue))


def injunction_standing(std: dict, standing_id: str) -> Injunction:
    """The injunction a standing carries, or a `KeyError`."""
    state = std[standing_id]
    clause = getattr(state.payload, "clause", None)
    if not isinstance(clause, Injunction):
        raise KeyError(f"{standing_id} carries no injunction")
    return clause
