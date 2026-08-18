"""The protected object, defined by role.

A coordinate list is a bad definition of what an advisor may not capture. It has
no closure argument, it grows whenever an attack finds a field nobody listed, and
it cannot say why the fields on it belong together.

The object here is instead the **normative response function**: the answers the
process gives to the normative questions, over an alphabet.

```
what arises        encounter kind        -> substance, and whether it is due
what settles       substance             -> the witness the process would use
what may merge     pair of substances    -> may one liability absorb the other
what bears         content, coordinate   -> is this content a reason for that
```

Three consequences, and they are the reason for the change of definition.

*Closure by role.* A field belongs to the protected object exactly when changing
it changes an answer. The five coordinates are a **presentation** of the response
function, checked as such rather than asserted: a writable field answering
nothing is outside it, and the presentation is faithful only over an alphabet
covering the keys the process can use.

*Representation independence.* Renaming the alphabet renames the answers and
nothing else, so the object is equivariant rather than tied to the fixture's
strings.

*Time.* An advisor can capture a process and hand it back. The protected object
is therefore the response function **along the run**, one answer set per step;
its last element is the endpoint projection the first pass used.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import combinations
from typing import Mapping, Sequence

from fixture import (ADEQUACY, BEARING, ENTITLEMENT, GENERATION, IDENTIFICATION,
                     Fixture, Machinery, Run, WITNESS_ORDER, _first_adequate)

MACHINERY_KEYS = (GENERATION, ENTITLEMENT, BEARING, ADEQUACY, IDENTIFICATION)


@dataclass(frozen=True)
class Alphabet:
    """The questions that get asked.

    Not part of the process: an alphabet is what an auditor, a coupling relation
    or a downstream theorem quantifies over, and the faithfulness of the
    five-coordinate presentation is relative to it.
    """

    kinds: tuple[str, ...]
    substances: tuple[str, ...]
    contents: tuple[str, ...]
    coordinates: tuple[str, ...] = MACHINERY_KEYS
    #: The process's closure tie-break, which is part of what it answers to
    #: "what settles this" and therefore renames with the alphabet.
    order: tuple[str, ...] = WITNESS_ORDER


def alphabet_of(fixture: Fixture, extra_substances: Sequence[str] = ()) -> Alphabet:
    """Every key the fixture's process can actually use.

    Derived rather than declared, so a scenario cannot quietly narrow the
    questions until its own attack stops being asked.
    """
    machinery = fixture.machinery
    kinds = set(machinery.generation) | {e.kind for e in fixture.encounters}
    substances = set(machinery.generation.values()) | set(machinery.entitlement)
    substances |= set(extra_substances)
    for witness in machinery.adequacy.values():
        substances |= set(witness)
    contents = set(machinery.bearing) | {g.content for g in
                                        fixture.grounds.grounds}
    coordinates = set(MACHINERY_KEYS)
    for licensed in machinery.bearing.values():
        coordinates |= set(licensed)
    for ground in fixture.grounds.grounds:
        coordinates |= set(ground.scope)
    return Alphabet(tuple(sorted(kinds)), tuple(sorted(substances)),
                    tuple(sorted(contents)), tuple(sorted(coordinates)))


def _settling(machinery: Machinery, substance: str,
              order: Sequence[str]) -> str | None:
    for witness in order:
        if substance in machinery.adequacy.get(witness, frozenset()):
            return witness
    return None


def response(machinery: Machinery, alphabet: Alphabet) -> tuple:
    """What the process answers. The protected object's one-step form."""
    arises = tuple(
        (kind, machinery.generation.get(kind),
         machinery.generation.get(kind) in machinery.entitlement)
        for kind in alphabet.kinds)
    settles = tuple((substance, _settling(machinery, substance, alphabet.order))
                    for substance in alphabet.substances)
    licences = tuple(sorted(machinery.identification))
    merges = tuple((first, second, bool(licences))
                   for first, second in combinations(alphabet.substances, 2))
    bears = tuple((content, coordinate,
                   coordinate in machinery.bearing.get(content, frozenset()))
                  for content in alphabet.contents
                  for coordinate in alphabet.coordinates)
    return (arises, settles, merges, bears)


def protected_process(run: Run, alphabet: Alphabet) -> tuple:
    """`Z_{0:T}` — the answers at every step.

    A capture that is undone before the horizon changes this and does not change
    its last element, which is the whole reason the object is a sequence.
    """
    return tuple(response(machinery, alphabet) for machinery in run.states)


def protected_endpoint(run: Run, alphabet: Alphabet) -> tuple:
    return response(run.states[-1], alphabet)


def presentation(machinery: Machinery) -> tuple:
    """The five coordinates, frozen — the first pass's projection."""
    return tuple((key, _freeze(machinery.get(key))) for key in MACHINERY_KEYS)


def writable_fields(machinery: Machinery) -> tuple:
    """Every mutable field, including the one no question reads.

    The naive protected object, kept so a test can show it is the wrong one.
    """
    from fixture import MACHINERY_ALL
    return tuple((key, _freeze(machinery.get(key))) for key in MACHINERY_ALL)


def _freeze(value):
    if isinstance(value, frozenset):
        return tuple(sorted(value))
    return tuple(sorted((k, tuple(sorted(v)) if isinstance(v, frozenset) else v)
                        for k, v in value.items()))


# --------------------------------------------------------------------------
# Renaming
# --------------------------------------------------------------------------

def rename_machinery(machinery: Machinery, mapping: Mapping[str, str]) -> Machinery:
    def name(value):
        return mapping.get(value, value)
    return replace(
        machinery,
        generation={name(k): name(v) for k, v in machinery.generation.items()},
        entitlement=frozenset(name(s) for s in machinery.entitlement),
        bearing={name(c): frozenset(machinery.bearing[c])
                 for c in machinery.bearing},
        adequacy={name(w): frozenset(name(s) for s in machinery.adequacy[w])
                  for w in machinery.adequacy},
        identification=frozenset(name(t) for t in machinery.identification))


def rename_alphabet(alphabet: Alphabet, mapping: Mapping[str, str]) -> Alphabet:
    def name(value):
        return mapping.get(value, value)
    return Alphabet(tuple(name(k) for k in alphabet.kinds),
                    tuple(name(s) for s in alphabet.substances),
                    tuple(name(c) for c in alphabet.contents),
                    alphabet.coordinates,
                    tuple(name(w) for w in alphabet.order))


def rename_response(answers: tuple, mapping: Mapping[str, str]) -> tuple:
    def name(value):
        return mapping.get(value, value) if isinstance(value, str) else value
    arises, settles, merges, bears = answers
    return (tuple((name(k), name(s), due) for k, s, due in arises),
            tuple((name(s), name(w)) for s, w in settles),
            tuple((name(a), name(b), ok) for a, b, ok in merges),
            tuple((name(c), x, ok) for c, x, ok in bears))


# --------------------------------------------------------------------------
# Non-capture over the role-defined object
# --------------------------------------------------------------------------

def process_projection(alphabet: Alphabet):
    """A `protected=` argument for `noncapture.non_capture`."""
    return lambda run: protected_process(run, alphabet)


def endpoint_projection(alphabet: Alphabet):
    return lambda run: protected_endpoint(run, alphabet)


def witnesses_off_alphabet(machinery: Machinery, kind: str,
                           substance: str) -> tuple[Machinery, Machinery]:
    """Two machineries the five-coordinate presentation separates and no
    question does: they differ on a generation key nothing ever encounters.

    The presentation is finer than the object it presents, so a condition stated
    over the coordinate list forbids changes that alter nothing the process
    answers.
    """
    first = replace(machinery,
                    generation={**machinery.generation, kind: substance})
    second = replace(machinery, generation=dict(machinery.generation))
    return first, second
