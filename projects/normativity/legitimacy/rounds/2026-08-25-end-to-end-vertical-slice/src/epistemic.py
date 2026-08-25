"""The epistemic substrate: what the record settles, and which worlds survive.

`DeductiveProcess` in the pinned dependency is two fields — `D : N -> Finset
Sentence` and `mono : D n subset D (n+1)` — and `ConsistentWith v D` is
`forall phi in D, v.Holds phi`. Nothing requires `D n` to be deductively
closed, to be a theory, to be consistent, or to have come from a proof search.
So a stage is a finite monotone stream of sentences, and any source that emits
one is a legal source.

That is what lets the settlement ledger feed the same slot the deductive
process feeds:

    Sigma_n = D_n  union  Sem_L(L_n)
    W_n     = PC(Sigma_n)

`sem_L` is the round's third parametric interpreter, in the shape Reflective
Integrity already uses twice for `[[.]]_S` and `[[.]]_D`. Its assumptions:

**E1 — rigidity.** `sem_L` is a function of the settlement's identity alone. It
reads no reason, no standing, no normative event, and no later settlement. This
is what keeps normative interpretation out of the world semantics, and it is
what makes an old settlement's denotation survive every later change.

**E2 — finiteness.** `sem_L(l)` is a finite set of sentences. The empty set is
admissible and is how an entry with no exact market-facing content is
represented: it constrains no world.

**E3 — computability.** `n |-> Sigma_n` is computable. This is what
`IsLogicalInductor` needs of the process it is stated against, and it is the
reason a raw observation is admitted through a certified reading rather than
directly.

**Monotonicity is a theorem, not an assumption.** The ledger is append-only and
`sem_L` is per-entry and rigid, so `Sigma_n subset Sigma_{n+1}` follows. A
settlement that could be retracted would break `DeductiveProcess.mono`, and
there would then be no object of that type to hand a trader.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable, Mapping, Sequence

from li import ONE, ZERO, atoms_of, consistent_with, holds, worlds_over


@dataclass(frozen=True)
class StageEntry:
    """One sentence in the stage, with the source that put it there.

    `source` is provenance and has no semantic role: `ConsistentWith` reads the
    sentence and nothing else. It is carried so that an infeasibility can be
    attributed, and so that the deductive and settled channels stay
    distinguishable in a trace after they have been unioned.
    """

    sentence: object
    source: str                 # "deductive" | a settlement id
    note: str = ""


class RawOutcome:
    """An environment observation, before any exact reading of it.

    A raw outcome is not a settlement and never reaches the ledger. It is the
    thing an ambiguous observation is, and holding the distinction is what stops
    an ambiguous observation from eliminating worlds.
    """

    __slots__ = ("id", "content")

    def __init__(self, oid: str, content: object) -> None:
        self.id = oid
        self.content = content

    def __repr__(self) -> str:
        return f"RawOutcome({self.id!r})"


@dataclass(frozen=True)
class SettlementReading:
    """A certified reading of a raw outcome: the entry's LI-facing denotation.

    This is `sem_L` at one settlement, frozen at admission. `sentences` empty is
    the non-exposure state — the entry is in the ledger with its provenance and
    constrains no world. It is the exact counterpart of a value query that
    compiles to no LUV.
    """

    settle_id: str
    of_outcome: str
    sentences: tuple = ()
    note: str = ""
    #: `(outcome_id, action, receipt_index)`, frozen with the reading, or
    #: `None` for a settlement that did not arise from a designated action.
    #:
    #: **The narrow provenance seam.** `sem_L` does not read this and neither
    #: does any world; `PC(Sigma_n)` is a function of the sentences alone. It
    #: exists so that a *service* judge can tell "this was settled" from "this
    #: was settled by the designated procedure" without the epistemic substrate
    #: acquiring an opinion about actions. Frozen at admission like the rest of
    #: the reading, so procedural provenance is as rigid as denotation.
    provenance: object = None

    @property
    def exposes(self) -> bool:
        return bool(self.sentences)


class SettlementSemantics:
    """`sem_L`, as a registry keyed by settlement id.

    Append-only and write-once. Re-reading an entry is refused rather than
    overwritten: that refusal is E1 made operational, and it is the mechanism
    by which an old settlement's denotation stays rigid under later language
    growth.
    """

    def __init__(self) -> None:
        self._readings: dict = {}
        self._order: list = []

    def admit(self, reading: SettlementReading) -> SettlementReading:
        if reading.settle_id in self._readings:
            raise ValueError(
                f"settlement {reading.settle_id} already carries a reading; "
                "E1 makes a denotation write-once")
        self._readings[reading.settle_id] = reading
        self._order.append(reading.settle_id)
        return reading

    def __contains__(self, settle_id: str) -> bool:
        return settle_id in self._readings

    def reading(self, settle_id: str) -> SettlementReading:
        return self._readings[settle_id]

    def sem(self, settle_id: str) -> tuple:
        """`sem_L(l)`. Total: an id with no admitted reading denotes nothing."""
        r = self._readings.get(settle_id)
        return () if r is None else tuple(r.sentences)

    def entries(self, settle_ids: Iterable[str]) -> tuple:
        out = []
        for sid in settle_ids:
            for phi in self.sem(sid):
                out.append(StageEntry(phi, sid, self._readings[sid].note))
        return tuple(out)


def deductive_entries(sentences: Iterable, note: str = "") -> tuple:
    return tuple(StageEntry(phi, "deductive", note) for phi in sentences)


@dataclass(frozen=True)
class Stage:
    """`Sigma_n`: the day-`n` stage, both channels unioned.

    Deduplicated on the sentence, keeping the first source that supplied it, so
    that the same fact settled twice is one stage member — which is what
    `Finset Sentence` already means on the other side.
    """

    entries: tuple

    @staticmethod
    def of(*groups: Iterable) -> "Stage":
        seen: dict = {}
        for group in groups:
            for e in group:
                if e.sentence not in seen:
                    seen[e.sentence] = e
        return Stage(tuple(seen.values()))

    def sentences(self) -> tuple:
        return tuple(e.sentence for e in self.entries)

    def atoms(self) -> frozenset:
        out = frozenset()
        for e in self.entries:
            out |= atoms_of(e.sentence)
        return out

    def by_source(self, source: str) -> tuple:
        return tuple(e for e in self.entries if e.source == source)

    def extends(self, earlier: "Stage") -> bool:
        """`DeductiveProcess.mono` between two days of the same trajectory."""
        return set(earlier.sentences()) <= set(self.sentences())


_WORLD_CACHE: dict = {}


def pc_worlds(stage: Stage, fragment: Sequence) -> list:
    """Worlds consistent with the stage, over the stage's and fragment's atoms.

    Enumerates `2^k` valuations of the atoms occurring in the stage or the
    fragment and keeps those satisfying every stage sentence. This is what
    `DeductiveRegion.admissiblePatterns` does in Lean, and the reason it
    enumerates over the union rather than over the fragment alone is that a
    fragment coordinate is a sentence, not an atom: two coordinates can
    constrain the same atom, and a `{0,1}` pattern can be unrealisable for that
    reason with no help from the stage.

    Memoized on the stage and fragment. The enumeration is exponential in the
    atom count and a day asks for it several times; the cache changes what it
    costs and not what it returns, since both arguments are immutable.
    """
    key = (stage.entries, tuple(fragment))
    hit = _WORLD_CACHE.get(key)
    if hit is not None:
        return hit
    names = set(stage.atoms())
    for phi in fragment:
        names |= atoms_of(phi)
    sentences = stage.sentences()
    out = [w for w in worlds_over(sorted(names))
           if consistent_with(w, sentences)]
    _WORLD_CACHE[key] = out
    return out


def admissible_patterns(stage: Stage, fragment: Sequence) -> list:
    """`admissiblePatterns`: the `{0,1}` price patterns the stage admits.

    One entry per distinct restriction to the fragment of a stage-consistent
    world. Sound and complete about worlds rather than about atom assignments.
    """
    seen = []
    for w in pc_worlds(stage, fragment):
        pattern = tuple(ONE if holds(w, phi) else ZERO for phi in fragment)
        if pattern not in seen:
            seen.append(pattern)
    return seen


def stage_satisfiable(stage: Stage) -> bool:
    """Whether any world is consistent with the stage.

    An unsatisfiable stage is not a type error on the other side: the pinned
    `isLogicalInductor_of_stage_unsatisfiable` says the criterion holds
    vacuously over a process with one, because every quantifier in it ranges
    over consistent worlds. So a contradictory ledger does not break the
    guarantees; it empties them, and nothing downstream notices unless this is
    checked.
    """
    return bool(pc_worlds(stage, ()))


def conflicting_sources(stage: Stage) -> tuple:
    """Minimal source sets whose stage entries admit no world.

    Returned smallest-first, so the first entry is the sharpest attribution
    available. Empty when the stage is satisfiable.
    """
    if stage_satisfiable(stage):
        return ()
    from itertools import combinations
    entries = list(stage.entries)
    for size in range(1, len(entries) + 1):
        hits = []
        for subset in combinations(entries, size):
            if not stage_satisfiable(Stage(tuple(subset))):
                hits.append(tuple(sorted({e.source for e in subset})))
        if hits:
            seen = []
            for h in hits:
                if h not in seen:
                    seen.append(h)
            return tuple(seen)
    return ()
