"""The objection grammar: named record tables and footprint-typed judges.

Per decision D2 an objection type declares no family.  It declares a **judge
footprint**: the record tables its judge may read, with standard-supplying book
content and evidence tables listed separately.  The verifier enforces the
declaration — a judge that reads an undeclared table fails the check.  Families,
where useful for reporting, are computed equivalence classes of footprints and
are never stored.

Finiteness discipline.  The table registry is a fixed finite set; every
objection type declares a finite footprint over it; grounds carry a finite
disposition-reference depth bounded by an explicit cap; and every judge is a
total function of the finitely many tables it declares.  No unbounded live state
is introduced: an ablation or a judgement allocates nothing that grows with date.

All arithmetic exposed by this module is exact.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Callable, Iterable, Mapping, Sequence


class TableKind(str, Enum):
    """A table either supplies the standard a judge applies, or is evidence."""

    STANDARD = "standard"
    EVIDENCE = "evidence"


@dataclass(frozen=True)
class TableSpec:
    name: str
    kind: TableKind
    description: str


# The registry of named record tables.  Fixed and finite.
REGISTRY: tuple[TableSpec, ...] = (
    TableSpec("book.endorsements", TableKind.STANDARD,
              "active endorsements and their compiled bounds"),
    TableSpec("book.declared_rates", TableKind.STANDARD,
              "rate bounds the book declares as its own standard"),
    TableSpec("schedule.procedure", TableKind.STANDARD,
              "frozen procedural schedules: thresholds, fallbacks, tariffs"),
    TableSpec("settled.record", TableKind.EVIDENCE,
              "the settled empirical and logical record"),
    TableSpec("rulings", TableKind.EVIDENCE, "issued rulings and their bases"),
    TableSpec("ledger.obligations", TableKind.EVIDENCE,
              "answerability-ledger obligations and their closures"),
    TableSpec("ledger.coverage", TableKind.EVIDENCE,
              "response-coverage edges and their adequacy certificates"),
    TableSpec("liabilities", TableKind.EVIDENCE, "accrued tariffs and charges"),
    TableSpec("region", TableKind.EVIDENCE,
              "the computed feasible set and its infeasibility certificates"),
    TableSpec("arrivals", TableKind.EVIDENCE, "the admitted case stream"),
    TableSpec("settlement.requests", TableKind.EVIDENCE,
              "funded settlement requests, their keys and their blackout windows"),
    TableSpec("settlement.pins", TableKind.EVIDENCE,
              "the settled record's pins and the funding profile recorded per pin"),
    TableSpec("positions", TableKind.EVIDENCE,
              "positions actors took on targets, by date"),
)

_BY_NAME = {spec.name: spec for spec in REGISTRY}
DEFAULT_DEPTH_CAP = 2


@dataclass(frozen=True)
class JudgeFootprint:
    """The read-set a judge is permitted, split by table kind."""

    standard_tables: tuple[str, ...] = ()
    evidence_tables: tuple[str, ...] = ()

    @property
    def declared(self) -> frozenset[str]:
        return frozenset(self.standard_tables) | frozenset(self.evidence_tables)

    def kind_of(self, name: str) -> TableKind | None:
        if name in self.standard_tables:
            return TableKind.STANDARD
        if name in self.evidence_tables:
            return TableKind.EVIDENCE
        return None


@dataclass(frozen=True)
class Grounds:
    """What is filed.  `disposition_refs` is what the depth cap attaches to."""

    grounds_id: str
    payload: Mapping[str, object]
    disposition_refs: tuple[str, ...] = ()
    depth: int = 0


@dataclass(frozen=True)
class ObjectionType:
    """An objection-shaped object on the footprint interface.

    `legacy_family` is recorded only so `GR-J2` can exhibit the computed
    classification against the pre-D2 scheme.  Nothing reads it as content.
    """

    type_id: str
    footprint: JudgeFootprint
    judge: Callable[["RecordAccess", Grounds], bool]
    references_dispositions: bool = False
    legacy_family: str | None = None
    origin: str = "downstream"


class RecordAccess:
    """A reader that records every table it is asked for."""

    def __init__(self, tables: Mapping[str, object]) -> None:
        self._tables = dict(tables)
        self._accessed: list[str] = []

    def read(self, name: str) -> object:
        if name not in self._accessed:
            self._accessed.append(name)
        return self._tables.get(name)

    def available(self, name: str) -> bool:
        """Membership test.  Counts as a read: knowing a table is absent is a read."""
        if name not in self._accessed:
            self._accessed.append(name)
        return name in self._tables

    @property
    def accessed(self) -> tuple[str, ...]:
        return tuple(self._accessed)


@dataclass(frozen=True)
class GrammarObstruction:
    code: str
    type_id: str
    tables: tuple[str, ...]
    detail: str


@dataclass(frozen=True)
class JudgeVerdict:
    type_id: str
    accepted: bool
    upheld: bool | None
    accessed: tuple[str, ...]
    obstructions: tuple[GrammarObstruction, ...]
    unused_declarations: tuple[str, ...]


def _obstruct(store: list[GrammarObstruction], code: str, type_id: str,
              tables: Iterable[str], detail: str) -> None:
    store.append(GrammarObstruction(code, type_id, tuple(sorted(tables)), detail))


def check_footprint(objection: ObjectionType) -> tuple[GrammarObstruction, ...]:
    """Static check: the declaration names registered tables of the right kind."""
    obstructions: list[GrammarObstruction] = []
    for name in sorted(objection.footprint.declared):
        spec = _BY_NAME.get(name)
        if spec is None:
            _obstruct(obstructions, "grammar.unknown_table", objection.type_id, (name,),
                      "the footprint names a table that is not registered")
            continue
        declared_kind = objection.footprint.kind_of(name)
        if declared_kind is not spec.kind:
            _obstruct(obstructions, "grammar.kind_mismatch", objection.type_id, (name,),
                      f"table {name!r} is registered {spec.kind.value} but declared "
                      f"{declared_kind.value if declared_kind else 'nothing'}")
    overlap = set(objection.footprint.standard_tables) & set(
        objection.footprint.evidence_tables)
    if overlap:
        _obstruct(obstructions, "grammar.kind_mismatch", objection.type_id, overlap,
                  "a table is declared both standard-supplying and evidence")
    return tuple(obstructions)


def judge_objection(objection: ObjectionType, tables: Mapping[str, object],
                    grounds: Grounds, *,
                    depth_cap: int = DEFAULT_DEPTH_CAP) -> JudgeVerdict:
    """Run a judge under its declared footprint and enforce the declaration."""
    obstructions = list(check_footprint(objection))
    if objection.references_dispositions and grounds.depth > depth_cap:
        _obstruct(obstructions, "grammar.depth_cap_exceeded", objection.type_id, (),
                  f"grounds reference dispositions at depth {grounds.depth} "
                  f"above the cap {depth_cap}")
    if grounds.disposition_refs and not objection.references_dispositions:
        _obstruct(obstructions, "grammar.undeclared_disposition_reference",
                  objection.type_id, (),
                  "grounds reference dispositions but the type does not declare it")
    access = RecordAccess(tables)
    upheld: bool | None = None
    try:
        upheld = bool(objection.judge(access, grounds))
    except Exception as error:  # a judge that cannot run is not a judge that passed
        _obstruct(obstructions, "grammar.judge_failed", objection.type_id, (),
                  f"the judge raised {type(error).__name__}: {error}")
    undeclared = [name for name in access.accessed
                  if name not in objection.footprint.declared]
    if undeclared:
        _obstruct(obstructions, "grammar.undeclared_table_read", objection.type_id,
                  undeclared,
                  "the judge read a table outside its declared footprint")
    unused = tuple(sorted(objection.footprint.declared - set(access.accessed)))
    accepted = not obstructions
    return JudgeVerdict(objection.type_id, accepted,
                        upheld if accepted else None, access.accessed,
                        tuple(obstructions), unused)


# --------------------------------------------------------------------------
# Computed classification (never stored)
# --------------------------------------------------------------------------


def footprint_classes(catalog: Sequence[ObjectionType],
                      ) -> Mapping[frozenset[str], tuple[str, ...]]:
    """Equivalence classes of full footprints."""
    classes: dict[frozenset[str], list[str]] = {}
    for objection in catalog:
        classes.setdefault(objection.footprint.declared, []).append(objection.type_id)
    return {key: tuple(sorted(value)) for key, value in sorted(
        classes.items(), key=lambda item: sorted(item[0]))}


def evidence_projection_classes(catalog: Sequence[ObjectionType],
                                ) -> Mapping[frozenset[str], tuple[str, ...]]:
    """Equivalence classes of the evidence-table projection only."""
    classes: dict[frozenset[str], list[str]] = {}
    for objection in catalog:
        classes.setdefault(frozenset(objection.footprint.evidence_tables),
                           []).append(objection.type_id)
    return {key: tuple(sorted(value)) for key, value in sorted(
        classes.items(), key=lambda item: sorted(item[0]))}


def legacy_classes(catalog: Sequence[ObjectionType]) -> Mapping[str, tuple[str, ...]]:
    classes: dict[str, list[str]] = {}
    for objection in catalog:
        if objection.legacy_family is not None:
            classes.setdefault(objection.legacy_family, []).append(objection.type_id)
    return {key: tuple(sorted(value)) for key, value in sorted(classes.items())}


def _partition(classes: Mapping[object, tuple[str, ...]]) -> frozenset[frozenset[str]]:
    return frozenset(frozenset(members) for members in classes.values())


def classification_agrees(left: Mapping[object, tuple[str, ...]],
                          right: Mapping[object, tuple[str, ...]]) -> bool:
    return _partition(left) == _partition(right)


def splits_against_legacy(catalog: Sequence[ObjectionType]) -> tuple[tuple[str, ...], ...]:
    """Legacy families the computed footprint classification splits."""
    computed = _partition(footprint_classes(catalog))
    split: list[tuple[str, ...]] = []
    for members in legacy_classes(catalog).values():
        block = frozenset(members)
        if block not in computed and len(block) > 1:
            split.append(tuple(sorted(block)))
    return tuple(split)


# --------------------------------------------------------------------------
# Per-table ablation (GR-N1)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class AblationResult:
    removed_table: str
    still_accepted: tuple[str, ...]
    became_unavailable: tuple[str, ...]
    verdict_changed: tuple[str, ...]


def ablate_table(catalog: Sequence[ObjectionType], tables: Mapping[str, object],
                 grounds: Mapping[str, Grounds], removed: str) -> AblationResult:
    """Drop one table and report which objections lose their judgement."""
    reduced = {name: value for name, value in tables.items() if name != removed}
    accepted, unavailable, changed = [], [], []
    for objection in catalog:
        payload = grounds.get(objection.type_id)
        if payload is None:
            continue
        before = judge_objection(objection, tables, payload)
        after = judge_objection(objection, reduced, payload)
        if removed in objection.footprint.declared:
            unavailable.append(objection.type_id)
            if before.upheld != after.upheld:
                changed.append(objection.type_id)
        elif after.accepted:
            accepted.append(objection.type_id)
    return AblationResult(removed, tuple(sorted(accepted)), tuple(sorted(unavailable)),
                          tuple(sorted(changed)))


# --------------------------------------------------------------------------
# The retrofitted catalog
#
# Upstream catalog types keep their frozen bytes; they receive declared
# footprints here, sourced from the theory files named in GRAMMAR.md's mapping
# table.  The three types introduced this round are born on the interface.
# --------------------------------------------------------------------------


def _frequency_judge(access: RecordAccess, grounds: Grounds) -> bool:
    bound = (access.read("book.endorsements") or {}).get(grounds.payload["bound_id"])
    observed = (access.read("settled.record") or {}).get(grounds.payload["target"])
    return bound is not None and observed is not None and observed < bound


def _calibration_judge(access: RecordAccess, grounds: Grounds) -> bool:
    book = access.read("book.endorsements") or {}
    settled = access.read("settled.record") or {}
    return any(settled.get(key, key) != value for key, value in book.items())


def _exposure_judge(access: RecordAccess, grounds: Grounds) -> bool:
    region = access.read("region") or {}
    return bool(region.get("infeasible"))


def _address_judge(access: RecordAccess, grounds: Grounds) -> bool:
    book = access.read("book.endorsements") or {}
    return book.get(grounds.payload["bound_id"]) is not None


def _coverage_judge(access: RecordAccess, grounds: Grounds) -> bool:
    coverage = access.read("ledger.coverage") or {}
    obligations = access.read("ledger.obligations") or {}
    return any(o not in coverage for o in obligations)


def _persistence_judge(access: RecordAccess, grounds: Grounds) -> bool:
    obligations = access.read("ledger.obligations") or {}
    return any(state == "open" for state in obligations.values())


def sure_loss_judge(access: RecordAccess, grounds: Grounds) -> bool:
    """CD-L3.  Footprint is the book itself: infeasibility is a property of it."""
    book = access.read("book.endorsements") or {}
    return bool(grounds.payload.get("farkas")) and bool(book)


def merits_evasion_judge(access: RecordAccess, grounds: Grounds) -> bool:
    """CD-L5.  A ruling with basis default while its bound interval cleared tau."""
    rulings = access.read("rulings") or {}
    schedules = access.read("schedule.procedure") or {}
    ruling = rulings.get(grounds.payload["ruling_id"])
    if ruling is None:
        return False
    schedule = schedules.get(ruling["schedule_version"])
    if schedule is None:
        return False
    return ruling["basis"] == "default" and bool(grounds.payload["cleared"])


def cross_subsidy_judge(access: RecordAccess, grounds: Grounds) -> bool:
    """T6.  A transfer crossing a declared fence, judged from the liability record."""
    liabilities = access.read("liabilities") or {}
    return (bool(grounds.payload.get("fence_id"))
            and grounds.payload["transfer_id"] in liabilities)


def aggregate_default_judge(access: RecordAccess, grounds: Grounds) -> bool:
    """CS-J4.  The computed rate against the book's own declared bound."""
    declared = access.read("book.declared_rates") or {}
    rulings = access.read("rulings") or {}
    bound = declared.get("default_resolution_rate")
    window = grounds.payload["window"]
    inside = [r for r in rulings.values() if window[0] <= r["date"] <= window[1]]
    if bound is None or not inside:
        return False
    weighted = sum(r["stakes"] for r in inside if r["basis"] == "default")
    total = sum(r["stakes"] for r in inside)
    return total > 0 and weighted * bound[1] > bound[0] * total


def probe_blackout_judge(access: RecordAccess, grounds: Grounds) -> bool:
    """The funder took a fresh position on its own request's target, in the window.

    The insider pattern of the conduct machinery, on the settlement surface.
    Its footprint is the request record and the position record: the judge never
    reads the book, because whether the funder was right is not the question.
    """
    requests = access.read("settlement.requests") or {}
    positions = access.read("positions") or {}
    request = requests.get(grounds.payload["request_id"])
    if request is None:
        return False
    start, end = grounds.payload["window"]
    if (request["funder_id"] != grounds.payload["funder_id"]
            or request["target"] != grounds.payload["target"]):
        return False
    return any(entry["actor_id"] == request["funder_id"]
               and entry["target"] == request["target"]
               and entry.get("fresh", True) and start <= entry["date"] <= end
               for entry in positions.values())


def common_source_judge(access: RecordAccess, grounds: Grounds) -> bool:
    """One purse bankrolled every premise pin of one conclusion.

    Recorded provenance is what makes the pattern visible at all; the judge
    checks that each named funder really appears in every premise's profile.
    """
    pins = access.read("settlement.pins") or {}
    premises = grounds.payload["premises"]
    shared = grounds.payload["common_funders"]
    if not premises or not shared:
        return False
    for premise in premises:
        pin = pins.get(premise)
        if pin is None:
            return False
        if not set(shared) <= set(pin.get("funder_profile", ())):
            return False
    return True


CATALOG: tuple[ObjectionType, ...] = (
    ObjectionType("frequency", JudgeFootprint(("book.endorsements",),
                                              ("settled.record",)),
                  _frequency_judge, legacy_family="calibration", origin="upstream"),
    ObjectionType("calibration", JudgeFootprint(("book.endorsements",),
                                                ("settled.record",)),
                  _calibration_judge, legacy_family="calibration", origin="upstream"),
    ObjectionType("exposure", JudgeFootprint((), ("region",)),
                  _exposure_judge, legacy_family="coherence", origin="upstream"),
    ObjectionType("address", JudgeFootprint(("book.endorsements",), ()),
                  _address_judge, references_dispositions=True,
                  legacy_family="repair", origin="upstream"),
    ObjectionType("coverage", JudgeFootprint((), ("ledger.coverage",
                                                  "ledger.obligations")),
                  _coverage_judge, legacy_family="repair", origin="upstream"),
    ObjectionType("persistence", JudgeFootprint((), ("ledger.obligations",)),
                  _persistence_judge, legacy_family="answerability", origin="upstream"),
    ObjectionType("sure-loss", JudgeFootprint(("book.endorsements",), ()),
                  sure_loss_judge, legacy_family="coherence"),
    ObjectionType("merits-evasion", JudgeFootprint(("schedule.procedure",), ("rulings",)),
                  merits_evasion_judge, legacy_family="answerability"),
    ObjectionType("aggregate-default", JudgeFootprint(("book.declared_rates",),
                                                      ("rulings",)),
                  aggregate_default_judge, legacy_family="answerability"),
    ObjectionType("cross-subsidy", JudgeFootprint((), ("liabilities",)),
                  cross_subsidy_judge, legacy_family="coherence"),
    ObjectionType("probe-blackout",
                  JudgeFootprint((), ("settlement.requests", "positions")),
                  probe_blackout_judge, legacy_family="answerability"),
    ObjectionType("common-source", JudgeFootprint((), ("settlement.pins",)),
                  common_source_judge, legacy_family="calibration"),
)

CATALOG_BY_ID = {objection.type_id: objection for objection in CATALOG}
