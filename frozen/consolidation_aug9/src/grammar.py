"""The objection grammar: named record tables and footprint-typed judges.

Folder-local; readable against `THEORY_7` alone.

An objection type declares no family. It declares a **judge footprint**: the
record tables its judge may read, with standard-supplying content and evidence
tables listed separately. The verifier enforces the declaration -- a judge that
reads an undeclared table fails the check, and a judge that raises is recorded
as failing rather than passing. Families, where useful for reporting, are
computed equivalence classes of footprints and are never stored.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Callable, Iterable, Mapping, Sequence


class Kind(str, Enum):
    STANDARD = "standard"
    EVIDENCE = "evidence"


@dataclass(frozen=True)
class TableSpec:
    name: str
    kind: Kind
    description: str


REGISTRY: tuple[TableSpec, ...] = (
    TableSpec("book.endorsements", Kind.STANDARD,
              "active endorsements and their compiled constraints"),
    TableSpec("book.declared_rates", Kind.STANDARD,
              "rate limits the book declares as its own standard"),
    TableSpec("schedule.procedure", Kind.STANDARD,
              "frozen procedural schedules: thresholds, fallbacks, tariffs"),
    TableSpec("settled.record", Kind.EVIDENCE, "the settled empirical and logical record"),
    TableSpec("rulings", Kind.EVIDENCE, "issued rulings and their bases"),
    TableSpec("ledger.obligations", Kind.EVIDENCE,
              "answerability-ledger obligations and their closures"),
    TableSpec("ledger.coverage", Kind.EVIDENCE,
              "response-coverage edges and their adequacy certificates"),
    TableSpec("liabilities", Kind.EVIDENCE, "accrued tariffs and charges"),
    TableSpec("region", Kind.EVIDENCE,
              "the computed feasible set and its infeasibility certificates"),
    TableSpec("arrivals", Kind.EVIDENCE, "the admitted case stream"),
    TableSpec("settlement.requests", Kind.EVIDENCE,
              "funded settlement requests, their keys and their blackout windows"),
    TableSpec("settlement.record", Kind.EVIDENCE,
              "settlement events and the funding profile recorded per event"),
    TableSpec("positions", Kind.EVIDENCE, "positions actors took on targets, by date"),
)

BY_NAME = {spec.name: spec for spec in REGISTRY}
DEPTH_CAP = 2


@dataclass(frozen=True)
class Footprint:
    standard_tables: tuple[str, ...] = ()
    evidence_tables: tuple[str, ...] = ()

    @property
    def declared(self) -> frozenset[str]:
        return frozenset(self.standard_tables) | frozenset(self.evidence_tables)

    def kind_of(self, name: str) -> Kind | None:
        if name in self.standard_tables:
            return Kind.STANDARD
        if name in self.evidence_tables:
            return Kind.EVIDENCE
        return None


@dataclass(frozen=True)
class Grounds:
    grounds_id: str
    payload: Mapping[str, object]
    disposition_refs: tuple[str, ...] = ()
    depth: int = 0


@dataclass(frozen=True)
class ObjectionType:
    type_id: str
    footprint: Footprint
    judge: Callable[["Access", Grounds], bool]
    references_dispositions: bool = False
    legacy_family: str | None = None


class Access:
    """A reader that records every table it is asked for, including absences."""

    def __init__(self, tables: Mapping[str, object]) -> None:
        self._tables = dict(tables)
        self._log: list[str] = []

    def read(self, name: str) -> object:
        if name not in self._log:
            self._log.append(name)
        return self._tables.get(name)

    def available(self, name: str) -> bool:
        if name not in self._log:
            self._log.append(name)
        return name in self._tables

    @property
    def accessed(self) -> tuple[str, ...]:
        return tuple(self._log)


@dataclass(frozen=True)
class Obstruction:
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
    obstructions: tuple[Obstruction, ...]
    unused: tuple[str, ...]


def _obstruct(store: list[Obstruction], code: str, type_id: str,
              tables: Iterable[str], detail: str) -> None:
    store.append(Obstruction(code, type_id, tuple(sorted(tables)), detail))


def check_footprint(objection: ObjectionType) -> tuple[Obstruction, ...]:
    """Static check: the declaration names registered tables of the right kind."""
    out: list[Obstruction] = []
    for name in sorted(objection.footprint.declared):
        spec = BY_NAME.get(name)
        if spec is None:
            _obstruct(out, "grammar.unknown_table", objection.type_id, (name,),
                      "the footprint names an unregistered table")
            continue
        if objection.footprint.kind_of(name) is not spec.kind:
            _obstruct(out, "grammar.kind_mismatch", objection.type_id, (name,),
                      f"table {name!r} is registered {spec.kind.value}")
    overlap = set(objection.footprint.standard_tables) & set(
        objection.footprint.evidence_tables)
    if overlap:
        _obstruct(out, "grammar.kind_mismatch", objection.type_id, overlap,
                  "a table is declared both standard-supplying and evidence")
    return tuple(out)


def judge(objection: ObjectionType, tables: Mapping[str, object], grounds: Grounds,
          depth_cap: int = DEPTH_CAP) -> JudgeVerdict:
    """Run a judge under its declared footprint and enforce the declaration."""
    out = list(check_footprint(objection))
    if objection.references_dispositions and grounds.depth > depth_cap:
        _obstruct(out, "grammar.depth_cap_exceeded", objection.type_id, (),
                  f"grounds reference dispositions at depth {grounds.depth}")
    if grounds.disposition_refs and not objection.references_dispositions:
        _obstruct(out, "grammar.undeclared_disposition_reference", objection.type_id,
                  (), "grounds reference dispositions undeclared by the type")
    access = Access(tables)
    upheld: bool | None = None
    try:
        upheld = bool(objection.judge(access, grounds))
    except Exception as error:
        _obstruct(out, "grammar.judge_failed", objection.type_id, (),
                  f"the judge raised {type(error).__name__}: {error}")
    undeclared = [n for n in access.accessed if n not in objection.footprint.declared]
    if undeclared:
        _obstruct(out, "grammar.undeclared_table_read", objection.type_id, undeclared,
                  "the judge read a table outside its declared footprint")
    accepted = not out
    return JudgeVerdict(objection.type_id, accepted, upheld if accepted else None,
                        access.accessed, tuple(out),
                        tuple(sorted(objection.footprint.declared - set(access.accessed))))


def footprint_classes(catalog: Sequence[ObjectionType],
                      ) -> Mapping[frozenset[str], tuple[str, ...]]:
    classes: dict[frozenset[str], list[str]] = {}
    for o in catalog:
        classes.setdefault(o.footprint.declared, []).append(o.type_id)
    return {k: tuple(sorted(v)) for k, v in sorted(classes.items(),
                                                   key=lambda kv: sorted(kv[0]))}


def evidence_classes(catalog: Sequence[ObjectionType],
                     ) -> Mapping[frozenset[str], tuple[str, ...]]:
    classes: dict[frozenset[str], list[str]] = {}
    for o in catalog:
        classes.setdefault(frozenset(o.footprint.evidence_tables), []).append(o.type_id)
    return {k: tuple(sorted(v)) for k, v in sorted(classes.items(),
                                                   key=lambda kv: sorted(kv[0]))}


def legacy_classes(catalog: Sequence[ObjectionType]) -> Mapping[str, tuple[str, ...]]:
    classes: dict[str, list[str]] = {}
    for o in catalog:
        if o.legacy_family is not None:
            classes.setdefault(o.legacy_family, []).append(o.type_id)
    return {k: tuple(sorted(v)) for k, v in sorted(classes.items())}


def _partition(classes: Mapping[object, tuple[str, ...]]) -> frozenset[frozenset[str]]:
    return frozenset(frozenset(v) for v in classes.values())


def splits_against_legacy(catalog: Sequence[ObjectionType]) -> tuple[tuple[str, ...], ...]:
    computed = _partition(footprint_classes(catalog))
    out = []
    for members in legacy_classes(catalog).values():
        block = frozenset(members)
        if block not in computed and len(block) > 1:
            out.append(tuple(sorted(block)))
    return tuple(out)


@dataclass(frozen=True)
class Ablation:
    removed: str
    still_accepted: tuple[str, ...]
    became_unavailable: tuple[str, ...]
    verdict_changed: tuple[str, ...]


def ablate(catalog: Sequence[ObjectionType], tables: Mapping[str, object],
           grounds: Mapping[str, Grounds], removed: str) -> Ablation:
    """Drop one table and report which objections lose their judgement."""
    reduced = {k: v for k, v in tables.items() if k != removed}
    accepted, unavailable, changed = [], [], []
    for o in catalog:
        payload = grounds.get(o.type_id)
        if payload is None:
            continue
        before, after = judge(o, tables, payload), judge(o, reduced, payload)
        if removed in o.footprint.declared:
            unavailable.append(o.type_id)
            if before.upheld != after.upheld:
                changed.append(o.type_id)
        elif after.accepted:
            accepted.append(o.type_id)
    return Ablation(removed, tuple(sorted(accepted)), tuple(sorted(unavailable)),
                    tuple(sorted(changed)))


# --------------------------------------------------------------------------
# Judges and the catalog
# --------------------------------------------------------------------------


def _frequency(a: Access, g: Grounds) -> bool:
    limit = (a.read("book.endorsements") or {}).get(g.payload["bound_id"])
    seen = (a.read("settled.record") or {}).get(g.payload["target"])
    return limit is not None and seen is not None and seen < limit


def _calibration(a: Access, g: Grounds) -> bool:
    book = a.read("book.endorsements") or {}
    settled = a.read("settled.record") or {}
    return any(settled.get(k, k) != v for k, v in book.items())


def _exposure(a: Access, g: Grounds) -> bool:
    return bool((a.read("region") or {}).get("infeasible"))


def _address(a: Access, g: Grounds) -> bool:
    return (a.read("book.endorsements") or {}).get(g.payload["bound_id"]) is not None


def _coverage(a: Access, g: Grounds) -> bool:
    cov = a.read("ledger.coverage") or {}
    obs = a.read("ledger.obligations") or {}
    return any(o not in cov for o in obs)


def _persistence(a: Access, g: Grounds) -> bool:
    return any(s == "open" for s in (a.read("ledger.obligations") or {}).values())


def _sure_loss(a: Access, g: Grounds) -> bool:
    return bool(g.payload.get("farkas")) and bool(a.read("book.endorsements") or {})


def _merits_evasion(a: Access, g: Grounds) -> bool:
    rulings = a.read("rulings") or {}
    schedules = a.read("schedule.procedure") or {}
    ruling = rulings.get(g.payload["ruling_id"])
    if ruling is None or schedules.get(ruling["schedule_version"]) is None:
        return False
    return ruling["basis"] == "default" and bool(g.payload["cleared"])


def _cross_subsidy(a: Access, g: Grounds) -> bool:
    liabilities = a.read("liabilities") or {}
    return bool(g.payload.get("fence_id")) and g.payload["transfer_id"] in liabilities


def _aggregate_default(a: Access, g: Grounds) -> bool:
    declared = a.read("book.declared_rates") or {}
    rulings = a.read("rulings") or {}
    limit = declared.get("default_resolution_rate")
    window = g.payload["window"]
    inside = [r for r in rulings.values() if window[0] <= r["date"] <= window[1]]
    if limit is None or not inside:
        return False
    weighted = sum(r["stakes"] for r in inside if r["basis"] == "default")
    total = sum(r["stakes"] for r in inside)
    return total > 0 and weighted * limit[1] > limit[0] * total


def _probe_blackout(a: Access, g: Grounds) -> bool:
    requests = a.read("settlement.requests") or {}
    positions = a.read("positions") or {}
    request = requests.get(g.payload["request_id"])
    if request is None:
        return False
    start, end = g.payload["window"]
    if (request["funder_id"] != g.payload["funder_id"]
            or request["target"] != g.payload["target"]):
        return False
    return any(p["actor_id"] == request["funder_id"] and p["target"] == request["target"]
               and p.get("fresh", True) and start <= p["date"] <= end
               for p in positions.values())


def _common_source(a: Access, g: Grounds) -> bool:
    events = a.read("settlement.record") or {}
    premises, shared = g.payload["premises"], g.payload["common_funders"]
    if not premises or not shared:
        return False
    for premise in premises:
        event = events.get(premise)
        if event is None or not set(shared) <= set(event.get("funder_profile", ())):
            return False
    return True


CATALOG: tuple[ObjectionType, ...] = (
    ObjectionType("frequency", Footprint(("book.endorsements",), ("settled.record",)),
                  _frequency, legacy_family="calibration"),
    ObjectionType("calibration", Footprint(("book.endorsements",), ("settled.record",)),
                  _calibration, legacy_family="calibration"),
    ObjectionType("exposure", Footprint((), ("region",)), _exposure,
                  legacy_family="coherence"),
    ObjectionType("address", Footprint(("book.endorsements",), ()), _address,
                  references_dispositions=True, legacy_family="repair"),
    ObjectionType("coverage", Footprint((), ("ledger.coverage", "ledger.obligations")),
                  _coverage, legacy_family="repair"),
    ObjectionType("persistence", Footprint((), ("ledger.obligations",)), _persistence,
                  legacy_family="answerability"),
    ObjectionType("sure-loss", Footprint(("book.endorsements",), ()), _sure_loss,
                  legacy_family="coherence"),
    ObjectionType("merits-evasion", Footprint(("schedule.procedure",), ("rulings",)),
                  _merits_evasion, legacy_family="answerability"),
    ObjectionType("aggregate-default", Footprint(("book.declared_rates",), ("rulings",)),
                  _aggregate_default, legacy_family="answerability"),
    ObjectionType("cross-subsidy", Footprint((), ("liabilities",)), _cross_subsidy,
                  legacy_family="coherence"),
    ObjectionType("probe-blackout",
                  Footprint((), ("settlement.requests", "positions")), _probe_blackout,
                  legacy_family="answerability"),
    ObjectionType("common-source", Footprint((), ("settlement.record",)), _common_source,
                  legacy_family="calibration"),
)

CATALOG_BY_ID = {o.type_id: o for o in CATALOG}
