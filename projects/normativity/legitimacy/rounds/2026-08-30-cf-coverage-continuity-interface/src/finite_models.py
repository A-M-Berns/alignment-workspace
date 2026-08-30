"""Exact finite hostile models for the CF/Coverage interface.

Worlds are records produced by an explicit beta table.  No probability or float is used.
The checks discriminate target preservation, single-policy structural exposure, actual
registration, and end-to-end route adequacy.  They are fixtures, not registered claims.
"""

from dataclasses import dataclass
from typing import Hashable, Mapping


BOTTOM = "⊥"


@dataclass(frozen=True)
class World:
    target: Hashable
    receipt: Hashable
    represented: bool


@dataclass(frozen=True)
class Model:
    name: str
    queries: tuple[Hashable, ...]
    complements: tuple[Hashable, ...]
    beta: Mapping[tuple[Hashable, Hashable], World]
    target: Mapping[Hashable, Hashable]
    actual_query: Hashable
    route_queries: tuple[Hashable, ...]
    active: bool = True
    disposition: bool = False

    def target_preserving(self) -> bool:
        return all(
            self.beta[q, z].target == self.target[z]
            for q in self.queries
            for z in self.complements
        )

    def query_exposes(self, q: Hashable) -> bool:
        """T factors through Y_q: equal receipts imply equal targets."""
        return all(
            self.beta[q, z0].receipt != self.beta[q, z1].receipt
            or self.target[z0] == self.target[z1]
            for z0 in self.complements
            for z1 in self.complements
        )

    def structurally_accessible(self) -> bool:
        return any(self.query_exposes(q) for q in self.route_queries)

    def registration_on_actual_policy(self) -> bool:
        """Robust counterfactual registration under q_act, not a past event."""
        return all(self.beta[self.actual_query, z].represented for z in self.complements)

    def route_registration_capable(self, q: Hashable) -> bool:
        return all(self.beta[q, z].represented for z in self.complements)

    def implemented(self) -> bool:
        if not self.active or self.disposition:
            return True
        return self.target_preserving() and any(
            self.query_exposes(q)
            and self.route_registration_capable(q)
            for q in self.route_queries
        )


def table(
    name: str,
    queries: tuple[Hashable, ...],
    complements: tuple[Hashable, ...],
    target: Mapping[Hashable, Hashable],
    rows: Mapping[tuple[Hashable, Hashable], tuple[Hashable, Hashable, bool]],
    actual: Hashable,
    routes: tuple[Hashable, ...],
    *,
    active: bool = True,
    disposition: bool = False,
) -> Model:
    return Model(
        name,
        queries,
        complements,
        {key: World(*value) for key, value in rows.items()},
        target,
        actual,
        routes,
        active,
        disposition,
    )


BITS = (0, 1)


def bit_rows(queries, rule):
    return {(q, z): rule(q, z) for q in queries for z in BITS}


MODELS = {
    "passive_sensor": table(
        "passive_sensor", ("idle", "read"), BITS, {0: 0, 1: 1},
        bit_rows(("idle", "read"), lambda q, z: (z, z if q == "read" else BOTTOM, q == "read")),
        "read", ("read",),
    ),
    "active_preserving": table(
        "active_preserving", ("dose0", "dose1"), BITS, {0: 0, 1: 1},
        bit_rows(("dose0", "dose1"), lambda q, z: (z, (q, z ^ (q == "dose1")), True)),
        "dose1", ("dose0", "dose1"),
    ),
    "changes_target": table(
        "changes_target", ("set0", "set1"), ("base",), {"base": 0},
        {("set0", "base"): (0, 0, True), ("set1", "base"): (1, 1, True)},
        "set1", ("set0", "set1"),
    ),
    "self_fulfilling": table(
        "self_fulfilling", ("announce0", "announce1"), ("person",), {"person": 0},
        {("announce0", "person"): (0, 0, True), ("announce1", "person"): (1, 1, True)},
        "announce1", ("announce0", "announce1"),
    ),
    "sensor_destruction": table(
        "sensor_destruction", ("destroy",), BITS, {0: 0, 1: 1},
        bit_rows(("destroy",), lambda q, z: (z, BOTTOM, False)),
        "destroy", ("destroy",),
    ),
    "sensor_replacement": table(
        "sensor_replacement", ("old", "new"), BITS, {0: 0, 1: 1},
        bit_rows(("old", "new"), lambda q, z: (z, (q, z), True)),
        "new", ("new",),
    ),
    "ontology_deletion": table(
        "ontology_deletion", ("read_without_concept",), BITS, {0: 0, 1: 1},
        bit_rows(("read_without_concept",), lambda q, z: (z, z, False)),
        "read_without_concept", ("read_without_concept",),
    ),
    "ontology_translation": table(
        "ontology_translation", ("old_words", "new_words"), BITS, {0: 0, 1: 1},
        bit_rows(("old_words", "new_words"), lambda q, z: (z, ("bad", "good")[z] if q == "old_words" else ("red", "blue")[z], True)),
        "new_words", ("new_words",),
    ),
    "delegation": table(
        "delegation", ("idle", "delegate_read"), BITS, {0: 0, 1: 1},
        bit_rows(("idle", "delegate_read"), lambda q, z: (z, z if q == "delegate_read" else BOTTOM, q == "delegate_read")),
        "delegate_read", ("delegate_read",),
    ),
    "censoring_delegate": table(
        "censoring_delegate", ("delegate_read",), BITS, {0: 0, 1: 1},
        bit_rows(("delegate_read",), lambda q, z: (z, BOTTOM, False)),
        "delegate_read", ("delegate_read",),
    ),
    "predictor_dependence": table(
        "predictor_dependence", ("idle", "probe"), BITS, {0: 0, 1: 1},
        bit_rows(("idle", "probe"), lambda q, z: (z, ("predicts", q), False)),
        "probe", ("probe",),
    ),
    "strategic_responder": table(
        "strategic_responder", ("soft", "hard"), BITS, {0: 0, 1: 1},
        bit_rows(("soft", "hard"), lambda q, z: (z, z if q == "hard" else BOTTOM, q == "hard")),
        "hard", ("hard",),
    ),
    "route_never_exercised": table(
        "route_never_exercised", ("idle", "read"), BITS, {0: 0, 1: 1},
        bit_rows(("idle", "read"), lambda q, z: (z, z if q == "read" else BOTTOM, q == "read")),
        "idle", ("read",),
    ),
    "receipt_not_registered": table(
        "receipt_not_registered", ("read",), BITS, {0: 0, 1: 1},
        bit_rows(("read",), lambda q, z: (z, z, False)),
        "read", ("read",),
    ),
    "persistent_broken": table(
        "persistent_broken", ("idle",), BITS, {0: 0, 1: 1},
        bit_rows(("idle",), lambda q, z: (z, BOTTOM, False)),
        "idle", ("idle",),
    ),
    "scope_shrunk": table(
        "scope_shrunk", ("read_c0",), ((0, 0), (0, 1), (1, 0), (1, 1)),
        {(a, b): b for a, b in ((0, 0), (0, 1), (1, 0), (1, 1))},
        {("read_c0", (a, b)): (b, a, True) for a, b in ((0, 0), (0, 1), (1, 0), (1, 1))},
        "read_c0", ("read_c0",),
    ),
    "terminal_retirement": table(
        "terminal_retirement", ("idle",), ("retired",), {"retired": 0},
        {("idle", "retired"): (0, BOTTOM, False)}, "idle", (), active=False, disposition=True,
    ),
    "prerequisite_discharged": table(
        "prerequisite_discharged", ("idle", "investigate"), BITS, {0: 0, 1: 1},
        bit_rows(("idle", "investigate"), lambda q, z: (z, z if q == "investigate" else BOTTOM, q == "investigate")),
        "investigate", ("investigate",),
    ),
    "procedural_no_physical": table(
        "procedural_no_physical", ("idle",), BITS, {0: 0, 1: 1},
        bit_rows(("idle",), lambda q, z: (z, BOTTOM, False)),
        "idle", ("idle",),
    ),
    "physical_no_normative": table(
        "physical_no_normative", ("read",), BITS, {0: 0, 1: 1},
        bit_rows(("read",), lambda q, z: (z, z, True)),
        "read", ("read",), active=False,
    ),
}


EXPECTED = {
    "passive_sensor": (True, True, True, True),
    "active_preserving": (True, True, True, True),
    "changes_target": (False, True, True, False),
    "self_fulfilling": (False, True, True, False),
    "sensor_destruction": (True, False, False, False),
    "sensor_replacement": (True, True, True, True),
    "ontology_deletion": (True, True, False, False),
    "ontology_translation": (True, True, True, True),
    "delegation": (True, True, True, True),
    "censoring_delegate": (True, False, False, False),
    "predictor_dependence": (True, False, False, False),
    "strategic_responder": (True, True, True, True),
    "route_never_exercised": (True, True, False, True),
    "receipt_not_registered": (True, True, False, False),
    "persistent_broken": (True, False, False, False),
    "scope_shrunk": (True, False, True, False),
    "terminal_retirement": (True, False, False, True),
    "prerequisite_discharged": (True, True, True, True),
    "procedural_no_physical": (True, False, False, False),
    "physical_no_normative": (True, True, True, True),
}


def signature(model: Model) -> tuple[bool, bool, bool, bool]:
    return (
        model.target_preserving(),
        model.structurally_accessible(),
        model.registration_on_actual_policy(),
        model.implemented(),
    )
