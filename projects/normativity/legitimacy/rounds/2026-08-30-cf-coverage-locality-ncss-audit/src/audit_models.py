"""Finite locality and one-step NCSS models.

These fixtures test necessity claims only.  A residual observation is a supplied map from
worlds to a protected behavioral value; locality quantifies over every ambient exterior.
No probability or floating-point arithmetic is used.
"""

from dataclasses import dataclass
from itertools import product
from typing import Callable, Hashable


World = tuple[Hashable, ...]


@dataclass(frozen=True)
class LocalPatch:
    name: str
    queries: tuple[Hashable, ...]
    residuals: tuple[Hashable, ...]
    exteriors: tuple[Hashable, ...]
    alpha: Callable[[Hashable, Hashable], Hashable]
    outcome: Callable[[Hashable, Hashable], World]
    residual_projection: Callable[[Hashable], Hashable]
    residual_observation: Callable[[World], Hashable]

    def cfp_holds(self) -> bool:
        # beta is definitionally outcome(alpha(q,r),e), with z=(r,e).
        return all(
            self.outcome(self.alpha(q, r), e)
            == self.outcome(self.alpha(q, r), e)
            for q, r, e in product(self.queries, self.residuals, self.exteriors)
        )

    def rp_holds(self) -> bool:
        return all(
            self.residual_projection(self.alpha(q, r)) == r
            for q, r in product(self.queries, self.residuals)
        )

    def behaviorally_local(self) -> bool:
        return all(
            self.residual_observation(self.outcome(self.alpha(q0, r), e))
            == self.residual_observation(self.outcome(self.alpha(q1, r), e))
            for q0, q1, r, e in product(
                self.queries, self.queries, self.residuals, self.exteriors
            )
        )

    def residual_observation_nontrivial(self) -> bool:
        values = {
            self.residual_observation(self.outcome(self.alpha(q, r), e))
            for q, r, e in product(self.queries, self.residuals, self.exteriors)
        }
        return len(values) > 1


def whole_agent_replacement() -> LocalPatch:
    # q chooses both inquiry mode and mission.  R is a singleton and RP is vacuous.
    return LocalPatch(
        "whole_agent_replacement",
        ("agent_red", "agent_blue"),
        ("unit",),
        ("calm", "hostile"),
        lambda q, _r: q,
        lambda a, e: (a, "receipt" if a == "agent_blue" else "none", e),
        lambda _a: "unit",
        lambda w: w[0],
    )


def fake_rp() -> LocalPatch:
    # Canonical second projection holds, but q still changes protected mission behavior.
    return LocalPatch(
        "fake_rp",
        (0, 1),
        ("residual-label",),
        (0, 1),
        lambda q, r: (q, r),
        lambda a, e: (a[0], a[1], e),
        lambda a: a[1],
        lambda w: w[0],
    )


def extensional_local() -> LocalPatch:
    # q changes receipt; protected residual behavior depends on r and e but not q.
    return LocalPatch(
        "extensional_local",
        ("idle", "query"),
        ("guard", "serve"),
        ("calm", "hostile"),
        lambda q, r: (q, r),
        lambda a, e: (a[1], e, "datum" if a[0] == "query" else "none"),
        lambda a: a[1],
        lambda w: (w[0], w[1]),
    )


def predictor_local() -> LocalPatch:
    # e is a predictor response function represented by its truth table.
    predictors = (("predict-idle", "predict-query"), ("x", "x"))
    return LocalPatch(
        "predictor_local",
        ("idle", "query"),
        ("serve",),
        predictors,
        lambda q, r: (q, r),
        lambda a, e: (a[1], e[0] if a[0] == "idle" else e[1]),
        lambda a: a[1],
        lambda w: w[0],
    )


def strategic_local() -> LocalPatch:
    # Exterior actions vary with q because the held-fixed object is a strategy table.
    strategies = (("ignore", "answer"), ("answer", "counter"))
    return LocalPatch(
        "strategic_local",
        ("soft", "hard"),
        ("mission",),
        strategies,
        lambda q, r: (q, r),
        lambda a, e: (a[1], e[0] if a[0] == "soft" else e[1]),
        lambda a: a[1],
        lambda w: w[0],
    )


def self_modify_local() -> LocalPatch:
    # q is a complete inquiry continuation, including its later self-edit; r is unchanged.
    return LocalPatch(
        "self_modify_local",
        ("keep_sensor", "upgrade_sensor"),
        ("serve", "guard"),
        ("quiet", "attack"),
        lambda q, r: (q, r),
        lambda a, e: (a[1], e, "v2" if a[0] == "upgrade_sensor" else "v1"),
        lambda a: a[1],
        lambda w: (w[0], w[1]),
    )


def delegation_query_factor() -> LocalPatch:
    # Treating delegate identity as q changes the protected controller and fails locality.
    return LocalPatch(
        "delegation_query_factor",
        ("delegate_A", "delegate_B"),
        ("task",),
        ("normal",),
        lambda q, r: (q, r),
        lambda a, e: (a[0], a[1], e),
        lambda a: a[1],
        lambda w: w[0],
    )


def delegation_residual_factor() -> LocalPatch:
    # Treating delegate identity as residual and varying only ask/idle is local.
    return LocalPatch(
        "delegation_residual_factor",
        ("idle", "ask"),
        ("delegate_A", "delegate_B"),
        ("normal",),
        lambda q, r: (q, r),
        lambda a, e: (a[1], a[0], e),
        lambda a: a[1],
        lambda w: w[0],
    )


def no_nontrivial_patch() -> LocalPatch:
    # Every query-policy difference changes the protected mission for every exterior.
    return LocalPatch(
        "no_nontrivial_patch",
        ("policy_0", "policy_1"),
        ("unit",),
        (0, 1),
        lambda q, _r: q,
        lambda a, e: (a, e),
        lambda _a: "unit",
        lambda w: w[0],
    )


LOCALITY_MODELS = {
    model.name: model
    for model in (
        whole_agent_replacement(),
        fake_rp(),
        extensional_local(),
        predictor_local(),
        strategic_local(),
        self_modify_local(),
        delegation_query_factor(),
        delegation_residual_factor(),
        no_nontrivial_patch(),
    )
}


@dataclass(frozen=True)
class NcssStep:
    pre_live: bool
    post_active: bool
    post_represented: bool
    post_adequate_route: bool
    resolves_last: bool
    opens_successor: bool
    resolution_continuity: bool = True
    fresh_successor: bool = True

    @property
    def post_defect(self) -> bool:
        return self.post_active and not self.post_represented and not self.post_adequate_route

    @property
    def local_close_adequacy(self) -> bool:
        # A terminal certificate must show no post-transition contract defect.
        return not (self.resolves_last and not self.opens_successor and self.post_defect)

    @property
    def post_live(self) -> bool:
        if not self.pre_live:
            return False
        if not self.resolution_continuity:
            return False
        if not self.resolves_last:
            return True
        return self.opens_successor and self.fresh_successor

    @property
    def post_implements(self) -> bool:
        # One-criticism instance of IMP.
        return not self.post_defect


def exact_ncss(step: NcssStep) -> bool:
    premise = step.pre_live and step.post_defect and step.local_close_adequacy
    return not premise or (step.post_live and not step.post_implements)


@dataclass(frozen=True)
class RegistrationStage:
    capable: bool
    exercised: bool
    receipt: bool
    registered: bool


REGISTRATION_TRACE = (
    RegistrationStage(True, False, False, False),
    RegistrationStage(True, True, False, False),
    RegistrationStage(True, True, True, False),
    RegistrationStage(True, True, True, True),
)
