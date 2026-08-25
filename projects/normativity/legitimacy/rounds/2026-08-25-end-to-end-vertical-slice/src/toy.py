"""The canonical trajectory, and the adversarial variants of it.

Three stages, on one Reflective Integrity history:

    A  a thin seed issues `PValue(v0)` and an injunction over a LUV `v0` exposes;
       the injunction compiles, composes with the deductive region, and is put to
       the enforcement interface.
    B  an environment outcome is read into a settlement, the settlement enters
       `L`, a reason cites it, and a normative event supersedes `v0` by `v1`.
       The injunction is untouched and still refers rigidly to `X[v0:q]`.
    C  a later normative event supersedes the injunction by one over `X[v1:q]`.
       Only now does the operative region change for that reason.

The point of B is that it is a state-transition fact rather than a sentence:
between B and C the record contains an active `PValue(v1)` and an active
injunction whose compiled rows mention `v0`'s thresholds, and the compiler has
no expression that could have rewritten one into the other.
"""
from __future__ import annotations

import pathlib
import sys
from fractions import Fraction
from typing import Optional

_HERE = pathlib.Path(__file__).resolve().parent
_RI = (_HERE.parents[1] / "2026-08-24-reflective-integrity-core" / "src")
if str(_RI) not in sys.path:
    sys.path.insert(0, str(_RI))

from ri_core import (ACCOUNT_FOR_SUCCESSION, ACTIVE, GENESIS, AnsRoot,
                     Derivation, History, PAuth, PForce, Seed, SchemaCode,
                     Standing, StandingState, Create, Supersede, creating)

import li
from epistemic import (RawOutcome, SettlementReading, SettlementSemantics,
                       Stage, StageEntry, deductive_entries)
from pipeline import run_day
from standing import PValue
from waist import (CertifiedLUV, Ineq, Injunction, Expect, Prob, ValueRegistry,
                   ValueSpec, luv_exposure, refusing)

Q = Fraction

PHI = li.Atom("phi")                  # an ordinary priced proposition

#: The days any run in this round inspects.
DAYS = (0, 1, 2)

#: Every threshold those days price. The stage's coherence chain runs over this,
#: because a stage is fixed while the day's grid moves.
GRID = li.merged_grid(DAYS)


# ------------------------------------------------------------ value layer


def registry() -> ValueRegistry:
    """`v0` and `v1`, both frozen, both exposing the same query name.

    `v1` supersedes `v0` as a matter of standing, and the two exposures are
    different LUVs with different names. There is no operation anywhere that
    maps `X[v0:q]` to `X[v1:q]`.
    """
    reg = ValueRegistry()
    reg.admit(ValueSpec(
        spec_id="v0",
        payload={"about": "an early reading of what the deployment is for"},
        exposures=(
            ("q", luv_exposure("thresholds-v0-q",
                               {"low": Q(0), "mid": Q(1, 2), "high": Q(1)})),
            ("incomparable", refusing(
                "the specification ranks two goods without a common scale")),
        )))
    reg.admit(ValueSpec(
        spec_id="v1",
        payload={"about": "the reading after the outcome was settled"},
        exposures=(
            ("q", luv_exposure("thresholds-v1-q",
                               {"low": Q(0), "mid": Q(1, 3), "high": Q(1)})),
        ),
        supersedes=("v0",)))
    return reg


def x0(reg: Optional[ValueRegistry] = None) -> CertifiedLUV:
    return (reg or registry()).compile_value("v0", "q")


def x1(reg: Optional[ValueRegistry] = None) -> CertifiedLUV:
    return (reg or registry()).compile_value("v1", "q")


# -------------------------------------------------------- operative layer


def j0(X0: CertifiedLUV) -> Injunction:
    """`Expect(X0) <= 1/2` and `Prob(phi) >= 1/4`, as one payload."""
    return Injunction("J0", (
        Ineq(((Q(1), Expect(X0)),), rhs=Q(1, 2), label="value-ceiling"),
        Ineq(((Q(-1), Prob(PHI)),), rhs=Q(-1, 4), label="reversibility-floor"),
    ))


def j1(X1: CertifiedLUV) -> Injunction:
    """`Expect(X1) <= 1/2`, over the LUV the revised specification exposes."""
    return Injunction("J1", (
        Ineq(((Q(1), Expect(X1)),), rhs=Q(1, 2), label="value-ceiling"),
    ))


# ------------------------------------------------------------ RI machinery


def _schema_superseding_by_wit(name: str, payloads) -> SchemaCode:
    """Supersede whichever standing the event's witness names.

    The witness is what fixes the target, so one authority serves a supersession
    whose target id is not known when the authority is created. Determinacy is
    intact: a fixed witness gives a fixed effect.
    """
    K = tuple(payloads)
    return SchemaCode(name, lambda wit, pre: Standing(Supersede(frozenset([wit]), K)))


def seed(X0: CertifiedLUV, X1: CertifiedLUV) -> Seed:
    """A thin seed: four authorities, one genesis root each, nothing else."""
    payloads = {
        "auth:value": PAuth(creating("issue-v0", [PValue("v0")])),
        "auth:force": PAuth(creating(
            "issue-J0",
            [PForce("auth:value", "auth:force", j0(X0))])),
        "auth:revalue": PAuth(_schema_superseding_by_wit(
            "supersede-value", [PValue("v1")])),
        "auth:reforce": PAuth(_schema_superseding_by_wit(
            "supersede-force",
            [PForce("auth:revalue", "auth:reforce", j1(X1))])),
    }
    std0 = {x: StandingState(ACTIVE, frozenset(), p) for x, p in payloads.items()}
    roots0 = tuple(AnsRoot(f"q0:{x}", ("P0", 0), "A", x, ACCOUNT_FOR_SUCCESSION,
                           GENESIS, 0) for x in payloads)
    return Seed("P0", std0, roots0)


#: Where the created objects land. `standing_tag(tau, i)` is `@s{tau}.{i}`, and
#: the trajectory below fixes the taus, so these are computed, not guessed.
V0_STANDING = "@s1.0"
J0_STANDING = "@s2.0"
V1_STANDING = "@s5.0"
J1_STANDING = "@s7.0"


class Trajectory:
    """The toy history, its ledger semantics, and the day runs over it."""

    def __init__(self) -> None:
        self.registry = registry()
        self.X0 = x0(self.registry)
        self.X1 = x1(self.registry)
        self.sem = SettlementSemantics()
        self.history = History(seed(self.X0, self.X1))
        self.settled: list = []
        self.outcomes: list = []

    # -- stage A ------------------------------------------------------

    def stage_a(self) -> "Trajectory":
        """Issue `PValue(v0)` at tau 1, then the injunction at tau 2."""
        self.history.norm("a:value", "auth:value", author="A")
        self.history.norm("a:force", "auth:force", author="A")
        return self

    # -- stage B ------------------------------------------------------

    def stage_b(self) -> "Trajectory":
        """An outcome is read, settled, cited, and answered with a revaluation.

        The order is the one the record forces: a settlement is appended before
        any reason may cite it, and a reason occurs before the normative event
        whose derivation has it among its leaves.
        """
        outcome = RawOutcome("o:trial", "the trial ran and the readout came back")
        self.outcomes.append(outcome)
        reading = self.sem.admit(SettlementReading(
            settle_id="l:trial",
            of_outcome=outcome.id,
            sentences=(self.X0.luv.gt(Q(1, 3)),
                       li.Neg(self.X0.luv.gt(Q(2, 3)))),
            note="the readout pins the exposed quantity into (1/3, 2/3]"))
        self.settled.append(reading.settle_id)
        self.history.settle("l:trial")
        self.history.reason("e:revalue", s_L=frozenset(["l:trial"]),
                            target=li.Atom("v0-is-superseded"))
        self.history.norm("a:revalue", "auth:revalue", author="A",
                          wit=V0_STANDING,
                          derivation=Derivation(
                              concl=li.Atom("v0-is-superseded"),
                              leaves=frozenset(["e:revalue"])))
        return self

    # -- stage C ------------------------------------------------------

    def stage_c(self) -> "Trajectory":
        """A second normative event, and only now does operative force move."""
        self.history.reason("e:reforce", s_L=frozenset(["l:trial"]),
                            target=li.Atom("J0-should-be-replaced"))
        self.history.norm("a:reforce", "auth:reforce", author="A",
                          wit=J0_STANDING,
                          derivation=Derivation(
                              concl=li.Atom("J0-should-be-replaced"),
                              leaves=frozenset(["e:reforce"])))
        return self

    # -- the epistemic substrate --------------------------------------

    def deductive(self) -> tuple:
        """`D_n`: threshold coherence for both LUVs, over the toy's grid.

        These are consequences of the theory representing the exposed
        quantities' computations. They are the deductive channel and never move.
        """
        return deductive_entries(
            li.threshold_chain(self.X0.luv, GRID)
            + li.threshold_chain(self.X1.luv, GRID),
            note="threshold coherence")

    def stage(self, t: Optional[int] = None) -> Stage:
        """`Sigma_n = D_n union Sem_L(L_n)`, at RI state `t`."""
        ids = [s.id for s in self.history.settlements(t)]
        return Stage.of(self.deductive(), self.sem.entries(ids))

    # -- the day runs -------------------------------------------------

    def day(self, n: int, t: Optional[int] = None, **kw):
        """Run day `n` against the record's state at `t`."""
        return run_day(n, self.stage(t), self.history.std(t), **kw)


def canonical(prior=(Q(3, 4), Q(1, 2))) -> dict:
    """The three-stage run, as a dictionary a trace or a test can walk.

    Day indices are chosen so that each stage is inspected at a different LI
    precision: `k = n + 1` is 1, 2 and 3, which is what makes the frozen
    injunction's changing low-level realization visible.
    """
    traj = Trajectory()
    traj.stage_a()
    a = traj.day(0, prior=prior)

    traj.stage_b()
    b = traj.day(1, prior=(Q(3, 4), Q(1, 4), Q(1, 2)))

    traj.stage_c()
    c = traj.day(2, prior=(Q(3, 4), Q(1, 2), Q(1, 4)))
    return {"trajectory": traj, "A": a, "B": b, "C": c}
