"""The composite guarantee, quantified over engines satisfying the interface.

The corpus's conditional composite is stated over one named condition bundle:
`NL-J3` inherits `C-MOVING-INTERFACE` wholesale, so its Logical Induction
boundary reads "such a corollary is available only if every condition of
`C-MOVING-INTERFACE` is separately supplied".  That is a theorem about one
bundle, not about a class of engines.

This module does two things.  It records the mapping between that bundle and the
settlement interface, condition by condition, including the conditions with no
counterpart and the clauses the bundle never needed -- those are findings, and
`MOVING_INTERFACE_MAP.md` carries them in full.  And it restates the composite
over **any engine satisfying the relevant interface clauses**, with the clauses
evaluated by the interface predicates rather than assumed.

**What kind of theorem this is.**  It is a substitution: every hypothesis of
`NL-J3` is discharged by a named interface clause, or carried as an explicit
hypothesis object, and the conclusion is `NL-J3`'s unchanged.  No new
mathematics is claimed, and the ledger row says *composition*, not *proved*.
The content is that the antecedent is now a checkable predicate over a class
instead of a bundle nobody can evaluate: `parametric_composite` refuses to
report a bound when a clause fails, and names which one.

**Where the audit's conditionals enter.**  Three hypotheses are marked
conditional by the witness audit and appear here as explicit hypothesis objects
rather than as discharged clauses: the certified core minimum's persistence, a
working tolerance, and consistency of the declared theory.  A fourth thing the
audit did not have is available here: because the core condition is linear in
the reference at fixed coefficient, the *current* satisfiability of a declared
core minimum is a linear program, so P1 splits into a checkable half and a
declared half, and only the declared half is open.

Finiteness discipline.  Every quantity is an exact rational computed from a
finite record prefix and finitely many declared parameters.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.joint import movement_recursion, uniform_wealth_cap
from src.settlement_interface import (
    CHECKABLE,
    DeclaredHypothesis,
    EngineDeclaration,
    SettlementRecord,
    evaluate_interface,
)

# Relations a corpus condition can bear to the interface clauses.
IMPLIED_BY_SI = "implied by the interface clauses"
IMPLIES_SI = "implies the interface clause, strictly stronger"
EQUIVALENT = "equivalent modulo the declared constant"
NEITHER = "neither direction"
NO_COUNTERPART = "no interface counterpart"


@dataclass(frozen=True)
class ConditionMapping:
    """One condition of the corpus bundle, and where it lands on the interface."""

    label: str
    condition: str
    clauses: tuple[str, ...]
    relation: str
    note: str


# The eight conditions of the corpus's positive moving-correspondence interface,
# read off its statement in the frozen operative-force theory.
MOVING_INTERFACE_MAP: tuple[ConditionMapping, ...] = (
    ConditionMapping(
        "MI-1", "fix a computable deductive process",
        ("J1", "C1-logical"), IMPLIED_BY_SI,
        "J1 makes the process declared public record and C1-logical quantifies "
        "over 'the declared deductive process', so the interface supplies this "
        "once declaration is read as effective presentation."),
    ConditionMapping(
        "MI-2", "each date publishes before demand a rational compact convex region",
        (), NO_COUNTERPART,
        "FINDING. Prefix-causal publication is a quote discipline on the "
        "mechanism, not a property of a world-channel, and no clause of the "
        "interface asks for it. It must be carried as an explicit hypothesis."),
    ConditionMapping(
        "MI-3",
        "computes a rational witnessed reference and a fixed positive core "
        "coefficient with the core condition against the ambient simplex",
        ("P1",), IMPLIES_SI,
        "FINDING. Strictly stronger in two independent ways: it fixes the "
        "coefficient where P1 admits a varying core with a certified minimum, "
        "and it reads the core against the ambient simplex, which voids on the "
        "first exact pin. P1 under the relative reading is what an engine can "
        "actually certify."),
    ConditionMapping(
        "MI-4",
        "coherently extends its retained world mixture to fresh queried sentences",
        (), NO_COUNTERPART,
        "FINDING. A compiler property about language growth. T1 is adjacent but "
        "governs the tolerance of existing prices, not extension to new "
        "sentences, and neither implies the other."),
    ConditionMapping(
        "MI-5",
        "bounds reference drift by a summable schedule with finite total",
        (), NO_COUNTERPART,
        "FINDING. Supplied downstream rather than by any engine: the movement "
        "recursion assigns each of the at most Psi_0 reference jumps its "
        "majorant, and their sum is the total. Mechanism-side, so it stays an "
        "explicit hypothesis of the parametric theorem."),
    ConditionMapping(
        "MI-6",
        "computes a constrained quote with errors summing to a finite total",
        ("T1",), NEITHER,
        "FINDING, and the refinement ρ1 needs. The bundle does carry an error "
        "budget, but it is a *solver* budget on quote selection, not a tolerance "
        "on how incoherent the engine's prices may be. The bundle has no "
        "coherence-tolerance clause; T1 has no solver-error clause."),
    ConditionMapping(
        "MI-7a", "preserves the rational prefix-causal clock",
        ("C2", "C3"), NEITHER,
        "The clock conditions are incomparable: prefix-causality is a "
        "constructibility discipline the interface never states, while ripeness, "
        "tolling and adequacy are docket structure the bundle never states."),
    ConditionMapping(
        "MI-7b", "preserves the aggregate downside limit of two",
        ("P2",), EQUIVALENT,
        "The cleanest correspondence in the table. The bundle's constant is P2's "
        "declared limit with the constant fixed at two."),
    ConditionMapping(
        "MI-8",
        "uses an aggregate trading field with the declared dominance property",
        ("P4",), IMPLIES_SI,
        "FINDING. The bundle hard-codes trader vocabulary; P4 declines to, and "
        "asks only that a certificate type be named and the guarantee stated "
        "relative to it. The bundle's condition is one instantiation of P4."),
)

# Interface clauses the corpus bundle never needed.
UNUSED_CLAUSES: tuple[tuple[str, str], ...] = (
    ("J2", "write-once, owner-only. The bundle has no exclusivity formulation at "
           "all: nothing in it prevents a variable being settled twice."),
    ("J3", "migration transport. The bundle is stated inside one fixed language."),
    ("C1-empirical", "funding-responsive completeness. The bundle's channel is "
                     "purely deductive."),
    ("C3", "adequacy. The bundle relates no downstream deadline to an upstream "
           "horizon."),
    ("P3", "finite gating. The bundle quantifies over an infinite enumerated "
           "trader family and never bounds what is live per date."),
    ("T1", "the coherence tolerance itself, as distinct from MI-6's solver "
           "budget."),
    ("T2", "certification layering. The bundle has no notion of who carries a "
           "breach."),
    ("F1", "request-keyed subsidy."),
    ("F2", "stopping neutrality."),
    ("F3", "probe blackout."),
    ("F4", "funder provenance."),
    ("S8-logical", "proof-carrying pins. The bundle's process emits sentences, "
                   "and nothing asks it for derivations."),
)


def mapping_findings() -> tuple[ConditionMapping, ...]:
    """The conditions whose mapping is a finding rather than a correspondence."""
    return tuple(m for m in MOVING_INTERFACE_MAP
                 if m.relation in (NO_COUNTERPART, IMPLIES_SI, NEITHER))


def mapping_is_identity() -> bool:
    """Is the mapping an identity?  Recorded so the prediction can be scored."""
    return all(m.relation == EQUIVALENT for m in MOVING_INTERFACE_MAP)


# --------------------------------------------------------------------------
# The parametric theorem
# --------------------------------------------------------------------------

# Clauses the composite consumes as *checked* facts about the engine.
CONSUMED_CLAUSES: tuple[str, ...] = (
    "J1", "J2", "J3", "C1-empirical", "C2", "C3", "P1", "P2", "P3", "P4", "T1",
    "T2", "S8-logical",
)

# Clauses the composite consumes as declared hypothesis objects.
DECLARED_CLAUSES_REQUIRED: tuple[str, ...] = (
    "C1-logical", "P1-persistence", "P4-semantics",
)

# Hypotheses with no interface counterpart, carried explicitly because the
# mapping table found no clause that supplies them.
UNCOVERED_HYPOTHESES: tuple[str, ...] = (
    "MI-2-prefix-causal-publication",
    "MI-4-coherent-witness-extension",
    "MI-5-summable-drift",
    "MI-6-constrained-quote-error-budget",
)

# The audit's named conditionals, carried explicitly.
AUDIT_CONDITIONALS: tuple[str, ...] = (
    "consistency-of-declared-theory",
    "core-minimum-or-clipping-adapter",
    "working-tolerance",
)

# Mechanism-side hypotheses of the corpus composite that are not engine clauses.
MECHANISM_HYPOTHESES: tuple[str, ...] = (
    "jointly-serviceable-terminal-certificate",
    "market-mechanism-noninterference",
    "event-order-and-refusal-contract",
)


@dataclass(frozen=True)
class MechanismParameters:
    """The mechanism-side constants the wealth bound is stated in.

    `quote_error_total` is the summable quote-error total; `risk_limit` is the
    worldwise aggregate risk guard; `ordinary_movement` is the ordinary adverse
    movement budget; `book_changes` is the potential bound on active-book
    changes.  Names follow the joint theory, whose recursion is imported rather
    than reimplemented.
    """

    quote_error_total: Q = Q(0)
    risk_limit: Q = Q(2)
    ordinary_movement: Q = Q(0)
    book_changes: int = 1

    def well_formed(self) -> bool:
        return (Q(self.quote_error_total) >= 0 and Q(self.risk_limit) >= 0
                and Q(self.ordinary_movement) >= 0 and self.book_changes >= 0)


@dataclass(frozen=True)
class CompositeVerdict:
    """What the parametric theorem yields on a given engine and record.

    `bound` is present exactly when every hypothesis is discharged.  A missing
    hypothesis produces `None` and a named list, never a number: the point of
    making the theorem consume the interface is that it cannot quietly report a
    cap it has not earned.
    """

    engine_id: str
    holds: bool
    bound: Q | None
    movement_cap: Q | None
    core_minimum: Q | None
    failing_clauses: tuple[str, ...]
    missing_hypotheses: tuple[str, ...]
    leaned_on: tuple[str, ...]
    obstructions: tuple[str, ...]


def parametric_composite(engine: EngineDeclaration, record: SettlementRecord,
                         mechanism: MechanismParameters,
                         hypotheses: Sequence[DeclaredHypothesis] = (),
                         ) -> CompositeVerdict:
    """`NL-J3` restated over any engine satisfying the relevant clauses.

    **Statement.**  Let `K` be a finite flow mechanism and challenger class
    satisfying the hypotheses of the corpus's finite reason-governed process
    result, together with that result's mechanism-side hypotheses.  Let `e` be a
    settlement engine and `R` a finite record prefix such that

      (a) `e` satisfies the checkable clauses J1, J2, J3, C1-empirical, C2, C3,
          P1, P2, P3, P4, T1, T2 and the proof-carrying pin requirement on `R`;
      (b) hypothesis objects are supplied for C1-logical, P1-persistence and
          P4-semantics;
      (c) hypothesis objects are supplied for the four bundle conditions the
          mapping table found no interface counterpart for; and
      (d) hypothesis objects are supplied for the audit's three conditionals:
          consistency of the declared theory, the core minimum or the clipping
          adapter, and a working tolerance.

    Then every conclusion of the corpus composite holds, and in particular for
    every represented world and every horizon the operative-force wealth bound

        quote_error_total / theta_min  +  kappa * ( risk_limit + movement cap )

    holds with `theta_min` the engine's certified core minimum, `kappa` the
    factor `(1 - theta_min) / theta_min`, and the movement cap the corpus
    recursion evaluated at the potential bound on active-book changes.

    **Proof.**  Substitution.  The corpus composite's hypothesis 3 -- a uniform
    positive core on every activated endpoint -- is discharged by (a)'s P1
    together with (b)'s persistence hypothesis, since P1 is precisely the
    statement that a reference admitting the declared coefficient exists at each
    recorded date, and persistence extends it beyond the prefix.  Hypothesis 5,
    the worldwise aggregate risk guard, is discharged by P2, whose declared limit
    is that guard.  Hypothesis 4 is (c)'s quote-error budget and hypothesis 6 is
    (c)'s drift schedule; neither has an interface counterpart, which is why they
    are hypotheses here rather than clauses.  The remaining hypotheses are
    mechanism-side and are carried unchanged.  With every hypothesis in place the
    corpus composite applies verbatim, and its wealth bound is the displayed one
    with the engine's certified coefficient substituted.  Nothing new is proved;
    what changes is that the antecedent is now evaluated rather than assumed.
    """
    if not mechanism.well_formed():
        raise ValueError("the mechanism parameters must be nonnegative")
    report = evaluate_interface(engine, record, hypotheses)
    by_clause = report.by_clause
    failing = tuple(name for name in CONSUMED_CLAUSES
                    if name in by_clause and not by_clause[name].holds)
    missing = [name for name in DECLARED_CLAUSES_REQUIRED
               if name in by_clause and not by_clause[name].holds]
    supplied = {h.clause for h in hypotheses}
    for name in UNCOVERED_HYPOTHESES + AUDIT_CONDITIONALS + MECHANISM_HYPOTHESES:
        if name not in supplied:
            missing.append(name)
    theta = engine.core_minimum
    if theta is None or Q(theta) <= 0:
        failing = failing + ("P1",) if "P1" not in failing else failing
    if failing or missing:
        return CompositeVerdict(
            engine.engine_id, False, None, None,
            None if theta is None else Q(theta), failing, tuple(missing),
            report.leaned_on, report.obstructions)
    theta = Q(theta)
    caps = movement_recursion(theta, Q(mechanism.quote_error_total),
                              Q(mechanism.risk_limit),
                              Q(mechanism.ordinary_movement),
                              mechanism.book_changes)
    movement_cap = caps[mechanism.book_changes]
    bound = uniform_wealth_cap(theta, Q(mechanism.quote_error_total),
                               Q(mechanism.risk_limit), movement_cap)
    return CompositeVerdict(engine.engine_id, True, bound, movement_cap, theta,
                            (), (), report.leaned_on, ())


def composite_hypotheses(declared_by: str) -> tuple[DeclaredHypothesis, ...]:
    """Every hypothesis object the parametric theorem needs, with its statement.

    Supplying this set is what it *means* to assert the composite of an engine.
    Reading it is the disclosure: nothing on this list was checked.
    """
    statements: Mapping[str, str] = {
        "C1-logical":
            "the declared deductive process eventually proves or refutes every "
            "sentence of the declared logical jurisdiction, with no rate promised",
        "P1-persistence":
            "the certified core minimum remains satisfiable at every future date "
            "as settlement contracts the region",
        "P4-semantics":
            "the named certificate type's semantics hold of this engine's "
            "pricing process on every history",
        "MI-2-prefix-causal-publication":
            "each date publishes its rational compact convex region before demand",
        "MI-4-coherent-witness-extension":
            "the retained world mixture extends coherently to fresh queried "
            "sentences",
        "MI-5-summable-drift":
            "reference drift is bounded by a computable schedule with finite total",
        "MI-6-constrained-quote-error-budget":
            "the constrained quote's errors sum to a finite total",
        "consistency-of-declared-theory":
            "the declared theory is consistent, so no report variable receives a "
            "second pin and the write-once guarantee is not routed to the breach "
            "stack",
        "core-minimum-or-clipping-adapter":
            "either the engine's certified core minimum is stably satisfiable, or "
            "the mechanism runs the clipping adapter and treats an empty "
            "admissible region as a detected breach",
        "working-tolerance":
            "at every date at which a merits certificate issues, the governing "
            "tolerance is working for the displayed book -- engine-certified, or "
            "book-declared under the certification layering",
        "jointly-serviceable-terminal-certificate":
            "the mechanism's jointly serviceable terminal certificate",
        "market-mechanism-noninterference":
            "the market and mechanism noninterference and account-assignment "
            "contracts",
        "event-order-and-refusal-contract":
            "the mechanism's event order and refusal contract",
    }
    return tuple(DeclaredHypothesis(f"H:{clause}", clause, statement, declared_by)
                 for clause, statement in statements.items())


# --------------------------------------------------------------------------
# The instance corollary
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class PairHypothesis:
    """The witness audit's pair, carried as a hypothesis object.

    The audit establishes by reading, not by construction, that the pair of a
    declared deductive process and a market satisfying the induction criterion
    inhabits the interface less the tolerance clause, the proof-carrying pin
    requirement, and the deduction-budget requirements.  Nothing in this tree
    constructs that pair, and this type is the disclosure of that fact.
    """

    hypothesis_id: str
    inhabited_clauses: tuple[str, ...]
    outside: tuple[str, ...]
    source: str


AUDITED_PAIR = PairHypothesis(
    "H:audited-pair",
    ("J1", "J2", "J3", "C1-logical", "C2", "C3", "P1", "P2", "P3", "P4", "T2"),
    ("T1", "S8-logical", "deduction-budget-requirements"),
    "the witness audit of the interface against the induction paper")


@dataclass(frozen=True)
class InstanceCorollary:
    holds: bool
    bound: Q | None
    named_conditionals: tuple[str, ...]
    missing: tuple[str, ...]
    disclosure: tuple[str, ...]


def instance_corollary(pair: PairHypothesis, mechanism: MechanismParameters,
                       core_minimum: Q,
                       consistency: DeclaredHypothesis | None,
                       floor_or_clip: DeclaredHypothesis | None,
                       working_tolerance: DeclaredHypothesis | None,
                       ) -> InstanceCorollary:
    """The audited pair meets the parametric theorem, modulo three conditionals.

    **Statement.**  Let the pair be as the witness audit describes it.  Then the
    parametric composite applies to it, with the wealth bound instantiated at the
    declared core minimum, **provided** three things the audit left conditional:
    consistency of the declared theory; either a stably satisfiable core minimum
    or the clipping adapter; and a working tolerance, which for this pair is
    available only by the certification-layering route, the book declaring a
    tighter tolerance and carrying the liability.

    This is the honest current form of the witness theorem's payoff.  It is a
    conditional whose antecedents are named, and the three conditionals are
    exactly the ones the audit could not discharge.  In particular the tolerance
    conditional is not a formality: the audit's sharpest finding is that this
    engine's only *sound* declaration is the maximal one, under which no merits
    certificate ever clears, so the working tolerance must come from the book.
    """
    named = AUDIT_CONDITIONALS
    supplied = {
        "consistency-of-declared-theory": consistency,
        "core-minimum-or-clipping-adapter": floor_or_clip,
        "working-tolerance": working_tolerance,
    }
    missing = tuple(name for name, value in supplied.items()
                    if value is None or value.clause != name)
    disclosure = (
        f"the pair inhabits {len(pair.inhabited_clauses)} clauses by reading, not "
        "by construction; nothing here builds it",
        f"outside the inhabited set: {', '.join(pair.outside)}",
        "the working tolerance for this pair is available only by the "
        "certification-layering route",
    )
    if missing or Q(core_minimum) <= 0 or not mechanism.well_formed():
        return InstanceCorollary(False, None, named, missing, disclosure)
    theta = Q(core_minimum)
    caps = movement_recursion(theta, Q(mechanism.quote_error_total),
                              Q(mechanism.risk_limit),
                              Q(mechanism.ordinary_movement),
                              mechanism.book_changes)
    bound = uniform_wealth_cap(theta, Q(mechanism.quote_error_total),
                               Q(mechanism.risk_limit),
                               caps[mechanism.book_changes])
    return InstanceCorollary(True, bound, named, (), disclosure)
