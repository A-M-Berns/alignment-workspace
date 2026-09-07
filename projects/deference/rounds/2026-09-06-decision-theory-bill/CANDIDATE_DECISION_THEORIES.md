# Candidate decision theories, prosecuted

Labels: **LEAN** (`GatedChoice.lean`), **FIX** (exact fixture, named test), **PAPER**,
**EXT**, **OPEN**.  The bill is `DECISION_THEORY_BILL.md` §6: a sound Lipschitz adapter.

## 1. Measurement is not motivation — what is proved

The Progress statistic is the assessment.  It charges an inquiry response and a violation
identically (both up to `D`); it is a scalar because it is a *score*, not because the
agent should optimize it.

Two exact statements, no more:

- **`scalar_bribery`** (LEAN; `test_finite_scalar_bribery`, `test_bounded_penalty_is_the_same_failure`,
  FIX).  A *finite additive* scalar penalty `λ · loss` cannot uniformly make a constraint
  non-compensable under unbounded independent task stakes: a task stake exceeding `λ · D`
  on the forbidden response flips the choice.  Assumptions: the objective is additive, the
  penalty is finite, the forbidden response's task value is unbounded above or exceeds
  `λ D`.  A bounded penalty `P` is the case `λ D ≤ P`.
- **`gate_invariant`** (LEAN).  A within-domain argmax never consults a forbidden
  response's task value: a domain restriction is one clean realization of
  non-compensation.

What is **not** claimed: that non-compensation *is* domain restriction.  Lexicographic
or non-Archimedean orders, partial choice structures and veto systems realize the same
priority; a completion of a partial order need not be a scalar.  The architectural
claim that survives is:

> **Non-compensability must appear in the choice or admissibility ordering itself, not
> solely as a finitely exchangeable task-value term.**

This is the same fact PR89 found for costly conservatism (no non-scalar *trade-off* rule
over a product order) and PR90 found for `Φ_C` (no value-register bound on the value of
what the domain excludes): a rule that trades the constraint against task value at a
finite rate is what `scalar_bribery` defeats.

## 2. The candidates

### 2.1 Scalar utility with a normative penalty

Pays `(R)` only via the value route, which needs `εresp ≥ D` on any forbidden optimum
(`regret_dominance_vacuous_on_forbidden_optimum`).  Self-modification preserves the
scalar, the wrong invariant.  **Killer:** `scalar_bribery`.

### 2.2 Bounded scalar penalty

Identical, `λ D ≤ P`.

### 2.3 Hard admissibility gate + ordinary optimizer

Sound at every region point; **no Lipschitz constant** (`hardGate_discontinuous`,
LEAN; `test_hard_gate_has_no_lipschitz_constant`, FIX).  Fails (D1) at every positive
defect.

### 2.4 Soft (ramped) admissibility gate + ordinary optimizer

Pays `(R)` on the regime `total > 0` — `softGate_practicalCert` with the sharp constant
`(Σ_{∉A} pref)/(W δ)` (`softGate_massOff_le_sharp`).  Inquiry is the wrapper
`gateWithInquiry`, silent under margin.  Non-compensation: `gate_invariant`.
Conflicts: the compiler's `conflict` output maps to `⊥`, or `Adequate(⊥)` is compiled and
`⊥` is an ordinary response (`NORMATIVE_CHOICE_THEOREM.md` §4).  LI-realizable: the gate
reads scores; adequacy prices are one instance, and the ramp is the summer soft-threshold
weight in a new role.  **Costs:** `κ = P⁻/(W(δ) δ)` is charged through the amplification hypothesis and the
margin is a separate hypothesis on `u` (route A) or on `b` (route B)
(`DECISION_THEORY_BILL.md` §4–§5); the `ℓ¹`-Lipschitz constant of the normalized map is
not derived; empirical adequacy is outside the static theorem.  **Residual exposure:** endogenous
admissibility (§2.8).

### 2.5 Lexicographic / non-Archimedean utility

Constitution first, task second.  On a finite menu with a crisp first tier it *is* 2.3
and inherits the discontinuity; with a ramped first tier it is 2.4.  Representationally
one order; the cost is that every constitutional trade-off must be placed in the first
tier explicitly, which is PR89's "costly conservatism is charter content".  It is a
legitimate realization of non-compensation, not a scalarization.  No separate theorem.

### 2.6 Incomplete preference

A partial order with no completion pays `(R)` only after a choice rule is added.  The
rule may be a scalar, a lexicographic priority, a veto system, or a randomization over
maximal elements; only the first is a scalarization.  The requirement is that the rule
be *authorized* (charter content), since whoever supplies it supplies the trade-off.
Absorbed into 2.4/2.5/2.7 with an authorized completion; not a separate candidate.

### 2.7 Branchwise veto / Pareto chooser

`A^const = ∩_{γ ∈ Γ_charter} A^γ` with `A^γ` an adequate set: `q ∈ A^γ` iff `q` keeps
branch `γ` realizable and meets its baseline.  Pays `(R)` as 2.4.  What it adds is
**branch persistence** (`test_branch_persistence_adequate_set_form`, FIX): with the
index read from the prestate charter, an action that destroys a branch's realization is
*inadequate* for that branch and the intersection excludes it; with the index recomputed
from what remains realizable, the branch drops out and the action passes.  Stated as a
lemma in `CORRIGIBILITY_CONNECTION.md` §2.  Incomparable trades between branches stay
incomparable (`test_branch_incompleteness`) until an authorized completion.

### 2.8 Normatively gated bounded inductive rationality

`Oesterheld, Demski and Conitzer` (TARK 2023, EPTCS 379, pp. 421–440): an estimating
agent chooses `α^c_t ∈ DP_t` and estimates `α^e_t`; hypotheses have the same type; the
criterion is no overestimation in the limit plus coverage of every efficiently
computable hypothesis (rejected only finitely often, or its tested record tends to
`−∞`).  Consequence (their Section 6): where one option guarantees `l`, a BRIA obtains at
least `l`.  Rewards may depend on the agent's choice; `DP_t` may depend on past choices;
the agent is myopic by design; counterfactual rewards are undefined.

**What gating buys.**  Gating is a change of decision problem, `DP_t := gated menu`, and
BRIA's guarantee transfers to the gated sequence.  So

```
soft gate (Region, MarginMass)  ⇒  (R), hence Progress                     LEAN
BRIA on the gated sequence       ⇒  at least l where a gated option guarantees l   cited
```

is a valid composition of two results on two different objects; it is not a theorem of
this round.

**Where it fails — endogenous admissibility** (`test_dynamic`, FIX).  BRIA's decision
problems may depend on prior choices, so slow-lane restrictions *can* be encoded into the
sequence: that is domain typing (A), and it gives safety
(`test_untyped_gate_is_hacked`).  It does not give competence: the myopic learner is
legitimate and loses linearly to the legitimate policy that invests in an authorized
amendment (`test_myopic_regret_against_legitimate_comparators_is_linear`).  The failure
is exactly myopia with respect to how current choices determine future decision problems.

**The minimum extension the application needs.**  Hypotheses must propose *continuation
policies* over a horizon `h` and promise horizon-`h` returns; test sets become blocks of
`h` steps in which the recommended policy is run; the gate is applied stepwise inside a
block, truncating a policy that would violate to `⊥` so that its record reflects the
truncation.  This keeps the no-overestimation/coverage shape (records are realized
returns, no counterfactuals are needed to test) at three costs: commitment for `h` steps,
exploration cost of testing policies, and a guarantee only against policies actually
tested — coverage tests each infinitely often, which is BRIA's own answer.  Whether the
criterion's consequences (Section 6) survive for policy hypotheses is **OPEN**; nothing
positive is asserted.  This is the leading candidate for the dynamic theorem.

### 2.9 Certified decision market

Hypotheses `(q, R̂, c)`.  One wealth account for `R̂` and `c` recreates 2.1 inside the
market (`scalar_bribery` on the account).  Elimination on normative failure is a hard
gate on hypotheses and inherits 2.3's discontinuity unless ramped.  Delayed settlement
lets a hypothesis accumulate influence before `c` is scored; a per-round influence cap
is the same repair the enforcement layer uses.  **Certification is an external gate**:
whichever way `c` is scored, which candidates may execute is a gate reading a score.
The market packages 2.4 + 2.8 and adds nothing to the bill.

### 2.10 Reason-to-choice correspondence

`𝒞 : ReasonState → 𝒫(Q ∪ {⊥})` is the *type* the gate consumes.  Of the dispatch's laws:
representation invariance follows if `𝒞` factors through anchored adequacy sentences
under the faithful-transfer order embedding (EXT otherwise); monotonicity and defeat
locality hold by construction for an intersection of per-reason adequate sets; continuity
under revision is Integrity's carry; non-compensation is `gate_invariant`; comparative
reasons are an authorized completion; inquiry is `⊥`.  Useful as a type; not a new theory.

### 2.11 Reflective constitutional chooser

`NORMATIVE_CHOICE_THEOREM.md` §3: a representation (`collapse`), a domain condition,
and a countermodel (`test_7`).  No reflective theorem.

## 3. The static gate versus embedded decision theory

Everything in §2 is about one occasion with an exogenous adequate set.  Trigger
manipulation, capture of the evaluator, containment and future-changing actions are not
discharged by this interface.  They are *preconditions for the gate theorem*, not outside
the scope of embedded decision theory in general: an embedded chooser may need to reason
about influencing its principal, controlling future evidence, selecting its evaluator, and
altering its own future decision problem.  The gate says nothing about those; it says
what any such chooser must satisfy at each occasion.

## 4. Ranking

| candidate | pays `(R)` | corrigibility illuminated | hides | theorem | LI-realizable | worst countermodel |
|---|---|---|---|---|---|---|
| scalar penalty | value route only | — | the trade-off rate | `scalar_bribery` (−) | yes | bribery |
| bounded penalty | same | — | same | same | yes | bribery |
| hard gate | **no** | non-compensation | continuity | `hardGate_discontinuous` (−) | no | control 10 |
| **soft gate** | **yes**, `total > 0` | non-compensation | `Region`, `MarginMass`, `δ ≤ m/2`, inquiry | `softGate_practicalCert` | yes | endogenous admissibility |
| **abstract adapter** | **yes** | — | its own Lipschitz constant | `adapter_practicalCert` | any Lipschitz reader | — |
| lexicographic | as hard/soft | same | trade-offs in tier one | none new | as gate | same |
| incomplete preference | after an authorized completion | branch incomparability | the completion | none | — | needs a rule |
| branchwise veto | as soft gate | **branch persistence** | index provenance | `test_branch_persistence` | as gate | branch deletion |
| gated BRIA | via the gate | competence in the gate | myopia | composition only | yes | endogenous admissibility |
| certified market | via the gate | packaging | delayed settlement | none new | yes | wealth mixing |
| reason correspondence | it is the type | non-compensation | nothing | inherited laws | — | — |
| reflective chooser | via the gate | gate preservation | alphabet completeness | `collapse` (representation) | — | control 7 |

Compositional: **abstract adapter** (the bill), **soft gate** (its realization),
**anchored branch index** (corrigibility's adequate sets), **BRIA inside the gate**
(static competence), **policy-BRIA** (the dynamic candidate, open), **two-level domain
with strict-prestate authorization** (reflection as a domain condition).
