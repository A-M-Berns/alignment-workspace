import Cleanroom.Udt.UdtPolicyCalc.Defs

/-!
# `Cleanroom.Udt.UdtCondenseDd.Access`: the predictor-access model; Gap 1's readings (T1, T2)

Work package `udt-condense-dd` (faf-cleanroom run, 2026-09-30), targets T1 (the three access-type
readings of Gap 1) and T2 (perfect accuracy on full support ⟹ factoring; the off-support
counterexample is in `Witness.lean`). Sources: [[gap1-reframing-predictor-access]] §2–§4
(udt-rep-028, 029, 030); the corpus Lean `lean/UDT/OptimalPredictor.lean:102–130` (the stipulation
`isOptimalPredictor := factorsThroughPolicy`).

## Representation of record (mandate §3, layer A)

* A mechanism type `M` (arbitrary); the policy `pol : M → O → A` is a *data* field (`π_M`, the
  I/O function), the predictor `p : M → O → A` another. "Extensional" is then a property of the
  predictor, not of `M`.
* `Factors p pol` is the corpus's `factorsThroughPolicy` verbatim: `pol M₁ = pol M₂ → p M₁ = p M₂`.
* Errors and disagreements are `Finset`s (`errSet`, `disSet`); masses are `mass D.w` for the
  family's observation law `D : FinDist O`.

## Which reading each theorem formalizes ([[gap1-reframing-predictor-access]] §2)

* Reading (iii), extensional mechanism access: `Extensional`, `factors_of_extensional`,
  `extensional_of_factors` — factoring is *definitional* (`T`), and the corpus stipulation
  `corpus_optimal_predictor_gives_dd` is a squeeze over it (`S`).
* Reading (ii)-exact, family statistical access with perfect accuracy: `factors_of_accurate_of_fullSupport`
  (`P`, one line) and its support-relative form `eq_on_support_of_accurate` (`L`).
* Reading (ii)-approximate: `Approx.lean` (T3, T4). The minimality reading: `Minimal.lean` (T6).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Finset

set_option linter.unusedSectionVars false

/-! ### The predictor-access model -/

/-- **A predictor with access to mechanisms**: a mechanism type `M` with its I/O function `pol`
(`π_M`) and the environment's prediction function `p` (`p(M, o)`, predictions are actions). The
family's observation law `D : FinDist O` is kept separate because T4(b) varies it.
Source: [[gap1-reframing-predictor-access]] §2 (udt-rep-028)
Kind: D
Fidelity: exact
Hyps: n/a -/
structure PredictorAccess (M O A : Type) where
  /-- `π_M`: the I/O function of mechanism `M`. -/
  pol : M → O → A
  /-- `p(M, ·)`: the predictor's output on mechanism `M`. -/
  p : M → O → A

variable {M O A : Type}

/-- **`p` factors through the policy**: mechanisms with the same I/O function get the same
prediction function. This is the corpus's `factorsThroughPolicy` (`OptimalPredictor.lean:102`)
verbatim, and the conclusion of every reading of Gap 1.
Source: [[gap1-reframing-predictor-access]] §2 ("when `p(M, ·)` depends on `M` only through `π_M`"); `OptimalPredictor.lean:102`
Kind: D
Fidelity: exact
Hyps: n/a -/
def Factors (p pol : M → O → A) : Prop := ∀ M₁ M₂, pol M₁ = pol M₂ → p M₁ = p M₂

/-- **Reading (iii), extensional mechanism access**: the predictor computes its output from the I/O
function alone, `p M = F (pol M)` for one `F`.
Source: [[gap1-reframing-predictor-access]] §2 (iii), §3 Observation 1 (udt-rep-028)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Extensional (p pol : M → O → A) : Prop := ∃ F : (O → A) → O → A, ∀ m, p m = F (pol m)

/-- **Observation 1: an extensional predictor factors through the policy** — by construction, with
no information theory. A `T` row: the hypothesis is the conclusion restated.
Source: [[gap1-reframing-predictor-access]] §3 Observation 1 (udt-rep-028)
Kind: T
Fidelity: exact
Hyps: (a) -/
theorem factors_of_extensional {p pol : M → O → A} (h : Extensional p pol) : Factors p pol := by
  obtain ⟨F, hF⟩ := h
  intro M₁ M₂ hpol
  rw [hF, hF, hpol]

/-- **The converse: factoring is extensionality.** `Factors` says `p` is constant on policy classes,
so `F π := p (any mechanism with policy π)` (and `F π := π` off the range of `pol`) witnesses
`Extensional`. Hence reading (iii)'s "fairness is extensionality" and "the predictor factors" are
the same statement — which is why the corpus's `isOptimalPredictor := factorsThroughPolicy`
*assumed* its conclusion (udt-rep-028; findings §6.1–6.2).
Source: [[gap1-reframing-predictor-access]] §3 Observation 1 (udt-rep-028)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem extensional_of_factors {p pol : M → O → A} (h : Factors p pol) : Extensional p pol := by
  classical
  refine ⟨fun π => if hπ : ∃ m, pol m = π then p hπ.choose else π, fun m => ?_⟩
  have hm : ∃ m', pol m' = pol m := ⟨m, rfl⟩
  simp only [hm, ↓reduceDIte]
  exact h m hm.choose hm.choose_spec.symm

/-- **Reading (iii) is definitional**: `Extensional ↔ Factors`.
Source: [[gap1-reframing-predictor-access]] §3 Observation 1 (udt-rep-028)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem extensional_iff_factors (p pol : M → O → A) : Extensional p pol ↔ Factors p pol :=
  ⟨factors_of_extensional, extensional_of_factors⟩

/-- **The corpus stipulation, restated for the record** (`optimal_predictor_gives_dd`,
`OptimalPredictor.lean:123–131`): a predictor that *factors* (the corpus's definition of
"optimal") together with a mechanism-blind utility gives decision-determination of the utility.
The hypothesis `hopt` **is** the factoring the conjecture was meant to prove: this is the `S` row
of T1 ([[STANDARDS]] §6), kept next to the readings that replace it. The corpus's own audit
([[cleanup-audit-2026-08-05]]) already says so.
Source: `lean/UDT/OptimalPredictor.lean:118–131` (udt-rep-028; findings §6.2)
Kind: S
Fidelity: exact (the corpus theorem's shape: `U : M → Prediction → ℝ`, `hU` mechanism-blind)
Hyps: (a) `hopt` — but it is the conclusion of Gap 1 assumed; (a) `hU` -/
theorem corpus_optimal_predictor_gives_dd {p pol : M → O → A} (hopt : Factors p pol)
    (U : M → (O → A) → ℝ) (hU : ∀ M₁ M₂ q, pol M₁ = pol M₂ → U M₁ q = U M₂ q) :
    ∀ M₁ M₂, pol M₁ = pol M₂ → U M₁ (p M₁) = U M₂ (p M₂) := by
  intro M₁ M₂ h
  rw [hopt M₁ M₂ h, hU M₁ M₂ (p M₂) h]

/-! ### Error and disagreement sets -/

variable [Fintype O] [DecidableEq O] [DecidableEq A]

/-- **The error set of mechanism `m`**: the observations at which the prediction misses the
policy, `{o : p(M, o) ≠ π_M(o)}` (the note's `S_i`).
Source: [[gap1-reframing-predictor-access]] §4 Lemma (proof, `S_i`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def errSet (p pol : M → O → A) (m : M) : Finset O := event fun o => p m o ≠ pol m o

/-- **The disagreement set of two mechanisms**: `{o : p(M₁, o) ≠ p(M₂, o)}` (the note's `S`).
Source: [[gap1-reframing-predictor-access]] §4 Lemma (proof, `S`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def disSet (p : M → O → A) (m₁ m₂ : M) : Finset O := event fun o => p m₁ o ≠ p m₂ o

/-- Supporting lemma `mem_errSet`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_errSet {p pol : M → O → A} {m : M} {o : O} :
    o ∈ errSet p pol m ↔ p m o ≠ pol m o := by simp [errSet]

/-- Supporting lemma `mem_disSet`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_disSet {p : M → O → A} {m₁ m₂ : M} {o : O} :
    o ∈ disSet p m₁ m₂ ↔ p m₁ o ≠ p m₂ o := by simp [disSet]

/-- **`S ⊆ S₁ ∪ S₂`**: under a shared policy, a disagreement is an error of one of the two
mechanisms (the note's one-line argument).
Source: [[gap1-reframing-predictor-access]] §4 Lemma (proof)
Kind: L
Fidelity: exact
Hyps: none -/
theorem disSet_subset_union {p pol : M → O → A} {m₁ m₂ : M} (h : pol m₁ = pol m₂) :
    disSet p m₁ m₂ ⊆ errSet p pol m₁ ∪ errSet p pol m₂ := by
  intro o ho
  rw [mem_disSet] at ho
  rw [Finset.mem_union, mem_errSet, mem_errSet]
  by_cases h1 : p m₁ o = pol m₁ o
  · exact Or.inr fun h2 => ho (by rw [h1, h2, h])
  · exact Or.inl h1

/-- **The disagreement set is empty iff the prediction functions agree.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem disSet_eq_empty_iff {p : M → O → A} {m₁ m₂ : M} : disSet p m₁ m₂ = ∅ ↔ p m₁ = p m₂ := by
  constructor
  · intro h
    funext o
    by_contra hne
    have : o ∈ disSet p m₁ m₂ := mem_disSet.2 hne
    rw [h] at this
    exact absurd this (Finset.notMem_empty o)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro o ho
    exact (mem_disSet.1 ho) (by rw [h])

/-! ### T2: perfect accuracy on the support -/

omit [DecidableEq O] [DecidableEq A] in
/-- **Support-relative exactness** (the `L` form T5 uses): if every mechanism is exactly accurate on
the support of `D`, then two mechanisms with the same policy predict the same at every observation
of positive mass — off the support nothing is said (T2(b), `Witness.lean`).
Source: [[gap1-reframing-predictor-access]] §3 Observation 2, §4 (udt-rep-029, 036)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem eq_on_support_of_accurate {p pol : M → O → A} (D : FinDist O)
    (hacc : ∀ m o, 0 < D.w o → p m o = pol m o) {m₁ m₂ : M} (h : pol m₁ = pol m₂) (o : O)
    (ho : 0 < D.w o) : p m₁ o = p m₂ o := by
  rw [hacc m₁ o ho, hacc m₂ o ho, h]

omit [DecidableEq O] [DecidableEq A] in
/-- **Observation 2: perfect accuracy on a full-support family is factoring** (reading (ii)-exact).
One line: on full support the predictor *is* the policy.
Source: [[gap1-reframing-predictor-access]] §3 Observation 2 (udt-rep-029)
Kind: P
Fidelity: exact
Hyps: (a) `hfull`, (a) `hacc` -/
theorem factors_of_accurate_of_fullSupport {p pol : M → O → A} (D : FinDist O)
    (hfull : ∀ o, 0 < D.w o) (hacc : ∀ m o, 0 < D.w o → p m o = pol m o) : Factors p pol :=
  fun _ _ h => funext fun o => eq_on_support_of_accurate D hacc h o (hfull o)

/-- **The exact chain as the `δ = 0` corollary**: with full support and no errors (`errSet = ∅` for
every mechanism), the predictor factors. This is T3's `δ = 0` instance stated combinatorially.
Source: [[gap1-reframing-predictor-access]] §4 ("the exact chain as the `δ = 0` corollary")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem factors_of_errSet_empty {p pol : M → O → A} (h : ∀ m, errSet p pol m = ∅) :
    Factors p pol := by
  have hex : ∀ m o, p m o = pol m o := fun m o => by
    by_contra hne
    have : o ∈ errSet p pol m := mem_errSet.2 hne
    rw [h m] at this
    exact absurd this (Finset.notMem_empty o)
  intro m₁ m₂ hpol
  funext o
  rw [hex m₁ o, hex m₂ o, hpol]

end Cleanroom.Udt.UdtCondenseDd
