import Cleanroom.Decision.DpCalibration.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Definition 10: trembles and limit calibration (algebraic limits), Lemma 2

T1 (the `LimitOC` definition of record) and T3(a) of [[dp-calibration-mandate]].

**The limit is algebraic.** `ν_{B,C^ε}(X)` is represented as a polynomial `nuPoly C B X` in `ε`
(from the path product: every draw weight `(1−ε)C(d)(a) + ε/|A_d|` is affine in `ε`), with
`eval ε (nuPoly C B X) = nu (tremble C ε) B X` on `[0, 1]`. The limiting conditional
`lim_{ε→0⁺} ν_ε(X ∩ O)/ν_ε(O)` is the quotient of the coefficients of `ε^k`, `k` the order of
`nuPoly O` at `0` (`limitCond`); this is the genuine lowest-order quotient because the order of
`nuPoly (X ∩ O)` is at least `k` (`natTrailingDegree_nuPoly_mono`), which follows from a purely
algebraic fact: every `leafLawPoly` is a product of polynomials with **positive trailing
coefficient** (`PosTrail`), a class closed under products and sums with no cancellation at the
lowest order. `Fidelity: variant: limit taken algebraically by lowest-order coefficients`; the
analytic upgrade (`|ν_ε(X∩O)/ν_ε(O) − limitCond| < δ` for small `ε`) is the T3(c) stretch and is
not needed for any theorem here.

* `tremble C ε h0 h1` — Definition 10's `C^ε` (every point trembled), a `Proc` for `0 ≤ ε ≤ 1`;
  `tremble_zero`, `tremble_fullSupport`.
* `leafLawPoly`, `nuPoly`, `payPoly`, `eval_nuPoly`, `eval_payPoly`.
* `PosTrail` and its closure lemmas; `nuPoly_posTrail`, `natTrailingDegree_nuPoly_mono`,
  `nuPoly_ne_zero_iff` ("`O` realized": some chance-positive leaf has its world in `O`),
  `nuPoly_ne_zero_iff_forall_pos` ("`ν_{C^ε}(O) > 0` for all `ε ∈ (0, 1]`").
* `limitCond`, `LimitOCAt`, `LimitOC` — the definition of record.
* `limitOC_imp_strictOC` — **Lemma 2 (⟹)**: limit calibration refines strict calibration.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## Trembles -/

section tremble

variable [∀ d, Nonempty (acts d)]

/-- **Definition 10's tremble `C^ε`**: `C^ε(d) := (1−ε)C(d) + ε·Unif(A_d)` at *every* point,
packaged as a distribution for `0 ≤ ε ≤ 1`.
Source: [[decision-problems-v2]] §3.1 Definition 10
Kind: D
Fidelity: exact -/
def tremble (C : Proc ι acts K) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Proc ι acts K :=
  fun d =>
    { w := fun a => (1 - ε) * (C d).w a + ε * (Fintype.card (acts d) : K)⁻¹
      nonneg := fun a => by
        have hc : (0 : K) ≤ (Fintype.card (acts d) : K)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
        have := (C d).nonneg a
        nlinarith
      sum_one := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, (C d).sum_one, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card (acts d) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        rw [mul_inv_cancel₀ this]; ring }

/-- The tremble's weights. Source: none: infrastructure. Kind: L -/
@[simp] theorem tremble_w (C : Proc ι acts K) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (d : ι)
    (a : acts d) :
    (tremble C ε h0 h1 d).w a = (1 - ε) * (C d).w a + ε * (Fintype.card (acts d) : K)⁻¹ := rfl

/-- `C^0 = C`. Source: [[decision-problems-v2]] Lemma 2 proof ("whose value at `0` is `μ_{B,C}`").
Kind: L -/
theorem tremble_zero (C : Proc ι acts K) : tremble C 0 le_rfl zero_le_one = C := by
  funext d; apply FinDistr.ext'; intro a; simp

/-- For `0 < ε ≤ 1` the tremble is full-support.
Source: [[decision-problems-v2]] §3.1 Definition 10 (trembles reach every action); mandate §3.4
Kind: L -/
theorem tremble_fullSupport (C : Proc ι acts K) (ε : K) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (tremble C ε h0.le h1).FullSupport := by
  intro d a
  simp only [tremble_w]
  have hc : (0 : K) < (Fintype.card (acts d) : K)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have h2 : 0 ≤ (1 - ε) * (C d).w a := mul_nonneg (by linarith) ((C d).nonneg a)
  nlinarith

/-- Under a full-support procedure every chance-positive leaf has positive mass.
Source: none: infrastructure
Kind: L -/
theorem leafLaw_pos_of_fullSupport {C : Proc ι acts K} (hC : C.FullSupport) :
    (T : Tree Ω ι acts K) → ∀ ℓ, 0 < chanceWeight T ℓ → 0 < leafLaw C T ℓ
  | Tree.leaf _ _, _, _ => one_pos
  | Tree.chance _ β child, ⟨i, ℓ⟩, h => by
      simp only [chanceWeight_chance] at h
      simp only [leafLaw_chance]
      have hi : 0 < β.w i := by
        rcases (β.nonneg i).lt_or_eq with hi | hi
        · exact hi
        · rw [← hi, zero_mul] at h; exact absurd h (lt_irrefl 0)
      have hrest : 0 < chanceWeight (child i) ℓ := by
        rcases (chanceWeight_nonneg (child i) ℓ).lt_or_eq with hc | hc
        · exact hc
        · rw [← hc, mul_zero] at h; exact absurd h (lt_irrefl 0)
      exact mul_pos hi (leafLaw_pos_of_fullSupport hC (child i) ℓ hrest)
  | Tree.decision d child, ⟨a, ℓ⟩, h => by
      simp only [chanceWeight_decision] at h
      simp only [leafLaw_decision]
      exact mul_pos (hC d a) (leafLaw_pos_of_fullSupport hC (child a) ℓ h)

end tremble

/-! ## Polynomials with positive trailing coefficient -/

section posTrail

/-- A polynomial is *positively trailing* if it is zero or its lowest-order coefficient is
positive. Products and sums of such polynomials are again such, and the order of a sum is the
minimum of the orders (no cancellation at the lowest order) — the algebra behind Definition 10's
"limits exist: ratios of polynomials".
Source: [[decision-problems-v2]] §3.1 Definition 10 ("limits exist: ratios of polynomials in
`ε`, by finiteness"); mandate §3.5
Kind: D -/
def PosTrail (p : Polynomial K) : Prop := p ≠ 0 → 0 < p.trailingCoeff

/-- `0` is positively trailing. Source: none: infrastructure. Kind: L -/
theorem PosTrail.zero : PosTrail (0 : Polynomial K) := fun h => absurd rfl h

/-- A non-negative constant is positively trailing. Source: none: infrastructure. Kind: L -/
theorem PosTrail.C {c : K} (hc : 0 ≤ c) : PosTrail (Polynomial.C c) := by
  intro h
  have hc' : c ≠ 0 := Polynomial.C_ne_zero.mp h
  rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_C, Polynomial.coeff_C_zero]
  exact lt_of_le_of_ne hc (Ne.symm hc')

/-- Products of positively trailing polynomials are positively trailing.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.mul {p q : Polynomial K} (hp : PosTrail p) (hq : PosTrail q) :
    PosTrail (p * q) := by
  intro h
  rw [Polynomial.trailingCoeff_mul]
  exact mul_pos (hp (left_ne_zero_of_mul h)) (hq (right_ne_zero_of_mul h))

/-- The core of the sum lemma: for `p ≠ 0` positively trailing and `q` positively trailing, some
`m ≤ ord p` has `(p + q).coeff m > 0` and all lower coefficients zero.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.add_core {p q : Polynomial K} (hp : PosTrail p) (hq : PosTrail q)
    (hp0 : p ≠ 0) :
    ∃ m, m ≤ p.natTrailingDegree ∧ 0 < (p + q).coeff m ∧ ∀ j < m, (p + q).coeff j = 0 := by
  by_cases hq0 : q = 0
  · subst hq0
    refine ⟨p.natTrailingDegree, le_rfl, ?_, fun j hj => ?_⟩
    · rw [add_zero]; exact hp hp0
    · rw [add_zero]; exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
  · have htp := hp hp0
    have htq := hq hq0
    rcases lt_trichotomy q.natTrailingDegree p.natTrailingDegree with hlt | heq | hgt
    · refine ⟨q.natTrailingDegree, hlt.le, ?_, fun j hj => ?_⟩
      · rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, zero_add]
        exact htq
      · rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hj.trans hlt),
          Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj, add_zero]
    · refine ⟨p.natTrailingDegree, le_rfl, ?_, fun j hj => ?_⟩
      · rw [Polynomial.coeff_add]
        have : q.coeff p.natTrailingDegree = q.trailingCoeff := by
          rw [Polynomial.trailingCoeff, heq]
        rw [this]
        exact add_pos htp htq
      · rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj,
          Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (heq ▸ hj), add_zero]
    · refine ⟨p.natTrailingDegree, le_rfl, ?_, fun j hj => ?_⟩
      · rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hgt, add_zero]
        exact htp
      · rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj,
          Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hj.trans hgt), add_zero]

/-- Sums of positively trailing polynomials are positively trailing.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.add {p q : Polynomial K} (hp : PosTrail p) (hq : PosTrail q) :
    PosTrail (p + q) := by
  intro hpq
  by_cases hp0 : p = 0
  · subst hp0; rw [zero_add] at hpq ⊢; exact hq hpq
  obtain ⟨m, -, hm, hlow⟩ := PosTrail.add_core hp hq hp0
  have hle : (p + q).natTrailingDegree ≤ m := Polynomial.natTrailingDegree_le_of_ne_zero hm.ne'
  have hge : m ≤ (p + q).natTrailingDegree := Polynomial.le_natTrailingDegree hpq hlow
  rw [Polynomial.trailingCoeff, le_antisymm hle hge]
  exact hm

/-- A positively trailing `p ≠ 0` plus a positively trailing `q` is non-zero.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.add_ne_zero {p q : Polynomial K} (hp : PosTrail p) (hq : PosTrail q)
    (hp0 : p ≠ 0) : p + q ≠ 0 := by
  obtain ⟨m, -, hm, -⟩ := PosTrail.add_core hp hq hp0
  intro h
  rw [h, Polynomial.coeff_zero] at hm
  exact lt_irrefl 0 hm

/-- The order of `p + q` is at most the order of `p` (`p ≠ 0`, both positively trailing).
Source: none: infrastructure. Kind: L -/
theorem PosTrail.natTrailingDegree_add_le {p q : Polynomial K} (hp : PosTrail p)
    (hq : PosTrail q) (hp0 : p ≠ 0) : (p + q).natTrailingDegree ≤ p.natTrailingDegree := by
  obtain ⟨m, hmp, hm, -⟩ := PosTrail.add_core hp hq hp0
  exact (Polynomial.natTrailingDegree_le_of_ne_zero hm.ne').trans hmp

/-- Finite sums of positively trailing polynomials are positively trailing.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.sum {α : Type} (S : Finset α) (f : α → Polynomial K)
    (h : ∀ i ∈ S, PosTrail (f i)) : PosTrail (∑ i ∈ S, f i) :=
  Finset.sum_induction f PosTrail (fun _ _ => PosTrail.add) PosTrail.zero h

/-- A finite sum of positively trailing polynomials with a non-zero term is non-zero.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.sum_ne_zero {α : Type} [DecidableEq α] (S : Finset α) (f : α → Polynomial K)
    (h : ∀ i ∈ S, PosTrail (f i)) {i₀ : α} (hi₀ : i₀ ∈ S) (hf : f i₀ ≠ 0) :
    ∑ i ∈ S, f i ≠ 0 := by
  rw [← Finset.add_sum_erase S f hi₀]
  exact PosTrail.add_ne_zero (h i₀ hi₀)
    (PosTrail.sum _ f fun i hi => h i (Finset.mem_of_mem_erase hi)) hf

/-- The order of a sum of positively trailing polynomials is at most the order of any non-zero
term.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.natTrailingDegree_sum_le {α : Type} [DecidableEq α] (S : Finset α)
    (f : α → Polynomial K) (h : ∀ i ∈ S, PosTrail (f i)) {i₀ : α} (hi₀ : i₀ ∈ S)
    (hf : f i₀ ≠ 0) : (∑ i ∈ S, f i).natTrailingDegree ≤ (f i₀).natTrailingDegree := by
  rw [← Finset.add_sum_erase S f hi₀]
  exact PosTrail.natTrailingDegree_add_le (h i₀ hi₀)
    (PosTrail.sum _ f fun i hi => h i (Finset.mem_of_mem_erase hi)) hf

/-- **Subset monotonicity of the order**: for `S ⊆ T` and positively trailing terms, if the
sub-sum over `S` is non-zero then the order of the sum over `T` is at most that of the sum
over `S`.
Source: none: infrastructure (mandate §3.5: "`ord(nuPoly (X∩O)) ≥ ord(nuPoly O)`")
Kind: L -/
theorem PosTrail.natTrailingDegree_sum_mono {α : Type} [DecidableEq α] {S T : Finset α}
    (hST : S ⊆ T) (f : α → Polynomial K) (h : ∀ i ∈ T, PosTrail (f i))
    (hS : ∑ i ∈ S, f i ≠ 0) :
    (∑ i ∈ T, f i).natTrailingDegree ≤ (∑ i ∈ S, f i).natTrailingDegree := by
  rw [← Finset.sum_sdiff hST, add_comm]
  exact PosTrail.natTrailingDegree_add_le
    (PosTrail.sum _ f fun i hi => h i (hST hi))
    (PosTrail.sum _ f fun i hi => h i (Finset.mem_sdiff.mp hi).1) hS

end posTrail

/-! ## The run law under trembles as a polynomial in `ε` -/

section poly

variable [∀ d, Nonempty (acts d)]

/-- The tremble weight at `(d, a)` as a polynomial in `ε`:
`C(d)(a) + ε·(1/|A_d| − C(d)(a))`.
Source: [[decision-problems-v2]] §3.1 Definition 10; Lemma 2 proof ("a polynomial in `ε`")
Kind: D -/
noncomputable def trembleW (C : Proc ι acts K) (d : ι) (a : acts d) : Polynomial K :=
  Polynomial.C ((C d).w a) +
    Polynomial.C ((Fintype.card (acts d) : K)⁻¹ - (C d).w a) * Polynomial.X

/-- `eval ε (trembleW C d a) = C^ε(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem eval_trembleW (C : Proc ι acts K) (d : ι) (a : acts d) (ε : K) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) : (trembleW C d a).eval ε = (tremble C ε h0 h1 d).w a := by
  simp only [trembleW, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, tremble_w]
  ring

/-- `trembleW` has positive trailing coefficient: either `C(d)(a) > 0` (order `0`) or
`C(d)(a) = 0` and the polynomial is `ε/|A_d|` (order `1`).
Source: none: infrastructure. Kind: L -/
theorem posTrail_trembleW (C : Proc ι acts K) (d : ι) (a : acts d) : PosTrail (trembleW C d a) := by
  intro _
  have hcard : (0 : K) < (Fintype.card (acts d) : K)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hc0 : (trembleW C d a).coeff 0 = (C d).w a := by
    simp [trembleW, Polynomial.coeff_add, Polynomial.coeff_C]
  have hc1 : (trembleW C d a).coeff 1 = (Fintype.card (acts d) : K)⁻¹ - (C d).w a := by
    simp [trembleW, Polynomial.coeff_add, Polynomial.coeff_C]
  rcases ((C d).nonneg a).lt_or_eq with hpos | hzero
  · have hne : (trembleW C d a).coeff 0 ≠ 0 := by rw [hc0]; exact hpos.ne'
    have hdeg : (trembleW C d a).natTrailingDegree = 0 :=
      Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero hne)
    rw [Polynomial.trailingCoeff, hdeg, hc0]; exact hpos
  · have hne : (trembleW C d a).coeff 1 ≠ 0 := by rw [hc1, ← hzero, sub_zero]; exact hcard.ne'
    have hne0 : trembleW C d a ≠ 0 := fun h => hne (by rw [h, Polynomial.coeff_zero])
    have hle : (trembleW C d a).natTrailingDegree ≤ 1 :=
      Polynomial.natTrailingDegree_le_of_ne_zero hne
    have hge : 1 ≤ (trembleW C d a).natTrailingDegree := by
      apply Polynomial.le_natTrailingDegree hne0
      intro m hm
      have : m = 0 := by omega
      rw [this, hc0, ← hzero]
    rw [Polynomial.trailingCoeff, le_antisymm hle hge, hc1, ← hzero, sub_zero]; exact hcard

/-- `trembleW ≠ 0`. Source: none: infrastructure. Kind: L -/
theorem trembleW_ne_zero (C : Proc ι acts K) (d : ι) (a : acts d) : trembleW C d a ≠ 0 := by
  intro h
  have hcard : (0 : K) < (Fintype.card (acts d) : K)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hc0 : (trembleW C d a).coeff 0 = (C d).w a := by
    simp [trembleW, Polynomial.coeff_add, Polynomial.coeff_C]
  have hc1 : (trembleW C d a).coeff 1 = (Fintype.card (acts d) : K)⁻¹ - (C d).w a := by
    simp [trembleW, Polynomial.coeff_add, Polynomial.coeff_C]
  rw [h, Polynomial.coeff_zero] at hc0 hc1
  rw [← hc0, sub_zero] at hc1
  exact hcard.ne' hc1.symm

/-- **The run law under trembles, as a polynomial in `ε`**, by the same recursion as
`leafLaw`: chance weights become constants, draw weights become `trembleW`.
Source: [[decision-problems-v2]] §3.1 Lemma 2 proof ("Each leaf probability under `C^ε` is a
polynomial in `ε`")
Kind: D -/
noncomputable def leafLawPoly (C : Proc ι acts K) : (B : Tree Ω ι acts K) → B.Leaves → Polynomial K
  | .leaf _ _, _ => 1
  | .chance _ β child, ⟨i, ℓ⟩ => Polynomial.C (β.w i) * leafLawPoly C (child i) ℓ
  | .decision d child, ⟨a, ℓ⟩ => trembleW C d a * leafLawPoly C (child a) ℓ

/-- **`eval ε (leafLawPoly C B ℓ) = μ_{B,C^ε}(ℓ)`** for `ε ∈ [0, 1]`.
Source: [[decision-problems-v2]] §3.1 Lemma 2 proof
Kind: P
Fidelity: exact -/
theorem eval_leafLawPoly (C : Proc ι acts K) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (B : Tree Ω ι acts K) → ∀ ℓ, (leafLawPoly C B ℓ).eval ε = leafLaw (tremble C ε h0 h1) B ℓ
  | .leaf _ _, _ => by simp [leafLawPoly, leafLaw]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPoly, Polynomial.eval_mul, Polynomial.eval_C, leafLaw_chance]
      rw [eval_leafLawPoly C ε h0 h1 (child i) ℓ]
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLawPoly, Polynomial.eval_mul, leafLaw_decision]
      rw [eval_trembleW C d a ε h0 h1, eval_leafLawPoly C ε h0 h1 (child a) ℓ]

/-- `leafLawPoly` is positively trailing. Source: none: infrastructure. Kind: L -/
theorem posTrail_leafLawPoly (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ, PosTrail (leafLawPoly C B ℓ)
  | .leaf _ _, _ => by
      intro _
      rw [show (leafLawPoly C (.leaf _ _) _ : Polynomial K) = Polynomial.C 1 by
        simp [leafLawPoly]]
      exact PosTrail.C zero_le_one (by simp)
  | .chance _ β child, ⟨i, ℓ⟩ =>
      PosTrail.mul (PosTrail.C (β.nonneg i)) (posTrail_leafLawPoly C (child i) ℓ)
  | .decision d child, ⟨a, ℓ⟩ =>
      PosTrail.mul (posTrail_trembleW C d a) (posTrail_leafLawPoly C (child a) ℓ)

/-- `leafLawPoly C B ℓ ≠ 0` iff the leaf is chance-positive.
Source: none: infrastructure. Kind: L -/
theorem leafLawPoly_ne_zero_iff (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLawPoly C B ℓ ≠ 0 ↔ 0 < chanceWeight B ℓ
  | .leaf _ _, _ => by simp [leafLawPoly, chanceWeight]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPoly, chanceWeight_chance, mul_ne_zero_iff, Polynomial.C_ne_zero,
        leafLawPoly_ne_zero_iff C (child i) ℓ]
      constructor
      · rintro ⟨h1, h2⟩
        exact mul_pos (lt_of_le_of_ne (β.nonneg i) (Ne.symm h1)) h2
      · intro h
        refine ⟨fun h1 => ?_, ?_⟩
        · rw [h1, zero_mul] at h; exact lt_irrefl 0 h
        · rcases (chanceWeight_nonneg (child i) ℓ).lt_or_eq with hc | hc
          · exact hc
          · rw [← hc, mul_zero] at h; exact absurd h (lt_irrefl 0)
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLawPoly, chanceWeight_decision, mul_ne_zero_iff,
        leafLawPoly_ne_zero_iff C (child a) ℓ]
      exact ⟨fun h => h.2, fun h => ⟨trembleW_ne_zero C d a, h⟩⟩

/-- **`ν_{B,C^ε}(X)` as a polynomial in `ε`.**
Source: [[decision-problems-v2]] §3.1 Definition 10 ("ratios of polynomials in `ε`")
Kind: D -/
noncomputable def nuPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : Polynomial K :=
  ∑ ℓ ∈ worldEv B X, leafLawPoly C B ℓ

/-- `∑_{λ⊨X} μ_{C^ε}(ℓ) r(ℓ)` as a polynomial in `ε`.
Source: [[decision-problems-v2]] §3.1 Definition 10 (the `V`-clause's limit)
Kind: D -/
noncomputable def payPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : Polynomial K :=
  ∑ ℓ ∈ worldEv B X, leafLawPoly C B ℓ * Polynomial.C (payoff B ℓ)

/-- **`eval ε (nuPoly C B X) = ν_{B,C^ε}(X)`** on `[0, 1]`.
Source: [[decision-problems-v2]] §3.1 Definition 10; mandate §3.5
Kind: P
Fidelity: exact -/
theorem eval_nuPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) (ε : K)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : (nuPoly C B X).eval ε = nu (tremble C ε h0 h1) B X := by
  unfold nuPoly nu mass
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun ℓ _ => eval_leafLawPoly C ε h0 h1 B ℓ

/-- `eval ε (payPoly C B X) = paySum (C^ε) B X`. Source: mandate §3.5. Kind: L -/
theorem eval_payPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) (ε : K)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : (payPoly C B X).eval ε = paySum (tremble C ε h0 h1) B X := by
  unfold payPoly paySum
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun ℓ _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, eval_leafLawPoly C ε h0 h1 B ℓ]

/-- `nuPoly` is positively trailing. Source: none: infrastructure. Kind: L -/
theorem posTrail_nuPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    PosTrail (nuPoly C B X) :=
  PosTrail.sum _ _ fun ℓ _ => posTrail_leafLawPoly C B ℓ

/-- The trailing coefficient of a non-zero `nuPoly` is positive.
Source: none: infrastructure. Kind: L -/
theorem trailingCoeff_nuPoly_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω)
    (h : nuPoly C B X ≠ 0) : 0 < (nuPoly C B X).trailingCoeff :=
  posTrail_nuPoly C B X h

/-- **The order of `nuPoly (X ∩ O)` is at least the order of `nuPoly O`** (when the former is
non-zero): the trailing-coefficient quotient `limitCond` is the genuine lowest-order quotient.
Source: mandate §3.5 ("prove that `ord(nuPoly (X ∩ O)) ≥ ord(nuPoly O)`")
Kind: P
Fidelity: exact -/
theorem natTrailingDegree_nuPoly_mono (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω)
    (h : nuPoly C B (X ∩ O) ≠ 0) :
    (nuPoly C B O).natTrailingDegree ≤ (nuPoly C B (X ∩ O)).natTrailingDegree := by
  unfold nuPoly at h ⊢
  apply PosTrail.natTrailingDegree_sum_mono _ _ (fun ℓ _ => posTrail_leafLawPoly C B ℓ) h
  intro ℓ hℓ
  simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter] at hℓ ⊢
  exact hℓ.2

/-- Coefficients of `nuPoly (X ∩ O)` below the order of `nuPoly O` vanish.
Source: mandate §3.5. Kind: L -/
theorem coeff_nuPoly_inter_eq_zero_of_lt (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω)
    {j : ℕ} (hj : j < (nuPoly C B O).natTrailingDegree) : (nuPoly C B (X ∩ O)).coeff j = 0 := by
  by_cases h : nuPoly C B (X ∩ O) = 0
  · rw [h, Polynomial.coeff_zero]
  · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      (hj.trans_le (natTrailingDegree_nuPoly_mono C B X O h))

/-- **Coefficients of `payPoly X` below the order of `nuPoly X` vanish**: every summand
`leafLawPoly ℓ · r(ℓ)` of `payPoly X` has order at least that of `nuPoly X = ∑ leafLawPoly ℓ`
(positively trailing summands never cancel), so the payoff only rescales. This is the fact that
makes the cross-multiplied `V`-clause of `LimitOCAt` (and `limitVal`) the algebraic limit of
`𝔼_ε[r | X]`: `payPoly X / nuPoly X` has a finite limit at `ε → 0⁺`, namely the quotient of the
coefficients at the order `k'` of `nuPoly X`. (Audit round 1 adversarial N9 / round 2 fidelity
N6 asked for this lemma.)
Source: [[decision-problems-v2]] §3.1 Definition 10 (the `V`-clause's limit); mandate §3.5
Kind: P
Fidelity: exact -/
theorem coeff_payPoly_eq_zero_of_lt (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω)
    {j : ℕ} (hj : j < (nuPoly C B X).natTrailingDegree) : (payPoly C B X).coeff j = 0 := by
  unfold payPoly
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun ℓ hℓ => ?_
  rw [Polynomial.coeff_mul_C]
  by_cases h : leafLawPoly C B ℓ = 0
  · rw [h, Polynomial.coeff_zero, zero_mul]
  · have hle : (nuPoly C B X).natTrailingDegree ≤ (leafLawPoly C B ℓ).natTrailingDegree := by
      have := PosTrail.natTrailingDegree_sum_mono (Finset.singleton_subset_iff.mpr hℓ)
        (leafLawPoly C B) (fun ℓ' _ => posTrail_leafLawPoly C B ℓ')
        (by rwa [Finset.sum_singleton])
      rw [Finset.sum_singleton] at this
      exact this
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hj.trans_le hle), zero_mul]

/-- **"`O` realized"**: `nuPoly C B O ≠ 0` iff some chance-positive leaf has its world in `O`
(independently of `C`).
Source: mandate §3.5 ("equivalently 'some chance-positive leaf has its world in `O_d`'")
Kind: L -/
theorem nuPoly_ne_zero_iff (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω) :
    nuPoly C B O ≠ 0 ↔ ∃ ℓ, world B ℓ ∈ O ∧ 0 < chanceWeight B ℓ := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply h
    unfold nuPoly
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    by_contra hne
    exact absurd ((leafLawPoly_ne_zero_iff C B ℓ).mp hne) (not_lt.mpr (hc ℓ hℓ))
  · rintro ⟨ℓ, hℓ, hpos⟩
    unfold nuPoly
    exact PosTrail.sum_ne_zero _ _ (fun ℓ' _ => posTrail_leafLawPoly C B ℓ')
      (by simp [worldEv, hℓ]) ((leafLawPoly_ne_zero_iff C B ℓ).mpr hpos)

/-- **"`ν_{C^ε}(O) > 0` for all small `ε`"** is `nuPoly O ≠ 0`: precisely, `nuPoly C B O ≠ 0`
iff `ν_{B,C^ε}(O) > 0` for every `ε ∈ (0, 1]` (and then for every such `ε`, not just small
ones).
Source: [[decision-problems-v2]] §3.1 Definition 10 ("with `ν_{B,C^ε}(O_d) > 0` for all small
`ε`"); mandate §3.5
Kind: L
Fidelity: exact -/
theorem nuPoly_ne_zero_iff_forall_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω) :
    nuPoly C B O ≠ 0 ↔ ∀ ε : K, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), 0 < nu (tremble C ε h0.le h1) B O := by
  constructor
  · intro h ε h0 h1
    obtain ⟨ℓ, hℓ, hpos⟩ := (nuPoly_ne_zero_iff C B O).mp h
    have hfull := tremble_fullSupport C ε h0 h1
    have hlpos := leafLaw_pos_of_fullSupport hfull B ℓ hpos
    unfold nu mass
    apply lt_of_lt_of_le hlpos
    apply Finset.single_le_sum (fun ℓ' _ => leafLaw_nonneg _ B ℓ') (by simp [worldEv, hℓ])
  · intro h hzero
    have := h (1/2) (by norm_num) (by norm_num)
    rw [← eval_nuPoly C B O (1/2) (by norm_num) (by norm_num), hzero, Polynomial.eval_zero] at this
    exact lt_irrefl 0 this

end poly

/-! ## Definition 10: limit calibration -/

section limitOC

variable [∀ d, Nonempty (acts d)]

/-- **The limiting conditional probability `lim_{ε→0⁺} ν_{C^ε}(X | O)`**, taken algebraically:
the quotient of the coefficients of `ε^k` in `nuPoly (X ∩ O)` and `nuPoly O`, where `k` is the
order of `nuPoly O` at `0`. Meaningful when `nuPoly O ≠ 0` (then the denominator is positive,
`trailingCoeff_nuPoly_pos`, and the lower coefficients of the numerator vanish,
`coeff_nuPoly_inter_eq_zero_of_lt`); `0` otherwise, a junk value no definition of record reads
outside the guard `nuPoly O ≠ 0`.
Source: [[decision-problems-v2]] §3.1 Definition 10 (`lim_{ε→0⁺} ν_{B,C^ε}(X ∣ O_d)`)
Kind: D
Fidelity: variant: limit taken algebraically by lowest-order coefficients -/
noncomputable def limitCond (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω) : K :=
  (nuPoly C B (X ∩ O)).coeff (nuPoly C B O).natTrailingDegree /
    (nuPoly C B O).coeff (nuPoly C B O).natTrailingDegree

/-- **Definition 10 at one point** (the definition of record): if `O_d` is tremble-realizable
(`nuPoly O_d ≠ 0`, equivalently `ν_{C^ε}(O_d) > 0` for small `ε`), then (1)
`P_{s_d}(X) = limitCond X O_d` for all `X`, and (2) for every `X` of non-vanishing limiting
conditional probability, `V_{s_d}(X)` is the limiting conditional expectation, cross-multiplied:
`V_{s_d}(X) · c_{k'}(nuPoly (X ∧ O_d)) = c_{k'}(payPoly (X ∧ O_d))` with `k'` the order of
`nuPoly (X ∧ O_d)` (whose coefficient there is positive).
Source: [[decision-problems-v2]] §3.1 Definition 10
Kind: D
Fidelity: variant: limit taken algebraically by lowest-order coefficients; `V`-clause
cross-multiplied against the positive trailing coefficient -/
def LimitOCAt (s : ι → State Ω K) (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) : Prop :=
  nuPoly C B (obs d) ≠ 0 →
    (∀ X, (s d).pr X = limitCond C B X (obs d)) ∧
    (∀ X, 0 < limitCond C B X (obs d) →
      (s d).V X * (nuPoly C B (X ∩ obs d)).coeff (nuPoly C B (X ∩ obs d)).natTrailingDegree =
        (payPoly C B (X ∩ obs d)).coeff (nuPoly C B (X ∩ obs d)).natTrailingDegree)

/-- **Definition 10: `B` is limit-calibrated for `C`** — `LimitOCAt` at every queried point.
Source: [[decision-problems-v2]] §3.1 Definition 10
Kind: D
Fidelity: variant: limit taken algebraically by lowest-order coefficients -/
def LimitOC (s : ι → State Ω K) (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) : Prop :=
  ∀ d ∈ queried B, LimitOCAt s obs C B d

/-- `nuPoly` at `ε = 0` is `ν_C`: the constant coefficient is `ν_{B,C}(X)`.
Source: [[decision-problems-v2]] Lemma 2 proof ("whose value at `0` is `μ_{B,C}(ℓ)`")
Kind: L -/
theorem coeff_zero_nuPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    (nuPoly C B X).coeff 0 = nu C B X := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_nuPoly C B X 0 le_rfl zero_le_one, tremble_zero]

/-- `payPoly` at `ε = 0` is `paySum C`. Source: none: infrastructure. Kind: L -/
theorem coeff_zero_payPoly (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    (payPoly C B X).coeff 0 = paySum C B X := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_payPoly C B X 0 le_rfl zero_le_one, tremble_zero]

/-- Where `ν_C(O) > 0`, `nuPoly O` has order `0` and non-zero constant term.
Source: [[decision-problems-v2]] Lemma 2 proof
Kind: L -/
theorem natTrailingDegree_nuPoly_eq_zero (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) : (nuPoly C B O).natTrailingDegree = 0 ∧ nuPoly C B O ≠ 0 := by
  have hne : (nuPoly C B O).coeff 0 ≠ 0 := by rw [coeff_zero_nuPoly]; exact h.ne'
  refine ⟨Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero hne), ?_⟩
  intro hz; rw [hz, Polynomial.coeff_zero] at hne; exact hne rfl

/-- Where `ν_C(O) > 0` the limiting conditional is the strict one:
`limitCond X O = ν_C(X ∩ O) / ν_C(O)`.
Source: [[decision-problems-v2]] Lemma 2 proof ("the limiting conditionals are the strict ones")
Kind: L -/
theorem limitCond_eq_of_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω)
    (h : 0 < nu C B O) : limitCond C B X O = nu C B (X ∩ O) / nu C B O := by
  unfold limitCond
  rw [(natTrailingDegree_nuPoly_eq_zero C B O h).1, coeff_zero_nuPoly, coeff_zero_nuPoly]

/-- **Lemma 2 (⟹), at a point**: limit calibration at `d` implies strict calibration at `d`.
Where `ν_C(O_d) > 0`, `nuPoly O_d` has non-zero constant term, so the trailing-coefficient
quotient is `ν_C(X ∧ O_d)/ν_C(O_d)`; and where moreover `ν_C(X ∧ O_d) > 0`, `nuPoly (X ∧ O_d)`
has order `0` too, so the limit `V`-clause at `X` is the strict one.
Source: [[decision-problems-v2]] §3.1 Lemma 2 ("If `B` is limit-calibrated for `C`, it is
strictly observation-calibrated for `C`")
Kind: P
Fidelity: exact (both clauses)
Hyps: (a) `LimitOCAt` -/
theorem limitOCAt_imp_strictOCAt (s : ι → State Ω K) (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) (h : LimitOCAt s obs C B d) : StrictOCAt s obs C B d := by
  intro hpos
  obtain ⟨hdeg, hne⟩ := natTrailingDegree_nuPoly_eq_zero C B (obs d) hpos
  obtain ⟨h1, h2⟩ := h hne
  refine ⟨fun X => ?_, fun X hX hXO => ?_⟩
  · rw [h1 X, limitCond_eq_of_pos C B X (obs d) hpos]
    exact div_mul_cancel₀ _ hpos.ne'
  · have hlc : 0 < limitCond C B X (obs d) := by rw [← h1 X]; exact hX
    have := h2 X hlc
    rwa [(natTrailingDegree_nuPoly_eq_zero C B (X ∩ obs d) hXO).1, coeff_zero_nuPoly,
      coeff_zero_payPoly] at this

/-- **Lemma 2 (⟹)**: limit calibration refines strict calibration.
Source: [[decision-problems-v2]] §3.1 Lemma 2
Kind: P
Fidelity: exact
Hyps: (a) `LimitOC` -/
theorem limitOC_imp_strictOC (s : ι → State Ω K) (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (h : LimitOC s obs C B) : StrictOC s obs C B :=
  fun d hd => limitOCAt_imp_strictOCAt s obs C B d (h d hd)

end limitOC

end Cleanroom.Decision.DpCalibration
