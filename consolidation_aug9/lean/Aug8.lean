import Mathlib.Data.Finset.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Substantive bounded formalization targets for the consolidation. -/

namespace ConsolidationAug8

open Finset

/-- Post-trade cumulative holdings through index `u`. -/
def holdings (x : ℕ → ℝ) (u : ℕ) : ℝ := ∑ t ∈ range (u + 1), x t

/-- Scalar coordinate form of the repaired summation-by-parts identity.
There are `n+1` trades and exactly `n` internal reference movements. -/
theorem summationByParts (x q : ℕ → ℝ) : ∀ n : ℕ,
    (∑ t ∈ range (n + 1), x t * q t) =
      holdings x n * q n +
        ∑ u ∈ range n, holdings x u * (q u - q (u + 1)) := by
  intro n
  induction n with
  | zero => simp [holdings]
  | succ n ih =>
      rw [sum_range_succ] at ih
      simp only [sum_range_succ]
      rw [← add_assoc, ih]
      simp only [holdings, sum_range_succ]
      ring

/-- Exact scalar-coordinate identity including execution prices. -/
theorem summationByPartsWithPrices (x q p : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ range (n + 1), x t * (q t - p t)) =
      (∑ t ∈ range (n + 1), x t * (q n - p t)) +
        ∑ u ∈ range n, holdings x u * (q u - q (u + 1)) := by
  rw [sum_congr rfl (fun i _ ↦ mul_sub (x i) (q i) (p i)),
      sum_congr rfl (fun i _ ↦ mul_sub (x i) (q n) (p i)),
      sum_sub_distrib, sum_sub_distrib]
  rw [summationByParts x q n]
  simp only [holdings, sum_mul]
  ring

/-- Equality between a sum of component peaks and a simultaneous aggregate
value forces every component to be at its own peak. -/
theorem peakAlignmentAtDate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value peak : ι → ℚ)
    (hle : ∀ i ∈ s, value i ≤ peak i) :
    (∑ i ∈ s, value i) = ∑ i ∈ s, peak i ↔
      ∀ i ∈ s, value i = peak i := by
  constructor
  · intro h i hi
    have hn : ∀ j ∈ s, 0 ≤ peak j - value j := by
      intro j hj
      exact sub_nonneg.mpr (hle j hj)
    have hz : ∑ j ∈ s, (peak j - value j) = 0 := by
      rw [sum_sub_distrib, h]
      ring
    have hterm : peak i - value i = 0 :=
      (sum_eq_zero_iff_of_nonneg hn).mp hz i hi
    linarith
  · intro h
    exact sum_congr rfl h

/-! ### Exact exhaustion time -/

/-- The atomic flow trigger at obligation `k`. -/
def FundingFailure (C I : ℕ → ℚ) (F₀ : ℚ) (k : ℕ) : Prop :=
  C k > F₀ + I k

/-- The least failing obligation, defined when a failure exists. -/
noncomputable def exhaustionTime (C I : ℕ → ℚ) (F₀ : ℚ)
    (h : ∃ k, FundingFailure C I F₀ k) : ℕ :=
  by classical exact Nat.find h

/-- Under the canonical flow hypotheses, `exhaustionTime` fails and every
earlier obligation is payable.  Monotonicity is part of the model statement;
leastness itself follows from well-ordering. -/
theorem exhaustionTime_spec (C I : ℕ → ℚ) (F₀ : ℚ)
    (_hC : Monotone C) (_hI : Monotone I) (_hC0 : C 0 = 0) (_hF : 0 ≤ F₀)
    (h : ∃ k, FundingFailure C I F₀ k) :
    FundingFailure C I F₀ (exhaustionTime C I F₀ h) ∧
      ∀ j < exhaustionTime C I F₀ h, ¬ FundingFailure C I F₀ j := by
  classical
  exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h (by simpa [exhaustionTime] using hj)⟩

/-- With zero inflow and constant positive charge, the canonical integer-floor formula
is exactly the least failure index. -/
theorem constantChargeExhaustionTime (F₀ γ : ℚ) (hF : 0 ≤ F₀) (hγ : 0 < γ) :
    let C : ℕ → ℚ := fun k => k * γ
    let I : ℕ → ℚ := fun _ => 0
    ∃ h : ∃ k, FundingFailure C I F₀ k,
      exhaustionTime C I F₀ h = ⌊F₀ / γ⌋₊ + 1 := by
  classical
  dsimp
  let m : ℕ := ⌊F₀ / γ⌋₊
  have hdiv_nonneg : 0 ≤ F₀ / γ := div_nonneg hF (le_of_lt hγ)
  have hm_le : (m : ℚ) ≤ F₀ / γ := Nat.floor_le hdiv_nonneg
  have hlt_succ : F₀ / γ < (m + 1 : ℕ) := by
    simpa [m] using (Nat.lt_floor_add_one (F₀ / γ))
  have hfail : FundingFailure (fun k : ℕ => (k : ℚ) * γ) (fun _ => 0) F₀ (m + 1) := by
    simp only [FundingFailure]
    simpa using (div_lt_iff₀ hγ).mp hlt_succ
  have h : ∃ k, FundingFailure (fun k : ℕ => (k : ℚ) * γ) (fun _ => 0) F₀ k :=
    ⟨m + 1, hfail⟩
  refine ⟨h, (Nat.find_eq_iff h).mpr ⟨hfail, ?_⟩⟩
  intro k hk
  simp only [FundingFailure, not_lt]
  have hk_le_m : k ≤ m := Nat.lt_succ_iff.mp hk
  have hkq_le : (k : ℚ) ≤ F₀ / γ := (Nat.cast_le.mpr hk_le_m).trans hm_le
  simpa using (le_div_iff₀ hγ).mp hkq_le

/-- Matched cumulative inflow makes the failure set empty at every date. -/
theorem matchedInflowHasNoExhaustionTime (C : ℕ → ℚ) (F₀ : ℚ) (hF : 0 ≤ F₀) :
    ¬ ∃ k, FundingFailure C C F₀ k := by
  intro h
  obtain ⟨k, hk⟩ := h
  simp only [FundingFailure] at hk
  linarith

/-! ### Peak synchronization -/

/-- For finite accounts over a finite horizon, the pooled peak equals the sum
of the attained account peaks exactly when all account peaks occur together. -/
theorem peakSynchronizationIff {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]
    (accounts : Finset ι) (dates : Finset τ) (demand : ι → τ → ℚ)
    (peak : ι → ℚ) (pooledPeak : ℚ)
    (hlocalUpper : ∀ i ∈ accounts, ∀ t ∈ dates, demand i t ≤ peak i)
    (_hlocalAttained : ∀ i ∈ accounts, ∃ t ∈ dates, demand i t = peak i)
    (hpooledUpper : ∀ t ∈ dates, ∑ i ∈ accounts, demand i t ≤ pooledPeak)
    (hpooledAttained : ∃ t ∈ dates, (∑ i ∈ accounts, demand i t) = pooledPeak) :
    pooledPeak = ∑ i ∈ accounts, peak i ↔
      ∃ t ∈ dates, ∀ i ∈ accounts, demand i t = peak i := by
  constructor
  · intro heq
    obtain ⟨t, ht, hsum⟩ := hpooledAttained
    refine ⟨t, ht, ?_⟩
    apply (peakAlignmentAtDate accounts (fun i => demand i t) peak
      (fun i hi => hlocalUpper i hi t ht)).mp
    calc
      ∑ i ∈ accounts, demand i t = pooledPeak := hsum
      _ = ∑ i ∈ accounts, peak i := heq
  · rintro ⟨t, ht, halign⟩
    have hpeak_le : (∑ i ∈ accounts, peak i) ≤ pooledPeak := by
      rw [← sum_congr rfl halign]
      exact hpooledUpper t ht
    obtain ⟨u, hu, hattain⟩ := hpooledAttained
    have hpool_le : pooledPeak ≤ ∑ i ∈ accounts, peak i := by
      rw [← hattain]
      exact sum_le_sum fun i hi => hlocalUpper i hi u hu
    exact le_antisymm hpool_le hpeak_le

/-! ### Orbit quotient and a name-sensitive counterexample -/

/-- Factoring through the orbit quotient is equivalent to invariance under
the entire group action. -/
theorem factorsThroughOrbit_iff {G X Y : Type*} [Group G] [MulAction G X]
    (F : X → Y) :
    (∃ f : MulAction.orbitRel.Quotient G X → Y,
        ∀ x, f (Quotient.mk'' x) = F x) ↔
      ∀ g : G, ∀ x : X, F (g • x) = F x := by
  constructor
  · rintro ⟨f, hf⟩ g x
    rw [← hf (g • x), ← hf x]
    apply congrArg f
    apply Quotient.sound'
    exact ⟨g, rfl⟩
  · intro hinv
    let f : MulAction.orbitRel.Quotient G X → Y :=
      Quotient.lift F (by
        intro a b hab
        change a ∈ MulAction.orbit G b at hab
        obtain ⟨g, hg⟩ := hab
        rw [← hg]
        exact hinv g b)
    exact ⟨f, fun x => rfl⟩

/-- A finite record with two literal names and Boolean field values. -/
abbrev TwoNameRecord := Fin 2 → Bool

/-- Sort-preserving renaming acts contravariantly on named fields. -/
instance : MulAction (Equiv.Perm (Fin 2)) TwoNameRecord where
  smul e r := fun i => r (e.symm i)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The functional that reads the value stored under the first literal name. -/
def firstLiteralValue (r : TwoNameRecord) : Bool := r 0

/-- Reading the lexicographically first literal name is computable from the
finite record but is not invariant under record renaming. -/
theorem firstLiteralValue_not_invariant :
    ¬ ∀ e : Equiv.Perm (Fin 2), ∀ r : TwoNameRecord,
      firstLiteralValue (e • r) = firstLiteralValue r := by
  intro h
  let r : TwoNameRecord := fun i => i = 0
  have bad := h (Equiv.swap (0 : Fin 2) 1) r
  change r 1 = r 0 at bad
  norm_num [r] at bad

end ConsolidationAug8
