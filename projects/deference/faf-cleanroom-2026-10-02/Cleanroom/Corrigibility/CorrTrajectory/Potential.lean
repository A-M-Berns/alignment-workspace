import Cleanroom.Corrigibility.CorrTrajectory.Process

/-!
# `corr-trajectory` — `Potential`: D4/D5 in Layer F; the finite Ville inequality

The grades D4 (forward invariance with hazard) and D5 (potential = nonnegative supermartingale;
barrier certificate) over `FinFiltered`, in product form, and the two Layer-F theorems every
certificate of the package rests on:

* `expect_antitone_of_steps` — the expectation of a supermartingale is non-increasing;
* `ville_finite` — **Ville's inequality, finite form**: for a nonnegative supermartingale `Z`,
  `λ · P*(∃ t ≤ n, Z_t ≥ λ) ≤ E*[Z_0]`, by induction on `n` through the first-hitting decomposition.

D5's "`t` adjoined to the state" (adversary item 26 / 2-024(b)) is automatic here: a potential is
`Φ : ℕ → Ω → ℝ`, a function of the time index *and* the point, so no product state is invented.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

section Supermart

variable (μ : Distr Ω) (A : Atoms Ω)

/-- **One supermartingale step** at time `t`, product form: `E*[Z_{t+1} 1_{atom}] ≤ E*[Z_t 1_{atom}]`
on every atom of `𝓕_t`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md D5
Kind: D
Fidelity: exact (product form) -/
def SupermartStep (Z : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, condSum μ A t (Z (t + 1)) ω ≤ condSum μ A t (Z t) ω

/-- **D5, Layer F: a supermartingale** — adapted (`Z_t` is `𝓕_t`-measurable) with the step
inequality at every `t`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md D5
Kind: D
Fidelity: exact (product form) -/
structure IsSupermart (Z : ℕ → Ω → ℝ) : Prop where
  meas : ∀ t, A.Meas t (Z t)
  step : ∀ t, SupermartStep μ A Z t

/-- **D5: a potential** is a nonnegative supermartingale. The time index is "`t` adjoined to the
state" (2-024(b)): `Φ : ℕ → Ω → ℝ` already is a function of `(t, s_t)`.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md D5
Kind: D
Fidelity: exact -/
def IsPotential (Φ : ℕ → Ω → ℝ) : Prop := IsSupermart μ A Φ ∧ ∀ t ω, 0 ≤ Φ t ω

/-- **D5: a barrier certificate** for the catastrophe set `cat`: a potential with `Φ ≥ 1` on `Cat`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md D5
Kind: D
Fidelity: exact -/
def IsBarrier (cat : ℕ → Ω → Bool) (Φ : ℕ → Ω → ℝ) : Prop :=
  IsPotential μ A Φ ∧ ∀ t ω, cat t ω = true → 1 ≤ Φ t ω

/-- **D4: forward invariance with hazard** of a family of events `I t`, product form:
`P*(¬I_{t+1} ∧ I_t ∣ 𝓕_t) ≤ δ̄_t · P*(I_t ∣ 𝓕_t)` on every atom.
Source: [[corr-wf14-inventory]] 070, 080 / invariant-final.md D4, Statement 10(a)
Kind: D
Fidelity: exact (product form; the ratio `P(¬I_{t+1} ∣ 𝓕_t, I_t) ≤ δ̄_t` needs `P(I_t ∣ 𝓕_t) > 0`) -/
def forwardInvariantWithHazard (I : ℕ → Finset Ω) (δbar : ℕ → ℝ) : Prop :=
  ∀ t ω, condSum μ A t (fun ω' => ind (I t) ω' * (1 - ind (I (t + 1)) ω')) ω ≤
    δbar t * condSum μ A t (ind (I t)) ω

variable {μ A}

/-- The step inequality integrates: `E*[Z_{t+1}] ≤ E*[Z_t]` (no measurability needed).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_succ_le_of_step {Z : ℕ → Ω → ℝ} {t : ℕ} (h : SupermartStep μ A Z t) :
    expect μ (Z (t + 1)) ≤ expect μ (Z t) :=
  expect_le_of_condSum_le t h

/-- **The expectation of a supermartingale is non-increasing**: `E*[Z_n] ≤ E*[Z_0]` from the steps
below `n`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md proof of Statement 8(b) ("`E*[Z_{T+1}] ≤ Z_0`")
Kind: P (small; induction on the step inequality through the atom decomposition)
Fidelity: exact
Hyps: (a) only -/
theorem expect_antitone_of_steps {Z : ℕ → Ω → ℝ} (n : ℕ) (h : ∀ t < n, SupermartStep μ A Z t) :
    expect μ (Z n) ≤ expect μ (Z 0) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (expect_succ_le_of_step (h n (Nat.lt_succ_self n))).trans
      (ih fun t ht => h t (Nat.lt_succ_of_lt ht))

/-! ### The hitting set and Ville's inequality -/

/-- `hitSet Z λ n = {ω ∣ ∃ t ≤ n, λ ≤ Z_t ω}`: the running certificate has reached `λ` by time `n`.
Source: invariant-final.md Statement 8(b) (the event of the uniform bound)
Kind: D
Fidelity: exact -/
noncomputable def hitSet (Z : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) : Finset Ω :=
  (range (n + 1)).biUnion fun t => univ.filter fun ω => lam ≤ Z t ω

/-- `mem_hitSet` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_hitSet {Z : ℕ → Ω → ℝ} {lam : ℝ} {n : ℕ} {ω : Ω} :
    ω ∈ hitSet Z lam n ↔ ∃ t ≤ n, lam ≤ Z t ω := by
  simp [hitSet]

/-- `hitSet_subset_succ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hitSet_subset_succ (Z : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) : hitSet Z lam n ⊆ hitSet Z lam (n + 1) := by
  intro ω h
  rw [mem_hitSet] at *
  obtain ⟨t, ht, h'⟩ := h
  exact ⟨t, ht.trans (Nat.le_succ n), h'⟩

/-- `mem_hitSet_succ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_hitSet_succ {Z : ℕ → Ω → ℝ} {lam : ℝ} {n : ℕ} {ω : Ω} :
    ω ∈ hitSet Z lam (n + 1) ↔ ω ∈ hitSet Z lam n ∨ lam ≤ Z (n + 1) ω := by
  simp only [mem_hitSet]
  constructor
  · rintro ⟨t, ht, h⟩
    rcases Nat.lt_or_ge t (n + 1) with hlt | hge
    · exact Or.inl ⟨t, Nat.lt_succ_iff.1 hlt, h⟩
    · exact Or.inr (by rwa [le_antisymm ht hge] at h)
  · rintro (⟨t, ht, h⟩ | h)
    · exact ⟨t, ht.trans (Nat.le_succ n), h⟩
    · exact ⟨n + 1, le_rfl, h⟩

/-- Membership in `hitSet Z λ n` is `𝓕_n`-measurable when each `Z_t` (`t ≤ n`) is `𝓕_t`-measurable.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hitSet_meas {Z : ℕ → Ω → ℝ} {lam : ℝ} {n : ℕ} (hmeas : ∀ t ≤ n, A.Meas t (Z t))
    {ω ω' : Ω} (h : ω' ∈ A.fib n ω) : ω' ∈ hitSet Z lam n ↔ ω ∈ hitSet Z lam n := by
  simp only [mem_hitSet]
  constructor
  · rintro ⟨t, ht, h'⟩
    exact ⟨t, ht, by rwa [(hmeas t ht).mono ht ω ω' h] at h'⟩
  · rintro ⟨t, ht, h'⟩
    exact ⟨t, ht, by rwa [(hmeas t ht).mono ht ω ω' h]⟩

/-- The induction invariant behind Ville: `λ P(hit by m) + E[Z_m 1_{not hit by m}] ≤ E[Z_0]`.
Source: none: infrastructure (the first-hitting decomposition)
Kind: P (small)
Fidelity: n/a -/
lemma ville_invariant {Z : ℕ → Ω → ℝ} (lam : ℝ) (n : ℕ) (hZ : ∀ t ω, 0 ≤ Z t ω)
    (hmeas : ∀ t ≤ n, A.Meas t (Z t)) (hstep : ∀ t < n, SupermartStep μ A Z t) :
    ∀ m ≤ n, lam * probOf μ (hitSet Z lam m) +
      expect μ (fun ω => Z m ω * (1 - ind (hitSet Z lam m) ω)) ≤ expect μ (Z 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [probOf_eq_expect_ind, ← Found.CorrThreeStep.expect_const_mul, ← Found.CorrThreeStep.expect_add]
    refine Found.CorrThreeStep.expect_mono μ fun ω => ?_
    by_cases h : ω ∈ hitSet Z lam 0
    · have : lam ≤ Z 0 ω := by
        obtain ⟨t, ht, h'⟩ := mem_hitSet.1 h
        rwa [Nat.le_zero.1 ht] at h'
      simp [ind_of_mem h, this]
    · simp [ind_of_not_mem h]
  | succ m ih =>
    intro hm
    have ih' := ih (Nat.le_of_succ_le hm)
    -- (1) the supermartingale step with the `𝓕_m`-measurable factor `1 − 1_{hit by m}`
    have hind : A.Meas m (fun ω => 1 - ind (hitSet Z lam m) ω) := by
      intro ω ω' h
      dsimp only
      unfold ind
      rw [if_congr (hitSet_meas (fun t ht => hmeas t (ht.trans (Nat.le_of_succ_le hm))) h) rfl rfl]
    have hstep' : expect μ (fun ω => Z (m + 1) ω * (1 - ind (hitSet Z lam m) ω)) ≤
        expect μ (fun ω => Z m ω * (1 - ind (hitSet Z lam m) ω)) := by
      refine expect_le_of_condSum_le (A := A) m fun ω => ?_
      have e1 := condSum_mul_meas (μ := μ) m hind (Z (m + 1)) ω
      have e2 := condSum_mul_meas (μ := μ) m hind (Z m) ω
      simp only [mul_comm (1 - ind _ _)] at e1 e2
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_right (hstep m (Nat.lt_of_succ_le hm) ω) ?_
      linarith [ind_le_one (hitSet Z lam m) ω]
    -- (2) the pointwise first-hitting inequality
    have hpt : ∀ ω, lam * ind (hitSet Z lam (m + 1)) ω + Z (m + 1) ω * (1 - ind (hitSet Z lam (m + 1)) ω) ≤
        lam * ind (hitSet Z lam m) ω + Z (m + 1) ω * (1 - ind (hitSet Z lam m) ω) := by
      intro ω
      by_cases h1 : ω ∈ hitSet Z lam m
      · have h2 : ω ∈ hitSet Z lam (m + 1) := hitSet_subset_succ Z lam m h1
        simp [ind_of_mem h1, ind_of_mem h2]
      · by_cases h2 : ω ∈ hitSet Z lam (m + 1)
        · have : lam ≤ Z (m + 1) ω := by
            rcases mem_hitSet_succ.1 h2 with h | h
            · exact absurd h h1
            · exact h
          simp [ind_of_not_mem h1, ind_of_mem h2, this]
        · simp [ind_of_not_mem h1, ind_of_not_mem h2]
    calc lam * probOf μ (hitSet Z lam (m + 1)) +
          expect μ (fun ω => Z (m + 1) ω * (1 - ind (hitSet Z lam (m + 1)) ω))
        = expect μ (fun ω => lam * ind (hitSet Z lam (m + 1)) ω +
            Z (m + 1) ω * (1 - ind (hitSet Z lam (m + 1)) ω)) := by
          rw [probOf_eq_expect_ind, ← Found.CorrThreeStep.expect_const_mul,
            ← Found.CorrThreeStep.expect_add]
      _ ≤ expect μ (fun ω => lam * ind (hitSet Z lam m) ω +
            Z (m + 1) ω * (1 - ind (hitSet Z lam m) ω)) := Found.CorrThreeStep.expect_mono μ hpt
      _ = lam * probOf μ (hitSet Z lam m) +
            expect μ (fun ω => Z (m + 1) ω * (1 - ind (hitSet Z lam m) ω)) := by
          rw [probOf_eq_expect_ind, ← Found.CorrThreeStep.expect_const_mul,
            ← Found.CorrThreeStep.expect_add]
      _ ≤ lam * probOf μ (hitSet Z lam m) +
            expect μ (fun ω => Z m ω * (1 - ind (hitSet Z lam m) ω)) := by linarith
      _ ≤ expect μ (Z 0) := ih'

/-- **Ville's inequality, finite form (Layer F).** For a nonnegative process `Z` that is adapted
and a supermartingale below `n`, `λ · P*(∃ t ≤ n, Z_t ≥ λ) ≤ E*[Z_0]`. Mathlib has no Ville for
supermartingales; this is the finite induction the mandate names, and the Layer-M twin is
`Martingale.ville`.
Source: [[corr-wf14-inventory]] 077, 078 / invariant-final.md Statement 7(b), 8(b) ("Ville's inequality")
Kind: P (the first-hitting decomposition and the tower step, by induction)
Fidelity: exact (finite horizon; `λ` unrestricted — for `λ ≤ 0` the bound is trivial)
Hyps: (a) only -/
theorem ville_finite {Z : ℕ → Ω → ℝ} (lam : ℝ) (n : ℕ) (hZ : ∀ t ω, 0 ≤ Z t ω)
    (hmeas : ∀ t ≤ n, A.Meas t (Z t)) (hstep : ∀ t < n, SupermartStep μ A Z t) :
    lam * probOf μ (hitSet Z lam n) ≤ expect μ (Z 0) := by
  have h := ville_invariant lam n hZ hmeas hstep n le_rfl
  have h0 : 0 ≤ expect μ (fun ω => Z n ω * (1 - ind (hitSet Z lam n) ω)) :=
    Found.CorrThreeStep.expect_nonneg μ fun ω =>
      mul_nonneg (hZ n ω) (by linarith [ind_le_one (hitSet Z lam n) ω])
  linarith

/-- Ville for a global supermartingale, in the ratio form `P*(∃ t ≤ n, Z_t ≥ λ) ≤ E*[Z_0] / λ` for `λ > 0`.
Source: invariant-final.md Statement 8(b)
Kind: L (`ville_finite` divided)
Fidelity: exact -/
theorem ville_of_isSupermart {Z : ℕ → Ω → ℝ} (hZ : ∀ t ω, 0 ≤ Z t ω) (hsm : IsSupermart μ A Z)
    {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    probOf μ (hitSet Z lam n) ≤ expect μ (Z 0) / lam := by
  rw [le_div_iff₀ hlam, mul_comm]
  exact ville_finite lam n hZ (fun t _ => hsm.meas t) (fun t _ => hsm.step t)

/-- **A barrier certificate bounds the probability of ever entering `Cat` by `E*[Φ_0]`** (Ville at
`λ = 1`): `P*(∃ t ≤ n, Cat_t) ≤ E*[Φ_0]`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(b) ("Ville's inequality gives `P*(Cat ever) ≤ Δ`")
Kind: C (`ville_finite` + `Φ ≥ 1` on `Cat`)
Fidelity: exact (finite horizon `n`; "ever" is the `n`-uniform statement)
Hyps: (a) only -/
theorem barrier_bound {cat : ℕ → Ω → Bool} {Φ : ℕ → Ω → ℝ} (hb : IsBarrier μ A cat Φ) (n : ℕ) :
    probOf μ ((range (n + 1)).biUnion fun t => univ.filter fun ω => cat t ω = true) ≤
      expect μ (Φ 0) := by
  have hsub : ((range (n + 1)).biUnion fun t => univ.filter fun ω => cat t ω = true) ⊆
      hitSet Φ 1 n := by
    intro ω h
    simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and] at h
    obtain ⟨t, ht, hc⟩ := h
    exact mem_hitSet.2 ⟨t, Nat.lt_succ_iff.1 ht, hb.2 t ω hc⟩
  have hmono : probOf μ _ ≤ probOf μ (hitSet Φ 1 n) :=
    sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => μ.nonneg ω
  have hv := ville_finite (μ := μ) (A := A) 1 n hb.1.2 (fun t _ => hb.1.1.meas t)
    (fun t _ => hb.1.1.step t)
  rw [one_mul] at hv
  exact hmono.trans hv

end Supermart

end Cleanroom.Corrigibility.CorrTrajectory
