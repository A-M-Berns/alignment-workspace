import Cleanroom.Corrigibility.CorrTrajectory.Potential

/-!
# `corr-trajectory` — `Hazard`: Statement 7, hazard budgets as barrier certificates (T6)

* **(a)** the per-round form: `P*(∃ t ≤ T, Cat_t) ≤ P*(Cat_0) + ∑_{t<T} δ̄_t` from `δ_t ≤ δ̄_t` on
  `𝓕_t` (first-entry events are disjoint; each has mass `≤ δ̄_t` by the tower step; union bound);
* **(b)** the budget form: `Φ_t = 𝟙[Cat_t] + ∑_{u ≥ t} δ̄_u` is a Layer-F barrier certificate (needs
  absorption and (a)'s hypothesis; `Φ ≥ 1` on `Cat`), so Ville at `λ = 1` gives
  `P*(Cat ever) ≤ Φ_0 = ∑ δ̄` when `¬Cat_0` — both with a finite tail through a horizon and with the
  `tsum` tail under `Summable`;
* **(d)** the factorization `δ_t ≤ ρ_t ε^irr_t (1 − β^min_t κ_t)` in product form, on the *pre-press*
  atoms (the source conditions on `𝓕_t`, which already contains the press: F-5 in the findings).

The harmonic (N−) and geometric (N+) witnesses are in `HazardWitness`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {M : Type}

/-- `P(A ∪ B) ≤ P(A) + P(B)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma probOf_union_le (μ : Distr Ω) (A B : Finset Ω) : probOf μ (A ∪ B) ≤ probOf μ A + probOf μ B := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := μ.mass)
  have h0 := probOf_nonneg μ (A ∩ B)
  unfold probOf at *
  linarith

namespace ShutdownProc

variable (S : ShutdownProc Ω M)

/-- The event `Cat_t`. Source: invariant-final.md S2. Kind: D. Fidelity: exact -/
def catAt (t : ℕ) : Finset Ω := univ.filter fun ω => S.cat t ω = true

/-- The first-entry event `¬Cat_t ∧ Cat_{t+1}`. Source: invariant-final.md proof of Statement 7(a). Kind: D. Fidelity: exact -/
def enterAt (t : ℕ) : Finset Ω := univ.filter fun ω => S.cat t ω = false ∧ S.cat (t + 1) ω = true

/-- The event `∃ t ≤ T, Cat_t` ("catastrophe by `T`"). Source: invariant-final.md Statement 7(a). Kind: D. Fidelity: exact -/
def catBy (T : ℕ) : Finset Ω := (range (T + 1)).biUnion fun t => S.catAt t

/-- `ind_enterAt` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ind_enterAt (t : ℕ) (ω : Ω) :
    ind (S.enterAt t) ω = (1 - indB (S.cat t) ω) * indB (S.cat (t + 1)) ω := by
  unfold ind indB enterAt
  cases h1 : S.cat t ω <;> cases h2 : S.cat (t + 1) ω <;> simp [h1, h2]

/-- **With `Cat_t` `𝓕_t`-measurable, `hazardLE` is the mandate's atom form off `Cat`**:
`∑_{atom} μ 𝟙[Cat_{t+1}] ≤ δ̄_t ∑_{atom} μ` on every atom outside `Cat_t`, and nothing on atoms inside.
Source: mandate T1 (iii) / invariant-final.md D4
Kind: L
Fidelity: exact -/
theorem hazardLE_iff_of_meas (δbar : ℕ → ℝ) (t : ℕ) (hcat : S.F.Meas t (indB (S.cat t))) :
    S.hazardLE δbar t ↔
      ∀ ω, S.cat t ω = false →
        condSum S.μ S.F t (indB (S.cat (t + 1))) ω ≤ δbar t * atomMass S.μ S.F t ω := by
  unfold hazardLE
  have hm : S.F.Meas t (fun ω' => 1 - indB (S.cat t) ω') := hcat.one_sub
  constructor
  · intro h ω hω
    have := h ω
    rw [condSum_mul_meas t hm, condSum_of_meas t hm] at this
    simpa [indB, hω] using this
  · intro h ω
    rw [condSum_mul_meas t hm, condSum_of_meas t hm]
    cases hω : S.cat t ω
    · simpa [indB, hω] using h ω hω
    · simp [indB, hω]

/-- **Each first-entry event has mass at most `δ̄_t`**, by the tower step on the hazard bound.
Source: invariant-final.md proof of Statement 7(a) ("`P(first entry at t+1) ≤ E[1[¬Cat_t] δ_t] ≤ δ̄_t`")
Kind: L
Fidelity: exact -/
theorem probOf_enterAt_le (δbar : ℕ → ℝ) (t : ℕ) (hz : S.hazardLE δbar t) (hδ : 0 ≤ δbar t) :
    probOf S.μ (S.enterAt t) ≤ δbar t := by
  rw [probOf_eq_expect_ind]
  have e : ind (S.enterAt t) = fun ω => (1 - indB (S.cat t) ω) * indB (S.cat (t + 1)) ω :=
    funext (S.ind_enterAt t)
  rw [e]
  have h1 : expect S.μ (fun ω => (1 - indB (S.cat t) ω) * indB (S.cat (t + 1)) ω) ≤
      expect S.μ (fun ω => δbar t * (1 - indB (S.cat t) ω)) := by
    refine expect_le_of_condSum_le (A := S.F) t fun ω => ?_
    rw [condSum_const_mul]
    exact hz ω
  have h2 : expect S.μ (fun ω => δbar t * (1 - indB (S.cat t) ω)) ≤ δbar t := by
    rw [Found.CorrThreeStep.expect_const_mul]
    refine (mul_le_mul_of_nonneg_left ?_ hδ).trans (le_of_eq (mul_one _))
    calc expect S.μ (fun ω => 1 - indB (S.cat t) ω) ≤ expect S.μ (fun _ => 1) :=
          Found.CorrThreeStep.expect_mono _ fun ω => by linarith [indB_nonneg (S.cat t) ω]
      _ = 1 := Found.CorrThreeStep.expect_const _ _
  exact h1.trans h2

/-- Catastrophe by `T` happens at time `0` or by a first entry at some `t < T`.
Source: invariant-final.md proof of Statement 7(a) (`τ`, the first entry time)
Kind: L
Fidelity: exact -/
theorem catBy_subset (T : ℕ) : S.catBy T ⊆ S.catAt 0 ∪ (range T).biUnion (S.enterAt) := by
  intro ω hω
  simp only [catBy, catAt, mem_biUnion, mem_range, mem_filter, mem_univ, true_and] at hω
  obtain ⟨t, ht, hc⟩ := hω
  have hex : ∃ s, S.cat s ω = true := ⟨t, hc⟩
  have hs₀c : S.cat (Nat.find hex) ω = true := Nat.find_spec hex
  have hs₀le : Nat.find hex ≤ t := Nat.find_min' hex hc
  rw [mem_union]
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · left
    simp only [catAt, mem_filter, mem_univ, true_and]
    rwa [h0] at hs₀c
  · right
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hsc : S.cat s ω = false := by
      have := Nat.find_min hex (show s < Nat.find hex by rw [hs]; exact Nat.lt_succ_self s)
      simpa using this
    have hsT : s < T := by omega
    rw [hs] at hs₀c
    simp only [enterAt, mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
    exact ⟨s, hsT, hsc, hs₀c⟩

/-- **Statement 7(a), the per-round form (D6).** If `δ_t ≤ δ̄_t` on `𝓕_t` for every `t < T` (a
deterministic schedule through the horizon, no independence), then
`P*(∃ t ≤ T, Cat_t) ≤ P*(Cat_0) + ∑_{t<T} δ̄_t`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(a)
Kind: P (first-entry decomposition, the tower step per round, the union bound)
Fidelity: exact (the source states it for `Cat_0 = ∅`; `P*(Cat_0)` is carried explicitly)
Hyps: (a) only -/
theorem catBy_le_budget (δbar : ℕ → ℝ) (T : ℕ) (hz : ∀ t < T, S.hazardLE δbar t)
    (hδ : ∀ t < T, 0 ≤ δbar t) :
    probOf S.μ (S.catBy T) ≤ probOf S.μ (S.catAt 0) + ∑ t ∈ range T, δbar t := by
  calc probOf S.μ (S.catBy T)
      ≤ probOf S.μ (S.catAt 0 ∪ (range T).biUnion S.enterAt) := probOf_mono (S.catBy_subset T)
    _ ≤ probOf S.μ (S.catAt 0) + probOf S.μ ((range T).biUnion S.enterAt) := probOf_union_le _ _ _
    _ ≤ probOf S.μ (S.catAt 0) + ∑ t ∈ range T, probOf S.μ (S.enterAt t) := by
        linarith [probOf_biUnion_range_le (μ := S.μ) S.enterAt T]
    _ ≤ probOf S.μ (S.catAt 0) + ∑ t ∈ range T, δbar t := by
        gcongr with t ht
        exact S.probOf_enterAt_le δbar t (hz t (mem_range.1 ht)) (hδ t (mem_range.1 ht))

/-! ### (b) the budget potential -/

/-- Absorption, as an inequality of indicators on the support.
Source: invariant-final.md S2 (`Cat` absorbing). Kind: L. Fidelity: exact -/
lemma indB_cat_succ_le (t : ℕ) (ω : Ω) (hμ : 0 < S.μ.mass ω) :
    indB (S.cat (t + 1)) ω ≤ indB (S.cat t) ω + (1 - indB (S.cat t) ω) * indB (S.cat (t + 1)) ω := by
  cases h : S.cat t ω
  · simp [indB, h]
  · have := S.cat_absorbing t ω hμ h
    simp [indB, h, this]

/-- The one-step inequality behind the budget potential:
`E*[𝟙[Cat_{t+1}] 1_atom] ≤ E*[𝟙[Cat_t] 1_atom] + δ̄_t · atomMass` from absorption and the hazard bound.
Source: invariant-final.md proof of Statement 7(b). Kind: L. Fidelity: exact -/
lemma condSum_cat_succ_le (δbar : ℕ → ℝ) (t : ℕ) (hz : S.hazardLE δbar t) (hδ : 0 ≤ δbar t) (ω : Ω) :
    condSum S.μ S.F t (indB (S.cat (t + 1))) ω ≤
      condSum S.μ S.F t (indB (S.cat t)) ω + δbar t * atomMass S.μ S.F t ω := by
  have h1 : condSum S.μ S.F t (indB (S.cat (t + 1))) ω ≤
      condSum S.μ S.F t (fun ω' => indB (S.cat t) ω' +
        (1 - indB (S.cat t) ω') * indB (S.cat (t + 1)) ω') ω :=
    condSum_mono_support t (fun ω' hμ => S.indB_cat_succ_le t ω' hμ) ω
  rw [condSum_add] at h1
  have h2 := hz ω
  have h3 : condSum S.μ S.F t (fun ω' => 1 - indB (S.cat t) ω') ω ≤ atomMass S.μ S.F t ω :=
    condSum_le_atomMass t (fun ω' => by linarith [indB_nonneg (S.cat t) ω']) ω
  nlinarith [mul_le_mul_of_nonneg_left h3 hδ]

/-- **The budget potential with a finite tail**: `Φ_t = 𝟙[Cat_t] + ∑_{u ∈ [t, T)} δ̄_u`.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(b)
Kind: D
Fidelity: exact (finite tail through the horizon `T`; the `tsum` form is `budgetPotInf`) -/
noncomputable def budgetPot (δbar : ℕ → ℝ) (T t : ℕ) (ω : Ω) : ℝ :=
  indB (S.cat t) ω + ∑ u ∈ Ico t T, δbar u

/-- **Statement 7(b), finite tail: the budget potential is a nonnegative supermartingale below `T`,
adapted, and `≥ 1` on `Cat`.**
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(b)
Kind: P (small: absorption + the hazard bound give the step)
Fidelity: exact
Hyps: (a) only (`Cat_t` `𝓕_t`-measurable is the adaptedness the source assumes) -/
theorem budgetPot_steps (δbar : ℕ → ℝ) (T : ℕ) (hz : ∀ t < T, S.hazardLE δbar t)
    (hδ : ∀ t, 0 ≤ δbar t) (hcat : ∀ t, S.F.Meas t (indB (S.cat t))) :
    (∀ t, S.F.Meas t (S.budgetPot δbar T t)) ∧ (∀ t < T, SupermartStep S.μ S.F (S.budgetPot δbar T) t) ∧
      (∀ t ω, 0 ≤ S.budgetPot δbar T t ω) ∧ (∀ t ω, S.cat t ω = true → 1 ≤ S.budgetPot δbar T t ω) := by
  refine ⟨fun t => (hcat t).add (S.F.meas_const t _), fun t ht ω => ?_, fun t ω => ?_, fun t ω h => ?_⟩
  · unfold budgetPot
    rw [condSum_add, condSum_add, condSum_const, condSum_const]
    have h1 := S.condSum_cat_succ_le δbar t (hz t ht) (hδ t) ω
    have h2 : ∑ u ∈ Ico t T, δbar u = δbar t + ∑ u ∈ Ico (t + 1) T, δbar u := by
      rw [Finset.sum_eq_sum_Ico_succ_bot ht]
    rw [h2]
    nlinarith [atomMass_nonneg (μ := S.μ) (A := S.F) t ω]
  · exact add_nonneg (indB_nonneg _ _) (sum_nonneg fun u _ => hδ u)
  · unfold budgetPot
    rw [indB_true h]
    linarith [sum_nonneg fun u (_ : u ∈ Ico t T) => hδ u]

/-- **Statement 7(b), finite tail, the bound**: `P*(∃ t ≤ T, Cat_t) ≤ E*[Φ_0] = P*(Cat_0) + ∑_{t<T} δ̄_t`,
by Ville at `λ = 1` on the budget potential — the same number as (a), now as a barrier certificate.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(b)
Kind: C (`ville_finite` on `budgetPot`)
Fidelity: exact
Hyps: (a) only -/
theorem catBy_le_budgetPot (δbar : ℕ → ℝ) (T : ℕ) (hz : ∀ t < T, S.hazardLE δbar t)
    (hδ : ∀ t, 0 ≤ δbar t) (hcat : ∀ t, S.F.Meas t (indB (S.cat t))) :
    probOf S.μ (S.catBy T) ≤ probOf S.μ (S.catAt 0) + ∑ t ∈ range T, δbar t := by
  obtain ⟨hm, hs, hn, h1⟩ := S.budgetPot_steps δbar T hz hδ hcat
  have hsub : S.catBy T ⊆ hitSet (S.budgetPot δbar T) 1 T := by
    intro ω hω
    simp only [catBy, catAt, mem_biUnion, mem_range, mem_filter, mem_univ, true_and] at hω
    obtain ⟨t, ht, hc⟩ := hω
    exact mem_hitSet.2 ⟨t, Nat.lt_succ_iff.1 ht, h1 t ω hc⟩
  have hv := ville_finite (μ := S.μ) (A := S.F) 1 T hn (fun t _ => hm t) hs
  rw [one_mul] at hv
  have he : expect S.μ (S.budgetPot δbar T 0) = probOf S.μ (S.catAt 0) + ∑ t ∈ range T, δbar t := by
    unfold budgetPot
    rw [Found.CorrThreeStep.expect_add, Found.CorrThreeStep.expect_const, probOf_eq_expect_ind,
      Finset.range_eq_Ico]
    congr 1
    refine congrArg _ (funext fun ω => ?_)
    unfold ind indB catAt
    simp
  rw [← he]
  exact (probOf_mono hsub).trans hv

/-! ### (b′) the `tsum` tail: a global barrier certificate -/

/-- **The budget potential with the infinite tail** `Φ_t = 𝟙[Cat_t] + ∑_{u ≥ t} δ̄_u` (the source's form).
Junk-guard: without `Summable δ̄` the `tsum` is `0` and `Φ` is not a potential; every theorem names
`Summable`.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(b)
Kind: D
Fidelity: exact under `Summable δ̄` -/
noncomputable def budgetPotInf (δbar : ℕ → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  indB (S.cat t) ω + ∑' u, δbar (u + t)

/-- **Statement 7(b): the budget potential is a Layer-F barrier certificate** (D5), given a summable
nonnegative schedule, the hazard bound at every round, absorption, and `Cat_t` `𝓕_t`-measurable.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(b)
Kind: P (small: the finite step with the tail shifted by `tsum_eq_zero_add`)
Fidelity: exact
Hyps: (a) only -/
theorem budgetPotInf_isBarrier (δbar : ℕ → ℝ) (hsum : Summable δbar) (hδ : ∀ t, 0 ≤ δbar t)
    (hz : ∀ t, S.hazardLE δbar t) (hcat : ∀ t, S.F.Meas t (indB (S.cat t))) :
    IsBarrier S.μ S.F S.cat (S.budgetPotInf δbar) := by
  refine ⟨⟨⟨fun t => (hcat t).add (S.F.meas_const t _), fun t ω => ?_⟩, fun t ω => ?_⟩, fun t ω h => ?_⟩
  · unfold budgetPotInf
    rw [condSum_add, condSum_add, condSum_const, condSum_const]
    have h1 := S.condSum_cat_succ_le δbar t (hz t) (hδ t) ω
    have hshift : Summable fun u => δbar (u + t) := (summable_nat_add_iff t).2 hsum
    have h2 : ∑' u, δbar (u + t) = δbar t + ∑' u, δbar (u + (t + 1)) := by
      rw [hshift.tsum_eq_zero_add]
      simp only [zero_add]
      congr 1
      refine tsum_congr fun u => ?_
      congr 1; omega
    rw [h2]
    nlinarith [atomMass_nonneg (μ := S.μ) (A := S.F) t ω]
  · exact add_nonneg (indB_nonneg _ _)
      (tsum_nonneg fun u => hδ _)
  · unfold budgetPotInf
    rw [indB_true h]
    have h0 : 0 ≤ ∑' u, δbar (u + t) := tsum_nonneg fun u => hδ (u + t)
    linarith

/-- **Statement 7(b), the bound uniformly in time**: `P*(∃ t ≤ n, Cat_t) ≤ P*(Cat_0) + ∑ δ̄` for every
`n`, and `≤ Δ` under the budget `∑ δ̄ ≤ Δ` when `Cat_0` is null.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(b) ("`P*(Cat ever) ≤ Δ` uniformly in time")
Kind: C (`barrier_bound` on `budgetPotInf`)
Fidelity: exact (`n`-uniform finite statement)
Hyps: (a) only -/
theorem catBy_le_tsum (δbar : ℕ → ℝ) (hsum : Summable δbar) (hδ : ∀ t, 0 ≤ δbar t)
    (hz : ∀ t, S.hazardLE δbar t) (hcat : ∀ t, S.F.Meas t (indB (S.cat t))) (n : ℕ) :
    probOf S.μ (S.catBy n) ≤ probOf S.μ (S.catAt 0) + ∑' u, δbar u := by
  have hb := barrier_bound (S.budgetPotInf_isBarrier δbar hsum hδ hz hcat) n
  have he : expect S.μ (S.budgetPotInf δbar 0) = probOf S.μ (S.catAt 0) + ∑' u, δbar u := by
    unfold budgetPotInf
    rw [Found.CorrThreeStep.expect_add, Found.CorrThreeStep.expect_const, probOf_eq_expect_ind]
    simp only [add_zero]
    congr 1
    refine congrArg _ (funext fun ω => ?_)
    unfold ind indB catAt
    simp
  rw [← he]
  exact hb

/-! ### (d) the factorization -/

/-- **Statement 7(d), the factorization in product form, on the pre-press atoms.** Under the S2
definition of `Irr` (`Cat_{t+1} ⊆ {Irr_t ∧ W_t ∧ executed_t}` on the support) and the detection bound
`β^min_t · P*(Irr_t ∧ W_t ∣ 𝓕_t^-) ≤ P*(Irr_t ∧ W_t ∧ Pr_t ∣ 𝓕_t^-)`:
`P*(Cat_{t+1} ∣ 𝓕_t^-) ≤ (1 − β^min_t κ_t) · P*(Irr_t ∧ W_t ∣ 𝓕_t^-)`, where `P*(Irr_t ∧ W_t ∣ ·)` is
the source's `ρ_t ε^irr_t`. The source conditions on `𝓕_t`, which contains `Pr_t`; the factorization
is a statement on `𝓕_t^-` (F-5).
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(d)
Kind: P (small)
Fidelity: variant: conditioning on `𝓕_t^-` instead of the source's `𝓕_t` (F-5); the three factors are
the source's
Hyps: (a) the `Irr` inclusion and `(βmin)` are the named hypotheses -/
theorem hazard_factorization (t : ℕ) (βmin : Ω → ℝ) (ω : Ω)
    (hirr : ∀ ω', 0 < S.μ.mass ω' → S.cat (t + 1) ω' = true →
      S.irr t ω' = true ∧ S.wrong t ω' = true ∧ S.executed t ω' = true)
    (hβ : βmin ω * condSum S.μ S.Fpre t (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω') ω ≤
      condSum S.μ S.Fpre t
        (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω' * indB (S.pressed t) ω') ω) :
    condSum S.μ S.Fpre t (indB (S.cat (t + 1))) ω ≤
      (1 - βmin ω * indB (S.kappa t) ω) *
        condSum S.μ S.Fpre t (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω') ω := by
  have hκ : ∀ ω', ω' ∈ S.Fpre.fib t ω → S.kappa t ω' = S.kappa t ω := by
    intro ω' h
    have := S.kappa_meas t ω ω' h
    unfold indB at this
    cases h1 : S.kappa t ω' <;> cases h2 : S.kappa t ω <;> simp_all
  cases hk : S.kappa t ω
  · -- defiance on the atom: `Cat_{t+1} ⊆ Irr ∧ W`
    simp only [indB_false hk, mul_zero, sub_zero, one_mul]
    refine condSum_mono_support t (fun ω' hμ => ?_) ω
    unfold indB
    cases hc : S.cat (t + 1) ω'
    · simp only [Bool.false_eq_true, if_false]; split_ifs <;> norm_num
    · obtain ⟨h1, h2, -⟩ := hirr ω' hμ hc
      simp [h1, h2]
  · -- compliance on the atom: `Cat_{t+1} ⊆ Irr ∧ W ∧ ¬Pr`
    simp only [indB_true hk, mul_one]
    have h1 : condSum S.μ S.Fpre t (indB (S.cat (t + 1))) ω ≤
        condSum S.μ S.Fpre t
          (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω' * (1 - indB (S.pressed t) ω')) ω := by
      unfold condSum
      refine sum_le_sum fun ω' hω' => ?_
      rcases (S.μ.nonneg ω').lt_or_eq with hμ | hμ
      · refine mul_le_mul_of_nonneg_left ?_ hμ.le
        unfold indB
        cases hc : S.cat (t + 1) ω'
        · simp only [Bool.false_eq_true, if_false]
          refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)) ?_
          split_ifs <;> norm_num
        · obtain ⟨h1, h2, h3⟩ := hirr ω' hμ hc
          have hp : S.pressed t ω' = false := by
            unfold executed at h3
            rw [hκ ω' hω', hk] at h3
            simpa using h3
          simp [h1, h2, hp]
      · rw [← hμ]; simp
    have h2 : condSum S.μ S.Fpre t
        (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω' * (1 - indB (S.pressed t) ω')) ω =
        condSum S.μ S.Fpre t (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω') ω -
          condSum S.μ S.Fpre t
            (fun ω' => indB (S.irr t) ω' * indB (S.wrong t) ω' * indB (S.pressed t) ω') ω := by
      rw [← condSum_sub]
      refine congrArg (fun f => condSum S.μ S.Fpre t f ω) (funext fun ω' => ?_)
      ring
    rw [h2] at h1
    linarith

end ShutdownProc

end Cleanroom.Corrigibility.CorrTrajectory
