import Cleanroom.Info.InfoVoiLatents.SplitValuePart

/-!
# info-voi-latents — Target 4(v), the composed bound: refuted at `leakθ`, attained at `meanField2`;
`HVal` versus the information form (repair round 2)

Audit r2 (fidelity B1, adversarial item 1) found that `SplitValuePart.valuePart_not_bounded_by_lambdaTV`
refutes only the *first link* of Target 4(v) (`voiΛ ≤ M·E[TV_Λ]`) while its docstring claimed the
*composed* bound `voiΛ ≤ M√(I[Λ:S]/2)` by a non sequitur (`¬(A ≤ B)` and `B ≤ C` say nothing about
`A ≤ C`). This file supplies the missing evidence — the auditors' probe
`run/wp/info-voi-latents/audit-r2-probes/ComposedBound.lean`, promoted:

* `leakΛ`, the Λ-marginal experiment of `leakθ` under the uniform prior (`k(true) = (½, ½)`,
  `k(false) = (¼, ¾)`), proved to be the Λ-lift (`leakΛ_eq_lift`), with `leakθ`'s signal masses
  (`sigMass_leakΛ`) and `leakθ`'s Λ-posteriors (`post_leakΛ_eq_postΛ`);
* `mutualInfo_leakΛ_le`: PFR's `I[fst : snd ; joint μΛ leakΛ] ≤ 1/15` through the bridge and
  `log x ≤ x − 1` per coordinate (the exact value is `log 2 − (3/8)·h₂(1/3) − (5/8)·h₂(2/5)
  ≈ 0.034` nats, not stated);
* **`valuePart_not_bounded_by_lambdaMI`**: the composed bound fails at `leakθ` —
  `voiΛ = 3M/8 > M√(1/30) ≥ M√(I/2)`. With the first link this refutes Target 4(v) as the mandate
  states it, for P3(a)'s definition of `VOI^Λ`.

Two further items from audit r2:

* **`meanField2_tv_bound_attained`** (fidelity item 6): the Λ-TV bound
  `SplitValuePart.voi_le_mul_sum_tvΛ_of_hval` is *attained* at `(mfPrior, meanField2, mfV)`:
  `voi = 6/25 = (3/5)·(2/5) = M·E[tv(postΛ s, μΛ)]` with `M = 3/5` the profile's within-action
  range — an N+ for the positive half of Target 4(v), at an `HVal` experiment whose `θ`-conditional
  is not trivial.
* **`nullθ_not_hval`**, **`nullθ_voi_eq_voiΛ`** (adversarial item 5): `HVal` — the kernel identity
  on *every* `ϑ` — is stronger than S3(c)'s information form `I[θ : S | Λ] = 0`: an experiment that
  violates the identity only at a null-mass `ϑ` fails `HVal` while `voi = voiΛ = 0` (the signal is
  a.s. constant). `HVal`'s Fidelity is `stronger`, disclosed at the definition (`Split.lean`).

Findings F12. Mandate: Target 4(v).
-/

namespace Cleanroom.Info.InfoVoiLatents.Split

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents.Voi
open MeasureTheory ProbabilityTheory

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The composed Target 4(v) bound fails at `leakθ` -/

/-- The Λ-marginal experiment of `leakθ` under the uniform prior: `k(true) = (½, ½)`,
`k(false) = (¼, ¾)` — the Λ-lift of `leakθ` (`leakΛ_eq_lift`).
Source: none: infrastructure (audit r2 probe `ComposedBound.lean`, promoted)
Kind: D
Fidelity: exact -/
def leakΛ : Experiment Bool (Fin 2) where
  k := fun l s => if l then 1 / 2 else (if s = 0 then 1 / 4 else 3 / 4)
  k_mem := fun l => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by
    cases l <;> simp [Fin.sum_univ_two] <;> norm_num⟩

/-- `muΛ leakPrior = (½, ½)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem muΛ_leakPrior : muΛ leakPrior = fun _ => 1 / 2 := by
  funext l
  simp [muΛ, leakPrior]
  norm_num

/-- `muΛ_leakPrior_mem`: the Λ-marginal of the uniform prior is in the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem muΛ_leakPrior_mem : muΛ leakPrior ∈ stdSimplex ℝ Bool := muΛ_mem leakPrior_mem

/-- `leakΛ` is the Λ-lift of `leakθ` under `leakPrior`:
`leakΛ.k l s = ∑ ϑ', (P(l, ϑ') / P(l)) · leakθ.k (l, ϑ') s`.
Source: none: infrastructure (the identification the probe checked through posteriors, made exact)
Kind: L
Fidelity: n/a -/
theorem leakΛ_eq_lift (l : Bool) (s : Fin 2) :
    leakΛ.k l s = ∑ ϑ', (leakPrior (l, ϑ') / muΛ leakPrior l) * leakθ.k (l, ϑ') s := by
  rw [muΛ_leakPrior]
  unfold leakΛ leakPrior leakθ
  cases l <;> fin_cases s <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The signal masses of `leakΛ` agree with `leakθ`'s (`3/8`, `5/8`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigMass_leakΛ (s : Fin 2) :
    sigMass (muΛ leakPrior) leakΛ s = if s = 0 then 3 / 8 else 5 / 8 := by
  rw [muΛ_leakPrior]
  unfold sigMass leakΛ
  fin_cases s <;> simp [Fintype.sum_bool] <;> norm_num

/-- The posteriors of `leakΛ`: `(2/3, 1/3)` and `(2/5, 3/5)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem post_leakΛ (s : Fin 2) :
    post (muΛ leakPrior) leakΛ s
      = fun l => if s = 0 then (if l then 2 / 3 else 1 / 3) else (if l then 2 / 5 else 3 / 5) := by
  funext l
  unfold post
  rw [sigMass_leakΛ, muΛ_leakPrior]
  unfold leakΛ
  fin_cases s <;> cases l <;> simp <;> norm_num

/-- `leakΛ` reproduces the Λ-posteriors of `leakθ`: the Λ-marginal problem is the one P3(a)'s
bound is about.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem post_leakΛ_eq_postΛ (s : Fin 2) :
    post (muΛ leakPrior) leakΛ s = postΛ leakPrior leakθ s := by
  rw [post_leakΛ, postΛ_leakθ]

/-- `x log (x / y) ≤ x (x / y − 1)` for `0 ≤ x`, `0 < y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mul_log_div_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x / y) ≤ x * (x / y - 1) := by
  rcases hx.lt_or_eq with hx' | hx'
  · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hx' hy)) hx'.le
  · rw [← hx']
    simp

/-- `klFin (post 0) μΛ ≤ 1/9` and `klFin (post 1) μΛ ≤ 1/25` (`log x ≤ x − 1` per coordinate).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem klFin_leakΛ_le (s : Fin 2) :
    klFin (post (muΛ leakPrior) leakΛ s) (muΛ leakPrior) ≤ if s = 0 then 1 / 9 else 1 / 25 := by
  rw [post_leakΛ, muΛ_leakPrior]
  unfold klFin
  rw [Fintype.sum_bool]
  fin_cases s
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte]
    have h1 := mul_log_div_le (x := (2 / 3 : ℝ)) (y := 1 / 2) (by norm_num) (by norm_num)
    have h2 := mul_log_div_le (x := (1 / 3 : ℝ)) (y := 1 / 2) (by norm_num) (by norm_num)
    norm_num at h1 h2 ⊢
    linarith
  · simp only [Fin.isValue, Fin.mk_one, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte]
    have h1 := mul_log_div_le (x := (2 / 5 : ℝ)) (y := 1 / 2) (by norm_num) (by norm_num)
    have h2 := mul_log_div_le (x := (3 / 5 : ℝ)) (y := 1 / 2) (by norm_num) (by norm_num)
    norm_num at h1 h2 ⊢
    linarith

/-- **PFR's mutual information between `Λ` and the signal at `leakθ` is at most `1/15`** (through
the bridge `Bridge.sum_klFin_eq_mutualInfo`: `3/8 · 1/9 + 5/8 · 1/25 = 1/15`; the exact value is
`log 2 − (3/8)·h₂(1/3) − (5/8)·h₂(2/5) ≈ 0.034` nats, not stated).
Source: none: infrastructure (audit r2, fidelity B1, adversarial item 1)
Kind: P
Fidelity: exact (an upper bound on the exact quantity)
Hyps: (a) none -/
theorem mutualInfo_leakΛ_le :
    I[(Prod.fst : Bool × Fin 2 → Bool) : (Prod.snd : Bool × Fin 2 → Fin 2) ;
        Bridge.joint (muΛ leakPrior) leakΛ muΛ_leakPrior_mem] ≤ 1 / 15 := by
  rw [← Bridge.sum_klFin_eq_mutualInfo leakΛ muΛ_leakPrior_mem, Fin.sum_univ_two]
  have h0 := klFin_leakΛ_le 0
  have h1 := klFin_leakΛ_le 1
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at h0 h1
  rw [sigMass_leakΛ, sigMass_leakΛ]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  nlinarith

open scoped Classical in
/-- **The composed Target 4(v) bound is false for P3(a)'s definition of the value part.** At
`(leakPrior, leakθ, guessθ M)`, `voiΛ = 3M/8` while `M√(I[Λ : S]/2) ≤ M√(1/30) < 3M/8`, with `I`
PFR's `mutualInfo` on the joint of `(μΛ, leakΛ)` — the Λ-marginal experiment, whose posteriors are
`leakθ`'s Λ-posteriors (`post_leakΛ_eq_postΛ`) and which is the Λ-lift of `leakθ`
(`leakΛ_eq_lift`). Together with `valuePart_not_bounded_by_lambdaTV` (the first link) this refutes
Target 4(v) as the mandate states it ("compose"), for P3(a)'s `VOI^Λ`. Under `HVal` the composed
bound holds (`voi_le_mul_sqrt_mutualInfoΛ_of_hval`); `leakθ` is not `HVal` (`not_hval_leakθ`).
Source: [[generalization-final]] S3(a) l. 66, P3(a) l. 113 ("`≤ M√(½ I(Λ_A ; E_a))`"); mandate
Target 4(v) ("compose"); findings F12; audit r2 (fidelity B1, adversarial item 1)
Kind: N+
Fidelity: exact (a refutation of the note's composed claim for its own definition)
Hyps: (a) all -/
theorem valuePart_not_bounded_by_lambdaMI {M : ℝ} (hM : 0 < M) :
    I[(Prod.fst : Bool × Fin 2 → Bool) : (Prod.snd : Bool × Fin 2 → Fin 2) ;
        Bridge.joint (muΛ leakPrior) leakΛ muΛ_leakPrior_mem] ≤ 1 / 15 ∧
    ¬ voiΛ leakPrior leakθ (menu (guessθ M))
        ≤ M * Real.sqrt (I[(Prod.fst : Bool × Fin 2 → Bool) : (Prod.snd : Bool × Fin 2 → Fin 2) ;
            Bridge.joint (muΛ leakPrior) leakΛ muΛ_leakPrior_mem] / 2) := by
  refine ⟨mutualInfo_leakΛ_le, ?_⟩
  rw [voiΛ_leakθ_eq_voi M, voi_leakθ hM.le]
  intro h
  have hI := mutualInfo_leakΛ_le
  have hsqrt : Real.sqrt (I[(Prod.fst : Bool × Fin 2 → Bool) : (Prod.snd : Bool × Fin 2 → Fin 2) ;
      Bridge.joint (muΛ leakPrior) leakΛ muΛ_leakPrior_mem] / 2)
      ≤ Real.sqrt (1 / 30) := by
    apply Real.sqrt_le_sqrt
    linarith
  have h30 : Real.sqrt (1 / 30) < 3 / 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have : M * Real.sqrt (I[(Prod.fst : Bool × Fin 2 → Bool) : (Prod.snd : Bool × Fin 2 → Fin 2) ;
      Bridge.joint (muΛ leakPrior) leakΛ muΛ_leakPrior_mem] / 2)
      < 3 / 8 * M := by
    calc M * Real.sqrt _ ≤ M * Real.sqrt (1 / 30) := mul_le_mul_of_nonneg_left hsqrt hM.le
      _ < M * (3 / 8) := mul_lt_mul_of_pos_left h30 hM
      _ = 3 / 8 * M := by ring
  linarith

/-! ### The Λ-TV bound is attained at `meanField2` -/

/-- The Λ-marginal of `mfPrior` is uniform.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem muΛ_mfPrior : muΛ mfPrior = fun _ => 1 / 2 := by
  funext l
  unfold muΛ mfPrior
  fin_cases l <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The value profile of `mfV` under `mfPrior`: `11/20` on the diagonal, `−1/20` off it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Vbar_mfV (a l : Fin 2) : Vbar mfPrior mfV a l = if a = l then 11 / 20 else -1 / 20 := by
  unfold Vbar
  rw [muΛ_mfPrior]
  unfold mfPrior mfV
  fin_cases a <;> fin_cases l <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The profile's within-action range is `3/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Vbar_mfV_range (a l l' : Fin 2) :
    Vbar mfPrior mfV a l - Vbar mfPrior mfV a l' ≤ 3 / 5 := by
  rw [Vbar_mfV, Vbar_mfV]
  split_ifs <;> norm_num

/-- Signal masses of `meanField2` under `mfPrior`: `½` each.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigMass_meanField2 (s : Fin 2) : sigMass mfPrior meanField2 s = 1 / 2 := by
  unfold sigMass mfPrior meanField2
  fin_cases s <;> simp [Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

/-- The Λ-posteriors of `meanField2`: `9/10` at `λ = s`, `1/10` otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postΛ_meanField2 (s : Fin 2) :
    postΛ mfPrior meanField2 s = fun l => if l = s then 9 / 10 else 1 / 10 := by
  funext l
  unfold postΛ post
  simp only [sigMass_meanField2]
  unfold mfPrior meanField2
  fin_cases s <;> fin_cases l <;> simp [Fin.sum_univ_two] <;> norm_num

/-- `∑_s P(s) · tv(postΛ s, μΛ) = 2/5` at `meanField2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lambdaTV_meanField2 :
    ∑ s, sigMass mfPrior meanField2 s * tv (postΛ mfPrior meanField2 s) (muΛ mfPrior) = 2 / 5 := by
  simp_rw [sigMass_meanField2, postΛ_meanField2, muΛ_mfPrior]
  unfold tv
  rw [Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, one_ne_zero]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- **The Λ-TV bound is attained at `meanField2`**: `voi = 6/25 = (3/5)·(2/5) = M·E[tv(postΛ s, μΛ)]`
with `M = 3/5` the profile's within-action range — `voi_le_mul_sum_tvΛ_of_hval` with equality, at
an `HVal` experiment whose `θ`-conditional (`P(ϑ = λ | λ) = 9/10`) is not trivial. The full
hypothesis package of the bound (simplex, `HVal`, range) is inhabited here.
Source: [[generalization-final]] S3(a) l. 66, P3(a) l. 113; audit r2 (fidelity item 6)
Kind: N+
Fidelity: exact (the bound's hypotheses inhabited and the bound attained)
Hyps: (a) all -/
theorem meanField2_tv_bound_attained :
    HVal meanField2 ∧
    (∀ a l l', Vbar mfPrior mfV a l - Vbar mfPrior mfV a l' ≤ 3 / 5) ∧
    voi mfPrior meanField2 (menu mfV)
      = 3 / 5 * ∑ s, sigMass mfPrior meanField2 s * tv (postΛ mfPrior meanField2 s) (muΛ mfPrior) := by
  refine ⟨hval_meanField2, Vbar_mfV_range, ?_⟩
  rw [mf_voi_meanField, lambdaTV_meanField2]
  norm_num

/-! ### `HVal` is stronger than the information form at null coordinates -/

/-- `Λ = Unit`, `θ = Fin 2`, all mass on `θ = 0`.
Source: none: infrastructure (audit r2 probe `Vacuity.lean` P4, promoted)
Kind: D
Fidelity: exact -/
def nullθPrior : Unit × Fin 2 → ℝ := fun p => if p.2 = 0 then 1 else 0

/-- `nullθPrior_mem`: the prior is in the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullθPrior_mem : nullθPrior ∈ stdSimplex ℝ (Unit × Fin 2) := by
  refine ⟨fun p => by unfold nullθPrior; split_ifs <;> norm_num, ?_⟩
  unfold nullθPrior
  rw [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two]
  simp

/-- Signal `0` always at `θ = 0`; signal `1` always at the null-mass `θ = 1`.
Source: none: infrastructure (audit r2 probe P4)
Kind: D
Fidelity: exact -/
def nullθExp : Experiment (Unit × Fin 2) (Fin 2) where
  k := fun p s => if s = p.2 then 1 else 0
  k_mem := fun p => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by simp⟩

/-- **`HVal` fails at a null coordinate**: the kernel identity is violated only at the null-mass
`θ = 1`.
Source: [[generalization-final]] S3(c) l. 68; audit r2 (adversarial item 5)
Kind: N−
Fidelity: exact (an encoding test: `HVal` constrains null coordinates)
Hyps: (a) none -/
theorem nullθ_not_hval : ¬ HVal nullθExp := by
  intro h
  have := h () 0 1 0
  simp [nullθExp] at this

/-- **Yet S3(c)'s conclusion holds**: `voi = voiΛ` (both `0`; the signal is a.s. constant, so the
information form `I[θ : S | Λ] = 0` of H_val holds while the kernel identity does not). So `HVal`
is strictly stronger than S3(c)'s hypothesis, and `voi_eq_voiΛ_of_hval` is proved under the
stronger one.
Source: [[generalization-final]] S3(c) l. 68; audit r2 (adversarial item 5)
Kind: N−
Fidelity: exact (an encoding test)
Hyps: (a) none -/
theorem nullθ_voi_eq_voiΛ {n : ℕ} (u : Fin (n + 1) → Unit × Fin 2 → ℝ) :
    voi nullθPrior nullθExp u = voiΛ nullθPrior nullθExp u ∧ voi nullθPrior nullθExp u = 0 := by
  have hvoi : voi nullθPrior nullθExp u = 0 := by
    refine le_antisymm ?_ (voi_nonneg _ _ _)
    unfold voi bayesValue
    rw [sub_nonpos, Finset.sup'_le_iff]
    intro δ _
    have hval : ∑ w, nullθPrior w * ∑ s, nullθExp.k w s * u (δ s) w = u (δ 0) ((), 0) := by
      simp [nullθPrior, nullθExp, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two]
    rw [hval]
    unfold priorValue
    refine Finset.le_sup'_of_le _ (mem_univ (δ 0)) (le_of_eq ?_)
    simp [E, nullθPrior, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two]
  refine ⟨?_, hvoi⟩
  refine le_antisymm ?_ (voiΛ_le_voi _ _ _)
  rw [hvoi]
  exact voi_nonneg _ _ _

end

end Cleanroom.Info.InfoVoiLatents.Split
