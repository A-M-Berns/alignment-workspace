import Cleanroom.Info.InfoVoiLatents.Split
import Cleanroom.Info.InfoVoiLatents.VoiWitness
import Cleanroom.Info.InfoVoiLatents.Bridge

/-!
# info-voi-latents — what "the value part" can and cannot mean (Target 4(v); repair round 1)

Audit r1 (fidelity B1) found that [[generalization-final]] S3(a)/P3(a) has no definition of the
"value part" `VOI^Λ` under which both of its sentences hold, and that the mandate's Target 4(v)
(`voiΛ ≤ M·E[TV_Λ] ≤ M√(I[Λ:S]/2)`, "compose") had been skipped without record. This file settles
it in Lean.

* **P3(a)'s definition** (the Λ-posterior garbling, `Split.voiΛ`) satisfies `voiΛ ≤ voi`
  (`voiΛ_le_voi`) but **not** the Λ-TV bound: `valuePart_not_bounded_by_lambdaTV` exhibits an
  experiment informative about `θ` beyond `Λ`, on a menu that does not depend on `Λ`, with
  distinct Λ-posteriors, so the garbling is a relabelling (`voiΛ = voi = 3M/8`,
  `bayesValue_le_pushforward_of_injective`) while `M·E[tv(postΛ s, μΛ)] = M/8`. That is the first
  link of Target 4(v); the composed bound `voiΛ ≤ M√(I[Λ:S]/2)` is refuted at the same instance
  in `SplitComposed.lean` (`valuePart_not_bounded_by_lambdaMI`, `I[Λ:S] ≤ 1/15` there; audit r2).
  Target 4(v) is **refuted** for this definition.
* **The "informative about `Λ` only" reading** (S3's gloss): the Λ-lift `k^Λ((λ,ϑ), s) :=
  ∑_ϑ' P(ϑ'|λ)·k((λ,ϑ'), s)`. It satisfies `HVal` by construction but is not a garbling of `k`,
  and `voiθ := voi − voiΛ ≥ 0` **fails** for it: `meanField_voi_gt_voi` (`voi = 3/20` for the
  experiment, `6/25` for its lift). So no definition makes both P3(a) sentences true.
* **Where Target 4(v) is true.** Under `HVal` the value problem *is* its Λ-marginal
  (`voi_eq_voi_margΛ_of_hval`: `voi μ k (menu V) = voi μΛ (margΛ k) V̄`), so the Target 3 chain
  applies verbatim with `Λ` in place of `ω`: `voi_le_mul_sum_tvΛ_of_hval` (`≤ M·E[tv(postΛ s, μΛ)]`,
  `M` the range of the profile `V̄` over the support of `μΛ` — `VbarSupp`, audit r2) and
  `voi_le_mul_sqrt_mutualInfoΛ_of_hval` (`≤ M√(I[Λ : S]/2)` over PFR's `mutualInfo` on the joint
  of `(μΛ, margΛ k)`). Under `HVal`, `voi = voiΛ` (`voi_eq_voiΛ_of_hval`), so this is Target 4(v)
  exactly where it holds; the TV bound is attained at `meanField2` (`SplitComposed.lean`).

Findings F12. Mandate: Target 4(v).
-/

namespace Cleanroom.Info.InfoVoiLatents.Split

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents.Voi
open MeasureTheory ProbabilityTheory

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Relabelling cannot lower the Bayes value -/

open scoped Classical in
/-- **Relabelling cannot lower the Bayes value**: for an injective signal map `f`,
`bayesValue μ k u ≤ bayesValue μ (pushforward k f) u` (with `voi_pushforward_le`, equality).
Source: none: infrastructure (audit r1 probe `ValuePart.lean`, promoted)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bayesValue_le_pushforward_of_injective {W S T : Type} [Fintype W] [Fintype S] [Fintype T]
    [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {f : S → T} (hf : Function.Injective f)
    {n : ℕ} (u : Fin (n + 1) → W → ℝ) :
    bayesValue μ k u ≤ bayesValue μ (pushforward k f) u := by
  rw [bayesValue_eq_sum_sup', bayesValue_eq_sum_sup']
  rw [← Finset.sum_fiberwise univ f
    (fun s => (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => postScore μ k u s a))]
  refine Finset.sum_le_sum fun t _ => ?_
  simp_rw [postScore_pushforward]
  rcases (univ.filter (fun s => f s = t)).eq_empty_or_nonempty with h | ⟨s, hs⟩
  · rw [h]
    simp
  · have hst : f s = t := by simpa using hs
    have hsing : univ.filter (fun s => f s = t) = {s} := by
      ext s'
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h' => hf (h'.trans hst.symm), fun h' => h' ▸ hst⟩
    rw [hsing]
    simp

open scoped Classical in
/-- **An injective relabelling of the signal preserves the VOI.**
Source: none: infrastructure
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem voi_pushforward_eq_of_injective {W S T : Type} [Fintype W] [Fintype S] [Fintype T]
    [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {f : S → T} (hf : Function.Injective f)
    {n : ℕ} (u : Fin (n + 1) → W → ℝ) : voi μ (pushforward k f) u = voi μ k u := by
  refine le_antisymm (voi_pushforward_le μ k f u) ?_
  unfold voi
  linarith [bayesValue_le_pushforward_of_injective μ k hf u]

/-! ### Counterexample 1: P3(a)'s Λ-garbling is not bounded by the Λ-TV -/

/-- The uniform prior on `Λ × θ = Bool × Fin 2`.
Source: none: infrastructure (audit r1 probe)
Kind: D
Fidelity: exact -/
def leakPrior : Bool × Fin 2 → ℝ := fun _ => 1 / 4

/-- `leakPrior_mem`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem leakPrior_mem : leakPrior ∈ stdSimplex ℝ (Bool × Fin 2) := by
  refine ⟨fun _ => by norm_num [leakPrior], ?_⟩
  simp [leakPrior]

/-- The experiment that leaks `θ` unevenly across `Λ`: `(true, 0) ↦ 0`; `(false, 0) ↦` a fair
coin; `(_, 1) ↦ 1`. Its two signals have distinct Λ-posteriors.
Source: none: infrastructure (audit r1 probe; findings F12)
Kind: D
Fidelity: exact -/
def leakθ : Experiment (Bool × Fin 2) (Fin 2) where
  k := fun p s =>
    if p.2 = 0 then (if p.1 then (if s = 0 then 1 else 0) else 1 / 2) else (if s = 0 then 0 else 1)
  k_mem := fun p => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by
    rcases p with ⟨l, ϑ⟩
    fin_cases ϑ <;> cases l <;> simp [Fin.sum_univ_two]⟩

/-- Guess `θ`, prize `M` (`Λ` is irrelevant to the payoff).
Source: none: infrastructure (audit r1 probe)
Kind: D
Fidelity: exact -/
def guessθ (M : ℝ) : Fin 2 → Bool → Fin 2 → ℝ := fun a _ ϑ => if a = ϑ then M else 0

/-- `sigMass_leakθ`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigMass_leakθ (s : Fin 2) : sigMass leakPrior leakθ s = if s = 0 then 3 / 8 else 5 / 8 := by
  unfold sigMass leakPrior leakθ
  fin_cases s <;> simp [Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

/-- The Λ-posteriors of the two signals: `(2/3, 1/3)` and `(2/5, 3/5)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postΛ_leakθ (s : Fin 2) :
    postΛ leakPrior leakθ s
      = fun l => if s = 0 then (if l then 2 / 3 else 1 / 3) else (if l then 2 / 5 else 3 / 5) := by
  funext l
  unfold postΛ post
  simp only [sigMass_leakθ]
  unfold leakPrior leakθ
  fin_cases s <;> cases l <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The Λ-posteriors differ, so `fΛ` is injective: the Λ-garbling is a relabelling.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fΛ_leakθ_injective : Function.Injective (fΛ leakPrior leakθ) := by
  intro s s' h
  have h' : postΛ leakPrior leakθ s = postΛ leakPrior leakθ s' := congrArg Subtype.val h
  rw [postΛ_leakθ, postΛ_leakθ] at h'
  have := congrFun h' true
  fin_cases s <;> fin_cases s' <;> simp at this ⊢ <;> norm_num at this

open scoped Classical in
/-- At this experiment the Λ-garbling loses nothing: `voiΛ = voi`.
Source: none: infrastructure (findings F12)
Kind: L
Fidelity: n/a -/
theorem voiΛ_leakθ_eq_voi (M : ℝ) :
    voiΛ leakPrior leakθ (menu (guessθ M)) = voi leakPrior leakθ (menu (guessθ M)) := by
  refine le_antisymm (voiΛ_le_voi leakPrior leakθ _) ?_
  have h := bayesValue_le_pushforward_of_injective leakPrior leakθ fΛ_leakθ_injective
    (menu (guessθ M))
  have h' : bayesValue leakPrior leakθ (menu (guessθ M))
      ≤ bayesValue leakPrior (kΛ leakPrior leakθ) (menu (guessθ M)) := by
    unfold kΛ
    convert h
  unfold voiΛ voi
  linarith

/-- `postScore_leakθ`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postScore_leakθ (M : ℝ) (s a : Fin 2) :
    postScore leakPrior leakθ (menu (guessθ M)) s a
      = if s = 0 then (if a = 0 then 3 / 8 * M else 0)
        else (if a = 0 then 1 / 8 * M else 1 / 2 * M) := by
  unfold postScore leakPrior leakθ menu guessθ
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  fin_cases s <;> fin_cases a <;> simp <;> (try norm_num) <;> (try ring)

/-- `voi = 3M/8`: every bit of it is information about `θ`.
Source: none: infrastructure (findings F12)
Kind: L
Fidelity: n/a -/
theorem voi_leakθ {M : ℝ} (hM : 0 ≤ M) : voi leakPrior leakθ (menu (guessθ M)) = 3 / 8 * M := by
  unfold voi
  rw [bayesValue_eq_sum_sup']
  simp_rw [postScore_leakθ M]
  have hprior : priorValue leakPrior (menu (guessθ M)) = M / 2 := by
    unfold priorValue
    rw [sup'_fin_two]
    simp [E, leakPrior, menu, guessθ, Fintype.sum_prod_type]
    ring
  rw [hprior, Fin.sum_univ_two, sup'_fin_two, sup'_fin_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

/-- The Λ-TV bound of P3(a) evaluates to `M/8`.
Source: none: infrastructure (findings F12)
Kind: L
Fidelity: n/a -/
theorem lambdaTV_leakθ (M : ℝ) :
    M * ∑ s, sigMass leakPrior leakθ s * tv (postΛ leakPrior leakθ s) (muΛ leakPrior) = M / 8 := by
  have hmu : muΛ leakPrior = fun _ => 1 / 2 := by
    funext l
    simp [muΛ, leakPrior]
    norm_num
  simp_rw [sigMass_leakθ, postΛ_leakθ, hmu, Fin.sum_univ_two]
  unfold tv
  simp only [Fintype.sum_bool]
  norm_num [abs_of_nonneg, abs_of_nonpos]
  ring

/-- `HVal` fails: given `λ = true`, the signal reveals `θ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem not_hval_leakθ : ¬ HVal leakθ := by
  intro h
  have := h true 0 1 0
  simp [leakθ] at this

open scoped Classical in
/-- **Target 4(v) is false for P3(a)'s definition of the value part.** With `voiΛ` the VOI of the
Λ-posterior garbling (P3(a), `Split.voiΛ`), there is an experiment informative about `θ` beyond
`Λ` (`¬ HVal`), on a menu independent of `Λ`, at which `voiΛ = voi = 3M/8` while P3(a)'s bound
`VOI^Λ ≤ M · E[TV(P(Λ | E), P(Λ))]` evaluates to `M/8`: the inequality fails. This refutes the
*first link* of Target 4(v). The *composed* bound `VOI^Λ ≤ M√(I[Λ:S]/2)` is weaker (Pinsker goes
the other way, so its failure does not follow from this one) and is refuted separately at the same
instance, because `I[Λ : S] ≤ 1/15` there: `SplitComposed.lean`'s
`valuePart_not_bounded_by_lambdaMI` (audit r2, fidelity B1).
Source: [[generalization-final]] S3(a) l. 66, P3(a) l. 113 ("the value part obeys P2 with `Λ_A` in
place of `ω_A`"); mandate Target 4(v); findings F12
Kind: N+
Fidelity: exact (a refutation of the note's claim for its own definition)
Hyps: (a) all -/
theorem valuePart_not_bounded_by_lambdaTV {M : ℝ} (hM : 0 < M) :
    voiΛ leakPrior leakθ (menu (guessθ M)) = voi leakPrior leakθ (menu (guessθ M)) ∧
    voi leakPrior leakθ (menu (guessθ M)) = 3 / 8 * M ∧
    ¬ HVal leakθ ∧
    ¬ voiΛ leakPrior leakθ (menu (guessθ M))
        ≤ M * ∑ s, sigMass leakPrior leakθ s * tv (postΛ leakPrior leakθ s) (muΛ leakPrior) := by
  refine ⟨voiΛ_leakθ_eq_voi M, voi_leakθ hM.le, not_hval_leakθ, ?_⟩
  rw [voiΛ_leakθ_eq_voi M, voi_leakθ hM.le, lambdaTV_leakθ M]
  intro h
  linarith

/-! ### Counterexample 2: the "informative about Λ only" lift can exceed the whole VOI -/

/-- The prior `P(λ) = ½`, `P(ϑ = λ | λ) = 9/10` on `Λ × θ = Fin 2 × Fin 2`.
Source: none: infrastructure (audit r1, fidelity B1's second example; findings F12)
Kind: D
Fidelity: exact -/
def mfPrior : Fin 2 × Fin 2 → ℝ := fun p => if p.1 = p.2 then 9 / 20 else 1 / 20

/-- `mfPrior_mem`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mfPrior_mem : mfPrior ∈ stdSimplex ℝ (Fin 2 × Fin 2) := by
  refine ⟨fun p => by unfold mfPrior; split_ifs <;> norm_num, ?_⟩
  simp [mfPrior, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- The experiment that reveals `θ` exactly (on `Fin 2 × Fin 2`).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def revealΘ2 : Experiment (Fin 2 × Fin 2) (Fin 2) where
  k := fun p s => if s = p.2 then 1 else 0
  k_mem := fun p => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by simp⟩

/-- **The Λ-lift of `revealΘ2`** ("the experiment informative about `Λ` only"): the signal's
`Λ`-likelihood `P(s | λ) = ∑_ϑ' P(ϑ' | λ)·k((λ, ϑ'), s)` read back as a kernel constant in `ϑ`:
`9/10` if `s = λ`, `1/10` otherwise (`meanField2_eq_lift`). It satisfies `HVal` by construction
and is **not** a garbling of `revealΘ2`.
Source: [[generalization-final]] S3 l. 65 ("the VOI `E_a` would have if it were informative about
`Λ` only"); findings F12
Kind: D
Fidelity: exact (one reading of the gloss, made concrete) -/
def meanField2 : Experiment (Fin 2 × Fin 2) (Fin 2) where
  k := fun p s => if s = p.1 then 9 / 10 else 1 / 10
  k_mem := fun p => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by
    rcases p with ⟨l, ϑ⟩
    fin_cases l <;> simp [Fin.sum_univ_two] <;> norm_num⟩

/-- `meanField2` is the Λ-lift of `revealΘ2` under `mfPrior`:
`k^Λ((λ, ϑ), s) = ∑_ϑ' (P(λ, ϑ') / P(λ)) · k((λ, ϑ'), s)`.
Source: none: infrastructure (findings F12)
Kind: L
Fidelity: n/a -/
theorem meanField2_eq_lift (p : Fin 2 × Fin 2) (s : Fin 2) :
    meanField2.k p s = ∑ ϑ', (mfPrior (p.1, ϑ') / muΛ mfPrior p.1) * revealΘ2.k (p.1, ϑ') s := by
  rcases p with ⟨l, ϑ⟩
  unfold meanField2 revealΘ2 mfPrior muΛ
  fin_cases l <;> fin_cases s <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The lift satisfies `HVal`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hval_meanField2 : HVal meanField2 := by
  intro l ϑ ϑ' s
  rfl

/-- The value function `V(a, λ, ϑ) = 𝟙[a = λ] − ½·𝟙[a = ϑ]`.
Source: none: infrastructure (audit r1, fidelity B1's second example)
Kind: D
Fidelity: exact -/
def mfV : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun a l ϑ => (if a = l then 1 else 0) - 1 / 2 * (if a = ϑ then 1 else 0)

/-- The prior value is `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mf_priorValue : priorValue mfPrior (menu mfV) = 1 / 4 := by
  unfold priorValue
  rw [sup'_fin_two]
  simp [E, mfPrior, menu, mfV, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- `postScore_revealΘ2`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postScore_revealΘ2 (s a : Fin 2) :
    postScore mfPrior revealΘ2 (menu mfV) s a = if a = s then 1 / 5 else 1 / 20 := by
  unfold postScore mfPrior revealΘ2 menu mfV
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases s <;> fin_cases a <;> simp <;> norm_num

/-- `postScore_meanField2`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postScore_meanField2 (s a : Fin 2) :
    postScore mfPrior meanField2 (menu mfV) s a = if a = s then 49 / 200 else 1 / 200 := by
  unfold postScore mfPrior meanField2 menu mfV
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases s <;> fin_cases a <;> simp <;> norm_num

/-- `voi = 3/20` for the experiment that reveals `θ`.
Source: none: infrastructure (findings F12)
Kind: L
Fidelity: n/a -/
theorem mf_voi_reveal : voi mfPrior revealΘ2 (menu mfV) = 3 / 20 := by
  unfold voi
  rw [bayesValue_eq_sum_sup', mf_priorValue]
  simp_rw [postScore_revealΘ2]
  rw [Fin.sum_univ_two, sup'_fin_two, sup'_fin_two]
  norm_num

/-- `voi = 6/25` for the Λ-lift.
Source: none: infrastructure (findings F12)
Kind: L
Fidelity: n/a -/
theorem mf_voi_meanField : voi mfPrior meanField2 (menu mfV) = 6 / 25 := by
  unfold voi
  rw [bayesValue_eq_sum_sup', mf_priorValue]
  simp_rw [postScore_meanField2]
  rw [Fin.sum_univ_two, sup'_fin_two, sup'_fin_two]
  norm_num

/-- **The "informative about `Λ` only" reading breaks `voiθ ≥ 0`.** The Λ-lift of the experiment
(which satisfies `HVal`, hence P3(a)'s Λ-TV bound by `voi_le_mul_sum_tvΛ_of_hval`) has a larger VOI
than the experiment itself: `6/25 > 3/20`. So the remainder `voi − VOI^Λ` is negative under this
reading, and P3(a)'s first sentence ("`voiθ ≥ 0` by Blackwell") fails: the lift is not a
garbling.
Source: [[generalization-final]] S3 l. 65, P3(a) l. 113; audit r1 (fidelity B1); findings F12
Kind: N+
Fidelity: exact (a refutation of the note's claim for the gloss's reading)
Hyps: (a) all -/
theorem meanField_voi_gt_voi :
    HVal meanField2 ∧
    (∀ p s, meanField2.k p s
      = ∑ ϑ', (mfPrior (p.1, ϑ') / muΛ mfPrior p.1) * revealΘ2.k (p.1, ϑ') s) ∧
    voi mfPrior revealΘ2 (menu mfV) < voi mfPrior meanField2 (menu mfV) := by
  refine ⟨hval_meanField2, meanField2_eq_lift, ?_⟩
  rw [mf_voi_reveal, mf_voi_meanField]
  norm_num

/-! ### Under H_val the value problem is its Λ-marginal: Target 4(v) where it holds -/

variable {S Λ Θ : Type} [Fintype S] [Fintype Λ] [Fintype Θ]

/-- **The Λ-marginal experiment**: the kernel read at a reference `ϑ₀` (under `HVal` it does not
depend on `ϑ₀`).
Source: [[generalization-final]] S3(c) l. 68 (H_val); none: infrastructure
Kind: D
Fidelity: exact under `HVal` -/
def margΛ (k : Experiment (Λ × Θ) S) (ϑ₀ : Θ) : Experiment Λ S where
  k := fun l s => k.k (l, ϑ₀) s
  k_mem := fun l => k.k_mem (l, ϑ₀)

/-- The Λ-marginal of a prior is in the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem muΛ_mem {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) : muΛ μ ∈ stdSimplex ℝ Λ := by
  refine ⟨fun l => Finset.sum_nonneg fun ϑ _ => hμ.1 (l, ϑ), ?_⟩
  rw [← hμ.2, Fintype.sum_prod_type]
  rfl

/-- Under `HVal`, the signal masses of the Λ-marginal agree with the original's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigMass_margΛ {μ : Λ × Θ → ℝ} {k : Experiment (Λ × Θ) S} (hk : HVal k) (ϑ₀ : Θ)
    (s : S) : sigMass (muΛ μ) (margΛ k ϑ₀) s = sigMass μ k s := by
  unfold sigMass margΛ muΛ
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ϑ _ => ?_
  rw [hk l ϑ₀ ϑ s]

/-- Under `HVal`, the Λ-posterior of `k` is the posterior of the Λ-marginal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postΛ_eq_post_margΛ {μ : Λ × Θ → ℝ} {k : Experiment (Λ × Θ) S} (hk : HVal k) (ϑ₀ : Θ)
    (s : S) : postΛ μ k s = post (muΛ μ) (margΛ k ϑ₀) s := by
  funext l
  unfold postΛ post
  rw [← Finset.sum_div, sigMass_margΛ hk ϑ₀ s]
  congr 1
  unfold margΛ muΛ
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ϑ _ => by rw [hk l ϑ₀ ϑ s]

/-- Under `HVal`, the posterior scores of `(μ, k, menu V)` are those of `(μΛ, margΛ k, V̄)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postScore_margΛ {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) {k : Experiment (Λ × Θ) S}
    (hk : HVal k) (ϑ₀ : Θ) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) (s : S) (a : Fin (n + 1)) :
    postScore (muΛ μ) (margΛ k ϑ₀) (fun a => Vbar μ V a) s a = postScore μ k (menu V) s a := by
  unfold postScore margΛ menu
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show muΛ μ l * k.k (l, ϑ₀) s * Vbar μ V a l = k.k (l, ϑ₀) s * (Vbar μ V a l * muΛ μ l) by
    ring, Vbar_mul_muΛ hμ.1 V a l, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ϑ _ => by rw [hk l ϑ₀ ϑ s]; ring

/-- The prior expectation of `menu V a` is the `μΛ`-expectation of the profile `V̄ a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_menu_eq_E_Vbar {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) {n : ℕ}
    (V : Fin (n + 1) → Λ → Θ → ℝ) (a : Fin (n + 1)) :
    E μ (menu V a) = E (muΛ μ) (fun l => Vbar μ V a l) := by
  unfold E menu
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (muΛ μ l), Vbar_mul_muΛ hμ.1 V a l]

/-- The prior value of `(μ, menu V)` is that of `(μΛ, V̄)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem priorValue_margΛ {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) {n : ℕ}
    (V : Fin (n + 1) → Λ → Θ → ℝ) :
    priorValue μ (menu V) = priorValue (muΛ μ) (fun a => Vbar μ V a) := by
  unfold priorValue
  exact Finset.sup'_congr univ_nonempty rfl fun a _ => E_menu_eq_E_Vbar hμ V a

/-- **Under H_val the value problem is its Λ-marginal**: `voi μ k (menu V) = voi μΛ (margΛ k) V̄`.
So the Target 3 chain applies to `(μΛ, margΛ k, V̄)` verbatim, with `Λ` in place of `ω` — this is
the content behind P3(a)'s "the value part obeys P2 with `Λ_A` in place of `ω_A`", true exactly
under `HVal` (where `voi = voiΛ`, `voi_eq_voiΛ_of_hval`).
Source: [[generalization-final]] S3(c) l. 68, P3(a) l. 113; mandate Target 4(v)
Kind: P
Fidelity: exact
Hyps: (a) all — `hμ` simplex, `hk : HVal k` (the claim's antecedent) -/
theorem voi_eq_voi_margΛ_of_hval [DecidableEq S] {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ))
    {k : Experiment (Λ × Θ) S} (hk : HVal k) (ϑ₀ : Θ) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) :
    voi μ k (menu V) = voi (muΛ μ) (margΛ k ϑ₀) (fun a => Vbar μ V a) := by
  unfold voi
  rw [bayesValue_eq_sum_sup', bayesValue_eq_sum_sup', priorValue_margΛ hμ V]
  congr 1
  exact Finset.sum_congr rfl fun s _ =>
    Finset.sup'_congr univ_nonempty rfl fun a _ => (postScore_margΛ hμ hk ϑ₀ V s a).symm

/-- A prior in the simplex has a supported `λ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_muΛ_ne_zero {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) :
    ∃ l, muΛ μ l ≠ 0 := by
  by_contra h
  push Not at h
  have := (muΛ_mem hμ).2
  rw [Finset.sum_eq_zero (fun l _ => h l)] at this
  exact zero_ne_one this

open scoped Classical in
/-- The value profile with its junk values at null `λ` replaced by the value at a supported `l₀`:
it agrees with `Vbar` on the support of `μΛ` (so the VOI does not see the change,
`Voi.voi_congr_of_support`), and its within-action range over *all* `λ` is `Vbar`'s range over the
support (`VbarSupp_range`). Infrastructure for stating the range hypothesis of the `HVal` bounds
on the support only (audit r2, adversarial item 6).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def VbarSupp (μ : Λ × Θ → ℝ) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) (l₀ : Λ) (a : Fin (n + 1))
    (l : Λ) : ℝ :=
  if muΛ μ l = 0 then Vbar μ V a l₀ else Vbar μ V a l

open scoped Classical in
/-- `VbarSupp` agrees with `Vbar` on the support of `μΛ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem VbarSupp_eq_of_ne_zero (μ : Λ × Θ → ℝ) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) (l₀ : Λ)
    (a : Fin (n + 1)) {l : Λ} (hl : muΛ μ l ≠ 0) : Vbar μ V a l = VbarSupp μ V l₀ a l := by
  unfold VbarSupp
  rw [if_neg hl]

open scoped Classical in
/-- The full range of `VbarSupp` is the supported range of `Vbar`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem VbarSupp_range {μ : Λ × Θ → ℝ} {n : ℕ} {V : Fin (n + 1) → Λ → Θ → ℝ} {M : ℝ}
    (hM : ∀ a l l', muΛ μ l ≠ 0 → muΛ μ l' ≠ 0 → Vbar μ V a l - Vbar μ V a l' ≤ M) {l₀ : Λ}
    (hl₀ : muΛ μ l₀ ≠ 0) : ∀ a l l', VbarSupp μ V l₀ a l - VbarSupp μ V l₀ a l' ≤ M := by
  intro a l l'
  unfold VbarSupp
  by_cases h1 : muΛ μ l = 0
  · rw [if_pos h1]
    by_cases h2 : muΛ μ l' = 0
    · rw [if_pos h2]
      exact hM a l₀ l₀ hl₀ hl₀
    · rw [if_neg h2]
      exact hM a l₀ l' hl₀ h2
  · rw [if_neg h1]
    by_cases h2 : muΛ μ l' = 0
    · rw [if_pos h2]
      exact hM a l l₀ h1 hl₀
    · rw [if_neg h2]
      exact hM a l l' h1 h2

open scoped Classical in
/-- **Target 4(v), first inequality, where it holds**: under `HVal`,
`voi ≤ M · ∑_s P(s) · tv(postΛ s, μΛ)` with `M` the within-action range of the profile `V̄` over
the *support* of `μΛ` (`Vbar` is junk `0` at a null `λ`; the range hypothesis does not see it —
audit r2, adversarial item 6). Attained at `meanField2` (`SplitComposed.meanField2_tv_bound_attained`).
Source: [[generalization-final]] S3(a) l. 66, P3(a) l. 113 ("`VOI^Λ ≤ M·E TV(P(Λ | E), P(Λ))`");
mandate Target 4(v)
Kind: C
Fidelity: weaker: under `HVal` only (without it the claim is false for P3(a)'s definition,
`valuePart_not_bounded_by_lambdaTV`, and `voiθ ≥ 0` fails for the lift reading,
`meanField_voi_gt_voi`)
Hyps: (a) all — `hμ` simplex, `hk : HVal k`, `hM` the profile's range on the support -/
theorem voi_le_mul_sum_tvΛ_of_hval [DecidableEq S] {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ))
    {k : Experiment (Λ × Θ) S} (hk : HVal k) (ϑ₀ : Θ) {n : ℕ} {V : Fin (n + 1) → Λ → Θ → ℝ} {M : ℝ}
    (hM : ∀ a l l', muΛ μ l ≠ 0 → muΛ μ l' ≠ 0 → Vbar μ V a l - Vbar μ V a l' ≤ M) :
    voi μ k (menu V) ≤ M * ∑ s, sigMass μ k s * tv (postΛ μ k s) (muΛ μ) := by
  rw [voi_eq_voi_margΛ_of_hval hμ hk ϑ₀ V]
  obtain ⟨l₀, hl₀⟩ := exists_muΛ_ne_zero hμ
  rw [voi_congr_of_support (margΛ k ϑ₀) (u' := VbarSupp μ V l₀)
    (fun a l hl => VbarSupp_eq_of_ne_zero μ V l₀ a hl)]
  have h := voi_le_mul_sum_tv (muΛ_mem hμ) (margΛ k ϑ₀) (u := VbarSupp μ V l₀)
    (VbarSupp_range hM hl₀)
  simp_rw [sigMass_margΛ hk ϑ₀, ← postΛ_eq_post_margΛ hk ϑ₀] at h
  exact h

open scoped Classical in
/-- **Target 4(v), composed, where it holds**: under `HVal`, `voi ≤ M · √(I[Λ : S] / 2)` over PFR's
`mutualInfo` on the joint measure of `(μΛ, margΛ k)` on `Λ × S` — the law of the pair
`(Λ, S)` (the Λ-marginal of the joint of `(μ, k)`; the identification of the two joints is not
stated). With `voi = voiΛ` under `HVal`, this is P3(a)'s `VOI^Λ ≤ M√(½ I(Λ_A ; E_a))`. `M` is the
profile's within-action range over the support of `μΛ` (audit r2, adversarial item 6).
Source: [[generalization-final]] S3(a) l. 66, P3(a) l. 113; mandate Target 4(v) ("compose")
Kind: C
Fidelity: weaker: under `HVal` only (as above); `M` is the profile's range on the support
Hyps: (a) all -/
theorem voi_le_mul_sqrt_mutualInfoΛ_of_hval [DecidableEq S] [MeasurableSpace Λ]
    [MeasurableSingletonClass Λ] [MeasurableSpace S] [MeasurableSingletonClass S] {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) {k : Experiment (Λ × Θ) S}
    (hk : HVal k) (ϑ₀ : Θ) {n : ℕ} {V : Fin (n + 1) → Λ → Θ → ℝ} {M : ℝ}
    (hM : ∀ a l l', muΛ μ l ≠ 0 → muΛ μ l' ≠ 0 → Vbar μ V a l - Vbar μ V a l' ≤ M) (hM0 : 0 ≤ M) :
    voi μ k (menu V)
      ≤ M * Real.sqrt (I[Prod.fst : Prod.snd ; Bridge.joint (muΛ μ) (margΛ k ϑ₀) (muΛ_mem hμ)] / 2) := by
  rw [voi_eq_voi_margΛ_of_hval hμ hk ϑ₀ V]
  obtain ⟨l₀, hl₀⟩ := exists_muΛ_ne_zero hμ
  rw [voi_congr_of_support (margΛ k ϑ₀) (u' := VbarSupp μ V l₀)
    (fun a l hl => VbarSupp_eq_of_ne_zero μ V l₀ a hl)]
  exact Bridge.voi_le_mul_sqrt_mutualInfo (margΛ k ϑ₀) (muΛ_mem hμ) (VbarSupp_range hM hl₀) hM0

end

end Cleanroom.Info.InfoVoiLatents.Split
