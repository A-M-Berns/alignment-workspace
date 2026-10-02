import Cleanroom.Corrigibility.CorrLegitGeneral.Transfer
import Cleanroom.Found.LitDdbFrames.Hull
import Cleanroom.Found.LitDdbFrames.Cycle

/-!
# corr-legit-general — T6: composition along a two-step chain

**The mixture lemma is the theorem.** Every threshold inequality is linear in the deferrer, so
the deferrers totally trusting a frame on `Q` form a convex cone (`totalTrustWrt_sum`, Defs).
Composition then needs exactly one thing at step one: that the restricted deferrer is a
nonnegative combination of its candidates (`MixtureOfCands`). Global `L`-conditioned Total
Trust supplies it through Theorem 4.1's hull half (`mixture_of_legitimizingTT`); local trust does
not (`WitnessesCompose.lean`, the T6(c) counterexample). With the mixture at step one,
`restrict π (L₁₂ ∩ L₂₃) = ∑ λ_ρ • restrict ρ L₂₃`, and each summand trusts the third frame on
`Q` — candidates with `ρ(L₂₃) = 0` contribute the zero deferrer, which trusts trivially, so no
positivity clause is needed (Known issues 4).

`compose_value` is mm I7.1's independent Value-form proof (add the followed strategy as an
option), which needs Value at step one.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-! ## Linearity of restriction; the global mixture lemma -/

/-- Restriction commutes with scaling.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_smul (c : ℝ) (π : W → ℝ) (L : Finset W) :
    restrict (c • π) L = c • restrict π L := by
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, restrict_apply]
  split_ifs <;> ring

/-- Restriction commutes with finite sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_sum {ι : Type*} (s : Finset ι) (ρ : ι → W → ℝ) (L : Finset W) :
    restrict (∑ i ∈ s, ρ i) L = ∑ i ∈ s, restrict (ρ i) L := by
  funext w
  simp only [restrict_apply, Finset.sum_apply]
  by_cases h : w ∈ L <;> simp [h]

/-- Total Trust is closed under nonnegative scaling.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem totalTrust_smul {c : ℝ} (hc : 0 ≤ c) {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) :
    TotalTrust (c • π) F := by
  rw [totalTrust_iff_totalTrustWrt_id] at h ⊢
  exact totalTrustWrt_smul hc h

/-- **The mixture lemma, global form**: Total Trust is closed under nonnegative linear
combinations of deferrers.
Source: [[legitimacy-general-final]] Statement 9(b) l. 67 ("the set of trusting deferrers is
convex"); [[ddb-mm-authors]] C6 l. 95
Kind: P
Fidelity: exact (cone form)
Hyps: (a) none -/
theorem totalTrust_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρ : ι → W → ℝ) (F : Frame W)
    (hc : ∀ i ∈ s, 0 ≤ c i) (h : ∀ i ∈ s, TotalTrust (ρ i) F) :
    TotalTrust (∑ i ∈ s, c i • ρ i) F := by
  rw [totalTrust_iff_totalTrustWrt_id]
  exact totalTrustWrt_sum s c ρ id F hc (fun i hi => totalTrust_iff_totalTrustWrt_id.1 (h i hi))

/-- **The hull hypothesis at step one, cone form**: the (unnormalized) deferrer is a nonnegative
combination of its candidates. Normalizing, this is `π ∈ convexHull C_π`; the cone form needs no
positivity of the total mass.
Source: [[legitimacy-general-final]] Statement 9(b) l. 67 ("`π_{L₁₂} ∈ CH({ρ})`")
Kind: D
Fidelity: exact (cone form of the hull hypothesis) -/
def MixtureOfCands (F : Frame W) (π : W → ℝ) : Prop :=
  ∃ lam : (W → ℝ) → ℝ, (∀ ρ ∈ F.cands π, 0 ≤ lam ρ) ∧ π = ∑ ρ ∈ F.cands π, lam ρ • ρ

/-- **Global `L`-conditioned Total Trust supplies the mixture at step one** (Theorem 4.1's hull
half for `π_{L₁₂}`, scaled back by `π(L₁₂)`).
Source: [[legitimacy-general-final]] Statement 9(a) l. 67, Proofs l. 138 (Thm 4.1 ⇒);
[[Deference Done Better]] Lemma 7.2 (`TotalTrust.mem_convexHull_cands`)
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L`, `LegitimizingTT π F L` -/
theorem mixture_of_legitimizingTT {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {L : Finset W}
    (hL : 0 < mass π L) (h : LegitimizingTT π F L) : MixtureOfCands F (restrict π L) := by
  have hcpos : (0 : ℝ) < (mass π L)⁻¹ := inv_pos.2 hL
  have hmem := restrict_normalize_mem hπ hL
  have hTT : TotalTrust ((mass π L)⁻¹ • restrict π L) F := (totalTrust_smul_iff hcpos _ _).2 h
  obtain ⟨lam, hl0, _, hπeq, _⟩ :=
    F.exists_weights_of_hull hmem (TotalTrust.mem_convexHull_cands hmem hTT)
  rw [cands_smul F hcpos] at hπeq hl0
  refine ⟨fun ρ => mass π L * lam ρ, fun ρ hρ => mul_nonneg hL.le (hl0 ρ hρ), ?_⟩
  have e : restrict π L = mass π L • ((mass π L)⁻¹ • restrict π L) := by
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  conv_lhs => rw [e, ← hπeq]
  rw [smul_sum]
  apply sum_congr rfl
  intro ρ _
  rw [smul_smul]

/-! ## Composition -/

/-- **Local composition under the mixture hypothesis at step one** (Statement 9(b)): if
`restrict π L₁₂` is a nonnegative combination of its `F₂`-candidates and every such candidate
`ρ` has `L₂₃`-conditioned Total Trust toward `F₃` on `Q`, then `π` has
`(L₁₂ ∩ L₂₃)`-conditioned Total Trust toward `F₃` on `Q`. Proof:
`restrict π (L₁₂ ∩ L₂₃) = ∑ λ_ρ • restrict ρ L₂₃` by linearity of restriction, and the
mixture lemma. Candidates with `ρ(L₂₃) = 0` contribute the zero deferrer (no positivity clause).
Source: [[legitimacy-general-final]] Statement 9(b) l. 67, Proofs l. 140; corr-wf14b-057
Kind: P
Fidelity: exact (the hull hypothesis in cone form)
Hyps: (a) `MixtureOfCands F₂ (restrict π L₁₂)`; step-two trust at every candidate -/
theorem compose_local_of_mixture {Q : W → C} {π : W → ℝ} {F₂ F₃ : Frame W} {L₁₂ L₂₃ : Finset W}
    (hmix : MixtureOfCands F₂ (restrict π L₁₂))
    (h₂ : ∀ ρ ∈ F₂.cands (restrict π L₁₂), LegitTotalTrustWrt Q ρ F₃ L₂₃) :
    LegitTotalTrustWrt Q π F₃ (L₁₂ ∩ L₂₃) := by
  obtain ⟨lam, hl0, hπeq⟩ := hmix
  unfold LegitTotalTrustWrt
  have e : restrict π (L₁₂ ∩ L₂₃) =
      ∑ ρ ∈ F₂.cands (restrict π L₁₂), lam ρ • restrict ρ L₂₃ := by
    conv_lhs => rw [← restrict_restrict, hπeq, restrict_sum]
    apply sum_congr rfl
    intro ρ _
    exact restrict_smul _ _ _
  rw [e]
  exact totalTrustWrt_sum _ _ _ Q F₃ hl0 (fun ρ hρ => h₂ ρ hρ)

/-- **Global composition conditional on the intersection** (Statement 9(a)): `L₁₂`-conditioned
Total Trust toward `F₂`, and `L₂₃`-conditioned Total Trust toward `F₃` at every legitimate
`F₂`-candidate, give `(L₁₂ ∩ L₂₃)`-conditioned Total Trust toward `F₃`. The source routes through
Theorem 4.1 in both directions and adds a clause `ρ(L₂₃) > 0`; only the hull half at step one is
needed and the clause is harmless (Known issues 4).
Source: [[legitimacy-general-final]] Statement 9(a) l. 67, Proofs l. 138; [[ddb-mm-authors]]
C6/T3 l. 95, l. 141; [[mm]] I7.1 l. 164; corr-wf14b-057, corr-wf13-2-060, corr-wf13-037
Kind: C
Fidelity: exact (the source's positivity clause `ρ(L₂₃) > 0` at step two is vacuous: at a
candidate with `ρ(L₂₃) = 0` the step-two hypothesis is `TotalTrust 0 F₃`, which holds for free,
so the two hypothesis packages are equivalent — audit r3 N1, both lenses; composition of Theorem
4.1's hull half, `mixture_of_legitimizingTT`, with the cone lemma through
`compose_local_of_mixture`, the new step)
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L₁₂`; step-one and step-two trust. The conclusion's own
guard `0 < mass π (L₁₂ ∩ L₂₃)` is not assumed: when the intersection is `π`-null the conclusion
is the vacuous `TotalTrust 0 F₃` (the mandate's first trap; `compose_positive_instance` has
`π(L) = 3/4`) -/
theorem compose_global {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F₂ F₃ : Frame W} {L₁₂ L₂₃ : Finset W}
    (hL : 0 < mass π L₁₂) (h₁ : LegitimizingTT π F₂ L₁₂)
    (h₂ : ∀ ρ ∈ F₂.cands (restrict π L₁₂), LegitimizingTT ρ F₃ L₂₃) :
    LegitimizingTT π F₃ (L₁₂ ∩ L₂₃) := by
  rw [← legitTotalTrustWrt_id_iff]
  exact compose_local_of_mixture (mixture_of_legitimizingTT hπ hL h₁)
    (fun ρ hρ => (legitTotalTrustWrt_id_iff).2 (h₂ ρ hρ))

/-- **Global composition with a local second step**: global `L₁₂`-conditioned trust at step one
and `L₂₃`-conditioned trust *on `Q`* at step two give `(L₁₂ ∩ L₂₃)`-conditioned trust on `Q`.
Source: [[legitimacy-general-final]] Statement 9(b) l. 67 (the hull hypothesis is "a
global-type condition")
Kind: C
Fidelity: exact
Hyps: (a) as `compose_global` -/
theorem compose_local_of_global {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F₂ F₃ : Frame W}
    {L₁₂ L₂₃ : Finset W} (hL : 0 < mass π L₁₂) (h₁ : LegitimizingTT π F₂ L₁₂)
    (h₂ : ∀ ρ ∈ F₂.cands (restrict π L₁₂), LegitTotalTrustWrt Q ρ F₃ L₂₃) :
    LegitTotalTrustWrt Q π F₃ (L₁₂ ∩ L₂₃) :=
  compose_local_of_mixture (mixture_of_legitimizingTT hπ hL h₁) h₂

/-- **ddb-mm-authors C6, the `L = univ` instance**: Total Trust composes along chains of frames.
Source: [[ddb-mm-authors]] C6 l. 95; [[legitimacy]] R5.6 l. 103
Kind: L
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem compose_univ {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F₂ F₃ : Frame W}
    (h₁ : TotalTrust π F₂) (h₂ : ∀ ρ ∈ F₂.cands π, TotalTrust ρ F₃) : TotalTrust π F₃ := by
  have hL : 0 < mass π univ := by rw [mass_univ hπ]; exact one_pos
  have h₁' : LegitimizingTT π F₂ univ := by unfold LegitimizingTT; rwa [restrict_univ]
  have h₂' : ∀ ρ ∈ F₂.cands (restrict π univ), LegitimizingTT ρ F₃ univ := by
    intro ρ hρ
    rw [restrict_univ] at hρ
    unfold LegitimizingTT; rw [restrict_univ]; exact h₂ ρ hρ
  have := compose_global hπ.1 hL h₁' h₂'
  unfold LegitimizingTT at this
  rwa [univ_inter, restrict_univ] at this

/-! ## mm I7.1: the Value-form route -/

/-- The strategy that follows `S'` at every candidate of `π` and makes an informed choice
elsewhere, for the menu `𝒪 ∪ {follow S'}`. Cellwise by construction.
Source: [[mm]] I7.1 l. 164 (proof); the null-world repair is this package's
Kind: D
Fidelity: n/a -/
def followOrInformed (F : Frame W) (π : W → ℝ) (𝒪 : DecisionProblem W) (f : W → ℝ) (w : W) :
    W → ℝ :=
  if F.P w ∈ F.cands π then f else F.informedStrategy (insert f 𝒪) (insert_nonempty f 𝒪) w

/-- **mm I7.1 (legitimacy composes, Value form)**: if `π` values `F₂` and every candidate of `π`
values `F₃`, then `π` values `F₃`. Proof: for a strategy `S` recommended by `F₃`, the random
variable `f := w ↦ S w w` ("follow `S`") is an option; every candidate `ρ` of `π` has
`E_ρ(O) ≤ E_ρ(f)` for `O ∈ 𝒪` (it values `F₃`), so the strategy that chooses `f` at every
candidate (and an informed option at the `π`-null worlds, where the hypothesis says nothing) is
recommended by `F₂` for `𝒪 ∪ {f}`; `π` values `F₂`, so `E_π(O) ≤ E_π(f) = E_π(S)`. The
source's proof silently uses the hypothesis at `π`-null worlds; the repair is the informed choice
there.
Source: [[mm]] I7.1 l. 164; corr-wf13-037
Kind: P
Fidelity: exact (null-world repair disclosed)
Hyps: (a) `π ∈ stdSimplex ℝ W`, `Value π F₂`, Value at every candidate -/
theorem compose_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F₂ F₃ : Frame W}
    (h₁ : Value π F₂) (h₂ : ∀ ρ ∈ F₂.cands π, Value ρ F₃) : Value π F₃ := by
  intro 𝒪 hne S hS o ho
  set f : W → ℝ := fun w => S w w with hf
  have hval_f : stratValue π S = E π f := by simp [stratValue, E, hf]
  -- every candidate prefers `f` to every option of `𝒪`
  have hpref : ∀ w, F₂.P w ∈ F₂.cands π → ∀ o ∈ 𝒪, E (F₂.P w) o ≤ E (F₂.P w) f := by
    intro w hw o ho
    have := h₂ _ hw 𝒪 hne S hS o ho
    simpa [stratValue, E, hf] using this
  set T := followOrInformed F₂ π 𝒪 f with hT
  have hTrec : F₂.Recommended (insert f 𝒪) T := by
    have hinf := F₂.informedStrategy_recommended (insert f 𝒪) (insert_nonempty f 𝒪)
    refine ⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o' ho' => ?_⟩
    · simp only [hT, followOrInformed]
      split_ifs
      · exact mem_insert_self f 𝒪
      · exact hinf.1.1 w
    · simp only [hT, followOrInformed, hwv]
      split_ifs
      · rfl
      · exact hinf.1.2 w v hwv
    · simp only [hT, followOrInformed]
      split_ifs with hw
      · rcases mem_insert.1 ho' with rfl | ho''
        · exact le_rfl
        · exact hpref w hw o' ho''
      · exact hinf.2 w o' ho'
  have hT_eq : stratValue π T = E π f := by
    unfold stratValue E
    apply sum_congr rfl
    intro w _
    rcases (hπ.1 w).lt_or_eq with hw | hw
    · have hc : F₂.P w ∈ F₂.cands π := F₂.P_mem_cands hw
      simp [hT, followOrInformed, hc]
    · rw [← hw]; simp
  have := h₁ (insert f 𝒪) (insert_nonempty f 𝒪) T hTrec o (mem_insert_of_mem ho)
  rw [hT_eq] at this
  rw [hval_f]
  exact this

end

end Cleanroom.Corrigibility.CorrLegitGeneral
