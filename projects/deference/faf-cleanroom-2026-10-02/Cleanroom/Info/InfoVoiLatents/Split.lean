import Cleanroom.Info.InfoVoiLatents.Voi
import Cleanroom.Info.InfoVoiLatents.Coverage

/-!
# info-voi-latents — the value/empirical split and the θ hole (Target 4, carrier (i))

* `pushforward k f`: the experiment obtained by post-processing signals through `f : S → T`;
  `blackwellLE_pushforward` (it is a garbling of `k`).
* **`bayesValue_le_of_blackwellLE`**: a garbling cannot raise the Bayes value (the easy direction of
  Blackwell's theorem; `tt-finite-frames` may re-prove or import it). Hence
  `voi_le_of_blackwellLE`, `voi_pushforward_le`.
* The value model `ω = Λ × θ`: `muΛ`, `Vbar` (product form `Vbar_mul_muΛ`), `menu V`, the
  Λ-posterior `postΛ` (the Λ-marginal of the posterior), the Λ-garbling `kΛ` (signals
  identified by their Λ-posterior; `PostT` is the finite set of attained posteriors), `voiΛ`,
  and **`voiΛ_le_voi`** — the split `voiθ := voi − voiΛ ≥ 0` is a definition; this is its content.
* **`HVal`** (the signal is uninformative about `θ` beyond `Λ`, as the kernel identity
  `k (λ, ϑ) s = k (λ, ϑ') s`) and **`voi_eq_voiΛ_of_hval`**: under `HVal`, `voi = voiΛ`
  (`postScore_eq_sigMass_mul_G`: the posterior expectation of every action depends on `s`
  only through the Λ-posterior).
* **The θ-hole witness** `thetaHole_*`: `Λ = Unit`, `θ = Fin 2` uniform, `k` reveals `θ`: `voi = M/2`
  while `voiΛ = 0` and every value gauge is `0` (`err_unit`, `dis_unit`).

Mandate: Target 4 (i), (ii), (iv), witness. (iii) is `Shannon.mutualInfo_pair_left`.
-/

namespace Cleanroom.Info.InfoVoiLatents.Split

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents.Voi

noncomputable section

set_option linter.unusedSectionVars false

variable {W S T : Type} [Fintype W] [Fintype S] [Fintype T]

/-! ### Garbling cannot raise the Bayes value -/

/-- **Pushforward** of an experiment along a signal map: `(pushforward k f) w t = ∑ s ∈ f⁻¹ t, k w s`.
Source: [[generalization-final]] P3(a) l. 113 ("the garbling of `E_a` that reveals only …")
Kind: D
Fidelity: exact -/
def pushforward [DecidableEq T] (k : Experiment W S) (f : S → T) : Experiment W T where
  k := fun w t => ∑ s ∈ univ.filter (fun s => f s = t), k.k w s
  k_mem := fun w => ⟨fun t => Finset.sum_nonneg fun s _ => (k.k_mem w).1 s, by
    rw [Finset.sum_fiberwise univ f (k.k w)]
    exact (k.k_mem w).2⟩

/-- The kernel of a pushforward, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem pushforward_k [DecidableEq T] (k : Experiment W S) (f : S → T) (w : W) (t : T) :
    (pushforward k f).k w t = ∑ s ∈ univ.filter (fun s => f s = t), k.k w s := rfl

/-- A pushforward is a garbling (through the deterministic channel `𝟙[f s = t]`).
Source: none: infrastructure (Target 4(ii))
Kind: L
Fidelity: n/a -/
theorem blackwellLE_pushforward [DecidableEq T] (k : Experiment W S) (f : S → T) :
    BlackwellLE (pushforward k f) k := by
  refine ⟨fun s t => if f s = t then 1 else 0,
    fun s => ⟨fun t => by dsimp only; split_ifs <;> norm_num, by simp⟩, ?_⟩
  intro w t
  simp only [pushforward_k, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]

/-- The posterior score of a pushforward is the fibre sum of posterior scores.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postScore_pushforward [DecidableEq T] (μ : W → ℝ) (k : Experiment W S) (f : S → T)
    {n : ℕ} (u : Fin (n + 1) → W → ℝ) (t : T) (a : Fin (n + 1)) :
    postScore μ (pushforward k f) u t a
      = ∑ s ∈ univ.filter (fun s => f s = t), postScore μ k u s a := by
  simp only [postScore, pushforward_k, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **A garbling cannot raise the Bayes value** (the easy direction of Blackwell's theorem):
`BlackwellLE k₂ k₁ → bayesValue μ k₂ u ≤ bayesValue μ k₁ u`. Proof: a rule `δ₂` for `k₂` has
value `∑ s, ∑ t, g s t · postScore₁ s (δ₂ t)`, a `g`-mixture of posterior scores of `k₁` at each
`s`, hence at most `∑ s, max_a postScore₁ s a = bayesValue μ k₁ u`. No hypothesis on `μ` is
needed (only the rows of `g` being distributions). Shared with `tt-finite-frames`.
Source: [[generalization-final]] P3(a) l. 113 ("Blackwell: a garbling cannot raise the value
of information"); none: infrastructure (Blackwell 1953, easy direction)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bayesValue_le_of_blackwellLE [DecidableEq S] [DecidableEq T] (μ : W → ℝ)
    {k₁ : Experiment W S} {k₂ : Experiment W T} (h : BlackwellLE k₂ k₁) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) : bayesValue μ k₂ u ≤ bayesValue μ k₁ u := by
  obtain ⟨g, hg, hgarb⟩ := h
  have hgarb' : ∀ w t, k₂.k w t = ∑ s, k₁.k w s * g s t := hgarb
  rw [bayesValue_eq_sum_sup' μ k₁ u]
  unfold bayesValue
  rw [Finset.sup'_le_iff]
  intro δ₂ _
  rw [rule_value_eq_sum_postScore]
  have hps : ∀ t a, postScore μ k₂ u t a = ∑ s, g s t * postScore μ k₁ u s a := by
    intro t a
    unfold postScore
    simp_rw [hgarb', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  calc ∑ t, postScore μ k₂ u t (δ₂ t)
      = ∑ t, ∑ s, g s t * postScore μ k₁ u s (δ₂ t) :=
        Finset.sum_congr rfl fun t _ => hps t (δ₂ t)
    _ ≤ ∑ t, ∑ s, g s t * (univ : Finset (Fin (n + 1))).sup' univ_nonempty
          (fun a => postScore μ k₁ u s a) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (Finset.le_sup' _ (mem_univ _)) ((hg s).1 t)
    _ = ∑ s, (∑ t, g s t) * (univ : Finset (Fin (n + 1))).sup' univ_nonempty
          (fun a => postScore μ k₁ u s a) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = ∑ s, (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => postScore μ k₁ u s a) :=
        Finset.sum_congr rfl fun s _ => by rw [(hg s).2, one_mul]

/-- **A garbling cannot raise the value of information.**
Source: [[generalization-final]] P3(a) l. 113
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem voi_le_of_blackwellLE [DecidableEq S] [DecidableEq T] (μ : W → ℝ)
    {k₁ : Experiment W S} {k₂ : Experiment W T} (h : BlackwellLE k₂ k₁) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) : voi μ k₂ u ≤ voi μ k₁ u := by
  unfold voi
  linarith [bayesValue_le_of_blackwellLE μ h u]

/-- Post-processing the signal cannot raise the value of information.
Source: none: infrastructure (Target 4(ii))
Kind: C
Fidelity: exact -/
theorem voi_pushforward_le [DecidableEq S] [DecidableEq T] (μ : W → ℝ) (k : Experiment W S)
    (f : S → T) {n : ℕ} (u : Fin (n + 1) → W → ℝ) : voi μ (pushforward k f) u ≤ voi μ k u :=
  voi_le_of_blackwellLE μ (blackwellLE_pushforward k f) u

/-! ### The value model `ω = Λ × θ` -/

variable {Λ Θ : Type} [Fintype Λ] [Fintype Θ]

/-- The `Λ`-marginal of a prior on `Λ × θ`.
Source: [[generalization-final]] D2 l. 27
Kind: D
Fidelity: exact -/
def muΛ (μ : Λ × Θ → ℝ) (l : Λ) : ℝ := ∑ ϑ, μ (l, ϑ)

/-- The **value profile** `V̄(a, λ) = E_{P(θ|λ)}[V(a, λ, θ)]`, in ratio form
`(∑ ϑ, μ (λ, ϑ) · V a λ ϑ) / μ_Λ(λ)`; junk `0` at a null `λ`, where the product form
`Vbar_mul_muΛ` is the statement of record.
Source: [[generalization-final]] D2 l. 27
Kind: D
Fidelity: exact under `0 < muΛ μ l` -/
def Vbar {α : Type} (μ : Λ × Θ → ℝ) (V : α → Λ → Θ → ℝ) (a : α) (l : Λ) : ℝ :=
  (∑ ϑ, μ (l, ϑ) * V a l ϑ) / muΛ μ l

/-- Product form of the value profile: `V̄(a, λ) · μ_Λ(λ) = ∑ ϑ, μ (λ, ϑ) · V a λ ϑ` for every `λ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Vbar_mul_muΛ {α : Type} {μ : Λ × Θ → ℝ} (hμ : ∀ p, 0 ≤ μ p) (V : α → Λ → Θ → ℝ) (a : α)
    (l : Λ) : Vbar μ V a l * muΛ μ l = ∑ ϑ, μ (l, ϑ) * V a l ϑ := by
  unfold Vbar
  rcases (Finset.sum_nonneg fun ϑ _ => hμ (l, ϑ) : 0 ≤ muΛ μ l).lt_or_eq with h | h
  · exact div_mul_cancel₀ _ h.ne'
  · have h0 : ∀ ϑ, μ (l, ϑ) = 0 :=
      fun ϑ => (Finset.sum_eq_zero_iff_of_nonneg fun ϑ _ => hμ (l, ϑ)).1 h.symm ϑ (mem_univ ϑ)
    have hm : muΛ μ l = 0 := by
      unfold muΛ
      exact h.symm
    rw [hm, mul_zero]
    exact (Finset.sum_eq_zero fun ϑ _ => by rw [h0 ϑ, zero_mul]).symm

/-- The menu induced by a value function: `u a (λ, ϑ) = V a λ ϑ`.
Source: [[generalization-final]] D2 l. 27, D11 l. 47
Kind: D
Fidelity: exact -/
def menu {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) : Fin (n + 1) → Λ × Θ → ℝ := fun a p => V a p.1 p.2

/-- The **Λ-posterior** given `s`: the `Λ`-marginal of the posterior on `Λ × θ`.
Source: [[generalization-final]] P3(a) l. 113 (`P_t(Λ_A | E_a)`)
Kind: D
Fidelity: exact -/
def postΛ (μ : Λ × Θ → ℝ) (k : Experiment (Λ × Θ) S) (s : S) : Λ → ℝ :=
  fun l => ∑ ϑ, post μ k s (l, ϑ)

/-- Product form of the Λ-posterior: `postΛ s λ · P(s) = ∑ ϑ, μ (λ, ϑ) · k (λ, ϑ) s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postΛ_mul_sigMass {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ))
    (k : Experiment (Λ × Θ) S) (s : S) (l : Λ) :
    postΛ μ k s l * sigMass μ k s = ∑ ϑ, μ (l, ϑ) * k.k (l, ϑ) s := by
  unfold postΛ
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ϑ _ => post_mul_sigMass hμ k s (l, ϑ)

/-- **H_val**: the signal is uninformative about `θ` beyond `Λ`, as the kernel identity
`k (λ, ϑ) s = k (λ, ϑ') s` for *every* `ϑ, ϑ'` — including null-mass coordinates, which S3(c)'s
information form `I[θ : S | Λ] = 0` does not see: an experiment that violates the identity only
at a null `ϑ` fails `HVal` while `voi = voiΛ` (`SplitComposed.nullθ_not_hval`,
`nullθ_voi_eq_voiΛ`; audit r2). The information form is implied by this one
(`SplitInfoForm.condMutualInfo_theta_signal_eq_zero_of_hval`, on `Bridge.joint μ k`), not the
definition.
Source: [[generalization-final]] S3(c) l. 68 (`I(θ_{A>t}; E_a | Λ_{A>t}) = 0`)
Kind: D
Fidelity: stronger: the kernel identity on all of `θ`, including null coordinates (audit r2,
adversarial item 5) -/
def HVal (k : Experiment (Λ × Θ) S) : Prop := ∀ l ϑ ϑ' s, k.k (l, ϑ) s = k.k (l, ϑ') s

open scoped Classical in
/-- The finite set of attained Λ-posteriors, as a type: the signal space of the Λ-garbling.
Source: [[generalization-final]] P3(a) l. 113 ("a sufficient statistic for `Λ_A`")
Kind: D
Fidelity: exact -/
abbrev PostT (μ : Λ × Θ → ℝ) (k : Experiment (Λ × Θ) S) : Type :=
  ↥((univ : Finset S).image (postΛ μ k))

open scoped Classical in
/-- The map from signals to their Λ-posterior.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def fΛ (μ : Λ × Θ → ℝ) (k : Experiment (Λ × Θ) S) : S → PostT μ k :=
  fun s => ⟨postΛ μ k s, Finset.mem_image_of_mem _ (mem_univ s)⟩

open scoped Classical in
/-- The **Λ-garbling** of `k`: the experiment that reveals only the Λ-posterior.
Source: [[generalization-final]] P3(a) l. 113 (`E^Λ_a`)
Kind: D
Fidelity: exact -/
def kΛ (μ : Λ × Θ → ℝ) (k : Experiment (Λ × Θ) S) : Experiment (Λ × Θ) (PostT μ k) :=
  pushforward k (fΛ μ k)

open scoped Classical in
/-- The **VOI of the Λ-posterior garbling** (P3(a)'s `VOI^Λ`). This is *not* "the VOI `E_a` would
have if it were informative about `Λ` only" (S3's gloss): whenever the signals' Λ-posteriors are
distinct the garbling is a relabelling and `voiΛ = voi`, whatever the signal says about `θ`
(`valuePart_not_bounded_by_lambdaTV`, findings F12). P3(a)'s bound `VOI^Λ ≤ M·E[TV_Λ]` is false for
this object; it holds under `HVal` (`voi_le_mul_sum_tvΛ_of_hval`).
Source: [[generalization-final]] S3 l. 65, P3(a) l. 113 (`VOI^Λ_t(a) := VOI_t(E^Λ_a; A)`)
Kind: D
Fidelity: variant: P3(a)'s Λ-posterior garbling, which is not "informative about `Λ` only" (F12) -/
def voiΛ (μ : Λ × Θ → ℝ) (k : Experiment (Λ × Θ) S) {n : ℕ} (u : Fin (n + 1) → Λ × Θ → ℝ) : ℝ :=
  voi μ (kΛ μ k) u

open scoped Classical in
/-- **The Λ-garbling's VOI is at most the whole VOI**: `voiΛ ≤ voi`, so `voiθ := voi − voiΛ ≥ 0`
for P3(a)'s definition — and only for it: the "informative about `Λ` only" lift is not a garbling
and violates this (`meanField_voi_gt_voi`, findings F12).
Source: [[generalization-final]] S3 l. 65, P3(a) l. 113
Kind: C
Fidelity: variant: P3(a)'s Λ-posterior garbling, which is not "informative about `Λ` only" (F12)
Hyps: (a) none -/
theorem voiΛ_le_voi [DecidableEq S] (μ : Λ × Θ → ℝ) (k : Experiment (Λ × Θ) S) {n : ℕ}
    (u : Fin (n + 1) → Λ × Θ → ℝ) : voiΛ μ k u ≤ voi μ k u :=
  voi_pushforward_le μ k (fΛ μ k) u

/-! ### Under H_val the whole VOI is the value part -/

/-- The profile score `G ρ a := ∑ λ, ρ λ · V̄(a, λ)` of a Λ-distribution.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def G {n : ℕ} (μ : Λ × Θ → ℝ) (V : Fin (n + 1) → Λ → Θ → ℝ) (ρ : Λ → ℝ) (a : Fin (n + 1)) : ℝ :=
  ∑ l, ρ l * Vbar μ V a l

/-- **Under H_val the posterior score factors through the Λ-posterior**:
`postScore s a = P(s) · G (postΛ s) a`, for every signal (junk-safe).
Source: [[generalization-final]] P3(a) l. 113, S3(c) l. 68
Kind: P
Fidelity: exact -/
theorem postScore_eq_sigMass_mul_G {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ))
    {k : Experiment (Λ × Θ) S} (hk : HVal k) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) (s : S)
    (a : Fin (n + 1)) :
    postScore μ k (menu V) s a = sigMass μ k s * G μ V (postΛ μ k s) a := by
  have hne : Nonempty (Λ × Θ) := by
    have : (univ : Finset (Λ × Θ)).Nonempty :=
      Finset.nonempty_of_sum_ne_zero (by rw [hμ.2]; exact one_ne_zero)
    exact Finset.univ_nonempty_iff.1 this
  obtain ⟨⟨_, ϑ₀⟩⟩ := hne
  have hκ : ∀ l ϑ, k.k (l, ϑ) s = k.k (l, ϑ₀) s := fun l ϑ => hk l ϑ ϑ₀ s
  unfold G
  rw [Finset.mul_sum]
  calc postScore μ k (menu V) s a
      = ∑ l, ∑ ϑ, μ (l, ϑ) * k.k (l, ϑ) s * V a l ϑ := by
        unfold postScore menu
        rw [Fintype.sum_prod_type]
    _ = ∑ l, k.k (l, ϑ₀) s * ∑ ϑ, μ (l, ϑ) * V a l ϑ := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ϑ _ => by rw [hκ l ϑ]; ring
    _ = ∑ l, k.k (l, ϑ₀) s * (Vbar μ V a l * muΛ μ l) := by
        simp_rw [Vbar_mul_muΛ hμ.1 V a]
    _ = ∑ l, (postΛ μ k s l * sigMass μ k s) * Vbar μ V a l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [postΛ_mul_sigMass hμ k s l]
        unfold muΛ
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ϑ _ => ?_
        rw [hκ l ϑ]
        ring
    _ = ∑ l, sigMass μ k s * (postΛ μ k s l * Vbar μ V a l) :=
        Finset.sum_congr rfl fun l _ => by ring

open scoped Classical in
/-- **Under H_val the Bayes value of the Λ-garbling equals that of the experiment.**
Source: [[generalization-final]] S3(c) l. 68 ("J3 follows from value coverage alone only under
H_val")
Kind: P
Fidelity: exact
Hyps: (a) all — `hμ` simplex, `hk : HVal k` (the claim's own antecedent) -/
theorem bayesValue_kΛ_eq_of_hval [DecidableEq S] {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ))
    {k : Experiment (Λ × Θ) S} (hk : HVal k) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) :
    bayesValue μ (kΛ μ k) (menu V) = bayesValue μ k (menu V) := by
  rw [bayesValue_eq_sum_sup', bayesValue_eq_sum_sup']
  -- each side is `∑ P · Gmax (postΛ)`, grouped by fibres on the left
  have hk' : ∀ s, (univ : Finset (Fin (n + 1))).sup' univ_nonempty
      (fun a => postScore μ k (menu V) s a)
      = sigMass μ k s * (univ : Finset (Fin (n + 1))).sup' univ_nonempty
          (fun a => G μ V (postΛ μ k s) a) := by
    intro s
    simp_rw [postScore_eq_sigMass_mul_G hμ hk V s]
    exact sup'_mul_left_nonneg univ_nonempty _ (sigMass_nonneg hμ k s)
  have hkΛ : ∀ t : PostT μ k, (univ : Finset (Fin (n + 1))).sup' univ_nonempty
      (fun a => postScore μ (kΛ μ k) (menu V) t a)
      = ∑ s ∈ univ.filter (fun s => fΛ μ k s = t), sigMass μ k s
          * (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => G μ V t.1 a) := by
    intro t
    have hfib : ∀ s ∈ univ.filter (fun s => fΛ μ k s = t), postΛ μ k s = t.1 := by
      intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      rw [← hs]
      rfl
    have : ∀ a, postScore μ (kΛ μ k) (menu V) t a
        = (∑ s ∈ univ.filter (fun s => fΛ μ k s = t), sigMass μ k s) * G μ V t.1 a := by
      intro a
      unfold kΛ
      rw [postScore_pushforward, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [postScore_eq_sigMass_mul_G hμ hk V s, hfib s hs]
    simp_rw [this]
    rw [sup'_mul_left_nonneg univ_nonempty _
      (Finset.sum_nonneg fun s _ => sigMass_nonneg hμ k s), Finset.sum_mul]
  simp_rw [hkΛ, hk']
  conv_rhs => rw [← Finset.sum_fiberwise univ (fΛ μ k)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s hs => ?_
  simp only [mem_filter, mem_univ, true_and] at hs
  rw [← hs]
  rfl

open scoped Classical in
/-- **Under H_val the VOI is the VOI of its Λ-garbling**: `voi = voiΛ` — S3(c)'s "J3 follows from
coverage only under H_val" made exact. Under `HVal` the two readings of "value part" coincide and
the split is trivial (`voiθ = 0`); see `voi_eq_voi_margΛ_of_hval` for the Λ-marginal form.
Source: [[generalization-final]] S3(c) l. 68, P3(a) l. 113; [[generalization-adversary]] A3.1 l. 41
Kind: P
Fidelity: variant: P3(a)'s Λ-posterior garbling, which is not "informative about `Λ` only" (F12);
the equality itself is S3(c) exactly
Hyps: (a) all — `hμ` simplex, `hk : HVal k` -/
theorem voi_eq_voiΛ_of_hval [DecidableEq S] {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ))
    {k : Experiment (Λ × Θ) S} (hk : HVal k) {n : ℕ} (V : Fin (n + 1) → Λ → Θ → ℝ) :
    voi μ k (menu V) = voiΛ μ k (menu V) := by
  unfold voiΛ voi
  rw [bayesValue_kΛ_eq_of_hval hμ hk V]

end

end Cleanroom.Info.InfoVoiLatents.Split
