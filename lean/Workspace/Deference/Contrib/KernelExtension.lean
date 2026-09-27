/-
# The corrigibility kernel — extension: learning realizations

Round `projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/`
(`prompts/2026-09-27-corrigibility-kernel-phase2/PROMPT.md`), ruling R6.  Separate from
the headline and not part of it: the headline's agent is a plain maximizer of the fidelity
score; this file says how much of that preference becomes behaviour for a learner.

**§1 The decision interface** (`DecisionInterface`): per block, the chooser's evaluation
has the stated form (`evalOf`: the estimated residual capped at `D`, less `ϖ` per violation
recognized in advance, less `ϖ` times the priced risk); on a non-exploration step it
chooses a maximizer, so its evaluation is at least inquiry's `c_k`; on an exploration step
the chosen option lies in the permitted exploration set (no recognized violation, priced
risk at most `θ_hi`, estimated residual at least inquiry's); its overestimation on chosen
options is at most `B(K)`; the expected score given the opening is at most `D − ϖ π_k`;
the noise over all blocks is at most `M(K)`.

**§2 The realized violation-rate theorem** (`rate_core`, `realized_rate_mul`, `realized_rate`):
`avg π ≤ avg (D − c_k)/ϖ + ε̄·θ_hi + (B(K) + M(K))/(ϖ Σ w_k)`, with `ε̄` the exploration
mass; exclusion of recognized violations (`maximizer_excludes`) and exploration never
violating (`exploration_never_violates`).

**§3 The Continuation BRIA realization** (`briaInterface`, `bria_rate`): no exploration,
`B(K) = ρ 𝒜_K` from the opening-timing overestimation bound; the landed per-block bound is
recovered.

**§4 The exploration realization over a logical inductor** (`overestimation_of_unbiased`,
`exploration_rate`, `ExplorationIndependent`): `B(K) = γ Σ w_k` from unbiasedness from
feedback on the chosen options (`BRIAFollowup.UnbiasedFromFeedback`, by content; the
pinned declaration is `LogicalInduction.lic_not_frequently_positive_feedback_return`);
exploration randomness the agent can neither predict nor influence, named by content.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Spec.Headline

namespace Workspace.Deference.Contrib.KernelExtension

open Finset
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.BRIAFollowup
open Workspace.Deference.Contrib.BRIAFollowup2
open Workspace.Deference.Contrib.AfterCompromise
open Workspace.Deference.Contrib.CorrigibilityKernel
open Workspace.Deference.ContinuationBRIA

/-! ## 1. The decision interface -/

/-- **The decision interface.**  Per-block data of a chooser over the history at each
opening, with the hypotheses a learning realization must discharge. -/
structure DecisionInterface where
  /-- the ordinary range -/
  D : ℝ
  /-- the authority weight -/
  ϖ : ℝ
  /-- the forecast filter's upper threshold, the exploration set's risk cap -/
  θhi : ℝ
  /-- block weights -/
  w : ℕ → ℝ
  /-- the chosen option's estimated residual (capped at `D`) -/
  bid : ℕ → ℝ
  /-- the chosen option's violations recognized in advance -/
  nKnown : ℕ → ℕ
  /-- the chosen option's priced risk -/
  p : ℕ → ℝ
  /-- inquiry's evaluation at the block -/
  c : ℕ → ℝ
  /-- the realized score of the block -/
  S : ℕ → ℝ
  /-- the expected score given the opening -/
  m : ℕ → ℝ
  /-- the expected number of violations of every class given the opening -/
  π : ℕ → ℝ
  /-- whether the block is an exploration step -/
  expl : ℕ → Bool
  /-- the overestimation bound on chosen options -/
  B : ℕ → ℝ
  /-- the noise bound over all blocks -/
  M : ℕ → ℝ
  ϖ_pos : 0 < ϖ
  w_pos : ∀ k, 0 < w k
  bid_le : ∀ k, bid k ≤ D
  p_nonneg : ∀ k, 0 ≤ p k
  /-- (2) on a non-exploration step a maximizer is chosen, with inquiry on the menu -/
  maximizer : ∀ k, expl k = false → c k ≤ bid k - ϖ * nKnown k - ϖ * p k
  /-- (3) an exploration step lies in the permitted exploration set -/
  explore_permitted : ∀ k, expl k = true → nKnown k = 0 ∧ p k ≤ θhi ∧ c k ≤ bid k
  /-- (4) the overestimation on chosen options -/
  overestimation : ∀ K, ∑ k ∈ range K, w k * ((bid k - ϖ * nKnown k - ϖ * p k) - S k) ≤ B K
  /-- the conditional-expectation bound -/
  cond_exp : ∀ k, m k ≤ D - ϖ * π k
  /-- the noise hypothesis over all blocks -/
  noise : ∀ K, |∑ k ∈ range K, w k * (S k - m k)| ≤ M K

namespace DecisionInterface

variable (𝓘 : DecisionInterface)

/-- (1) The chooser's evaluation of the chosen option has the stated form. -/
noncomputable def eval (k : ℕ) : ℝ := 𝓘.bid k - 𝓘.ϖ * 𝓘.nKnown k - 𝓘.ϖ * 𝓘.p k

/-- The exploration mass through `K`. -/
noncomputable def explMass (K : ℕ) : ℝ :=
  ∑ k ∈ (range K).filter (fun k => 𝓘.expl k = true), 𝓘.w k

theorem explMass_eq (K : ℕ) :
    𝓘.explMass K = ∑ k ∈ range K, 𝓘.w k * (if 𝓘.expl k = true then 1 else 0) := by
  unfold explMass
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- **Exploration never violates**: a chosen exploration option carries no recognized
violation and a priced risk at most the cap. -/
theorem exploration_never_violates (k : ℕ) (h : 𝓘.expl k = true) :
    𝓘.nKnown k = 0 ∧ 𝓘.p k ≤ 𝓘.θhi :=
  ⟨(𝓘.explore_permitted k h).1, (𝓘.explore_permitted k h).2.1⟩

/-- **The maximizer excludes recognized violations** whenever inquiry's evaluation is at
least the window and `D − ϖ < w`. -/
theorem maximizer_excludes (w : ℝ) (hwin : 𝓘.D - 𝓘.ϖ < w) (k : ℕ) (h : 𝓘.expl k = false)
    (hc : w ≤ 𝓘.c k) : 𝓘.nKnown k = 0 := by
  by_contra hne
  have hn : (1 : ℝ) ≤ 𝓘.nKnown k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have h1 := 𝓘.maximizer k h
  have h2 := 𝓘.bid_le k
  have h3 := mul_nonneg 𝓘.ϖ_pos.le (𝓘.p_nonneg k)
  have h4 : 𝓘.ϖ * 1 ≤ 𝓘.ϖ * 𝓘.nKnown k := mul_le_mul_of_nonneg_left hn 𝓘.ϖ_pos.le
  linarith

/-- Per block: `ϖ π_k ≤ (D − c_k) + ϖ θ_hi·[exploration] + (eval_k − S_k) + (S_k − m_k)`. -/
theorem block_bound (k : ℕ) :
    𝓘.ϖ * 𝓘.π k ≤ (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * (if 𝓘.expl k = true then 1 else 0)
      + (𝓘.eval k - 𝓘.S k) + (𝓘.S k - 𝓘.m k) := by
  have hm := 𝓘.cond_exp k
  unfold eval
  by_cases h : 𝓘.expl k = true
  · obtain ⟨hn, hp, hc⟩ := 𝓘.explore_permitted k h
    rw [if_pos h, hn]
    simp only [Nat.cast_zero, mul_zero, sub_zero, mul_one]
    have := mul_le_mul_of_nonneg_left hp 𝓘.ϖ_pos.le
    linarith
  · have h' : 𝓘.expl k = false := by simpa using h
    have := 𝓘.maximizer k h'
    rw [if_neg h]
    simp only [mul_zero]
    linarith

/-- **The rate bound with an explicit overestimation term**: for any `Bbound` bounding the
weighted overestimation on the chosen options through `K`,
`ϖ Σ w_k π_k ≤ Σ w_k (D − c_k) + ϖ θ_hi · (exploration mass) + Bbound + M(K)`. -/
theorem rate_core (K : ℕ) (Bbound : ℝ)
    (hB : ∑ k ∈ range K, 𝓘.w k * (𝓘.eval k - 𝓘.S k) ≤ Bbound) :
    𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k * 𝓘.π k
      ≤ ∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * 𝓘.explMass K + Bbound + 𝓘.M K := by
  have hpt : ∀ k ∈ range K, 𝓘.w k * (𝓘.ϖ * 𝓘.π k) ≤
      𝓘.w k * (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * (𝓘.w k * (if 𝓘.expl k = true then 1 else 0))
        + 𝓘.w k * (𝓘.eval k - 𝓘.S k) + 𝓘.w k * (𝓘.S k - 𝓘.m k) := by
    intro k _
    have := mul_le_mul_of_nonneg_left (𝓘.block_bound k) (𝓘.w_pos k).le
    linarith [this]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hM := (abs_le.mp (𝓘.noise K)).2
  have eA : ∑ k ∈ range K, 𝓘.w k * (𝓘.ϖ * 𝓘.π k) = 𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k * 𝓘.π k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have eB : ∑ k ∈ range K, 𝓘.ϖ * 𝓘.θhi * (𝓘.w k * (if 𝓘.expl k = true then 1 else 0))
      = 𝓘.ϖ * 𝓘.θhi * 𝓘.explMass K := by
    rw [𝓘.explMass_eq, Finset.mul_sum]
  linarith

/-- **The realized violation-rate theorem, multiplied form.** -/
theorem realized_rate_mul (K : ℕ) :
    𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k * 𝓘.π k
      ≤ ∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * 𝓘.explMass K + 𝓘.B K + 𝓘.M K :=
  𝓘.rate_core K (𝓘.B K) (𝓘.overestimation K)

/-- The averaged form of a multiplied bound. -/
theorem average_of_mul (K : ℕ) (hK : 0 < ∑ k ∈ range K, 𝓘.w k) (Bbound : ℝ)
    (h : 𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k * 𝓘.π k
      ≤ ∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * 𝓘.explMass K + Bbound + 𝓘.M K) :
    (∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k)
      ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
        + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * 𝓘.θhi
        + (Bbound + 𝓘.M K) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k) := by
  have hϖ := 𝓘.ϖ_pos
  rw [div_le_iff₀ hK]
  have key : (∑ k ∈ range K, 𝓘.w k * 𝓘.π k)
      ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * 𝓘.explMass K + Bbound + 𝓘.M K) / 𝓘.ϖ := by
    rw [le_div_iff₀ hϖ]; linarith
  calc (∑ k ∈ range K, 𝓘.w k * 𝓘.π k)
      ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k) + 𝓘.ϖ * 𝓘.θhi * 𝓘.explMass K + Bbound + 𝓘.M K) / 𝓘.ϖ := key
    _ = ((∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
        + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * 𝓘.θhi
        + (Bbound + 𝓘.M K) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)) * ∑ k ∈ range K, 𝓘.w k := by
        field_simp
        try ring

/-- **The realized violation-rate theorem.**  The weighted average expected violation count
per block is at most the average exchange rate, plus the exploration mass times the risk
cap, plus the overestimation and noise bounds over `ϖ` times the total weight. -/
theorem realized_rate (K : ℕ) (hK : 0 < ∑ k ∈ range K, 𝓘.w k) :
    (∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k)
      ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
        + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * 𝓘.θhi
        + (𝓘.B K + 𝓘.M K) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k) :=
  𝓘.average_of_mul K hK (𝓘.B K) (𝓘.realized_rate_mul K)

end DecisionInterface

/-! ## 3. The Continuation BRIA realization -/

section BRIA

/-- **Continuation BRIA realizes the interface with no exploration.**  Given the landed
hypotheses of the per-block exchange-rate theorem — the auction feasible under opening
timing, the winner's overestimation the evaluation less the realized score over the
range `ρ`, inquiry on the menu, the conditional-expectation bound and the noise
hypothesis — the interface's overestimation bound is `ρ 𝒜_K`. -/
noncomputable def briaInterface (D ϖ θhi : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n)
    (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (bid : ℕ → ℝ) (hb : ∀ k, bid k ≤ D)
    (nKnown : ℕ → ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (c S m π : ℕ → ℝ)
    (hwin : ∀ k, c k ≤ bid k - ϖ * nKnown k - ϖ * p k)
    (hcons : ∀ k, a.b k - a.G k = ((bid k - ϖ * nKnown k - ϖ * p k) - S k) / ρ)
    (hm : ∀ k, m k ≤ D - ϖ * π k) (M : ℕ → ℝ)
    (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) : DecisionInterface where
  D := D
  ϖ := ϖ
  θhi := θhi
  w := a.w
  bid := bid
  nKnown := nKnown
  p := p
  c := c
  S := S
  m := m
  π := π
  expl := fun _ => false
  B := fun K => ρ * a.totalAllowance K
  M := M
  ϖ_pos := hϖ
  w_pos := a.w_pos
  bid_le := hb
  p_nonneg := hp
  maximizer := fun k _ => hwin k
  explore_permitted := fun k h => by simp at h
  overestimation := fun K => by
    have h1 := a.overestimation_le_allowance_opening hf K
    have h2 : ∑ k ∈ range K, a.w k * ((bid k - ϖ * nKnown k - ϖ * p k) - S k)
        = ρ * ∑ k ∈ range K, a.w k * (a.b k - a.G k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcons k]
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hρ.le
  cond_exp := hm
  noise := hN

/-- The BRIA realization has no exploration mass. -/
theorem briaInterface_explMass (D ϖ θhi : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n)
    (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (bid : ℕ → ℝ) (hb : ∀ k, bid k ≤ D)
    (nKnown : ℕ → ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (c S m π : ℕ → ℝ)
    (hwin : ∀ k, c k ≤ bid k - ϖ * nKnown k - ϖ * p k)
    (hcons : ∀ k, a.b k - a.G k = ((bid k - ϖ * nKnown k - ϖ * p k) - S k) / ρ)
    (hm : ∀ k, m k ≤ D - ϖ * π k) (M : ℕ → ℝ)
    (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ) :
    (briaInterface D ϖ θhi hϖ a hf ρ hρ bid hb nKnown p hp c S m π hwin hcons hm M hN).explMass K
      = 0 := by
  unfold DecisionInterface.explMass briaInterface
  simp

/-- **The landed per-block bound, recovered from the interface**: with no exploration and
`B(K) = ρ 𝒜_K`, the interface theorem is the after-compromise round's
`violation_rate_le_exchange_perblock`. -/
theorem bria_rate (D ϖ θhi : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n)
    (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (bid : ℕ → ℝ) (hb : ∀ k, bid k ≤ D)
    (nKnown : ℕ → ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (c S m π : ℕ → ℝ)
    (hwin : ∀ k, c k ≤ bid k - ϖ * nKnown k - ϖ * p k)
    (hcons : ∀ k, a.b k - a.G k = ((bid k - ϖ * nKnown k - ϖ * p k) - S k) / ρ)
    (hm : ∀ k, m k ≤ D - ϖ * π k) (M : ℕ → ℝ)
    (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ)
    (hK : 0 < ∑ k ∈ range K, a.w k) :
    (∑ k ∈ range K, a.w k * π k) / (∑ k ∈ range K, a.w k)
      ≤ (∑ k ∈ range K, a.w k * (D - c k)) / (ϖ * ∑ k ∈ range K, a.w k)
        + (ρ * a.totalAllowance K + M K) / (ϖ * ∑ k ∈ range K, a.w k) := by
  have h := (briaInterface D ϖ θhi hϖ a hf ρ hρ bid hb nKnown p hp c S m π hwin hcons hm M hN).realized_rate
    K hK
  rw [briaInterface_explMass] at h
  simpa [briaInterface] using h

end BRIA

/-! ## 4. The exploration realization over a logical inductor -/

section Exploration

/-- **Unbiasedness from feedback bounds the overestimation.**  On the chosen weighting `w`,
with `bias_k` the chosen option's evaluation less its realized score, unbiasedness from
feedback at `γ` from day `N` gives `Σ_{k<K} w_k · bias_k ≤ γ Σ_{k<K} w_k` for `K ≥ N`. -/
theorem overestimation_of_unbiased (w bias : ℕ → ℝ) (γ : ℝ) (N : ℕ)
    (hU : UnbiasedFromFeedback w bias γ N) (K : ℕ) (hK : N ≤ K) :
    ∑ k ∈ range K, w k * bias k ≤ γ * ∑ k ∈ range K, w k :=
  (abs_le.mp (hU K hK)).2

/-- **Exploration randomness, by content.**  The exploration indicator is fixed at each
block's opening and independent of the block's noise: the weighted signed noise over the
exploration blocks is bounded by `M_e(K)`.  This is the noise hypothesis on the selection
"exploration block", which is what "the agent can neither predict nor influence the draw"
buys — the selection is measurable at the opening.  Named; consumed by nothing in the rate
theorem, which uses the noise over all blocks. -/
def ExplorationIndependent (w S m : ℕ → ℝ) (expl : ℕ → Bool) (Me : ℕ → ℝ) : Prop :=
  ∀ K, |∑ k ∈ (range K).filter (fun k => expl k = true), w k * (S k - m k)| ≤ Me K

/-- **The exploration realization's rate.**  For an interface whose overestimation bound is
supplied by unbiasedness from feedback at `γ` from day `N`:
`avg π ≤ avg (D − c_k)/ϖ + ε̄·θ_hi + γ/ϖ + M(K)/(ϖ Σ w_k)` for `K ≥ N`. -/
theorem exploration_rate (𝓘 : DecisionInterface) (γ : ℝ) (N : ℕ)
    (hU : UnbiasedFromFeedback 𝓘.w (fun k => 𝓘.eval k - 𝓘.S k) γ N) (K : ℕ) (hK : N ≤ K)
    (hw : 0 < ∑ k ∈ range K, 𝓘.w k) :
    (∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k)
      ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
        + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * 𝓘.θhi
        + γ / 𝓘.ϖ + 𝓘.M K / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k) := by
  have hB := overestimation_of_unbiased 𝓘.w (fun k => 𝓘.eval k - 𝓘.S k) γ N hU K hK
  have hcore := 𝓘.rate_core K (γ * ∑ k ∈ range K, 𝓘.w k) hB
  have havg := 𝓘.average_of_mul K hw (γ * ∑ k ∈ range K, 𝓘.w k) hcore
  have hϖ := 𝓘.ϖ_pos
  have hsplit : (γ * ∑ k ∈ range K, 𝓘.w k + 𝓘.M K) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
      = γ / 𝓘.ϖ + 𝓘.M K / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k) := by
    field_simp
    try ring
  linarith [havg, hsplit]

end Exploration

#print axioms DecisionInterface
#print axioms DecisionInterface.eval
#print axioms DecisionInterface.explMass
#print axioms DecisionInterface.explMass_eq
#print axioms DecisionInterface.exploration_never_violates
#print axioms DecisionInterface.maximizer_excludes
#print axioms DecisionInterface.block_bound
#print axioms DecisionInterface.rate_core
#print axioms DecisionInterface.realized_rate_mul
#print axioms DecisionInterface.average_of_mul
#print axioms DecisionInterface.realized_rate
#print axioms briaInterface
#print axioms briaInterface_explMass
#print axioms bria_rate
#print axioms overestimation_of_unbiased
#print axioms ExplorationIndependent
#print axioms exploration_rate

end Workspace.Deference.Contrib.KernelExtension
