import Cleanroom.Found.LitDdbFrames.Basic
import Cleanroom.Found.LitDdbFrames.Blackwell
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Blackwell's theorem over the dependency's definitions

Package `tt-finite-frames`, Targets B1–B4 (B3 is load-bearing 3).

* **B1** garbling never adds value: `BlackwellLE k₂ k₁ → MoreValuable k₁ k₂`. Per signal `s`,
  a decision rule on the garbled signals earns `∑_t g s t · A s (δ t) ≤ max_j A s j` because
  `g s` is a distribution; the argmax rule on the original signals earns the maximum.
* **B2** a non-garbling is beaten by some prior and menu: the set of garblings of `k₁` is the
  image of a product of simplices under a linear map — compact, convex, closed — so a kernel
  outside it is separated by a functional `φ`; the uniform prior and the menu read off `φ`'s
  coefficients make `k₂` strictly more valuable. The prior is *constructed* (uniform, full
  support), as the mandate's risk note requires.
* **B3** Blackwell's theorem: `MoreValuable k₁ k₂ ↔ BlackwellLE k₂ k₁`, and the strict form.
* **B4** for deterministic experiments, garbling is refinement of maps.

`BlackwellLE k₂ k₁` has the *less* informative experiment first (the dependency's convention).
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell

noncomputable section

set_option linter.unusedSectionVars false

variable {W S T : Type} [Fintype W] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-! ## Decision rules and their value -/

/-- The expected utility of a decision rule `δ : S → Fin (n+1)` for prior `μ`, experiment `k` and
menu `u`: `∑ w, μ w · ∑ s, k w s · u (δ s) w`. `bayesValue` is its maximum over rules.
Source: none: infrastructure (Blackwell 1953)
Kind: D
Fidelity: exact -/
def ruleValue (μ : W → ℝ) (k : Experiment W S) {n : ℕ} (u : Fin (n + 1) → W → ℝ)
    (δ : S → Fin (n + 1)) : ℝ :=
  ∑ w, μ w * ∑ s, k.k w s * u (δ s) w

/-- Every rule is worth at most the Bayes value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ruleValue_le_bayesValue (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) (δ : S → Fin (n + 1)) : ruleValue μ k u δ ≤ bayesValue μ k u :=
  (le_sup'_iff _).2 ⟨δ, mem_univ δ, le_rfl⟩

/-- The Bayes value is bounded by any bound on all rules.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bayesValue_le (μ : W → ℝ) (k : Experiment W S) {n : ℕ} (u : Fin (n + 1) → W → ℝ)
    {a : ℝ} (h : ∀ δ, ruleValue μ k u δ ≤ a) : bayesValue μ k u ≤ a :=
  sup'_le _ _ fun δ _ => h δ

/-- The value of a rule, summed signal-first: `∑ s, ∑ w, μ w · k w s · u (δ s) w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ruleValue_eq_sum_signals (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) (δ : S → Fin (n + 1)) :
    ruleValue μ k u δ = ∑ s, ∑ w, μ w * k.k w s * u (δ s) w := by
  unfold ruleValue
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro s _; apply sum_congr rfl; intro w _; ring

/-- Commuting three finite sums: `∑ w ∑ t ∑ s = ∑ s ∑ t ∑ w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_comm₃ (P : W → S → T → ℝ) :
    ∑ w, ∑ t, ∑ s, P w s t = ∑ s, ∑ t, ∑ w, P w s t := by
  calc ∑ w, ∑ t, ∑ s, P w s t = ∑ w, ∑ s, ∑ t, P w s t := sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ s, ∑ w, ∑ t, P w s t := sum_comm
    _ = ∑ s, ∑ t, ∑ w, P w s t := sum_congr rfl (fun _ _ => sum_comm)

/-- The value of a rule on a garbled experiment, as a `g`-mixture of signalwise payoffs of the
original: `∑ s, ∑ t, g s t · (∑ w, μ w · k₁ w s · u (δ t) w)`.
Source: none: infrastructure (B1)
Kind: L
Fidelity: n/a -/
theorem ruleValue_of_isGarbling (μ : W → ℝ) {k₁ : Experiment W S} {k₂ : Experiment W T}
    {g : S → T → ℝ} (hg : IsGarbling k₁ k₂ g) {n : ℕ} (u : Fin (n + 1) → W → ℝ)
    (δ : T → Fin (n + 1)) :
    ruleValue μ k₂ u δ = ∑ s, ∑ t, g s t * ∑ w, μ w * k₁.k w s * u (δ t) w := by
  have hg' : ∀ w t, k₂.k w t = ∑ s, k₁.k w s * g s t := hg
  have e1 : ruleValue μ k₂ u δ = ∑ w, ∑ t, ∑ s, μ w * (k₁.k w s * g s t * u (δ t) w) := by
    unfold ruleValue
    simp only [hg', sum_mul, mul_sum]
  have e2 := sum_comm₃ (fun w s t => μ w * (k₁.k w s * g s t * u (δ t) w))
  rw [e1, e2]
  simp only [mul_sum]
  apply sum_congr rfl; intro s _; apply sum_congr rfl; intro t _; apply sum_congr rfl; intro w _
  ring

/-! ## B1: garbling never adds value -/

/-- **B1. Garbling never adds value.** If `k₂` is a garbling of `k₁` then `k₁` is more valuable:
for every prior and menu, `bayesValue μ k₂ u ≤ bayesValue μ k₁ u`.
Source: fixpoint-lit-025 (i) (Blackwell 1953, kernel form); corr-wf13-010 (monotonicity)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem moreValuable_of_blackwellLE {k₁ : Experiment W S} {k₂ : Experiment W T}
    (h : BlackwellLE k₂ k₁) : MoreValuable k₁ k₂ := by
  obtain ⟨g, hg, hgar⟩ := h
  intro μ _ n u
  apply bayesValue_le
  intro δ
  set A : S → Fin (n + 1) → ℝ := fun s j => ∑ w, μ w * k₁.k w s * u j w with hA
  have hex : ∀ s, ∃ j, ∀ j', A s j' ≤ A s j := fun s => by
    obtain ⟨j, _, hj⟩ := exists_max_image univ (A s) univ_nonempty
    exact ⟨j, fun j' => hj j' (mem_univ _)⟩
  choose ρ hρ using hex
  calc ruleValue μ k₂ u δ = ∑ s, ∑ t, g s t * A s (δ t) := ruleValue_of_isGarbling μ hgar u δ
    _ ≤ ∑ s, ∑ t, g s t * A s (ρ s) := by
        apply sum_le_sum; intro s _; apply sum_le_sum; intro t _
        exact mul_le_mul_of_nonneg_left (hρ s (δ t)) ((hg s).1 t)
    _ = ∑ s, A s (ρ s) := by
        apply sum_congr rfl; intro s _
        rw [← sum_mul, (hg s).2, one_mul]
    _ = ruleValue μ k₁ u ρ := (ruleValue_eq_sum_signals μ k₁ u ρ).symm
    _ ≤ bayesValue μ k₁ u := ruleValue_le_bayesValue μ k₁ u ρ

/-! ## B2: a non-garbling is beaten by some prior and menu -/

/-- The garbling map `g ↦ k₁ ∘ g` as a linear map `(S → T → ℝ) →ₗ (W → T → ℝ)`.
Source: none: infrastructure (B2)
Kind: D
Fidelity: n/a -/
def garbleMap (k₁ : Experiment W S) : (S → T → ℝ) →ₗ[ℝ] (W → T → ℝ) where
  toFun g := fun w t => ∑ s, k₁.k w s * g s t
  map_add' g₁ g₂ := by
    funext w t
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c g := by
    funext w t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    apply sum_congr rfl; intro s _; ring

/-- The basis vector `δ_w ⊗ δ_t` of `W → T → ℝ`.
Source: none: infrastructure (B2)
Kind: D
Fidelity: n/a -/
def basis [DecidableEq W] (w : W) (t : T) : W → T → ℝ :=
  fun w' t' => if w' = w then (if t' = t then 1 else 0) else 0

/-- Every `M : W → T → ℝ` is the combination `∑ w t, M w t • basis w t`.
Source: none: infrastructure (B2)
Kind: L
Fidelity: n/a -/
theorem eq_sum_basis [DecidableEq W] (M : W → T → ℝ) :
    M = ∑ w, ∑ t, M w t • basis w t := by
  funext w' t'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basis]
  simp [mul_ite]

/-- A continuous linear functional on `W → T → ℝ` is `M ↦ ∑ w t, M w t · c w t` for the
coefficients `c w t = f(δ_w ⊗ δ_t)`.
Source: none: infrastructure (B2; the two-index form of the dependency's `StrongDual.apply_eq_E`)
Kind: L
Fidelity: n/a -/
theorem StrongDual.apply_eq_sum [DecidableEq W] (f : StrongDual ℝ (W → T → ℝ)) (M : W → T → ℝ) :
    f M = ∑ w, ∑ t, M w t * f (basis w t) := by
  conv_lhs => rw [eq_sum_basis M]
  simp [map_sum, map_smul, smul_eq_mul]

/-- **B2. A non-garbling is beaten by some prior and menu.** If `k₂` is not a garbling of `k₁`
then there is a full-support prior (uniform) and a finite menu on which `k₂` has strictly larger
Bayes value. Hahn–Banach separates `k₂` from the compact convex set of garblings of `k₁`; the
separating functional's coefficients are the menu.
Source: fixpoint-lit-025 (ii) (Blackwell 1953, kernel form)
Kind: P
Fidelity: exact (`[Nonempty W]` is needed: on an empty `W` every experiment is a garbling of
every other, so the hypothesis is never met)
Hyps: (a) none -/
theorem exists_prior_menu_of_not_blackwellLE [DecidableEq W] [Nonempty W] {k₁ : Experiment W S}
    {k₂ : Experiment W T} (h : ¬ BlackwellLE k₂ k₁) :
    ∃ μ : W → ℝ, μ ∈ stdSimplex ℝ W ∧ (∀ w, 0 < μ w) ∧
      ∃ (n : ℕ) (u : Fin (n + 1) → W → ℝ), bayesValue μ k₁ u < bayesValue μ k₂ u := by
  classical
  -- `T` is nonempty since rows of `k₂` are distributions
  have hT : Nonempty T := by
    obtain ⟨w⟩ := ‹Nonempty W›
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := (k₂.k_mem w).2
    rw [univ_eq_empty, sum_empty] at this
    exact zero_ne_one this
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card T = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : T ≃ Fin (n + 1) := (Fintype.equivFin T).trans (finCongr hn)
  -- the set of garblings of `k₁`
  set G : Set (W → T → ℝ) := garbleMap k₁ '' (Set.pi Set.univ fun _ : S => stdSimplex ℝ T)
    with hG
  have hGconv : Convex ℝ G :=
    (convex_pi fun _ _ => convex_stdSimplex ℝ T).linear_image (garbleMap k₁)
  have hGcl : IsClosed G :=
    ((isCompact_univ_pi fun _ => isCompact_stdSimplex ℝ T).image
      (garbleMap k₁).continuous_of_finiteDimensional).isClosed
  have hk₂ : k₂.k ∉ G := by
    rintro ⟨g, hg, hgk⟩
    apply h
    refine ⟨g, fun s => hg s (Set.mem_univ _), fun w t => ?_⟩
    have := congrFun (congrFun hgk w) t
    exact this.symm
  obtain ⟨f, u₀, hfx, hfG⟩ := geometric_hahn_banach_point_closed hGconv hGcl hk₂
  -- coefficients of the separating functional
  set c : W → T → ℝ := fun w t => f (basis w t) with hc
  have hrep : ∀ M : W → T → ℝ, f M = ∑ w, ∑ t, M w t * c w t := fun M =>
    StrongDual.apply_eq_sum f M
  -- the prior (uniform) and the menu
  have hNpos : (0 : ℝ) < Fintype.card W := Nat.cast_pos.2 Fintype.card_pos
  set μ : W → ℝ := fun _ => 1 / (Fintype.card W : ℝ) with hμ
  have hμpos : ∀ w, 0 < μ w := fun _ => one_div_pos.2 hNpos
  have hμs : μ ∈ stdSimplex ℝ W := by
    refine ⟨fun w => (hμpos w).le, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hNpos.ne']
  set u : Fin (n + 1) → W → ℝ := fun j w => -((Fintype.card W : ℝ) * c w (e.symm j)) with hu
  -- the value of any rule for either experiment, in terms of `c`
  have hrule : ∀ {S' : Type} [Fintype S'] [DecidableEq S'] (k : Experiment W S')
      (δ : S' → Fin (n + 1)),
      ruleValue μ k u δ = -∑ w, ∑ s, k.k w s * c w (e.symm (δ s)) := by
    intro S' _ _ k δ
    unfold ruleValue
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro w _
    rw [mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl; intro s _
    simp only [hμ, hu]
    field_simp
  refine ⟨μ, hμs, hμpos, n, u, ?_⟩
  -- (i) `k₂` with the identity rule earns `−f k₂`
  have h₂ : -f k₂.k ≤ bayesValue μ k₂ u := by
    have := ruleValue_le_bayesValue μ k₂ u (fun t => e t)
    rw [hrule k₂ (fun t => e t)] at this
    simp only [Equiv.symm_apply_apply] at this
    rw [hrep k₂.k]
    exact this
  -- (ii) every rule for `k₁` is a garbling, so earns `−f b < −u₀`
  have h₁ : bayesValue μ k₁ u ≤ -u₀ := by
    apply bayesValue_le
    intro ρ
    set g : S → T → ℝ := fun s t => if t = e.symm (ρ s) then 1 else 0 with hg
    have hgs : g ∈ Set.pi Set.univ fun _ : S => stdSimplex ℝ T := by
      intro s _
      refine ⟨fun t => by simp only [hg]; split_ifs <;> norm_num, ?_⟩
      simp [hg]
    have hmem : garbleMap k₁ g ∈ G := ⟨g, hgs, rfl⟩
    have hlt := hfG _ hmem
    have hval : f (garbleMap k₁ g) = ∑ w, ∑ s, k₁.k w s * c w (e.symm (ρ s)) := by
      rw [hrep]
      apply sum_congr rfl; intro w _
      simp only [garbleMap, LinearMap.coe_mk, AddHom.coe_mk, hg, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl; intro s _
      simp [mul_ite]
    rw [hrule k₁ ρ, ← hval]
    linarith
  linarith

/-! ## B3: Blackwell's theorem -/

/-- **B3 (load-bearing 3). Blackwell's theorem.** `k₁` is more valuable than `k₂` — for every
prior in the simplex and every finite menu — iff `k₂` is a garbling of `k₁`.
Source: fixpoint-lit-025 (Blackwell 1953); [[Deference and Infinite Frames]] §2 l. 112
Kind: C (B1 and B2)
Fidelity: exact
Hyps: (a) none (`[Nonempty W]` for the converse; see B2) -/
theorem blackwell_iff [DecidableEq W] [Nonempty W] (k₁ : Experiment W S) (k₂ : Experiment W T) :
    MoreValuable k₁ k₂ ↔ BlackwellLE k₂ k₁ := by
  constructor
  · intro h
    by_contra hnot
    obtain ⟨μ, hμ, _, n, u, hlt⟩ := exists_prior_menu_of_not_blackwellLE hnot
    exact absurd (h μ hμ n u) (not_le.2 hlt)
  · exact moreValuable_of_blackwellLE

/-- **B3, strict form.** Strictly more informative is strictly more valuable for some prior and
menu (and never less valuable).
Source: fixpoint-lit-025 (Blackwell 1953)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem exists_strict_of_blackwellLT [DecidableEq W] [Nonempty W] {k₁ : Experiment W S}
    {k₂ : Experiment W T} (h : BlackwellLT k₂ k₁) :
    MoreValuable k₁ k₂ ∧ ∃ μ : W → ℝ, μ ∈ stdSimplex ℝ W ∧
      ∃ (n : ℕ) (u : Fin (n + 1) → W → ℝ), bayesValue μ k₂ u < bayesValue μ k₁ u := by
  refine ⟨moreValuable_of_blackwellLE h.1, ?_⟩
  obtain ⟨μ, hμ, _, n, u, hlt⟩ := exists_prior_menu_of_not_blackwellLE h.2
  exact ⟨μ, hμ, n, u, hlt⟩

/-! ## B4: deterministic experiments -/

/-- **B4. For deterministic experiments, garbling is refinement.** `ofMap f₂` is a garbling of
`ofMap f₁` iff `f₂` factors through `f₁`. (⇒) row `w` of the garbling identity says
`𝟙[f₂ w = t] = g (f₁ w) t`, so `g (f₁ w)` is the point mass at `f₂ w`, which determines `f₂ w`
from `f₁ w`. (⇐) is the dependency's `Refines.blackwellLE`.
Source: fixpoint-lit-025; [[Deference and Infinite Frames]] §2 l. 114 (refinement as
"more informative")
Kind: P
Fidelity: exact (`[Nonempty T]` for the map off the range of `f₁`)
Hyps: (a) none -/
theorem blackwellLE_ofMap_iff [Nonempty T] (f₁ : W → S) (f₂ : W → T) :
    BlackwellLE (ofMap f₂) (ofMap f₁) ↔ Refines f₁ f₂ := by
  constructor
  · rintro ⟨g, hg, hgar⟩
    classical
    -- `g (f₁ w) t = 𝟙[f₂ w = t]`
    have hrow : ∀ w t, g (f₁ w) t = if f₂ w = t then 1 else 0 := by
      intro w t
      have := hgar w t
      simp only [ofMap, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at this
      exact this.symm
    refine ⟨fun s => if hs : ∃ w, f₁ w = s then f₂ hs.choose else Classical.arbitrary T, ?_⟩
    funext w
    have hs : ∃ v, f₁ v = f₁ w := ⟨w, rfl⟩
    simp only [Function.comp, dif_pos hs]
    -- `g (f₁ w)` is the point mass at both `f₂ w` and `f₂ (choose)`
    have h1 := hrow w (f₂ hs.choose)
    have h2 := hrow hs.choose (f₂ hs.choose)
    rw [hs.choose_spec] at h2
    rw [h2, if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  · exact Refines.blackwellLE

end

end Cleanroom.Trust.TtFiniteFrames
