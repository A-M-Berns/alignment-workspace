import Cleanroom.Fixpoint.FixOraclesCorresp.Defs
import Mathlib.Data.Fin.VecNotation

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Lifts`: the Dirac and barycentric lifts

Target 2 (fixpoint-lit-002): the Dirac lift `p ↦ {δ_{f p}}` has a convex graph iff `f` is
**constant** on `Δ(X)` — the note says "affine" (finding F1); its own argument proves constant.

Target 3 (fixpoint-lit-003): the barycentric lift `p ↦ {μ ∈ Δ² | bary μ = f p}` has nonempty convex
values, its graph is convex iff `f` is affine on `Δ(X)`, and both its Dirac and its collapse fixed
points are exactly the fixed points of `f` in `Δ(X)`. Instances: `negation` on `Δ(Fin 2)` (affine,
unique fixed point `![1/2, 1/2]`) and `id` (affine, fixed-point set `Δ(X)`) — the two desiderata the
notes attribute to Scott, realized at the level of fixed-point *sets* (ATTRIBUTION-UNVETTED that this
is his reading).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set

/-- **Affine on a set**: `f (t • p + (1 - t) • q) = t • f p + (1 - t) • f q` for `p, q ∈ K`,
`t ∈ [0, 1]`.
Source: [[fixpoint-lit-inventory]] 003 ("`f` is affine on `Δ(X)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def AffineOn {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
    (f : E → F) (K : Set E) : Prop :=
  ∀ p ∈ K, ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, f (t • p + (1 - t) • q) = t • f p + (1 - t) • f q

/-- `AffineOn` in Mathlib's `a + b = 1` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem AffineOn.combo {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
    {f : E → F} {K : Set E} (hf : AffineOn f K) {p q : E} (hp : p ∈ K) (hq : q ∈ K) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : f (a • p + b • q) = a • f p + b • f q := by
  obtain rfl : b = 1 - a := by linarith
  exact hf p hp q hq a ⟨ha, by linarith⟩

variable {X : Type*} [Fintype X]

/-- **Target 2: the Dirac lift has a convex graph iff `f` is constant on `Δ(X)`** (no `|X| ≥ 2`
needed). ⟹: the midpoint of `(p, δ_{f p})` and `(q, δ_{f q})` must lie on the graph, so a proper
mixture of two point masses is a point mass, forcing `f p = f q` (`eq_of_combo_dirac_eq_dirac`).
⟸: the graph is `Δ(X) × {δ_c}`.
Source: [[fixpoint-lit-inventory]] 002 (conversation-notes §2 "The Convexity Problem";
conversation-reconstruction "won't be convex (unless `f` is affine)" — the note's "affine" should be
"constant": finding F1)
Kind: P
Fidelity: stronger: no cardinality hypothesis, and no hypothesis that `f` maps `Δ(X)` to itself;
variant: Δ² finitely supported
Hyps: (a) none; (c) carrier: Δ² as finitely supported measures -/
theorem hasConvexGraph_diracLift_iff (f : (X → ℝ) → (X → ℝ)) :
    HasConvexGraph (diracLift f) ↔ ∀ p ∈ stdSimplex ℝ X, ∀ q ∈ stdSimplex ℝ X, f p = f q := by
  constructor
  · intro h p hp q hq
    have h1 : (p, dirac (f p)) ∈ Graph (diracLift f) := ⟨hp, rfl⟩
    have h2 : (q, dirac (f q)) ∈ Graph (diracLift f) := ⟨hq, rfl⟩
    have hm := h h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    obtain ⟨-, hμ⟩ := hm
    simp only [Prod.smul_mk, Prod.mk_add_mk, diracLift, mem_singleton_iff] at hμ
    have hμ' : (1 / 2 : ℝ) • dirac (f p) + (1 - 1 / 2 : ℝ) • dirac (f q) =
        dirac (f ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q)) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; exact hμ
    exact eq_of_combo_dirac_eq_dirac (by norm_num) (by norm_num) hμ'
  · intro h
    rintro ⟨p, μ⟩ ⟨hp, hμ⟩ ⟨q, ν⟩ ⟨hq, hν⟩ a b ha hb hab
    have hμ' : μ = dirac (f p) := hμ
    have hν' : ν = dirac (f q) := hν
    have hpq : a • p + b • q ∈ stdSimplex ℝ X := convex_stdSimplex ℝ X hp hq ha hb hab
    refine ⟨hpq, ?_⟩
    show a • μ + b • ν ∈ diracLift f (a • p + b • q)
    rw [hμ', hν', h p hp q hq, h q hq _ hpq, ← add_smul, hab, one_smul]
    rfl

/-- **Target 3 (i), nonempty values**: `δ_{f p} ∈ baryLift f p` when `f p ∈ Δ(X)`.
Source: [[fixpoint-lit-inventory]] 003 (i)
Kind: P
Fidelity: variant: Δ² finitely supported
Hyps: (a) `MapsTo f Δ Δ` is the note's standing assumption `f : Δ(X) → Δ(X)`; (c) carrier: Δ² as finitely supported measures -/
theorem baryLift_nonempty {f : (X → ℝ) → (X → ℝ)} (hf : MapsTo f (stdSimplex ℝ X) (stdSimplex ℝ X))
    {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) : (baryLift f p).Nonempty :=
  ⟨dirac (f p), dirac_mem_finMeasure (hf hp), by simp⟩

/-- **Target 3 (i), convex values**: `baryLift f p = Δ² ∩ bary⁻¹ {f p}` is convex.
Source: [[fixpoint-lit-inventory]] 003 (i)
Kind: P
Fidelity: variant: Δ² finitely supported
Hyps: (a) none; (c) carrier: Δ² as finitely supported measures -/
theorem baryLift_convex (f : (X → ℝ) → (X → ℝ)) (p : X → ℝ) : Convex ℝ (baryLift f p) := by
  have : baryLift f p = FinMeasure X ∩ bary ⁻¹' {f p} := by
    ext μ; simp [baryLift]
  rw [this]
  exact convex_finMeasure.inter ((convex_singleton _).linear_preimage bary)

/-- **Target 3 (ii): the barycentric lift has a convex graph iff `f` is affine on `Δ(X)`.**
⟸: mix two graph points and use that `bary` is linear. ⟹: mix `(p, δ_{f p})` and `(q, δ_{f q})`.
Source: [[fixpoint-lit-inventory]] 003 (ii) (the precise reading of the "affine" remark of 002)
Kind: P
Fidelity: variant: Δ² finitely supported
Hyps: (a) `MapsTo f Δ Δ` is the note's standing assumption; (c) carrier: Δ² as finitely supported measures -/
theorem hasConvexGraph_baryLift_iff {f : (X → ℝ) → (X → ℝ)}
    (hf : MapsTo f (stdSimplex ℝ X) (stdSimplex ℝ X)) :
    HasConvexGraph (baryLift f) ↔ AffineOn f (stdSimplex ℝ X) := by
  constructor
  · intro h p hp q hq t ht
    have h1 : (p, dirac (f p)) ∈ Graph (baryLift f) := ⟨hp, dirac_mem_finMeasure (hf hp), by simp⟩
    have h2 : (q, dirac (f q)) ∈ Graph (baryLift f) := ⟨hq, dirac_mem_finMeasure (hf hq), by simp⟩
    have hm := h h1 h2 (show (0 : ℝ) ≤ t from ht.1) (show (0 : ℝ) ≤ 1 - t by linarith [ht.2])
      (show t + (1 - t) = 1 by ring)
    obtain ⟨-, -, hb⟩ := hm
    simp only [Prod.smul_mk, Prod.mk_add_mk, map_add, map_smul, bary_dirac] at hb
    exact hb.symm
  · intro haff
    rintro ⟨p, μ⟩ ⟨hp, hμF, hμb⟩ ⟨q, ν⟩ ⟨hq, hνF, hνb⟩ a b ha hb hab
    refine ⟨convex_stdSimplex ℝ X hp hq ha hb hab, convex_finMeasure hμF hνF ha hb hab, ?_⟩
    show bary (a • μ + b • ν) = f (a • p + b • q)
    rw [map_add, map_smul, map_smul, hμb, hνb, haff.combo hp hq ha hb hab]

/-- **Target 3 (iii): the Dirac fixed points of `baryLift f` are exactly `Fix f ∩ Δ(X)`.**
Source: [[fixpoint-lit-inventory]] 003 (iii)
Kind: P
Fidelity: variant: Δ² finitely supported
Hyps: (a) none; (c) carrier: Δ² as finitely supported measures -/
theorem isDiracFixedPoint_baryLift_iff (f : (X → ℝ) → (X → ℝ)) (p : X → ℝ) :
    IsDiracFixedPoint (baryLift f) p ↔ p ∈ stdSimplex ℝ X ∧ f p = p := by
  constructor
  · rintro ⟨hp, -, hb⟩
    rw [bary_dirac] at hb
    exact ⟨hp, hb.symm⟩
  · rintro ⟨hp, hfp⟩
    exact ⟨hp, dirac_mem_finMeasure hp, by rw [bary_dirac, hfp]⟩

/-- **Target 3 (iv): the collapse fixed points of `baryLift f` are exactly `Fix f ∩ Δ(X)`.** So for
lifts of functions the `Δ²` level adds nothing to fixed-point *sets*.
Source: [[fixpoint-lit-inventory]] 003 (iv); 015 (the script's search finds collapse fixed points)
Kind: P
Fidelity: variant: Δ² finitely supported
Hyps: (a) `MapsTo f Δ Δ` is the note's standing assumption (used for ⟸ only); (c) carrier: Δ² as finitely supported measures -/
theorem isCollapseFixedPoint_baryLift_iff {f : (X → ℝ) → (X → ℝ)}
    (hf : MapsTo f (stdSimplex ℝ X) (stdSimplex ℝ X)) (p : X → ℝ) :
    IsCollapseFixedPoint (baryLift f) p ↔ p ∈ stdSimplex ℝ X ∧ f p = p := by
  constructor
  · rintro ⟨hp, μ, ⟨-, hμb⟩, hμp⟩
    exact ⟨hp, by rw [← hμb, hμp]⟩
  · rintro ⟨hp, hfp⟩
    exact ⟨hp, dirac (f p), ⟨dirac_mem_finMeasure (hf hp), by simp⟩, by rw [bary_dirac, hfp]⟩

/-! ### Instances: negation and identity -/

/-- **Negation on `Δ(Fin 2)`**: `p ↦ ![p 1, p 0]` (swap the two probabilities).
Source: [[fixpoint-lit-inventory]] 003 ("negation `p ↦ (p₁, p₀)`"); README "Specific Examples Scott
Mentioned" (ATTRIBUTION-UNVETTED)
Kind: D
Fidelity: exact
Hyps: n/a -/
def negation (p : Fin 2 → ℝ) : Fin 2 → ℝ := ![p 1, p 0]

/-- `negation` maps `Δ(Fin 2)` to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem negation_mapsTo : MapsTo negation (stdSimplex ℝ (Fin 2)) (stdSimplex ℝ (Fin 2)) := by
  intro p hp
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [negation, hp.1]
  · have := hp.2
    simp only [Fin.sum_univ_two, negation, Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
    linarith

/-- `negation` is affine (on any set, in particular on `Δ(Fin 2)`).
Source: [[fixpoint-lit-inventory]] 003 ("negation … is affine")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem affineOn_negation (K : Set (Fin 2 → ℝ)) : AffineOn negation K := by
  intro p _ q _ t _
  ext i
  fin_cases i <;> simp [negation]

/-- `negation` is not constant on `Δ(Fin 2)`: it swaps the two vertices.
Source: none: infrastructure (audit round 1, fidelity probe)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem negation_not_const :
    ¬ ∀ p ∈ stdSimplex ℝ (Fin 2), ∀ q ∈ stdSimplex ℝ (Fin 2), negation p = negation q := by
  intro h
  have h0 := h (Pi.single 0 1) (single_mem_stdSimplex ℝ 0) (Pi.single 1 1) (single_mem_stdSimplex ℝ 1)
  have := congrFun h0 0
  simp [negation] at this

/-- **The Dirac lift of `negation` does not have a convex graph** — `negation` is affine
(`affineOn_negation`) but not constant, so target 2's iff bites: the ⟸ direction of
`hasConvexGraph_diracLift_iff` is not vacuous, and the contrast with `hasConvexGraph_baryLift_iff`
(the *barycentric* lift of `negation` does have a convex graph) is the precise content of finding F1.
Source: [[fixpoint-lit-inventory]] 002 (the negation example of conversation-notes §2)
Kind: N+
Fidelity: variant: Δ² finitely supported
Hyps: (a) none; (c) carrier: Δ² as finitely supported measures -/
theorem not_hasConvexGraph_diracLift_negation : ¬ HasConvexGraph (diracLift negation) := by
  rw [hasConvexGraph_diracLift_iff]
  exact negation_not_const

/-- **The negation instance (N+)**: the Dirac fixed points of `baryLift negation` are exactly
`{![1/2, 1/2]}` — "negation has a unique fixed point, the uniform distribution", at the level of the
fixed-point set (by target 3 (iii): `negation p = p ∧ p ∈ Δ` forces `p 0 = p 1 = 1/2`).
Source: [[fixpoint-lit-inventory]] 003 (instance); README "negation ↦ mass on 50 %"
(ATTRIBUTION-UNVETTED that this set-level reading is Scott's)
Kind: N+
Fidelity: variant: Δ² finitely supported; the desideratum is realized as a fixed-point *set*
Hyps: (a) none -/
theorem diracFixedPoints_baryLift_negation :
    {p | IsDiracFixedPoint (baryLift negation) p} = {![1 / 2, 1 / 2]} := by
  ext p
  rw [mem_setOf_eq, isDiracFixedPoint_baryLift_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hp, hfp⟩
    have h0 := congrFun hfp 0
    have hs := hp.2
    simp only [negation, Matrix.cons_val_zero, Fin.sum_univ_two] at h0 hs
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp
    · simp [Fin.sum_univ_two]; norm_num
    · ext i; fin_cases i <;> simp [negation]

/-- The collapse fixed points of `baryLift negation` are the same set `{![1/2, 1/2]}`.
Source: [[fixpoint-lit-inventory]] 003 (iv), 015
Kind: N+
Fidelity: variant: Δ² finitely supported
Hyps: (a) none -/
theorem collapseFixedPoints_baryLift_negation :
    {p | IsCollapseFixedPoint (baryLift negation) p} = {![1 / 2, 1 / 2]} := by
  rw [← diracFixedPoints_baryLift_negation]
  ext p
  simp only [mem_setOf_eq, isCollapseFixedPoint_baryLift_iff negation_mapsTo,
    isDiracFixedPoint_baryLift_iff]

omit [Fintype X] in
/-- `id` is affine on any set.
Source: [[fixpoint-lit-inventory]] 003 ("the identity is affine")
Kind: L
Fidelity: exact
Hyps: none -/
theorem affineOn_id (K : Set (X → ℝ)) : AffineOn (id : (X → ℝ) → (X → ℝ)) K :=
  fun _ _ _ _ _ _ => rfl

/-- **The identity instance (N+)**: the Dirac fixed points of `baryLift id` are all of `Δ(X)` —
"the identity spreads its fixed points over all of `Δ(X)`", at the level of the fixed-point set.
Source: [[fixpoint-lit-inventory]] 003 (instance); README "identity ↦ spread over all of Δ(X)"
(ATTRIBUTION-UNVETTED that this set-level reading is Scott's)
Kind: N+
Fidelity: variant: Δ² finitely supported; the desideratum is realized as a fixed-point *set*
Hyps: (a) none -/
theorem diracFixedPoints_baryLift_id :
    {p | IsDiracFixedPoint (baryLift (id : (X → ℝ) → (X → ℝ))) p} = stdSimplex ℝ X := by
  ext p
  simp [isDiracFixedPoint_baryLift_iff]

/-- The collapse fixed points of `baryLift id` are all of `Δ(X)`.
Source: [[fixpoint-lit-inventory]] 003 (iv)
Kind: N+
Fidelity: variant: Δ² finitely supported
Hyps: (a) none -/
theorem collapseFixedPoints_baryLift_id :
    {p | IsCollapseFixedPoint (baryLift (id : (X → ℝ) → (X → ℝ))) p} = stdSimplex ℝ X := by
  ext p
  simp [isCollapseFixedPoint_baryLift_iff (mapsTo_id _)]

end Cleanroom.Fixpoint.FixOraclesCorresp
