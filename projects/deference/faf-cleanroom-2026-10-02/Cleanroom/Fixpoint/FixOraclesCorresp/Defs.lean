import Cleanroom.Found.FixKakutani
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Convex.StdSimplex

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Defs`: definitions of record for Part A

The `internal-fixpoint/reflective-oracles-project/` notes take fixed points of correspondences
`G : Δ(X) ⇉ Δ²(X)` (mandate target 1). Carrier: `X` a `Fintype`, `Δ(X) := stdSimplex ℝ X ⊆ (X → ℝ)`,
and **Δ²(X) as finitely supported measures** on `X → ℝ` whose support lies in `Δ(X)`
(`FinMeasure X`, a `(c)` modelling substitution for the notes' Borel `Δ(Δ(X))`, disclosed on every
Part A headline as `Fidelity: variant: Δ² finitely supported`). `bary` is the barycentre (the monad
multiplication), `dirac p` the point mass (the unit), `Graph G` the graph over `Δ(X)`,
`HasConvexGraph G` whole-graph convexity, and the two fixed-point notions of the notes: *Dirac*
(`δ_p ∈ G p`, the docs' definition) and *collapse* (`p ∈ bary '' G p`, the docs' "Option 3").
`diracLift` and `baryLift` are the two lifts of a function `f : Δ(X) → Δ(X)`.

Junk-value guards: `dirac p` with `p ∉ Δ(X)` is a point mass outside `Δ²(X)`; both fixed-point
predicates therefore carry the conjunct `p ∈ Δ(X)`, and `FinMeasure` carries `support ⊆ Δ(X)`.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set

section Generic

variable {α β : Type*}

/-- The graph of a correspondence `G` over a domain `K`: `{(x, y) | x ∈ K ∧ y ∈ G x}`. This is the set
whose closedness is `Cleanroom.Found.FixKakutani.HasClosedGraphOn G K` (definitionally).
Source: [[fixpoint-lit-inventory]] 001 (mathematical-formulation §3 "Graph(G)")
Kind: D
Fidelity: exact
Hyps: n/a -/
def graphOn (K : Set α) (G : α → Set β) : Set (α × β) := {q | q.1 ∈ K ∧ q.2 ∈ G q.1}

/-- `HasClosedGraphOn G K` is closedness of `graphOn K G`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasClosedGraphOn_iff_isClosed_graphOn [TopologicalSpace α] [TopologicalSpace β]
    (G : α → Set β) (K : Set α) :
    Cleanroom.Found.FixKakutani.HasClosedGraphOn G K ↔ IsClosed (graphOn K G) := Iff.rfl

/-- A convex graph has convex slices: if `graphOn K G` is convex then `G x` is convex for `x ∈ K`
(the slice at `x` is the section of the graph, and `a • x + b • x = x`).
Source: [[fixpoint-lit-inventory]] 011(i) ("its slices are nonempty convex")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem convex_apply_of_convex_graphOn [AddCommMonoid α] [Module ℝ α] [AddCommMonoid β]
    [Module ℝ β] {K : Set α} {G : α → Set β} (h : Convex ℝ (graphOn K G)) {x : α} (hx : x ∈ K) :
    Convex ℝ (G x) := by
  intro y hy z hz a b ha hb hab
  have := h (show (x, y) ∈ graphOn K G from ⟨hx, hy⟩) (show (x, z) ∈ graphOn K G from ⟨hx, hz⟩)
    ha hb hab
  simp only [graphOn, Prod.smul_mk, Prod.mk_add_mk, mem_setOf_eq, Convex.combo_self hab] at this
  exact this.2

end Generic

variable {X : Type*} [Fintype X]

/-- **Δ²(X) as finitely supported measures**: `μ : (X → ℝ) →₀ ℝ` with nonnegative weights, total
mass `1`, and support inside `Δ(X) = stdSimplex ℝ X`. A `(c)` modelling substitution for the notes'
Borel probability measures on the simplex (every example, counterexample and repair of Part A lives
inside finitely supported measures, so nothing the notes claim is weakened except the topology of
target 5, see `exists_collapse_fixed_point`).
Source: [[fixpoint-lit-inventory]] 003 ("replace Δ² by finitely-supported measures to stay
elementary"); mathematical-formulation §1 (Δ²(X))
Kind: D
Fidelity: variant: Δ² finitely supported
Hyps: n/a -/
def FinMeasure (X : Type*) [Fintype X] : Set ((X → ℝ) →₀ ℝ) :=
  {μ | (∀ q, 0 ≤ μ q) ∧ μ.sum (fun _ w => w) = 1 ∧ (↑μ.support : Set (X → ℝ)) ⊆ stdSimplex ℝ X}

/-- The total mass `∑ w` of a finitely supported measure, as a linear map (so that convexity of
`FinMeasure` is linear algebra).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def mass : ((X → ℝ) →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ (fun _ => (1 : ℝ))

omit [Fintype X] in
/-- `mass μ = μ.sum (fun _ w => w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_apply (μ : (X → ℝ) →₀ ℝ) : mass μ = μ.sum (fun _ w => w) := by
  simp [mass, Finsupp.linearCombination_apply]

/-- **The barycentre** `bary μ = ∑ q, μ q • q` (the monad multiplication `Δ²(X) → Δ(X)`), as a linear
map on all finitely supported functions.
Source: [[fixpoint-lit-inventory]] 003 (mathematical-formulation §4 Example 2, `∫ q dμ = p`);
conversation-reconstruction "Option 3: With Monad Collapse"
Kind: D
Fidelity: exact (on `FinMeasure`, the integral is the finite sum)
Hyps: n/a -/
noncomputable def bary : ((X → ℝ) →₀ ℝ) →ₗ[ℝ] (X → ℝ) := Finsupp.linearCombination ℝ id

omit [Fintype X] in
/-- `bary μ = μ.sum (fun q w => w • q)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem bary_apply (μ : (X → ℝ) →₀ ℝ) : bary μ = μ.sum (fun q w => w • q) := by
  simp [bary, Finsupp.linearCombination_apply]

/-- **The point mass** `δ_p = Finsupp.single p 1` (the monad unit `ι : Δ(X) → Δ²(X)`). Junk when
`p ∉ Δ(X)`: consumers keep the conjunct `p ∈ Δ(X)`.
Source: [[fixpoint-lit-inventory]] 001 (`ι(p) = δ_p`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def dirac (p : X → ℝ) : (X → ℝ) →₀ ℝ := Finsupp.single p 1

omit [Fintype X] in
/-- `bary (dirac p) = p`: the monad unit law.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem bary_dirac (p : X → ℝ) : bary (dirac p) = p := by
  simp [bary, dirac, Finsupp.linearCombination_single]

omit [Fintype X] in
/-- `mass (dirac p) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mass_dirac (p : X → ℝ) : mass (dirac p) = 1 := by
  simp [mass, dirac, Finsupp.linearCombination_single]

/-- `δ_p ∈ Δ²(X)` for `p ∈ Δ(X)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dirac_mem_finMeasure {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) : dirac p ∈ FinMeasure X := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    classical
    simp only [dirac, Finsupp.single_apply]
    split_ifs <;> norm_num
  · rw [← mass_apply, mass_dirac]
  · intro q hq
    have : q ∈ ({p} : Finset (X → ℝ)) := Finsupp.support_single_subset (Finset.mem_coe.1 hq)
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hp

/-- The mass of a finitely supported measure is `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_one_of_mem {μ : (X → ℝ) →₀ ℝ} (hμ : μ ∈ FinMeasure X) : mass μ = 1 := by
  rw [mass_apply]; exact hμ.2.1

/-- The barycentre of a finitely supported measure on `Δ(X)` lies in `Δ(X)`.
Source: [[fixpoint-lit-inventory]] 005 ("bary is affine and continuous", values in Δ(X))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bary_mem_stdSimplex {μ : (X → ℝ) →₀ ℝ} (hμ : μ ∈ FinMeasure X) :
    bary μ ∈ stdSimplex ℝ X := by
  obtain ⟨hnn, hsum, hsupp⟩ := hμ
  rw [bary_apply]
  have hsupp' : ∀ q ∈ μ.support, q ∈ stdSimplex ℝ X := fun q hq => hsupp (Finset.mem_coe.2 hq)
  constructor
  · intro x
    rw [Finsupp.sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun q hq => mul_nonneg (hnn q) ((hsupp' q hq).1 x)
  · rw [Finsupp.sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    have : ∀ q ∈ μ.support, ∑ x, μ q * q x = μ q := fun q hq => by
      rw [← Finset.mul_sum, (hsupp' q hq).2, mul_one]
    rw [Finset.sum_congr rfl this]
    simpa [Finsupp.sum] using hsum

/-- `Δ²(X)` is convex.
Source: none: infrastructure
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem convex_finMeasure : Convex ℝ (FinMeasure X) := by
  intro μ hμ ν hν a b ha hb hab
  obtain ⟨hμn, hμs, hμsupp⟩ := hμ
  obtain ⟨hνn, hνs, hνsupp⟩ := hν
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hμn q)) (mul_nonneg hb (hνn q))
  · rw [← mass_apply, map_add, map_smul, map_smul, mass_apply, mass_apply, hμs, hνs]
    simp [hab]
  · intro q hq
    have hq' : q ∈ (a • μ).support ∪ (b • ν).support :=
      Finsupp.support_add (Finset.mem_coe.1 hq)
    rcases Finset.mem_union.1 hq' with h | h
    · exact hμsupp (Finset.mem_coe.2 (Finsupp.support_smul h))
    · exact hνsupp (Finset.mem_coe.2 (Finsupp.support_smul h))

/-- **The graph** of `G : Δ(X) ⇉ Δ²(X)`: `{(p, μ) | p ∈ Δ(X) ∧ μ ∈ G p}`, in the product module
`(X → ℝ) × ((X → ℝ) →₀ ℝ)`.
Source: [[fixpoint-lit-inventory]] 001 (mathematical-formulation §3)
Kind: D
Fidelity: variant: Δ² finitely supported
Hyps: n/a -/
def Graph (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ)) : Set ((X → ℝ) × ((X → ℝ) →₀ ℝ)) :=
  graphOn (stdSimplex ℝ X) G

/-- **Whole-graph convexity** (the notes' "convex-graph correspondence"): `Graph G` is convex.
Source: [[fixpoint-lit-inventory]] 004 (theoretical-insights §2 l. 30 "Key Innovation: Convex Graph
Property" — "require the entire graph to be convex"; mathematical-formulation §3 Definition 2 — "a
convex subset of Δ(X) × Δ²(X) … stronger than Kakutani's requirement")
Kind: D
Fidelity: variant: Δ² finitely supported
Hyps: n/a -/
def HasConvexGraph (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ)) : Prop := Convex ℝ (Graph G)

/-- **Dirac fixed point** (the docs' definition of fixed point): `p ∈ Δ(X)` and `δ_p ∈ G p`.
Source: [[fixpoint-lit-inventory]] 001 (mathematical-formulation §3; `ReflectiveOracles.lean`
`fixedPoints`)
Kind: D
Fidelity: variant: Δ² finitely supported (plus the explicit `p ∈ Δ(X)` guard)
Hyps: n/a -/
def IsDiracFixedPoint (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ)) (p : X → ℝ) : Prop :=
  p ∈ stdSimplex ℝ X ∧ dirac p ∈ G p

/-- **Collapse fixed point** (the docs' "Option 3", `Δ(X) → Δ² ⇉ Δ² → Δ(X)` via the monad
multiplication): `p ∈ Δ(X)` and `p ∈ bary '' G p`.
Source: [[fixpoint-lit-inventory]] 005 (conversation-reconstruction "Option 3: With Monad Collapse";
`distribution_fixed_points.py:find_fixed_points`)
Kind: D
Fidelity: variant: Δ² finitely supported
Hyps: n/a -/
def IsCollapseFixedPoint (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ)) (p : X → ℝ) : Prop :=
  p ∈ stdSimplex ℝ X ∧ p ∈ bary '' G p

/-- **The Dirac lift** of `f`: `G p = {δ_{f p}}`.
Source: [[fixpoint-lit-inventory]] 002 (conversation-notes §2, conversation-reconstruction "lift a
function directly by `G(p) = δ_{f(p)}`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def diracLift (f : (X → ℝ) → (X → ℝ)) : (X → ℝ) → Set ((X → ℝ) →₀ ℝ) :=
  fun p => {dirac (f p)}

/-- **The barycentric lift** of `f`: `G p = {μ ∈ Δ²(X) | bary μ = f p}`.
Source: [[fixpoint-lit-inventory]] 003 (mathematical-formulation §4 Example 2: `G_id(p) = {μ : ∫ q dμ
= p}`)
Kind: D
Fidelity: variant: Δ² finitely supported
Hyps: n/a -/
def baryLift (f : (X → ℝ) → (X → ℝ)) : (X → ℝ) → Set ((X → ℝ) →₀ ℝ) :=
  fun p => {μ | μ ∈ FinMeasure X ∧ bary μ = f p}

/-- fixpoint-lit-001, first half: `p` is a Dirac fixed point iff `(p, δ_p) ∈ Graph G`. This is the
definition restated (`Iff.rfl`): the notes' "Key Theorem: Fixed Points as Intersections" has no content
beyond the definition of fixed point.
Source: [[fixpoint-lit-inventory]] 001 (mathematical-formulation §3 "Key Theorem")
Kind: L
Fidelity: exact
Hyps: none -/
theorem isDiracFixedPoint_iff_mem_graph (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ)) (p : X → ℝ) :
    IsDiracFixedPoint G p ↔ (p, dirac p) ∈ Graph G := Iff.rfl

/-- fixpoint-lit-001, second half: the Dirac fixed-point set is the first projection of
`Graph G ∩ Graph (diracLift id)` (the graph of the unit `ι`). Again a restatement of the definition.
Source: [[fixpoint-lit-inventory]] 001 (mathematical-formulation §3 "Fix(G) = π₁(Graph(G) ∩ Graph(ι))")
Kind: L
Fidelity: exact
Hyps: none -/
theorem diracFixedPoints_eq_fst_image (G : (X → ℝ) → Set ((X → ℝ) →₀ ℝ)) :
    {p | IsDiracFixedPoint G p} = Prod.fst '' (Graph G ∩ Graph (diracLift id)) := by
  ext p
  constructor
  · rintro ⟨hp, hG⟩
    exact ⟨(p, dirac p), ⟨⟨hp, hG⟩, ⟨hp, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨q, μ⟩, ⟨⟨hq, hμ⟩, ⟨-, hμ'⟩⟩, rfl⟩
    have : μ = dirac q := hμ'
    subst this
    exact ⟨hq, hμ⟩

/-- **The key lemma of target 2**: a proper mixture of two point masses is a point mass only if the
two points coincide (evaluate at `a`: the left side is `t ∈ (0,1)` when `a ≠ b`, the right side is
`0` or `1`).
Source: [[fixpoint-lit-inventory]] 002 (conversation-notes §2 "NOT a point mass unless
`f(p₁) = f(p₂)`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem eq_of_combo_dirac_eq_dirac {a b c : X → ℝ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : t • dirac a + (1 - t) • dirac b = dirac c) : a = b := by
  classical
  by_contra hab
  have hba : b ≠ a := fun h' => hab h'.symm
  have := congrArg (fun μ : (X → ℝ) →₀ ℝ => μ a) h
  simp only [dirac, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    Finsupp.single_apply, smul_eq_mul, if_true, hba, if_false, mul_one, mul_zero, add_zero] at this
  split_ifs at this <;> linarith

end Cleanroom.Fixpoint.FixOraclesCorresp
