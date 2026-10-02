import Cleanroom.Fixpoint.FixOraclesCorresp.Defs
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Fin.VecNotation

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Composition`: composition of correspondences

Target 7, second half (fixpoint-lit-010/011 (i)(ii)), the Discord claims: Kakutani correspondences do
not compose (`comp H F` of two nonempty-convex-valued closed-graph correspondences need not be
convex-valued: `F ≡ [0,1]`, `H y = {(y, y²)}`, whose composite at any point is the parabola arc), while
total convex-graph relations do (`comp_total_convex`), and closedness composes when the middle set is
compact (`isClosed_graphOn_comp`). Then 011: a total relation on a compact convex set with closed
convex graph has a point related to itself (`exists_mem_self_of_convex_closed_graph`, via
`kakutani_findim` on the slices), and a cycle of `n` Kakutani correspondences has a cyclic point
(`exists_cyclic_point`, via `kakutani_findim` on the product), hence the composite
`f (n−1) ∘ ⋯ ∘ f 0` has a fixed point although it need not be Kakutani (`mem_iterComp_of_cyclic`).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Cleanroom.Found.FixKakutani

section Comp

variable {α β γ : Type*}

/-- **Composition of correspondences**: `comp S R x = {z | ∃ y ∈ R x, z ∈ S y}`.
Source: [[fixpoint-lit-inventory]] 010 (discord-notes "Composition of Kakutani Maps")
Kind: D
Fidelity: exact
Hyps: n/a -/
def comp (S : β → Set γ) (R : α → Set β) : α → Set γ := fun x => {z | ∃ y ∈ R x, z ∈ S y}

/-- **Target 7-composition (ii): total convex-graph relations compose.** If `R : A ⇉ B` and `S : B ⇉ C`
are total with convex graphs (and `R` takes values in `B` on `A`), then `comp S R : A ⇉ C` is total with
convex graph.
Source: [[fixpoint-lit-inventory]] 010 (ii) (Scott: "Total convex-graph relations still compose")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem comp_total_convex [AddCommMonoid α] [Module ℝ α] [AddCommMonoid β] [Module ℝ β]
    [AddCommMonoid γ] [Module ℝ γ] {A : Set α} {B : Set β} {R : α → Set β} {S : β → Set γ}
    (hRB : ∀ x ∈ A, R x ⊆ B) (hRt : ∀ x ∈ A, (R x).Nonempty) (hSt : ∀ y ∈ B, (S y).Nonempty)
    (hRc : Convex ℝ (graphOn A R)) (hSc : Convex ℝ (graphOn B S)) :
    (∀ x ∈ A, (comp S R x).Nonempty) ∧ Convex ℝ (graphOn A (comp S R)) := by
  constructor
  · intro x hx
    obtain ⟨y, hy⟩ := hRt x hx
    obtain ⟨z, hz⟩ := hSt y (hRB x hx hy)
    exact ⟨z, y, hy, hz⟩
  · rintro ⟨x, z⟩ ⟨hx, y, hy, hz⟩ ⟨x', z'⟩ ⟨hx', y', hy', hz'⟩ a b ha hb hab
    have h1 := hRc (show (x, y) ∈ graphOn A R from ⟨hx, hy⟩)
      (show (x', y') ∈ graphOn A R from ⟨hx', hy'⟩) ha hb hab
    have h2 := hSc (show (y, z) ∈ graphOn B S from ⟨hRB x hx hy, hz⟩)
      (show (y', z') ∈ graphOn B S from ⟨hRB x' hx' hy', hz'⟩) ha hb hab
    simp only [graphOn, Prod.smul_mk, Prod.mk_add_mk, mem_setOf_eq] at h1 h2 ⊢
    exact ⟨h1.1, a • y + b • y', h1.2, h2.2⟩

/-- **Target 7-composition (iii): closedness composes over a compact middle set.** If `B` is compact,
`R` takes values in `B` on `A`, and the graphs of `R` over `A` and of `S` over `B` are closed, then the
graph of `comp S R` over `A` is closed (projection along the compact factor is a closed map).
Source: [[fixpoint-lit-inventory]] 010 (iii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isClosed_graphOn_comp [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {A : Set α} {B : Set β} {R : α → Set β} {S : β → Set γ} (hB : IsCompact B)
    (hRB : ∀ x ∈ A, R x ⊆ B) (hRcl : IsClosed (graphOn A R)) (hScl : IsClosed (graphOn B S)) :
    IsClosed (graphOn A (comp S R)) := by
  haveI : CompactSpace B := isCompact_iff_compactSpace.1 hB
  let T : Set (B × (α × γ)) :=
    {p | (p.2.1, (p.1 : β)) ∈ graphOn A R ∧ ((p.1 : β), p.2.2) ∈ graphOn B S}
  have hT : IsClosed T :=
    (hRcl.preimage (by fun_prop)).inter (hScl.preimage (by fun_prop))
  have hEq : graphOn A (comp S R) = Prod.snd '' T := by
    ext ⟨x, z⟩
    constructor
    · rintro ⟨hx, y, hy, hz⟩
      exact ⟨(⟨y, hRB x hx hy⟩, (x, z)), ⟨⟨hx, hy⟩, ⟨hRB x hx hy, hz⟩⟩, rfl⟩
    · rintro ⟨⟨⟨y, hyB⟩, ⟨x', z'⟩⟩, ⟨⟨hx, hy⟩, ⟨-, hz⟩⟩, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hx, y, hy, hz⟩
  rw [hEq]
  exact isClosedMap_snd_of_compactSpace T hT

end Comp

/-! ### Target 7-composition (i): Kakutani correspondences do not compose -/

/-- The constant correspondence `F ≡ [0, 1]` on `[0, 1] ⊆ ℝ`.
Source: [[fixpoint-lit-inventory]] 010 (i)
Kind: D
Fidelity: exact
Hyps: n/a -/
def fullF (_ : ℝ) : Set ℝ := Icc 0 1

/-- The single-valued correspondence `H y = {(y, y²)}`.
Source: [[fixpoint-lit-inventory]] 010 (i) (the survey's half-circle replaced by the parabola arc, as
the mandate specifies)
Kind: D
Fidelity: variant: parabola in place of the half-circle
Hyps: n/a -/
def parabH (y : ℝ) : Set (ℝ × ℝ) := {(y, y ^ 2)}

/-- `fullF` is Kakutani on `[0, 1]`: nonempty convex values in `[0,1]`, closed graph.
Source: [[fixpoint-lit-inventory]] 010 (i)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fullF_kakutani :
    (∀ x ∈ Icc (0 : ℝ) 1, fullF x ⊆ Icc 0 1) ∧ (∀ x ∈ Icc (0 : ℝ) 1, (fullF x).Nonempty) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, Convex ℝ (fullF x)) ∧ HasClosedGraphOn fullF (Icc 0 1) := by
  refine ⟨fun _ _ => subset_rfl, fun _ _ => ⟨0, le_rfl, zero_le_one⟩, fun _ _ => convex_Icc 0 1, ?_⟩
  unfold HasClosedGraphOn fullF
  exact (isClosed_Icc.preimage continuous_fst).inter (isClosed_Icc.preimage continuous_snd)

/-- `parabH` is Kakutani on `[0, 1]`: values in `[0, 1]²`, nonempty convex (singleton) values, closed
graph.
Source: [[fixpoint-lit-inventory]] 010 (i)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem parabH_kakutani :
    (∀ y ∈ Icc (0 : ℝ) 1, parabH y ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
    (∀ y ∈ Icc (0 : ℝ) 1, (parabH y).Nonempty) ∧ (∀ y ∈ Icc (0 : ℝ) 1, Convex ℝ (parabH y)) ∧
    HasClosedGraphOn parabH (Icc 0 1) := by
  refine ⟨fun y hy q hq => ?_, fun y _ => ⟨_, rfl⟩, fun _ _ => convex_singleton _, ?_⟩
  · rw [parabH, mem_singleton_iff] at hq
    subst hq
    exact ⟨hy, pow_nonneg hy.1 2, pow_le_one₀ hy.1 hy.2⟩
  unfold HasClosedGraphOn
  have : {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ parabH p.1} =
      {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc (0 : ℝ) 1} ∩ {p | p.2 = (p.1, p.1 ^ 2)} := by
    ext p; simp [parabH]
  rw [this]
  exact (isClosed_Icc.preimage continuous_fst).inter
    (isClosed_eq continuous_snd (continuous_fst.prodMk (continuous_fst.pow 2)))

/-- **Target 7-composition (i): the composite of two Kakutani correspondences need not be
convex-valued.** `comp parabH fullF x` is the parabola arc `{(y, y²) | y ∈ [0,1]}`, which contains
`(0,0)` and `(1,1)` but not their midpoint `(1/2, 1/2)`.
Source: [[fixpoint-lit-inventory]] 010 (i) (Scott: "kakutani maps do not compose")
Kind: P
Fidelity: variant: parabola in place of the half-circle
Hyps: (a) none -/
theorem comp_parabH_fullF_not_convex (x : ℝ) : ¬ Convex ℝ (comp parabH fullF x) := by
  intro h
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ comp parabH fullF x := ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [parabH]⟩
  have h1 : ((1 : ℝ), (1 : ℝ)) ∈ comp parabH fullF x := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [parabH]⟩
  have hm := h h0 h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  obtain ⟨y, -, hy⟩ := hm
  simp only [parabH, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [← hy1] at hy2
  norm_num at hy2

/-! ### Target 7-composition, 011 (i): fixed points of total closed convex-graph relations -/

/-- **011 (i)**: a total relation `R` on a nonempty compact convex `K` (finite-dimensional), with
values in `K` and a closed convex graph over `K`, has some `x ∈ K` with `x ∈ R x`: its slices are
nonempty and convex (`convex_apply_of_convex_graphOn`), so `kakutani_findim` applies.
Source: [[fixpoint-lit-inventory]] 011 (i)
Kind: C
Fidelity: exact
Hyps: (a) all: Kakutani is `kakutani_findim` -/
theorem exists_mem_self_of_convex_closed_graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKn : K.Nonempty)
    (R : E → Set E) (hRK : ∀ x ∈ K, R x ⊆ K) (hRt : ∀ x ∈ K, (R x).Nonempty)
    (hconv : Convex ℝ (graphOn K R)) (hcl : IsClosed (graphOn K R)) : ∃ x ∈ K, x ∈ R x :=
  kakutani_findim hK hKc hKn R hRK hRt (fun _ hx => convex_apply_of_convex_graphOn hconv hx) hcl

/-! ### 011 (ii): cyclic compositions -/

section Cyclic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} [NeZero n]

/-- **The cyclic product correspondence** of `f : Fin n → E → Set E`:
`cyclicCorr f x = {y | ∀ i, y (i + 1) ∈ f i (x i)}` (indices mod `n`; Sam's "look at `∏ fᵢ`").
Source: [[fixpoint-lit-inventory]] 011 (ii) (discord-notes: "`fᵢ : Xᵢ → Xᵢ₊₁`, look at `∏ fᵢ`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def cyclicCorr (f : Fin n → E → Set E) (x : Fin n → E) : Set (Fin n → E) :=
  {y | ∀ i, y (i + 1) ∈ f i (x i)}

/-- **011 (ii): a cycle of Kakutani correspondences has a cyclic point.** For `f i : K i ⇉ K (i+1)`
(indices mod `n`) with nonempty convex values and closed graphs over nonempty compact convex `K i`,
there is `x ∈ ∏ K i` with `x (i + 1) ∈ f i (x i)` for all `i`: `kakutani_findim` on the product
`Fin n → E` for `cyclicCorr f`.
Source: [[fixpoint-lit-inventory]] 011 (ii)
Kind: C
Fidelity: exact
Hyps: (a) all: Kakutani is `kakutani_findim` -/
theorem exists_cyclic_point [FiniteDimensional ℝ E] (K : Fin n → Set E)
    (hKc : ∀ i, IsCompact (K i)) (hKv : ∀ i, Convex ℝ (K i)) (hKn : ∀ i, (K i).Nonempty)
    (f : Fin n → E → Set E) (hmaps : ∀ i, ∀ x ∈ K i, f i x ⊆ K (i + 1))
    (hne : ∀ i, ∀ x ∈ K i, (f i x).Nonempty) (hconv : ∀ i, ∀ x ∈ K i, Convex ℝ (f i x))
    (hgraph : ∀ i, HasClosedGraphOn (f i) (K i)) :
    ∃ x ∈ Set.univ.pi K, ∀ i, x (i + 1) ∈ f i (x i) := by
  have hKcl : ∀ i, IsClosed (K i) := fun i => (hKc i).isClosed
  refine kakutani_findim (isCompact_univ_pi hKc) (convex_pi fun i _ => hKv i)
    (Set.univ_pi_nonempty_iff.2 hKn) (cyclicCorr f) ?_ ?_ ?_ ?_
  · intro x hx y hy j _
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, (sub_add_cancel j 1).symm⟩
    exact hmaps i (x i) (hx i (mem_univ _)) (hy i)
  · intro x hx
    choose g hg using fun i => hne i (x i) (hx i (mem_univ _))
    refine ⟨fun j => g (j - 1), fun i => ?_⟩
    show g (i + 1 - 1) ∈ f i (x i)
    rw [add_sub_cancel_right]
    exact hg i
  · intro x hx y hy z hz a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply]
    exact hconv i (x i) (hx i (mem_univ _)) (hy i) (hz i) ha hb hab
  · unfold HasClosedGraphOn
    have : {q : (Fin n → E) × (Fin n → E) | q.1 ∈ Set.univ.pi K ∧ q.2 ∈ cyclicCorr f q.1} =
        {q : (Fin n → E) × (Fin n → E) | q.1 ∈ Set.univ.pi K} ∩
        ⋂ i, (fun q : (Fin n → E) × (Fin n → E) => (q.1 i, q.2 (i + 1))) ⁻¹'
          {p : E × E | p.1 ∈ K i ∧ p.2 ∈ f i p.1} := by
      ext ⟨x, y⟩
      simp only [cyclicCorr, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage]
      constructor
      · rintro ⟨hx, hy⟩; exact ⟨hx, fun i => ⟨hx i (mem_univ _), hy i⟩⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, fun i => (h i).2⟩
    rw [this]
    refine ((isClosed_set_pi fun i _ => hKcl i).preimage continuous_fst).inter
      (isClosed_iInter fun i => (hgraph i).preimage ?_)
    exact ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply (i + 1)).comp continuous_snd)

end Cyclic

/-- **Iterated composition** `iterComp f k = f (k−1) ∘ ⋯ ∘ f 0` of a sequence of correspondences on
one space: `iterComp f 0 x = {x}`, `iterComp f (k+1) x = comp (f k) (iterComp f k) x`.
Source: [[fixpoint-lit-inventory]] 011 (ii) ("`f_{n−1} ∘ ⋯ ∘ f₀`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def iterComp {E : Type*} (f : ℕ → E → Set E) : ℕ → E → Set E
  | 0 => fun x => {x}
  | k + 1 => fun x => {z | ∃ y ∈ iterComp f k x, z ∈ f k y}

open Fin.NatCast in
/-- **011 (ii), the consequence**: a cyclic point `x` of `f : Fin n → E → Set E` gives a fixed point of
the composite `f (n−1) ∘ ⋯ ∘ f 0`: `x 0 ∈ iterComp (fun k => f k) n (x 0)` — although the composite need
not be Kakutani (`comp_parabH_fullF_not_convex`).
Source: [[fixpoint-lit-inventory]] 011 (ii) (Scott: "I wonder if arbitrary compositions of kakutani
maps have fixed points")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem mem_iterComp_of_cyclic {E : Type*} {n : ℕ} [NeZero n] (f : Fin n → E → Set E)
    (x : Fin n → E) (hx : ∀ i, x (i + 1) ∈ f i (x i)) :
    x 0 ∈ iterComp (fun k => f (k : Fin n)) n (x 0) := by
  have key : ∀ k : ℕ, x (k : Fin n) ∈ iterComp (fun k => f (k : Fin n)) k (x 0) := by
    intro k
    induction k with
    | zero => simp [iterComp]
    | succ k ih =>
      refine ⟨x (k : Fin n), ih, ?_⟩
      rw [Nat.cast_succ]
      exact hx _
  have := key n
  rwa [Fin.natCast_self] at this

/-! ### N+ witness of 011 (ii): a two-cycle on `[0, 1]` -/

/-- **The two-cycle** `f 0 x = {1 − x}`, `f 1 y = {y}` on `[0, 1]` (`f 0 : K 0 ⇉ K 1`, `f 1 : K 1 ⇉ K 0`
with both `K i = [0, 1]`). The composite `f 1 ∘ f 0` is `x ↦ {1 − x}`.
Source: mandate target 7 (011 (ii)); audit round 1 (adversarial 3.4)
Kind: D
Fidelity: exact
Hyps: n/a -/
def twoCycle : Fin 2 → ℝ → Set ℝ := ![fun x => {1 - x}, fun y => {y}]

/-- `twoCycle` inhabits the hypothesis package of `exists_cyclic_point` on `K i = [0, 1]`: values in
`[0, 1]`, nonempty, convex, closed graphs.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem twoCycle_kakutani :
    (∀ i, ∀ x ∈ Icc (0 : ℝ) 1, twoCycle i x ⊆ Icc 0 1) ∧
    (∀ i, ∀ x ∈ Icc (0 : ℝ) 1, (twoCycle i x).Nonempty) ∧
    (∀ i, ∀ x ∈ Icc (0 : ℝ) 1, Convex ℝ (twoCycle i x)) ∧
    (∀ i, HasClosedGraphOn (twoCycle i) (Icc (0 : ℝ) 1)) := by
  refine ⟨fun i x hx => ?_, fun i x _ => ?_, fun i x _ => ?_, fun i => ?_⟩
  · fin_cases i
    · intro y hy
      simp only [twoCycle] at hy
      rw [hy]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · intro y hy
      simp only [twoCycle] at hy
      rw [hy]; exact hx
  · fin_cases i <;> exact ⟨_, rfl⟩
  · fin_cases i <;> exact convex_singleton _
  · unfold HasClosedGraphOn
    fin_cases i
    · show IsClosed {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ twoCycle 0 p.1}
      have : {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ twoCycle 0 p.1} =
          {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1} ∩ {p | p.2 = 1 - p.1} := by
        ext p; simp [twoCycle]
      rw [this]
      exact (isClosed_Icc.preimage continuous_fst).inter
        (isClosed_eq continuous_snd (continuous_const.sub continuous_fst))
    · show IsClosed {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ twoCycle 1 p.1}
      have : {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ twoCycle 1 p.1} =
          {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1} ∩ {p | p.2 = p.1} := by
        ext p; simp [twoCycle]
      rw [this]
      exact (isClosed_Icc.preimage continuous_fst).inter (isClosed_eq continuous_snd continuous_fst)

/-- **N+ witness of 011 (ii)**: the cyclic points of `twoCycle` are exactly `![1/2, 1/2]`
(`x 1 = 1 − x 0` and `x 0 = x 1`). Not degenerate: the maps are single-valued but the cycle is
genuine — neither map is a constant correspondence, and the cyclic point is unique.
Source: mandate target 7 (011 (ii)); audit round 1 (adversarial 3.4)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cyclic_twoCycle_iff (x : Fin 2 → ℝ) :
    (∀ i, x (i + 1) ∈ twoCycle i (x i)) ↔ x = ![1 / 2, 1 / 2] := by
  constructor
  · intro h
    have h0 : x 1 = 1 - x 0 := by simpa [twoCycle] using h 0
    have h1 : x 0 = x 1 := by simpa [twoCycle] using h 1
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl i
    fin_cases i <;> simp [twoCycle]
    norm_num

/-- **011 (ii) instantiated**: `exists_cyclic_point` on the two-cycle (its full hypothesis package is
`twoCycle_kakutani`); by `cyclic_twoCycle_iff` the point it produces is `![1/2, 1/2]`.
Source: [[fixpoint-lit-inventory]] 011 (ii)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem exists_cyclic_point_twoCycle :
    ∃ x ∈ Set.univ.pi (fun _ : Fin 2 => Icc (0 : ℝ) 1), ∀ i, x (i + 1) ∈ twoCycle i (x i) :=
  exists_cyclic_point (fun _ => Icc 0 1) (fun _ => isCompact_Icc) (fun _ => convex_Icc 0 1)
    (fun _ => nonempty_Icc.2 zero_le_one) twoCycle twoCycle_kakutani.1 twoCycle_kakutani.2.1
    twoCycle_kakutani.2.2.1 twoCycle_kakutani.2.2.2

open Fin.NatCast in
/-- **The composite's fixed point, instantiated**: `1/2 ∈ (f 1 ∘ f 0) (1/2)` for the two-cycle, by
`mem_iterComp_of_cyclic` at the cyclic point `![1/2, 1/2]`.
Source: [[fixpoint-lit-inventory]] 011 (ii)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem half_mem_iterComp_twoCycle :
    (1 / 2 : ℝ) ∈ iterComp (fun k => twoCycle (k : Fin 2)) 2 (1 / 2) := by
  have := mem_iterComp_of_cyclic twoCycle ![1 / 2, 1 / 2] ((cyclic_twoCycle_iff _).2 rfl)
  simpa using this

end Cleanroom.Fixpoint.FixOraclesCorresp
