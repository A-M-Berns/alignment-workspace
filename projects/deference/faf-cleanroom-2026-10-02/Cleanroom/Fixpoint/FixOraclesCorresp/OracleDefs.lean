import Cleanroom.Found.FixKakutani
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Constructions.SumProd

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.OracleDefs`: reflective oracles, the finite abstract core

Definitions of record for Part B (mandate target 9; FTC 2015 §2). The paper's oracle answers queries
`(M, p)` about probabilistic oracle *machines* `M`; FAF has no oracle-relative machine model, so the
carrier here is abstract: a finite query index set `I`, thresholds `p : I → ℝ`, an **evaluation map**
`ev : I → (I → ℝ) → ℝ` (query `i`'s output probability `P(Mᵢ^O() = 1)` as a function of the answer
vector `x`, the paper's `eval(Mᵢ)` as a function of `query`), and the cube `Set.univ.pi (fun _ => Icc 0 1)`
of answer vectors. Every Part B headline is `Fidelity: variant: abstract (evaluation maps in place of
machines)`.

* `Reflective ev p x`: the paper's two displayed conditions, per query — `p i < ev i x → x i = 1` and
  `ev i x < p i → x i = 0` (ties free). **Strictness is load-bearing**: with `≤`/`≥` the tie case
  forces `x i = 1 = 0` (`ReflectiveNonStrict`, shown unsatisfiable on the liar in `Liar.lean`).
* `signStep e p`: App. B's per-query condition, pointwise convexified: `{1}` if `p < e`, `{0}` if
  `e < p`, `Icc 0 1` at the tie.
* `oracleCorr ev p`: the product correspondence `x ↦ ∏ᵢ signStep (ev i x) (p i)` whose fixed points
  in the cube are exactly the reflective vectors (`mem_oracleCorr_self_iff`).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set

variable {I : Type*} [Fintype I]

/-- The cube `[0, 1]^I` of answer vectors.
Source: FTC 2015 §5 ("a vector `x ∈ [0,1]ⁿ`")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev cube (I : Type*) : Set (I → ℝ) := Set.univ.pi fun _ : I => Icc (0 : ℝ) 1

/-- **Reflectivity** of an answer vector `x` for evaluation maps `ev` at thresholds `p`: for every
query `i`, `p i < ev i x → x i = 1` and `ev i x < p i → x i = 0`. This is FTC 2015 §2's definition
("reflective on `R`") with `R = I`, `P(M^O() = 1) = ev i x` and `P(O(M, p) = 1) = x i`.
Source: FTC 2015 §2 (the two displayed conditions; Definition "reflective on `R`");
[[fixpoint-lit-2-inventory]] 001
Kind: D
Fidelity: variant: abstract (evaluation maps in place of machines)
Hyps: n/a -/
def Reflective (ev : I → (I → ℝ) → ℝ) (p : I → ℝ) (x : I → ℝ) : Prop :=
  ∀ i, (p i < ev i x → x i = 1) ∧ (ev i x < p i → x i = 0)

/-- The **non-strict** variant (`≤`/`≥` in place of `<`/`>`), recorded only to show that strictness
is load-bearing: at a tie it forces `x i = 1 ∧ x i = 0`. See `liar_no_nonStrict` in `Liar.lean`.
Source: mandate target 9, trap (a)
Kind: D
Fidelity: variant: deliberately wrong (a trap witness)
Hyps: n/a -/
def ReflectiveNonStrict (ev : I → (I → ℝ) → ℝ) (p : I → ℝ) (x : I → ℝ) : Prop :=
  ∀ i, (p i ≤ ev i x → x i = 1) ∧ (ev i x ≤ p i → x i = 0)

/-- **The per-query step, pointwise convexified** (FTC App. B's condition on `query'(M, p)`): `{1}` if
`p < e`, `{0}` if `e < p`, and `[0, 1]` at the tie.
Source: FTC 2015 App. B ("if `eval(M) > p` then `query'(M,p) = 1`; if `< p` then `0`");
[[fixpoint-lit-2-inventory]] 011 (`Φ_p`)
Kind: D
Fidelity: exact (per query)
Hyps: n/a -/
noncomputable def signStep (e p : ℝ) : Set ℝ :=
  if p < e then {1} else if e < p then {0} else Icc 0 1

/-- Membership in `signStep`: `y ∈ [0,1]`, and the two sign conditions.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_signStep_iff {e p y : ℝ} :
    y ∈ signStep e p ↔ y ∈ Icc (0 : ℝ) 1 ∧ (p < e → y = 1) ∧ (e < p → y = 0) := by
  unfold signStep
  split_ifs with h1 h2
  · simp only [mem_singleton_iff]
    constructor
    · rintro rfl; exact ⟨⟨zero_le_one, le_rfl⟩, fun _ => rfl, fun h => absurd h1 (lt_asymm h)⟩
    · exact fun h => h.2.1 h1
  · simp only [mem_singleton_iff]
    constructor
    · rintro rfl; exact ⟨⟨le_rfl, zero_le_one⟩, fun h => absurd h h1, fun _ => rfl⟩
    · exact fun h => h.2.2 h2
  · constructor
    · exact fun h => ⟨h, fun h' => absurd h' h1, fun h' => absurd h' h2⟩
    · exact fun h => h.1

/-- `signStep e p ⊆ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem signStep_subset_Icc (e p : ℝ) : signStep e p ⊆ Icc 0 1 := fun _ h =>
  (mem_signStep_iff.1 h).1

/-- `signStep e p` is nonempty (it contains `if p < e then 1 else 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem signStep_nonempty (e p : ℝ) : (signStep e p).Nonempty := by
  refine ⟨if p < e then 1 else 0, ?_⟩
  rw [mem_signStep_iff]
  split_ifs with h
  · exact ⟨⟨zero_le_one, le_rfl⟩, fun _ => rfl, fun h' => absurd h (lt_asymm h')⟩
  · exact ⟨⟨le_rfl, zero_le_one⟩, fun h' => absurd h' h, fun _ => rfl⟩

/-- `signStep e p` is convex.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem signStep_convex (e p : ℝ) : Convex ℝ (signStep e p) := by
  unfold signStep
  split_ifs
  · exact convex_singleton _
  · exact convex_singleton _
  · exact convex_Icc 0 1

/-- **The oracle correspondence**: `oracleCorr ev p x = {y | ∀ i, y i ∈ signStep (ev i x) (p i)}`,
the product over queries of the pointwise convexified steps (FTC App. B's `f`, restricted to the
`query` coordinates of a finite `R`).
Source: FTC 2015 App. B (the correspondence `f`); [[fixpoint-lit-2-inventory]] 010 (route (a):
"`x ↦ ∏ᵢ Φᵢ(x)`")
Kind: D
Fidelity: variant: abstract (evaluation maps in place of machines)
Hyps: n/a -/
def oracleCorr (ev : I → (I → ℝ) → ℝ) (p : I → ℝ) (x : I → ℝ) : Set (I → ℝ) :=
  {y | ∀ i, y i ∈ signStep (ev i x) (p i)}

omit [Fintype I] in
/-- `oracleCorr ev p x` is the product set `Set.univ.pi (fun i => signStep (ev i x) (p i))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem oracleCorr_eq_pi (ev : I → (I → ℝ) → ℝ) (p x : I → ℝ) :
    oracleCorr ev p x = Set.univ.pi fun i => signStep (ev i x) (p i) := by
  ext y; simp [oracleCorr]

omit [Fintype I] in
/-- **Fixed points of the oracle correspondence in the cube are exactly the reflective vectors.**
Source: FTC 2015 App. B ("fixed points `(query, eval) ∈ f(query, eval)` yield oracles `O'` of the
desired form"); mandate target 9
Kind: L
Fidelity: variant: abstract
Hyps: none -/
theorem mem_oracleCorr_self_iff {ev : I → (I → ℝ) → ℝ} {p x : I → ℝ} (hx : x ∈ cube I) :
    x ∈ oracleCorr ev p x ↔ Reflective ev p x := by
  constructor
  · intro h i
    exact (mem_signStep_iff.1 (h i)).2
  · intro h i
    exact mem_signStep_iff.2 ⟨hx i (mem_univ _), h i⟩

/-- **Closedness of a single sign-step graph**: for `e : α → ℝ` continuous on a closed `K`, the set
`{(x, y) | x ∈ K ∧ y ∈ signStep (e x) p}` is closed in `α × ℝ` (App. B's limit argument, in
closed-set form: `{p < e x → y = 1} = {e x ≤ p} ∪ {y = 1}`, and the tie case is `Icc` closed).
Source: FTC 2015 App. B (closed graph of `f`); [[fixpoint-lit-2-inventory]] 002
Kind: P
Fidelity: exact (per query)
Hyps: (a) none -/
theorem isClosed_signStep_graph {α : Type*} [TopologicalSpace α] {K : Set α} (hK : IsClosed K)
    {e : α → ℝ} (he : ContinuousOn e K) (p : ℝ) :
    IsClosed {q : α × ℝ | q.1 ∈ K ∧ q.2 ∈ signStep (e q.1) p} := by
  have hset : {q : α × ℝ | q.1 ∈ K ∧ q.2 ∈ signStep (e q.1) p} =
      ({q : α × ℝ | q.1 ∈ K} ∩ {q | q.2 ∈ Icc (0 : ℝ) 1}) ∩
      (({q : α × ℝ | q.1 ∈ K ∧ e q.1 ≤ p} ∪ {q | q.2 = 1}) ∩
        ({q : α × ℝ | q.1 ∈ K ∧ p ≤ e q.1} ∪ {q | q.2 = 0})) := by
    ext ⟨x, y⟩
    simp only [mem_setOf_eq, mem_signStep_iff, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨hx, hy, h1, h2⟩
      refine ⟨⟨hx, hy⟩, ?_, ?_⟩
      · by_cases h : p < e x
        · exact Or.inr (h1 h)
        · exact Or.inl ⟨hx, not_lt.1 h⟩
      · by_cases h : e x < p
        · exact Or.inr (h2 h)
        · exact Or.inl ⟨hx, not_lt.1 h⟩
    · rintro ⟨⟨hx, hy⟩, h1, h2⟩
      refine ⟨hx, hy, fun h => ?_, fun h => ?_⟩
      · rcases h1 with ⟨-, h1⟩ | h1
        · exact absurd h (not_lt.2 h1)
        · exact h1
      · rcases h2 with ⟨-, h2⟩ | h2
        · exact absurd h (not_lt.2 h2)
        · exact h2
  rw [hset]
  have hK' : IsClosed {q : α × ℝ | q.1 ∈ K} := hK.preimage continuous_fst
  have hle : IsClosed {q : α × ℝ | q.1 ∈ K ∧ e q.1 ≤ p} := by
    have := (he.comp continuous_fst.continuousOn (fun q hq => hq) :
      ContinuousOn (fun q : α × ℝ => e q.1) {q | q.1 ∈ K}).preimage_isClosed_of_isClosed hK'
      (isClosed_Iic (a := p))
    convert this using 1
    ext q; simp
  have hge : IsClosed {q : α × ℝ | q.1 ∈ K ∧ p ≤ e q.1} := by
    have := (he.comp continuous_fst.continuousOn (fun q hq => hq) :
      ContinuousOn (fun q : α × ℝ => e q.1) {q | q.1 ∈ K}).preimage_isClosed_of_isClosed hK'
      (isClosed_Ici (a := p))
    convert this using 1
    ext q; simp
  refine (hK'.inter (isClosed_Icc.preimage continuous_snd)).inter
    ((hle.union (isClosed_eq continuous_snd continuous_const)).inter
      (hge.union (isClosed_eq continuous_snd continuous_const)))

end Cleanroom.Fixpoint.FixOraclesCorresp
