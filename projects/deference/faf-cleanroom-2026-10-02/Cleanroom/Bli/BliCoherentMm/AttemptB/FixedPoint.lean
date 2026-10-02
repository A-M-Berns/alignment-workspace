import Cleanroom.Bli.BliOverlay
import Cleanroom.Bli.BliFinite
import LogicalInduction.Construction.Brouwer
import Mathlib.Analysis.Convex.StdSimplex

/-!
# `bli-coherent-mm` (attempt B) · FixedPoint: the coherent fixed point (T1, M1)

Soto's Theorem 2 (PDF 05, "Fixed point lemma"), proved. Two layers:

* **The abstract lemma** `coherent_fixed_point_abstract` (the mathematics): for a nonempty
  finite type `ι` and a continuous `G : stdSimplex ℝ ι → (ι → ℝ)` with the zero-expected-value
  identity `∑ u, p u * G p u = 0` on the simplex, there is `p* ∈ stdSimplex` with `G p* ≤ 0`.
  **Angle B's map**: clip and normalise, `g p u := max 0 (p u + G p u) / ∑ u', max 0 (p u' + G p u')`
  — the simplex form of FAF's `priceAdjustment` (`max 0 (min 1 (x + shares))`). The normaliser
  is **positive** on the simplex (`∑ p u · (p u + G p u) = ∑ p u² > 0` by the identity, and each
  summand is at most its clipped value), **not** `≥ 1` as the mandate's angle-B sketch says —
  that claim is false (findings), and positivity is all the argument needs. At a fixed point with
  normaliser `Z`: on the support `G p u = p u (Z − 1)`, off it `G p u ≤ 0`; the identity gives
  `(Z − 1) ∑ p u² = 0`, so `Z = 1` and `G p ≤ 0` everywhere. Brouwer is FAF's `stdSimplex_hasFPP`
  (Sperner), grade (a), transported from `Fin (card ι)` to `ι` by `Fintype.equivFin`.
* **The headline** `coherent_fixed_point` over FAF's objects: for a day-`n` strategy `T`, a past,
  a stage `D` and an atom bound `B`, a real probability on `FiniteWorld B` **supported on the
  `D`-consistent worlds** whose marginal prices make `T`'s value `≤ 0` in every `D`-consistent
  finite world, and in every `PCWorld` consistent with `D`. The identity for the instance is
  *proved* (`sum_worldValue_eq_zero`), continuity is derived from `EF.continuous_denote`, and the
  simplex is nonempty by `hW`.

Sources: [[bli-coherent-mm-mandate]] T1, §Attempt angles (B); Soto PDF 05 Thm 2 and fn. 1
(bli-soto-a-044); [[bli-program]] §3.3, §4 row M1.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay
  Cleanroom.Bli.BliFinite Finset

/-! ## The abstract lemma: clip-and-normalise on the standard simplex -/

section Abstract

variable {ι : Type} [Fintype ι]

/-- The normaliser of the clip-and-normalise map: `∑ u, max 0 (p u + G p u)`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (B)
Kind: D
Fidelity: n/a -/
noncomputable def clipNorm (G : (ι → ℝ) → ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ u, max 0 (p u + G p u)

/-- **Angle B's map**: `g p u := max 0 (p u + G p u) / clipNorm G p` — FAF's clipped price
adjustment carried to the simplex and renormalised.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (B); FAF `priceAdjustment`
Kind: D
Fidelity: n/a -/
noncomputable def clipMap (G : (ι → ℝ) → ι → ℝ) (p : ι → ℝ) : ι → ℝ :=
  fun u => max 0 (p u + G p u) / clipNorm G p

/-- On the simplex (nonempty index), `∑ p u² > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_sq_pos_of_mem_stdSimplex [Nonempty ι] {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    0 < ∑ u, p u * p u := by
  by_contra h
  have h0 : ∑ u, p u * p u = 0 :=
    le_antisymm (not_lt.mp h) (sum_nonneg fun u _ => mul_self_nonneg (p u))
  rw [sum_eq_zero_iff_of_nonneg (fun u _ => mul_self_nonneg (p u))] at h0
  have h1 : ∑ u, p u = 0 := sum_eq_zero fun u hu => mul_self_eq_zero.mp (h0 u hu)
  rw [hp.2] at h1
  exact one_ne_zero h1

/-- The normaliser is **positive** on the simplex under the identity: `clipNorm G p ≥ ∑ p u²`.
(It is *not* `≥ 1` in general — the mandate's sketch overstates; see the findings.)
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clipNorm_pos [Nonempty ι] (G : (ι → ℝ) → ι → ℝ)
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    0 < clipNorm G p := by
  have hsq := sum_sq_pos_of_mem_stdSimplex hp
  have hle : ∑ u, p u * p u ≤ clipNorm G p := by
    have hsplit : ∑ u, p u * (p u + G p u) = ∑ u, p u * p u + ∑ u, p u * G p u := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun u _ => by ring
    have heq : ∑ u, p u * p u = ∑ u, p u * (p u + G p u) := by
      rw [hsplit, hid p hp, add_zero]
    rw [heq]
    unfold clipNorm
    apply sum_le_sum
    intro u _
    have h0 : 0 ≤ p u := hp.1 u
    have h1 : p u ≤ 1 := (mem_Icc_of_mem_stdSimplex hp u).2
    calc p u * (p u + G p u) ≤ p u * max 0 (p u + G p u) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) h0
      _ ≤ 1 * max 0 (p u + G p u) := mul_le_mul_of_nonneg_right h1 (le_max_left _ _)
      _ = max 0 (p u + G p u) := one_mul _
  exact lt_of_lt_of_le hsq hle

/-- The clip-and-normalise map is continuous on the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clipMap_continuousOn [Nonempty ι] (G : (ι → ℝ) → ι → ℝ)
    (hG : ContinuousOn G (stdSimplex ℝ ι))
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) :
    ContinuousOn (clipMap G) (stdSimplex ℝ ι) := by
  have hterm : ∀ u, ContinuousOn (fun p : ι → ℝ => max 0 (p u + G p u)) (stdSimplex ℝ ι) :=
    fun u => ContinuousOn.sup continuousOn_const
      ((continuous_apply u).continuousOn.add ((continuous_apply u).comp_continuousOn hG))
  have hZ : ContinuousOn (clipNorm G) (stdSimplex ℝ ι) := by
    unfold clipNorm
    exact continuousOn_finsetSum _ fun u _ => hterm u
  rw [continuousOn_pi]
  intro u
  exact (hterm u).div hZ fun p hp => (clipNorm_pos G hid hp).ne'

/-- The clip-and-normalise map sends the simplex to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clipMap_mapsTo [Nonempty ι] (G : (ι → ℝ) → ι → ℝ)
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) :
    Set.MapsTo (clipMap G) (stdSimplex ℝ ι) (stdSimplex ℝ ι) := by
  intro p hp
  have hZ := clipNorm_pos G hid hp
  refine ⟨fun u => div_nonneg (le_max_left _ _) hZ.le, ?_⟩
  show ∑ u, max 0 (p u + G p u) / clipNorm G p = 1
  rw [← sum_div]
  exact div_self hZ.ne'

/-- At a fixed point of the clip-and-normalise map on the simplex, `G p ≤ 0` everywhere: on the
support `G p u = p u (Z − 1)` with `Z` the normaliser, off it `G p u ≤ 0`; the identity forces
`Z = 1`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (B)
Kind: P
Fidelity: n/a -/
lemma clipMap_fixed_le [Nonempty ι] (G : (ι → ℝ) → ι → ℝ)
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι)
    (hfix : clipMap G p = p) : ∀ u, G p u ≤ 0 := by
  have hZ := clipNorm_pos G hid hp
  have hcoord : ∀ u, p u * clipNorm G p = max 0 (p u + G p u) := by
    intro u
    have h := congrFun hfix u
    unfold clipMap at h
    rw [div_eq_iff hZ.ne'] at h
    exact h.symm
  have hsupp : ∀ u, 0 < p u → G p u = p u * (clipNorm G p - 1) := by
    intro u hu
    have h := hcoord u
    have hpos : 0 < max 0 (p u + G p u) := h ▸ mul_pos hu hZ
    have hx : 0 < p u + G p u := by
      rcases lt_max_iff.mp hpos with h0 | h0
      · exact absurd h0 (lt_irrefl _)
      · exact h0
    rw [max_eq_right hx.le] at h
    linarith
  have hoff : ∀ u, p u = 0 → G p u ≤ 0 := by
    intro u hu
    have h := hcoord u
    rw [hu, zero_mul, zero_add] at h
    exact max_eq_left_iff.mp h.symm
  have hZ1 : clipNorm G p = 1 := by
    have h1 : ∑ u, p u * G p u = (clipNorm G p - 1) * ∑ u, p u * p u := by
      rw [mul_sum]
      apply sum_congr rfl
      intro u _
      rcases (hp.1 u).lt_or_eq with hu | hu
      · rw [hsupp u hu]; ring
      · rw [← hu]; ring
    rw [hid p hp] at h1
    have hsq := sum_sq_pos_of_mem_stdSimplex hp
    rcases mul_eq_zero.mp h1.symm with h | h
    · linarith
    · exact absurd h hsq.ne'
  intro u
  rcases (hp.1 u).lt_or_eq with hu | hu
  · rw [hsupp u hu, hZ1]; simp
  · exact hoff u hu.symm

/-- **The abstract coherent fixed point on `Fin d`** (Brouwer = FAF's `stdSimplex_hasFPP`).
Source: [[bli-coherent-mm-mandate]] T1 (abstract lemma); Soto PDF 05 Thm 2
Kind: P
Fidelity: exact
Hyps: (a) `hd`, `hG`, `hid` — the abstract lemma's own hypotheses; the headline discharges all -/
theorem coherent_fixed_point_abstract_fin {d : ℕ} (hd : 0 < d) (G : (Fin d → ℝ) → Fin d → ℝ)
    (hG : ContinuousOn G (stdSimplex ℝ (Fin d)))
    (hid : ∀ p ∈ stdSimplex ℝ (Fin d), ∑ u, p u * G p u = 0) :
    ∃ p ∈ stdSimplex ℝ (Fin d), ∀ u, G p u ≤ 0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨p, hp, hfix⟩ := BrouwerProof.fixed_of_hasFPP (BrouwerProof.stdSimplex_hasFPP hd)
    (clipMap_continuousOn G hG hid) (clipMap_mapsTo G hid)
  exact ⟨p, hp, clipMap_fixed_le G hid hp hfix⟩

/-- **The abstract coherent fixed point (Soto's Theorem 2, "necessary and sufficient" form).**
For a nonempty finite `ι` and a continuous `G : stdSimplex ℝ ι → (ι → ℝ)` with
`∑ u, p u * G p u = 0` on the simplex, some `p* ∈ stdSimplex ℝ ι` has `G p* ≤ 0` in every
coordinate. Proved by angle B's clip-and-normalise map and FAF's Brouwer (`stdSimplex_hasFPP`),
transported from `Fin (card ι)`.
Source: [[bli-coherent-mm-mandate]] T1 (abstract lemma); Soto PDF 05 Thm 2 (bli-soto-a-044)
Kind: P
Fidelity: exact
Hyps: (a) `hG`, `hid` — the lemma's own; the headline `coherent_fixed_point` discharges both -/
theorem coherent_fixed_point_abstract [Nonempty ι] (G : (ι → ℝ) → ι → ℝ)
    (hG : ContinuousOn G (stdSimplex ℝ ι))
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) :
    ∃ p ∈ stdSimplex ℝ ι, ∀ u, G p u ≤ 0 := by
  let e := Fintype.equivFin ι
  have hd : 0 < Fintype.card ι := Fintype.card_pos
  let ofFin : (Fin (Fintype.card ι) → ℝ) → ι → ℝ := fun x u => x (e u)
  have hofFin : Continuous ofFin := continuous_pi fun u => continuous_apply (e u)
  have hmem : ∀ x : Fin (Fintype.card ι) → ℝ,
      x ∈ stdSimplex ℝ (Fin (Fintype.card ι)) ↔ ofFin x ∈ stdSimplex ℝ ι := by
    intro x
    simp only [stdSimplex, Set.mem_setOf_eq, ofFin]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨fun u => h0 (e u), by rw [e.sum_comp (fun i => x i)]; exact h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨fun i => by simpa using h0 (e.symm i), ?_⟩
      rw [← e.sum_comp (fun i => x i)]
      exact h1
  let G' : (Fin (Fintype.card ι) → ℝ) → Fin (Fintype.card ι) → ℝ :=
    fun x i => G (ofFin x) (e.symm i)
  have hG' : ContinuousOn G' (stdSimplex ℝ (Fin (Fintype.card ι))) := by
    rw [continuousOn_pi]
    intro i
    exact ((continuous_apply (e.symm i)).comp_continuousOn hG).comp hofFin.continuousOn
      fun x hx => (hmem x).mp hx
  have hid' : ∀ x ∈ stdSimplex ℝ (Fin (Fintype.card ι)), ∑ i, x i * G' x i = 0 := by
    intro x hx
    have h := hid (ofFin x) ((hmem x).mp hx)
    rw [← e.sum_comp (fun i => x i * G' x i)]
    simpa [G', ofFin] using h
  obtain ⟨x, hx, hle⟩ := coherent_fixed_point_abstract_fin hd G' hG' hid'
  refine ⟨ofFin x, (hmem x).mp hx, fun u => ?_⟩
  simpa [G', ofFin] using hle (e u)

end Abstract

/-! ## The `D`-consistent finite worlds (D1) and real world measures (D2, real form) -/

/-- Consistency of a finite world with a finite stage is decidable (FAF's Boolean `eval`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecidableConsistentWith {B : ℕ} (u : FiniteWorld B) (D : Finset Sentence) :
    Decidable ((worldOf u).ConsistentWith D) :=
  decidable_of_iff (∀ φ ∈ D, BoolPCWorld.eval u.toBoolPCWorld φ = true)
    (by simp only [PCWorld.ConsistentWith, BoolPCWorld.eval_eq_true_iff_holds])

/-- **D1. The `D`-consistent finite worlds** `W_D B`: the finite worlds on `B` atoms whose
`PCWorld` (atoms `≥ B` read `false`) makes every sentence of `D` true. Meaningful only with an
atom bound covering `D` (else atoms beyond `B` are silently decided false).
Source: [[bli-coherent-mm-mandate]] D1
Kind: D
Fidelity: exact -/
def worldsOf (D : Finset Sentence) (B : ℕ) : Finset (FiniteWorld B) :=
  Finset.univ.filter fun u => (worldOf u).ConsistentWith D

/-- Membership in `W_D B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mem_worldsOf {D : Finset Sentence} {B : ℕ} {u : FiniteWorld B} :
    u ∈ worldsOf D B ↔ (worldOf u).ConsistentWith D := by
  simp [worldsOf]

/-- **D2 (real form). A real world measure on `W_D B`**: nonnegative, total mass `1`, supported
on the `D`-consistent worlds.
Source: [[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact -/
def IsRealWorldMeasure (D : Finset Sentence) (B : ℕ) (p : FiniteWorld B → ℝ) : Prop :=
  (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧ ∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D

/-- The real price table of a real weight vector: `priceOf p φ := ∑ u, p u * payout_u φ`.
Source: [[bli-coherent-mm-mandate]] D2 (`π`, real form)
Kind: D
Fidelity: exact -/
noncomputable def priceOf {B : ℕ} (p : FiniteWorld B → ℝ) (φ : Sentence) : ℝ :=
  ∑ u, p u * (worldOf u).payout φ

/-- The day-`n` history whose day `n` is the price table of `p` and whose days `< n` are `past`.
Source: [[bli-coherent-mm-mandate]] T1 (`V_p`)
Kind: D
Fidelity: exact -/
noncomputable def fixedHistory (past : List RationalBeliefState) (n : ℕ) {B : ℕ}
    (p : FiniteWorld B → ℝ) : History :=
  Function.update (beliefHistory past) n (priceOf p)

/-- The value of `T` on the history of `p`, assessed by the finite world `u`.
Source: [[bli-coherent-mm-mandate]] T1 (the map `G`)
Kind: D
Fidelity: exact -/
noncomputable def worldValue {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    {B : ℕ} (p : FiniteWorld B → ℝ) (u : FiniteWorld B) : ℝ :=
  T.value (fixedHistory past n p) (worldOf u).payout

/-! ## Continuity (from `EF.continuous_denote`) and the identity (proved) -/

/-- Each price is continuous in the weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma continuous_priceOf {B : ℕ} (φ : Sentence) :
    Continuous (fun p : FiniteWorld B → ℝ => priceOf p φ) := by
  unfold priceOf
  exact continuous_finsetSum _ fun u _ => (continuous_apply u).mul continuous_const

/-- The history of `p` is continuous in `p` (product topology on `History`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma continuous_fixedHistory (past : List RationalBeliefState) (n : ℕ) {B : ℕ} :
    Continuous (fun p : FiniteWorld B → ℝ => fixedHistory past n p) := by
  unfold fixedHistory
  apply continuous_pi
  intro k
  apply continuous_pi
  intro φ
  by_cases hk : k = n
  · subst hk
    simp only [Function.update_self]
    exact continuous_priceOf φ
  · simp only [Function.update_of_ne hk]
    exact continuous_const

/-- A trade list's value is continuous in the history (`EF.continuous_denote` termwise).
Source: none: infrastructure (the pattern of FAF's `continuous_strategyWorldValue`)
Kind: L
Fidelity: n/a -/
lemma continuous_tradeList_value (l : List (EF × Sentence)) (n : ℕ) (w : Sentence → ℝ) :
    Continuous (fun V : History => (l.map (fun p => p.1.denote V * (w p.2 - V n p.2))).sum) := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact continuous_const
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ((EF.continuous_denote p.1).mul
        (continuous_const.sub ((continuous_apply p.2).comp (continuous_apply n)))).add ih

/-- `p ↦ T.value (V_p) (payout of u)` is continuous.
Source: [[bli-coherent-mm-mandate]] T1 ("continuity from `EF.continuous_denote`")
Kind: L
Fidelity: n/a -/
lemma continuous_worldValue {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) {B : ℕ}
    (u : FiniteWorld B) : Continuous (fun p : FiniteWorld B → ℝ => worldValue T past p u) := by
  unfold worldValue Strategy.value
  exact (continuous_tradeList_value T.trades n _).comp (continuous_fixedHistory past n)

/-- The one-sentence accounting identity: `∑ u, p u * (a * (w u − c)) = a * (∑ p w − (∑ p) c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_mul_shares_sub {ι : Type} [Fintype ι] (p w : ι → ℝ) (a c : ℝ) :
    ∑ u, p u * (a * (w u - c)) = a * ∑ u, p u * w u - (a * c) * ∑ u, p u := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun u _ => by ring

/-- **The zero-expected-value identity, proved for the instance**: a weight vector of total mass
`1` assigns zero expected value to any day-`n` strategy priced at its own marginal,
`∑ u, p u * T.value (V_p) (payout_u) = 0`, because `∑ u, p u * payout_u φ = V_p n φ`.
Source: [[bli-coherent-mm-mandate]] T1 ("the identity … is proved, not assumed")
Kind: P
Fidelity: exact
Hyps: (a) `hp1 : ∑ u, p u = 1` — total mass, the only thing used -/
lemma sum_worldValue_eq_zero {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) {B : ℕ}
    (p : FiniteWorld B → ℝ) (hp1 : ∑ u, p u = 1) :
    ∑ u, p u * worldValue T past p u = 0 := by
  unfold worldValue
  simp_rw [Strategy.value_eq_sum_support, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro φ _
  have hV : fixedHistory past n p n φ = ∑ u, p u * (worldOf u).payout φ := by
    simp [fixedHistory, priceOf]
  rw [hV, sum_mul_shares_sub, hp1]
  ring

/-! ## The headline: the coherent fixed point over FAF's objects -/

/-- Zero-extension of weights on the `D`-consistent worlds to all finite worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def extWeights (D : Finset Sentence) (B : ℕ) (q : ↥(worldsOf D B) → ℝ) :
    FiniteWorld B → ℝ :=
  fun u => if h : u ∈ worldsOf D B then q ⟨u, h⟩ else 0

/-- Zero-extension is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma continuous_extWeights (D : Finset Sentence) (B : ℕ) : Continuous (extWeights D B) := by
  apply continuous_pi
  intro u
  by_cases h : u ∈ worldsOf D B
  · simp only [extWeights, dif_pos h]
    exact continuous_apply _
  · simp only [extWeights, dif_neg h]
    exact continuous_const

/-- A sum over all finite worlds of a function of the extension is the sum over `W_D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_extWeights_mul (D : Finset Sentence) (B : ℕ) (q : ↥(worldsOf D B) → ℝ)
    (f : FiniteWorld B → ℝ) :
    ∑ u, extWeights D B q u * f u = ∑ u : ↥(worldsOf D B), q u * f u := by
  rw [← sum_subset (subset_univ (worldsOf D B)) (fun u _ hu => by
    simp [extWeights, hu])]
  rw [← sum_coe_sort (worldsOf D B)]
  apply sum_congr rfl
  intro u _
  simp [extWeights, u.2]

/-- The extension has the mass of `q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_extWeights (D : Finset Sentence) (B : ℕ) (q : ↥(worldsOf D B) → ℝ) :
    ∑ u, extWeights D B q u = ∑ u : ↥(worldsOf D B), q u := by
  have h := sum_extWeights_mul D B q (fun _ => 1)
  simpa using h

/-- The payout of the restriction of a `PCWorld` agrees with the world's payout within the atom
bound.
Source: FAF `eval_toBoolPCWorld_restrict` (through bli-finite's `holds_worldOf_restrict`)
Kind: L
Fidelity: n/a -/
lemma payout_worldOf_restrict (v : PCWorld) {B : ℕ} {φ : Sentence} (hφ : atomBound φ ≤ B) :
    (worldOf (FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B)).payout φ = v.payout φ := by
  by_cases h : v.Holds φ
  · have h' := (holds_worldOf_restrict v hφ).mpr h
    simp [PCWorld.payout, h, h']
  · have h' : ¬ (worldOf (FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B)).Holds φ :=
      fun hc => h ((holds_worldOf_restrict v hφ).mp hc)
    simp [PCWorld.payout, h, h']

/-- The restriction of a `D`-consistent `PCWorld` is a `D`-consistent finite world, within the
atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_mem_worldsOf {D : Finset Sentence} {B : ℕ} (hBD : ∀ φ ∈ D, atomBound φ ≤ B)
    {v : PCWorld} (hv : v.ConsistentWith D) :
    FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B ∈ worldsOf D B := by
  rw [mem_worldsOf]
  intro φ hφ
  rw [holds_worldOf_restrict v (hBD φ hφ)]
  exact hv φ hφ

/-- A strategy's value in a `PCWorld` equals its value in the world's restriction, provided the
atom bound covers every traded sentence.
Source: FAF `Strategy.value_eq_of_world_eqOn_support`
Kind: L
Fidelity: n/a -/
lemma value_restrict_eq {n : ℕ} (T : Strategy n) (V : History) {B : ℕ}
    (hB : ∀ φ ∈ T.support, atomBound φ ≤ B) (v : PCWorld) :
    T.value V (worldOf (FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B)).payout =
      T.value V v.payout :=
  T.value_eq_of_world_eqOn_support V _ _ fun φ hφ => payout_worldOf_restrict v (hB φ hφ)

/-- Traded sentences are within an atom bound covering the mentioned set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomBound_support_le {n : ℕ} {T : Strategy n} {D : Finset Sentence} {B : ℕ}
    (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B) :
    ∀ φ ∈ T.support, atomBound φ ≤ B :=
  fun φ hφ => hB φ (Finset.mem_union_left _ (support_subset_mentionedSet T hφ))

/-- **T1 (headline, M1). The coherent fixed point over FAF's objects** (Soto's Theorem 2 for
FAF's `Strategy n`, `PCWorld.payout`, `FiniteWorld B`). For a day-`n` strategy `T`, a past, a
stage `D` and an atom bound `B` covering `mentionedSet T ∪ D`, if some finite world is
consistent with `D` then there is a real world measure `p` on `W_D B` (nonnegative, mass `1`,
supported on `D`-consistent worlds) such that, with
`V_p := Function.update (beliefHistory past) n (fun φ => ∑ u, p u * (worldOf u).payout φ)`,
`T.value V_p (worldOf u).payout ≤ 0` for every `u ∈ W_D B`, and
`T.value V_p v.payout ≤ 0` for every `PCWorld` `v` consistent with `D`. **Over `D`-consistent
worlds only** — not over all Boolean tables on the support (T4 shows that is false for coherent
`p`). Proved from `coherent_fixed_point_abstract` on `ι = ↥(W_D B)`; the identity is
`sum_worldValue_eq_zero`, continuity is `continuous_worldValue`, nonemptiness is `hW`.
Source: [[bli-coherent-mm-mandate]] T1; Soto PDF 05 Thm 2 (bli-soto-a-044); [[bli-program]] §4 M1
Kind: P
Fidelity: exact (Soto's statement, over FAF's objects, relative to a stage `D`)
Hyps: (a) `hB` (the atom bound; discharged by computation in witnesses and by `B n` in the
recursion), (a) `hW` (a `D`-consistent world exists; from `paperDP_hworld` in the witness) — no
(b), no (c) -/
theorem coherent_fixed_point {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, IsRealWorldMeasure D B p ∧
      (∀ u ∈ worldsOf D B, T.value (Function.update (beliefHistory past) n
        (fun φ => ∑ u, p u * (worldOf u).payout φ)) (worldOf u).payout ≤ 0) ∧
      ∀ v : PCWorld, v.ConsistentWith D → T.value (Function.update (beliefHistory past) n
        (fun φ => ∑ u, p u * (worldOf u).payout φ)) v.payout ≤ 0 := by
  obtain ⟨u₀, hu₀⟩ := hW
  haveI : Nonempty ↥(worldsOf D B) := ⟨⟨u₀, mem_worldsOf.mpr hu₀⟩⟩
  let G : (↥(worldsOf D B) → ℝ) → ↥(worldsOf D B) → ℝ :=
    fun q u => worldValue T past (extWeights D B q) u.1
  have hG : ContinuousOn G (stdSimplex ℝ ↥(worldsOf D B)) := by
    apply Continuous.continuousOn
    apply continuous_pi
    intro u
    exact (continuous_worldValue T past u.1).comp (continuous_extWeights D B)
  have hid : ∀ q ∈ stdSimplex ℝ ↥(worldsOf D B), ∑ u, q u * G q u = 0 := by
    intro q hq
    have h1 : ∑ u, extWeights D B q u = 1 := by rw [sum_extWeights]; exact hq.2
    have h := sum_worldValue_eq_zero T past (extWeights D B q) h1
    rw [sum_extWeights_mul] at h
    exact h
  obtain ⟨q, hq, hle⟩ := coherent_fixed_point_abstract G hG hid
  refine ⟨extWeights D B q, ⟨fun u => ?_, ?_, fun u hu => ?_⟩, fun u hu => ?_, fun v hv => ?_⟩
  · unfold extWeights
    split_ifs with h
    · exact hq.1 ⟨u, h⟩
    · exact le_rfl
  · rw [sum_extWeights]; exact hq.2
  · by_contra hcon
    apply hu
    unfold extWeights
    rw [dif_neg (fun h => hcon (mem_worldsOf.mp h))]
  · exact hle ⟨u, hu⟩
  · have hmem := restrict_mem_worldsOf (fun φ hφ => hB φ (Finset.mem_union_right _ hφ)) hv
    have h := hle ⟨_, hmem⟩
    show T.value (fixedHistory past n (extWeights D B q)) v.payout ≤ 0
    rw [← value_restrict_eq T _ (atomBound_support_le hB) v]
    exact h

end Cleanroom.Bli.BliCoherentMm.AttemptB
