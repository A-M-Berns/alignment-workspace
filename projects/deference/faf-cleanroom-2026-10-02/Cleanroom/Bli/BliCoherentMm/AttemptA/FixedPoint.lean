import Cleanroom.Bli.BliCoherentMm.AttemptA.Worlds
import LogicalInduction.Construction.Brouwer

/-!
# `bli-coherent-mm` (attempt A) · FixedPoint: the coherent fixed point (T1, M1)

**T1 of the mandate, angle A (Nash's map).** Two layers:

* **The abstract lemma** `coherent_fixed_point_abstract` (the mathematics; Soto's Theorem 2 in its
  "necessary and sufficient" form): for a finite nonempty `ι` and `G : (ι → ℝ) → ι → ℝ`
  continuous in each coordinate with the zero-expected-value identity `∑ u, p u * G p u = 0` on
  the simplex, some `p* ∈ stdSimplex ℝ ι` has `G p* ≤ 0` everywhere. The map is **Nash's**
  `f p u := (p u + max (G p u) 0) / (1 + ∑ u', max (G p u') 0)`: continuous on all of `ι → ℝ`
  (denominator `≥ 1`), simplex-preserving; at a fixed point `p u * ∑ max(G p, 0) = max (G p u) 0`
  for every `u`, so if `∑ max(G p, 0) > 0` every `u` with `p u > 0` has `G p u > 0` and
  `∑ u, p u * G p u > 0`, against the identity. Brouwer is FAF's `stdSimplex_hasFPP` (from
  Sperner, in `Construction/Brouwer.lean`), transported from `Fin (card ι)` to `ι` by
  `Fintype.equivFin` (`exists_fixed_stdSimplex`) — grade (a).
* **The FAF instance** `coherent_fixed_point` (headline): for a day-`n` strategy `T`, a prior
  history, a stage `D` and an atom bound `B` with a `D`-consistent world (`hW`), there is a real
  world measure `p` on `WD D B` such that, with `V_p := Function.update prior n (worldTable p)`
  (day `n` priced at `∑ u, p u * payout u`), `T.value V_p (payout u) ≤ 0` in every `u ∈ WD D B`.
  The identity for the instance is **proved** (`sum_mul_value_worldHistory`: `∑ p = 1` makes
  `∑ u, p u * (payout u φ − V_p n φ) = 0`), not assumed; continuity comes from FAF's
  `EF.continuous_denote` composed with the affine map `p ↦ V_p` (`continuous_worldHistory_extR`).
  The `PCWorld` form `coherent_fixed_point_pcWorld` adds `hB` (support and stage within the atom
  bound) and restricts each consistent `PCWorld` to `B` atoms.

What is *not* here: FAF's `fixed_point_lemma` output (a per-sentence `[0,1]` valuation with no
measure) is never used; the conclusion is over `D`-consistent worlds only (T4 in `Contrast.lean`
shows the all-Boolean-tables form is false for coherent prices).

Sources: [[bli-coherent-mm-mandate]] T1, §Attempt angles (A); Soto PDF 05 Thm 2 (bli-soto-a-044);
[[bli-program]] §3.8.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## The abstract lemma: Nash's map on the simplex -/

section Abstract

variable {ι : Type} [Fintype ι]

/-- **Nash's map** for a demand function `G`: `f p u := (p u + max (G p u) 0) / (1 + ∑ u', max (G p u') 0)`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (A)
Kind: D
Fidelity: exact -/
noncomputable def nashMap (G : (ι → ℝ) → ι → ℝ) (p : ι → ℝ) : ι → ℝ :=
  fun u => (p u + max (G p u) 0) / (1 + ∑ u', max (G p u') 0)

/-- The normaliser is at least one, hence positive, everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nashMap_denom_pos (G : (ι → ℝ) → ι → ℝ) (p : ι → ℝ) : 0 < 1 + ∑ u', max (G p u') 0 :=
  add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun _ _ => le_max_right _ _)

/-- Nash's map is continuous on all of `ι → ℝ` when `G` is continuous in each coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma continuous_nashMap (G : (ι → ℝ) → ι → ℝ) (hG : ∀ u, Continuous fun p => G p u) :
    Continuous (nashMap G) := by
  apply continuous_pi
  intro u
  apply Continuous.div
  · exact (continuous_apply u).add ((hG u).max continuous_const)
  · exact continuous_const.add (continuous_finsetSum _ fun u' _ => (hG u').max continuous_const)
  · intro p
    exact (nashMap_denom_pos G p).ne'

/-- Nash's map sends the simplex into itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nashMap_mem_stdSimplex (G : (ι → ℝ) → ι → ℝ) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    nashMap G p ∈ stdSimplex ℝ ι := by
  refine ⟨fun u => div_nonneg (add_nonneg (hp.1 u) (le_max_right _ _)) (nashMap_denom_pos G p).le,
    ?_⟩
  unfold nashMap
  rw [← Finset.sum_div, Finset.sum_add_distrib, hp.2, div_self (nashMap_denom_pos G p).ne']

/-- **The fixed-point argument.** At a fixed point of Nash's map on the simplex, under the
zero-expected-value identity, every coordinate of `G` is `≤ 0`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (A)
Kind: P
Fidelity: exact -/
lemma nashMap_fixed_le (G : (ι → ℝ) → ι → ℝ) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι)
    (hid : ∑ u, p u * G p u = 0) (hfix : nashMap G p = p) : ∀ u, G p u ≤ 0 := by
  set M := ∑ u', max (G p u') 0 with hM
  have hkey : ∀ u, p u * M = max (G p u) 0 := by
    intro u
    have h := congrFun hfix u
    unfold nashMap at h
    rw [div_eq_iff (nashMap_denom_pos G p).ne'] at h
    rw [← hM] at h
    linarith
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨u₀, hu₀⟩ := hcon
  have hMpos : 0 < M := by
    calc (0 : ℝ) < max (G p u₀) 0 := lt_max_of_lt_left hu₀
      _ ≤ M := Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ u₀)
  have hpos : ∀ u, 0 < p u → 0 < G p u := by
    intro u hu
    have h : 0 < max (G p u) 0 := by rw [← hkey u]; exact mul_pos hu hMpos
    rcases lt_max_iff.mp h with h' | h'
    · exact h'
    · exact absurd h' (lt_irrefl 0)
  have hsum : 0 < ∑ u, p u * G p u := by
    apply Finset.sum_pos'
    · intro u _
      rcases (hp.1 u).lt_or_eq with h | h
      · exact (mul_pos h (hpos u h)).le
      · rw [← h, zero_mul]
    · by_contra hall
      simp only [not_exists, not_and, not_lt] at hall
      have hzero : ∑ u, p u = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        rcases (hp.1 u).lt_or_eq with h | h
        · exact absurd (mul_pos h (hpos u h)) (not_lt.mpr (hall u (Finset.mem_univ u)))
        · exact h.symm
      rw [hp.2] at hzero
      exact one_ne_zero hzero
  rw [hid] at hsum
  exact lt_irrefl 0 hsum

/-- **Brouwer on `stdSimplex ℝ ι`** for any finite nonempty `ι`: FAF's `stdSimplex_hasFPP` on
`Fin (card ι)` transported along `Fintype.equivFin` (reindexing preserves the simplex, by
`Equiv.sum_comp`). Stated in the `ContinuousOn`/`MapsTo`-free form a globally continuous map
needs.
Source: FAF `stdSimplex_hasFPP` (`Construction/Brouwer.lean`)
Kind: L
Fidelity: n/a -/
lemma exists_fixed_stdSimplex [Nonempty ι] (f : (ι → ℝ) → (ι → ℝ)) (hf : Continuous f)
    (hmaps : ∀ p ∈ stdSimplex ℝ ι, f p ∈ stdSimplex ℝ ι) : ∃ p ∈ stdSimplex ℝ ι, f p = p := by
  let e := Fintype.equivFin ι
  let toFin : (ι → ℝ) → (Fin (Fintype.card ι) → ℝ) := fun p i => p (e.symm i)
  let ofFin : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun x u => x (e u)
  have hto : ∀ p ∈ stdSimplex ℝ ι, toFin p ∈ stdSimplex ℝ (Fin (Fintype.card ι)) := by
    intro p hp
    refine ⟨fun i => hp.1 _, ?_⟩
    show ∑ i, p (e.symm i) = 1
    rw [Equiv.sum_comp e.symm p]
    exact hp.2
  have hof : ∀ x ∈ stdSimplex ℝ (Fin (Fintype.card ι)), ofFin x ∈ stdSimplex ℝ ι := by
    intro x hx
    refine ⟨fun u => hx.1 _, ?_⟩
    show ∑ u, x (e u) = 1
    rw [Equiv.sum_comp e x]
    exact hx.2
  have hofto : ∀ p, ofFin (toFin p) = p := fun p => funext fun u => by simp [ofFin, toFin]
  have hcont_to : Continuous toFin := continuous_pi fun i => continuous_apply _
  have hcont_of : Continuous ofFin := continuous_pi fun u => continuous_apply _
  obtain ⟨x, hx, hfx⟩ := BrouwerProof.fixed_of_hasFPP (BrouwerProof.stdSimplex_hasFPP Fintype.card_pos)
    (f := toFin ∘ f ∘ ofFin) (hcont_to.comp (hf.comp hcont_of)).continuousOn
    (fun x hx => hto _ (hmaps _ (hof x hx)))
  refine ⟨ofFin x, hof x hx, ?_⟩
  have h := congrArg ofFin hfx
  simp only [Function.comp_apply, hofto] at h
  exact h

/-- **T1, abstract lemma (Soto's Theorem 2, finite form).** For a finite nonempty `ι` and a demand
function `G : (ι → ℝ) → ι → ℝ` continuous in each coordinate with `∑ u, p u * G p u = 0` on the
simplex, some probability vector `p*` has `G p* u ≤ 0` for every `u`: no world in the support of
the market's own measure, nor outside it, pays the demand. Nash's map and Brouwer.
Source: [[bli-coherent-mm-mandate]] T1 (abstract lemma); Soto PDF 05 Thm 2 (bli-soto-a-044)
Kind: P
Fidelity: exact (the identity is a hypothesis here, as the mandate allows for the abstract
lemma; the FAF instance below derives it)
Hyps: (a) `hid` is derived at the instance (`sum_mul_worldValue`); `hG` from `EF.continuous_denote` -/
theorem coherent_fixed_point_abstract [Nonempty ι] (G : (ι → ℝ) → ι → ℝ)
    (hG : ∀ u, Continuous fun p => G p u) (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) :
    ∃ p ∈ stdSimplex ℝ ι, ∀ u, G p u ≤ 0 := by
  obtain ⟨p, hp, hfix⟩ := exists_fixed_stdSimplex (nashMap G) (continuous_nashMap G hG)
    (fun p hp => nashMap_mem_stdSimplex G hp)
  exact ⟨p, hp, nashMap_fixed_le G hp (hid p hp) hfix⟩

end Abstract

/-! ## The FAF instance: worlds, tables, histories -/

variable {D : Finset Sentence} {B : ℕ}

/-- Extension by zero of a vector on the `D`-consistent worlds to all finite worlds (real).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def extR (D : Finset Sentence) (B : ℕ) (p : ↥(WD D B) → ℝ) : FiniteWorld B → ℝ :=
  fun u => if h : u ∈ WD D B then p ⟨u, h⟩ else 0

/-- `extR` on a consistent world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extR_of_mem (p : ↥(WD D B) → ℝ) (x : ↥(WD D B)) : extR D B p x = p x := by
  simp [extR, x.2]

/-- `extR` vanishes off the consistent worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extR_of_not_mem (p : ↥(WD D B) → ℝ) {u : FiniteWorld B} (hu : u ∉ WD D B) :
    extR D B p u = 0 := by
  simp [extR, hu]

/-- Sums against `extR` are sums over the consistent worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_extR_mul (p : ↥(WD D B) → ℝ) (f : FiniteWorld B → ℝ) :
    ∑ u, extR D B p u * f u = ∑ x, p x * f x := by
  calc ∑ u, extR D B p u * f u = ∑ u ∈ WD D B, extR D B p u * f u :=
        (Finset.sum_subset (Finset.subset_univ _)
          (fun u _ hu => by rw [extR_of_not_mem p hu, zero_mul])).symm
    _ = ∑ x : ↥(WD D B), extR D B p x * f x := (Finset.sum_coe_sort _ _).symm
    _ = ∑ x, p x * f x := Finset.sum_congr rfl fun x _ => by rw [extR_of_mem]

/-- `extR` preserves the total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_extR (p : ↥(WD D B) → ℝ) : ∑ u, extR D B p u = ∑ x, p x := by
  have h := sum_extR_mul p (fun _ => 1)
  simpa using h

/-- **The day-`n` price table of a real world weight vector**: `∑ u, p u * payout u φ`.
Source: [[bli-coherent-mm-mandate]] T1 (`V_p`)
Kind: D
Fidelity: exact -/
noncomputable def worldTable (p : FiniteWorld B → ℝ) (φ : Sentence) : ℝ :=
  ∑ u, p u * (u.payoutRat φ : ℝ)

/-- The cast of a rational marginal is the real world table of the cast weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldTable_cast (w : FiniteWorld B → ℚ) (φ : Sentence) :
    worldTable (fun u => (w u : ℝ)) φ = (marginal w φ : ℝ) := by
  simp [worldTable, marginal]

/-- **The history with day `n` priced by `p`**: `V_p := Function.update prior n (worldTable p)`.
Source: [[bli-coherent-mm-mandate]] T1 (`V_p`)
Kind: D
Fidelity: exact -/
noncomputable def worldHistory (prior : History) (n : ℕ) (p : FiniteWorld B → ℝ) : History :=
  Function.update prior n (worldTable p)

/-- Day `n` of `V_p` is the world table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldHistory_self (prior : History) (n : ℕ) (p : FiniteWorld B → ℝ) :
    worldHistory prior n p n = worldTable p :=
  Function.update_self _ _ _

/-- Days `≠ n` of `V_p` are the prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldHistory_of_ne (prior : History) {n k : ℕ} (hk : k ≠ n) (p : FiniteWorld B → ℝ) :
    worldHistory prior n p k = prior k :=
  Function.update_of_ne hk _ _

/-- **The zero-expected-value identity, proved**: for a weight vector of total mass one, the
`p`-expectation over worlds of a strategy's value on `V_p` is zero, because
`∑ u, p u * payout u φ = V_p n φ` is the day-`n` price of every traded `φ`.
Source: [[bli-coherent-mm-mandate]] T1 ("the identity … is proved, not assumed")
Kind: P
Fidelity: exact -/
lemma sum_mul_value_worldHistory {n : ℕ} (T : Strategy n) (prior : History)
    (p : FiniteWorld B → ℝ) (hp : ∑ u, p u = 1) :
    ∑ u, p u * T.value (worldHistory prior n p) (payoutReal u) = 0 := by
  simp_rw [Strategy.value_eq_sum_support, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro φ _
  rw [worldHistory_self]
  have hsplit : ∀ u, p u * (T.shares (worldHistory prior n p) φ * (payoutReal u φ - worldTable p φ))
      = T.shares (worldHistory prior n p) φ * (p u * (u.payoutRat φ : ℝ))
        - T.shares (worldHistory prior n p) φ * worldTable p φ * p u := by
    intro u
    unfold payoutReal
    ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, mul_one]
  unfold worldTable
  ring

/-- Continuity of the world table of the extension in the simplex coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma continuous_worldTable_extR (φ : Sentence) :
    Continuous fun p : ↥(WD D B) → ℝ => worldTable (extR D B p) φ := by
  unfold worldTable
  apply continuous_finsetSum
  intro u _
  apply Continuous.mul _ continuous_const
  unfold extR
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

/-- Continuity of `p ↦ V_p` (product topology on `History`).
Source: [[bli-coherent-mm-mandate]] T1 (the affine map `p ↦ V_p`); FAF `continuous_strategyHistory`
Kind: L
Fidelity: n/a -/
lemma continuous_worldHistory_extR (prior : History) (n : ℕ) :
    Continuous fun p : ↥(WD D B) → ℝ => worldHistory prior n (extR D B p) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro φ
  by_cases hk : k = n
  · subst hk
    simp only [worldHistory, Function.update_self]
    exact continuous_worldTable_extR φ
  · simp only [worldHistory, Function.update_of_ne hk]
    exact continuous_const

/-- A strategy's value is continuous in any continuous parametrisation of the history
(`EF.continuous_denote` composed, one trade at a time).
Source: FAF `EF.continuous_denote`; the pattern of `continuous_strategyWorldValue`
Kind: L
Fidelity: n/a -/
lemma continuous_value_comp {X : Type} [TopologicalSpace X] {n : ℕ} (T : Strategy n)
    (V : X → History) (hV : Continuous V) (w : Sentence → ℝ) :
    Continuous fun x => T.value (V x) w := by
  unfold Strategy.value
  apply continuous_list_sum (f := fun (q : EF × Sentence) (x : X) =>
    q.1.denote (V x) * (w q.2 - V x n q.2))
  intro q _
  apply Continuous.mul
  · exact (EF.continuous_denote q.1).comp hV
  · exact continuous_const.sub ((continuous_apply q.2).comp ((continuous_apply n).comp hV))

/-- **The demand function of the instance**: the value of `T` on `V_{extR p}` in the consistent
world `x`, as a function of the simplex coordinates `p`.
Source: [[bli-coherent-mm-mandate]] T1
Kind: D
Fidelity: exact -/
noncomputable def worldValue {n : ℕ} (T : Strategy n) (prior : History) (D : Finset Sentence)
    (B : ℕ) (p : ↥(WD D B) → ℝ) (x : ↥(WD D B)) : ℝ :=
  T.value (worldHistory prior n (extR D B p)) (payoutReal x.1)

/-- Continuity of the demand function in each coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma continuous_worldValue {n : ℕ} (T : Strategy n) (prior : History) (D : Finset Sentence)
    (B : ℕ) (x : ↥(WD D B)) : Continuous fun p => worldValue T prior D B p x :=
  continuous_value_comp T _ (continuous_worldHistory_extR prior n) _

/-- The identity for the demand function on the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_mul_worldValue {n : ℕ} (T : Strategy n) (prior : History) {p : ↥(WD D B) → ℝ}
    (hp : p ∈ stdSimplex ℝ ↥(WD D B)) : ∑ x, p x * worldValue T prior D B p x = 0 := by
  have h := sum_mul_value_worldHistory T prior (extR D B p) (by rw [sum_extR]; exact hp.2)
  rw [← h, sum_extR_mul]
  rfl

/-- The fixed point on the `D`-consistent world simplex, in simplex coordinates.
Source: [[bli-coherent-mm-mandate]] T1
Kind: P
Fidelity: exact
Hyps: (a) `hW` (nonempty simplex) -/
theorem exists_fixedPoint_worldValue {n : ℕ} (T : Strategy n) (prior : History)
    (D : Finset Sentence) (B : ℕ) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p ∈ stdSimplex ℝ ↥(WD D B), ∀ x, worldValue T prior D B p x ≤ 0 := by
  haveI : Nonempty ↥(WD D B) := by
    obtain ⟨u, hu⟩ := hW
    exact ⟨⟨u, mem_WD.mpr hu⟩⟩
  exact coherent_fixed_point_abstract _ (continuous_worldValue T prior D B)
    (fun p hp => sum_mul_worldValue T prior hp)

/-! ## T1, the headline over FAF's objects -/

/-- **T1 (headline, M1). The coherent fixed point.** For a day-`n` strategy `T`, a prior history,
a stage `D` and an atom bound `B` with a `D`-consistent finite world, there is a real world
measure `p` on `FiniteWorld B` — nonnegative, total mass one, supported on the `D`-consistent
worlds — such that, with day `n` priced by `p`'s marginals (`worldHistory prior n p`), `T`'s
value is `≤ 0` in **every `D`-consistent world over `B` atoms**. Not FAF's `fixed_point_lemma`
(a per-sentence valuation with no measure); not a bound over all Boolean tables on the support
(false for coherent prices, `Contrast.lean`). No atom bound is needed in this finite form; the
`PCWorld` form below needs `hB`.
Source: [[bli-coherent-mm-mandate]] T1; Soto PDF 05 Thm 2; [[bli-program]] §3.8, §4 row M1
Kind: P
Fidelity: exact (stated for any prior `History`; `beliefHistory past` is the instance of record)
Hyps: (a) `hW : ∃ u, (worldOf u).ConsistentWith D` — the simplex is nonempty (discharged from
`paperDP_hworld` in `Witness.lean`); the identity and continuity are derived -/
theorem coherent_fixed_point {n : ℕ} (T : Strategy n) (prior : History) (D : Finset Sentence)
    (B : ℕ) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      ∀ u ∈ WD D B, T.value (worldHistory prior n p) (payoutReal u) ≤ 0 := by
  obtain ⟨p, hp, hval⟩ := exists_fixedPoint_worldValue T prior D B hW
  refine ⟨extR D B p, ?_, ?_, ?_, ?_⟩
  · intro u
    unfold extR
    split_ifs
    · exact hp.1 _
    · exact le_rfl
  · rw [sum_extR]
    exact hp.2
  · intro u hu
    by_contra hcon
    exact hu (extR_of_not_mem p (fun h => hcon (mem_WD.mp h)))
  · intro u hu
    exact hval ⟨u, hu⟩

/-- **T1, `PCWorld` form.** With every traded sentence and every stage sentence within the atom
bound, the fixed point's value is `≤ 0` in every `PCWorld` consistent with `D`: restrict the world
to `B` atoms (`restrict_mem_WD`, `value_payout_eq_restrict`).
Source: [[bli-coherent-mm-mandate]] T1 (`PCWorld` form)
Kind: C
Fidelity: exact
Hyps: (a) `hB` (atom bound; `T.support ∪ D` suffices, weaker than the mandate's
`mentionedSet T ∪ D`), `hW` (as in `coherent_fixed_point`) -/
theorem coherent_fixed_point_pcWorld {n : ℕ} (T : Strategy n) (prior : History)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ T.support ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      ∀ v : PCWorld, v.ConsistentWith D → T.value (worldHistory prior n p) v.payout ≤ 0 := by
  obtain ⟨p, h0, h1, hD, hval⟩ := coherent_fixed_point T prior D B hW
  refine ⟨p, h0, h1, hD, fun v hv => ?_⟩
  rw [value_payout_eq_restrict T _ v (fun φ hφ => hB φ (Finset.mem_union_left _ hφ))]
  exact hval _ (restrict_mem_WD (fun φ hφ => hB φ (Finset.mem_union_right _ hφ)) hv)

end Cleanroom.Bli.BliCoherentMm.AttemptA
