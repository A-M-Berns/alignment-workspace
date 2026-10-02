import Cleanroom.Found.FixKakutani.Transport
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fin.VecNotation

/-!
# Witnesses for the Kakutani package

* **N+ (target 5a): matching pennies.** The best-response correspondence `mpBR` of the
  matching-pennies game on the square `[0,1]²` (row player wants to match, column player to
  mismatch), defined honestly as the argmax of the expected payoffs. It satisfies the full
  hypothesis package of `kakutani_pi_Icc` (`mpBR_maps`, `mpBR_nonempty`, `mpBR_convex`,
  `mpBR_hasClosedGraphOn`), so `kakutani_pi_Icc` yields a fixed point (`mpBR_exists_fixed`).
  Two further facts certify that the theorem does set-valued work here: the fixed point is
  exactly `(1/2, 1/2)` (`mem_mpBR_self_iff`), and `mpBR` has **no continuous selection** on the
  square (`mpBR_no_continuous_selection`), so no Brouwer instance is hiding inside.
* **Round trip to Brouwer (5b):** a continuous self-map of `K` is the singleton-valued
  correspondence `x ↦ {f x}`, which has a closed graph; `kakutani_findim` then returns a fixed
  point of `f` (`brouwer_findim_of_kakutani`). This checks that `HasClosedGraphOn` is not too
  strong to include continuous functions.
* **Sharpness (5c, N−):** three one-dimensional correspondences on `Icc 0 1`, each dropping one
  hypothesis (nonempty values, convex values, closed graph), keeping the others and having no
  fixed point.
* **A second N+ witness, singleton value at the fixed point (repair round 1):** at the
  matching-pennies fixed point the value of `mpBR` is the whole square, so there the fixed-point
  property reads `x* ∈ K`. `wedgeF` on `Icc 0 1` (`{(x+1)/2}` for `x < 1/2`, `Icc (3/4) 1` at
  `1/2`, `{1}` for `x > 1/2`) has the unique fixed point `1` with value `{1}`, no continuous
  selection, and is fed to `kakutani_findim` directly on `ℝ` (`wedgeF_exists_fixed`); it also
  gives `exists_approx_selection` a direct instance (`wedgeF_approx_selection`).
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology

/-! ### Matching pennies -/

/-- Row player's expected payoff in matching pennies when the row player plays `1` with
probability `p` and the column player plays `1` with probability `q`: the probability the
two choices match.
Source: none: infrastructure (target 5a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def rowPayoff (p q : ℝ) : ℝ := p * q + (1 - p) * (1 - q)

/-- Column player's expected payoff: the probability the two choices differ.
Source: none: infrastructure (target 5a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def colPayoff (p q : ℝ) : ℝ := p * (1 - q) + (1 - p) * q

/-- The best-response set of a one-dimensional payoff `u` over mixed strategies in `[0,1]`: the
argmax of `u` on `Icc 0 1`.
Source: none: infrastructure (target 5a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def bestResponse (u : ℝ → ℝ) : Set ℝ := {p | p ∈ Icc (0 : ℝ) 1 ∧ ∀ p' ∈ Icc (0 : ℝ) 1, u p' ≤ u p}

/-- The square `[0,1]²` as `Set.univ.pi (fun _ : Fin 2 => Icc 0 1)` in `Fin 2 → ℝ`, the domain
form of `kakutani_pi_Icc` with `Q = Fin 2`.
Source: none: infrastructure (target 5a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev square : Set (Fin 2 → ℝ) := Set.univ.pi fun _ : Fin 2 => Icc (0 : ℝ) 1

/-- The matching-pennies best-response correspondence on the square: `y ∈ mpBR x` iff `y 0` is a
best response of the row player to the column mix `x 1` and `y 1` a best response of the column
player to the row mix `x 0`.
Source: none: infrastructure (target 5a: the mandate's N+ witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mpBR (x : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {y | y 0 ∈ bestResponse (fun p => rowPayoff p (x 1)) ∧
       y 1 ∈ bestResponse (fun q => colPayoff (x 0) q)}

/-- `rowPayoff` is affine in `p` with slope `2q − 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem rowPayoff_eq (p q : ℝ) : rowPayoff p q = p * (2 * q - 1) + (1 - q) := by
  unfold rowPayoff; ring

/-- `colPayoff` is affine in `q` with slope `1 − 2p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem colPayoff_eq (p q : ℝ) : colPayoff p q = q * (1 - 2 * p) + p := by
  unfold colPayoff; ring

/-- Row's best response to `q > 1/2` is to play `1` for sure (the mandate's explicit case form, derived from the argmax definition).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_row_of_gt {q : ℝ} (hq : 1 / 2 < q) :
    bestResponse (fun p => rowPayoff p q) = {1} := by
  ext p
  simp only [bestResponse, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff, rowPayoff_eq]
  constructor
  · rintro ⟨⟨hp0, hp1⟩, hmax⟩
    have := hmax 1 ⟨zero_le_one, le_rfl⟩
    nlinarith
  · rintro rfl
    exact ⟨⟨zero_le_one, le_rfl⟩, fun p' ⟨_, hp'1⟩ => by nlinarith⟩

/-- Row's best response to `q < 1/2` is to play `0` for sure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_row_of_lt {q : ℝ} (hq : q < 1 / 2) :
    bestResponse (fun p => rowPayoff p q) = {0} := by
  ext p
  simp only [bestResponse, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff, rowPayoff_eq]
  constructor
  · rintro ⟨⟨hp0, hp1⟩, hmax⟩
    have := hmax 0 ⟨le_rfl, zero_le_one⟩
    nlinarith
  · rintro rfl
    exact ⟨⟨le_rfl, zero_le_one⟩, fun p' ⟨hp'0, _⟩ => by nlinarith⟩

/-- Against `q = 1/2` every mixed strategy of row is a best response.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_row_half : bestResponse (fun p => rowPayoff p (1 / 2)) = Icc 0 1 := by
  ext p
  simp only [bestResponse, Set.mem_setOf_eq, rowPayoff_eq]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun p' _ => by norm_num⟩

/-- Column's best response to `p > 1/2` is `0` (mismatch).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_col_of_gt {p : ℝ} (hp : 1 / 2 < p) :
    bestResponse (fun q => colPayoff p q) = {0} := by
  ext q
  simp only [bestResponse, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff, colPayoff_eq]
  constructor
  · rintro ⟨⟨hq0, hq1⟩, hmax⟩
    have := hmax 0 ⟨le_rfl, zero_le_one⟩
    nlinarith
  · rintro rfl
    exact ⟨⟨le_rfl, zero_le_one⟩, fun q' ⟨hq'0, _⟩ => by nlinarith⟩

/-- Column's best response to `p < 1/2` is `1` (mismatch).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_col_of_lt {p : ℝ} (hp : p < 1 / 2) :
    bestResponse (fun q => colPayoff p q) = {1} := by
  ext q
  simp only [bestResponse, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff, colPayoff_eq]
  constructor
  · rintro ⟨⟨hq0, hq1⟩, hmax⟩
    have := hmax 1 ⟨zero_le_one, le_rfl⟩
    nlinarith
  · rintro rfl
    exact ⟨⟨zero_le_one, le_rfl⟩, fun q' ⟨_, hq'1⟩ => by nlinarith⟩

/-- Against `p = 1/2` every mixed strategy of column is a best response.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_col_half : bestResponse (fun q => colPayoff (1 / 2) q) = Icc 0 1 := by
  ext q
  simp only [bestResponse, Set.mem_setOf_eq, colPayoff_eq]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun q' _ => by norm_num⟩

/-- Best responses are mixed strategies: `bestResponse u ⊆ Icc 0 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bestResponse_subset_Icc (u : ℝ → ℝ) : bestResponse u ⊆ Icc 0 1 := fun _ h => h.1

/-- Membership in the square, coordinatewise.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mem_square_iff {x : Fin 2 → ℝ} : x ∈ square ↔ x 0 ∈ Icc (0 : ℝ) 1 ∧ x 1 ∈ Icc (0 : ℝ) 1 := by
  simp only [square, Set.mem_univ_pi]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i; fin_cases i <;> assumption

/-- `mpBR` maps the square into itself.
Source: none: infrastructure (target 5a hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBR_maps : ∀ x ∈ square, mpBR x ⊆ square := by
  intro x _ y hy
  exact mem_square_iff.2 ⟨hy.1.1, hy.2.1⟩

/-- `mpBR x` is nonempty for every `x` (a best response always exists).
Source: none: infrastructure (target 5a hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBR_nonempty : ∀ x ∈ square, (mpBR x).Nonempty := by
  intro x _
  -- row's best response
  have hrow : ∃ p, p ∈ bestResponse (fun p => rowPayoff p (x 1)) := by
    rcases le_or_gt (1 / 2) (x 1) with h | h
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, fun p' ⟨_, hp'1⟩ => ?_⟩
      simp only [rowPayoff_eq]; nlinarith
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, fun p' ⟨hp'0, _⟩ => ?_⟩
      simp only [rowPayoff_eq]; nlinarith
  have hcol : ∃ q, q ∈ bestResponse (fun q => colPayoff (x 0) q) := by
    rcases le_or_gt (x 0) (1 / 2) with h | h
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, fun q' ⟨_, hq'1⟩ => ?_⟩
      simp only [colPayoff_eq]; nlinarith
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, fun q' ⟨hq'0, _⟩ => ?_⟩
      simp only [colPayoff_eq]; nlinarith
  obtain ⟨p, hp⟩ := hrow
  obtain ⟨q, hq⟩ := hcol
  exact ⟨![p, q], by simpa [mpBR] using ⟨hp, hq⟩⟩

/-- Row's best-response set is convex (it is `{0}`, `{1}` or `Icc 0 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem convex_bestResponse_row (q : ℝ) : Convex ℝ (bestResponse (fun p => rowPayoff p q)) := by
  rcases lt_trichotomy q (1 / 2) with h | rfl | h
  · rw [bestResponse_row_of_lt h]; exact convex_singleton _
  · rw [bestResponse_row_half]; exact convex_Icc _ _
  · rw [bestResponse_row_of_gt h]; exact convex_singleton _

/-- Column's best-response set is convex (it is `{0}`, `{1}` or `Icc 0 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem convex_bestResponse_col (p : ℝ) : Convex ℝ (bestResponse (fun q => colPayoff p q)) := by
  rcases lt_trichotomy p (1 / 2) with h | rfl | h
  · rw [bestResponse_col_of_lt h]; exact convex_singleton _
  · rw [bestResponse_col_half]; exact convex_Icc _ _
  · rw [bestResponse_col_of_gt h]; exact convex_singleton _

/-- `mpBR x` is convex (a product of two convex sets of `[0,1]`).
Source: none: infrastructure (target 5a hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBR_convex : ∀ x ∈ square, Convex ℝ (mpBR x) := by
  intro x _ y hy z hz a b ha hb hab
  exact ⟨convex_bestResponse_row (x 1) hy.1 hz.1 ha hb hab,
    convex_bestResponse_col (x 0) hy.2 hz.2 ha hb hab⟩

/-- `mpBR` has a closed graph over the square: the graph is cut out by the closed conditions
`y 0 ∈ Icc 0 1`, `y 1 ∈ Icc 0 1` and, for each pure deviation, a non-strict payoff inequality
between continuous functions of `(x, y)`.
Source: none: infrastructure (target 5a hypothesis package; the closed-graph check consumers
must do, plan §0.4 rule 11)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBR_hasClosedGraphOn : HasClosedGraphOn mpBR square := by
  unfold HasClosedGraphOn
  have hset : {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | p.1 ∈ square ∧ p.2 ∈ mpBR p.1} =
      (Prod.fst ⁻¹' square) ∩
      ((fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2 0) ⁻¹' Icc (0 : ℝ) 1) ∩
      (⋂ p' ∈ Icc (0 : ℝ) 1, {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) |
        rowPayoff p' (p.1 1) ≤ rowPayoff (p.2 0) (p.1 1)}) ∩
      ((fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2 1) ⁻¹' Icc (0 : ℝ) 1) ∩
      (⋂ q' ∈ Icc (0 : ℝ) 1, {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) |
        colPayoff (p.1 0) q' ≤ colPayoff (p.1 0) (p.2 1)}) := by
    ext p
    simp only [mpBR, bestResponse, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter]
    tauto
  rw [hset]
  have hsq : IsClosed square := isClosed_set_pi fun _ _ => isClosed_Icc
  refine ((((hsq.preimage continuous_fst).inter (isClosed_Icc.preimage (by fun_prop))).inter
    (isClosed_biInter fun p' _ => isClosed_le ?_ ?_)).inter
    (isClosed_Icc.preimage (by fun_prop))).inter
    (isClosed_biInter fun q' _ => isClosed_le ?_ ?_)
  all_goals simp only [rowPayoff, colPayoff]; fun_prop

/-- **N+ witness: Kakutani on matching pennies.** The best-response correspondence of matching
pennies satisfies the full hypothesis package of `kakutani_pi_Icc` on `[0,1]²`, so it has a
fixed point (a mixed Nash equilibrium). `mpBR` has non-singleton values along `x 0 = 1/2` and
`x 1 = 1/2` and no continuous selection (`mpBR_no_continuous_selection`), so this exercises the
set-valued content of the theorem.
Source: none: infrastructure (target 5a; the mandate's N+ witness)
Kind: N+
Fidelity: n/a
Hyps: (a) all, each proved above -/
theorem mpBR_exists_fixed : ∃ x ∈ square, x ∈ mpBR x :=
  kakutani_pi_Icc mpBR mpBR_maps mpBR_nonempty mpBR_convex mpBR_hasClosedGraphOn

/-- The fixed points of `mpBR` are exactly `(1/2, 1/2)`: the unique mixed equilibrium of
matching pennies.
Source: none: infrastructure (target 5a)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem mem_mpBR_self_iff {x : Fin 2 → ℝ} : x ∈ mpBR x ↔ x = fun _ => 1 / 2 := by
  constructor
  · rintro ⟨h0, h1⟩
    have hx1 : x 1 = 1 / 2 := by
      rcases lt_trichotomy (x 1) (1 / 2) with h | h | h
      · exfalso
        rw [bestResponse_row_of_lt h] at h0
        have hx0 : x 0 = 0 := h0
        rw [bestResponse_col_of_lt (by rw [hx0]; norm_num)] at h1
        have : x 1 = 1 := h1
        linarith
      · exact h
      · exfalso
        rw [bestResponse_row_of_gt h] at h0
        have hx0 : x 0 = 1 := h0
        rw [bestResponse_col_of_gt (by rw [hx0]; norm_num)] at h1
        have : x 1 = 0 := h1
        linarith
    have hx0 : x 0 = 1 / 2 := by
      rcases lt_trichotomy (x 0) (1 / 2) with h | h | h
      · exfalso
        rw [bestResponse_col_of_lt h] at h1
        have : x 1 = 1 := h1
        linarith
      · exact h
      · exfalso
        rw [bestResponse_col_of_gt h] at h1
        have : x 1 = 0 := h1
        linarith
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [bestResponse_row_half]; norm_num
    · rw [bestResponse_col_half]; norm_num

/-- **No continuous selection.** There is no `g` continuous on the square with `g x ∈ mpBR x`
for all `x` in the square: along the segment `x = (1/2, t)`, any selection has first coordinate
`0` for `t < 1/2` and `1` for `t > 1/2`, so by the intermediate value theorem (applied twice,
to the values `1/3` and `2/3`) continuity fails at `t = 1/2`. Hence `mpBR_exists_fixed` is not
a Brouwer instance in disguise.
Source: none: infrastructure (target 5a, the no-selection clause)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem mpBR_no_continuous_selection :
    ¬ ∃ g : (Fin 2 → ℝ) → (Fin 2 → ℝ), ContinuousOn g square ∧ ∀ x ∈ square, g x ∈ mpBR x := by
  rintro ⟨g, hg_cont, hg_sel⟩
  let γ : ℝ → (Fin 2 → ℝ) := fun t => ![1 / 2, t]
  have hγ_cont : Continuous γ := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [γ] using continuous_const
    · simpa [γ] using continuous_id'
  have hγ_mem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ square := by
    intro t ht
    rw [mem_square_iff]
    simp only [γ, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by norm_num, ht⟩
  let h : ℝ → ℝ := fun t => g (γ t) 0
  have hh_cont : ContinuousOn h (Icc 0 1) :=
    (continuous_apply 0).comp_continuousOn (hg_cont.comp hγ_cont.continuousOn hγ_mem)
  have hval : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ bestResponse (fun p => rowPayoff p t) := by
    intro t ht
    have := (hg_sel (γ t) (hγ_mem t ht)).1
    simpa [γ, h] using this
  have hI : Icc (1 / 4 : ℝ) (3 / 4) ⊆ Icc 0 1 := Icc_subset_Icc (by norm_num) (by norm_num)
  have h_lo : h (1 / 4) = 0 := by
    have := hval (1 / 4) (by norm_num)
    rw [bestResponse_row_of_lt (by norm_num)] at this
    exact this
  have h_hi : h (3 / 4) = 1 := by
    have := hval (3 / 4) (by norm_num)
    rw [bestResponse_row_of_gt (by norm_num)] at this
    exact this
  have hivt := intermediate_value_Icc (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4) (hh_cont.mono hI)
  rw [h_lo, h_hi] at hivt
  have key : ∀ t ∈ Icc (1 / 4 : ℝ) (3 / 4), h t ≠ 0 → h t ≠ 1 → t = 1 / 2 := by
    intro t ht h0 h1
    rcases lt_trichotomy t (1 / 2) with hlt | heq | hgt
    · exfalso
      have := hval t (hI ht)
      rw [bestResponse_row_of_lt hlt] at this
      exact h0 this
    · exact heq
    · exfalso
      have := hval t (hI ht)
      rw [bestResponse_row_of_gt hgt] at this
      exact h1 this
  obtain ⟨t₁, ht₁, ht₁v⟩ := hivt (⟨by norm_num, by norm_num⟩ : (1 / 3 : ℝ) ∈ Icc 0 1)
  obtain ⟨t₂, ht₂, ht₂v⟩ := hivt (⟨by norm_num, by norm_num⟩ : (2 / 3 : ℝ) ∈ Icc 0 1)
  have e₁ : t₁ = 1 / 2 := key t₁ ht₁ (by rw [ht₁v]; norm_num) (by rw [ht₁v]; norm_num)
  have e₂ : t₂ = 1 / 2 := key t₂ ht₂ (by rw [ht₂v]; norm_num) (by rw [ht₂v]; norm_num)
  rw [e₁] at ht₁v
  rw [e₂] at ht₂v
  rw [ht₁v] at ht₂v
  norm_num at ht₂v

/-! ### Round trip to Brouwer -/

/-- **Brouwer from Kakutani** (round trip, finite-dimensional real normed spaces): a continuous
self-map `f` of a nonempty compact convex `K` is the singleton-valued correspondence
`x ↦ {f x}`, which has a closed graph over `K`, nonempty convex values in `K`; `kakutani_findim`
returns a fixed point of `f`. This checks that `HasClosedGraphOn` includes the graphs of
continuous maps (it is not accidentally too strong).
Source: none: infrastructure (target 5b)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem brouwer_findim_of_kakutani {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    (f : E → E) (hf_cont : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  have hgraph : HasClosedGraphOn (fun x => {f x}) K := by
    rw [hasClosedGraphOn_iff_seq_of_isClosed hK_compact.isClosed]
    intro xs ys x y hmem hxs hys
    have hxK : x ∈ K :=
      hK_compact.isClosed.mem_of_tendsto hxs (Eventually.of_forall fun n => (hmem n).1)
    have hfx : Tendsto (fun n => f (xs n)) atTop (𝓝 (f x)) :=
      (hf_cont x hxK).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxs, Eventually.of_forall fun n => (hmem n).1⟩)
    have hys' : ys = fun n => f (xs n) := funext fun n => (hmem n).2
    rw [hys'] at hys
    exact (tendsto_nhds_unique hys hfx).symm ▸ Set.mem_singleton _
  obtain ⟨x, hx, hfx⟩ := kakutani_findim hK_compact hK_convex hK_nonempty (fun x => {f x})
    (fun x hx => by simpa using hf_maps hx) (fun x _ => Set.singleton_nonempty _)
    (fun x _ => convex_singleton _) hgraph
  exact ⟨x, hx, (Set.mem_singleton_iff.1 hfx).symm⟩

/-! ### Sharpness: each hypothesis is needed (one-dimensional examples on `Icc 0 1`) -/

/-- Dropping nonemptiness: the empty correspondence has convex values in `Icc 0 1` and a closed
graph, but no fixed point.
Source: none: infrastructure (target 5c)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem sharp_nonempty :
    (∀ x ∈ Icc (0 : ℝ) 1, (fun _ : ℝ => (∅ : Set ℝ)) x ⊆ Icc 0 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, Convex ℝ ((fun _ : ℝ => (∅ : Set ℝ)) x)) ∧
    HasClosedGraphOn (fun _ : ℝ => (∅ : Set ℝ)) (Icc 0 1) ∧
    ¬ ∃ x ∈ Icc (0 : ℝ) 1, x ∈ (fun _ : ℝ => (∅ : Set ℝ)) x := by
  refine ⟨fun _ _ => empty_subset _, fun _ _ => convex_empty, ?_, ?_⟩
  · unfold HasClosedGraphOn
    simp
  · rintro ⟨x, _, hx⟩
    exact hx

/-- The non-convex example: `{1}` for `x < 1/2`, `{0, 1}` at `x = 1/2`, `{0}` for `x > 1/2`.
Source: none: infrastructure (target 5c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def sharpConvexF (x : ℝ) : Set ℝ := {y | (x ≤ 1 / 2 ∧ y = 1) ∨ (1 / 2 ≤ x ∧ y = 0)}

/-- Dropping convexity of the values: `sharpConvexF` has nonempty values in `Icc 0 1` and a
closed graph over `Icc 0 1`, its value at `1/2` is `{0, 1}` (not convex), and it has no fixed
point.
Source: none: infrastructure (target 5c)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem sharp_convex :
    (∀ x ∈ Icc (0 : ℝ) 1, sharpConvexF x ⊆ Icc 0 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, (sharpConvexF x).Nonempty) ∧
    HasClosedGraphOn sharpConvexF (Icc 0 1) ∧
    ¬ Convex ℝ (sharpConvexF (1 / 2)) ∧
    ¬ ∃ x ∈ Icc (0 : ℝ) 1, x ∈ sharpConvexF x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro x _ y (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · intro x _
    rcases le_or_gt x (1 / 2) with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨h.le, rfl⟩⟩
  · unfold HasClosedGraphOn
    exact (isClosed_Icc.preimage continuous_fst).inter
      (((isClosed_le continuous_fst continuous_const).inter
          (isClosed_eq continuous_snd continuous_const)).union
        ((isClosed_le continuous_const continuous_fst).inter
          (isClosed_eq continuous_snd continuous_const)))
  · intro hconv
    have h0 : (0 : ℝ) ∈ sharpConvexF (1 / 2) := Or.inr ⟨le_rfl, rfl⟩
    have h1 : (1 : ℝ) ∈ sharpConvexF (1 / 2) := Or.inl ⟨le_rfl, rfl⟩
    have := hconv h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at this
    rcases this with ⟨_, h⟩ | ⟨_, h⟩ <;> norm_num at h
  · rintro ⟨x, _, (⟨hx, rfl⟩ | ⟨hx, rfl⟩)⟩ <;> norm_num at hx

/-- The non-closed-graph example: `{1}` for `x < 1`, `{0}` at `x = 1`.
Source: none: infrastructure (target 5c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def sharpGraphF (x : ℝ) : Set ℝ := if x < 1 then {1} else {0}

/-- Dropping the closed graph: `sharpGraphF` has nonempty convex values in `Icc 0 1` and no fixed
point; its graph over `Icc 0 1` is not closed (`(1 − 1/(n+1), 1) → (1, 1)` but `1 ∉ F 1`).
Source: none: infrastructure (target 5c)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem sharp_graph :
    (∀ x ∈ Icc (0 : ℝ) 1, sharpGraphF x ⊆ Icc 0 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, (sharpGraphF x).Nonempty) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, Convex ℝ (sharpGraphF x)) ∧
    ¬ HasClosedGraphOn sharpGraphF (Icc 0 1) ∧
    ¬ ∃ x ∈ Icc (0 : ℝ) 1, x ∈ sharpGraphF x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x _ y hy
    unfold sharpGraphF at hy
    split_ifs at hy <;> simp only [Set.mem_singleton_iff] at hy <;> subst hy <;> norm_num
  · intro x _
    unfold sharpGraphF
    split_ifs <;> exact Set.singleton_nonempty _
  · intro x _
    unfold sharpGraphF
    split_ifs <;> exact convex_singleton _
  · intro h
    let xs : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
    have hxs_mem : ∀ n, xs n ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ sharpGraphF (xs n) := by
      intro n
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      refine ⟨⟨by simp only [xs]; linarith, by simp only [xs]; linarith⟩, ?_⟩
      simp only [sharpGraphF, xs]
      rw [if_pos (by linarith)]
      exact Set.mem_singleton _
    have hlim : Tendsto xs atTop (𝓝 1) := by
      have := tendsto_const_nhds (x := (1 : ℝ)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [xs] using this
    have := (h.mem_of_tendsto (Eventually.of_forall hxs_mem) hlim tendsto_const_nhds).2
    simp [sharpGraphF] at this
  · rintro ⟨x, _, hx⟩
    unfold sharpGraphF at hx
    split_ifs at hx with hlt
    · simp only [Set.mem_singleton_iff] at hx
      linarith
    · simp only [Set.mem_singleton_iff] at hx
      linarith

/-! ### A second N+ witness: singleton value at the fixed point, still no continuous selection

Added in repair round 1 (round-1 adversarial audit, issue 3). At the matching-pennies fixed
point the value of `mpBR` is the whole square, so there the fixed-point property is `x* ∈ K`.
`wedgeF` is a one-dimensional correspondence on `Icc 0 1` whose unique fixed point `1` has the
singleton value `{1}`, and which still has no continuous selection: any selection is
`(x + 1)/2 → 3/4` from the left of `1/2` and `1` from the right. It is fed to `kakutani_findim`
directly on `ℝ`, and it gives `exists_approx_selection` a direct instance. -/

/-- The wedge correspondence on `Icc 0 1`: `{(x+1)/2}` for `x < 1/2`, `Icc (3/4) 1` at
`x = 1/2`, `{1}` for `x > 1/2`. Stated with non-strict inequalities so that the graph is a
finite union of closed sets; the three clauses agree at `1/2` (`wedgeF_half`).
Source: none: infrastructure (round-1 adversarial audit, issue 3)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def wedgeF (x : ℝ) : Set ℝ :=
  {y | (x ≤ 1 / 2 ∧ y = (x + 1) / 2) ∨ (x = 1 / 2 ∧ 3 / 4 ≤ y ∧ y ≤ 1) ∨ (1 / 2 ≤ x ∧ y = 1)}

/-- `wedgeF x = {(x + 1)/2}` for `x < 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_of_lt {x : ℝ} (hx : x < 1 / 2) : wedgeF x = {(x + 1) / 2} := by
  ext y
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd h hx.ne
    · exact absurd hx (not_lt.2 h)
  · intro h
    exact Or.inl ⟨hx.le, h⟩

/-- `wedgeF (1/2) = Icc (3/4) 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_half : wedgeF (1 / 2) = Icc (3 / 4) 1 := by
  ext y
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h1, h2⟩ | ⟨_, h⟩)
    · rw [h]; norm_num
    · exact ⟨h1, h2⟩
    · rw [h]; norm_num
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)

/-- `wedgeF x = {1}` for `x > 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_of_gt {x : ℝ} (hx : 1 / 2 < x) : wedgeF x = {1} := by
  ext y
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd hx (not_lt.2 h)
    · exact absurd h hx.ne'
    · exact h
  · intro h
    exact Or.inr (Or.inr ⟨hx.le, h⟩)

/-- `wedgeF` maps `Icc 0 1` into itself.
Source: none: infrastructure (hypothesis package of the second witness)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_maps : ∀ x ∈ Icc (0 : ℝ) 1, wedgeF x ⊆ Icc 0 1 := by
  intro x hx y hy
  rcases lt_trichotomy x (1 / 2) with h | rfl | h
  · rw [wedgeF_of_lt h, Set.mem_singleton_iff] at hy
    rw [hy]
    constructor <;> linarith [hx.1, hx.2]
  · rw [wedgeF_half] at hy
    exact ⟨by linarith [hy.1], hy.2⟩
  · rw [wedgeF_of_gt h, Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨zero_le_one, le_rfl⟩

/-- `wedgeF x` is nonempty on `Icc 0 1`.
Source: none: infrastructure (hypothesis package of the second witness)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_nonempty : ∀ x ∈ Icc (0 : ℝ) 1, (wedgeF x).Nonempty := by
  intro x _
  rcases lt_trichotomy x (1 / 2) with h | rfl | h
  · rw [wedgeF_of_lt h]; exact Set.singleton_nonempty _
  · rw [wedgeF_half]; exact Set.nonempty_Icc.2 (by norm_num)
  · rw [wedgeF_of_gt h]; exact Set.singleton_nonempty _

/-- `wedgeF x` is convex on `Icc 0 1` (a singleton, an interval, or a singleton).
Source: none: infrastructure (hypothesis package of the second witness)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_convex : ∀ x ∈ Icc (0 : ℝ) 1, Convex ℝ (wedgeF x) := by
  intro x _
  rcases lt_trichotomy x (1 / 2) with h | rfl | h
  · rw [wedgeF_of_lt h]; exact convex_singleton _
  · rw [wedgeF_half]; exact convex_Icc _ _
  · rw [wedgeF_of_gt h]; exact convex_singleton _

/-- `wedgeF` has a closed graph over `Icc 0 1`: the graph is `fst⁻¹ (Icc 0 1)` intersected with a
union of three sets, each cut out by non-strict inequalities and equations between continuous
functions of `(x, y)`.
Source: none: infrastructure (hypothesis package of the second witness)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_hasClosedGraphOn : HasClosedGraphOn wedgeF (Icc 0 1) := by
  unfold HasClosedGraphOn
  have h1 : IsClosed {p : ℝ × ℝ | p.1 ≤ 1 / 2 ∧ p.2 = (p.1 + 1) / 2} :=
    (isClosed_le continuous_fst continuous_const).inter
      (isClosed_eq continuous_snd (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 + 1) / 2))
  have h2 : IsClosed {p : ℝ × ℝ | p.1 = 1 / 2 ∧ 3 / 4 ≤ p.2 ∧ p.2 ≤ 1} :=
    (isClosed_eq continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const))
  have h3 : IsClosed {p : ℝ × ℝ | 1 / 2 ≤ p.1 ∧ p.2 = 1} :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_eq continuous_snd continuous_const)
  exact (isClosed_Icc.preimage continuous_fst).inter (h1.union (h2.union h3))

/-- The fixed points of `wedgeF` are exactly `x = 1`: `x = (x + 1)/2` forces `x = 1 > 1/2`,
`1/2 ∉ Icc (3/4) 1`, and on `x > 1/2` the value is `{1}`.
Source: none: infrastructure (second witness, uniqueness certificate)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem mem_wedgeF_self_iff {x : ℝ} : x ∈ wedgeF x ↔ x = 1 := by
  constructor
  · rintro (⟨h, hx⟩ | ⟨h, hx, _⟩ | ⟨_, hx⟩)
    · exfalso; linarith
    · exfalso; linarith
    · exact hx
  · rintro rfl
    exact Or.inr (Or.inr ⟨by norm_num, rfl⟩)

/-- At its fixed point `1` the value of `wedgeF` is the singleton `{1}` (contrast `mpBR`, whose
value at its fixed point is the whole square).
Source: none: infrastructure (second witness, singleton-value certificate)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_one : wedgeF 1 = {1} := wedgeF_of_gt (by norm_num)

/-- **N+ witness with a singleton-valued fixed point: Kakutani on `wedgeF`.** `wedgeF` satisfies
the full hypothesis package on `Icc 0 1 ⊆ ℝ` (`wedgeF_maps`, `wedgeF_nonempty`, `wedgeF_convex`,
`wedgeF_hasClosedGraphOn`), so `kakutani_findim` on `ℝ` yields a fixed point. Certificates:
`mem_wedgeF_self_iff` (the fixed point is exactly `1`), `wedgeF_one` (its value there is `{1}`),
and `wedgeF_no_continuous_selection` (no Brouwer instance hides inside).
Source: none: infrastructure (round-1 adversarial audit, issue 3)
Kind: N+
Fidelity: n/a
Hyps: none: the four hypotheses are theorems -/
theorem wedgeF_exists_fixed : ∃ x ∈ Icc (0 : ℝ) 1, x ∈ wedgeF x :=
  kakutani_findim isCompact_Icc (convex_Icc 0 1) (Set.nonempty_Icc.2 zero_le_one) wedgeF
    wedgeF_maps wedgeF_nonempty wedgeF_convex wedgeF_hasClosedGraphOn

/-- **No continuous selection of `wedgeF`.** A selection `g` has `g x = (x + 1)/2 < 3/4` for
`x < 1/2` and `g x = 1` for `x > 1/2`; by the intermediate value theorem on `Icc (1/4) (3/4)`
(`g (1/4) = 5/8`, `g (3/4) = 1`) it takes both values `13/16` and `15/16`, which it can only do at
`x = 1/2`.
Source: none: infrastructure (second witness, the no-selection clause)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem wedgeF_no_continuous_selection :
    ¬ ∃ g : ℝ → ℝ, ContinuousOn g (Icc 0 1) ∧ ∀ x ∈ Icc (0 : ℝ) 1, g x ∈ wedgeF x := by
  rintro ⟨g, hg_cont, hg_sel⟩
  have hI : Icc (1 / 4 : ℝ) (3 / 4) ⊆ Icc 0 1 := Icc_subset_Icc (by norm_num) (by norm_num)
  have h_lo : g (1 / 4) = 5 / 8 := by
    have := hg_sel (1 / 4) (by norm_num)
    rw [wedgeF_of_lt (by norm_num), Set.mem_singleton_iff] at this
    rw [this]; norm_num
  have h_hi : g (3 / 4) = 1 := by
    have := hg_sel (3 / 4) (by norm_num)
    rw [wedgeF_of_gt (by norm_num)] at this
    exact this
  have hivt := intermediate_value_Icc (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4) (hg_cont.mono hI)
  rw [h_lo, h_hi] at hivt
  have key : ∀ t ∈ Icc (1 / 4 : ℝ) (3 / 4), 3 / 4 < g t → g t ≠ 1 → t = 1 / 2 := by
    intro t ht h34 h1
    rcases lt_trichotomy t (1 / 2) with hlt | heq | hgt
    · exfalso
      have := hg_sel t (hI ht)
      rw [wedgeF_of_lt hlt, Set.mem_singleton_iff] at this
      rw [this] at h34
      linarith
    · exact heq
    · exfalso
      have := hg_sel t (hI ht)
      rw [wedgeF_of_gt hgt] at this
      exact h1 this
  obtain ⟨t₁, ht₁, ht₁v⟩ := hivt (⟨by norm_num, by norm_num⟩ : (13 / 16 : ℝ) ∈ Icc (5 / 8) 1)
  obtain ⟨t₂, ht₂, ht₂v⟩ := hivt (⟨by norm_num, by norm_num⟩ : (15 / 16 : ℝ) ∈ Icc (5 / 8) 1)
  have e₁ : t₁ = 1 / 2 := key t₁ ht₁ (by rw [ht₁v]; norm_num) (by rw [ht₁v]; norm_num)
  have e₂ : t₂ = 1 / 2 := key t₂ ht₂ (by rw [ht₂v]; norm_num) (by rw [ht₂v]; norm_num)
  rw [e₁] at ht₁v
  rw [e₂] at ht₂v
  rw [ht₁v] at ht₂v
  norm_num at ht₂v

/-- **Direct instance of `exists_approx_selection`** (round-1 adversarial audit, issue 4): on
`Icc 0 1` with `F = wedgeF`, every `ε > 0` admits a continuous self-map `f` of `Icc 0 1` with
`f x` in the convex hull of the values of `wedgeF` within `ε` of `x`. The full hypothesis package
of the lemma (compact convex domain, nonempty values in the domain) is inhabited by a
correspondence with no continuous selection, so the approximate selection is not an exact one.
Source: none: infrastructure (target 2, direct N+ instance)
Kind: N+
Fidelity: n/a
Hyps: none: the hypotheses are theorems -/
theorem wedgeF_approx_selection {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) ∧ MapsTo f (Icc 0 1) (Icc 0 1) ∧
      ∀ x ∈ Icc (0 : ℝ) 1,
        f x ∈ convexHull ℝ (⋃ x' ∈ Icc (0 : ℝ) 1 ∩ Metric.ball x ε, wedgeF x') :=
  exists_approx_selection isCompact_Icc (convex_Icc 0 1) wedgeF_maps wedgeF_nonempty hε

end Cleanroom.Found.FixKakutani
