import Cleanroom.Decision.DpCalibration.Witnesses

/-!
# The two-point fantasy tree and Transparent Newcomb: T2(b), T2(c)(iii), T9, T13

* `fantasy241` with `C = (out, y)`: `d₂`'s observation is decided upstream, so no local self-model
  realizes `O₂` — **the two readings of Definition 9 differ** (`fantasy_maskedOC_vacuity`,
  `fantasy_not_masked_letter`).
* Transparent Newcomb: **E6** — at `p = 1` with `C = (large, large)` the point `E` is null under
  every local self-model in V1 (`tnV1_E_null`, vacuous) but *calibrated, not vacuous* in V2
  (`tnV2_E_realized`: the self-model at the hypothetical `E`-node routes to the empty branch with
  probability `m(both) > 0`, and the real node's act-conditional is `m`); **Observation 1** (T9)
  on V2 with a perfect predictor and `C = (both, both)`: the state certain of fullness is strictly
  calibrated at `F` (vacuously: `ν(O_F) = 0`) and not per-run SSC at `F` (`occ(F)` is every run);
  **Corollary 9.1(ii)** (T13): for `0 < p < 1` every procedure (in particular all four
  deterministic policies) is masked-calibrated on V2(p) with the calibrated states
  `ν_{C[d↦m]}(· | O_F)`, `(· | O_E)` (`tnV2_maskedOC_all`); **(iii)** `(large, large)` makes `O_E`
  `(1−p)`-inconsistent in `Σ_{V2(p)}` at every sense (`tnV2_makesInconsistent`, kind `T`: `ν(O_E)`
  does not depend on the states).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## The fantasy tree `(2;4,1)` with `C = (out, y)`: the two readings differ -/

section fantasy

/-- `C = (out, y)`: `a` (out) at `p1`, `b` (y) at `p2`.
Source: `calibration.md` CA-1′(iii) ("`C = (out, y)` on `T₂`")
Kind: D -/
def procOutY : Proc Pt2 (fun _ => Act2) ℚ := Proc.ofFun fun | .p1 => .a | .p2 => .b

/-- A sum over the leaves of a two-point tree as three terms.
Source: none: infrastructure. Kind: L -/
theorem twoPoint_sum (rOut rX rY : ℚ) (f : (twoPoint rOut rX rY).Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩ := by
  unfold twoPoint at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  ring

/-- Under `(out, y)[p2 ↦ m]` the inner observation `O_{p2} = {in}` has probability `0` for
every `m`: it is decided upstream by `p1`'s answer `out`.
Source: `calibration.md` CA-1′(iii) ("`d₂` is free since `O₂` is decided upstream");
`v2-amendments.md` A5(b)
Kind: L -/
theorem fantasy_nu_p2_eq_zero (m : FinDistr ℚ Act2) :
    nu (procOutY.deviate .p2 m) fantasy241 (twoObs .p2) = 0 := by
  rw [nu_eq_sum]
  unfold fantasy241
  rw [twoPoint_sum]
  simp [twoObs, twoPoint, leafLaw_decision, world_decision, procOutY, Proc.deviate,
    Function.update_of_ne, Function.update_self]

/-- **Under the vacuity reading, `fantasy241` is masked-calibrated at `p2` for `(out, y)` with
any state** (no local self-model realizes `O₂`).
Source: `v2-amendments.md` A5(b) ("read as *unconstrained* … its state is free");
`calibration.md` CA-1′(iii)
Kind: N+
Fidelity: variant: null case read as vacuity (A5) -/
theorem fantasy_maskedOC_vacuity (s : Pt2 → State TwoW ℚ) :
    MaskedOCAt s twoObs procOutY fantasy241 .p2 := by
  refine Or.inr ⟨rfl, fun C' hC' => ?_⟩
  obtain ⟨m, -, rfl⟩ := hC'
  exact fantasy_nu_p2_eq_zero m

/-- **Under the letter reading, `fantasy241` is not masked-calibrated at `p2` for `(out, y)` with
any state** — the readings classify the tree oppositely.
Source: `v2-amendments.md` A5(b) ("the alternative, literal reading … classifies the two-point
tree … oppositely at the inner point")
Kind: N+
Fidelity: exact (v2's letter is `MaskedOCAtV … .LF .letter`) -/
theorem fantasy_not_masked_letter (s : Pt2 → State TwoW ℚ) :
    ¬ MaskedOCAtV s twoObs procOutY fantasy241 .LF .letter .p2 := by
  rintro (⟨C', ⟨m, -, rfl⟩, hpos, -⟩ | ⟨h, -⟩)
  · rw [fantasy_nu_p2_eq_zero] at hpos; exact lt_irrefl 0 hpos
  · cases h

/-- `p2` is queried on `fantasy241`. Source: none: infrastructure. Kind: L -/
theorem fantasy_p2_queried : Pt2.p2 ∈ queried fantasy241 := by
  unfold fantasy241 twoPoint
  simp [queried_decision, queried_leaf, Act2.univ_eq]

/-- Hence **`MaskedOCV .LF .letter` fails for `(out, y)` on `fantasy241` with every state**,
while the vacuity reading is available at `p2` with every state.
Source: `v2-amendments.md` A5(b); `calibration.md` CA-1′(iii)
Kind: N+ -/
theorem fantasy_readings_differ (s : Pt2 → State TwoW ℚ) :
    ¬ MaskedOCV s twoObs procOutY fantasy241 .LF .letter ∧
    MaskedOCAt s twoObs procOutY fantasy241 .p2 :=
  ⟨fun h => fantasy_not_masked_letter s (h .p2 fantasy_p2_queried), fantasy_maskedOC_vacuity s⟩

end fantasy

/-! ## Transparent Newcomb -/

section newcomb

/-- A sum over the leaves of `tnV2 p L S` as a fourfold sum.
Source: none: infrastructure. Kind: L -/
theorem tnV2_sum (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (f : (tnV2 p h0 h1 L S).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ x : Box, ∑ y : Box, ∑ i : Fin 2, ∑ act : Box, f ⟨x, y, i, act, ()⟩ := by
  unfold tnV2 tnReal at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- A sum over the leaves of `tnV1 p L S` as a threefold sum.
Source: none: infrastructure. Kind: L -/
theorem tnV1_sum (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (f : (tnV1 p h0 h1 L S).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ x : Box, ∑ i : Fin 2, ∑ act : Box, f ⟨x, i, act, ()⟩ := by
  unfold tnV1 tnReal at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The world at a leaf of V2. Source: none: infrastructure. Kind: L -/
theorem tnV2_world (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (x y : Box) (i : Fin 2)
    (act : Box) : world (tnV2 p h0 h1 L S) ⟨x, y, i, act, ()⟩ = (decide (i = 0), act) := by
  unfold tnV2 tnReal; simp

/-- The run law at a leaf of V2 as a product of weights. Source: none: infrastructure. Kind: L -/
theorem tnV2_leafLaw (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (C : Proc TnPt (fun _ => Box) ℚ) (x y : Box) (i : Fin 2) (act : Box) :
    leafLaw C (tnV2 p h0 h1 L S) ⟨x, y, i, act, ()⟩ =
      (C .F).w x * ((C .E).w y *
        ((![if x = .large ∧ y = .large then p else 1 - p,
            1 - (if x = .large ∧ y = .large then p else 1 - p)] i) *
          ((C (if i = 0 then .F else .E)).w act * 1))) := by
  unfold tnV2 tnReal
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf]
  rfl

/-- The world at a leaf of V1. Source: none: infrastructure. Kind: L -/
theorem tnV1_world (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (x : Box) (i : Fin 2)
    (act : Box) : world (tnV1 p h0 h1 L S) ⟨x, i, act, ()⟩ = (decide (i = 0), act) := by
  unfold tnV1 tnReal; simp

/-- The run law at a leaf of V1 as a product of weights. Source: none: infrastructure. Kind: L -/
theorem tnV1_leafLaw (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (C : Proc TnPt (fun _ => Box) ℚ) (x : Box) (i : Fin 2) (act : Box) :
    leafLaw C (tnV1 p h0 h1 L S) ⟨x, i, act, ()⟩ =
      (C .F).w x *
        ((![if x = .large then p else 1 - p, 1 - (if x = .large then p else 1 - p)] i) *
          ((C (if i = 0 then .F else .E)).w act * 1)) := by
  unfold tnV1 tnReal
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf]
  rfl

/-- The two-boxer `(both, both)`. Source: [[decision-problems-v2]] Observation 1. Kind: D -/
def procBoth : Proc TnPt (fun _ => Box) ℚ := Proc.ofFun fun _ => .both

/-- The one-boxer `(large, large)`. Source: [[decision-problems-v2]] Corollary 9.1. Kind: D -/
def procLarge : Proc TnPt (fun _ => Box) ℚ := Proc.ofFun fun _ => .large

/-- `occ(F)` on V2 is every run (the root queries `F`).
Source: [[decision-problems-v2]] Observation 1 ("`occ(d_F) = Leaves`")
Kind: L -/
theorem tnV2_occ_F (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    occ .F (tnV2 p h0 h1 L S) = Finset.univ := by
  ext ℓ
  unfold tnV2 at ℓ ⊢
  rcases ℓ with ⟨x, y, i, act, _⟩
  simp [count_decision]

/-- **Observation 1, the statistics**: on V2 with a perfect predictor (`p = 1`) and the
two-boxer, `ν(O_F) = 0`: every positive run ends in an empty-box world.
Source: [[decision-problems-v2]] §3.1 Observation 1 ("the runs end in empty-box worlds a.s.")
Kind: L -/
theorem tnV2_perfect_both_nu_F (L S : ℚ) :
    nu procBoth (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .F) = 0 := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw]
  simp [tnObs, procBoth]

/-- **Observation 1 (T9)**: on V2 with a perfect predictor and the two-boxer, the state certain
of fullness (`δ_{(1, large)}`, any desirability) is strictly calibrated at `F` — vacuously, as
`ν(O_F) = 0` — and **not** per-run SSC at `F`, where `occ(F)` is every run and the runs end in
empty-box worlds.
Source: [[decision-problems-v2]] §3.1 Observation 1
Kind: N+
Fidelity: exact (variant V2; V1 would do as well) -/
theorem tnV2_observation1 (L S v : ℚ) :
    StrictOCAt (fun _ => State.dirac (true, Box.large) v) tnObs procBoth
      (tnV2 1 (by norm_num) (by norm_num) L S) .F ∧
    ¬ PerRunSSCAt (fun _ => State.dirac (true, Box.large) v) procBoth
      (tnV2 1 (by norm_num) (by norm_num) L S) .F := by
  constructor
  · intro h
    rw [tnV2_perfect_both_nu_F] at h
    exact absurd h (lt_irrefl 0)
  · intro h
    have hocc := tnV2_occ_F 1 (by norm_num) (by norm_num) L S
    have hm : 0 < mass procBoth (tnV2 1 (by norm_num) (by norm_num) L S)
        (occ .F (tnV2 1 (by norm_num) (by norm_num) L S)) := by
      rw [hocc, mass_univ]; exact one_pos
    have h1 := (h hm).1 (tnObs .F)
    rw [hocc, mass_univ, Finset.inter_univ, mul_one] at h1
    have hnu : mass procBoth (tnV2 1 (by norm_num) (by norm_num) L S)
        (worldEv (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .F)) = 0 :=
      tnV2_perfect_both_nu_F L S
    rw [hnu, State.dirac_pr] at h1
    simp [tnObs] at h1

/-- **E6, the V1 half**: on V1 with `p = 1` and `C = (large, large)`, the point `E` has
probability `0` under every local self-model `C[E ↦ m]` — the full branch is certain because the
(unmasked) root answers `large`. So `E` is vacuous under Definition 9 in V1.
Source: `v2-amendments.md` E6 ("in V1 there is no hypothetical `d_E` node and vacuity holds")
Kind: N+ -/
theorem tnV1_E_null (L S : ℚ) (m : FinDistr ℚ Box) :
    nu (procLarge.deviate .E m) (tnV1 1 (by norm_num) (by norm_num) L S) (tnObs .E) = 0 := by
  rw [nu_eq_sum, tnV1_sum]
  simp only [tnV1_world, tnV1_leafLaw]
  simp [Box.sum_univ, Fin.sum_univ_two, tnObs, procLarge, Proc.deviate, Function.update_of_ne]

/-- Hence on V1 at `p = 1` the point `E` is masked-calibrated (vacuity) for `(large, large)`
with any state, and not under the letter.
Source: `v2-amendments.md` E6; [[decision-problems-v2]] Corollary 9.1 ("at `p = 1` the
unrealized observation is vacuous under Definitions 8–9")
Kind: N+
Fidelity: variant: null case read as vacuity (A5) -/
theorem tnV1_E_maskedOC_vacuity (L S : ℚ) (s : TnPt → State TnW ℚ) :
    MaskedOCAt s tnObs procLarge (tnV1 1 (by norm_num) (by norm_num) L S) .E ∧
    ¬ MaskedOCAtV s tnObs procLarge (tnV1 1 (by norm_num) (by norm_num) L S) .LF .letter .E := by
  constructor
  · refine Or.inr ⟨rfl, fun C' hC' => ?_⟩
    obtain ⟨m, -, rfl⟩ := hC'
    exact tnV1_E_null L S m
  · rintro (⟨C', ⟨m, -, rfl⟩, hpos, -⟩ | ⟨h, -⟩)
    · rw [tnV1_E_null] at hpos; exact lt_irrefl 0 hpos
    · cases h

/-- **E6, the V2 half**: on V2 with `p = 1` and `C = (large, large)`, the self-model `C[E ↦ m]`
acts at the hypothetical `E`-node too and sends the run to the empty branch with probability
`m(both)`: `ν_{C[E↦m]}(O_E) = m(both)`, and `ν_{C[E↦m]}(act = a ∧ O_E) = m(both) · m(a)`.
Source: `v2-amendments.md` E6 ("the hypothetical query routes the self-model into the empty
branch")
Kind: L -/
theorem tnV2_E_nu (L S : ℚ) (m : FinDistr ℚ Box) :
    nu (procLarge.deviate .E m) (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .E) = m.w .both ∧
    ∀ act, nu (procLarge.deviate .E m) (tnV2 1 (by norm_num) (by norm_num) L S)
      (tnActEv .E act ∩ tnObs .E) = m.w .both * m.w act := by
  have hsum := m.sum_one
  rw [Box.sum_univ] at hsum
  constructor
  · rw [nu_eq_sum, tnV2_sum]
    simp only [tnV2_world, tnV2_leafLaw]
    simp [Box.sum_univ, Fin.sum_univ_two, tnObs, procLarge, Proc.deviate, Function.update_of_ne]
    linear_combination m.w Box.both * hsum
  · intro act
    rw [nu_eq_sum, tnV2_sum]
    simp only [tnV2_world, tnV2_leafLaw]
    cases act <;>
      simp [Box.sum_univ, Fin.sum_univ_two, tnObs, tnActEv, procLarge, Proc.deviate,
        Function.update_of_ne]

/-- **E6 (T2(c)(iii))**: on V2 at `p = 1`, `E` is *calibrated, not vacuous*, for `(large, large)`:
with any full-support self-model `m`, `ν_{C[E↦m]}(O_E) = m(both) > 0`, and the calibrated state
at `E` — `ν_{C[E↦m]}(· | O_E)` — is a masked witness (`MaskedOCAt`) whose act-credences are
exactly `m`: `P_{s_E}(act = a) = m(a)`. Corollary 9.1's "vacuous under Definitions 8–9 at
`p = 1`" is wrong for V2.
Source: `v2-amendments.md` E6; [[decision-problems-v2]] Corollary 9.1 (line 246), refuted for V2
Kind: N+
Fidelity: exact -/
theorem tnV2_E_realized (L S : ℚ) (m : FinDistr ℚ Box) (hm : ∀ a, 0 < m.w a) :
    ∃ h : 0 < nu (procLarge.deviate .E m) (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .E),
      MaskedOCAt (fun _ => calibratedState (procLarge.deviate .E m)
          (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .E) h)
        tnObs procLarge (tnV2 1 (by norm_num) (by norm_num) L S) .E ∧
      ∀ act, (calibratedState (procLarge.deviate .E m)
          (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .E) h).pr (tnActEv .E act) = m.w act := by
  obtain ⟨hO, hact⟩ := tnV2_E_nu L S m
  have h : 0 < nu (procLarge.deviate .E m) (tnV2 1 (by norm_num) (by norm_num) L S) (tnObs .E) := by
    rw [hO]; exact hm .both
  refine ⟨h, maskedOCAt_calibratedState tnObs procLarge _ _ .E m hm h rfl, fun act => ?_⟩
  rw [calibratedState_pr, hact, hO]
  exact mul_div_cancel_left₀ (m.w act) (hm .both).ne'

/-- **Corollary 9.1(ii), the positivity behind it**: on V2(p) with `0 < p < 1`, for every
procedure `C` and every full-support self-model `m`, both lifted observations are realized:
`0 < ν_{C[F↦m]}(O_F)` and `0 < ν_{C[E↦m]}(O_E)`. (One positive leaf suffices for each.)
Source: [[decision-problems-v2]] §9 Corollary 9.1 ("Under masking, all four policies are
calibrated for `p < 1`")
Kind: L -/
theorem tnV2_deviations_realized (p : ℚ) (h0 : 0 < p) (h1 : p < 1) (L S : ℚ)
    (C : Proc TnPt (fun _ => Box) ℚ) (m : FinDistr ℚ Box) (hm : ∀ a, 0 < m.w a) :
    0 < nu (C.deviate .F m) (tnV2 p h0.le h1.le L S) (tnObs .F) ∧
    0 < nu (C.deviate .E m) (tnV2 p h0.le h1.le L S) (tnObs .E) := by
  obtain ⟨yE, hyE⟩ := FinDistr.exists_pos_w' (C .E)
  obtain ⟨xF, hxF⟩ := FinDistr.exists_pos_w' (C .F)
  constructor
  · -- the leaf `⟨both, yE, 0, large, ()⟩`: full box with probability `1 − p > 0`
    have hleaf : 0 < leafLaw (C.deviate .F m) (tnV2 p h0.le h1.le L S) ⟨.both, yE, 0, .large, ()⟩ := by
      rw [tnV2_leafLaw]
      simp [Proc.deviate, Function.update_self, Function.update_of_ne]
      have := hm .both; have := hm .large; have : 0 < 1 - p := by linarith
      positivity
    rw [nu_eq_sum]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun ℓ _ => ?_)
      (Finset.mem_univ ⟨.both, yE, 0, .large, ()⟩))
    · rw [if_pos]
      · exact hleaf
      · rw [tnV2_world]; simp [tnObs]
    · split_ifs
      · exact leafLaw_nonneg _ _ _
      · exact le_rfl
  · -- the leaf `⟨xF, both, 1, large, ()⟩`: empty box with probability `p > 0`
    have hleaf : 0 < leafLaw (C.deviate .E m) (tnV2 p h0.le h1.le L S) ⟨xF, .both, 1, .large, ()⟩ := by
      rw [tnV2_leafLaw]
      simp [Proc.deviate, Function.update_self, Function.update_of_ne]
      have := hm .both; have := hm .large
      positivity
    rw [nu_eq_sum]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun ℓ _ => ?_)
      (Finset.mem_univ ⟨xF, .both, 1, .large, ()⟩))
    · rw [if_pos]
      · exact hleaf
      · rw [tnV2_world]; simp [tnObs]
    · split_ifs
      · exact leafLaw_nonneg _ _ _
      · exact le_rfl

/-- The queried points of V2(p) are `F` and `E`. Source: none: infrastructure. Kind: L -/
theorem tnV2_queried (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (d : TnPt) :
    d ∈ queried (tnV2 p h0 h1 L S) := by
  unfold tnV2 tnReal
  cases d <;> simp [queried_decision, queried_chance, queried_leaf]

/-- **Corollary 9.1(ii)**: on V2(p) with `0 < p < 1`, *every* procedure — in particular all four
deterministic policies — is masked-calibrated with the calibrated states `ν_{C[F↦m]}(· | O_F)`
at `F` and `ν_{C[E↦m]}(· | O_E)` at `E` (for any full-support self-model `m`).
Source: [[decision-problems-v2]] §9 Corollary 9.1 ("Under masking, all four policies are
calibrated for `p < 1`")
Kind: N+
Fidelity: stronger (every procedure, not only the four deterministic ones); `0 < p` added — at
`p = 0` the point `E` is unrealizable for `x = both` and the vacuity case applies instead -/
theorem tnV2_maskedOC_all (p : ℚ) (h0 : 0 < p) (h1 : p < 1) (L S : ℚ)
    (C : Proc TnPt (fun _ => Box) ℚ) (m : FinDistr ℚ Box) (hm : ∀ a, 0 < m.w a) :
    ∃ s : TnPt → State TnW ℚ, MaskedOC s tnObs C (tnV2 p h0.le h1.le L S) ∧
      (∃ hF, s .F = calibratedState (C.deviate .F m) (tnV2 p h0.le h1.le L S) (tnObs .F) hF) ∧
      (∃ hE, s .E = calibratedState (C.deviate .E m) (tnV2 p h0.le h1.le L S) (tnObs .E) hE) := by
  obtain ⟨hF, hE⟩ := tnV2_deviations_realized p h0 h1 L S C m hm
  refine ⟨fun d => match d with
    | .F => calibratedState (C.deviate .F m) (tnV2 p h0.le h1.le L S) (tnObs .F) hF
    | .E => calibratedState (C.deviate .E m) (tnV2 p h0.le h1.le L S) (tnObs .E) hE,
    fun d _ => ?_, ⟨hF, rfl⟩, ⟨hE, rfl⟩⟩
  cases d
  · exact maskedOCAt_calibratedState tnObs C _ _ .F m hm hF rfl
  · exact maskedOCAt_calibratedState tnObs C _ _ .E m hm hE rfl

/-- `ν_{(large,large)}(O_E) = 1 − p` on V2(p), for any states.
Source: [[decision-problems-v2]] Remark 3.13 ("the both-cases one-boxer makes `{seen = E}`
`(1−p)`-inconsistent")
Kind: L -/
theorem tnV2_large_nu_E (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    nu procLarge (tnV2 p h0 h1 L S) (tnObs .E) = 1 - p := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw]
  simp [Fin.sum_univ_two, tnObs, procLarge]

/-- The abstract problem `Σ_{V2(p)}`: every state assignment on the tree `tnV2 p L S`.
Source: [[decision-problems-v2]] Remark 3.13 ("Transparent Newcomb V2(p)")
Kind: D -/
def sigmaV2 (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) : AbstractProblem TnW TnPt (fun _ => Box) ℚ :=
  {I | I.B = tnV2 p h0 h1 L S}

/-- **Corollary 9.1(iii) / Remark 3.13**: `(large, large)` makes `O_E` `(1−p)`-inconsistent in
`Σ_{V2(p)}` at every calibration sense. Kind `T`: `ν(O_E) = 1 − p` regardless of the states, so
the calibration hypothesis does no work — not a headline.
Source: [[decision-problems-v2]] §3.2 Remark 3.13; §9 Corollary 9.1 ("relative to the V2
abstract problem, `(1,1)` makes `O_E` `(1−p)`-inconsistent")
Kind: T
Fidelity: exact -/
theorem tnV2_makesInconsistent (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (κ : Sense) :
    MakesInconsistent κ tnObs (sigmaV2 p h0 h1 L S) procLarge (tnObs .E) (1 - p) := by
  intro I hI _
  simp only [sigmaV2, Set.mem_setOf_eq] at hI
  rw [hI, tnV2_large_nu_E]

end newcomb

end Cleanroom.Decision.DpCalibration
