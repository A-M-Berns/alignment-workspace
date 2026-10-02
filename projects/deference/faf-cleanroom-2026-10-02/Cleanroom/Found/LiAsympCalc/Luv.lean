import Cleanroom.Found.LiAsympCalc.Defs
import LogicalInduction.Properties.TimelyLearning

/-!
# G. LUV-combination wrappers and the determinacy bridges

Targets G1–G3 of [[li-asymp-calc-mandate]], over FAF's `LUVCombination`
(`Properties/ExpectationProperties.lean`; `expect A P n = A.expectAt P (n+1) n`).

* G1: `ofLUV`, `affineImage α β`, `scaleByFeature g` expect as they should (`α · 𝔼 + β`,
  `g · 𝔼`), and `WorldValued` / `LUVCombination.DeterminedViaTheory` pass through
  `affineImage` with `truth ↦ α · truth + β`. Of `BoundedSequence`'s two fields only `bounded`
  transfers by arithmetic (`l1Norm` laws below); the `poly` field is an emission certificate for
  the mesh and needs one for `g` — not done, see the report.
* G2 (ii): the feature scalar pulls out exactly (`scaleByFeature_expect`). (iii) A LUV scalar
  `X · c_n` is **not** a `LUVCombination`; recorded in the report, not formalized.
* G3: from `LUV.DeterminedVia X DP y`: (a) `WorldValued` of `ofLUV`; (b) `DeterminedViaTheory`
  of `ofLUV` at `y` (uniqueness is FAF's `PCWorld.ValuesAt.eq`); (c) the precision-`(n+1)` mesh
  of `ofLUV (X n)` is `ApproxDeterminedViaTheory` at `y` with error `1/(n+1)` (FAF's
  `PCWorld.expectApprox_near_ofGrid`), and **exactly** determined at the grid-rounded truth
  `(n+1)⁻¹ · #{i < n+1 : i/(n+1) < y n}` only under an **off-grid** hypothesis (finding: a
  threshold equal to `y n` is unconstrained by `ValuesAt`, so the mandate's unconditional
  "exact" claim is false on the grid); (d) threshold-wise affine determinacy of
  `sentenceAffine ((X n).gt r)` at a coherent `τ` gives `DeterminedVia`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology

/-! ### G1. Expectations and values of the wrappers -/

/-- `(ofLUV X).expect P n = X.expect P n`.
Source: [[li-deference]] line 92; root-deference-2-003
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ofLUV_expect (X : LUV) (P : History) (n : ℕ) :
    (LUVCombination.ofLUV X).expect P n = X.expect P n := by
  simp only [LUVCombination.ofLUV, LUVCombination.expect, LUVCombination.expectAt, LUV.expect,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- `(affineImage α β X).expect P n = α · X.expect P n + β`.
Source: [[li-deference]] line 92; [[faithful-acceleration]] §5 line 113
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem affineImage_expect (α β : ℚ) (X : LUV) (P : History) (n : ℕ) :
    (LUVCombination.affineImage α β X).expect P n = α * X.expect P n + β := by
  simp only [LUVCombination.affineImage, LUVCombination.expect, LUVCombination.expectAt,
    LUV.expect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  ring

/-- **G2 (ii)**: a feature scalar pulls out exactly:
`(scaleByFeature g X).expect P n = g.denote P · X.expect P n`.
Source: root-fa-008; [[faithful-acceleration]] §5 line 113
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scaleByFeature_expect (g : EF) (X : LUV) (P : History) (n : ℕ) :
    (LUVCombination.scaleByFeature g X).expect P n = g.denote P * X.expect P n := by
  simp only [LUVCombination.scaleByFeature, LUVCombination.expect, LUVCombination.expectAt,
    LUV.expect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- Value of `ofLUV X` under a LUV valuation `ν`: `ν X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem ofLUV_value (X : LUV) (P : History) (ν : LUV → ℝ) :
    (LUVCombination.ofLUV X).value P ν = ν X := by
  simp only [LUVCombination.ofLUV, LUVCombination.value, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- Value of `affineImage α β X` under `ν`: `α · ν X + β`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem affineImage_value (α β : ℚ) (X : LUV) (P : History) (ν : LUV → ℝ) :
    (LUVCombination.affineImage α β X).value P ν = α * ν X + β := by
  simp only [LUVCombination.affineImage, LUVCombination.value, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  ring

/-- Value of `scaleByFeature g X` under `ν`: `g.denote P · ν X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem scaleByFeature_value (g : EF) (X : LUV) (P : History) (ν : LUV → ℝ) :
    (LUVCombination.scaleByFeature g X).value P ν = g.denote P * ν X := by
  simp only [LUVCombination.scaleByFeature, LUVCombination.value, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- A world values the singleton combination `ofLUV X` at `ν` iff it values `X` at `ν X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem valuesAt_ofLUV_iff (v : PCWorld) (X : LUV) (ν : LUV → ℝ) :
    (LUVCombination.ofLUV X).ValuesAt v ν ↔ v.ValuesAt X (ν X) := by
  simp [LUVCombination.ValuesAt, LUVCombination.ofLUV]

/-- Same for `affineImage`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem valuesAt_affineImage_iff (α β : ℚ) (v : PCWorld) (X : LUV) (ν : LUV → ℝ) :
    (LUVCombination.affineImage α β X).ValuesAt v ν ↔ v.ValuesAt X (ν X) := by
  simp [LUVCombination.ValuesAt, LUVCombination.affineImage]

/-- Same for `scaleByFeature`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem valuesAt_scaleByFeature_iff (g : EF) (v : PCWorld) (X : LUV) (ν : LUV → ℝ) :
    (LUVCombination.scaleByFeature g X).ValuesAt v ν ↔ v.ValuesAt X (ν X) := by
  simp [LUVCombination.ValuesAt, LUVCombination.scaleByFeature]

/-! ### `l1Norm` / `shareNorm` of the wrappers (the `bounded` half of `BoundedSequence`) -/

/-- `shareNorm (ofLUV X) = 1`, `l1Norm = 1`.
Source: [[li-asymp-calc-mandate]] G1 (`BoundedSequence.bounded`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem l1Norm_ofLUV (X : LUV) (P : History) :
    (LUVCombination.ofLUV X).shareNorm P = 1 ∧ (LUVCombination.ofLUV X).l1Norm P = 1 := by
  simp [LUVCombination.ofLUV, LUVCombination.shareNorm, LUVCombination.l1Norm]

/-- `l1Norm (affineImage α β X) = |β| + |α|`.
Source: [[li-asymp-calc-mandate]] G1 (`BoundedSequence.bounded`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem l1Norm_affineImage (α β : ℚ) (X : LUV) (P : History) :
    (LUVCombination.affineImage α β X).l1Norm P = |(β : ℝ)| + |(α : ℝ)| := by
  simp [LUVCombination.affineImage, LUVCombination.shareNorm, LUVCombination.l1Norm]

/-- `l1Norm (scaleByFeature g X) = |g.denote P|`: bounded iff `g` is.
Source: [[li-asymp-calc-mandate]] G1 (`BoundedSequence.bounded`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem l1Norm_scaleByFeature (g : EF) (X : LUV) (P : History) :
    (LUVCombination.scaleByFeature g X).l1Norm P = |g.denote P| := by
  simp [LUVCombination.scaleByFeature, LUVCombination.shareNorm, LUVCombination.l1Norm]

/-! ### G3 (a), (b) and the `affineImage` transfers -/

/-- **G3 (a)**: per-world values for every `X n` give `WorldValued` of the `ofLUV` sequence.
Feeds FAF's `wubexp`, `recurringunbiasednessexp`, `lic_expect_combination_provind_*`
(together with (b) and `hshare`).
Source: [[li-asymp-calc-mandate]] G3 (a)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem worldValued_ofLUV {X : ℕ → LUV} {DP : DeductiveProcess}
    (h : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ y, v.ValuesAt (X n) y) :
    LUVCombination.WorldValued (fun n => LUVCombination.ofLUV (X n)) DP := by
  intro n v hv
  obtain ⟨y, hy⟩ := h n v hv
  exact ⟨fun _ => y, (valuesAt_ofLUV_iff v (X n) _).2 hy⟩

/-- **G3 (a)** from `DeterminedVia`.
Source: [[li-asymp-calc-mandate]] G3 (a)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DeterminedVia.worldValued_ofLUV {X : ℕ → LUV} {y : ℕ → ℝ} {DP : DeductiveProcess}
    (h : ∀ n, LUV.DeterminedVia (X n) DP (y n)) :
    LUVCombination.WorldValued (fun n => LUVCombination.ofLUV (X n)) DP :=
  Cleanroom.Found.LiAsympCalc.worldValued_ofLUV (fun n v hv => Exists.intro (y n) (h n v hv))

/-- **G3 (b)**: `DeterminedVia (X n) DP (y n)` for all `n` gives FAF's
`LUVCombination.DeterminedViaTheory` of the `ofLUV` sequence at `y` (uniqueness of the valued
real is FAF's `PCWorld.ValuesAt.eq`).
Source: [[li-asymp-calc-mandate]] G3 (b)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DeterminedVia.determinedViaTheory_ofLUV {X : ℕ → LUV} {y : ℕ → ℝ}
    {DP : DeductiveProcess} (P : History) (h : ∀ n, LUV.DeterminedVia (X n) DP (y n)) :
    LUVCombination.DeterminedViaTheory (fun n => LUVCombination.ofLUV (X n)) P DP y := by
  intro n v ν hv hval
  rw [ofLUV_value]
  exact ((valuesAt_ofLUV_iff v (X n) ν).1 hval).eq (h n v hv)

/-- `WorldValued` passes through `affineImage`.
Source: [[li-asymp-calc-mandate]] G1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem worldValued_affineImage (α β : ℚ) {X : ℕ → LUV} {DP : DeductiveProcess}
    (h : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ y, v.ValuesAt (X n) y) :
    LUVCombination.WorldValued (fun n => LUVCombination.affineImage α β (X n)) DP := by
  intro n v hv
  obtain ⟨y, hy⟩ := h n v hv
  exact ⟨fun _ => y, (valuesAt_affineImage_iff α β v (X n) _).2 hy⟩

/-- `DeterminedViaTheory` passes through `affineImage` with `truth ↦ α · truth + β`.
Source: [[li-asymp-calc-mandate]] G1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DeterminedVia.determinedViaTheory_affineImage (α β : ℚ) {X : ℕ → LUV} {y : ℕ → ℝ}
    {DP : DeductiveProcess} (P : History) (h : ∀ n, LUV.DeterminedVia (X n) DP (y n)) :
    LUVCombination.DeterminedViaTheory (fun n => LUVCombination.affineImage α β (X n)) P DP
      (fun n => α * y n + β) := by
  intro n v ν hv hval
  rw [affineImage_value, ((valuesAt_affineImage_iff α β v (X n) ν).1 hval).eq (h n v hv)]

/-! ### G3 (c). The precision-`(n+1)` mesh of `ofLUV` -/

/-- The mesh of `ofLUV X` at precision `k` is valued at `X.expectApprox w k`.
Source: none: infrastructure (FAF `LUVCombination.meshAffine_value`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem meshAffine_ofLUV_value (X : LUV) (P : History) (w : Valuation) (k : ℕ) :
    ((LUVCombination.ofLUV X).meshAffine k).value P w = X.expectApprox w k := by
  simp only [LUVCombination.meshAffine_value, ofLUV_value]

/-- **G3 (c), approximate**: `DeterminedVia (X n) DP (y n)` makes the precision-`(n+1)` mesh
of `ofLUV (X n)` `ApproxDeterminedViaTheory` at `y` with error `1/(n+1)` — "exact per-LUV
determinacy ⟹ approximate mesh determinacy with the `conluvapprox` cost", FAF's
`PCWorld.expectApprox_near_ofGrid`. Feeds `lic_wubaff` / `affine_provind_theory_*`.
Source: [[li-asymp-calc-mandate]] G3 (c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DeterminedVia.approxDetermined_mesh_ofLUV {X : ℕ → LUV} {y : ℕ → ℝ}
    {DP : DeductiveProcess} (P : History) (h : ∀ n, LUV.DeterminedVia (X n) DP (y n)) :
    AffineCombination.ApproxDeterminedViaTheory
      (fun n => (LUVCombination.ofLUV (X n)).meshAffine (n + 1)) P DP y
      (fun n => 1 / ((n : ℝ) + 1)) := by
  intro n v hv
  simp only [meshAffine_ofLUV_value]
  have hval := h n v hv
  have hgrid : ∀ i : ℕ, i < n + 1 →
      (((i : ℝ) / ((n + 1 : ℕ) : ℝ) < y n → v.Holds ((X n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)))) ∧
        (y n < (i : ℝ) / ((n + 1 : ℕ) : ℝ) →
          ¬ v.Holds ((X n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))))) := by
    intro i _
    have hc : (((i : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have := hval.2.2 ((i : ℚ) / ((n + 1 : ℕ) : ℚ))
    rw [hc] at this
    exact this
  have := PCWorld.expectApprox_near_ofGrid hval.1 hval.2.1 (Nat.succ_pos n) hgrid
  push_cast at this
  exact this

/-- **G3 (c), exact off the grid**: if no grid point `i/(n+1)` with `i ≤ n` (the grid
`expectApprox` reads at precision `n+1`) equals `y n`, the mesh of `ofLUV (X n)` is *exactly*
determined at the grid-rounded truth `(n+1)⁻¹ · #{i < n+1 : i/(n+1) < y n}`. On the grid the
claim fails: `ValuesAt` leaves a threshold equal to `y n` unconstrained, so completed worlds
may disagree by `1/(n+1)` — and do: `not_determined_mesh_ofLUV_onGrid` below exhibits `y ≡ 0`
with no exactly determining truth stream at all. The hypothesis is restricted to `i ≤ n` so
that `y n = 1` (not a grid point) is not excluded (audit round 1, adversarial N3).
Source: [[li-asymp-calc-mandate]] G3 (c) (corrected: off-grid hypothesis added)
Kind: L
Fidelity: weaker: off-grid hypothesis, which the mandate's statement lacks and needs
Hyps: (a) none -/
theorem DeterminedVia.determined_mesh_ofLUV_offGrid {X : ℕ → LUV} {y : ℕ → ℝ}
    {DP : DeductiveProcess} (P : History) (h : ∀ n, LUV.DeterminedVia (X n) DP (y n))
    (hoff : ∀ n (i : ℕ), i ≤ n → (i : ℝ) / ((n + 1 : ℕ) : ℝ) ≠ y n) :
    AffineCombination.DeterminedViaTheory
      (fun n => (LUVCombination.ofLUV (X n)).meshAffine (n + 1)) P DP
      (fun n => (((n + 1 : ℕ) : ℝ))⁻¹ *
        ((Finset.range (n + 1)).filter
          (fun i : ℕ => (i : ℝ) / ((n + 1 : ℕ) : ℝ) < y n)).card) := by
  intro n v hv
  simp only [meshAffine_ofLUV_value, LUV.expectApprox]
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hval := h n v hv
  have hc : (((i : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hthr := hval.2.2 ((i : ℚ) / ((n + 1 : ℕ) : ℚ))
  rw [hc] at hthr
  unfold PCWorld.payout
  by_cases hlt : (i : ℝ) / ((n + 1 : ℕ) : ℝ) < y n
  · rw [if_pos (hthr.1 hlt), if_pos hlt]
  · have hgt : y n < (i : ℝ) / ((n + 1 : ℕ) : ℝ) :=
      lt_of_le_of_ne (not_lt.1 hlt) (hoff n i hi').symm
    rw [if_neg (hthr.2 hgt), if_neg hlt]

/-! ### G3 (c), refutation on the grid -/

/-- The empty deductive process: nothing is ever revealed, so every world is consistent with it.
Source: none: infrastructure (FAF `DeductiveProcess`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def DeductiveProcess.empty : DeductiveProcess := ⟨fun _ => ∅, fun _ => Finset.Subset.refl _⟩

/-- Every world is consistent with the empty deductive process.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma consistentWithTheory_empty (v : PCWorld) : v.ConsistentWithTheory DeductiveProcess.empty :=
  fun _ φ hφ => absurd hφ (Finset.notMem_empty φ)

/-- The grid LUV: `⌜X > r⌝` is `⊤` for `r < 0`, `⊥` for `r > 0`, and the atom `0` at `r = 0`.
Every world values it at `0` (FAF's `ValuesAt` never looks at the threshold equal to the value),
but its precision-`1` mesh is the payout of the atom, which worlds disagree on.
Source: [[li-asymp-calc-findings]] 9
Kind: D
Fidelity: n/a
Hyps: n/a -/
def gridLUV : LUV :=
  ⟨fun r => if r < 0 then (⊤ : Sentence) else if 0 < r then LO.Propositional.Formula.falsum
    else LO.Propositional.Formula.atom 0⟩

/-- Every world values `gridLUV` at `0`.
Source: [[li-asymp-calc-findings]] 9
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma gridLUV_valuesAt (v : PCWorld) : v.ValuesAt gridLUV 0 := by
  refine ⟨le_rfl, zero_le_one, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have hr' : r < 0 := by exact_mod_cast hr
    simp only [gridLUV, if_pos hr']
    exact PCWorld.holds_top v
  · have hr' : 0 < r := by exact_mod_cast hr
    simp only [gridLUV, if_neg (not_lt.2 hr'.le), if_pos hr']
    intro h
    exact h

/-- **G3 (c) is false on the grid** (refutation of the mandate's unconditional claim): with
`X n = gridLUV` and `y n = 0` (a grid point of every precision), every world values `X n` at
`y n` — so `DeterminedVia` holds for the empty deductive process — and yet **no** truth stream
makes the precision-`(n+1)` mesh of `ofLUV (X n)` exactly `DeterminedViaTheory`: the worlds
`fun _ => True` and `fun _ => False` are both consistent and value the day-`0` mesh at `1` and
`0`. So the off-grid hypothesis of `determined_mesh_ofLUV_offGrid` is needed, not decorative, and
the approximate form `approxDetermined_mesh_ofLUV` is the best unconditional statement.
Source: [[li-asymp-calc-mandate]] G3 (c); [[li-asymp-calc-findings]] 9
Kind: P
Fidelity: stronger: refutes exact determination at *every* truth stream, not only the grid-rounded one
Hyps: (a) none -/
theorem not_determined_mesh_ofLUV_onGrid (P : History) :
    (∀ n : ℕ, LUV.DeterminedVia ((fun _ : ℕ => gridLUV) n) DeductiveProcess.empty
        ((fun _ : ℕ => (0 : ℝ)) n)) ∧
      ¬ ∃ truth : ℕ → ℝ, AffineCombination.DeterminedViaTheory
        (fun n : ℕ => (LUVCombination.ofLUV ((fun _ : ℕ => gridLUV) n)).meshAffine (n + 1)) P
        DeductiveProcess.empty truth := by
  refine ⟨fun _ v _ => gridLUV_valuesAt v, ?_⟩
  rintro ⟨truth, htruth⟩
  have h1 := htruth 0 (fun _ => True) (consistentWithTheory_empty _)
  have h0 := htruth 0 (fun _ => False) (consistentWithTheory_empty _)
  simp only [meshAffine_ofLUV_value, LUV.expectApprox, zero_add, Finset.sum_range_one,
    Nat.cast_zero, zero_div, Nat.cast_one, inv_one, one_mul] at h1 h0
  have hgt : gridLUV.gt 0 = LO.Propositional.Formula.atom 0 := by
    simp [gridLUV]
  rw [hgt] at h1 h0
  simp only [PCWorld.payout, PCWorld.holds_atom] at h1 h0
  rw [if_pos trivial] at h1
  rw [if_neg (fun h => h)] at h0
  linarith

/-! ### G3 (d). From threshold-wise affine determinacy to `DeterminedVia` -/

/-- The one-share affine combination of a sentence is valued at the sentence's payout.
Source: none: infrastructure (FAF `AffineCombination.sentenceAffine`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sentenceAffine_value_payout (φ : ℕ → Sentence) (n : ℕ) (P : History) (v : PCWorld) :
    (AffineCombination.sentenceAffine φ n).value P v.payout = v.payout (φ n) := by
  simp [AffineCombination.sentenceAffine, AffineCombination.value]

/-- If every completed world pays `τ r` on `X.gt r`, and `τ` is threshold-coherent around
`y ∈ [0,1]` (`1` strictly below `y`, `0` strictly above), then `X` is `DeterminedVia` at `y`.
Source: [[li-asymp-calc-mandate]] G3 (d)
Kind: L
Fidelity: variant: `y` is supplied with its coherence, not constructed from `τ`
Hyps: (a) none -/
theorem determinedVia_of_thresholds {X : LUV} {DP : DeductiveProcess} {τ : ℚ → ℝ} {y : ℝ}
    (hy : 0 ≤ y ∧ y ≤ 1)
    (hτ : ∀ v : PCWorld, v.ConsistentWithTheory DP → ∀ r : ℚ, v.payout (X.gt r) = τ r)
    (hcoh : ∀ r : ℚ, ((r : ℝ) < y → τ r = 1) ∧ (y < r → τ r = 0)) :
    LUV.DeterminedVia X DP y := by
  intro v hv
  refine ⟨hy.1, hy.2, fun r => ⟨fun hr => ?_, fun hr hholds => ?_⟩⟩
  · have := hτ v hv r
    rw [(hcoh r).1 hr] at this
    unfold PCWorld.payout at this
    by_contra hnot
    rw [if_neg hnot] at this
    norm_num at this
  · have := hτ v hv r
    rw [(hcoh r).2 hr] at this
    unfold PCWorld.payout at this
    rw [if_pos hholds] at this
    norm_num at this

/-- **G3 (d)**: `AffineCombination.DeterminedViaTheory` of the one-share combinations
`sentenceAffine ((X ·).gt r)` at `τ · r`, for every rational `r`, with `τ` coherent around a
`[0,1]`-valued `y`, gives `DeterminedVia (X n) DP (y n)` for every `n` — hence (b).
Source: [[li-asymp-calc-mandate]] G3 (d)
Kind: L
Fidelity: variant: `y` supplied with its coherence
Hyps: (a) none -/
theorem determinedVia_of_sentenceAffine_determined {X : ℕ → LUV} {DP : DeductiveProcess}
    (P : History) {τ : ℕ → ℚ → ℝ} {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n ∧ y n ≤ 1)
    (hdet : ∀ r : ℚ, AffineCombination.DeterminedViaTheory
      (fun n => AffineCombination.sentenceAffine (fun m => (X m).gt r) n) P DP (fun n => τ n r))
    (hcoh : ∀ n (r : ℚ), ((r : ℝ) < y n → τ n r = 1) ∧ (y n < r → τ n r = 0)) :
    ∀ n, LUV.DeterminedVia (X n) DP (y n) := fun n =>
  determinedVia_of_thresholds (hy n)
    (fun v hv r => by
      have := hdet r n v hv
      rwa [sentenceAffine_value_payout] at this)
    (hcoh n)

end Cleanroom.Found.LiAsympCalc
