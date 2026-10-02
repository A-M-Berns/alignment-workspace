import Cleanroom.Bli.BliFinite.Witness
import Cleanroom.Bli.BliFinite.FaceCoherent
import Cleanroom.Bli.BliFinite.Bridge
import Cleanroom.Bli.BliSuperbelief.Face
import Cleanroom.Bli.BliSuperbelief.Expr
import Cleanroom.Bli.BliSuperbelief.Boundary
import Cleanroom.Bli.BliSuperbelief.Dogmatism
import Cleanroom.Bli.BliSuperbelief.CoherentGrid

/-!
# `bli-superbelief` · Witnesses: the non-vacuity instances

Every headline's hypothesis package inhabited, on `bli-finite`'s reused objects (never
reinvented): `witIndex`/`witMesh`/`t₀`/`t₀'`/`Q₁` (`d = 2`, `S 0 = {p}`, `S 1 = {p, q}`) and
`extIndex`/`extMesh`/`extT`/`extQ₀` (`d = 2`, `S = {p, q, p ⋏ q}`, the coherent grid).

* **E1** on a **non-product** carrier: `G := coherentGrid extIndex 2 1 ∅ 2`, `t := extT =
  (1/2, 1/2, 0)`. The day-1 tables `ext1 = (1,0,0)` and `ext2 = (0,1,0)` are on `G` and average
  to `extT` (`extF`, the two-point balance solution), so both lie in `faceGen G extT`, while
  `extQ₀ = 0` does not (`bli-finite`); `face_witness` exhibits E1(i)'s full-support solution
  charging `ext1`, `ext2` and not `extQ₀`, and E1(ii)'s `ε = 1` for `ext1` (`ext1_backaway`, an
  independent route into the face) and its failure for `extQ₀` (`extQ₀_no_backaway`). N+: a face
  with ≥ 2 points, positive mass on each, `d = 2`, non-product carrier.
* **E2**: `tentExpr₁ witMesh 0 Q₁` denotes `1/9` at the history with `p ↦ 1/2` (through the
  theorem and `bli-finite`'s `tentLaw_t₀`, and again by direct unfolding of FAF's `denoteRat` on
  the whole pinned product `tentExpr₁_direct`, coordinate list `[p, q]` by `sort_S1`); the
  coordinate term `mix3E (price p 0) 0 (1/3) 0`
  denotes `1/3` there by direct unfolding of FAF's `denoteRat`; the horizon-2 term at the table
  `(1/2, 1/2)` denotes `1/81` (`tentExpr_two_witness`), with the horizon-2 constants
  `(0, 1/9, 0)` at `v = 1/2` computed by recursion through the mesh (`chainFrom_two_half`).
* **E5**: N− for the printed grid at `d = 2`, `t ⊥ = 0`; (b) at `t₀' = (p ↦ 0)`; (c) the tent
  kernel at `t₀'`: face of 3 points, mass `1/3` each, `Q₁ = (1/2, 0)` off the face with mass `0`.
* **E6**: a hand-built belief-state sequence (`p` unlisted on day 0, listed at `1/2` on day 1)
  over `witIndex`, `d = 2`: the day-0 table is `t₀'`, the realized day-1 state is `Q₁`, off the
  face, null under every balanced superbelief, while the face has 3 points of positive tent
  mass — the support-entry mechanism of E6(d) in the finite layer, N+.
* **E7**: the two-point solution on the coherent grid forces `extT` coherent
  (`extT_coherent`, by the theorem); the contrast `ext11 = (1, 1, 0)` is charged by the
  product-grid tent kernel at `extT` and is incoherent for every `B` — the hypothesis of E7(a)
  is load-bearing; and a belief state with `p`, `∼p` both unlisted gives an incoherent table.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction LO.Propositional Finset BoolPCWorld Classical Cleanroom.Bli.BliFinite

/-! ## E1 on the coherent grid -/

/-- The day-1 table `(1, 0, 0)` on `extIndex`.
Source: mandate E1 (witness)
Kind: D
Fidelity: n/a -/
def ext1 : Table extIndex 1 := fun φ => if φ.1 = pA then 1 else 0

/-- The day-1 table `(0, 1, 0)` on `extIndex`.
Source: mandate E1 (witness)
Kind: D
Fidelity: n/a -/
def ext2 : Table extIndex 1 := fun φ => if φ.1 = qA then 1 else 0

/-- `p ≠ q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pA_ne_qA : pA ≠ qA := fun h => absurd (Formula.atom.inj h) (by norm_num)

/-- `p ≠ p ⋏ q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pA_ne_pq : pA ≠ pA ⋏ qA := fun h => by cases h

/-- `q ≠ p ⋏ q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma qA_ne_pq : qA ≠ pA ⋏ qA := fun h => by cases h

/-- The world `p ∧ ¬q` pays `ext1` on every extension sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPnQ_ext (φ : Sentence) (hφ : φ ∈ extIndex.S 1) : wPnQ.payoutRat φ = ext1 ⟨φ, hφ⟩ := by
  simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
  rcases hφ with rfl | rfl | rfl
  · show wPnQ.payoutRat pA = if pA = pA then 1 else 0
    rw [if_pos rfl]; decide
  · show wPnQ.payoutRat qA = if qA = pA then 1 else 0
    rw [if_neg pA_ne_qA.symm]; decide
  · show wPnQ.payoutRat (pA ⋏ qA) = if pA ⋏ qA = pA then 1 else 0
    rw [if_neg pA_ne_pq.symm]; decide

/-- The world `¬p ∧ q` pays `ext2` on every extension sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wnPQ_ext (φ : Sentence) (hφ : φ ∈ extIndex.S 1) : wnPQ.payoutRat φ = ext2 ⟨φ, hφ⟩ := by
  simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
  rcases hφ with rfl | rfl | rfl
  · show wnPQ.payoutRat pA = if pA = qA then 1 else 0
    rw [if_neg pA_ne_qA]; decide
  · show wnPQ.payoutRat qA = if qA = qA then 1 else 0
    rw [if_pos rfl]; decide
  · show wnPQ.payoutRat (pA ⋏ qA) = if pA ⋏ qA = qA then 1 else 0
    rw [if_neg qA_ne_pq.symm]; decide

/-- Two units of world mass on a chosen world, none elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def extCAt (u₀ : FiniteWorld 2) (u : FiniteWorld 2) : Fin (extMesh.d 1 + 1) :=
  if u = u₀ then ⟨2, by norm_num [extMesh]⟩ else ⟨0, by norm_num⟩

/-- A table paid by a single world is on the coherent grid (all mass on that world).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_coherentGrid_of_world (u₀ : FiniteWorld 2) (Q : Table extIndex 1)
    (hQ : ∀ φ : ↥(extIndex.S 1), u₀.payoutRat φ.1 = Q φ) :
    Q ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 := by
  unfold coherentGrid
  rw [Finset.mem_image]
  refine ⟨extCAt u₀, ?_, ?_⟩
  · unfold worldWeights
    rw [Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_, ?_⟩
    · have hval : ∀ u, (extCAt u₀ u).val = if u = u₀ then 2 else 0 := by
        intro u; unfold extCAt; split_ifs <;> rfl
      simp only [hval, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · intro u _ φ hφ; simp at hφ
  · funext φ
    unfold marginalOf
    have hval : ∀ u : FiniteWorld 2, (((extCAt u₀ u).val : ℕ) : ℚ) / (extMesh.d 1 : ℚ) =
        if u = u₀ then 1 else 0 := by
      intro u
      unfold extCAt
      show (((if u = u₀ then (⟨2, _⟩ : Fin (extMesh.d 1 + 1)) else ⟨0, _⟩).val : ℕ) : ℚ) /
        ((2 : ℕ) : ℚ) = _
      split_ifs <;> norm_num
    simp only [hval, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hQ φ

/-- `ext1` is on the coherent grid.
Source: mandate E1 (witness)
Kind: L
Fidelity: n/a -/
lemma ext1_mem_coherentGrid : ext1 ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 :=
  mem_coherentGrid_of_world wPnQ ext1 fun φ => payout_wPnQ_ext φ.1 φ.2

/-- `ext2` is on the coherent grid.
Source: mandate E1 (witness)
Kind: L
Fidelity: n/a -/
lemma ext2_mem_coherentGrid : ext2 ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 :=
  mem_coherentGrid_of_world wnPQ ext2 fun φ => payout_wnPQ_ext φ.1 φ.2

/-- `ext1 ≠ ext2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ext1_ne_ext2 : ext1 ≠ ext2 := by
  intro h
  have := congrFun h ⟨pA, pA_mem_ext 1⟩
  simp only [ext1, ext2, if_pos rfl, if_neg pA_ne_qA] at this
  norm_num at this

/-- The two-point balance solution `½ δ_{ext1} + ½ δ_{ext2}` on the coherent grid.
Source: mandate E1 (witness: "find a second point")
Kind: D
Fidelity: n/a -/
def extF : Superbelief extIndex 1 :=
  fun Q => if Q ∈ ({ext1, ext2} : Finset (Table extIndex 1)) then 1 / 2 else 0

/-- `extF` is a probability on the coherent grid.
Source: mandate E1 (witness)
Kind: L
Fidelity: n/a -/
lemma extF_isProbOn : IsProbOn (coherentGrid extIndex extMesh.d 1 ∅ 2) extF := by
  refine ⟨fun Q => ?_, fun Q hQ => ?_, ?_⟩
  · unfold extF; split_ifs <;> norm_num
  · unfold extF
    rw [if_neg]
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact hQ ext1_mem_coherentGrid
    · exact hQ ext2_mem_coherentGrid
  · unfold extF
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr, Finset.sum_pair ext1_ne_ext2]
    · norm_num
    · intro Q hQ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with rfl | rfl
      · exact ext1_mem_coherentGrid
      · exact ext2_mem_coherentGrid

/-- The restricted mean of `extF` is `extT = (1/2, 1/2, 0)`.
Source: mandate E1 (witness: "(1,0,0) and (0,1,0) average to (1/2,1/2,0)")
Kind: L
Fidelity: n/a -/
lemma extF_mean : (meanOn (coherentGrid extIndex extMesh.d 1 ∅ 2) extF).restrict = extT := by
  funext φ
  rw [Table.restrict_apply]
  unfold meanOn extF
  have hsub : ({ext1, ext2} : Finset (Table extIndex 1)) ⊆ coherentGrid extIndex extMesh.d 1 ∅ 2 := by
    intro Q hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl
    · exact ext1_mem_coherentGrid
    · exact ext2_mem_coherentGrid
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub,
    Finset.sum_pair ext1_ne_ext2]
  have hφ := φ.2
  simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
  unfold ext1 ext2 extT
  rcases hφ with h | h | h <;> simp only [h, if_pos rfl, if_neg pA_ne_qA, if_neg pA_ne_qA.symm,
    if_neg pA_ne_pq, if_neg qA_ne_pq, if_neg pA_ne_pq.symm, if_neg qA_ne_pq.symm] <;> norm_num

/-- `ext1` and `ext2` lie in the generated face of the coherent grid over `extT`.
Source: mandate E1 (witness)
Kind: L
Fidelity: n/a -/
lemma ext1_mem_faceGen : ext1 ∈ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT :=
  mem_faceGen_of_pos extF_isProbOn extF_mean (by unfold extF; rw [if_pos (by simp)]; norm_num)

/-- `ext2 ∈ faceGen`.
Source: mandate E1 (witness)
Kind: L
Fidelity: n/a -/
lemma ext2_mem_faceGen : ext2 ∈ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT :=
  mem_faceGen_of_pos extF_isProbOn extF_mean (by unfold extF; rw [if_pos (by simp)]; norm_num)

/-- **E1's N+ witness, assembled.** On the coherent grid (a non-product carrier, `d = 2`) over
`extT = (1/2, 1/2, 0)`: E1(i)'s full-support solution exists, charges the two distinct points
`ext1 = (1,0,0)` and `ext2 = (0,1,0)`, and puts mass `0` on `extQ₀ = 0` (which is in the product
face and on the carrier, `bli-finite`'s `faceGen_coherentGrid_not_prod`). The face has at least
two points.
Source: mandate E1 (witness); [[bli-program]] §7 item 11
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem face_witness :
    ∃ F : Superbelief extIndex 1, IsProbOn (coherentGrid extIndex extMesh.d 1 ∅ 2) F ∧
      (meanOn (coherentGrid extIndex extMesh.d 1 ∅ 2) F).restrict = extT ∧
      (∀ Q, 0 < F Q ↔ Q ∈ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT) ∧
      0 < F ext1 ∧ 0 < F ext2 ∧ F extQ₀ = 0 ∧ ext1 ≠ ext2 ∧
      2 ≤ (faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT).card := by
  obtain ⟨F, hF, hb, hsupp⟩ :=
    exists_fullSupport_faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT ⟨ext1, ext1_mem_faceGen⟩
  refine ⟨F, hF, hb, hsupp, (hsupp ext1).mpr ext1_mem_faceGen, (hsupp ext2).mpr ext2_mem_faceGen,
    ?_, ext1_ne_ext2, ?_⟩
  · exact le_antisymm (not_lt.mp fun h => faceGen_coherentGrid_not_prod.2.2 ((hsupp extQ₀).mp h))
      (hF.1 extQ₀)
  · calc 2 = ({ext1, ext2} : Finset (Table extIndex 1)).card := (Finset.card_pair ext1_ne_ext2).symm
      _ ≤ _ := Finset.card_le_card (by
          intro Q hQ
          simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
          rcases hQ with rfl | rfl
          · exact ext1_mem_faceGen
          · exact ext2_mem_faceGen)

/-- **E1(ii)'s `ε` for `ext1`**: with `ε = 1`, `extT + 1 • (extT − ext1.restrict) = ext2.restrict`,
a point of the restricted carrier — so `ext1 ∈ faceGen` also by the backward direction of
`faceGen_eq_hullFace` (an independent route into the face).
Source: mandate E1 (witness: "verify (ii)'s ε for one of them")
Kind: N+
Fidelity: exact -/
theorem ext1_backaway :
    extT + (1 : ℚ) • (extT - ext1.restrict) ∈
      convexHull ℚ (↑((coherentGrid extIndex extMesh.d 1 ∅ 2).image Table.restrict) : Set (Table extIndex 0)) := by
  have h : extT + (1 : ℚ) • (extT - ext1.restrict) = ext2.restrict := by
    funext φ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, one_mul, Table.restrict_apply]
    have hφ := φ.2
    simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
    unfold ext1 ext2 extT
    rcases hφ with h | h | h <;> simp only [h, if_neg pA_ne_qA, if_neg pA_ne_qA.symm,
      if_neg pA_ne_pq, if_neg qA_ne_pq, if_neg pA_ne_pq.symm, if_neg qA_ne_pq.symm] <;> norm_num
  rw [h]
  exact subset_convexHull ℚ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ext2_mem_coherentGrid))

/-- `ext1 ∈ faceGen` by the hull characterization (independent of `extF`).
Source: mandate E1 (witness)
Kind: N+
Fidelity: exact -/
theorem ext1_mem_faceGen' : ext1 ∈ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT :=
  (faceGen_eq_hullFace _ _ _).mpr ⟨ext1_mem_coherentGrid, 1, one_pos, ext1_backaway⟩

/-- **E1(ii) fails for `extQ₀`**: no `ε > 0` backs `extT` away from `0` inside the hull of the
restricted coherent grid — because `extQ₀ ∉ faceGen` (`bli-finite`) and the characterization.
Source: mandate E1 (witness: "its failure for `extQ₀`")
Kind: N+
Fidelity: exact -/
theorem extQ₀_no_backaway :
    ¬ ∃ ε : ℚ, 0 < ε ∧ extT + ε • (extT - extQ₀.restrict) ∈
      convexHull ℚ (↑((coherentGrid extIndex extMesh.d 1 ∅ 2).image Table.restrict) : Set (Table extIndex 0)) :=
  fun ⟨ε, hε, hmem⟩ => faceGen_coherentGrid_not_prod.2.2
    ((faceGen_eq_hullFace _ _ _).mpr ⟨faceGen_coherentGrid_not_prod.2.1, ε, hε, hmem⟩)

/-! ## E2 on the worked witness -/

/-- The history pricing `p` at `1/2` on every day, everything else at `0`.
Source: mandate E2 (witness)
Kind: D
Fidelity: n/a -/
def V₀ : ℕ → Sentence → ℚ := fun _ φ => if φ = pW then 1 / 2 else 0

/-- Its day-0 table is `t₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualTable_V₀ : actualTable witIndex V₀ 0 = t₀ := by
  funext ⟨x, hx⟩
  have hx' := hx
  rw [witIndex_S_zero, Finset.mem_singleton] at hx'
  simp [actualTable, V₀, t₀, hx']

/-- **E2's one-step witness**: `tentExpr₁ witMesh 0 Q₁` denotes `1/9` at `V₀` — the tent law at
`t₀ = (p ↦ 1/2)`, `Q₁ = (1/2, 0)`, on the 9-point grid (`bli-finite`'s `tentLaw_t₀`).
Source: mandate E2 (witness: "evaluate `tentExpr₁` … to `1/9`")
Kind: N+
Fidelity: exact (through `tentExpr₁_denoteRat`; the same value by direct unfolding of FAF's
`denoteRat` on the whole product is `tentExpr₁_direct`, at the coordinate level `mix3E_witness`) -/
theorem tentExpr₁_witness : (tentExpr₁ witMesh 0 Q₁).denoteRat V₀ = 1 / 9 := by
  rw [tentExpr₁_denoteRat, actualTable_V₀]
  exact tentLaw_t₀ Q₁_mem_grid

/-- **Direct evaluation of a coordinate term** through FAF's `denoteRat`: the `p`-coordinate term
at grid value `1/2` (constants `[1/2 = 0] = 0`, `uniform1 2 (1/2) = 1/3`, `[1/2 = 1] = 0`) denotes
`1/3` at price `1/2` — unfolding `max`/`mul`/`add`/`const`/`price`, no lemma of this package.
Source: mandate E2 (witness: "by `norm_num` on the denotation, not `native_decide`")
Kind: N+
Fidelity: exact -/
theorem mix3E_witness : (mix3E (.price pW 0) 0 (1 / 3) 0).denoteRat V₀ = 1 / 3 := by
  simp only [mix3E, w0E, wUE, w1E, clampE, minE, negE, subE, absE, EF.denoteRat, EF.denoteRatWith,
    V₀]
  norm_num

/-- The three grid values at `d = 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridVals_two : gridVals 2 = {0, 1 / 2, 1} := by
  ext q
  rw [mem_gridVals_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> norm_num
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩

/-- `p` precedes `q` in FAF's code order (`⌜p⌝ = 3 < 4 = ⌜q⌝`, kernel-decidable).
Source: none: infrastructure (audit r2 adversarial §3.3, probe `EncodeOrder.lean`)
Kind: L
Fidelity: n/a -/
lemma encLE_p_q : encLE witIndex 1 ⟨pW, pW_mem_S1⟩ ⟨qW, qW_mem_S1⟩ := by
  show Encodable.encode pW ≤ Encodable.encode qW
  decide

/-- The sorted day-1 coordinate list of `tentExpr₁ witMesh 0` is `[p, q]`.
Source: none: infrastructure (audit r2 adversarial §3.3, probe `DirectEval.lean`)
Kind: L
Fidelity: n/a -/
lemma sort_S1 : (Finset.univ : Finset ↥(witIndex.S 1)).sort (encLE witIndex 1) =
    [⟨pW, pW_mem_S1⟩, ⟨qW, qW_mem_S1⟩] := by
  rw [univ_S1, Finset.sort_insert (encLE witIndex 1) (fun b hb => ?_)
    (by rw [Finset.mem_singleton]; exact subtype_p_ne_q), Finset.sort_singleton]
  rw [Finset.mem_singleton] at hb
  subst hb
  exact encLE_p_q

/-- **The full one-step term, evaluated directly**: `tentExpr₁ witMesh 0 Q₁` denotes `1/9` at `V₀`
through FAF's `denoteRat` on the whole pinned product `mul (coordExpr p) (mul (coordExpr q)
(const 1))` — the coordinate list pinned by `sort_S1`, then `max`/`mul`/`add`/`const`/`price`
unfolded and `norm_num`; no lemma of this package's `Expr.lean` beyond the definitions. The
mandate's "by `norm_num` on the denotation", end to end (the round-1 "not done" item: the only
blocker was the code order of the two atoms, which the kernel decides).
Source: mandate E2 (witness); audit r2 adversarial §3.3 (probe `DirectEval.lean`, lifted)
Kind: N+
Fidelity: exact -/
theorem tentExpr₁_direct : (tentExpr₁ witMesh 0 Q₁).denoteRat V₀ = 1 / 9 := by
  show (prodList (((Finset.univ : Finset ↥(witIndex.S 1)).sort (encLE witIndex 1)).map
    fun φ => coordExpr witMesh 0 0 φ (Q₁ φ))).denoteRat V₀ = 1 / 9
  rw [sort_S1]
  simp only [List.map, prodList, coordExpr, pW_mem_S0, qW_not_mem_S0, dite_true, dite_false,
    chainFrom_zero, coordMarg_zero, tentCoord]
  simp only [EF.denoteRat, EF.denoteRatWith, mix3E, w0E, wUE, w1E, clampE, minE, negE, subE,
    absE, V₀, Q₁, uniform1, witMesh, gridVals_two, Finset.mem_insert, Finset.mem_singleton]
  norm_num [pW_ne_qW, pW_ne_qW.symm]

/-- **The horizon-2 constants at `d = 2`, `v = 1/2`**: the chain from `δ₀`, `U`, `δ₁` through one
tent step reads `0`, `1/9`, `0` at `1/2` (computed by recursion through the mesh).
Source: mandate E2 (witness: "one `h = 2` instance of (c)")
Kind: N+
Fidelity: exact -/
theorem chainFrom_two_half :
    chainFrom witMesh 0 1 (fun u => if u = 0 then 1 else 0) (1 / 2) = 0 ∧
    chainFrom witMesh 0 1 (uniform1 2) (1 / 2) = 1 / 9 ∧
    chainFrom witMesh 0 1 (fun u => if u = 1 then 1 else 0) (1 / 2) = 0 := by
  have hmesh : witMesh.d (0 + 0 + 1) = 2 := rfl
  have hmesh' : witMesh.d (0 + 0 + 1 + 1) = 2 := rfl
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [chainFrom_succ, hmesh, hmesh', gridVals_two, Finset.sum_insert (by norm_num),
      Finset.sum_insert (by norm_num), Finset.sum_singleton]
    simp only [chainFrom_zero, tent1, uniform1, clamp01, gridVals_two, Finset.mem_insert,
      Finset.mem_singleton]
    norm_num

/-- `p` is small on day 2 (`0 + 1 + 1`, as `tentExpr` indexes it).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pW_mem_S2 : pW ∈ witIndex.S (0 + 1 + 1) := by simp [witIndex]

/-- `q` is small on day 2.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma qW_mem_S2 : qW ∈ witIndex.S (0 + 1 + 1) := by simp [witIndex]

/-- The universe of day-2 small sentences, as the pair `{p, q}` in the subtype.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univ_S2 : (Finset.univ : Finset ↥(witIndex.S (0 + 1 + 1))) = {⟨pW, pW_mem_S2⟩, ⟨qW, qW_mem_S2⟩} := by
  ext ⟨x, hx⟩
  have hx' : x = pW ∨ x = qW := by simpa [witIndex] using hx
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
  exact hx'

/-- The two day-2 small sentences are distinct as subtype elements.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma subtype_p_ne_q₂ : (⟨pW, pW_mem_S2⟩ : ↥(witIndex.S (0 + 1 + 1))) ≠ ⟨qW, qW_mem_S2⟩ :=
  fun h => pW_ne_qW (Subtype.mk.inj h)

/-- The day-2 table `(1/2, 1/2)` on the worked witness.
Source: mandate E2 (witness)
Kind: D
Fidelity: n/a -/
def Qhh : Table witIndex (0 + 1 + 1) := fun _ => 1 / 2

/-- **E2's horizon-2 witness**: `tentExpr witMesh 0 1 Qhh` denotes `1/81` at `V₀` — the product of
the `p`-coordinate's two-step marginal `1/9` (from price `1/2`) and the `q`-coordinate's `1/9`
(entering uniformly on day 1, one tent step), on the 9-point day-2 grid.
Source: mandate E2 (witness: "one `h = 2` instance of (c)")
Kind: N+
Fidelity: exact -/
theorem tentExpr_two_witness : (tentExpr witMesh 0 1 Qhh).denoteRat V₀ = 1 / 81 := by
  rw [denoteRat_tentExpr_prod, actualTable_V₀]
  rw [univ_S2, Finset.prod_pair subtype_p_ne_q₂]
  have hp : coordMarg witMesh 0 1 t₀ ⟨pW, pW_mem_S2⟩ (Qhh ⟨pW, pW_mem_S2⟩) = 1 / 9 := by
    rw [coordMarg_of_mem t₀ 1 _ _ pW_mem_S0]
    show chainFrom witMesh 0 1 (tent1 (witMesh.d (0 + 1)) (1 / 2)) (1 / 2) = 1 / 9
    rw [chainFrom_tentW, show witMesh.d (0 + 1) = 2 from rfl]
    obtain ⟨h0, hU, h1⟩ := chainFrom_two_half
    rw [h0, hU, h1]
    simp only [tentW, clamp01]
    norm_num
  have hq : coordMarg witMesh 0 1 t₀ ⟨qW, qW_mem_S2⟩ (Qhh ⟨qW, qW_mem_S2⟩) = 1 / 9 := by
    rw [coordMarg_succ_of_mem t₀ _ qW_mem_S1]
    have hmesh : witMesh.d (0 + 0 + 1) = 2 := rfl
    have hmesh' : witMesh.d (0 + 0 + 1 + 1) = 2 := rfl
    rw [hmesh, hmesh', gridVals_two, Finset.sum_insert (by norm_num),
      Finset.sum_insert (by norm_num), Finset.sum_singleton]
    simp only [coordMarg_zero, tentCoord, dif_neg qW_not_mem_S0, Qhh, tent1, uniform1, clamp01,
      show witMesh.d (0 + 1) = 2 from rfl, gridVals_two,
      Finset.mem_insert, Finset.mem_singleton]
    norm_num
  rw [hp, hq]
  norm_num

/-! ## E5 -/

/-- The index with `S m = {⊥}` on every day.
Source: mandate E5 (witness)
Kind: D
Fidelity: n/a -/
def botIndex : SmallIndex := ⟨fun _ => {⊥}, fun _ => Finset.Subset.refl _⟩

/-- **E5(a)'s N− witness**: at `d = 2`, the printed grid admits no balance solution over the table
pricing `⊥` at `0` (`0 < 1/2`).
Source: mandate E5 (witness)
Kind: N−
Fidelity: exact (degenerate: one sentence, the best the refutation needs) -/
theorem posGrid_witness :
    ¬ ∃ F : Superbelief botIndex 1, IsProbOn (posGrid botIndex (fun _ => 2) 1) F ∧
      (meanOn (posGrid botIndex (fun _ => 2) 1) F).restrict = (fun _ => 0) :=
  posGrid_no_balance_below (by norm_num) (fun _ => 0) ⟨⊥, by simp [botIndex]⟩ (by norm_num)

/-- **E5(b)'s witness**: at `t₀' = (p ↦ 0)`, `d = 2`, no fully supported balanced grid probability
exists; **E5(c)'s witness**: the tent kernel there is non-degenerate on a face of 3 points with
mass `1/3` each, the face is a proper subset of the 9-point grid, and the off-face grid table
`Q₁ = (1/2, 0)` has mass `0` (`bli-finite`'s `worked_witness`, reused).
Source: mandate E5 (witness); [[bli-program]] §7 item 6
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem boundary_witness :
    (¬ ∃ F : Superbelief witIndex 1, IsProb witMesh.d F ∧ Balanced witMesh.d F t₀' ∧
        ∀ Q ∈ grid witIndex witMesh.d 1, 0 < F Q) ∧
    NonDegenerate witMesh.d (tentLaw witMesh 0 t₀') t₀' ∧
    (faceProd witIndex witMesh.d 0 t₀').card = 3 ∧
    (∀ Q ∈ faceProd witIndex witMesh.d 0 t₀', tentLaw witMesh 0 t₀' Q = 1 / 3) ∧
    faceProd witIndex witMesh.d 0 t₀' ⊂ grid witIndex witMesh.d 1 ∧
    Q₁ ∈ grid witIndex witMesh.d 1 ∧ tentLaw witMesh 0 t₀' Q₁ = 0 :=
  ⟨not_fullSupport_of_zeroOne (witMesh.d_pos 1) ⟨⟨pW, pW_mem_S0⟩, Or.inl rfl⟩,
    tentLaw_nonDegenerate t₀'_inUnit, worked_witness.2.2.2.2.2.2.2.1,
    worked_witness.2.2.2.2.2.2.2.2.1, worked_witness.2.2.2.2.2.2.2.2.2.1,
    worked_witness.2.2.2.2.2.2.2.2.2.2.1, worked_witness.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## E6: a hand-built support-entry day -/

/-- The empty belief state (nothing listed; every quote `0`).
Source: mandate E6 (witness: "day `n`: `φ` absent")
Kind: D
Fidelity: n/a -/
def st₀ : RationalBeliefState := ⟨[], List.nodup_nil, by simp⟩

/-- The belief state listing `p` at `1/2`.
Source: mandate E6 (witness: "day `n+1`: `φ` listed at `1/2`")
Kind: D
Fidelity: n/a -/
def st₁ : RationalBeliefState := ⟨[(pW, 1 / 2)], by simp, by norm_num⟩

/-- The sequence: `st₀` on day 0, `st₁` afterwards.
Source: mandate E6 (witness)
Kind: D
Fidelity: n/a -/
def dogB : ℕ → RationalBeliefState := fun n => if n = 0 then st₀ else st₁

/-- The day-0 actual table of `dogB` is `t₀' = (p ↦ 0)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualTable_dogB_zero : actualTable witIndex (ofBeliefStates dogB) 0 = t₀' := by
  funext φ
  simp [actualTable, ofBeliefStates, dogB, st₀, RationalBeliefState.quote, t₀']

/-- The realized day-1 state of `dogB` is `Q₁ = (1/2, 0)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualState_dogB_one : actualState witIndex witMesh.d (ofBeliefStates dogB) 1 = Q₁ := by
  funext ⟨x, hx⟩
  have hφ : x = pW ∨ x = qW := by
    have hx' := hx
    rwa [witIndex_S_succ, Finset.mem_insert, Finset.mem_singleton] at hx'
  show roundVal 2 (st₁.quote x) = Q₁ ⟨x, hx⟩
  rcases hφ with h | h
  · rw [show st₁.quote x = 1 / 2 by simp [st₁, RationalBeliefState.quote, h]]
    rw [roundVal_eq_self (by norm_num) half_mem_gridVals_two]
    simp [Q₁, h]
  · rw [show st₁.quote x = 0 by simp [st₁, RationalBeliefState.quote, h, pW_ne_qW.symm]]
    rw [roundVal_zero]
    simp [Q₁, h, pW_ne_qW.symm]

/-- **E6's N+ witness (finite layer).** Over `witIndex`, `d = 2`, the belief states `dogB`: `p` is
unlisted on day 0 and listed at `1/2` on day 1; the day-0 table is `t₀' = (p ↦ 0)` and the
realized day-1 state is `Q₁ = (1/2, 0)`, which is off the product face and null under every
balanced superbelief on day 0, while the face has 3 points, each of positive tent mass — the
support-entry mechanism of E6(d), with a face of ≥ 2 points.
Source: mandate E6 (witness (i)); [[bli-program]] §7 item 11
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem dogmatism_witness :
    pW ∉ (dogB 0).support ∧ pW ∈ (dogB 1).support ∧
    actualTable witIndex (ofBeliefStates dogB) 0 = t₀' ∧
    actualState witIndex witMesh.d (ofBeliefStates dogB) 1 = Q₁ ∧
    Q₁ ∉ faceProd witIndex witMesh.d 0 t₀' ∧
    (∀ F : Superbelief witIndex 1, IsProb witMesh.d F → Balanced witMesh.d F t₀' → F Q₁ = 0) ∧
    (faceProd witIndex witMesh.d 0 t₀').card = 3 ∧
    NonDegenerate witMesh.d (tentLaw witMesh 0 t₀') t₀' := by
  refine ⟨?_, ?_, actualTable_dogB_zero, actualState_dogB_one, Q₁_not_mem_faceProd,
    fun F hF hb => null_of_not_mem_faceProd hF hb Q₁_not_mem_faceProd,
    worked_witness.2.2.2.2.2.2.2.1, tentLaw_nonDegenerate t₀'_inUnit⟩
  · simp [dogB, st₀, RationalBeliefState.support]
  · simp [dogB, st₁, RationalBeliefState.support]

/-- The realized day-1 state of `V₀` is `Q₁ = (1/2, 0)`.
Source: none: infrastructure (audit r1 probe `DogmatismPositive.lean`)
Kind: L
Fidelity: n/a -/
lemma actualState_V₀_one : actualState witIndex witMesh.d V₀ 1 = Q₁ := by
  funext ⟨x, hx⟩
  have hφ : x = pW ∨ x = qW := by
    have hx' := hx
    rwa [witIndex_S_succ, Finset.mem_insert, Finset.mem_singleton] at hx'
  show roundVal 2 (V₀ 1 x) = Q₁ ⟨x, hx⟩
  rcases hφ with h | h
  · simp only [V₀, h, Q₁, if_true]
    exact roundVal_eq_self (by norm_num) half_mem_gridVals_two
  · simp only [V₀, h, Q₁, if_neg pW_ne_qW.symm]
    exact roundVal_zero 2

/-- **E6's N+ witness, positive direction.** At `V₀` (`p ↦ 1/2` on every day, `q ↦ 0`) the day-0
table `t₀ = (p ↦ 1/2)` has no `0/1` coordinate, so the face condition holds vacuously and
`dogmatism` gives the realized day-1 state — `Q₁`, of tent mass `1/9` — positive mass under the
tent law. With `dogmatism_witness` (the null direction at `t₀'`), both directions of the E6 iff
are inhabited on the worked witness.
Source: mandate E6 (witness); audit r1 (adversarial §3.6, probe `DogmatismPositive.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem dogmatism_positive_witness :
    actualState witIndex witMesh.d V₀ 1 = Q₁ ∧
    0 < tentLaw witMesh 0 t₀ (actualState witIndex witMesh.d V₀ 1) ∧
    tentLaw witMesh 0 t₀ Q₁ = 1 / 9 := by
  refine ⟨actualState_V₀_one, ?_, tentLaw_t₀ Q₁_mem_grid⟩
  have hF : IsProb witMesh.d (tentLaw witMesh 0 t₀) := tentLaw_isProb t₀
  have hb : Balanced witMesh.d (tentLaw witMesh 0 t₀) (actualTable witIndex V₀ 0) := by
    rw [actualTable_V₀]; exact tentLaw_balanced t₀_inUnit
  have hnd : NonDegenerate witMesh.d (tentLaw witMesh 0 t₀) (actualTable witIndex V₀ 0) := by
    rw [actualTable_V₀]; exact tentLaw_nonDegenerate t₀_inUnit
  refine (dogmatism V₀ 0 hF hb hnd).mpr ?_
  rintro ⟨x, hx⟩ hφ
  exfalso
  have hp : x = pW := by
    have hx' := hx
    rwa [witIndex_S_zero, Finset.mem_singleton] at hx'
  norm_num [V₀, hp] at hφ

/-! ## E7 -/

/-- **E7(a)'s N+ witness**: the two-point balance solution `extF` on the coherent grid forces
`extT = (1/2, 1/2, 0)` coherent — by the theorem.
Source: mandate E7 (witness)
Kind: N+
Fidelity: exact -/
theorem extT_coherent : CoherentOn extT ∅ 2 :=
  base_coherent_of_balance_on_coherentGrid (extMesh.d_pos 1) extF_isProbOn extF_mean

/-- The day-1 table `(1, 1, 0)`: charged by the product-grid tent kernel at `extT`, incoherent.
Source: mandate E7 (witness: the contrast)
Kind: D
Fidelity: n/a -/
def ext11 : Table extIndex 1 := fun φ => if φ.1 = pA ⋏ qA then 0 else 1

/-- `extT` lies in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extT_inUnit : extT.InUnit := fun _ => by unfold extT; split_ifs <;> norm_num

/-- `ext11` is on the product face over `extT` (grid values, and `p ⋏ q` pinned at `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ext11_mem_faceProd : ext11 ∈ faceProd extIndex extMesh.d 0 extT := by
  rw [mem_faceProd_iff]
  refine ⟨mem_grid_iff.mpr fun φ => ?_, fun φ hφ => ?_⟩
  · unfold ext11
    split_ifs
    · exact zero_mem_gridVals _
    · exact one_mem_gridVals (extMesh.d_pos _)
  · rw [Table.restrict_apply]
    unfold ext11 extT at *
    split_ifs with h
    · rfl
    · exfalso
      rcases hφ with h' | h' <;> simp [h] at h'

/-- A coherent table has `Q p + Q q ≤ 1 + Q (p ⋏ q)` (Boolean, mixed).
Source: none: infrastructure (`bli-finite`'s `payoutRat_p_add_q_le`)
Kind: L
Fidelity: n/a -/
lemma coherentOn_p_add_q_le {B : ℕ} {Q : Table extIndex 1} (hQ : CoherentOn Q ∅ B) :
    Q ⟨pA, pA_mem_ext 1⟩ + Q ⟨qA, qA_mem_ext 1⟩ ≤ 1 + Q ⟨pA ⋏ qA, pq_mem_ext 1⟩ := by
  obtain ⟨w, hw0, hw1, -, ht⟩ := hQ
  rw [ht, ht, ht, ← hw1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  have := payoutRat_p_add_q_le u
  nlinarith [hw0 u]

/-- **The contrast for E7(a)**: `ext11 = (1, 1, 0)` carries positive mass under the product-grid
tent kernel at `extT`, and is not coherent for any atom bound `B` — so the hypothesis "every
charged point is coherent" of `base_coherent_of_coherentGrid` is load-bearing (the product-grid
solution does not satisfy it).
Source: mandate E7 (witness: the contrast); [[bli-program]] §3.5(ii)
Kind: N+
Fidelity: exact (the mandate's `(1/2,1/2,1/2)` is not on the face; `(1,1,0)` is) -/
theorem ext11_charged_not_coherent :
    0 < tentLaw extMesh 0 extT ext11 ∧ ∀ B : ℕ, ¬ CoherentOn ext11 ∅ B := by
  refine ⟨(tentLaw_pos_iff extT_inUnit ext11).mpr ext11_mem_faceProd, fun B hB => ?_⟩
  have := coherentOn_p_add_q_le hB
  unfold ext11 at this
  simp only [if_neg pA_ne_pq, if_neg qA_ne_pq] at this
  norm_num at this

/-- The index with `S m = {p, ∼p}` on every day.
Source: mandate E7 (witness (b)/(c))
Kind: D
Fidelity: n/a -/
def negIndex : SmallIndex := ⟨fun _ => {pA, ∼pA}, fun _ => Finset.Subset.refl _⟩

/-- **E7(b)/(c)'s N+ witness**: with `p` and `∼p` both unlisted (the empty belief state), the
day-0 actual table prices both at `0` and is not coherent for any `D`, `B`. Minimal by
necessity: the theorem's hypotheses fix both load-bearing prices at `0`, so no instance is less
degenerate where it matters (the empty belief state is the whole market here).
Source: mandate E7 (witness (b)/(c)); audit r1 (adversarial §3.4)
Kind: N+ (minimal: the hypotheses fix the table)
Fidelity: exact -/
theorem offSupport_pair_witness :
    pA ∉ st₀.support ∧ (∼pA) ∉ st₀.support ∧
    ∀ (D : Finset Sentence) (B : ℕ),
      ¬ CoherentOn (actualTable negIndex (ofBeliefStates fun _ => st₀) 0) D B := by
  refine ⟨by simp [st₀, RationalBeliefState.support], by simp [st₀, RationalBeliefState.support],
    fun D B => ?_⟩
  exact not_coherent_of_offSupport_pair (𝒮 := negIndex) (m := 0) (φ := pA) (by simp [negIndex])
    (by simp [negIndex]) rfl rfl D B

end Cleanroom.Bli.BliSuperbelief
