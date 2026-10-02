import Cleanroom.Bli.BliExactBase.Bli
import Cleanroom.Bli.BliExactBase.Skeleton

/-!
# `bli-exact-base` · Uncharged: where the exact update is `x · 0 = 0`, and where it is not
(repair round 1)

Audit round 1 (adversarial B2/B3) showed that the two "exact small-sentence update on segment
days" headlines over the **linked** splice are vacuous: the product form
`𝐏_{n+1}(φ) · 𝐏_n(σ) = 𝐏_n(φ ⋏ σ)` holds with `𝐏_n(σ) = 0`, `σ` the realized day-`(n+1)` state.
The two probes are incorporated here as theorems, and the picture is completed on the positive
side.

* **The tent BLI over the linked splice** (`Bli.linkedBli_update_exact_segment`,
  `linkedBli_package` (ii)): the day-`n` linked table prices *every* atom of day-`(n+1)`
  cell-literal shape for `⊤` at cell `1` at `1` (the kernel's override by shape, `Kernel.slice`),
  while the day-`(n+1)` linked table prices such an atom strictly inside `(0,1)` once it is
  day-`(n+1)`-small (a free atom of a complete family; `wAtom`, `linkedPrice_wAtom_eq_one`,
  `linkedPrice_wAtom_succ_interior`). The atom `litIdx (n+2) (n+1) ⌜⊤⌝ 1` is machine-metered,
  hence day-`n`-small from some `N` on; so the realized next table is off the product face of the
  current one (`linkedTable_succ_not_mem_faceProd`) and the tent law charges it `0`
  (`tent_actual_next_zero`) — at every mesh, `segmentMesh K` and `denominatorMesh` alike.
* **The skeleton BLI** (`Skel.segmentBli_update_exact`): the two-point law's candidates are
  certain about `freshCoord`, the realized next table prices it `1/2` (findings F19), so the mass
  is `0` on every segment day `1 ≤ n` (`segmentBli_actual_next_zero`).
* **The unlinked segment tables are different** (the repair's push): a sentence the stage decides
  stays decided (`DeductiveProcess.mono`), and a segment table prices a stage-decided sentence at
  exactly `0`/`1` and an undecided one strictly inside (`segmentPrice_trichotomy`), so the
  realized next segment table is **on** the product face of the current one
  (`segmentTable_succ_mem_faceProd`); at the denominator mesh the tent BLI over the unlinked
  splice charges the realized next state positively on every segment day
  (`segmentTent_actual_next_pos`), and `spliceBli_update_exact_denominator` there is a genuine
  Bayes update in ratio form (`segmentTent_update_ratio`). This is K7's "exactly Bayesian on days
  `< H`" with content — for the unlinked tables, at a noncomputable mesh; the computable-mesh
  form would need a dyadic refinement of `segmentPrice` (not built).

So the program's "linked" and "exactly Bayesian" clauses (§3.6 (vi)) conflict under Route W by
shape, as F17 showed for "linked" and "non-dogmatic": findings F22.
-/

namespace Cleanroom.Bli.BliExactBase.Uncharged

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Kernel Cleanroom.Bli.BliExactBase.Skel

noncomputable section

/-! ## The tent BLI over the linked splice: the realized next table is off the face -/

/-- The witness atom on day `n`: the day-`(n+1)` cell literal of `⊤` at cell `1` under code `n+2`
(any code works for the override; `n + 2` keeps the family machine-metered).
Source: audit r1 adversarial B2 (probe `AdvTentUpdateVacuous.wAtom`)
Kind: D
Fidelity: n/a -/
abbrev wAtom (n : ℕ) : ℕ := litIdx (n + 2) (n + 1) (Encodable.encode (⊤ : Sentence)) 1

/-- The family `n ↦ atom (wAtom n)` is machine-metered, hence eventually day-`n`-small.
Source: audit r1 adversarial B2; bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem wAtom_eventually_small : ∃ N, ∀ n ≥ N, SmallOn n (Formula.atom (wAtom n)) := by
  have hd : MachineDigits fun n => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (n + 2) (Nat.pair (n + 1) (Nat.pair (Encodable.encode (⊤ : Sentence)) 1))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 2))
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
              (MachineDigits.const (Nat.pair (Encodable.encode (⊤ : Sentence)) 1))))))).of_eq
      (fun _ => rfl)
  exact machineSentenceCodes_eventually_small
    (MachineSentenceCodes.ofCanonical
      (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl)))

/-- The witness atom is not the fresh coordinate's atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wAtom_ne_freshCode (n : ℕ) : wAtom n ≠ freshCode := litIdx_ne_freshCode _ _ _ _

/-- The witness atom of day `n` is not of day-`(n+2)` literal shape.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wAtom_not_litShape_succ (n : ℕ) : ¬ LitShape (n + 2) (wAtom n) := by
  rintro ⟨e, c, -, r, -, h⟩
  have := (litIdx_inj h).2.1
  omega

/-- Fresh at stage `n` (the kernel's hypothesis).
Source: `Kernel.litIdx_fresh`
Kind: L
Fidelity: n/a -/
lemma wAtom_freshAt (n : ℕ) : FreshAt ((paperDP 𝗜𝚺₁).D n) (wAtom n) :=
  litIdx_fresh 𝗜𝚺₁ (Nat.lt_succ_self n) _ _ _

/-- Fresh at stage `n + 1` too: the quotation input is `≥ n + 2`.
Source: `QuoteLane.quotationClaimCode_fresh_of_lt`
Kind: L
Fidelity: n/a -/
lemma wAtom_freshAt_succ (n : ℕ) : FreshAt ((paperDP 𝗜𝚺₁).D (n + 1)) (wAtom n) := by
  intro φ hφ
  show quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (n + 2) (Nat.pair (n + 1) (Nat.pair (Encodable.encode (⊤ : Sentence)) 1))) ∉
      sentenceAtomCodes φ
  refine quotationClaimCode_fresh_of_lt 𝗜𝚺₁ ?_ φ hφ
  calc n + 1 < n + 2 := Nat.lt_succ_self _
    _ ≤ Nat.pair (n + 2) _ := Nat.left_le_pair _ _

/-- **The day-`n` linked table prices the witness atom at `1`** (the kernel's override by shape:
both slices set every stage-fresh atom of that shape true).
Source: audit r1 adversarial B2; `Kernel.slice_holds_lit`
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma linkedPrice_wAtom_eq_one (n : ℕ) : Segment.linkedPrice n (Formula.atom (wAtom n)) = 1 := by
  have hk := (Segment.WAt_spec n).1
  have hc : Encodable.encode (⊤ : Sentence) ∈ segmentIndex (n + 1) := by simp [segmentIndex]
  have h : Segment.kernelMarket n (Formula.atom (wAtom n)) = 1 := by
    unfold Segment.kernelMarket
    rw [kMix_eq_ite hk (pT := True) (pF := True)
      (fun i => by rw [slice_holds_lit hc le_rfl (wAtom_freshAt n)]; simp)
      (fun i => by rw [slice_holds_lit hc le_rfl (wAtom_freshAt n)]; simp)]
    norm_num
  have := Segment.linkedPrice_cast n (Formula.atom (wAtom n))
  rw [h] at this
  exact_mod_cast this

/-- **The day-`(n+1)` linked table prices the witness atom strictly inside `(0, 1)`** when the atom
is day-`(n+1)`-small: the day-`(n+1)` kernel's slices do not touch it (it is not of day-`(n+2)`
shape), so it is the uniform mixture over a complete family at a free atom.
Source: audit r1 adversarial B2; `Mixing.mixRat_trichotomy`, `free_atom_undecided`
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma linkedPrice_wAtom_succ_interior (n : ℕ) (hs : Formula.atom (wAtom n) ∈ smallSet (n + 1)) :
    0 < Segment.linkedPrice (n + 1) (Formula.atom (wAtom n)) ∧
      Segment.linkedPrice (n + 1) (Formula.atom (wAtom n)) < 1 := by
  obtain ⟨hk, -, hcomp⟩ := Segment.WAt_spec (n + 1)
  have hsl : ∀ (x y z : ℕ) (b : Prop) (i : Fin (Segment.kAt (n + 1))),
      (slice ((paperDP 𝗜𝚺₁).D (n + 1)) (n + 2) x y z b (Segment.WAt (n + 1) i)).payoutRat
          (Formula.atom (wAtom n)) =
        (Segment.WAt (n + 1) i).payoutRat (Formula.atom (wAtom n)) := by
    intro x y z b i
    have h := slice_other (D := (paperDP 𝗜𝚺₁).D (n + 1)) (m := n + 2) (wAtom_ne_freshCode n)
      (fun h => wAtom_not_litShape_succ n h.1) x y z b (Segment.WAt (n + 1) i)
    by_cases hh : Segment.WAt (n + 1) i (wAtom n)
    · rw [payoutRat_of_holds' (by rw [PCWorld.holds_atom]; exact h.2 hh),
        payoutRat_of_holds' (by rw [PCWorld.holds_atom]; exact hh)]
    · rw [payoutRat_of_not_holds' (by rw [PCWorld.holds_atom]; exact fun h' => hh (h.1 h')),
        payoutRat_of_not_holds' (by rw [PCWorld.holds_atom]; exact hh)]
  have hkq : (0 : ℚ) < Segment.kAt (n + 1) := by exact_mod_cast hk
  have hmix : Segment.linkedPrice (n + 1) (Formula.atom (wAtom n)) =
      mixRat (Segment.WAt (n + 1)) (fun _ => 1 / (Segment.kAt (n + 1) : ℚ))
        (Formula.atom (wAtom n)) := by
    unfold Segment.linkedPrice kMixRat mixRat
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, kWorld, hsl]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hw0 : ∀ i : Fin (Segment.kAt (n + 1)),
      (0 : ℚ) < (fun _ : Fin (Segment.kAt (n + 1)) => 1 / (Segment.kAt (n + 1) : ℚ)) i :=
    fun _ => by positivity
  have hw1 : ∑ i : Fin (Segment.kAt (n + 1)),
      (fun _ : Fin (Segment.kAt (n + 1)) => 1 / (Segment.kAt (n + 1) : ℚ)) i = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hφ : sentenceAtomCodes (Formula.atom (wAtom n)) ⊆ smallAtoms (n + 1) :=
    atoms_subset_smallAtoms hs
  rcases mixRat_trichotomy hw0 hw1 hcomp hφ with h | h | h
  · obtain ⟨-, v, hv, hvn⟩ :=
      free_atom_undecided (wAtom_freshAt_succ n) (paperDP_hworld 𝗜𝚺₁ (n + 1))
    exact absurd (h v hv) hvn
  · obtain ⟨⟨v, hv, hvy⟩, -⟩ :=
      free_atom_undecided (wAtom_freshAt_succ n) (paperDP_hworld 𝗜𝚺₁ (n + 1))
    exact absurd hvy (h v hv)
  · rw [hmix]; exact h

/-- **The realized day-`(n+1)` linked table is off the product face of the day-`n` linked table**
whenever the witness atom is day-`n`-small — at every mesh `d`.
Source: audit r1 adversarial B2 (probe `linkedTable_succ_not_mem_faceProd`)
Kind: P
Fidelity: exact
Hyps: (a) `hs` (discharged from some `N` on by `wAtom_eventually_small`) -/
theorem linkedTable_succ_not_mem_faceProd {n : ℕ} (hs : Formula.atom (wAtom n) ∈ smallSet n)
    (d : ℕ → ℕ) : linkedTable (n + 1) ∉ faceProd smallIndex d n (linkedTable n) := by
  intro h
  rw [mem_faceProd_iff] at h
  have hs1 : Formula.atom (wAtom n) ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hs
  have h1 := h.2 ⟨Formula.atom (wAtom n), hs⟩ (Or.inr (linkedPrice_wAtom_eq_one n))
  rw [Table.restrict_apply] at h1
  have h2 := (linkedPrice_wAtom_succ_interior n hs1).2
  have h3 : Segment.linkedPrice (n + 1) (Formula.atom (wAtom n)) = 1 := by
    have := h1
    simp only [linkedTable] at this
    rw [this]; exact linkedPrice_wAtom_eq_one n
  rw [h3] at h2
  exact lt_irrefl _ h2

/-- **The tent BLI over the linked splice gives the realized day-`(n+1)` state mass `0` on every
segment day `n ≥ N`, `n + 1 < H`**, at `segmentMesh K`: `Bli.linkedBli_update_exact_segment` and
the exact-update conjunct of `linkedBli_package` read `x · 0 = 0` there.
Source: audit r1 adversarial B2 (probe `tent_actual_next_zero`)
Kind: P
Fidelity: exact
Hyps: (a) `hK` (as in `linkedBli_update_exact_segment`) -/
theorem tent_actual_next_zero : ∃ N, ∀ (H K : ℕ)
    (hK : ∀ n < H, ∀ φ, Segment.linkedPrice n φ ∈ gridVals ((Bli.segmentMesh K).d n))
    (c : StateCoding (Bli.segmentMesh K)) (n : ℕ), N ≤ n → n + 1 < H →
    Bli.spliceBli H Segment.linkedPrice (Bli.segmentMesh K) c n
      (stateAtom (n + 1)
        ((bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) c).actual
          (n + 1))) = 0 := by
  obtain ⟨N, hN⟩ := wAtom_eventually_small
  refine ⟨N, fun H K hK c n hn hnH => ?_⟩
  have hs : Formula.atom (wAtom n) ∈ smallSet n := mem_smallSet.2 (hN n hn)
  have hgrid := Bli.linked_actualTable_mem_grid hK hnH
  have hact : actualState smallIndex (Bli.segmentMesh K).d (spliceRat H Segment.linkedPrice)
      (n + 1) = linkedTable (n + 1) := by
    unfold actualState
    rw [roundTo_eq_self_of_mem_grid ((Bli.segmentMesh K).d_pos _) hgrid]
    exact actualTable_eq_linkedTable hnH
  have hA : linkedTable (n + 1) ∈ grid smallIndex (Bli.segmentMesh K).d (n + 1) := by
    rw [← hact]; exact actualState_mem_grid
  show ((bliPrice _ _ _ _ _ _ : ℚ) : ℝ) = 0
  rw [bliStateSystem_actual, hact, bliPrice_state c _ _ n hA,
    actualTable_eq_linkedTable (by omega)]
  show ((tentLaw (Bli.segmentMesh K) n (linkedTable n) (linkedTable (n + 1)) : ℚ) : ℝ) = 0
  have hnot := linkedTable_succ_not_mem_faceProd hs (Bli.segmentMesh K).d
  have hle : tentLaw (Bli.segmentMesh K) n (linkedTable n) (linkedTable (n + 1)) ≤ 0 :=
    not_lt.1 fun hpos => hnot ((tentLaw_pos_iff (linkedTable_inUnit n) _).1 hpos)
  have h0 : tentLaw (Bli.segmentMesh K) n (linkedTable n) (linkedTable (n + 1)) = 0 :=
    le_antisymm hle (tentLaw_nonneg _ _)
  rw [h0]; simp

/-- **`tent_actual_next_zero` at every mesh** whose day-`(n+1)` grid contains the realized next
linked table (repair round 2, audit r2 fidelity N4): the same face argument, the mesh a
parameter.
Source: audit r1 adversarial B2; audit r2 fidelity N4
Kind: P
Fidelity: exact
Hyps: (a) `hgrid` (the realized next table on the mesh's grid) -/
theorem tent_actual_next_zero_mesh : ∃ N, ∀ (H : ℕ) (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ),
    N ≤ n → n + 1 < H →
    actualTable smallIndex (spliceRat H Segment.linkedPrice) (n + 1) ∈
      grid smallIndex 𝓜.d (n + 1) →
    Bli.spliceBli H Segment.linkedPrice 𝓜 c n
      (stateAtom (n + 1)
        ((bliStateSystem (spliceRat H Segment.linkedPrice) 𝓜 c).actual (n + 1))) = 0 := by
  obtain ⟨N, hN⟩ := wAtom_eventually_small
  refine ⟨N, fun H 𝓜 c n hn hnH hgrid => ?_⟩
  have hs : Formula.atom (wAtom n) ∈ smallSet n := mem_smallSet.2 (hN n hn)
  have hact : actualState smallIndex 𝓜.d (spliceRat H Segment.linkedPrice) (n + 1) =
      linkedTable (n + 1) := by
    unfold actualState
    rw [roundTo_eq_self_of_mem_grid (𝓜.d_pos _) hgrid]
    exact actualTable_eq_linkedTable hnH
  have hA : linkedTable (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) := by
    rw [← hact]; exact actualState_mem_grid
  show ((bliPrice _ _ _ _ _ _ : ℚ) : ℝ) = 0
  rw [bliStateSystem_actual, hact, bliPrice_state c _ _ n hA,
    actualTable_eq_linkedTable (by omega)]
  show ((tentLaw 𝓜 n (linkedTable n) (linkedTable (n + 1)) : ℚ) : ℝ) = 0
  have hnot := linkedTable_succ_not_mem_faceProd hs 𝓜.d
  have hle : tentLaw 𝓜 n (linkedTable n) (linkedTable (n + 1)) ≤ 0 :=
    not_lt.1 fun hpos => hnot ((tentLaw_pos_iff (linkedTable_inUnit n) _).1 hpos)
  have h0 : tentLaw 𝓜 n (linkedTable n) (linkedTable (n + 1)) = 0 :=
    le_antisymm hle (tentLaw_nonneg _ _)
  rw [h0]; simp

/-- **`tent_actual_next_zero` at the splice's own denominator mesh**: the tent BLI over the
linked splice at `denominatorMesh (spliceRat H linkedPrice)` gives the realized day-`(n+1)`
state mass `0` on every segment day `n ≥ N`, `n + 1 < H` — so `Bli.spliceBli_update_exact_denominator`
at `t := linkedPrice` is `x · 0 = 0` there too (findings F22: "at every mesh, `denominatorMesh`
included", now in the Lean).
Source: audit r2 fidelity N4; findings F22
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem tent_actual_next_zero_denominator : ∃ N, ∀ (H : ℕ)
    (c : StateCoding (denominatorMesh (spliceRat H Segment.linkedPrice))) (n : ℕ),
    N ≤ n → n + 1 < H →
    Bli.spliceBli H Segment.linkedPrice (denominatorMesh (spliceRat H Segment.linkedPrice)) c n
      (stateAtom (n + 1)
        ((bliStateSystem (spliceRat H Segment.linkedPrice)
          (denominatorMesh (spliceRat H Segment.linkedPrice)) c).actual (n + 1))) = 0 := by
  obtain ⟨N, hN⟩ := tent_actual_next_zero_mesh
  exact ⟨N, fun H c n hn hnH => hN H _ c n hn hnH
    (actualTable_mem_grid_denominatorMesh _
      (Bli.spliceRat_range H Segment.linkedPrice (Segment.linkedPrice_inUnit H)) (n + 1))⟩

/-! ## The skeleton BLI: the realized next table is neither slice marginal -/

/-- The linked table on day `n + 1` prices `freshCoord` at `1/2`.
Source: `Kernel.kMix_fresh`
Kind: L
Fidelity: n/a -/
lemma linkedTable_succ_fresh (n : ℕ) (hf : freshCoord ∈ smallIndex.S (n + 1)) :
    linkedTable (n + 1) ⟨freshCoord, hf⟩ = 1 / 2 := by
  show Segment.linkedPrice (n + 1) freshCoord = 1 / 2
  have hk := (Segment.WAt_spec (n + 1)).1
  have := Segment.linkedPrice_cast (n + 1) freshCoord
  rw [show Segment.kernelMarket (n + 1) freshCoord = 1 / 2 from Kernel.kMix_fresh _ _ hk _] at this
  exact Rat.cast_injective (α := ℝ) (by rw [this]; norm_num)

/-- The realized next table is not the true slice marginal (`1/2 ≠ 1` at `freshCoord`).
Source: findings F19
Kind: L
Fidelity: n/a -/
lemma linkedTable_succ_ne_sliceT {n : ℕ} (h1 : 1 ≤ n) : linkedTable (n + 1) ≠ sliceT n := by
  intro h
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  have := congrFun h ⟨freshCoord, hf⟩
  rw [linkedTable_succ_fresh n hf] at this
  simp only [sliceT] at this
  rw [sliceTable_fresh] at this
  norm_num at this

/-- The realized next table is not the false slice marginal (`1/2 ≠ 0` at `freshCoord`).
Source: findings F19
Kind: L
Fidelity: n/a -/
lemma linkedTable_succ_ne_sliceF {n : ℕ} (h1 : 1 ≤ n) : linkedTable (n + 1) ≠ sliceF n := by
  intro h
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  have := congrFun h ⟨freshCoord, hf⟩
  rw [linkedTable_succ_fresh n hf] at this
  simp only [sliceF] at this
  rw [sliceTable_fresh] at this
  norm_num at this

/-- **The skeleton BLI gives the realized day-`(n+1)` state mass `0` on every segment day
`1 ≤ n`, `n + 1 < H`**: `Skel.segmentBli_update_exact` reads `x · 0 = 0` there (findings F19
carried to the update theorem).
Source: audit r1 adversarial B3 (probe `segmentBli_actual_next_zero`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem segmentBli_actual_next_zero {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 < H) :
    bliPrice (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) (segmentSkeleton H K hK) c n
      (stateAtom (n + 1)
        ((bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) c).actual
          (n + 1))) = 0 := by
  have hgrid : actualTable smallIndex (spliceRat H Segment.linkedPrice) (n + 1) ∈
      grid smallIndex (Bli.segmentMesh K).d (n + 1) := by
    rw [mem_grid_iff]
    intro φ
    show spliceRat H Segment.linkedPrice (n + 1) φ.1 ∈ gridVals ((Bli.segmentMesh K).d (n + 1))
    rw [Bli.spliceRat_eq_tbl_of_lt hn φ.2]
    exact gridVals_mono (pow_dvd_pow 2 (by have := hK (n + 1) hn; omega)) (Nat.two_pow_pos _)
      (Bli.linkedPrice_mem_gridVals (n + 1) φ.1)
  have hact : actualState smallIndex (Bli.segmentMesh K).d (spliceRat H Segment.linkedPrice)
      (n + 1) = linkedTable (n + 1) := by
    unfold actualState
    rw [roundTo_eq_self_of_mem_grid ((Bli.segmentMesh K).d_pos _) hgrid]
    exact actualTable_eq_linkedTable hn
  have hA : linkedTable (n + 1) ∈ grid smallIndex (Bli.segmentMesh K).d (n + 1) := by
    rw [← hact]; exact actualState_mem_grid
  rw [bliStateSystem_actual, hact, bliPrice_state c _ _ n hA,
    actualTable_eq_linkedTable (by omega), segmentSkeleton_law_linked hK (by omega)]
  unfold twoPointLaw
  rw [if_neg (linkedTable_succ_ne_sliceT h1), if_neg (linkedTable_succ_ne_sliceF h1)]
  norm_num

/-- The same, as the history (the form in `segmentBli_update_exact`).
Source: audit r1 adversarial B3
Kind: L
Fidelity: n/a -/
theorem segmentBli_actual_next_zero' {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 < H) :
    segmentBli H K hK c n
      (stateAtom (n + 1)
        ((bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) c).actual
          (n + 1))) = 0 := by
  show ((bliPrice _ _ _ _ _ _ : ℚ) : ℝ) = 0
  rw [segmentBli_actual_next_zero hK c h1 hn]
  simp

/-! ## The unlinked segment tables stay on the face -/

/-- A sentence every stage-`n`-consistent world holds is priced exactly `1` by the day-`n` segment
table (a mixture over such worlds).
Source: `Tables.segmentPrice_spec` (coherence on every algebra)
Kind: L
Fidelity: n/a -/
lemma segmentPrice_eq_one_of_valid {n : ℕ} {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) → v.Holds φ) :
    segmentPrice n φ = 1 := by
  obtain ⟨k, W, w, hW, -, hsum, hrep⟩ := (segmentPrice_spec n).2.1 (sentenceAtomCodes φ)
  have h1 : ((segmentPrice n φ : ℚ) : ℝ) = 1 := by
    have := hrep φ (subset_refl _)
    simp only at this
    rw [this, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [PCWorld.payout, h (W i) (hW i)]
  exact_mod_cast h1

/-- A sentence no stage-`n`-consistent world holds is priced exactly `0` by the day-`n` segment
table.
Source: `Tables.segmentPrice_spec`
Kind: L
Fidelity: n/a -/
lemma segmentPrice_eq_zero_of_invalid {n : ℕ} {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) → ¬ v.Holds φ) :
    segmentPrice n φ = 0 := by
  obtain ⟨k, W, w, hW, -, -, hrep⟩ := (segmentPrice_spec n).2.1 (sentenceAtomCodes φ)
  have h1 : ((segmentPrice n φ : ℚ) : ℝ) = 0 := by
    have := hrep φ (subset_refl _)
    simp only at this
    rw [this]
    exact Finset.sum_eq_zero fun i _ => by simp [PCWorld.payout, h (W i) (hW i)]
  exact_mod_cast h1

/-- **A segment table's `0`/`1` entries persist**: a day-`n` small sentence priced `0` or `1` by
the day-`n` segment table has the same price on day `n + 1` — a `0`/`1` price is a stage
decision (`segmentPrice_trichotomy`), and the stages are nested (`DeductiveProcess.mono`).
Source: [[bli-program]] §3.4 (the product face: "agree wherever today's table is `0` or `1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem segmentPrice_decided_succ {n : ℕ} {φ : Sentence} (hφ : φ ∈ smallSet n)
    (h : segmentPrice n φ = 0 ∨ segmentPrice n φ = 1) :
    segmentPrice (n + 1) φ = segmentPrice n φ := by
  rcases segmentPrice_trichotomy n hφ with hv | hv | hv
  · have hv' : ∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D (n + 1)) → v.Holds φ :=
      fun v hc => hv v (fun ψ hψ => hc ψ ((paperDP 𝗜𝚺₁).mono n hψ))
    rw [segmentPrice_eq_one_of_valid hv', segmentPrice_eq_one_of_valid hv]
  · have hv' : ∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D (n + 1)) → ¬ v.Holds φ :=
      fun v hc => hv v (fun ψ hψ => hc ψ ((paperDP 𝗜𝚺₁).mono n hψ))
    rw [segmentPrice_eq_zero_of_invalid hv', segmentPrice_eq_zero_of_invalid hv]
  · rcases h with h | h <;> rw [h] at hv <;> norm_num at hv

/-- **The realized next segment table is on the product face of the current one** on every
segment day `n + 1 < H`, at any mesh `d` whose day-`(n+1)` grid contains it (contrast
`linkedTable_succ_not_mem_faceProd` for the linked table).
Source: [[bli-program]] §3.4; findings F22
Kind: C
Fidelity: exact
Hyps: (a) `hg` (the grid clause; discharged at the denominator mesh below) -/
theorem segmentTable_succ_mem_faceProd {H n : ℕ} (hn : n + 1 < H) {d : ℕ → ℕ}
    (hg : actualTable smallIndex (spliceRat H segmentPrice) (n + 1) ∈
      grid smallIndex d (n + 1)) :
    actualTable smallIndex (spliceRat H segmentPrice) (n + 1) ∈
      faceProd smallIndex d n (actualTable smallIndex (spliceRat H segmentPrice) n) := by
  rw [mem_faceProd_iff]
  refine ⟨hg, fun φ h01 => ?_⟩
  have hφ : φ.1 ∈ smallSet n := φ.2
  have h01' : segmentPrice n φ.1 = 0 ∨ segmentPrice n φ.1 = 1 := by
    have this : spliceRat H segmentPrice n φ.1 = 0 ∨ spliceRat H segmentPrice n φ.1 = 1 := h01
    rwa [Bli.spliceRat_eq_tbl_of_lt (by omega) hφ] at this
  rw [Table.restrict_apply]
  show spliceRat H segmentPrice (n + 1) φ.1 = spliceRat H segmentPrice n φ.1
  rw [Bli.spliceRat_eq_tbl_of_lt hn (smallSet_mono (Nat.le_succ n) hφ),
    Bli.spliceRat_eq_tbl_of_lt (by omega) hφ]
  exact segmentPrice_decided_succ hφ h01'

/-- **The tent BLI over the unlinked segment tables charges the realized next state** at the
splice's denominator mesh on every segment day `n + 1 < H`: `0 < 𝐏_n(σ)`. So
`Bli.spliceBli_update_exact_denominator` at `t := segmentPrice` is a genuine Bayes update there
(contrast `tent_actual_next_zero` at the linked table).
Source: [[bli-program]] §3.6 (vi) ("exactly Bayesian"); mandate § 5 (ii); findings F22
Kind: C
Fidelity: exact (unlinked tables; noncomputable mesh; segment days)
Hyps: (a) -/
theorem segmentTent_actual_next_pos (H : ℕ)
    (c : StateCoding (denominatorMesh (spliceRat H segmentPrice))) {n : ℕ} (hn : n + 1 < H) :
    0 < Bli.spliceBli H segmentPrice (denominatorMesh (spliceRat H segmentPrice)) c n
      (stateAtom (n + 1)
        ((bliStateSystem (spliceRat H segmentPrice) (denominatorMesh (spliceRat H segmentPrice))
          c).actual (n + 1))) := by
  have hrange := Bli.spliceRat_range H segmentPrice (segmentPrice_inUnit H)
  have hgrid : actualTable smallIndex (spliceRat H segmentPrice) (n + 1) ∈
      grid smallIndex (denominatorMesh (spliceRat H segmentPrice)).d (n + 1) :=
    actualTable_mem_grid_denominatorMesh _ hrange (n + 1)
  have hact : actualState smallIndex (denominatorMesh (spliceRat H segmentPrice)).d
      (spliceRat H segmentPrice) (n + 1) = actualTable smallIndex (spliceRat H segmentPrice) (n + 1) := by
    unfold actualState
    exact roundTo_eq_self_of_mem_grid ((denominatorMesh (spliceRat H segmentPrice)).d_pos _) hgrid
  show (0 : ℝ) < ((bliPrice _ _ _ _ _ _ : ℚ) : ℝ)
  rw [bliStateSystem_actual, hact, bliPrice_state c _ _ n hgrid]
  show (0 : ℝ) < ((tentLaw (denominatorMesh (spliceRat H segmentPrice)) n
    (actualTable smallIndex (spliceRat H segmentPrice) n)
    (actualTable smallIndex (spliceRat H segmentPrice) (n + 1)) : ℚ) : ℝ)
  have hunit : (actualTable smallIndex (spliceRat H segmentPrice) n).InUnit :=
    actualTable_inUnit hrange
  have hpos : 0 < tentLaw (denominatorMesh (spliceRat H segmentPrice)) n
      (actualTable smallIndex (spliceRat H segmentPrice) n)
      (actualTable smallIndex (spliceRat H segmentPrice) (n + 1)) :=
    (tentLaw_pos_iff hunit _).2 (segmentTable_succ_mem_faceProd hn hgrid)
  exact_mod_cast hpos

/-- **K7e (ii) with content — the ratio form**: over the unlinked segment tables at the
denominator mesh, on every segment day `n + 1 < H` and every day-`n` small `φ`,
`𝐏_{n+1}(φ) = 𝐏_n(φ ⋏ σ) / 𝐏_n(σ)` with `𝐏_n(σ) > 0` (`σ` the realized day-`(n+1)` state).
Source: [[bli-program]] §3.6 (vi) ("exactly Bayesian"); mandate § 5 (ii); Appendix B
(`main.tex:440–442`)
Kind: C
Fidelity: exact (unlinked tables; noncomputable mesh; segment days; the computable-mesh form
needs a dyadic `segmentPrice`, not built)
Hyps: (a) -/
theorem segmentTent_update_ratio (H : ℕ)
    (c : StateCoding (denominatorMesh (spliceRat H segmentPrice))) {n : ℕ} (hn : n + 1 < H)
    {φ : Sentence} (hφ : φ ∈ smallSet n) :
    Bli.spliceBli H segmentPrice (denominatorMesh (spliceRat H segmentPrice)) c (n + 1) φ =
      Bli.spliceBli H segmentPrice (denominatorMesh (spliceRat H segmentPrice)) c n
          (φ ⋏ stateAtom (n + 1)
            ((bliStateSystem (spliceRat H segmentPrice)
              (denominatorMesh (spliceRat H segmentPrice)) c).actual (n + 1))) /
        Bli.spliceBli H segmentPrice (denominatorMesh (spliceRat H segmentPrice)) c n
          (stateAtom (n + 1)
            ((bliStateSystem (spliceRat H segmentPrice)
              (denominatorMesh (spliceRat H segmentPrice)) c).actual (n + 1))) := by
  rw [eq_div_iff (segmentTent_actual_next_pos H c hn).ne']
  exact Bli.spliceBli_update_exact_denominator H segmentPrice (segmentPrice_inUnit H) c n hφ

end

end Cleanroom.Bli.BliExactBase.Uncharged
