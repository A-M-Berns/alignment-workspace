import Cleanroom.Bli.BliMeasure.Base
import Cleanroom.Bli.BliMeasure.Dogmatism

/-!
# `bli-measure` · Witness: the N+ instance of exact Bayesian update over the recursion of record
(targets 3 and 4)

Over `paperDP 𝗜𝚺₁`, the coherent recursion of record (`X := smallSet`), and the **denominator mesh**
of its base (on which rounding is the identity and `MeshFine` holds on every day), at every day
`n ≥ 2`:

* the realized next state is charged (`paper_realized_charged`, from `realized_charged` with the
  recursion's full support) — the update is never null-conditioned;
* a **second** candidate is charged (`paper_second_candidate`): the point mass at the extension of
  a consistent world, which differs from the realized state because the realized state has full
  support on the stage's consistent worlds, of which there are at least two
  (`paper_two_consistent` — the stage mentions no state-tagged atom, so the atom `90 =
  Nat.pair stateTag 0` — the code of `stateAtom 0 0`, a state-tagged atom that is **not** a
  candidate's (`0 ∉ wstates 0`), hence read from the base world (`sysState`'s disclosed
  convention) — which is within the bound from day `2` on, can be flipped freely);
* hence `0 < 𝐏_n(σ_{n+1}) < 1`, and for a sentence of the **shape** of `bli-trajectory`'s
  `tb_refuted_at`'s (`ψ := ∼⌜𝑸_{n+2} = q⌝`; there with the zero table's code, here with the
  realized `q`) `0 < 𝐏_{n+1}(ψ) < 1`, and the identity
  `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)` holds (`paper_TB_witness`): the identity that fails for B1
  holds for B3 on a non-degenerate instance. **N+.** The numeric values are not computed: the
  face average is a `Classical.choose`d average of chosen balance solutions (bli-superbelief's
  design), so "both sides computed" is out of reach for any instance; what is established is that
  both factors and the conjunction lie strictly inside `(0, 1)`.

Everything here is conditional on `bli-coherent-mm`: computability open.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliCoherentMm

/-- The base of record over the paper process.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperBase (ov : Overlay) : CoherentBase (paperDP 𝗜𝚺₁) :=
  recBase (paperDP 𝗜𝚺₁) ov paperDP_hcons

/-- The denominator mesh of the base of record over the paper process.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperMesh (ov : Overlay) : Mesh := denomMesh (paperBase ov)

/-- **The realized next state is charged on every day** over the paper process on the denominator
mesh.
Source: [[bli-measure-mandate]] target 4 (over the recursion)
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paper_realized_charged (ov : Overlay) (n : ℕ) :
    0 < superbelief (b3History (paperBase ov) (paperMesh ov)) n
      (b3Actual (paperBase ov) (paperMesh ov) (n + 1)) :=
  realized_charged _ _ (recBase_fullSupport _ ov paperDP_hcons n) (meshFine_denomMesh _ n)

/-! ## Two consistent worlds -/

/-- The atom `90 = Nat.pair stateTag 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_stateTag_zero : Nat.pair stateTag 0 = 90 := by decide

/-- The free atom's tag is the state tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unpair_90 : (Nat.unpair 90).1 = stateTag := by
  rw [← pair_stateTag_zero, Nat.unpair_pair]

/-- The free atom is a day-`2` small sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atom_90_small (n : ℕ) (hn : 2 ≤ n) : Formula.atom 90 ∈ smallSet n := by
  rw [mem_smallSet]
  unfold SmallOn
  rw [tokenSize_atom]
  have h1 : (natDigits4 (90 + 5)).length = 4 := by
    rw [length_natDigits4_eq_log (by norm_num)]
    have : Nat.log 4 95 = 3 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    rw [this]
  rw [h1]
  calc 4 + 1 ≤ sizeBound 2 := by unfold sizeBound; norm_num
    _ ≤ sizeBound n := sizeBound_mono hn

/-- The free atom lies within the bound from day `2` on.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_recB_90 (ov : Overlay) (n : ℕ) (hn : 2 ≤ n) : 90 < (paperBase ov).𝔅.B n :=
  lt_of_lt_of_le (Nat.lt_succ_self 90)
    (show atomBound (Formula.atom 90) ≤ _ from (paperBase ov).𝔅.B_cover n _ (atom_90_small n hn))

/-- **Two consistent worlds** over the bound, on every day `n ≥ 2`: a restriction of a consistent
`PCWorld`, and the same with the free atom flipped. The free atom `90` is the code of
`stateAtom 0 0` — a state-tagged atom of a non-candidate code, which B3 reads from the base
world (`sysState`'s disclosed convention), not a propositional atom of the base.
Source: [[bli-measure-mandate]] target 3 (witness: "a day with ≥ 2 charged next states")
Kind: N+
Fidelity: exact
Hyps: (a) `hn` -/
theorem paper_two_consistent (ov : Overlay) (n : ℕ) (hn : 2 ≤ n) :
    ∃ u₁ u₂ : FiniteWorld ((paperBase ov).𝔅.B n), u₁ ≠ u₂ ∧
      (worldOf u₁).ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
      (worldOf u₂).ConsistentWith ((paperDP 𝗜𝚺₁).D n) := by
  classical
  obtain ⟨v, hv⟩ := paperDP_hcons n
  set B := (paperBase ov).𝔅.B n
  let u₁ : FiniteWorld B := FiniteWorld.restrict (ofPCWorld v) B
  have h90 : 90 < B := lt_recB_90 ov n hn
  let i : Fin B := ⟨90, h90⟩
  let u₂ : FiniteWorld B := Function.update u₁ i (!u₁ i)
  have hfree := paperDP_tagFree 𝗜𝚺₁ (le_refl stateTag)
  have hu₁ : (worldOf u₁).ConsistentWith ((paperDP 𝗜𝚺₁).D n) := by
    intro φ hφ
    exact (holds_worldOf_restrict v ((paperBase ov).B_stage n φ hφ)).mpr (hv φ hφ)
  refine ⟨u₁, u₂, ?_, hu₁, ?_⟩
  · intro h
    have := congrFun h i
    simp only [u₂, Function.update_self] at this
    cases u₁ i <;> simp at this
  · intro φ hφ
    have hφfree := hfree n φ hφ
    have hagree : ∀ a ∈ sentenceAtomCodes φ, (worldOf u₁) a ↔ (worldOf u₂) a := by
      intro a ha
      have hne : a ≠ 90 := by
        intro h90'
        apply hφfree a ha
        rw [h90']
        exact unpair_90
      show u₁.toBoolPCWorld a = true ↔ u₂.toBoolPCWorld a = true
      unfold FiniteWorld.toBoolPCWorld
      split_ifs with ha'
      · have : (⟨a, ha'⟩ : Fin B) ≠ i := fun h => hne (congrArg Fin.val h)
        simp only [u₂, Function.update_of_ne this]
      · exact Iff.rfl
    exact (PCWorld.holds_congr_atomCodes φ hagree).mp (hu₁ φ hφ)

/-! ## A second charged candidate -/

/-- The vector of a point table is the point mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vecOf_pointTable {B : ℕ → ℕ} (m : ℕ) (u₀ u : FiniteWorld (B m)) :
    vecOf (pointTable m u₀) u = if u₀ = u then 1 else 0 := by
  show pointTable m u₀ (wcSelf m u) = _
  rw [pointTable_apply, wcAt_val, payoutRat_worldConj_self]

/-- The rounded measure of the paper base has at least two support worlds on every day `n ≥ 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paper_measureRound_two_support (ov : Overlay) (n : ℕ) (hn : 2 ≤ n) :
    ∃ u₁ u₂ : FiniteWorld ((paperBase ov).𝔅.B n), u₁ ≠ u₂ ∧
      measureRound (paperBase ov) (paperMesh ov) n u₁ ≠ 0 ∧
      measureRound (paperBase ov) (paperMesh ov) n u₂ ≠ 0 := by
  obtain ⟨u₁, u₂, hne, h₁, h₂⟩ := paper_two_consistent ov n hn
  refine ⟨u₁, u₂, hne, ?_, ?_⟩
  · exact (measureRound_ne_zero_iff_of_meshFine _ _ (meshFine_denomMesh _ n) u₁).mpr
      (recBase_fullSupport _ ov paperDP_hcons n u₁ h₁)
  · exact (measureRound_ne_zero_iff_of_meshFine _ _ (meshFine_denomMesh _ n) u₂).mpr
      (recBase_fullSupport _ ov paperDP_hcons n u₂ h₂)

/-- **A second charged candidate**: on every day `n ≥ 2` there is a day-`(n+1)` grid table in the
face of the rounded table that is not the realized next state.
Source: [[bli-measure-mandate]] target 3 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) `hn` -/
theorem paper_second_candidate (ov : Overlay) (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q' ∈ faceGen (cgrid (paperBase ov).𝔅 (paperMesh ov) (n + 1))
        (roundedTable (paperBase ov) (paperMesh ov) n),
      Q' ≠ roundedTable (paperBase ov) (paperMesh ov) (n + 1) := by
  obtain ⟨u₁, -, -, h₁, -⟩ := paper_two_consistent ov n hn
  let v : FiniteWorld ((paperBase ov).𝔅.B (n + 1)) := extFW ((paperBase ov).𝔅.B_mono n) u₁
  refine ⟨pointTable (n + 1) v, ?_, ?_⟩
  · apply candidate_charged_of_support (paperBase ov) (paperMesh ov)
      (recBase_fullSupport _ ov paperDP_hcons n) (meshFine_denomMesh _ n)
      (pointTable_mem_cgrid (paperBase ov).𝔅 (paperMesh ov) (n + 1) v)
    intro u' hu'
    change vecOf (pointTable (n + 1) v) u' ≠ 0 at hu'
    rw [vecOf_pointTable] at hu'
    have : v = u' := by
      by_contra h
      rw [if_neg h] at hu'
      exact hu' rfl
    rw [← this]
    show (worldOf (restrFW ((paperBase ov).𝔅.B_mono n)
      (extFW ((paperBase ov).𝔅.B_mono n) u₁))).ConsistentWith _
    rw [restrFW_extFW]
    exact h₁
  · intro heq
    obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ := paper_measureRound_two_support ov (n + 1) (by omega)
    have h1 := congrFun (vecOf_roundedTable (paperBase ov) (paperMesh ov) (n + 1)) w₁
    have h2 := congrFun (vecOf_roundedTable (paperBase ov) (paperMesh ov) (n + 1)) w₂
    rw [← heq, vecOf_pointTable] at h1 h2
    rw [← h1] at hw₁
    rw [← h2] at hw₂
    by_cases hv1 : v = w₁
    · rw [if_pos hv1] at hw₁
      have hv2 : v ≠ w₂ := fun h => hne (hv1.symm.trans h)
      rw [if_neg hv2] at hw₂
      exact hw₂ rfl
    · rw [if_neg hv1] at hw₁
      exact hw₁ rfl

/-- **`𝐏_n(σ_{n+1}) < 1`** on every day `n ≥ 2` over the paper process: the kernel charges a second
candidate.
Source: [[bli-measure-mandate]] target 3 (witness, "`𝐏_n(σ) < 1`")
Kind: N+
Fidelity: exact
Hyps: (a) `hn` -/
theorem paper_superbelief_actual_lt_one (ov : Overlay) (n : ℕ) (hn : 2 ≤ n) :
    superbelief (b3History (paperBase ov) (paperMesh ov)) n
      (b3Actual (paperBase ov) (paperMesh ov) (n + 1)) < 1 := by
  set base := paperBase ov
  set 𝓜 := paperMesh ov
  obtain ⟨Q', hQ'face, hQ'ne⟩ := paper_second_candidate ov n hn
  have hrt := roundedTable_mem_cgrid base 𝓜 n
  unfold superbelief
  rw [b3History_stateAtom_succ base 𝓜 n (b3Actual_mem base 𝓜 (n + 1)), wdecode_b3Actual]
  have hprob := ((faceSkeleton base.𝔅 𝓜).κ n).prob _ hrt
  have hpos : 0 < ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) Q' :=
    (faceKernel_pos_iff base.𝔅 𝓜 hrt Q').mpr hQ'face
  have hQ'mem : Q' ∈ cgrid base.𝔅 𝓜 (n + 1) := faceGen_subset _ _ hQ'face
  have hpair : ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) (roundedTable base 𝓜 (n + 1)) +
      ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) Q' ≤ 1 := by
    rw [← hprob.2.2, ← Finset.sum_pair hQ'ne.symm]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun Q _ _ => hprob.1 Q)
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact roundedTable_mem_cgrid base 𝓜 (n + 1)
    · exact hQ'mem
  have : ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) (roundedTable base 𝓜 (n + 1)) < 1 := by
    linarith
  exact_mod_cast this

/-! ## The witness -/

/-- **The N+ instance of exact Bayesian update** (target 3's witness): over the paper process on
the denominator mesh, on every day `n ≥ 2`, with `σ := ⌜𝑸_{n+1} = actual (n+1)⌝` and
`ψ := ∼⌜𝑸_{n+2} = actual (n+2)⌝` (the sentence of `bli-trajectory`'s `tb_refuted_at`, at the
realized code): `0 < 𝐏_n(σ) < 1`, `0 < 𝐏_{n+1}(ψ) < 1`, and `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)`.
The identity that fails for B1 holds for B3 on a non-degenerate instance.
Source: [[bli-measure-mandate]] target 3 (witness); `bli-trajectory` `tb_refuted_at`
Kind: N+
Fidelity: exact (the numeric values are not computed: the face average is classically chosen;
see the module docstring)
Hyps: (a) `hn` -/
theorem paper_TB_witness (ov : Overlay) (n : ℕ) (hn : 2 ≤ n) :
    0 < b3History (paperBase ov) (paperMesh ov) n
        (stateAtom (n + 1) (b3Actual (paperBase ov) (paperMesh ov) (n + 1))) ∧
    b3History (paperBase ov) (paperMesh ov) n
        (stateAtom (n + 1) (b3Actual (paperBase ov) (paperMesh ov) (n + 1))) < 1 ∧
    0 < b3History (paperBase ov) (paperMesh ov) (n + 1)
        (∼stateAtom (n + 2) (b3Actual (paperBase ov) (paperMesh ov) (n + 2))) ∧
    b3History (paperBase ov) (paperMesh ov) (n + 1)
        (∼stateAtom (n + 2) (b3Actual (paperBase ov) (paperMesh ov) (n + 2))) < 1 ∧
    b3History (paperBase ov) (paperMesh ov) (n + 1)
        (∼stateAtom (n + 2) (b3Actual (paperBase ov) (paperMesh ov) (n + 2))) *
      b3History (paperBase ov) (paperMesh ov) n
        (stateAtom (n + 1) (b3Actual (paperBase ov) (paperMesh ov) (n + 1))) =
    b3History (paperBase ov) (paperMesh ov) n
        (∼stateAtom (n + 2) (b3Actual (paperBase ov) (paperMesh ov) (n + 2)) ⋏
          stateAtom (n + 1) (b3Actual (paperBase ov) (paperMesh ov) (n + 1))) := by
  set base := paperBase ov
  set 𝓜 := paperMesh ov
  have hσpos : 0 < b3History base 𝓜 n (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) :=
    paper_realized_charged ov n
  have hσlt : b3History base 𝓜 n (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) < 1 :=
    paper_superbelief_actual_lt_one ov n hn
  have hσ'pos : 0 < b3History base 𝓜 (n + 1) (stateAtom (n + 2) (b3Actual base 𝓜 (n + 2))) :=
    paper_realized_charged ov (n + 1)
  have hσ'lt : b3History base 𝓜 (n + 1) (stateAtom (n + 2) (b3Actual base 𝓜 (n + 2))) < 1 :=
    paper_superbelief_actual_lt_one ov (n + 1) (by omega)
  have hneg := b3History_add_neg base 𝓜 (n + 1) (stateAtom (n + 2) (b3Actual base 𝓜 (n + 2)))
  refine ⟨hσpos, hσlt, by linarith, by linarith, ?_⟩
  have h := b3_TB base 𝓜 n (∼stateAtom (n + 2) (b3Actual base 𝓜 (n + 2)))
  rw [b3StateSystem_actual] at h
  exact h

end Cleanroom.Bli.BliMeasure
