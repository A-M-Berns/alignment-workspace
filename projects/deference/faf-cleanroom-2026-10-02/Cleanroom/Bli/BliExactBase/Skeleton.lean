import Cleanroom.Bli.BliExactBase.Bli

/-!
# `bli-exact-base` · Skeleton: `segmentSkeleton` — the linked kernel as `bli-finite` skeleton
data on the segment (for `bli-witness-lia`)

K7d's kernel market (`Kernel.kMix`, `Segment.kernelMarket`) is a world mixture whose day-`(n+1)`
candidates are *cell patterns* on three coordinates (`kSystem`, cells `{0,1}`). `bli-witness-lia`
instantiates `udt-bli-sist`'s `sistSkel sk n h t coin c V r₀ Qh` with a `Skeleton 𝒮 d`, a day-`n`
table `t` and a coin sentence (udt-bli-sist report § Interface notes 5), so the same kernel is
packaged here in `bli-finite`'s shape: on day `n < H` the law at the linked table
`linkedTable n` (= `actualTable smallIndex (spliceRat H linkedPrice) n`, the realized day-`n`
table of the linked splice) is the **two-point law** on the two **slice marginals** — the uniform
averages, over the day-`n` family of record, of the true slice (`freshCoord` true, `q₁`'s
pattern) and of the false slice (`freshCoord` false, `q₀`'s pattern), as full day-`(n+1)` tables
(`sliceT n`, `sliceF n`); at every other table, and on every day `≥ H`, the law is the tent's.
Balance is the kernel's own decomposition `linkedPrice n = ½ · sliceT n + ½ · sliceF n`
(`linkedPrice_eq_avg`); the laws are probabilities on the grid of `segmentMesh K` because the
family of record has `2 ^ k₀ n` members (`Segment.kAt`) and `k₀ n + 1 ≤ K` on the segment
(`segmentK`). **The coin**: on days `1 ≤ n < H` the two charged tables are distinct and differ
exactly as U15 wants at `freshCoord` — `sliceT n` prices it `1`, `sliceF n` prices it `0`, while
the day-`n` table prices it `1/2` (days `≥ 2`); so `sistSkel` at this skeleton puts mass `1/2` on
"coin true" and `1/2` on "coin false", with the day-`n` kernel law equal to the state mass at
horizon one (`stateMass_sistSkel_h0`).

What the skeleton BLI `bliHistory (spliceRat H linkedPrice) (segmentMesh K) (segmentSkeleton …) c`
has: the scoped Roman bundle on every day (`bliHistory_isBLI_scoped` is over any skeleton), the
product-form small-sentence update on segment days (`bli_update_small_exact_of_gridVal`) — which
is `x · 0 = 0` there, since the two-point law charges the realized next table `0`
(`Uncharged.segmentBli_actual_next_zero`; repair round 1, audit r1 adversarial B3) — and the two
charged states at `1/2` (`segmentBli_state_half`). What it does not have: the criterion — stated
OPEN (`segmentBli_isLogicalInductor`, mandate § 6): the tent's own criterion is `partial`
(`bli-assemble`'s `C`/`hov`), no expression map is defined for the modified skeleton, and the
day-wise finite-perturbation route is closed in general (`not_overgeneral_ifp`). **The chain
across days does not hold in this shape**: the realized day-`(n+1)` table `linkedTable (n+1)`
prices `freshCoord` at `1/2` and is neither slice marginal (each is certain about `freshCoord`),
so the two-point law does not charge it — the cell-form chain (`Segment.linked_actual_state_charged`:
the realized *rounded* pattern is `q₁`) is the chain statement of record; in the table form it
would need interior candidates (findings F17's four-cell kernel), not built.

Sources: mandate § 4 (K7d stretch: "`segmentSkeleton : Skeleton smallIndex (segmentMesh H K).d`-shaped
data on the segment (tent off the segment) for `bli-witness-lia`, with `Balanced` and `IsProb`
proved on the segment"), § 6, § Deliverables (stable names); udt-bli-sist report § Interface notes 5.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliAssemble Cleanroom.Bli.BliTransfer

namespace Skel

open Classical

noncomputable section

/-! ## The slice marginals -/

/-- **A slice marginal**: the uniform average, over the day-`n` family of record `Segment.WAt n`,
of the slice worlds with `freshCoord` set to `b` and the day-`(n+1)` cell-literal pattern
`(x, y, z)`, as a day-`(n+1)` table on `smallIndex`.
Source: mandate § 4 (K7d stretch, the skeleton's candidates); `Kernel.slice`
Kind: D
Fidelity: exact -/
def sliceTable (n x y z : ℕ) (b : Prop) : Table smallIndex (n + 1) :=
  fun φ => ∑ i : Fin (Segment.kAt n), (1 / (Segment.kAt n : ℚ)) *
    (Kernel.slice ((paperDP 𝗜𝚺₁).D n) (n + 1) x y z b (Segment.WAt n i)).payoutRat φ.1

/-- The true slice marginal (`q₁`'s pattern, `freshCoord` true).
Source: mandate § 4
Kind: D
Fidelity: exact -/
abbrev sliceT (n : ℕ) : Table smallIndex (n + 1) := sliceTable n 1 0 1 True

/-- The false slice marginal (`q₀`'s pattern, `freshCoord` false).
Source: mandate § 4
Kind: D
Fidelity: exact -/
abbrev sliceF (n : ℕ) : Table smallIndex (n + 1) := sliceTable n 0 0 1 False

/-- **The linked table as a `bli-finite` table** on day `n`: `linkedPrice n` on the day-`n` small
sentences — the realized day-`n` table of the linked splice on segment days
(`actualTable_eq_linkedTable`). The linked analogue of `Tables.segmentTable` (the stable name of
the mandate's Deliverables for the unlinked tables).
Source: mandate § Deliverables (`segmentTable n : Table smallIndex n`, linked form)
Kind: D
Fidelity: exact -/
def linkedTable (n : ℕ) : Table smallIndex n := fun φ => Segment.linkedPrice n φ.1

/-- The linked table lies in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedTable_inUnit (n : ℕ) : (linkedTable n).InUnit :=
  fun φ => Kernel.kMixRat_mem_Icc _ _ (Segment.WAt_spec n).1 _ φ.1

/-- **The kernel's decomposition**: the linked price is the half-half average of the two slice
marginals, on every day-`(n+1)` small sentence.
Source: mandate § 4 (`P n := ∑_c μ c · ρ_{q_c}`; `Q n` its marginal); `Kernel.kMix_eq_avg`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem linkedPrice_eq_avg (n : ℕ) (φ : ↥(smallIndex.S (n + 1))) :
    Segment.linkedPrice n φ.1 = 1 / 2 * sliceT n φ + 1 / 2 * sliceF n φ := by
  simp only [sliceT, sliceF, sliceTable, Segment.linkedPrice, Kernel.kMixRat]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Kernel.kWorld]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

/-- A slice marginal's value is a count over the family: a grid value of denominator `kAt n`.
Source: none: infrastructure (as `Bli.kMixRat_mem_gridVals`)
Kind: L
Fidelity: n/a -/
lemma sliceTable_mem_gridVals (n x y z : ℕ) (b : Prop) (φ : ↥(smallIndex.S (n + 1))) :
    sliceTable n x y z b φ ∈ gridVals (Segment.kAt n) := by
  rw [mem_gridVals_iff]
  refine ⟨(Finset.univ.filter fun i : Fin (Segment.kAt n) =>
    (Kernel.slice ((paperDP 𝗜𝚺₁).D n) (n + 1) x y z b (Segment.WAt n i)).Holds φ.1).card, ?_, ?_⟩
  · calc _ ≤ (Finset.univ : Finset (Fin (Segment.kAt n))).card := Finset.card_filter_le _ _
      _ = Segment.kAt n := by simp
  · unfold sliceTable
    simp only [PCWorld.payoutRat]
    rw [← Finset.mul_sum, Finset.sum_boole]
    ring

/-- A slice marginal is a grid table of any mesh whose day-`(n+1)` denominator `kAt n` divides.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sliceTable_mem_grid {d : ℕ → ℕ} {n : ℕ} (hd : 0 < d (n + 1))
    (hdvd : Segment.kAt n ∣ d (n + 1)) (x y z : ℕ) (b : Prop) :
    sliceTable n x y z b ∈ grid smallIndex d (n + 1) :=
  mem_grid_iff.mpr fun φ => gridVals_mono hdvd hd (sliceTable_mem_gridVals n x y z b φ)

/-- **The coin**: a slice marginal prices `freshCoord` at `1` or `0` according to its slice.
Source: mandate § 4; udt-bli-sist report § Interface notes 5 (the coin sentence)
Kind: L
Fidelity: n/a -/
lemma sliceTable_fresh (n x y z : ℕ) (b : Prop) (h : freshCoord ∈ smallIndex.S (n + 1)) :
    sliceTable n x y z b ⟨freshCoord, h⟩ = if b then 1 else 0 := by
  have hk : (Segment.kAt n : ℚ) ≠ 0 := by exact_mod_cast (Segment.WAt_spec n).1.ne'
  unfold sliceTable
  simp only [PCWorld.payoutRat, Kernel.slice_holds_fresh]
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The two slice marginals are distinct** on every day `1 ≤ n`: they differ at `freshCoord`
(small on day `n + 1 ≥ 2`).
Source: mandate § 4 ("two distinct charged candidates")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem sliceT_ne_sliceF {n : ℕ} (h1 : 1 ≤ n) : sliceT n ≠ sliceF n := by
  intro h
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  have := congrFun h ⟨freshCoord, hf⟩
  simp only [sliceT, sliceF] at this
  rw [sliceTable_fresh, sliceTable_fresh] at this
  simp at this

/-! ## The two-point law and the segment kernel -/

/-- **The two-point law**: mass `1/2` on each slice marginal.
Source: mandate § 4 (K7d stretch); `Kernel.kMix_two_charged`
Kind: D
Fidelity: exact -/
def twoPointLaw (n : ℕ) : Superbelief smallIndex (n + 1) :=
  fun Q => (if Q = sliceT n then 1 / 2 else 0) + (if Q = sliceF n then 1 / 2 else 0)

/-- The two-point law is a probability on any grid containing both marginals.
Source: mandate § 4 ("with `Balanced` and `IsProb` proved on the segment")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem twoPointLaw_isProb {d : ℕ → ℕ} {n : ℕ} (hT : sliceT n ∈ grid smallIndex d (n + 1))
    (hF : sliceF n ∈ grid smallIndex d (n + 1)) : IsProb d (twoPointLaw n) := by
  refine ⟨fun Q => ?_, fun Q hQ => ?_, ?_⟩
  · unfold twoPointLaw; split_ifs <;> norm_num
  · unfold twoPointLaw
    rw [if_neg (show ¬ Q = sliceT n from fun h => hQ (by rw [h]; exact hT)),
      if_neg (show ¬ Q = sliceF n from fun h => hQ (by rw [h]; exact hF))]
    norm_num
  · unfold twoPointLaw
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hT, if_pos hF]
    norm_num

/-- **Balance at the linked table**: the restricted mean of the two-point law is the linked
table — the kernel's decomposition `linkedPrice_eq_avg`.
Source: mandate § 4 ("with `Balanced` and `IsProb` proved on the segment"); bli-slides-017 constraint 4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem twoPointLaw_balanced {d : ℕ → ℕ} {n : ℕ} (hT : sliceT n ∈ grid smallIndex d (n + 1))
    (hF : sliceF n ∈ grid smallIndex d (n + 1)) :
    Balanced d (twoPointLaw n) (linkedTable n) := by
  intro φ
  show meanOn (grid smallIndex d (n + 1)) (twoPointLaw n) ⟨φ.1, _⟩ = Segment.linkedPrice n φ.1
  unfold meanOn twoPointLaw
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', if_pos hT,
    if_pos hF]
  exact (linkedPrice_eq_avg n _).symm

/-- The two-point law charges each slice marginal `1/2` when they are distinct.
Source: mandate § 4 ("two distinct charged candidates")
Kind: L
Fidelity: n/a -/
lemma twoPointLaw_charged {n : ℕ} (hne : sliceT n ≠ sliceF n) :
    twoPointLaw n (sliceT n) = 1 / 2 ∧ twoPointLaw n (sliceF n) = 1 / 2 := by
  unfold twoPointLaw
  rw [if_pos rfl, if_neg hne, if_neg hne.symm, if_pos rfl]
  norm_num

/-- **The segment kernel** on day `n` for a mesh `𝓜`: the two-point law at the linked table, the
tent law at every other table. A `bli-finite` `Kernel`: probability on the grid and balance for
every table in the unit cube.
Source: mandate § 4 (K7d stretch: "tent off the segment")
Kind: D
Fidelity: exact -/
def segKernel (𝓜 : Mesh) (n : ℕ) (hT : sliceT n ∈ grid smallIndex 𝓜.d (n + 1))
    (hF : sliceF n ∈ grid smallIndex 𝓜.d (n + 1)) : BliFinite.Kernel smallIndex 𝓜.d n where
  law t := if t = linkedTable n then twoPointLaw n else tentLaw 𝓜 n t
  prob t := by
    split_ifs
    · exact twoPointLaw_isProb hT hF
    · exact tentLaw_isProb t
  balanced t ht := by
    split_ifs with h
    · subst h; exact twoPointLaw_balanced hT hF
    · exact tentLaw_balanced ht

/-- **The segment's `K`**: `∑_{m < H} (k₀ m + 1)`, so that `k₀ n + 1 ≤ K` on every day `n < H`
— the `K` of `Bli.exists_segment_K`, named.
Source: mandate § Definitions ("choose `K` so every hand-built value has denominator dividing `2 ^ K`")
Kind: D
Fidelity: exact -/
def segmentK (H : ℕ) : ℕ := ∑ m ∈ Finset.range H, (Segment.k₀ m + 1)

/-- `k₀ n + 1 ≤ segmentK H` for `n < H`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma k₀_add_one_le_segmentK {H n : ℕ} (hn : n < H) : Segment.k₀ n + 1 ≤ segmentK H :=
  Finset.single_le_sum (f := fun m => Segment.k₀ m + 1) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hn)

/-- On a segment day the family size divides the next day's segment-mesh denominator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kAt_dvd_segmentMesh {H K n : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) (hn : n < H) :
    Segment.kAt n ∣ (Bli.segmentMesh K).d (n + 1) := by
  show 2 ^ Segment.k₀ n ∣ 2 ^ (n + 1 + K)
  exact pow_dvd_pow 2 (by have := hK n hn; omega)

/-- **The segment skeleton** at horizon `H` and a `K` with `k₀ n + 1 ≤ K` on the segment: the
segment kernel on every day `n < H`, the tent kernel on every day `≥ H`. A `bli-finite`
`Skeleton smallIndex (segmentMesh K).d` — the stable name of the mandate's Deliverables for
`bli-witness-lia`.
Source: mandate § 4 (K7d stretch), § Deliverables (`segmentSkeleton`)
Kind: D
Fidelity: exact (two-point law at the linked table on segment days; tent elsewhere) -/
def segmentSkeleton (H K : ℕ) (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) :
    Skeleton smallIndex (Bli.segmentMesh K).d :=
  ⟨fun n => if hn : n < H then
      segKernel (Bli.segmentMesh K) n
        (sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 1 0 1 True)
        (sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 0 0 1 False)
    else tentKernel (Bli.segmentMesh K) n⟩

/-- On a segment day the skeleton's law at the linked table is the two-point law.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentSkeleton_law_linked {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ}
    (hn : n < H) : ((segmentSkeleton H K hK).κ n).law (linkedTable n) = twoPointLaw n := by
  show ((if hn : n < H then _ else _ : BliFinite.Kernel smallIndex _ n)).law _ = _
  rw [dif_pos hn]
  show (if linkedTable n = linkedTable n then _ else _) = _
  rw [if_pos rfl]

/-- On a segment day the realized table of the linked splice is the linked table.
Source: none: infrastructure (`Bli.spliceRat_eq_tbl_of_lt`)
Kind: L
Fidelity: n/a -/
lemma actualTable_eq_linkedTable {H n : ℕ} (hn : n < H) :
    actualTable smallIndex (spliceRat H Segment.linkedPrice) n = linkedTable n :=
  funext fun φ => Bli.spliceRat_eq_tbl_of_lt hn φ.2

/-! ## The skeleton BLI over the linked splice -/

/-- **The skeleton BLI**: `bli-trajectory`'s construction at the linked splice, the segment mesh
and the segment skeleton.
Source: mandate § 4 (K7d stretch), § 6
Kind: D
Fidelity: exact -/
abbrev segmentBli (H K : ℕ) (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) : History :=
  bliHistory (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) (segmentSkeleton H K hK) c

/-- **The two slice marginals are the charged day-`(n+1)` states of the skeleton BLI, `1/2`
each**, on every day `1 ≤ n < H`: the BLI's day-`n` price of the state atom of `sliceT n` (and
of `sliceF n`) is `1/2` — U15's two states, differing at the coin `freshCoord`
(`sliceTable_fresh`), while the day-`n` base prices the coin at `1/2` (`linked_fresh_half`).
Source: mandate § 4 (K7d stretch); udt-bli-sist report § Interface notes 5
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem segmentBli_state_half {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) {n : ℕ} (h1 : 1 ≤ n) (hn : n < H) :
    bliPrice (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) (segmentSkeleton H K hK) c n
        (stateAtom (n + 1) (c.code (n + 1) (sliceT n))) = 1 / 2 ∧
      bliPrice (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) (segmentSkeleton H K hK) c n
        (stateAtom (n + 1) (c.code (n + 1) (sliceF n))) = 1 / 2 := by
  have hT := sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 1 0 1 True
  have hF := sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 0 0 1 False
  obtain ⟨hcT, hcF⟩ := twoPointLaw_charged (sliceT_ne_sliceF h1)
  constructor
  · rw [bliPrice_state c _ _ n hT, actualTable_eq_linkedTable hn, segmentSkeleton_law_linked hK hn,
      hcT]
  · rw [bliPrice_state c _ _ n hF, actualTable_eq_linkedTable hn, segmentSkeleton_law_linked hK hn,
      hcF]

/-- **The skeleton BLI carries the scoped Roman bundle** against the linked splice as base
(`bli-trajectory`'s `bliHistory_isBLI_scoped`, over any skeleton).
Source: mandate § 4; `bli-trajectory` M3
Kind: C
Fidelity: weaker: faith scoped (as `bli-trajectory`'s row)
Hyps: (a) -/
theorem segmentBli_isBLI_scoped {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) :
    IsBLI_RomanScoped c (bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) c)
      (Segment.linkedSplice H) (segmentBli H K hK c) :=
  bliHistory_isBLI_scoped c _ _
    (Bli.spliceRat_range H Segment.linkedPrice (Segment.linkedPrice_inUnit H))

/-- **The skeleton BLI satisfies the product-form update on segment days**
(`Bli.bli_update_small_exact_of_gridVal` is over any skeleton) — **vacuously**: on every segment
day `1 ≤ n`, `n + 1 < H` the two-point law gives the realized day-`(n+1)` table mass `0` (its
candidates are certain about `freshCoord`, the realized table prices it `1/2`; findings F19), so
both sides are `0` (`Uncharged.segmentBli_actual_next_zero'`). The day-`n` conditional on the
realized state is undefined under this skeleton; the realized trajectory has prior probability
`0` under its law read as a SIST prior (`bli-witness-lia`, note this).
Source: mandate § 5 (ii), § 4; repair round 1 (audit r1 adversarial B3)
Kind: C
Fidelity: weaker: product form; vacuous (`𝐏_n(σ) = 0`) on every segment day `n ≥ 1`
Hyps: (a) -/
theorem segmentBli_update_exact {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) {n : ℕ} (hn : n + 1 < H) {φ : Sentence}
    (hφ : φ ∈ smallSet n) :
    segmentBli H K hK c (n + 1) φ *
        segmentBli H K hK c n
          (stateAtom (n + 1)
            ((bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) c).actual
              (n + 1))) =
      segmentBli H K hK c n
        (φ ⋏ stateAtom (n + 1)
          ((bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) c).actual
            (n + 1))) :=
  Bli.bli_update_small_exact_of_gridVal c _ _ n hφ
    (by rw [Bli.spliceRat_eq_tbl_of_lt hn (smallSet_mono (Nat.le_succ n) hφ)]
        exact gridVals_mono (pow_dvd_pow 2 (by have := hK (n + 1) hn; omega))
          (Nat.two_pow_pos _) (Bli.linkedPrice_mem_gridVals (n + 1) φ))

/-- **OPEN — the skeleton BLI as a logical inductor** (mandate § 6): whether
`bliHistory (spliceRat H linkedPrice) (segmentMesh K) (segmentSkeleton H K hK) c` is a logical
inductor over `paperDP 𝗜𝚺₁`. Obstructions recorded: the tent BLI's own criterion is `partial`
(`bli-assemble`'s `C`/`hov`, OPEN there); no expression map is defined for the modified skeleton
(`bli-assemble`'s `tentMap` is the template; the two-point law's chain probabilities are constants
on the segment, so its expressions may be cheaper than the tent's — not probed); and the
day-wise finite-perturbation route is closed in general — the skeleton BLI differs from the tent
BLI on finitely many *days* but infinitely many sentences, which `thm:ifp` does not cover and
`not_overgeneral_ifp` refutes as a general principle. Status never above `partial`.
Source: mandate § 6
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem segmentBli_isLogicalInductor (H K : ℕ) (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K)
    (c : StateCoding (Bli.segmentMesh K)) :
    IsLogicalInductor (segmentBli H K hK c) (paperDP 𝗜𝚺₁) := by
  sorry

end

end Skel

end Cleanroom.Bli.BliExactBase
