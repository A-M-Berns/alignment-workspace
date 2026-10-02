import Cleanroom.Bli.BliExactBase.Skeleton
import Cleanroom.Bli.BliExactBase.Uncharged
import Cleanroom.Bli.UdtBliSist.Skeleton

/-!
# `bli-witness-lia` · Prior: the SIST mugging prior over FAF's inductor (U15, T1)

`udt-bli-sist`'s skeleton SIST prior `sistSkel sk n h t coin c V r₀ Qh` is parametric in the
skeleton `sk` and the base table `t`. Here it is instantiated — by instantiation, not by editing —
at the one object the run has that is both a FAF logical inductor and linked to a non-degenerate
superbelief: `bli-exact-base`'s linked splice `Segment.linkedSplice H` (FAF's LIA over
`paperDP 𝗜𝚺₁`, re-priced on days `< H` at the linked kernel table `Segment.linkedPrice`), packaged
as the skeleton `Skel.segmentSkeleton H K hK`. The prior of record is

`segmentSist H K hK n hn h2 c V r₀ := sistSkel (segmentSkeleton H K hK) n 0 (linkedTable n) (coinAt n _) c V r₀ (askTable K hK hn)`

with the coin `freshCoord`, the observed table the kernel's true-slice marginal `Skel.sliceT n`
(Ask) and the Rec table its false-slice marginal `Skel.sliceF n`.

**What is derived, not typed** (the mandate's fake-success checklist): the branch masses
`μ(Ask) = μ(Rec) = 1/2` come through `stateMass_sistSkel_h0` (the `trajLaw` fiber at horizon one
is the kernel's law), `segmentSkeleton_law_linked` (the kernel's law at the linked table is the
two-point law) and `twoPointLaw_charged`; `askC askTable` is proved from `sliceTable_fresh`,
never hypothesized; the base table is the inductor's realized day-`n` table
(`actualTable_eq_linkedTable`); and the coin coordinate of the base table is the inductor's own
price `1/2` (`coin_price`, from `linked_fresh_half` through `linkedSplice_eq_kernel` and
`linkedPrice_cast`). So `μ(Ask) = μ(Rec) = 1/2` is the inductor's price of the coin, read through
the kernel whose mixture the inductor quotes (`linkedPrice_eq_avg`) — U15's "branch beliefs
derived from `E2x` and the inductor's small beliefs".

**Days of record.** Every headline carries `(hn : n < H) (h2 : 2 ≤ n)`: the coin is small on day
`n` only from `n = 2` (`freshCoord_mem_smallSet`; `sizeBound 1 = 4` admits no atom), and
`linked_fresh_half` is stated on `[2, H)`. Nothing here is planted on `n ∈ {0, 1}`.

**Plumbing** (mandate § 5 item 5): the day index is written `n + 0 + 1`, not `n + 1`, so that
`stateMass_sistSkel_h0` (stated at `h = 0`) applies syntactically; `smallIndex` is
`BliTrajectory`'s (the one `Skel` uses); membership in `↥(smallIndex.S m)` is coerced with `show`.

Sources: [[bli-program]] §3.9 (U15), §4 (`D:U-L1`); mandate T1, § 0.2 (the verified
instantiation), § 3.1–3.2; [[bli-exact-base-report]] § 4 (`segmentSkeleton`);
[[udt-bli-sist-report]] § Interface notes 5, § T8.
-/

namespace Cleanroom.Bli.BliWitnessLia

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist

noncomputable section

/-! ## The coin and the two charged tables -/

/-- **The coin**: `freshCoord` as a day-`(n+1)` small sentence (small from day `2`, so for
`1 ≤ n`). The day index is `n + 0 + 1` (horizon `h = 0`), kept syntactic for
`stateMass_sistSkel_h0`.
Source: mandate T1, § 0.2 (`coinAt`); udt-bli-sist report § Interface notes 5 (the coin sentence)
Kind: D
Fidelity: exact -/
def coinAt (n : ℕ) (h1 : 1 ≤ n) : ↥(smallIndex.S (n + 0 + 1)) :=
  ⟨freshCoord, show freshCoord ∈ smallIndex.S (n + 0 + 1) from
    freshCoord_mem_smallSet (by omega)⟩

/-- The coin's sentence is `freshCoord`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma coinAt_val (n : ℕ) (h1 : 1 ≤ n) : (coinAt n h1).1 = freshCoord := rfl

/-- **The Ask table**: the kernel's true-slice marginal `Skel.sliceT n` (the uniform average of
the day-`n` family's worlds with `freshCoord` set true and `q₁`'s day-`(n+1)` literal pattern),
as a grid table of `segmentMesh K` on day `n + 0 + 1`. It is the observed table `Qh` of the
mugging and one of the two charged candidates of the linked splice's own kernel.
Source: mandate T1, § 0.2 (`askTable`); [[bli-exact-base-report]] § 4 (`sliceT`)
Kind: D
Fidelity: exact -/
def askTable (K : ℕ) {H : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) :
    ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)) :=
  ⟨sliceT n, sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 1 0 1 True⟩

/-- **The Rec table**: the kernel's false-slice marginal `Skel.sliceF n` (`freshCoord` false, `q₀`'s
pattern), as a grid table of `segmentMesh K` on day `n + 0 + 1` — the other charged candidate.
Source: mandate T1, § 0.2 (`recTable`); [[bli-exact-base-report]] § 4 (`sliceF`)
Kind: D
Fidelity: exact -/
def recTable (K : ℕ) {H : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) :
    ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)) :=
  ⟨sliceF n, sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 0 0 1 False⟩

/-- The Ask table's underlying table is `sliceT n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma askTable_val (K : ℕ) {H : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ}
    (hn : n < H) : (askTable K hK hn).1 = sliceT n := rfl

/-- The Rec table's underlying table is `sliceF n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma recTable_val (K : ℕ) {H : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ}
    (hn : n < H) : (recTable K hK hn).1 = sliceF n := rfl

/-! ## The prior of record -/

/-- **The SIST mugging prior over the linked splice** (U15, definition of record): `udt-bli-sist`'s
`sistSkel` at the skeleton `segmentSkeleton H K hK` (the linked splice's own kernel on segment
days, two-point law at the linked table), horizon `h = 0` (day `n` to day `n+1`), base table the
inductor's realized day-`n` table `linkedTable n`, coin `freshCoord`, stakes `c` (the ask) and
`V` (the reward), residual `r₀`, observed table the Ask table `sliceT n`. Every structural fact
about it is an instance of `udt-bli-sist`'s theorems at this skeleton; the content of this package
is that its branch masses are the inductor's own prices (`stateMass_ask`, `stateMass_rec`,
`coin_price`). The instance of record takes `K := Skel.segmentK H`, `hK := fun n hn =>
k₀_add_one_le_segmentK hn`, `(c, V) = (10, 100)`.
Source: [[bli-program]] §3.9 (U15: "SIST whose hypotheses are inhabited by a logical inductor");
mandate T1, § 3.1; udt-bli-sist T8 (`sistSkel`)
Kind: D
Fidelity: exact (the "inductor" is the base `Segment.linkedSplice H`; the skeleton BLI
`Skel.segmentBli` is not known to be one, OPEN `Skel.segmentBli_isLogicalInductor`) -/
abbrev segmentSist (H K : ℕ) (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) (n : ℕ) (hn : n < H)
    (h2 : 2 ≤ n) (c V : ℚ) (r₀ : Bool → ℚ) :
    FiniteBLIPrior smallIndex (n + 0 + 1) (grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)) Bool :=
  sistSkel (segmentSkeleton H K hK) n 0 (linkedTable n) (coinAt n (by omega)) c V r₀
    (askTable K hK hn)

section Headlines

variable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
variable (c V : ℚ) (r₀ : Bool → ℚ)

/-! ## The classes: Ask and Rec are the two tables -/

/-- **The Ask table is in the Ask class**: `sliceT n` prices the coin at `1` (`sliceTable_fresh`).
Proved, never hypothesized (mandate § 6).
Source: mandate T1 (`askC_askTable`)
Kind: L
Fidelity: exact -/
lemma askC_askTable : askC n 0 (coinAt n (by omega)) (askTable K hK hn) :=
  (sliceTable_fresh n 1 0 1 True _).trans (by simp)

/-- **The Rec table is in the Rec class**: `sliceF n` prices the coin at `0`.
Source: mandate T1 (`recC_recTable`)
Kind: L
Fidelity: exact -/
lemma recC_recTable : recC n 0 (coinAt n (by omega)) (recTable K hK hn) :=
  (sliceTable_fresh n 0 0 1 False _).trans (by simp)

/-- The Rec table is not in the Ask class (`0 ≠ 1` at the coin).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_askC_recTable : ¬ askC n 0 (coinAt n (by omega)) (recTable K hK hn) := by
  intro h
  have h' : (recTable K hK hn).1 (coinAt n (by omega)) = 1 := h
  rw [recTable_val] at h'
  rw [show (sliceF n) (coinAt n (by omega)) = 0 from
    (sliceTable_fresh n 0 0 1 False _).trans (by simp)] at h'
  norm_num at h'

/-- The Ask table is not in the Rec class (`1 ≠ 0` at the coin).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_recC_askTable : ¬ recC n 0 (coinAt n (by omega)) (askTable K hK hn) := by
  intro h
  have h' : (askTable K hK hn).1 (coinAt n (by omega)) = 0 := h
  rw [askTable_val] at h'
  rw [show (sliceT n) (coinAt n (by omega)) = 1 from
    (sliceTable_fresh n 1 0 1 True _).trans (by simp)] at h'
  norm_num at h'

/-- The two charged tables are distinct (they differ at the coin: `1` versus `0`).
Source: mandate T5 (e) (the § 7 item-11 guard); `Skel.sliceT_ne_sliceF`
Kind: L
Fidelity: exact -/
lemma askTable_ne_recTable (h1 : 1 ≤ n) : askTable K hK hn ≠ recTable K hK hn := fun h =>
  sliceT_ne_sliceF (n := n) h1 (congrArg Subtype.val h)

/-! ## The branch masses are the inductor's own law -/

/-- **`μ(Ask) = 1/2` and `μ(Rec) = 1/2`, derived from the inductor's kernel** (U15's branch
beliefs): the state mass of `sistSkel` at horizon one is the skeleton's law at the base table
(`stateMass_sistSkel_h0`, a `trajLaw` fiber); at the linked table that law is the two-point law
(`segmentSkeleton_law_linked`), which charges each slice marginal `1/2`
(`twoPointLaw_charged`, the two being distinct, `sliceT_ne_sliceF`). The two-point law is the
kernel's decomposition `linkedPrice n = ½·sliceT n + ½·sliceF n` (`Skel.linkedPrice_eq_avg`),
i.e. the mixture the inductor quotes on day `n`. No number is typed in.
Source: [[bli-program]] §3.9 (U15: "`μ` is `trajLaw`"); mandate T1 (`stateMass_ask`,
`stateMass_rec`), § 0.2
Kind: N+ (two distinct charged states at `1/2` each, from the kernel's law)
Fidelity: exact
Hyps: (a) -/
theorem stateMass_ask_rec :
    (segmentSist H K hK n hn h2 c V r₀).stateMass (askTable K hK hn) = 1 / 2 ∧
    (segmentSist H K hK n hn h2 c V r₀).stateMass (recTable K hK hn) = 1 / 2 := by
  unfold segmentSist
  rw [stateMass_sistSkel_h0, stateMass_sistSkel_h0, segmentSkeleton_law_linked hK hn]
  exact twoPointLaw_charged (sliceT_ne_sliceF (by omega))

/-- `μ(Ask) = 1/2` (the first half of `stateMass_ask_rec`).
Source: mandate T1 (`stateMass_ask`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem stateMass_ask :
    (segmentSist H K hK n hn h2 c V r₀).stateMass (askTable K hK hn) = 1 / 2 :=
  (stateMass_ask_rec hK hn h2 c V r₀).1

/-- `μ(Rec) = 1/2` (the second half of `stateMass_ask_rec`).
Source: mandate T1 (`stateMass_rec`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem stateMass_rec :
    (segmentSist H K hK n hn h2 c V r₀).stateMass (recTable K hK hn) = 1 / 2 :=
  (stateMass_ask_rec hK hn h2 c V r₀).2

/-- **Every other grid table has mass `0`**: the two-point law charges nothing but the two slice
marginals. (The realized day-`(n+1)` table of the inductor is among the "other" tables,
`Realized.stateMass_realized_zero`.)
Source: mandate T1 (`stateMass_other_zero`)
Kind: L
Fidelity: exact -/
theorem stateMass_other_zero (T : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)))
    (hA : T ≠ askTable K hK hn) (hR : T ≠ recTable K hK hn) :
    (segmentSist H K hK n hn h2 c V r₀).stateMass T = 0 := by
  unfold segmentSist
  rw [stateMass_sistSkel_h0, segmentSkeleton_law_linked hK hn]
  unfold twoPointLaw
  rw [if_neg (show ¬ (T.1 = sliceT n) from fun h => hA (Subtype.ext h)),
    if_neg (show ¬ (T.1 = sliceF n) from fun h => hR (Subtype.ext h))]
  norm_num

/-- The Ask mass is positive (the positivity `homeEU_sistSkel` needs, derived).
Source: mandate T2 ("positivity of the Ask mass (T1)")
Kind: L
Fidelity: n/a -/
lemma stateMass_ask_pos : 0 < (segmentSist H K hK n hn h2 c V r₀).stateMass (askTable K hK hn) := by
  rw [stateMass_ask]; norm_num

/-- The Rec mass is positive.
Source: mandate T2
Kind: L
Fidelity: n/a -/
lemma stateMass_rec_pos : 0 < (segmentSist H K hK n hn h2 c V r₀).stateMass (recTable K hK hn) := by
  rw [stateMass_rec]; norm_num

/-! ## The class masses -/

/-- **`μ(Ask class) = 1/2`**: the Ask class filter contains the Ask table, and every other table in
it has mass `0` (it is not the Rec table, whose coin is `0`).
Source: mandate T1 (`classMass_ask`)
Kind: L
Fidelity: exact -/
theorem classMass_ask :
    classMass (segmentSist H K hK n hn h2 c V r₀) (univ.filter (askC n 0 (coinAt n (by omega)))) =
      1 / 2 := by
  unfold classMass
  rw [Finset.sum_eq_single (askTable K hK hn)]
  · exact stateMass_ask hK hn h2 c V r₀
  · intro T hT hTA
    have hask : askC n 0 (coinAt n (by omega)) T := (Finset.mem_filter.1 hT).2
    refine stateMass_other_zero hK hn h2 c V r₀ T hTA (fun hTR => ?_)
    exact not_askC_recTable hK hn h2 (hTR ▸ hask)
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, askC_askTable hK hn h2⟩) h

/-- **`μ(Rec ∖ Ask) = 1/2`**: the class `¬ Ask ∧ Rec` contains the Rec table, and every other table
in it has mass `0` (it is not the Ask table, which is in `Ask`).
Source: mandate T1 (`classMass_rec`)
Kind: L
Fidelity: exact -/
theorem classMass_rec :
    classMass (segmentSist H K hK n hn h2 c V r₀)
      (univ.filter (fun T => ¬ askC n 0 (coinAt n (by omega)) T ∧ recC n 0 (coinAt n (by omega)) T)) =
      1 / 2 := by
  unfold classMass
  rw [Finset.sum_eq_single (recTable K hK hn)]
  · exact stateMass_rec hK hn h2 c V r₀
  · intro T hT hTR
    have hnask : ¬ askC n 0 (coinAt n (by omega)) T := (Finset.mem_filter.1 hT).2.1
    refine stateMass_other_zero hK hn h2 c V r₀ T (fun hTA => ?_) hTR
    exact hnask (hTA ▸ askC_askTable hK hn h2)
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      not_askC_recTable hK hn h2, recC_recTable hK hn h2⟩) h

/-- **`μ(Other) = 0`**: the residual class `¬ Ask ∧ ¬ Rec` contains neither charged table, so its
mass is `0` (the two-point law). This is where the witness differs from the source's `49/49/2`
and from the tent's `1/3, 1/3, 1/3`: the residual term of the verdict vanishes identically.
Source: mandate T1 (`classMass_other`), § 3.3, § 5 item 6
Kind: L
Fidelity: exact -/
theorem classMass_other :
    classMass (segmentSist H K hK n hn h2 c V r₀)
      (univ.filter (fun T => ¬ askC n 0 (coinAt n (by omega)) T ∧
        ¬ recC n 0 (coinAt n (by omega)) T)) = 0 := by
  unfold classMass
  refine Finset.sum_eq_zero fun T hT => ?_
  obtain ⟨hnask, hnrec⟩ := (Finset.mem_filter.1 hT).2
  refine stateMass_other_zero hK hn h2 c V r₀ T (fun hTA => ?_) (fun hTR => ?_)
  · exact hnask (hTA ▸ askC_askTable hK hn h2)
  · exact hnrec (hTR ▸ recC_recTable hK hn h2)

/-! ## The tie to the inductor: the base table and the coin's price -/

/-- **The base table is the inductor's realized day-`n` table**: `linkedTable n` is
`actualTable smallIndex (spliceRat H linkedPrice) n`, the day-`n` small prices of the linked splice
(`Skel.actualTable_eq_linkedTable`, restated with the prior's base on the left).
Source: mandate T1 (`baseTable_eq_actual`); udt-bli-sist report § Interface notes 5 ("`t` the
spliced inductor's segment")
Kind: L
Fidelity: exact -/
theorem baseTable_eq_actual (hn : n < H) :
    linkedTable n = BliFinite.actualTable smallIndex (spliceRat H Segment.linkedPrice) n :=
  (actualTable_eq_linkedTable hn).symm

/-- **The coin's price is the inductor's `1/2`**: the base table prices `freshCoord` (small on day
`n ≥ 2`) at `1/2`, and that is the linked splice's own day-`n` price of `freshCoord`
(`Segment.linked_fresh_half`, read back through `linkedSplice_eq_kernel` and `linkedPrice_cast`).
This is the line that says the branch masses `1/2`, `1/2` are the inductor's price of the coin.
Source: mandate T1 (`coin_price`), § 2 ("the mugging's `μ(Ask) = μ(Rec) = 1/2` is the inductor's
own price of the coin, not a number typed in")
Kind: L
Fidelity: exact -/
theorem coin_price (hn : n < H) (h2 : 2 ≤ n) :
    linkedTable n ⟨freshCoord, freshCoord_mem_smallSet h2⟩ = 1 / 2 ∧
    Segment.linkedSplice H n freshCoord = 1 / 2 := by
  have hR : Segment.linkedSplice H n freshCoord = 1 / 2 := Segment.linked_fresh_half hn h2
  refine ⟨?_, hR⟩
  have h := hR
  rw [Segment.linkedSplice_eq_kernel hn (freshCoord_mem_smallSet h2),
    ← Segment.linkedPrice_cast] at h
  show Segment.linkedPrice n freshCoord = 1 / 2
  exact Rat.cast_injective (α := ℝ) (by rw [h]; norm_num)

end Headlines

end

end Cleanroom.Bli.BliWitnessLia
