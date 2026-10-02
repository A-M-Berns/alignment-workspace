import Cleanroom.Bli.BliExactBase.Kernel

/-!
# `bli-exact-base` — K7c (d), K7d: the linked segment over the spliced inductor

**The linked table.** `linkedPrice n` is the day-`n` kernel market (`Kernel.kMix`) over a complete
family `WAt n` of worlds consistent with `(paperDP 𝗜𝚺₁).D n` for the day-`n` small atoms, with the
slices at day `n+1`. It is defined on every day and never reads its own program code (the kernel
overrides every code's literal atoms of the right shape; `Kernel.lean` header). Spliced into FAF's
LIA at horizon `H` it gives `linkedSplice H`, a logical inductor over `paperDP 𝗜𝚺₁`
(`linkedSplice_isLogicalInductor`, K7a at this table) that is a stage mixture on the small
sentences on every day `n < H` (`linked_D_PCsmall_on`, K7b's coherence clause) and prices
`freshCoord` at exactly `1/2` on every day in `[2, H)` (`linked_fresh_half`).

**The package (K7d).** On every day `n` with `2 ≤ n < H`, the BLI market `linkedP H` (the kernel
on days `< H`, the base itself after) and the state system `kSystem rep01` satisfy every hypothesis
of `bli-linkage`'s per-day engine `nnu_day` with the base `Q := linkedSplice H` and the base's
**own** cell family `linkedCF H` (the splice's cell literals, reflected at the splice's rounded
price, `spliceCellSentence_reflected`): coherence, partition, `E1x`, `SpuriousEntails`,
`ValuesAtRep`, faith at all three segment coordinates on every candidate — and two distinct
candidates are charged `1/2` each (`segment_package_inhabited`, N+). No `StageFresh` hypothesis
remains: the day-`(n+1)` literals are fresh at stage `n` for every code
(`QuoteLane.stageFresh_splice`, `Kernel.litIdx_fresh`).

**The identity (K7c (d)).** On every pinned coordinate of every day in `[2, H)`, the base
satisfies the exact cell-form no-net-update identity (`linked_nnu_day`, `nnu_day` applied —
`bli-linkage`'s engine doing work on an inductor's base), so `D_NNUcell_on H 2 (linkedCF H)
segmentIndex (linkedSplice H)` (`segment_D_NNUcell_on`). Pinnedness is what the *base* needs:
the splice re-prices small sentences only, so the base carries the kernel's literal prices exactly
where the day-`(n+1)` literals are small on day `n`; the kernel market itself satisfies the identity
on all three coordinates on every day (`kernel_identity`).

**The cell quote code is a parameter (repair round 2).** `linkedCF H` is the family at the cell
quote code FAF's `ofComputable` selects by `Classical.choice`; nothing bounds that code's size in
either direction, so a statement about *which days are pinned before `H`* at that code is not a
conjecture about the kernel but about which program the choice returned (audit r2 fidelity B1).
Every theorem of this module is therefore proved for the family `linkedCFq H q` at an arbitrary
cell quote code `q` of the linked splice's cell truth (the `_q` forms are the statements of
record), with the `linkedCF H` forms as their instances at `linkedQuote H`.

**What is open, and what is refuted.** (i) Whether some horizon admits a code with a pinned day
before it (`linked_segment_day_exists`, OPEN, the code quantified): `pinned_eventually_spliceQ`
gives smallness from some `N₀` on for every code, but `N₀` depends on the code's size, and no
explicit short code is built — that needs an explicit `Nat.Partrec.Code` of the cell truth with a
size bound, hence an explicit code for the LIA's own quotes (findings F16). Round 0's
`exists_segment_day` is pure arithmetic in an `N₀` fixed before `H` and does not witness this.
(ii) **Stage-level non-dogmatism fails on every linked day** (`linked_package_dogmatic`,
unconditional over an abstract package; `linked_not_D_ND_on_q`, at the splice, on a day where
`⌜⊤⌝` is pinned): with `⌜⊤⌝` pinned, faith at `⊤` charges only candidates listing `⊤` in a cell of
representative `1`, so the day-`n` price of the literal "`⊤` in the `0` cell" is `0`, while that
literal is a free atom at stage `n` and so undecided by it. K7b's `D_ND_on` (stage-relative) and
K7d's package are incompatible on the same day for the same table; the non-dogmatism that
survives linkage is theory-relative at the quote literals (findings F17).
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.BliLinkage.AttemptA.B2 (rep01)
open Kernel

namespace Segment

/-! ## The linked table and its splice -/

/-- The size of the day-`n` complete family as chosen (a choice). The family of record `WAt`
re-indexes the chosen one by `Fin (2 ^ k₀ n)` (continuation 2: the dyadic refinement).
Source: `Mixing.exists_completeFor`
Kind: D
Fidelity: n/a -/
noncomputable def k₀ (n : ℕ) : ℕ :=
  Classical.choose (exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n))

/-- The day-`n` complete family as chosen: worlds consistent with `(paperDP 𝗜𝚺₁).D n`, complete
for the day-`n` small atoms (a choice over a finite set, never computed).
Source: mandate § 2, § 4 ("a `D n`-consistent complete world family (K7b)")
Kind: D
Fidelity: exact -/
noncomputable def W₀ (n : ℕ) : Fin (k₀ n) → PCWorld :=
  Classical.choose (Classical.choose_spec
    (exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n)))

/-- The defining property of the chosen family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma W₀_spec (n : ℕ) :
    0 < k₀ n ∧ (∀ i, (W₀ n i).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      CompleteFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (W₀ n) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n)))

/-- **The size of the family of record: `2 ^ k₀ n`**, a power of two — so that the kernel's
weights `1 / (2 · kAt n)` (uniform over the `Fin (kAt n)` indices; over the *distinct* members
of the chosen family they are proportional to multiplicity, since `WAt` repeats members) are
dyadic and the linked table lies on a dyadic grid
(`Bli.linkedPrice_mem_gridVals`; the dyadic refinement of the mixing lemma, mandate § 2,
[[bli-exact-base-handoff]] item 4). Continuation 2; round 0/1 used the chosen size `k₀ n`.
Source: mandate § 2 ("duplicate worlds so the family has `2^k` members of weight `2^{-k}`")
Kind: D
Fidelity: exact -/
noncomputable def kAt (n : ℕ) : ℕ := 2 ^ k₀ n

/-- **The day-`n` complete family of record**: the chosen family re-indexed by `Fin (2 ^ k₀ n)`
through `j ↦ j % k₀ n` — a surjection onto the chosen members (members repeat), so the family
stays consistent and complete with a power-of-two size.
Source: mandate § 2, § 4 ("a `D n`-consistent complete world family (K7b)"; dyadic weights)
Kind: D
Fidelity: exact (members repeat; every lemma of `Kernel` is for an arbitrary family) -/
noncomputable def WAt (n : ℕ) : Fin (kAt n) → PCWorld :=
  fun j => W₀ n ⟨j.val % k₀ n, Nat.mod_lt _ (W₀_spec n).1⟩

/-- The defining property of the family of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma WAt_spec (n : ℕ) :
    0 < kAt n ∧ (∀ i, (WAt n i).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      CompleteFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (WAt n) := by
  obtain ⟨hk, hcons, hcomp⟩ := W₀_spec n
  refine ⟨Nat.two_pow_pos _, fun i => hcons _, fun v hv => ?_⟩
  obtain ⟨i, hi⟩ := hcomp v hv
  refine ⟨⟨i.val, lt_of_lt_of_le i.2 (Nat.lt_two_pow_self).le⟩, fun a ha => ?_⟩
  have hidx : (⟨i.val % k₀ n, Nat.mod_lt _ hk⟩ : Fin (k₀ n)) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.2)
  show (W₀ n ⟨i.val % k₀ n, Nat.mod_lt _ hk⟩ a ↔ v a)
  rw [hidx]
  exact hi a ha

/-- **The day-`n` kernel market** over the day-`n` family, slices at day `n+1`.
Source: mandate § 4 (`P n`)
Kind: D
Fidelity: exact -/
noncomputable def kernelMarket (n : ℕ) : Sentence → ℝ :=
  kMix ((paperDP 𝗜𝚺₁).D n) (n + 1) (WAt n)

/-- **The linked table**: the exact rational kernel market of every day. Defined for every day;
independent of any program code.
Source: mandate § 4 ("`Q n` := its marginal on `smallSet n` … this *is* the day-`n` segment
table"); [[bli-exact-base-handoff]] item 2
Kind: D
Fidelity: exact -/
noncomputable def linkedPrice (n : ℕ) (φ : Sentence) : ℚ :=
  kMixRat ((paperDP 𝗜𝚺₁).D n) (n + 1) (WAt n) φ

/-- The linked table casts to the kernel market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedPrice_cast (n : ℕ) (φ : Sentence) : (linkedPrice n φ : ℝ) = kernelMarket n φ :=
  kMixRat_cast _ _ _ _

/-- The linked table lies in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedPrice_inUnit (H : ℕ) :
    ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ linkedPrice n φ ∧ linkedPrice n φ ≤ 1 :=
  fun n _ φ _ => kMixRat_mem_Icc _ _ (WAt_spec n).1 _ φ

/-- **The linked splice** at horizon `H`: FAF's LIA over `paperDP 𝗜𝚺₁` re-priced on the small
sentences of days `< H` by the linked table (finitely many `(day, sentence)` pairs,
`segmentPatch H`). The base of K7c (d)/K7d.
Source: mandate § 1, § 4
Kind: D
Fidelity: exact -/
noncomputable abbrev linkedSplice (H : ℕ) : History := spliceHistory H linkedPrice

/-- **K7a at the linked table**: the linked splice is a logical inductor over `paperDP 𝗜𝚺₁`.
Source: mandate § 1 (judged item 1), § 4; FAF `thm:ifp`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem linkedSplice_isLogicalInductor (H : ℕ) :
    IsLogicalInductor (linkedSplice H) (paperDP 𝗜𝚺₁) :=
  splice_isLogicalInductor H linkedPrice (linkedPrice_inUnit H)

/-- On a segment day the linked splice is the kernel market on the small sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedSplice_eq_kernel {H n : ℕ} (hn : n < H) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    linkedSplice H n φ = kernelMarket n φ := by
  show spliceHistory H linkedPrice n φ = _
  rw [spliceHistory_eq_tbl_of_lt hn hφ, linkedPrice_cast]

/-- `freshCode` is fresh at every stage of `paperDP 𝗜𝚺₁`.
Source: `Tables.freshCoord_free`
Kind: L
Fidelity: n/a -/
lemma freshCode_freshAt (n : ℕ) : FreshAt ((paperDP 𝗜𝚺₁).D n) freshCode :=
  freshCoord_free n

/-- The kernel market is a stage mixture on every algebra.
Source: `Kernel.kMix_coherentOn`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem kernelMarket_coherentOn (n : ℕ) (A : Finset ℕ) :
    CoherentOn ((paperDP 𝗜𝚺₁).D n) A (kernelMarket n) :=
  kMix_coherentOn (freshCode_freshAt n) (n + 1) (WAt_spec n).1 (WAt_spec n).2.1 A

/-- **K7b (coherence) at the linked table**: the linked splice agrees with a stage mixture on
the small sentences on every day `n < H`.
Source: mandate § 2 (judged item 2), § 4; [[bli-program]] §2.6
Kind: C
Fidelity: weaker: small-sentence form (the literal `D_PC_on` is empty for every splice, `Tables.not_D_PC_on_splice`)
Hyps: (a) -/
theorem linked_D_PCsmall_on (H : ℕ) : D_PCsmall_on H (linkedSplice H) (paperDP 𝗜𝚺₁) := by
  intro n hn
  rw [coherentOnSmall_iff_exists_mixture_agree]
  exact ⟨kernelMarket n, kernelMarket_coherentOn n _,
    fun φ hφ => (linkedSplice_eq_kernel hn hφ).symm⟩

/-- The linked splice prices `freshCoord` at exactly `1/2` on every day in `[2, H)`.
Source: mandate § 2 (N+: the uncertain coordinate priced strictly inside)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem linked_fresh_half {H n : ℕ} (hn : n < H) (h2 : 2 ≤ n) :
    linkedSplice H n freshCoord = 1 / 2 := by
  rw [linkedSplice_eq_kernel hn (freshCoord_mem_smallSet h2)]
  exact kMix_fresh _ _ (WAt_spec n).1 _

/-! ## The linked splice's own cell family -/

/-- **The cell family of the linked splice**: its own cell literals at `halfRound`, cells
`{0, 1}`, representatives `rep01`.
Source: mandate § 3 (a) (`spliceCellFamily`)
Kind: D
Fidelity: exact -/
noncomputable def linkedCF (H : ℕ) : CellFamilyT (paperDP 𝗜𝚺₁) :=
  spliceCF H linkedPrice halfRound halfRound_computable twoCells halfRound_mem_twoCells rep01

/-- **The cell family of the linked splice under an arbitrary cell quote code `q`** of its cell
truth (repair round 2, audit r2 fidelity B1): its cell literals are `q`'s quotation atoms, cells
`{0, 1}`, representatives `rep01`. `linkedCF H` is the instance at the code FAF's `ofComputable`
selects (`linkedCF_eq_q`). Every K7c (d)/K7d statement below is proved for every `q`; the size of
the code, which decides whether a day `< H` is pinned, enters only the OPEN row
`linked_segment_day_exists`, which quantifies over `q`.
Source: mandate § 3 (a) (`spliceCellFamily`); audit r2 fidelity B1
Kind: D
Fidelity: exact -/
noncomputable def linkedCFq (H : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) :
    CellFamilyT (paperDP 𝗜𝚺₁) :=
  spliceCFq H linkedPrice halfRound q twoCells halfRound_mem_twoCells rep01

/-- The cell quote code of the linked splice at horizon `H` that FAF's `ofComputable` selects
(a `Classical.choice`: `BooleanQuoteCode.ofComputable` chooses the decider and then its
`Nat.Partrec.Code`; nothing bounds its size either way).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def linkedQuote (H : ℕ) :
    BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound) :=
  spliceCellQuote H linkedPrice halfRound halfRound_computable

/-- `linkedCF H` is `linkedCFq H` at the `ofComputable` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedCF_eq_q (H : ℕ) : linkedCF H = linkedCFq H (linkedQuote H) := rfl

/-- The cell quote code of the linked splice at horizon `H`: the `code` field of `linkedQuote H`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def linkedCode (H : ℕ) : ℕ :=
  (spliceCellQuote H linkedPrice halfRound halfRound_computable).code

/-- The linked cell family under `q` has the shape atoms of `q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedCFq_litAtoms (H : ℕ) (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) :
    LitAtoms (linkedCFq H q) q.code :=
  spliceCFq_litAtoms _ _ _ _ _ _ _

/-- The linked cell family has the shape atoms of its code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedCF_litAtoms (H : ℕ) : LitAtoms (linkedCF H) (linkedCode H) :=
  spliceCF_litAtoms _ _ _ _ _ _ _

/-- The six day-`(n+1)` literal atoms of **any** code `e` are fresh at stage `n`.
Source: `Kernel.litIdx_fresh`
Kind: L
Fidelity: n/a -/
lemma hf_any (e n : ℕ) :
    ∀ c ∈ segmentIndex (n + 1), ∀ r ≤ 1,
      FreshAt ((paperDP 𝗜𝚺₁).D n) (litIdx e (n + 1) c r) :=
  fun c _ r _ => litIdx_fresh 𝗜𝚺₁ (Nat.lt_succ_self n) _ c r

/-- `hf_any` at the `ofComputable` code.
Source: `Kernel.litIdx_fresh`
Kind: L
Fidelity: n/a -/
lemma hf_at (H n : ℕ) :
    ∀ c ∈ segmentIndex (n + 1), ∀ r ≤ 1,
      FreshAt ((paperDP 𝗜𝚺₁).D n) (litIdx (linkedCode H) (n + 1) c r) :=
  hf_any (linkedCode H) n

/-- **The pinned set of the linked splice is eventually the whole segment index** (instance of
`pinned_eventually_splice`; `N₀` depends on `linkedCode H`).
Source: mandate § 3 (b)
Kind: C
Fidelity: exact (`∃ N₀`, depending on `H`)
Hyps: (a) -/
theorem linked_pinned_eventually (H : ℕ) :
    ∃ N₀, ∀ n ≥ N₀,
      Encodable.encode freshCoord ∈ pinned (linkedCF H) segmentIndex n ∧
      Encodable.encode (⊥ : Sentence) ∈ pinned (linkedCF H) segmentIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCF H) segmentIndex n :=
  pinned_eventually_splice H linkedPrice rep01

/-- **The pinned set of the linked splice is eventually the whole segment index, for every cell
quote code `q`** (`N₀` depends on `q`). So for every `q` the segment form is non-vacuous *from
some day on*; whether that day precedes the horizon is `linked_segment_day_exists`.
Source: mandate § 3 (b); audit r2 fidelity B1
Kind: C
Fidelity: exact (`∃ N₀`, depending on `H` and `q`)
Hyps: (a) -/
theorem linked_pinned_eventually_q (H : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) :
    ∃ N₀, ∀ n ≥ N₀,
      Encodable.encode freshCoord ∈ pinned (linkedCFq H q) segmentIndex n ∧
      Encodable.encode (⊥ : Sentence) ∈ pinned (linkedCFq H q) segmentIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCFq H q) segmentIndex n :=
  pinned_eventually_spliceQ H linkedPrice q rep01

/-! ## The BLI market and the per-day package -/

/-- **The BLI market over the linked splice**: the kernel market on days `< H`, the base itself
after (so `E1x` holds globally, `linked_E1x`).
Source: mandate § 4 ("define `P` to copy `Q` on small sentences on every day … so it holds
globally")
Kind: D
Fidelity: exact -/
noncomputable def linkedP (H : ℕ) : History :=
  fun n φ => if n < H then kernelMarket n φ else linkedSplice H n φ

/-- On a segment day the BLI market is the kernel market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedP_of_lt {H n : ℕ} (hn : n < H) : linkedP H n = kernelMarket n := by
  funext φ; simp [linkedP, hn]

/-- **`E1x` over the linked splice**: the BLI market agrees with the base on every small sentence
of every day.
Source: bli-found `E1x`; mandate § 4
Kind: L
Fidelity: exact -/
theorem linked_E1x (H : ℕ) : E1x (linkedSplice H) (linkedP H) := by
  intro n φ hφ
  unfold linkedP
  split_ifs with hn
  · exact (linkedSplice_eq_kernel hn hφ).symm
  · rfl

/-- A segment coordinate's sentence is small on every day `≥ 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentIndex_small {n c : ℕ} (h2 : 2 ≤ n) (hc : c ∈ segmentIndex (n + 1)) :
    sentenceOfCode c ∈ smallSet n := by
  simp only [segmentIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rw [sentenceOfCode_encode]
  · exact freshCoord_mem_smallSet h2
  · exact falsum_mem_smallSet n
  · exact verum_mem_smallSet (by omega)

/-- **K7d — the per-day determination package is inhabited over the spliced inductor on every
day `n` with `2 ≤ n < H`**, with the base's own cell family **under every cell quote code `q`**
of its cell truth: a BLI market `P` and a state system `S` with coherence on the day-`n` algebra,
the partition at day `n+1`, exact small agreement with the base, `SpuriousEntails`,
`ValuesAtRep`, faith at every segment coordinate on every candidate, and **two distinct charged
candidates** (`1/2` each), `freshCoord` at `1/2`. The witness is `linkedP H`, `kSystem rep01`.
The candidates are `{0,1}`-certain tables (`tbl3`), so the faith clause is certainty-faith.
`h2` is unused (the package needs no lower bound on the day; the identity does, through
`segmentIndex_small`).
Source: mandate § 4 (judged item 3: "the per-day determination package of `bli-linkage` inhabited
on a segment day with the spliced inductor as base"); [[bli-program]] §3.6 (vi)
Kind: N+
Fidelity: exact (non-degeneracy on the coherent carrier — two charged candidates — in place of product-face `NonDegenerate`, mandate § 4; no `StageFresh` hypothesis: discharged by `stageFresh_spliceQ`; the candidates are `{0,1}`-certain tables, so faith is certainty-faith)
Hyps: (a) -/
theorem segment_package_inhabited_q (H : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (n : ℕ) (hn : n < H)
    (h2 : 2 ≤ n) :
    ∃ (P : History) (S : StateSystem),
      CoherentOn ((paperDP 𝗜𝚺₁).D n)
        (smallAtoms n ∪ stateAtoms (stateOf (linkedCFq H q)) S n) (P n) ∧
      PartitionAt (stateOf (linkedCFq H q)) S (P n) (n + 1) ∧
      E1x (linkedSplice H) P ∧
      SpuriousEntails (stateOf (linkedCFq H q)) (linkedCFq H q).literal S segmentIndex twoCells n ∧
      ValuesAtRep (linkedCFq H q) S segmentIndex n ∧
      (∀ c ∈ segmentIndex (n + 1), ∀ s ∈ S.states (n + 1),
        P n (sentenceOfCode c ⋏ stateOf (linkedCFq H q) (n + 1) s) =
          S.val (n + 1) s (sentenceOfCode c) * P n (stateOf (linkedCFq H q) (n + 1) s)) ∧
      (∃ s ∈ S.states (n + 1), ∃ s' ∈ S.states (n + 1), s ≠ s' ∧
        0 < P n (stateOf (linkedCFq H q) (n + 1) s) ∧
        0 < P n (stateOf (linkedCFq H q) (n + 1) s')) ∧
      P n freshCoord = 1 / 2 := by
  have hk := (WAt_spec n).1
  refine ⟨linkedP H, kSystem rep01, ?_, ?_, linked_E1x H, kSystem_spuriousEntails _ _ n,
    kSystem_valuesAtRep _ (fun _ => rfl) (fun _ _ => rfl) n, ?_, ?_, ?_⟩
  · rw [linkedP_of_lt hn]; exact kernelMarket_coherentOn n _
  · rw [linkedP_of_lt hn]
    exact kMix_partitionAt (linkedCFq_litAtoms H q) (hf_any q.code n) hk _ rep01
  · rw [linkedP_of_lt hn]
    intro c hc s hs
    exact kMix_faith (linkedCFq_litAtoms H q) (hf_any q.code n) hk _ hc hs
  · rw [linkedP_of_lt hn]
    obtain ⟨h1, h0, hne, hm1, hm0⟩ :=
      kMix_two_charged (linkedCFq_litAtoms H q) (hf_any q.code n) hk (WAt n)
    refine ⟨q₁, h1, q₀, h0, hne, ?_, ?_⟩
    · show (0 : ℝ) < kMix _ _ _ _
      rw [hm1]; norm_num
    · show (0 : ℝ) < kMix _ _ _ _
      rw [hm0]; norm_num
  · rw [linkedP_of_lt hn]; exact kMix_fresh _ _ hk _

/-- **K7d at the `ofComputable` code**: `segment_package_inhabited_q` at `linkedQuote H`
(`linkedCF H`). The statement of record is the generic one; this instance is kept for the
dependents and the round-0/1 ledger rows.
Source: mandate § 4 (judged item 3); [[bli-program]] §3.6 (vi)
Kind: N+
Fidelity: exact (as `segment_package_inhabited_q`; the code fixed to FAF's choice)
Hyps: (a) -/
theorem segment_package_inhabited (H n : ℕ) (hn : n < H) (h2 : 2 ≤ n) :
    ∃ (P : History) (S : StateSystem),
      CoherentOn ((paperDP 𝗜𝚺₁).D n)
        (smallAtoms n ∪ stateAtoms (stateOf (linkedCF H)) S n) (P n) ∧
      PartitionAt (stateOf (linkedCF H)) S (P n) (n + 1) ∧
      E1x (linkedSplice H) P ∧
      SpuriousEntails (stateOf (linkedCF H)) (linkedCF H).literal S segmentIndex twoCells n ∧
      ValuesAtRep (linkedCF H) S segmentIndex n ∧
      (∀ c ∈ segmentIndex (n + 1), ∀ q ∈ S.states (n + 1),
        P n (sentenceOfCode c ⋏ stateOf (linkedCF H) (n + 1) q) =
          S.val (n + 1) q (sentenceOfCode c) * P n (stateOf (linkedCF H) (n + 1) q)) ∧
      (∃ q ∈ S.states (n + 1), ∃ q' ∈ S.states (n + 1), q ≠ q' ∧
        0 < P n (stateOf (linkedCF H) (n + 1) q) ∧ 0 < P n (stateOf (linkedCF H) (n + 1) q')) ∧
      P n freshCoord = 1 / 2 :=
  segment_package_inhabited_q H (linkedQuote H) n hn h2

/-- **K7c (d) — exact `D_NNUcell` on every pinned coordinate of every day in `[2, H)`, through
the engine, for every cell quote code `q`**: `bli-linkage`'s `nnu_day` applied to the package of
`segment_package_inhabited_q`. The identity is on the *base* `linkedSplice H` with the base's own
literals — the quotation atoms of `q` at the splice's day-`(n+1)` cells.
Source: mandate § 3 (d) (judged item 3); bli-linkage `Determination.nnu_day`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem linked_nnu_day_q {H n : ℕ}
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (hn : n < H)
    (h2 : 2 ≤ n) {c : ℕ} (hc : c ∈ pinned (linkedCFq H q) segmentIndex n) :
    linkedSplice H n (sentenceOfCode c) =
      ∑ r ∈ twoCells (n + 1), (rep01 (n + 1) r : ℝ) *
        linkedSplice H n ((linkedCFq H q).literal (n + 1) (sentenceOfCode c) r) := by
  have hk := (WAt_spec n).1
  have hcidx : c ∈ segmentIndex (n + 1) := ((mem_pinned _ _ _ _).1 hc).1
  exact Cleanroom.Bli.BliLinkage.nnu_day (linkedCFq H q) (S := kSystem rep01)
    (atoms := fun n => stateAtoms (stateOf (linkedCFq H q)) (kSystem rep01) n)
    (DP := paperDP 𝗜𝚺₁) (P := linkedP H) (Q := linkedSplice H) (index := segmentIndex)
    (by rw [linkedP_of_lt hn]; exact kernelMarket_coherentOn n _)
    subset_rfl
    (by rw [linkedP_of_lt hn]
        exact kMix_partitionAt (linkedCFq_litAtoms H q) (hf_any q.code n) hk _ rep01)
    (linked_E1x H) (kSystem_spuriousEntails _ _ n)
    (kSystem_valuesAtRep _ (fun _ => rfl) (fun _ _ => rfl) n) hc
    (by rw [linkedP_of_lt hn]
        intro s hs
        exact kMix_faith (linkedCFq_litAtoms H q) (hf_any q.code n) hk _ hcidx hs)
    (segmentIndex_small h2 hcidx)

/-- `linked_nnu_day_q` at the `ofComputable` code.
Source: mandate § 3 (d) (judged item 3); bli-linkage `Determination.nnu_day`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem linked_nnu_day {H n : ℕ} (hn : n < H) (h2 : 2 ≤ n) {c : ℕ}
    (hc : c ∈ pinned (linkedCF H) segmentIndex n) :
    linkedSplice H n (sentenceOfCode c) =
      ∑ r ∈ twoCells (n + 1), (rep01 (n + 1) r : ℝ) *
        linkedSplice H n ((linkedCF H).literal (n + 1) (sentenceOfCode c) r) :=
  linked_nnu_day_q (linkedQuote H) hn h2 hc

/-- **`D_NNUcell` on the segment `[N₀, H)`** (the mandate's segment form of `bli-linkage`'s
`D_NNUcell`): on every day `N₀ ≤ n < H`, every pinned coordinate satisfies the cell-form identity.
Source: mandate § Definitions (`D_NNUcell_on`)
Kind: D
Fidelity: exact (segment form) -/
def D_NNUcell_on (H N₀ : ℕ) {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (index : ℕ → List ℕ)
    (Q : History) : Prop :=
  ∀ n, N₀ ≤ n → n < H → ∀ c ∈ pinned C index n,
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) (sentenceOfCode c) r)

/-- **K7c (d) of record: the linked splice is `D_NNUcell` on the segment `[2, H)` with its own
quote lane, for every cell quote code `q`** — on every pinned coordinate of every day
`2 ≤ n < H`. Whether some code has a pinned coordinate before `H` is `linked_segment_day_exists`
(OPEN, quantified over the code).
Source: mandate § 3 (d) (judged item 3: "exact `D_NNUcell` on the segment with the splice's own
quote lane")
Kind: C
Fidelity: exact (segment `[2, H)`; non-vacuity of `pinned` before `H` OPEN, `linked_segment_day_exists`)
Hyps: (a) -/
theorem segment_D_NNUcell_on_q (H : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) :
    D_NNUcell_on H 2 (linkedCFq H q) segmentIndex (linkedSplice H) :=
  fun n h2 hn c hc => linked_nnu_day_q q hn h2 hc

/-- `segment_D_NNUcell_on_q` at the `ofComputable` code (`linkedCF H`). Whether any coordinate is
pinned before `H` for *this* code is not a conjecture about the kernel but about which program
`Classical.choice` returned (audit r2 fidelity B1); the open question is stated over the code,
`linked_segment_day_exists`.
Source: mandate § 3 (d) (judged item 3)
Kind: C
Fidelity: exact (segment `[2, H)`; at FAF's chosen code)
Hyps: (a) -/
theorem segment_D_NNUcell_on (H : ℕ) :
    D_NNUcell_on H 2 (linkedCF H) segmentIndex (linkedSplice H) :=
  segment_D_NNUcell_on_q H (linkedQuote H)

/-- The mandate's `[N₀, H)` form, for every `N₀ ≥ 2` and every cell quote code.
Source: mandate § 3 (c)/(d) ("every K7c/K7d theorem carries `N₀ ≤ n < H`")
Kind: L
Fidelity: n/a -/
theorem segment_D_NNUcell_on_of_le (H N₀ : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (h2 : 2 ≤ N₀) :
    D_NNUcell_on H N₀ (linkedCFq H q) segmentIndex (linkedSplice H) :=
  fun n hN hn c hc => linked_nnu_day_q q hn (h2.trans hN) hc

/-! ## The kernel's own identity, no pinnedness -/

/-- The kernel's price of a day-`(n+1)` literal atom of a segment coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kernelMarket_lit (e n : ℕ) {c r : ℕ} (hc : c ∈ segmentIndex (n + 1)) (hr : r ≤ 1) :
    kernelMarket n (Formula.atom (litIdx e (n + 1) c r)) =
      ((if (c = Encodable.encode freshCoord ∧ r = 1) ∨
            (c = Encodable.encode (⊥ : Sentence) ∧ r = 0) ∨
            (c = Encodable.encode (⊤ : Sentence) ∧ r = 1) then 1 else 0) +
        (if (c = Encodable.encode freshCoord ∧ r = 0) ∨
            (c = Encodable.encode (⊥ : Sentence) ∧ r = 0) ∨
            (c = Encodable.encode (⊤ : Sentence) ∧ r = 1) then 1 else 0)) / 2 :=
  kMix_eq_ite (WAt_spec n).1
    (fun i => slice_holds_lit hc hr (hf_any e n c hc r hr) 1 0 1 True (WAt n i))
    (fun i => slice_holds_lit hc hr (hf_any e n c hc r hr) 0 0 1 False (WAt n i))

/-- **The kernel market satisfies the cell-form identity on all three segment coordinates on
every day, for every cell quote code**, by construction (`fresh`: `1/2 = 0 · 1/2 + 1 · 1/2`; `⊥`:
`0 = 0 · 1 + 1 · 0`; `⊤`: `1 = 0 · 0 + 1 · 1`). Pinnedness is what transfers it to the *base*
(`linked_nnu_day_q`).
Source: mandate § 3 (d) ("by construction … `Balanced` + `ValuesAtRep` unfolded: Kind `L`/`C`")
Kind: L
Fidelity: exact (on the kernel market `P n`, not the base)
Hyps: (a) -/
theorem kernel_identity_q (H n : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) {c : ℕ}
    (hc : c ∈ segmentIndex (n + 1)) :
    kernelMarket n (sentenceOfCode c) =
      ∑ r ∈ twoCells (n + 1), (rep01 (n + 1) r : ℝ) *
        kernelMarket n ((linkedCFq H q).literal (n + 1) (sentenceOfCode c) r) := by
  have hk := (WAt_spec n).1
  rw [show twoCells (n + 1) = {0, 1} from rfl, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  have hc' := hc
  simp only [segmentIndex, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl <;>
    rw [sentenceOfCode_encode, linkedCFq_litAtoms H q, linkedCFq_litAtoms H q,
      kernelMarket_lit q.code n hc zero_le_one, kernelMarket_lit q.code n hc le_rfl]
  · show kMix _ _ _ freshCoord = _
    rw [kMix_fresh _ _ hk]
    simp [rep01, freshCoord_ne_falsum, freshCoord_ne_verum]
  · show kMix _ _ _ ⊥ = _
    rw [(kMix_top_bot _ _ hk _).2]
    simp [rep01, freshCoord_ne_falsum.symm]
  · show kMix _ _ _ ⊤ = _
    rw [(kMix_top_bot _ _ hk _).1]
    simp [rep01, freshCoord_ne_verum.symm]

/-- `kernel_identity_q` at the `ofComputable` code.
Source: mandate § 3 (d)
Kind: L
Fidelity: exact (on the kernel market `P n`, not the base)
Hyps: (a) -/
theorem kernel_identity (H n : ℕ) {c : ℕ} (hc : c ∈ segmentIndex (n + 1)) :
    kernelMarket n (sentenceOfCode c) =
      ∑ r ∈ twoCells (n + 1), (rep01 (n + 1) r : ℝ) *
        kernelMarket n ((linkedCF H).literal (n + 1) (sentenceOfCode c) r) :=
  kernel_identity_q H n (linkedQuote H) hc

/-! ## Stage-level non-dogmatism fails under linkage -/

/-- **Any linked per-day package is dogmatic at the stage level about the base's uncharged
literals**: under the hypotheses of `nnu_day` with faith at `⊤` and `⌜⊤⌝` pinned, the base's
day-`n` price of the literal "`⊤` in cell `r₀`" is `0` for every cell with `rep r₀ ≠ 1` — a
charged candidate values `⊤` at `1` (`Linked.charged_val_top_eq_one`), so no candidate listing
`⊤` at `r₀` is charged and the literal's forced marginal (`forced_marginal_day`) vanishes.
Source: this package (findings F17); mandate § 4 (`charged_coherent_of_faith`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem linked_package_dogmatic {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem}
    {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ} {n : ℕ}
    (hcoh : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n))
    (hatoms : stateAtoms (stateOf C) S n ⊆ atoms n)
    (hpart : PartitionAt (stateOf C) S (P n) (n + 1)) (hE1 : E1x Q P)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ValuesAtRep C S index n)
    (htop : Encodable.encode (⊤ : Sentence) ∈ pinned C index n)
    (hfaith : ∀ q ∈ S.states (n + 1),
      P n ((⊤ : Sentence) ⋏ stateOf C (n + 1) q) =
        S.val (n + 1) q ⊤ * P n (stateOf C (n + 1) q))
    {r₀ : ℕ} (hr₀ : r₀ ∈ C.cells (n + 1)) (hrep : C.rep (n + 1) r₀ ≠ 1) :
    Q n (C.literal (n + 1) ⊤ r₀) = 0 := by
  have hlit : C.literal (n + 1) ⊤ r₀ ∈ smallSet n := by
    have := ((mem_pinned C index n _).1 htop).2 r₀ hr₀
    rw [sentenceOfCode_encode] at this
    exact mem_smallSet.2 this
  rw [← hE1 n _ hlit]
  have hfm := Cleanroom.Bli.BliLinkage.forced_marginal_day C hcoh hatoms hpart hsp htop hr₀
  rw [sentenceOfCode_encode] at hfm
  rw [hfm, cellMass]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.mem_filter] at hq
  obtain ⟨hqS, hent⟩ := hq
  obtain ⟨r, -, he, hv⟩ := hval q hqS _ ((mem_pinned C index n _).1 htop).1
  rw [he] at hent
  obtain rfl := Option.some.inj hent
  rw [sentenceOfCode_encode] at hv
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 hcoh)
  have hσA : sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n :=
    (atoms_subset_stateAtoms (stateOf C) S hqS).trans (hatoms.trans Finset.subset_union_right)
  rcases (hM.nonneg_of_subset hσA).lt_or_eq with hpos | h0
  · exfalso
    have h1 := charged_val_top_eq_one hcoh hσA (hfaith q hqS) hpos
    rw [hv] at h1
    exact hrep (by exact_mod_cast h1)
  · exact h0.symm

/-- **The linked splice is dogmatic about its own `⊤`-in-cell-`0` literal on every day `n < H`
where `⌜⊤⌝` is pinned**: the literal is priced `0`, yet it is a free atom at stage `n` — some
stage-consistent world holds it and some does not.
Source: this package (findings F17)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem linked_literal_dogmatic_q {H n : ℕ}
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (hn : n < H)
    (htop : Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCFq H q) segmentIndex n) :
    linkedSplice H n ((linkedCFq H q).literal (n + 1) ⊤ 0) = 0 ∧
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
      v.Holds ((linkedCFq H q).literal (n + 1) ⊤ 0)) ∧
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
      ¬ v.Holds ((linkedCFq H q).literal (n + 1) ⊤ 0)) := by
  have hlit : (linkedCFq H q).literal (n + 1) ⊤ 0 ∈ smallSet n := by
    have := ((mem_pinned _ _ _ _).1 htop).2 0 (by simp [linkedCFq, spliceCFq, twoCells])
    rw [sentenceOfCode_encode] at this
    exact mem_smallSet.2 this
  refine ⟨?_, ?_⟩
  · rw [linkedSplice_eq_kernel hn hlit, linkedCFq_litAtoms H q,
      kernelMarket_lit q.code n (by simp [segmentIndex]) zero_le_one]
    simp [encode_freshCoord_ne_verum.symm, encode_falsum_ne_encode_verum.symm]
  · rw [linkedCFq_litAtoms H q]
    exact free_atom_undecided (litIdx_fresh 𝗜𝚺₁ (Nat.lt_succ_self n) _ _ _) (paperDP_hworld 𝗜𝚺₁ n)

/-- `linked_literal_dogmatic_q` at the `ofComputable` code.
Source: this package (findings F17)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem linked_literal_dogmatic {H n : ℕ} (hn : n < H)
    (htop : Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCF H) segmentIndex n) :
    linkedSplice H n ((linkedCF H).literal (n + 1) ⊤ 0) = 0 ∧
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
      v.Holds ((linkedCF H).literal (n + 1) ⊤ 0)) ∧
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
      ¬ v.Holds ((linkedCF H).literal (n + 1) ⊤ 0)) :=
  linked_literal_dogmatic_q (linkedQuote H) hn htop

/-- **Stage-relative non-dogmatism fails at the linked splice**: `¬ D_ND_on H (linkedSplice H)
(paperDP 𝗜𝚺₁)` as soon as `⌜⊤⌝` is pinned on some day `n < H`. K7b's `segment_D_ND_on` holds for
the unlinked segment tables and cannot hold for any table carrying the linked package on the
same day (`linked_package_dogmatic`).
Source: this package (findings F17); mandate § 2 (`D_ND_on`), § 4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem linked_not_D_ND_on_q {H n : ℕ}
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (hn : n < H)
    (htop : Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCFq H q) segmentIndex n) :
    ¬ D_ND_on H (linkedSplice H) (paperDP 𝗜𝚺₁) := by
  intro hND
  obtain ⟨h0, ⟨v₁, hv₁, h₁⟩, ⟨v₀, hv₀, h₀⟩⟩ := linked_literal_dogmatic_q q hn htop
  have hlit : (linkedCFq H q).literal (n + 1) ⊤ 0 ∈ smallSet n := by
    have := ((mem_pinned _ _ _ _).1 htop).2 0 (by simp [linkedCFq, spliceCFq, twoCells])
    rw [sentenceOfCode_encode] at this
    exact mem_smallSet.2 this
  rcases hND n hn _ hlit with h | h | h
  · exact h₀ (h v₀ hv₀)
  · exact h v₁ hv₁ h₁
  · rw [h0] at h
    exact lt_irrefl _ h.1

/-- `linked_not_D_ND_on_q` at the `ofComputable` code.
Source: this package (findings F17); mandate § 2 (`D_ND_on`), § 4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem linked_not_D_ND_on {H n : ℕ} (hn : n < H)
    (htop : Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCF H) segmentIndex n) :
    ¬ D_ND_on H (linkedSplice H) (paperDP 𝗜𝚺₁) :=
  linked_not_D_ND_on_q (linkedQuote H) hn htop

/-! ## What is open: a pinned day before the horizon -/

/-- **OPEN — some horizon admits a cell quote code of the linked splice short enough that a
segment day is pinned before the horizon.** For every `H` and every code `q`,
`linked_pinned_eventually_q` gives an `N₀` from which every segment coordinate is pinned, but
`N₀` depends on `q`: `⌜⊤⌝` is pinned on day `n` iff the two atoms `litIdx q.code (n+1) ⌜⊤⌝ r`
are day-`n` small (`pinned` unfolded), a bound on the token size of an index nesting `q.code`.
The Lean fixes no code: `linkedCF H` is at FAF's `ofComputable`, which selects its
`Nat.Partrec.Code` by `Classical.choose`, so a row stated at *that* code (round 0's form, through
repair round 1) was neither provable nor refutable — nothing bounds the chosen code either way
(audit r2 fidelity B1). With the code quantified this is a genuine conjecture, plausibly true:
the kernel is uniformly computable in the day, so a short explicit code should exist, with
roughly `O(log H)` bits for the horizon plus constants; closing it needs an explicit
`Nat.Partrec.Code` of the cell truth with a size bound, which needs the LIA's own quote code
explicit (FAF's is also `ofComputable`) — a project of its own (`bli-short-code`, findings F16).
Round 0's `exists_segment_day` does not witness this: it fixes `N₀` before `H`.
Source: mandate § 3 (b) ("a theorem whose segment is empty is vacuous: the N+ exhibits `n` with
`N₀ ≤ n < H`"); findings F16; audit r2 fidelity B1
Kind: OPEN
Fidelity: exact (the code quantified)
Hyps: n/a -/
theorem linked_segment_day_exists :
    ∃ (H n : ℕ) (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)),
      2 ≤ n ∧ n < H ∧
        Encodable.encode (⊤ : Sentence) ∈ pinned (linkedCFq H q) segmentIndex n := by
  sorry

/-! ## The realized next state is the charged candidate `q₁` -/

/-- The splice's value family at a small sentence on a segment day is the linked table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceValue_linked {H m : ℕ} (hm : m < H) {φ : Sentence} (hφ : φ ∈ smallSet m) :
    spliceValue H linkedPrice (Nat.pair m (Encodable.encode φ)) = linkedPrice m φ := by
  have := spliceValue_eq_history H linkedPrice m φ
  rw [spliceHistory_eq_tbl_of_lt hm hφ] at this
  exact_mod_cast this

/-- **The splice's realized day-`(n+1)` cells at the three coordinates are `q₁`'s** (`1`, `0`, `1`)
when `1 ≤ n` and `n + 1 < H`: `freshCoord` is priced exactly `1/2` tomorrow, which `halfRound`
sends to cell `1`; `⊤` to `1`; `⊥` to `0`.
Source: mandate § 4 (the chain across days, first step)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem linked_actual_cells {H n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 < H) :
    halfRound (n + 1)
        (spliceValue H linkedPrice (Nat.pair (n + 1) (Encodable.encode freshCoord))) = 1 ∧
    halfRound (n + 1)
        (spliceValue H linkedPrice (Nat.pair (n + 1) (Encodable.encode (⊥ : Sentence)))) = 0 ∧
    halfRound (n + 1)
        (spliceValue H linkedPrice (Nat.pair (n + 1) (Encodable.encode (⊤ : Sentence)))) = 1 := by
  have hk := (WAt_spec (n + 1)).1
  have hf : linkedPrice (n + 1) freshCoord = 1 / 2 := by
    have := linkedPrice_cast (n + 1) freshCoord
    rw [show kernelMarket (n + 1) freshCoord = 1 / 2 from kMix_fresh _ _ hk _] at this
    exact Rat.cast_injective (α := ℝ) (by rw [this]; norm_num)
  have ht : linkedPrice (n + 1) ⊤ = 1 := by
    have := linkedPrice_cast (n + 1) ⊤
    rw [show kernelMarket (n + 1) ⊤ = 1 from (kMix_top_bot _ _ hk _).1] at this
    exact_mod_cast this
  have hb : linkedPrice (n + 1) ⊥ = 0 := by
    have := linkedPrice_cast (n + 1) ⊥
    rw [show kernelMarket (n + 1) ⊥ = 0 from (kMix_top_bot _ _ hk _).2] at this
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [spliceValue_linked hn (freshCoord_mem_smallSet (by omega)), hf]; norm_num [halfRound]
  · rw [spliceValue_linked hn (falsum_mem_smallSet _), hb]; norm_num [halfRound]
  · rw [spliceValue_linked hn (verum_mem_smallSet (by omega)), ht]; norm_num [halfRound]

/-- **The superbelief charges the true next state**: for `1 ≤ n` and `n + 1 < H`, every
completed-theory world of `paperDP 𝗜𝚺₁` holds the state sentence of the charged candidate `q₁`
(reflection of the splice's own cell literals at the splice's rounded day-`(n+1)` prices), and
`q₁` has mass `1/2` on day `n` — the first step of the mandate's chain across days: the realized
day-`(n+1)` table is a charged candidate. At the boundary `n + 1 = H` the day-`H` market is the
LIA: the realized pattern is charged **iff** the LIA's rounded `⊥`/`⊤` cells on day `H` are
`0`/`1`, whatever it does at `freshCoord` — both `freshCoord` cells are charged, and unlistedness
is not available (`linked_boundary`, findings F20; this docstring once expected "cell `0`,
uncharged", which was wrong).
Source: mandate § 4 ("make the realized day-`(n+1)` table one charged candidate")
Kind: C
Fidelity: exact (for `n + 1 < H`; the boundary day is `linked_boundary`)
Hyps: (a) -/
theorem linked_actual_state_charged_q {H n : ℕ}
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (h1 : 1 ≤ n)
    (hn : n + 1 < H) :
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      v.Holds (stateOf (linkedCFq H q) (n + 1) q₁)) ∧
    linkedP H n (stateOf (linkedCFq H q) (n + 1) q₁) = 1 / 2 := by
  obtain ⟨hf, hb, ht⟩ := linked_actual_cells h1 hn
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [q₁, holds_stateOf_tbl3]
    exact ⟨(spliceCellSentenceQ_reflected H linkedPrice halfRound q (n + 1) _ 1 v hv).2 hf,
      (spliceCellSentenceQ_reflected H linkedPrice halfRound q (n + 1) _ 0 v hv).2 hb,
      (spliceCellSentenceQ_reflected H linkedPrice halfRound q (n + 1) _ 1 v hv).2 ht⟩
  · rw [linkedP_of_lt (by omega)]
    exact (kMix_two_charged (linkedCFq_litAtoms H q) (hf_any q.code n)
      (WAt_spec n).1 (WAt n)).2.2.2.1

/-- `linked_actual_state_charged_q` at the `ofComputable` code.
Source: mandate § 4 ("make the realized day-`(n+1)` table one charged candidate")
Kind: C
Fidelity: exact (for `n + 1 < H`; the boundary day is `linked_boundary`)
Hyps: (a) -/
theorem linked_actual_state_charged {H n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 < H) :
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      v.Holds (stateOf (linkedCF H) (n + 1) q₁)) ∧
    linkedP H n (stateOf (linkedCF H) (n + 1) q₁) = 1 / 2 :=
  linked_actual_state_charged_q (linkedQuote H) h1 hn

/-! ## The boundary day `n + 1 = H` (continuation 2) -/

/-- The splice's rounded day-`m` cell of `φ` at `halfRound`: the `halfRound` of its own price —
on a day `m ≥ H` the LIA's price (`spliceHistory_eq_lia_of_ge`).
Source: mandate § 4 ("the last segment day's day-`H` candidates are the LIA's … state what holds at the boundary")
Kind: D
Fidelity: exact -/
noncomputable def spliceCell (H m : ℕ) (φ : Sentence) : ℕ :=
  halfRound m (spliceValue H linkedPrice (Nat.pair m (Encodable.encode φ)))

/-- A `halfRound` cell is `0` or `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCell_le_one (H m : ℕ) (φ : Sentence) : spliceCell H m φ ≤ 1 := by
  unfold spliceCell halfRound; split_ifs <;> omega

/-- The two-charged-candidates mass as a function of the realized cells: `1/2` iff `⊥` is in
cell `0` and `⊤` in cell `1`, whatever the `freshCoord` cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_charged_eq_half_iff {f b t : ℕ} (hf : f ≤ 1) :
    (if f = 1 ∧ b = 0 ∧ t = 1 then (1 : ℝ) / 2 else 0) +
        (if f = 0 ∧ b = 0 ∧ t = 1 then (1 : ℝ) / 2 else 0) = 1 / 2 ↔
      b = 0 ∧ t = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf with rfl | rfl <;>
    by_cases hb : b = 0 <;> by_cases ht : t = 1 <;> simp [hb, ht]

/-- **The boundary day `n + 1 = H`** (every `n`): the day-`H` market is the LIA
(`spliceHistory_eq_lia_of_ge`), so the realized day-`H` cells of the three coordinates are the
LIA's rounded prices `spliceCell (n+1) (n+1) ·`; every completed-theory world of `paperDP 𝗜𝚺₁`
holds the state sentence of that pattern (reflection of the splice's own literals); and the
day-`n` superbelief charges it (mass `1/2`) **iff** the LIA's day-`H` rounded cells of `⊥` and
`⊤` are `0` and `1` — whatever the LIA does at `freshCoord`, since both `freshCoord` cells are
charged (`q₁`, `q₀`). Whether the LIA lists `⊥`/`⊤` on day `H` with those rounded prices is not
controlled by anything in the run (its day-`H` support is a question about the enumerated
traders), so the chain's continuation through the seam is stated as this biconditional.
Source: mandate § 4 ("the last segment day's day-`H` candidates are the LIA's and cannot be charged coherently — state what holds at the boundary"); [[bli-exact-base-handoff]] item 2
Kind: C
Fidelity: exact (the boundary day; the LIA's rounded `⊥`/`⊤` cells left as the condition)
Hyps: (a) -/
theorem linked_boundary_q (n : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth (n + 1) linkedPrice halfRound)) :
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      v.Holds (stateOf (linkedCFq (n + 1) q) (n + 1) (Encodable.encode
        (tbl3 (spliceCell (n + 1) (n + 1) freshCoord) (spliceCell (n + 1) (n + 1) ⊥)
          (spliceCell (n + 1) (n + 1) ⊤))))) ∧
    (linkedP (n + 1) n (stateOf (linkedCFq (n + 1) q) (n + 1) (Encodable.encode
        (tbl3 (spliceCell (n + 1) (n + 1) freshCoord) (spliceCell (n + 1) (n + 1) ⊥)
          (spliceCell (n + 1) (n + 1) ⊤)))) = 1 / 2 ↔
      spliceCell (n + 1) (n + 1) ⊥ = 0 ∧ spliceCell (n + 1) (n + 1) ⊤ = 1) := by
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [holds_stateOf_tbl3]
    exact ⟨(spliceCellSentenceQ_reflected (n + 1) linkedPrice halfRound q (n + 1) _ _ v hv).2 rfl,
      (spliceCellSentenceQ_reflected (n + 1) linkedPrice halfRound q (n + 1) _ _ v hv).2 rfl,
      (spliceCellSentenceQ_reflected (n + 1) linkedPrice halfRound q (n + 1) _ _ v hv).2 rfl⟩
  · rw [linkedP_of_lt (Nat.lt_succ_self n)]
    show kMix _ _ _ _ = 1 / 2 ↔ _
    rw [kMix_state (linkedCFq_litAtoms (n + 1) q) (hf_any q.code n) (WAt_spec n).1 (WAt n)
      (spliceCell_le_one _ _ _) (spliceCell_le_one _ _ _) (spliceCell_le_one _ _ _)]
    exact two_charged_eq_half_iff (spliceCell_le_one _ _ _)

/-- `linked_boundary_q` at the `ofComputable` code.
Source: mandate § 4 (the boundary day); [[bli-exact-base-handoff]] item 2
Kind: C
Fidelity: exact (the boundary day; the LIA's rounded `⊥`/`⊤` cells left as the condition)
Hyps: (a) -/
theorem linked_boundary (n : ℕ) :
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      v.Holds (stateOf (linkedCF (n + 1)) (n + 1) (Encodable.encode
        (tbl3 (spliceCell (n + 1) (n + 1) freshCoord) (spliceCell (n + 1) (n + 1) ⊥)
          (spliceCell (n + 1) (n + 1) ⊤))))) ∧
    (linkedP (n + 1) n (stateOf (linkedCF (n + 1)) (n + 1) (Encodable.encode
        (tbl3 (spliceCell (n + 1) (n + 1) freshCoord) (spliceCell (n + 1) (n + 1) ⊥)
          (spliceCell (n + 1) (n + 1) ⊤)))) = 1 / 2 ↔
      spliceCell (n + 1) (n + 1) ⊥ = 0 ∧ spliceCell (n + 1) (n + 1) ⊤ = 1) :=
  linked_boundary_q n (linkedQuote (n + 1))

/-! ## The trilemma's sharpness over an inductor (mandate § 10 (c); continuation 2) -/

/-- **`bli-linkage`'s `trilemma_sharp`, over an inductor's base**: the conjunction that
`Trilemma.trilemma_sharp` asserts over its abstract four-world base (`PCPσ ∧ E1x ∧ E2xσ ∧ E5σ ∧
D_NNUcell ∧` two candidates at `1/2`), in its per-day segment form with `Q := linkedSplice H`
(a logical inductor over `paperDP 𝗜𝚺₁`) on every day `n < H`: coherence on the day-`n`
algebra over the small and state atoms (`PCPσ`'s per-day clause), `E1x`, faith at every segment
coordinate on every candidate (`E2xσIdx`-shaped, bli-linkage report § Interface notes 2), the
partition (`E5σ`'s per-day clause), `D_NNUcell_on H 2` on the segment, and `q₁`, `q₀` at `1/2`.
So the trilemma's sharpness is about an inductor's base, not the encoding. Differences from the
sharp witness, disclosed: per-day segment form; `P ≠ Q` (the sharp witness has `P = Q`; here
`E1x Q P` with `P` the kernel market); the identity on the base only on pinned coordinates
(`linked_segment_day_exists` OPEN).
Source: mandate § 10 (c); bli-linkage `Trilemma.trilemma_sharp`
Kind: C
Fidelity: variant: per-day segment form over the splice; `P ≠ Q`; identity on pinned coordinates
Hyps: (a) -/
theorem trilemma_sharp_segment_q (H n : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)) (hn : n < H) :
    ∃ (P : History) (S : StateSystem),
      CoherentOn ((paperDP 𝗜𝚺₁).D n)
        (smallAtoms n ∪ stateAtoms (stateOf (linkedCFq H q)) S n) (P n) ∧
      E1x (linkedSplice H) P ∧
      (∀ c ∈ segmentIndex (n + 1), ∀ s ∈ S.states (n + 1),
        P n (sentenceOfCode c ⋏ stateOf (linkedCFq H q) (n + 1) s) =
          S.val (n + 1) s (sentenceOfCode c) * P n (stateOf (linkedCFq H q) (n + 1) s)) ∧
      PartitionAt (stateOf (linkedCFq H q)) S (P n) (n + 1) ∧
      D_NNUcell_on H 2 (linkedCFq H q) segmentIndex (linkedSplice H) ∧
      (P n (stateOf (linkedCFq H q) (n + 1) q₁) = 1 / 2 ∧
        P n (stateOf (linkedCFq H q) (n + 1) q₀) = 1 / 2) := by
  have hk := (WAt_spec n).1
  obtain ⟨-, -, -, hm1, hm0⟩ :=
    kMix_two_charged (linkedCFq_litAtoms H q) (hf_any q.code n) hk (WAt n)
  refine ⟨linkedP H, kSystem rep01, ?_, linked_E1x H, ?_, ?_, segment_D_NNUcell_on_q H q, ?_⟩
  · rw [linkedP_of_lt hn]; exact kernelMarket_coherentOn n _
  · rw [linkedP_of_lt hn]
    intro c hc s hs
    exact kMix_faith (linkedCFq_litAtoms H q) (hf_any q.code n) hk _ hc hs
  · rw [linkedP_of_lt hn]
    exact kMix_partitionAt (linkedCFq_litAtoms H q) (hf_any q.code n) hk _ rep01
  · rw [linkedP_of_lt hn]; exact ⟨hm1, hm0⟩

/-- `trilemma_sharp_segment_q` at the `ofComputable` code.
Source: mandate § 10 (c); bli-linkage `Trilemma.trilemma_sharp`
Kind: C
Fidelity: variant: per-day segment form over the splice; `P ≠ Q`; identity on pinned coordinates
Hyps: (a) -/
theorem trilemma_sharp_segment (H n : ℕ) (hn : n < H) :
    ∃ (P : History) (S : StateSystem),
      CoherentOn ((paperDP 𝗜𝚺₁).D n)
        (smallAtoms n ∪ stateAtoms (stateOf (linkedCF H)) S n) (P n) ∧
      E1x (linkedSplice H) P ∧
      (∀ c ∈ segmentIndex (n + 1), ∀ q ∈ S.states (n + 1),
        P n (sentenceOfCode c ⋏ stateOf (linkedCF H) (n + 1) q) =
          S.val (n + 1) q (sentenceOfCode c) * P n (stateOf (linkedCF H) (n + 1) q)) ∧
      PartitionAt (stateOf (linkedCF H)) S (P n) (n + 1) ∧
      D_NNUcell_on H 2 (linkedCF H) segmentIndex (linkedSplice H) ∧
      (P n (stateOf (linkedCF H) (n + 1) q₁) = 1 / 2 ∧
        P n (stateOf (linkedCF H) (n + 1) q₀) = 1 / 2) :=
  trilemma_sharp_segment_q H n (linkedQuote H) hn

end Segment

end Cleanroom.Bli.BliExactBase
