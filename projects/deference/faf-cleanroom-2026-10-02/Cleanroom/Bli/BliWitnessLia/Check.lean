import Cleanroom.Bli.BliWitnessLia.Prior

/-!
# `bli-witness-lia` · Check: the §2.6 predicate check on the spliced segment, FAF level, tied to
the prior (T3)

One theorem, `segment_predicate_check`, bundles — at the same `H`, `n`, `K` as the prior
`segmentSist` — the inductor-level facts `bli-exact-base` proved about the linked splice
`Segment.linkedSplice H` (FAF's LIA over `paperDP 𝗜𝚺₁`, re-priced on days `< H` at the linked
kernel table), and ties them to the prior:

| program §2.6 predicate | FAF-level Lean fact (cited) | status |
|---|---|---|
| LIC (of the base) | `Segment.linkedSplice_isLogicalInductor H` | proved |
| COMP | `splice_computableMarket H linkedPrice _` | proved |
| D-PC | `Segment.linked_D_PCsmall_on H` | proved: small form; the literal `D_PC_on` is **refuted** (`not_D_PC_on`, F1 of `bli-exact-base`) |
| D-ND | `Segment.linked_fresh_half hn h2` | at the coin only (`1/2`); the stage-level `D_ND_on` is **refuted** at the linked table once `⌜⊤⌝` is pinned (`not_D_ND_on_of_pinned`, F17) |
| E1x | `Segment.linked_E1x H` | proved |
| E2x / E5 / coherence with the state atoms | `Segment.segment_package_inhabited_q H q n hn h2` (`k7dPackage`) | proved, every cell quote code `q`, two charged candidates at `1/2` |
| D-NNU | `Segment.segment_D_NNUcell_on_q H q` | proved on every *pinned* coordinate, every `q`; whether a day `< H` is pinned is **OPEN** (`Segment.linked_segment_day_exists`, F16 (b)) |
| E1x ∧ E2xScoped ∧ E3Scoped ∧ E4 ∧ E5 of the skeleton BLI | `Skel.segmentBli_isBLI_scoped hK cd` | proved (faith scoped), every coding |
| LIC of the skeleton BLI | `Skel.segmentBli_isLogicalInductor` | **OPEN** (cited, never used) |
| FS (`NonDegenerate`, product-face form) | `not_nonDegenerate_twoPointLaw` | **refuted** at this kernel; the non-degeneracy of record is the two charged candidates (`Checks.charged_distinct`) |
| TB at the linked table | `Skel.segmentBli_update_exact`, `Uncharged.segmentBli_actual_next_zero` | vacuous (`x · 0 = 0`); content at the unlinked tables only (F22) |

The tie to the prior (the last four conjuncts): the prior's base table *is* the inductor's
realized day-`n` table (`baseTable_eq_actual`), its two branch masses are `1/2` each
(`stateMass_ask_rec`), its coin coordinate *is* the inductor's price `1/2` (`coin_price`), and the
skeleton's law at the base table is balanced at it — the mean of the two candidates is the
inductor's table (`Balanced`, the finite D-NNU shadow, exact).

Every conjunct is a cited theorem; the proof is `⟨…⟩` (Kind C). The two refutations and the two
OPENs are part of the check, not footnotes; nothing here depends on an OPEN row.

Sources: mandate T3; [[bli-program]] §2.6; [[bli-exact-base-report]] § State, § 2–6;
[[bli-exact-base-findings]] F1, F16, F17, F19, F22.
-/

namespace Cleanroom.Bli.BliWitnessLia

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist

noncomputable section

/-- **The K7d per-day determination package** of `bli-exact-base`, named: the conclusion of
`Segment.segment_package_inhabited_q H q n _ _` verbatim — a BLI market `P` and a state system
`S` with coherence on the day-`n` algebra over the small and state atoms, the partition at day
`n+1`, `E1x` with the linked splice, `SpuriousEntails`, `ValuesAtRep`, faith at every segment
coordinate on every candidate (the FAF-level `E2x`), two distinct charged candidates, and
`freshCoord` at `1/2`. (That it is that conclusion is checked by the typechecker in
`segment_predicate_check`.)
Source: mandate T3 ("the K7d package as `segment_package_inhabited_q H q n hn h2` gives it")
Kind: D
Fidelity: exact -/
abbrev k7dPackage (H : ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H Segment.linkedPrice halfRound)) (n : ℕ) : Prop :=
  ∃ (P : History) (S : StateSystem),
    BliFound.CoherentOn ((paperDP 𝗜𝚺₁).D n)
      (smallAtoms n ∪ stateAtoms (stateOf (Segment.linkedCFq H q)) S n) (P n) ∧
    PartitionAt (stateOf (Segment.linkedCFq H q)) S (P n) (n + 1) ∧
    E1x (Segment.linkedSplice H) P ∧
    SpuriousEntails (stateOf (Segment.linkedCFq H q)) (Segment.linkedCFq H q).literal S
      segmentIndex twoCells n ∧
    ValuesAtRep (Segment.linkedCFq H q) S segmentIndex n ∧
    (∀ c ∈ segmentIndex (n + 1), ∀ s ∈ S.states (n + 1),
      P n (sentenceOfCode c ⋏ stateOf (Segment.linkedCFq H q) (n + 1) s) =
        S.val (n + 1) s (sentenceOfCode c) * P n (stateOf (Segment.linkedCFq H q) (n + 1) s)) ∧
    (∃ s ∈ S.states (n + 1), ∃ s' ∈ S.states (n + 1), s ≠ s' ∧
      0 < P n (stateOf (Segment.linkedCFq H q) (n + 1) s) ∧
      0 < P n (stateOf (Segment.linkedCFq H q) (n + 1) s')) ∧
    P n freshCoord = 1 / 2

section Check

variable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
variable (c V : ℚ) (r₀ : Bool → ℚ)

/-- **The §2.6 predicate check on the spliced segment, FAF level, tied to the prior** (T3): at
the prior's `H`, `n`, `K`, for every cell quote code `q` of the linked splice's cell truth —
(1) the base `linkedSplice H` is a logical inductor over `paperDP 𝗜𝚺₁` (LIC); (2) it is a
`ComputableMarket` (COMP); (3) it is small-sentence coherent on every day `< H` (D-PC, small form;
the literal form is refuted, `not_D_PC_on`); (4) it prices the coin at exactly `1/2` on day `n`
(D-ND *at the coin*; the stage-level `D_ND_on` is refuted once `⌜⊤⌝` is pinned,
`not_D_ND_on_of_pinned`); (5) `E1x` with the kernel market `linkedP H`; (6) the K7d package
(`E2x`/`E5`/coherence with the state atoms, two charged candidates at `1/2`); (7) `D_NNUcell` on
every pinned coordinate of `[2, H)` (its non-vacuity before `H` is OPEN,
`Segment.linked_segment_day_exists`); (8) the skeleton BLI carries the scoped Roman bundle
`E1x ∧ E2xScoped ∧ E3Scoped ∧ E4 ∧ E5` against the base, for every coding (its own LIC is OPEN,
`Skel.segmentBli_isLogicalInductor`); and the tie to the prior — (9) the prior's base table is the
inductor's realized day-`n` table, (10) its branch masses are `1/2`, `1/2`, (11) its coin
coordinate is the inductor's `1/2`, (12) the skeleton's law at the base is balanced at it (the
finite D-NNU shadow: the mean of the two candidates is the inductor's table). The proof is `⟨…⟩`
over cited theorems; nothing depends on an OPEN row.
Source: mandate T3; [[bli-program]] §2.6, §3.9 (U15); [[bli-exact-base-report]] § 2–6
Kind: C (a bundle of cited FAF-level theorems; each conjunct's provenance in the ledger)
Fidelity: variant: D-PC in small form; D-ND at the coin only; D-NNU on pinned coordinates; the
skeleton BLI's bundle with faith scoped (each disclosed)
Hyps: (a) -/
theorem segment_predicate_check
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H Segment.linkedPrice halfRound)) :
    IsLogicalInductor (Segment.linkedSplice H) (paperDP 𝗜𝚺₁) ∧
    ComputableMarket (Segment.linkedSplice H) ∧
    D_PCsmall_on H (Segment.linkedSplice H) (paperDP 𝗜𝚺₁) ∧
    Segment.linkedSplice H n freshCoord = 1 / 2 ∧
    E1x (Segment.linkedSplice H) (Segment.linkedP H) ∧
    k7dPackage H q n ∧
    Segment.D_NNUcell_on H 2 (Segment.linkedCFq H q) segmentIndex (Segment.linkedSplice H) ∧
    (∀ cd : StateCoding (Bli.segmentMesh K),
      IsBLI_RomanScoped cd
        (bliStateSystem (spliceRat H Segment.linkedPrice) (Bli.segmentMesh K) cd)
        (Segment.linkedSplice H) (segmentBli H K hK cd)) ∧
    linkedTable n = BliFinite.actualTable smallIndex (spliceRat H Segment.linkedPrice) n ∧
    ((segmentSist H K hK n hn h2 c V r₀).stateMass (askTable K hK hn) = 1 / 2 ∧
      (segmentSist H K hK n hn h2 c V r₀).stateMass (recTable K hK hn) = 1 / 2) ∧
    linkedTable n ⟨freshCoord, freshCoord_mem_smallSet h2⟩ = 1 / 2 ∧
    Balanced (Bli.segmentMesh K).d (((segmentSkeleton H K hK).κ n).law (linkedTable n))
      (linkedTable n) :=
  ⟨Segment.linkedSplice_isLogicalInductor H,
    splice_computableMarket H Segment.linkedPrice (Segment.linkedPrice_inUnit H),
    Segment.linked_D_PCsmall_on H,
    Segment.linked_fresh_half hn h2,
    Segment.linked_E1x H,
    Segment.segment_package_inhabited_q H q n hn h2,
    Segment.segment_D_NNUcell_on_q H q,
    fun cd => segmentBli_isBLI_scoped hK cd,
    baseTable_eq_actual hn,
    stateMass_ask_rec hK hn h2 c V r₀,
    (coin_price hn h2).1,
    ((segmentSkeleton H K hK).κ n).balanced (linkedTable n) (linkedTable_inUnit n)⟩

/-- **D-PC, literal form: refuted** at every splice with `H ≥ 1` (`bli-found`'s `CoherentOn`
reaches the whole algebra over the small atoms; `bli-exact-base` F1). The surviving neighbour is
the small form `D_PCsmall_on` (conjunct 3 of the check).
Source: mandate T3 ("rows for `D_PC` (literal: refuted, `not_D_PC_on_splice`)")
Kind: L (restatement of `Tables.not_D_PC_on_splice` at the linked table)
Fidelity: exact -/
theorem not_D_PC_on (hH : 0 < H) : ¬ D_PC_on H (Segment.linkedSplice H) (paperDP 𝗜𝚺₁) :=
  not_D_PC_on_splice H hH Segment.linkedPrice

/-- **D-ND, stage-level form: refuted at the linked table** as soon as `⌜⊤⌝` is pinned on the day
(`bli-exact-base` F17: the uncharged quote literal "`⊤` in cell `0`" is priced `0` while stage-free).
The surviving neighbour is D-ND *at the coin* (conjunct 4 of the check: `freshCoord` priced
strictly inside, at `1/2`). Whether `⌜⊤⌝` is pinned on some day `< H` is the OPEN
`Segment.linked_segment_day_exists`; this refutation is conditional on it exactly as the
`D_NNUcell` identity's non-vacuity is.
Source: mandate T3 (`not_D_ND_on_of_pinned`); [[bli-exact-base-findings]] F17
Kind: L (restatement of `Segment.linked_not_D_ND_on_q`)
Fidelity: exact -/
theorem not_D_ND_on_of_pinned (hn : n < H)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H Segment.linkedPrice halfRound))
    (htop : Encodable.encode (⊤ : Sentence) ∈ pinned (Segment.linkedCFq H q) segmentIndex n) :
    ¬ D_ND_on H (Segment.linkedSplice H) (paperDP 𝗜𝚺₁) :=
  Segment.linked_not_D_ND_on_q q hn htop

/-! ## FS: product-face non-degeneracy fails at the two-point law -/

/-- **The day-`n` linked table read on day-`(n+1)` small sentences**: `linkedPrice n` on
`smallIndex.S (n+1)` — the kernel's own marginal on tomorrow's sentences, the midpoint of the two
slice marginals (`Skel.linkedPrice_eq_avg`). A third point of the product face over
`linkedTable n`, uncharged by the two-point law.
Source: mandate T3 (the N− for `FS`)
Kind: D
Fidelity: exact -/
def linkedExt (n : ℕ) : Table smallIndex (n + 1) := fun φ => Segment.linkedPrice n φ.1

/-- `linkedExt n` is a grid table of `segmentMesh K` on day `n+1` (the linked table is dyadic).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedExt_mem_grid (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) (hn : n < H) :
    linkedExt n ∈ grid smallIndex (Bli.segmentMesh K).d (n + 1) := by
  rw [mem_grid_iff]
  intro φ
  show Segment.linkedPrice n φ.1 ∈ gridVals ((Bli.segmentMesh K).d (n + 1))
  exact gridVals_mono (pow_dvd_pow 2 (by have := hK n hn; omega)) (Nat.two_pow_pos _)
    (Bli.linkedPrice_mem_gridVals n φ.1)

/-- `linkedExt n` lies on the product face over `linkedTable n`: its restriction to the day-`n`
sentences *is* `linkedTable n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma linkedExt_mem_faceProd (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) (hn : n < H) :
    linkedExt n ∈ faceProd smallIndex (Bli.segmentMesh K).d n (linkedTable n) := by
  unfold faceProd
  rw [Finset.mem_filter]
  exact ⟨linkedExt_mem_grid hK hn, fun φ _ => rfl⟩

/-- **FS refuted at this kernel**: the two-point law is not product-face `NonDegenerate` at the
linked table — `linkedExt n` is on the face (it restricts to `linkedTable n`) and is neither slice
marginal (its coin is `1/2`, theirs `1`/`0`), so it has mass `0`. The non-degeneracy of record is
the two charged candidates on the coherent carrier (`Checks.charged_distinct`), as
`bli-exact-base` § 4 declares; `NonDegenerate` is not weakened to make it hold.
Source: mandate T3 ("`FS` (`NonDegenerate`: refuted at this kernel …)"), § 3.5, § 5 item 8
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem not_nonDegenerate_twoPointLaw (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) (hn : n < H)
    (h2 : 2 ≤ n) :
    ¬ NonDegenerate (Bli.segmentMesh K).d (twoPointLaw n) (linkedTable n) := by
  intro hND
  have hpos := hND (linkedExt n) (linkedExt_mem_faceProd hK hn)
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  have hhalf : Segment.linkedPrice n freshCoord = 1 / 2 := (coin_price hn h2).1
  have hT : linkedExt n ≠ sliceT n := by
    intro h
    have := congrFun h ⟨freshCoord, hf⟩
    simp only [sliceT] at this
    rw [sliceTable_fresh] at this
    change Segment.linkedPrice n freshCoord = _ at this
    rw [hhalf] at this
    norm_num at this
  have hF : linkedExt n ≠ sliceF n := by
    intro h
    have := congrFun h ⟨freshCoord, hf⟩
    simp only [sliceF] at this
    rw [sliceTable_fresh] at this
    change Segment.linkedPrice n freshCoord = _ at this
    rw [hhalf] at this
    norm_num at this
  unfold twoPointLaw at hpos
  rw [if_neg hT, if_neg hF] at hpos
  norm_num at hpos

/-- **The finite §2.6 shadows at the base table** (mandate § 3.5, reported *as shadows*): the base
is in the unit cube (D-PC shadow; the FAF-level fact is `linked_D_PCsmall_on`), the skeleton's law
at it is a probability on the grid (`E5` shadow) and balanced at it (D-NNU shadow, exact), and the
prior's state is a function (`E5`: the branch masses sum to one). Each FAF-level fact these shadow
is a conjunct of `segment_predicate_check`.
Source: mandate T3 ("the finite shadows on the table … reported *as shadows*")
Kind: C
Fidelity: variant: finite shadows (disclosed; the FAF-level facts are in `segment_predicate_check`)
Hyps: (a) -/
theorem shadows :
    (linkedTable n).InUnit ∧
    IsProb (Bli.segmentMesh K).d (((segmentSkeleton H K hK).κ n).law (linkedTable n)) ∧
    Balanced (Bli.segmentMesh K).d (((segmentSkeleton H K hK).κ n).law (linkedTable n))
      (linkedTable n) ∧
    ∑ T, (segmentSist H K hK n hn h2 c V r₀).stateMass T = 1 :=
  ⟨linkedTable_inUnit n, ((segmentSkeleton H K hK).κ n).prob (linkedTable n),
    ((segmentSkeleton H K hK).κ n).balanced (linkedTable n) (linkedTable_inUnit n),
    (segmentSist H K hK n hn h2 c V r₀).sum_stateMass⟩

end Check

end

end Cleanroom.Bli.BliWitnessLia
