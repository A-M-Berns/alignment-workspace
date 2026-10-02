import Cleanroom.Bli.BliMeasure.Coherence
import Cleanroom.Bli.BliMeasure.Bayes
import Cleanroom.Bli.BliMeasure.Constraints
import Cleanroom.Bli.BliCoherentMm.Recursion
import Cleanroom.Bli.BliCoherentMm.Witness

/-!
# `bli-measure` · Base: the instantiation over the coherent recursion of record

The abstract `CoherentBase` is discharged from `bli-coherent-mm`'s recursion with
`X := smallSet` (`pcQuote DP ov smallSet`, so that the priced set contains `smallSet n` —
`pcOverlaySmall_coherent`), under `hcons : ∀ n, ∃ v, v.ConsistentWith (DP.D n)` (F11; `paperDP_hcons`
at the witness). **Honest status**: `ComputableMarket (pcHistory DP ov smallSet)` is open upstream
(`bli-coherent-mm` F4/Known issue 8), so nothing here is a logical inductor — every row over the
recursion is `conditional on bli-coherent-mm: computability open`.

**Re-indexing.** The recursion's atom bound `pcAtoms` is `sup atomBound + 1` over
`pcSet n ∪ DP.D n`, and the firm's mentioned set need not be monotone; the base's bound is the
**running maximum** `recB n := max_{k ≤ n} pcAtoms k`, and the day-`n` measure is
`pcCoreWeights n` **spread uniformly over the fiber of extensions** (`spreadVec`: each world's
weight divided equally among the worlds over `recB n` atoms restricting to it). Spreading, rather
than extension by `false`, keeps **full support on every `DP.D n`-consistent world over the
re-indexed bound** (`recBase_fullSupport`), which target 4's `realized_charged` needs; marginals
of sentences within `pcAtoms n` atoms (all of `smallSet n ∪ DP.D n`) are unchanged
(`wMarginal_spreadVec`).

Bridges: `WMeasure` is `IsWorldMeasure` and `wMarginal` is `marginal`, by `rfl`.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliCoherentMm

/-! ## Bridges to `bli-coherent-mm` -/

/-- `WMeasure` is `bli-coherent-mm`'s `IsWorldMeasure`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wMeasure_iff_isWorldMeasure {B : ℕ} (w : FiniteWorld B → ℚ) (D : Finset Sentence) :
    WMeasure w D ↔ IsWorldMeasure w D := Iff.rfl

/-- `wMarginal` is `bli-coherent-mm`'s `marginal`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wMarginal_eq_marginal {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    wMarginal w φ = marginal w φ := rfl

/-! ## Spreading a measure over a larger atom bound -/

/-- The fiber of extensions of `u`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fiberOf {B B' : ℕ} (hB : B ≤ B') (u : FiniteWorld B) : Finset (FiniteWorld B') :=
  univ.filter fun u' => restrFW hB u' = u

/-- Every fiber is nonempty (it contains the extension by `false`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fiberOf_card_pos {B B' : ℕ} (hB : B ≤ B') (u : FiniteWorld B) : 0 < (fiberOf hB u).card :=
  Finset.card_pos.mpr ⟨extFW hB u, Finset.mem_filter.mpr ⟨mem_univ _, restrFW_extFW hB u⟩⟩

/-- **Spreading**: the measure on `FiniteWorld B'` giving each world the weight of its restriction
divided by the size of the restriction's fiber.
Source: [[bli-measure-mandate]] target 0 ("re-index the measures by extension — say which")
Kind: D
Fidelity: variant: uniform spread over the fiber (disclosed; chosen for full support) -/
noncomputable def spreadVec {B B' : ℕ} (hB : B ≤ B') (w : FiniteWorld B → ℚ) : FiniteWorld B' → ℚ :=
  fun u' => w (restrFW hB u') / ((fiberOf hB (restrFW hB u')).card : ℚ)

/-- Spreading preserves nonnegativity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spreadVec_nonneg {B B' : ℕ} (hB : B ≤ B') {w : FiniteWorld B → ℚ} (hw : ∀ u, 0 ≤ w u)
    (u' : FiniteWorld B') : 0 ≤ spreadVec hB w u' :=
  div_nonneg (hw _) (Nat.cast_nonneg _)

/-- A spread weight is nonzero iff the restriction's weight is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spreadVec_ne_zero_iff {B B' : ℕ} (hB : B ≤ B') (w : FiniteWorld B → ℚ) (u' : FiniteWorld B') :
    spreadVec hB w u' ≠ 0 ↔ w (restrFW hB u') ≠ 0 := by
  unfold spreadVec
  have hc : ((fiberOf hB (restrFW hB u')).card : ℚ) ≠ 0 := by
    exact_mod_cast (fiberOf_card_pos hB _).ne'
  rw [div_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩

/-- **Spreading preserves marginals within the bound** (and the total mass, at `⊤`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wMarginal_spreadVec {B B' : ℕ} (hB : B ≤ B') (w : FiniteWorld B → ℚ) {φ : Sentence}
    (hφ : atomBound φ ≤ B) : wMarginal (spreadVec hB w) φ = wMarginal w φ := by
  unfold wMarginal
  rw [← Finset.sum_fiberwise (univ : Finset (FiniteWorld B')) (restrFW hB)]
  apply Finset.sum_congr rfl
  intro u _
  have hc : ((fiberOf hB u).card : ℚ) ≠ 0 := by exact_mod_cast (fiberOf_card_pos hB u).ne'
  calc ∑ u' ∈ univ.filter (fun u' : FiniteWorld B' => restrFW hB u' = u),
        spreadVec hB w u' * u'.payoutRat φ
      = ∑ u' ∈ fiberOf hB u, w u / ((fiberOf hB u).card : ℚ) * u.payoutRat φ := by
        apply Finset.sum_congr rfl
        intro u' hu'
        rw [Finset.mem_filter] at hu'
        unfold spreadVec
        rw [hu'.2, ← payoutRat_restrFW hB u' hφ, hu'.2]
    _ = w u * u.payoutRat φ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp

/-- Spreading preserves the total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_spreadVec {B B' : ℕ} (hB : B ≤ B') (w : FiniteWorld B → ℚ) :
    ∑ u', spreadVec hB w u' = ∑ u, w u := by
  have := wMarginal_spreadVec hB w (φ := ⊤) (by show max 0 0 ≤ B; simp)
  rw [wMarginal_top, wMarginal_top] at this
  exact this

/-! ## The recursion's atom bounds and measures -/

variable (DP : DeductiveProcess) (ov : Cleanroom.Bli.BliOverlay.Overlay)

/-- The running maximum of the recursion's atom bounds.
Source: [[bli-measure-mandate]] target 0 ("take the running maximum")
Kind: D
Fidelity: exact -/
noncomputable def recB (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (pcAtoms DP ov smallSet)

/-- The recursion's bound is below the running maximum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcAtoms_le_recB (n : ℕ) : pcAtoms DP ov smallSet n ≤ recB DP ov n :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- The running maximum is monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recB_mono (n : ℕ) : recB DP ov n ≤ recB DP ov (n + 1) :=
  Finset.sup_mono (Finset.range_mono (Nat.le_succ _))

/-- Every day-`n` small sentence lies within the recursion's day-`n` bound.
Source: none: infrastructure (`pcAtoms_bound` at `X := smallSet`)
Kind: L
Fidelity: n/a -/
lemma atomBound_le_pcAtoms_of_small (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    atomBound φ ≤ pcAtoms DP ov smallSet n := by
  apply pcAtoms_bound DP ov smallSet n φ
  apply Finset.mem_union_left
  show φ ∈ mentionedSet (pcFirmStrat DP ov smallSet n) ∪ smallSet n
  exact Finset.mem_union_right _ hφ

/-- Every day-`n` stage sentence lies within the recursion's day-`n` bound.
Source: none: infrastructure (`pcAtoms_bound`)
Kind: L
Fidelity: n/a -/
lemma atomBound_le_pcAtoms_of_stage (n : ℕ) {φ : Sentence} (hφ : φ ∈ DP.D n) :
    atomBound φ ≤ pcAtoms DP ov smallSet n :=
  pcAtoms_bound DP ov smallSet n φ (Finset.mem_union_right _ hφ)

/-- **The recursion's atom bounds**: the running maximum of `pcAtoms`.
Source: [[bli-measure-mandate]] target 0 (instantiation of record, `B n := pcAtoms …`)
Kind: D
Fidelity: variant: running maximum (disclosed) -/
noncomputable def recAtomBounds : AtomBounds where
  B := recB DP ov
  B_mono := recB_mono DP ov
  B_cover n φ hφ := (atomBound_le_pcAtoms_of_small DP ov n hφ).trans (pcAtoms_le_recB DP ov n)
  B_unbounded a := ⟨tokenSize (Formula.atom a),
    lt_of_lt_of_le (Nat.lt_succ_self a)
      (show atomBound (Formula.atom a) ≤ recB DP ov (tokenSize (Formula.atom a)) from
        (atomBound_le_pcAtoms_of_small DP ov _
          (mem_smallSet.mpr (smallOn_tokenSize (Formula.atom a)))).trans
        (pcAtoms_le_recB DP ov _))⟩

/-- **The recursion's day-`n` measure**, spread over the running-maximum bound.
Source: [[bli-measure-mandate]] target 0 (`w n := pcCoreWeights DP ov smallSet n`, re-indexed)
Kind: D
Fidelity: variant: spread (disclosed) -/
noncomputable def recW (n : ℕ) : FiniteWorld (recB DP ov n) → ℚ :=
  spreadVec (pcAtoms_le_recB DP ov n) (pcCoreWeights DP ov smallSet n)

variable (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))

/-- **The coherent base of record**: `bli-coherent-mm`'s recursion with `X := smallSet`, under
`hcons`.
Source: [[bli-measure-mandate]] target 0 (instantiation of record); `bli-coherent-mm`
`pcOverlaySmall_coherent`, `pcAtoms_bound`
Kind: D
Fidelity: exact (bounds and measures re-indexed as disclosed)
Hyps: (a) `hcons` (F11; `paperDP_hcons` at the witness) -/
noncomputable def recBase : CoherentBase DP where
  𝔅 := recAtomBounds DP ov
  Q := pcQuote DP ov smallSet
  w := recW DP ov
  w_nonneg n u := spreadVec_nonneg _ ((pcOverlaySmall_coherent DP ov n (hcons n)).1).1 u
  w_sum n := by
    show ∑ u : FiniteWorld (recB DP ov n),
      spreadVec (pcAtoms_le_recB DP ov n) (pcCoreWeights DP ov smallSet n) u = 1
    rw [sum_spreadVec]
    exact ((pcOverlaySmall_coherent DP ov n (hcons n)).1).2.1
  w_supp n u hu := by
    unfold recW at hu
    rw [spreadVec_ne_zero_iff] at hu
    have hc := ((pcOverlaySmall_coherent DP ov n (hcons n)).1).2.2 _ hu
    intro φ hφ
    exact (holds_worldOf_restrFW (pcAtoms_le_recB DP ov n) u
      (atomBound_le_pcAtoms_of_stage DP ov n hφ)).mp (hc φ hφ)
  Q_eq n φ hφ := by
    show pcQuote DP ov smallSet n φ =
      wMarginal (spreadVec (pcAtoms_le_recB DP ov n) (pcCoreWeights DP ov smallSet n)) φ
    rw [(pcOverlaySmall_coherent DP ov n (hcons n)).2 φ hφ,
      wMarginal_spreadVec _ _ (atomBound_le_pcAtoms_of_small DP ov n hφ)]
    rfl
  B_stage n φ hφ := (atomBound_le_pcAtoms_of_stage DP ov n hφ).trans (pcAtoms_le_recB DP ov n)

/-- The base of record has full support on every consistent world over its bound (from
`pcCoreWeights_fullSupport`, through the spread).
Source: `bli-coherent-mm` `pcCoreWeights_fullSupport`; [[bli-measure-mandate]] target 4
Kind: L
Fidelity: exact -/
theorem recBase_fullSupport (n : ℕ) :
    ∀ u : FiniteWorld ((recBase DP ov hcons).𝔅.B n),
      (worldOf u).ConsistentWith (DP.D n) → (recBase DP ov hcons).w n u ≠ 0 := by
  intro u hu
  show spreadVec _ (pcCoreWeights DP ov smallSet n) u ≠ 0
  rw [spreadVec_ne_zero_iff]
  apply ne_of_gt
  apply pcCoreWeights_fullSupport DP ov smallSet n (hcons n)
  rw [mem_WD]
  intro φ hφ
  exact (holds_worldOf_restrFW (pcAtoms_le_recB DP ov n) u
    (atomBound_le_pcAtoms_of_stage DP ov n hφ)).mpr (hu φ hφ)

/-! ## B3 over the recursion of record -/

/-- **`𝐏` of record**: B3 over the coherent recursion (`X := smallSet`) and a mesh.
Source: [[bli-measure-mandate]] target 0 (instantiation of record)
Kind: D
Fidelity: exact; conditional on `bli-coherent-mm`: computability open -/
noncomputable def pcB3History (𝓜 : Mesh) : History := b3History (recBase DP ov hcons) 𝓜

/-- The state system of record over the recursion.
Source: [[bli-measure-mandate]] target 0
Kind: D
Fidelity: exact -/
noncomputable def pcB3StateSystem (𝓜 : Mesh) : StateSystem := b3StateSystem (recBase DP ov hcons) 𝓜

/-- **T3 over the recursion of record**: exact total Bayesian update on every sentence.
Source: [[bli-measure-mandate]] target 3
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) `hcons` -/
theorem pcB3_TB (𝓜 : Mesh) : TB (pcB3StateSystem DP ov hcons 𝓜) (pcB3History DP ov hcons 𝓜) :=
  b3_TB _ 𝓜

/-- **T1 over the recursion of record**: `𝐏_n` coherent on every finite algebra relative to the B3
stage.
Source: [[bli-measure-mandate]] target 1
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) `hcons`, `hfree` -/
theorem pcB3_coherentOn (hfree : TagFreeProcess stateTag DP) (𝓜 : Mesh) (n : ℕ) (A : Finset ℕ) :
    Cleanroom.Bli.BliFound.CoherentOn (b3Stage (recBase DP ov hcons) 𝓜 n) A (pcB3History DP ov hcons 𝓜 n) :=
  b3History_coherentOn _ 𝓜 hfree n A

/-- **`PCP` over `bliDP` for the recursion of record**.
Source: [[bli-measure-mandate]] target 1(b)
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) `hcons`, `hfree` -/
theorem pcB3_PCP_bliDP (hfree : TagFreeProcess stateTag DP) (𝓜 : Mesh) (hh : ℕ → ℕ) :
    PCP hh (pcB3StateSystem DP ov hcons 𝓜)
      (bliDP DP (wstates (recBase DP ov hcons).𝔅 𝓜) (b3Actual (recBase DP ov hcons) 𝓜))
      (pcB3History DP ov hcons 𝓜) :=
  b3History_PCP_bliDP _ 𝓜 hfree hh

/-- **The B3 bundle over the recursion of record.**
Source: [[bli-measure-mandate]] target 2
Kind: C
Fidelity: variant: scopes as `IsBLI_B3`; conditional on `bli-coherent-mm`: computability open
Hyps: (a) `hcons` -/
theorem pcB3_isBLI_B3 (𝓜 : Mesh) :
    IsBLI_B3 (recB DP ov) (pcB3StateSystem DP ov hcons 𝓜) (pcB3History DP ov hcons 𝓜) :=
  b3_isBLI_B3 _ 𝓜

/-! ## Over `paperDP 𝗜𝚺₁` -/

/-- **B3 over the paper process** (`paperDP 𝗜𝚺₁`, every stage consistent by `paperDP_hcons`).
Source: [[bli-measure-mandate]] target 0 ("the witness over `paperDP 𝗜𝚺₁` for every headline")
Kind: D
Fidelity: exact; conditional on `bli-coherent-mm`: computability open -/
noncomputable def paperB3History (ov : Cleanroom.Bli.BliOverlay.Overlay) (𝓜 : Mesh) : History :=
  pcB3History (paperDP 𝗜𝚺₁) ov paperDP_hcons 𝓜

/-- The state system of record over the paper process.
Source: [[bli-measure-mandate]] target 0
Kind: D
Fidelity: exact -/
noncomputable def paperB3StateSystem (ov : Cleanroom.Bli.BliOverlay.Overlay) (𝓜 : Mesh) : StateSystem :=
  pcB3StateSystem (paperDP 𝗜𝚺₁) ov paperDP_hcons 𝓜

/-- **T3 over the paper process**, unconditional.
Source: [[bli-measure-mandate]] target 3 (witness)
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paperB3_TB (ov : Cleanroom.Bli.BliOverlay.Overlay) (𝓜 : Mesh) : TB (paperB3StateSystem ov 𝓜) (paperB3History ov 𝓜) :=
  pcB3_TB _ ov paperDP_hcons 𝓜

/-- **T1 over the paper process**, unconditional (`paperDP_tagFree` discharges `hfree`).
Source: [[bli-measure-mandate]] target 1 (witness)
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paperB3_coherentOn (ov : Cleanroom.Bli.BliOverlay.Overlay) (𝓜 : Mesh) (n : ℕ) (A : Finset ℕ) :
    Cleanroom.Bli.BliFound.CoherentOn (b3Stage (recBase (paperDP 𝗜𝚺₁) ov paperDP_hcons) 𝓜 n) A
      (paperB3History ov 𝓜 n) :=
  pcB3_coherentOn _ ov paperDP_hcons (paperDP_tagFree 𝗜𝚺₁ le_rfl) 𝓜 n A

/-- **`PCP` over `bliDP` for the paper process**, unconditional.
Source: [[bli-measure-mandate]] target 1(b) (witness)
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paperB3_PCP_bliDP (ov : Cleanroom.Bli.BliOverlay.Overlay) (𝓜 : Mesh) (hh : ℕ → ℕ) :
    PCP hh (paperB3StateSystem ov 𝓜)
      (bliDP (paperDP 𝗜𝚺₁) (wstates (recBase (paperDP 𝗜𝚺₁) ov paperDP_hcons).𝔅 𝓜)
        (b3Actual (recBase (paperDP 𝗜𝚺₁) ov paperDP_hcons) 𝓜))
      (paperB3History ov 𝓜) :=
  pcB3_PCP_bliDP _ ov paperDP_hcons (paperDP_tagFree 𝗜𝚺₁ le_rfl) 𝓜 hh

/-- **The B3 bundle over the paper process**, unconditional.
Source: [[bli-measure-mandate]] target 2 (witness)
Kind: C
Fidelity: variant: scopes as `IsBLI_B3`; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paperB3_isBLI_B3 (ov : Cleanroom.Bli.BliOverlay.Overlay) (𝓜 : Mesh) :
    IsBLI_B3 (recB (paperDP 𝗜𝚺₁) ov) (paperB3StateSystem ov 𝓜) (paperB3History ov 𝓜) :=
  pcB3_isBLI_B3 _ ov paperDP_hcons 𝓜

end Cleanroom.Bli.BliMeasure
