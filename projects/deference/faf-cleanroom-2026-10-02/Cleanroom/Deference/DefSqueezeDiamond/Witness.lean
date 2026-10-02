import Cleanroom.Deference.DefSqueezeDiamond.GapIndicator
import Cleanroom.Deference.DefSqueezeDiamond.HardRefuted

/-!
# `def-squeeze-diamond` · Witness: non-vacuity on the diagonal family

The source of record is FAF's own diagonal family `χ_n := (paperDiagonalQuoteCode T ½).sentence n`
— `χ_n ↔ P_n(χ_n) < ½` in every completed-theory world, whose price tends to `½` (FAF's
`lic_paradox_resistance_ofDiagonal_unconditional`) and is never decided in advance: the
literal-indicator source `X n := literalIndicator (χ n)` is valued, in every world, at the
market-decided bit `1[P_n(χ_n) < ½]`, a non-constant family in general. Over `𝗣𝗔` at
`succDeferral` (and at every strictly increasing `f`):

* **Target 1 (N+)** `witness_reindex`: target 1's `_eq` endpoint on the two-term deferred
  combination `X + ⌜1[½ ≤ P_n(χ_n)]⌝ − 1` (world value `0` everywhere), giving the deferred-day
  identity `P_{f n}(χ_n) ≈ₙ 1 − E_{f n}(⌜1[½ ≤ P_n(χ_n)]⌝)` — the reindexing exercised on a
  family whose deferred-day prices are not constant and whose members are not provable.
* **Target 2a (N+)** `witness_pin_diagonal`: the pin `E_{f n}(G_n) ≈ₙ ½` on the indicator gap
  `G := indicatorGap` of `X` (sign `+1`), a LUV valued at `(payout(χ_n) − P_{f n}(χ_n) + 1)/2`
  — neither constant nor decided in advance.
* **Target 2b (N+)** `witness_fold_diagonal`: the fold at `rampAbove (1/4) (1/2)` on `X` with
  FAF's ramp quote `paperRampQuote`.
* **Target 7** is witnessed in `HardRefuted.lean` itself (`deferredLiarOfDiagonal`,
  `sameDay_hard_faces_refuted`).

`def-self-trust`'s parity family is N− for pins (a decided source: the pin is trivial), recorded.
The only file importing `HardRefuted` together with `GapIndicator`; no `LIACompiler`
(li-quote-lane's `Witnesses.lean` is not needed: the distinct-novice arrows of `PaperArrows`
are instantiated on the ledger process in that file's own `example`).
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- FAF's diagonal family at threshold `½`: `χ_n ↔ P_n(χ_n) < ½`.
Source: FAF `paperDiagonalQuoteCode` (`Construction/Paper/Market.lean`)
Kind: D
Fidelity: exact -/
def diagFamily : ℕ → Sentence :=
  (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence

omit [Entailment.Consistent T] in
/-- The diagonal family is e.c.
Source: FAF `BooleanQuoteCode.sentence_poly`, `MachineSentenceCodes.ofPolySentenceCodes`
Kind: L
Fidelity: n/a -/
theorem diagFamily_codes : MachineSentenceCodes (diagFamily T) :=
  MachineSentenceCodes.ofPolySentenceCodes
    (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly

omit [Entailment.Consistent T] in
/-- The diagonal clause in every completed-theory world.
Source: FAF `BooleanQuoteCode.reflected`, `parameterizedDiagonalQuoteCodeOfMarket_public_price_iff`
Kind: L
Fidelity: n/a -/
theorem diagFamily_holds_iff (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (diagFamily T n) ↔ liaHistory (paperDP T) n (diagFamily T n) < ((1 / 2 : ℚ) : ℝ) :=
  ((paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.reflected
    (paperQuotationPresentation T) n v hv).trans
    (parameterizedDiagonalQuoteCodeOfMarket_public_price_iff (paperMarketComputation T) T
      (1 / 2) n)

/-- **Target 1, N+**: on the diagonal family, the deferred-day identity
`P_{f n}(χ_n) ≈ₙ 1 − E_{f n}(⌜1[½ ≤ P_n(χ_n)]⌝)` from target 1's `_eq` endpoint on the
two-term deferred combination `1(χ) + ⌜1[½ ≤ P_n(χ_n)]⌝ − 1`, valued `0` in every world
(`1[P_n(χ_n) < ½] + 1[½ ≤ P_n(χ_n)] = 1`). The source is non-constant and not provable; both
sides vary with `n`.
Source: mandate target 1 (witness: "the diagonal family … reindexed along `succDeferral`, with
1b's conclusion exercised on it")
Kind: N+
Fidelity: exact
Hyps: (a); `hf` -/
theorem witness_reindex (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    (fun n => liaHistory (paperDP T) (f n) (diagFamily T n)) ≈ₙ
      (fun n => 1 - (sharpW T Computable.id (diagFamily_codes T) n).expect
        (liaHistory (paperDP T)) (f n)) := by
  set P := liaHistory (paperDP T) with hP
  set X : ℕ → LUV := fun n => literalIndicator (diagFamily T n) with hX
  set W : ℕ → LUV := sharpW T Computable.id (diagFamily_codes T) with hW
  have hXc : LUV.MachineThresholdCodeSeq X := literalIndicator_machineThresholdCodeSeq (diagFamily_codes T)
  have hWc : LUV.MachineThresholdCodeSeq W := (sharp_codes T Computable.id (diagFamily_codes T)).1
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, X), (fun _ => EF.const 1, W)] with hterms
  have hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact constWeighting 1
  have hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hXc
    · exact hWc
  have hvalued : ∀ p ∈ terms, Valued (paperDP T) p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact fun n v hv => ⟨_, literalIndicator_valuesAt _ _ hv⟩
    · exact fun n v hv => ⟨_, sharpW_reflected T Computable.id (diagFamily_codes T) n v hv⟩
  have h := expect_deferred_asympEq_zero_of_slack (P := P) (DP := paperDP T) f hf
    (c₀ := fun _ => EF.const (-1)) (constWeighting (-1)) hcoeff hluv hvalued (B := 3) (by norm_num)
    (fun m => by
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
      norm_num)
    (fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have hXν := hν (fun _ => EF.const 1, X) (by simp [hterms])
      have hWν := hν (fun _ => EF.const 1, W) (by simp [hterms])
      simp only at hXν hWν
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
      rw [hXν.eq (literalIndicator_valuesAt _ _ hv),
        hWν.eq (sharpW_reflected T Computable.id (diagFamily_codes T) n v hv)]
      have h12 : ((1 / 2 : ℚ) : ℝ) = 2⁻¹ := by norm_num
      have hiff : v.Holds (diagFamily T n) ↔ P n (diagFamily T n) < (2⁻¹ : ℝ) := by
        rw [← h12]; exact diagFamily_holds_iff T n v hv
      have key : v.payout (diagFamily T n) + hardAbove (1 / 2) (P (id n) (diagFamily T n)) = 1 := by
        unfold PCWorld.payout hardAbove
        rw [h12]
        by_cases hlt : P n (diagFamily T n) < (2⁻¹ : ℝ)
        · have hh : v.Holds (diagFamily T n) := hiff.mpr hlt
          simp [hh, not_le.2 hlt]
        · have hnot : ¬ v.Holds (diagFamily T n) := fun hh => hlt (hiff.mp hh)
          simp [hnot, not_lt.1 hlt]
      simp only [id_eq] at key ⊢
      push_cast
      rw [abs_le]
      constructor <;> linarith [key]) (paperDP_hworld T)
  have h' : (fun n => P (f n) (diagFamily T n) - (1 - (W n).expect P (f n))) ≈ₙ (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const, hX, literalIndicator_expect]
    push_cast
    ring
  exact asympEq_sub_zero_iff.mp h'

/-- **Target 2a, N+**: the self-expert pins the indicator gap of the diagonal family at `½`,
`E_{f n}(G_n) ≈ₙ ½` with `G := indicatorGap` (sign `+1`), valued at
`(payout(χ_n) − P_{f n}(χ_n) + 1)/2` — a non-constant LUV not decided in advance.
Source: mandate target 2 (witness: "2a on the gap of the diagonal family")
Kind: N+
Fidelity: exact
Hyps: (a); `hf` -/
theorem witness_pin_diagonal (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (indicatorGap T f (Or.inl rfl) (diagFamily_codes T)) (1 / 2) :=
  selfPinGap T f hf (Or.inl rfl) (literalIndicator_machineThresholdCodeSeq (diagFamily_codes T))
    (gapQuote_indicator T f (Or.inl rfl) (diagFamily_codes T))

/-- **Target 2b, N+**: the fold at `rampAbove (1/4) (1/2)` on the diagonal family's indicator
source with FAF's ramp quote.
Source: mandate target 2 (witness: "2b at `rampAbove (1/4) (1/2)` on the same family")
Kind: N+
Fidelity: exact
Hyps: (a); `hf` -/
theorem witness_fold_diagonal (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ExpertFoldAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (diagFamily T n)) (rampAbove (1 / 4) (1 / 2))
      (estXW T f (literalIndicator_machineThresholdCodeSeq (diagFamily_codes T))
        (by norm_num : (0 : ℚ) < 1 / 4) (1 / 2)) :=
  selfFoldsAt_rampAbove T f hf (1 / 2) (by norm_num) _ _ _
    (literalIndicator_machineThresholdCodeSeq (diagFamily_codes T))
    (paperRampQuote T f (extendsBase_self T) hf.injective
      (literalIndicator_machineThresholdCodeSeq (diagFamily_codes T))
      (fun n v hv => ⟨_, literalIndicator_valuesAt _ _ hv⟩) (by norm_num) (1 / 2))

/-- The witnesses over `𝗣𝗔` at `succDeferral`.
Source: mandate design decision 7
Kind: N+
Fidelity: n/a -/
example :
    ExpertPin (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
      (indicatorGap 𝗣𝗔 succDeferral (Or.inl rfl) (diagFamily_codes 𝗣𝗔)) (1 / 2) :=
  witness_pin_diagonal 𝗣𝗔 succDeferral succDeferral_strict

end

end Cleanroom.Deference.DefSqueezeDiamond
