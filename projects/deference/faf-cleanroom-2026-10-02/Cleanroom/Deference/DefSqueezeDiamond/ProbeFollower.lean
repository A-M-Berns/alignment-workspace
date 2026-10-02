import Cleanroom.Deference.DefSqueezeDiamond.GapIndicator
import Cleanroom.Deference.DefLatticeArrows.Probe

/-!
# `def-squeeze-diamond` · ProbeFollower: the probe follower of the self-expert on every e.c.
valued gap bet (target 4b's probe package; repair round 1)

The arrows' `ProbeData DP E ε G S hG` asks for an e.c. follower `S` of the expert's least-index
argmax on the probe menu `{G, K_ε}` (`Follows`: in every completed-theory world `S n` is valued
as the chosen option). The choice is `Menu.argmax_two`: option `0` (the gap bet `G`) iff
`E*(K_ε) ≤ E*(G_n)`, a **decided comparison of two of the expert's own prices** — both are
FAF's computable rationals `expectQuoteAt` at the deferred day. So the follower is the select
(`GapIndicator`'s `selectLUV`) between `G` and `K_ε` by the quoted bit
`⌜1[E*(K_ε) ≤ E*(G_n)] > ½⌝` (`followBit`, quoted by `RationalQuoteCode.ofComputable` exactly as
`HardRefuted`'s sharp weights are): e.c. by `selectLUV_codes`, and `Follows` because the bit is
reflected in every world (`followSentence_holds_iff`) and the select is valued at the selected
option (`selectLUV_valuesAt`). Nothing depends on which gap LUV `G` is — any e.c. valued `G`
has a probe follower at every margin (`probeData_self`). The boundary `E*(K_ε) = E*(G_n)` is
handled exactly: the argmax takes option `0` there, and so does the bit (`≤`).

Construction-facing; single market (self).
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The decided comparison** `1[E*(K_ε) ≤ E*(G_n)]` at the deferred day, as a computable
`{0,1}`-rational: the self-expert's least-index argmax on `{G, K_ε}` takes `G` exactly when it
is `1` (`Menu.argmax_two`).
Source: mandate target 4b ("a select by the decided comparison of two quotes"); `def-lattice`
`Menu.argmax` ("the ledger-decided least-index rule")
Kind: D
Fidelity: exact -/
def followBit (f : DeferralFunction) (ε : ℚ) (G : ℕ → LUV) (n : ℕ) : ℚ :=
  if (paperMarketComputation T).expectQuoteAt (probeConst ε) n (f.f n) ≤
      (paperMarketComputation T).expectQuoteAt G n (f.f n) then 1 else 0

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The decided comparison is computable (both prices by FAF's `expectQuoteAt_computable`, the
comparison by `ratLE_prim`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem followBit_computable (f : DeferralFunction) {ε : ℚ} (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) : Computable (followBit T f ε G) := by
  have hK0 : 0 ≤ (1 - ε) / 2 := by linarith
  have hK : Computable fun n =>
      (paperMarketComputation T).expectQuoteAt (probeConst ε) n (f.f n) :=
    (((paperMarketComputation T).expectQuoteAt_computable (constLUV_codes hK0)).comp
      (Computable.id.pair f.computable) : _)
  have hG' : Computable fun n => (paperMarketComputation T).expectQuoteAt G n (f.f n) :=
    (((paperMarketComputation T).expectQuoteAt_computable hG).comp
      (Computable.id.pair f.computable) : _)
  have hleB : Primrec fun p : ℚ × ℚ => decide (p.1 ≤ p.2) := ratLE_prim.decide
  have hdec : Computable fun n => decide
      ((paperMarketComputation T).expectQuoteAt (probeConst ε) n (f.f n) ≤
        (paperMarketComputation T).expectQuoteAt G n (f.f n)) :=
    (hleB.to_comp.comp (hK.pair hG') : _)
  exact (Computable.cond hdec (Computable.const (1 : ℚ)) (Computable.const (0 : ℚ))).of_eq
    (fun n => by simp [followBit, Bool.cond_decide])

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The decided comparison lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem followBit_mem (f : DeferralFunction) (ε : ℚ) (G : ℕ → LUV) (n : ℕ) :
    0 ≤ followBit T f ε G n ∧ followBit T f ε G n ≤ 1 := by
  unfold followBit
  split_ifs <;> norm_num

/-- FAF's quote code of the decided comparison.
Source: mandate design decision 5 (sharp weights as quoted decided numbers)
Kind: D
Fidelity: exact -/
def followBitCode (f : DeferralFunction) {ε : ℚ} (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) : RationalQuoteCode T (followBit T f ε G) :=
  RationalQuoteCode.ofComputable T (followBit_computable T f hε1 hG) (followBit_mem T f ε G)

/-- **The selector sentence** `⌜1[E*(K_ε) ≤ E*(G_n)] > ½⌝`: holds in every completed-theory
world exactly when the expert's argmax on `{G, K_ε}` is `G`.
Source: mandate target 4b
Kind: D
Fidelity: exact -/
def followSentence (f : DeferralFunction) {ε : ℚ} (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) (n : ℕ) : Sentence :=
  ((followBitCode T f hε1 hG).luv n).gt ((1 : ℚ) / 2)

omit [Entailment.Consistent T] in
/-- The selector family is e.c. (the quote's threshold stream read at `⟨n, ⟨2, 1⟩⟩`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem followSentence_codes (f : DeferralFunction) {ε : ℚ} (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) : MachineSentenceCodes (followSentence T f hε1 hG) :=
  (MachineSentenceCodes.comp (followBitCode T f hε1 hG).poly
    (UnaryRuler.id.pair ((UnaryRuler.const 2).pair (UnaryRuler.const 1)))).of_eq
    (fun n => by simp [followSentence])

omit [Entailment.Consistent T] in
/-- **The selector is reflected**: a completed-theory world holds `followSentence n` iff
`E*(K_ε) ≤ E*(G_n)` (the rational comparison of the two deferred-day prices).
Source: none: infrastructure (FAF `RationalQuoteCode.reflected`)
Kind: L
Fidelity: n/a -/
theorem followSentence_holds_iff (f : DeferralFunction) {ε : ℚ} (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (followSentence T f hε1 hG n) ↔
      (paperMarketComputation T).expectQuoteAt (probeConst ε) n (f.f n) ≤
        (paperMarketComputation T).expectQuoteAt G n (f.f n) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (followBitCode T f hε1 hG)
    n v hv
  unfold followSentence
  by_cases hc : (paperMarketComputation T).expectQuoteAt (probeConst ε) n (f.f n) ≤
      (paperMarketComputation T).expectQuoteAt G n (f.f n)
  · have hb : followBit T f ε G n = 1 := by simp [followBit, hc]
    rw [hb] at h
    exact ⟨fun _ => hc, fun _ => (h.2.2 ((1 : ℚ) / 2)).1 (by norm_num)⟩
  · have hb : followBit T f ε G n = 0 := by simp [followBit, hc]
    rw [hb] at h
    exact ⟨fun hh => absurd hh ((h.2.2 ((1 : ℚ) / 2)).2 (by norm_num)),
      fun hc' => absurd hc' hc⟩

/-- **The probe follower**: the select between the gap bet and the constant probe by the
decided comparison.
Source: mandate target 4b (the probe package); [[value-implies-tower]] §The probe menu
Kind: D
Fidelity: exact -/
def probeFollower (f : DeferralFunction) {ε : ℚ} (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) : ℕ → LUV :=
  selectLUV (followSentence T f hε1 hG) G (probeConst ε)

omit [Entailment.Consistent T] in
/-- The probe follower is e.c.
Source: none: infrastructure (`selectLUV_codes`)
Kind: L
Fidelity: n/a -/
theorem probeFollower_codes (f : DeferralFunction) {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {G : ℕ → LUV} (hG : LUV.MachineThresholdCodeSeq G) :
    LUV.MachineThresholdCodeSeq (probeFollower T f hε1 hG) :=
  selectLUV_codes (followSentence_codes T f hε1 hG) hG
    (constLUV_codes (probeConst_mem hε hε1).1)

omit [Entailment.Consistent T] in
/-- **The probe follower follows the self-expert's argmax** on `{G, K_ε}`: where the expert
quotes `G` at least as high as `K_ε` the argmax is `0` (`Menu.argmax_two`) and the selector
holds, so the select is valued as `G n`; otherwise the argmax is `1`, the selector fails, and
the select is valued as `K_ε`.
Source: mandate target 4b; `def-lattice` `Follows`
Kind: C
Fidelity: exact
Hyps: (a); `hGv : Valued (paperDP T) G` -/
theorem probeFollower_follows (f : DeferralFunction) {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {G : ℕ → LUV} (hG : LUV.MachineThresholdCodeSeq G) (hGv : Valued (paperDP T) G) :
    Follows (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (twoOptionMenu G (probeConst ε) hG (constLUV_codes (probeConst_mem hε hε1).1))
      (probeFollower T f hε1 hG) := by
  intro n v hv x hx
  set E := Expert.self (liaHistory (paperDP T)) (paperDP T) f with hE
  set M := twoOptionMenu G (probeConst ε) hG (constLUV_codes (probeConst_mem hε hε1).1) with hM
  have hargmax := M.argmax_two E n
  simp only [hM, Menu.quote, twoOptionMenu_O_zero, twoOptionMenu_O_one] at hargmax
  have hiff : (E.estimate (probeConst ε) n ≤ E.estimate G n) ↔
      ((paperMarketComputation T).expectQuoteAt (probeConst ε) n (f.f n) ≤
        (paperMarketComputation T).expectQuoteAt G n (f.f n)) := by
    simp only [hE, Expert.self_estimate]
    rw [(paperMarketComputation T).expectQuoteAt_cast (probeConst ε) n (f.f n),
      (paperMarketComputation T).expectQuoteAt_cast G n (f.f n)]
    exact Rat.cast_le
  obtain ⟨g, hg⟩ := hGv n v hv
  have hK := constLUV_valuesAt (probeConst_mem hε hε1) v
  have hsel := selectLUV_valuesAt (followSentence T f hε1 hG) G (probeConst ε) n v hg hK
  show v.ValuesAt (selectLUV (followSentence T f hε1 hG) G (probeConst ε) n) x
  by_cases hc : E.estimate (probeConst ε) n ≤ E.estimate G n
  · rw [if_pos hc] at hargmax
    rw [hargmax] at hx
    simp only [hM, twoOptionMenu_O_zero] at hx
    have hφ : v.Holds (followSentence T f hε1 hG n) :=
      (followSentence_holds_iff T f hε1 hG n v hv).2 (hiff.1 hc)
    rw [if_pos hφ] at hsel
    rw [hx.eq hg]
    exact hsel
  · rw [if_neg hc] at hargmax
    rw [hargmax] at hx
    simp only [hM, twoOptionMenu_O_one] at hx
    have hφ : ¬ v.Holds (followSentence T f hε1 hG n) :=
      fun h => hc (hiff.2 ((followSentence_holds_iff T f hε1 hG n v hv).1 h))
    rw [if_neg hφ] at hsel
    rw [hx.eq hK]
    exact hsel

/-- **The probe data of the self-expert on every e.c. valued gap bet, at every margin** (target
4b's probe package, (a)): the follower is `probeFollower`.
Source: mandate target 4b; `def-lattice-arrows` `ProbeData`
Kind: C
Fidelity: exact
Hyps: (a); `hGv` -/
def probeData_self (f : DeferralFunction) {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) {G : ℕ → LUV}
    (hG : LUV.MachineThresholdCodeSeq G) (hGv : Valued (paperDP T) G) :
    ProbeData (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ε G
      (probeFollower T f hε1 hG) hG where
  hε := ⟨hε, hε1⟩
  codes_S := probeFollower_codes T f hε hε1 hG
  follows := probeFollower_follows T f hε hε1 hG hGv

end

end Cleanroom.Deference.DefSqueezeDiamond
