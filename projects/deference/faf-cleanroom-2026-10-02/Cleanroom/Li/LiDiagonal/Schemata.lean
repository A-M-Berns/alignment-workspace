import Cleanroom.Li.LiDiagonal.Grade

/-!
# `li-diagonal` · Schemata: the 2×2 verdict table for endorsement on the deferred liar (T5g)

trust-lab-026 asks for the "maximal" endorsement schema on the deferred liar among all
schemata — ill-posed (there is no order on schemata; finding F-4). The honest stand-in is the
verdict table over the four schemata `{hard, soft δ} × {=, ≥}`:

| schema | reading | verdict |
|---|---|---|
| hard `=` at `t` | `P_n(χ_n ⋏ ∼χ_n) ≈ₙ t · P_n(∼χ_n)` | **fails** for every `t > 0` (`hard_eq_schema_fails`) |
| hard `≥` at `t` | `P_n(χ_n ⋏ ∼χ_n) ≳ₙ t · P_n(∼χ_n)` | **fails** for every `t > 0` (`hard_ge_schema_fails`) |
| soft `=` at `p'` | `𝔼_n(A_n) ≈ₙ p' · 𝔼_n(B_n)` | **fails** for every `p' + δ < p` (`soft_eq_schema_fails`) |
| soft `≥` at `p'` | `𝔼_n(A_n) ≳ₙ p' · 𝔼_n(B_n)` | **holds** for every `p'` (FAF's `thm:st`, `soft_self_trust_deferredDiagonal`) |

Here `χ := defDiag (kleeneDiag T market p) f` is the deferred liar at threshold `p ∈ (0,1)`,
`A_n`, `B_n` are `thm:st`'s product and confidence LUVs at constant width `δ` and threshold
`p'`. The hard rows are stronger than the mandate's (which asked for `t = ½` at `p = ½`): the
left side `→ 0` (`lic_provind_false` on the refutable family `χ_n ⋏ ∼χ_n`) while the right side
`→ t(1 − p) > 0` (T5d). The soft-`=` row is the new content made possible by `Grade.lean`: the
left side `→ p`, the right side `→ p'`. `schemata_two_by_two` bundles the four over one
`SelfTrustQuote` package and one `thm:ceu` package.

Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

/-- The refutable conjunction `χ_n ⋏ ∼χ_n` of any e.c. family has price `→ 0` (FAF's
`lic_provind_false`; the step inside T5e, named).
Scope: single-market.
Source: LI paper `thm:provind`; [[li-diagonal-mandate]] T5e
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem conj_neg_price_tendsto_zero (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (χ : ℕ → Sentence) (hχ : MachineSentenceCodes χ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n (χ n ⋏ ∼ χ n)) atTop (𝓝 0) := by
  have h := lic_provind_false P DP (fun n => χ n ⋏ ∼ χ n) (hχ.and hχ.neg) (fun n v _ => by
      rw [PCWorld.holds_neg, PCWorld.holds_and, PCWorld.holds_neg]
      tauto) hworld
  unfold AsympEq at h
  simpa using h

section Schemata

variable {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
  (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
  (market : MarketComputation P) (p : ℚ) (f : DeferralFunction)

include Q

/-- The negated deferred liar's price tends to `1 − p` (T5d in `Tendsto` form).
Source: [[li-diagonal-mandate]] T5d
Kind: L
Fidelity: exact
Hyps: (a) `hq` (the `thm:ceu` package) -/
theorem defDiag_neg_price_tendsto (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market p) f) Y) :
    Tendsto (fun n => P n (∼ defDiag (kleeneDiag T market p) f n)) atTop (𝓝 (1 - (p : ℝ))) := by
  have h := defDiag_neg_price_of_quote Q P market p f hp0 hp1 hworld Y hq
  unfold AsympEq at h
  simpa using h.add_const (1 - (p : ℝ))

/-- **Hard `=` fails at every positive threshold.** `¬ (P_n(χ_n ⋏ ∼χ_n) ≈ₙ t · P_n(∼χ_n))` for
`t > 0`: the left side `→ 0`, the right side `→ t(1 − p) > 0`. T5e is the case `t = p = ½`.
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 023, 026; [[li-diagonal-mandate]] T5e, T5g
Kind: P
Fidelity: stronger (every `t > 0`, every `p ∈ (0,1)`; the source has `t = ½`)
Hyps: (a) `hq` (the `thm:ceu` package; discharged over the paper market in `Paper.lean`) -/
theorem hard_eq_schema_fails (hp0 : 0 < p) (hp1 : p < 1) (t : ℚ) (ht : 0 < t)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market p) f) Y) :
    ¬ ((fun n => P n (defDiag (kleeneDiag T market p) f n ⋏
          ∼ defDiag (kleeneDiag T market p) f n)) ≈ₙ
        fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) := by
  intro h
  have hfalse := conj_neg_price_tendsto_zero P DP _ hq.sentence_codes hworld
  have hneg := defDiag_neg_price_tendsto Q P market p f hp0 hp1 hworld Y hq
  have hB : Tendsto (fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) atTop
      (𝓝 ((t : ℝ) * (1 - p))) := hneg.const_mul _
  have hB0 : Tendsto (fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) atTop
      (𝓝 0) := by
    unfold AsympEq at h
    have := hfalse.sub h
    simpa using this
  have huniq := tendsto_nhds_unique hB0 hB
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpR : (p : ℝ) < 1 := by exact_mod_cast hp1
  have : (0 : ℝ) < (t : ℝ) * (1 - p) := mul_pos htR (by linarith)
  linarith

/-- **Hard `≥` fails at every positive threshold.** `¬ (P_n(χ_n ⋏ ∼χ_n) ≳ₙ t · P_n(∼χ_n))` for
`t > 0`: the demand `t(1 − p) − o(1)` exceeds the vanishing left side.
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 026; [[li-diagonal-mandate]] T5g ("hard-`≥` fails … `0 ≳ ½·𝔼(w)` against T5d")
Kind: P
Fidelity: stronger (every `t > 0`, every `p ∈ (0,1)`)
Hyps: (a) `hq` (the `thm:ceu` package) -/
theorem hard_ge_schema_fails (hp0 : 0 < p) (hp1 : p < 1) (t : ℚ) (ht : 0 < t)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market p) f) Y) :
    ¬ ((fun n => P n (defDiag (kleeneDiag T market p) f n ⋏
          ∼ defDiag (kleeneDiag T market p) f n)) ≳ₙ
        fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) := by
  intro h
  have hfalse := conj_neg_price_tendsto_zero P DP _ hq.sentence_codes hworld
  have hneg := defDiag_neg_price_tendsto Q P market p f hp0 hp1 hworld Y hq
  have hB : Tendsto (fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) atTop
      (𝓝 ((t : ℝ) * (1 - p))) := hneg.const_mul _
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpR : (p : ℝ) < 1 := by exact_mod_cast hp1
  set c : ℝ := (t : ℝ) * (1 - p) with hc
  have hcpos : 0 < c := mul_pos htR (by linarith)
  have h1 : ∀ᶠ n in atTop, (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n) ≤
      P n (defDiag (kleeneDiag T market p) f n ⋏ ∼ defDiag (kleeneDiag T market p) f n) + c / 2 :=
    h (c / 2) (by positivity)
  have h2 : ∀ᶠ n in atTop,
      P n (defDiag (kleeneDiag T market p) f n ⋏ ∼ defDiag (kleeneDiag T market p) f n) < c / 4 :=
    hfalse.eventually (gt_mem_nhds (by positivity))
  have h3 : ∀ᶠ n in atTop,
      3 * c / 4 < (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n) :=
    hB.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and h3)).exists
  linarith

/-- **Soft `=` fails below the pin.** At `p' + δ < p`, `¬ (𝔼_n(A_n) ≈ₙ p' · 𝔼_n(B_n))`: the left
side `→ p` (`product_expect_tendsto_p`), the right side `→ p'` (`confidence_expect_tendsto_one`),
and `p' < p`. The mandate's instance is `p = ½`, `p' = ¼` ("`½ ≠ ¼`").
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 026; [[li-diagonal-mandate]] T5g ("soft-`=` fails at `t = ¼`")
Kind: C
Fidelity: stronger (every `p' + δ < p`)
Hyps: (a) the `thm:st` product/confidence fields (`hA`, `hArefl`, `hB`, `hBrefl`), `hχ`, `hpres` (T5c's conclusion) -/
theorem soft_eq_schema_fails (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ) (hδ : 0 < δ)
    (hp'0 : 0 < p') (hlt : p' + δ < p) (A B : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : LUV.MachineThresholdCodeSeq A)
    (hArefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (A n) (v.payout (defDiag (kleeneDiag T market p) f n) *
        ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ)))
    (hB : LUV.MachineThresholdCodeSeq B)
    (hBrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (B n) (ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ)))
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T market p) f))
    (hpres : (fun n => P n (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ)) :
    ¬ ((fun n => (A n).expect P n) ≈ₙ fun n => (p' : ℝ) * (B n).expect P n) := by
  intro h
  obtain ⟨hAlim, hBlim, -, hlt'⟩ := soft_self_trust_nondegenerate Q P market p f hp0 hp1 δ p' hδ
    hp'0 hlt A B hworld hA hArefl hB hBrefl hχ hpres
  unfold AsympEq at h
  have huniq := tendsto_nhds_unique h (hAlim.sub hBlim)
  linarith

/-- **The 2×2 table over one `thm:st` package and one `thm:ceu` package** (trust-lab-026 made
well-posed): hard-`=` and hard-`≥` fail at every positive threshold `t`; soft-`=` fails at the
package's threshold `p'` whenever `p' + δ < p`; soft-`≥` holds (FAF's `thm:st`).
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[trust-lab-inventory]] 026 (ill-posed as stated, F-4); [[li-diagonal-mandate]] T5g
Kind: C
Fidelity: variant: the source's "maximal among all schemata" has no order on schemata; this is the verdict table (hard rows stronger than the mandate's)
Hyps: (a) `hq` (`thm:ceu` package), `hst` (`thm:st` package; both discharged over the paper market by FAF's closed forms), `hp'0`, `hlt` -/
theorem schemata_two_by_two (hp0 : 0 < p) (hp1 : p < 1) (t : ℚ) (ht : 0 < t) (δ p' : ℚ)
    (hp'0 : 0 < p') (hlt : p' + δ < p) (A B Y : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market p) f) Y)
    (hst : SelfTrustQuote P DP f (defDiag (kleeneDiag T market p) f) (fun _ => δ) (fun _ => p')
      A B) :
    ¬ ((fun n => P n (defDiag (kleeneDiag T market p) f n ⋏
          ∼ defDiag (kleeneDiag T market p) f n)) ≈ₙ
        fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) ∧
      ¬ ((fun n => P n (defDiag (kleeneDiag T market p) f n ⋏
          ∼ defDiag (kleeneDiag T market p) f n)) ≳ₙ
        fun n => (t : ℝ) * P n (∼ defDiag (kleeneDiag T market p) f n)) ∧
      ¬ ((fun n => (A n).expect P n) ≈ₙ fun n => (p' : ℝ) * (B n).expect P n) ∧
      ((fun n => (A n).expect P n) ≳ₙ fun n => (p' : ℝ) * (B n).expect P n) := by
  have hδ : 0 < δ := hst.delta_pos 0
  refine ⟨hard_eq_schema_fails Q P market p f hp0 hp1 t ht hworld Y hq,
    hard_ge_schema_fails Q P market p f hp0 hp1 t ht hworld Y hq,
    soft_eq_schema_fails Q P market p f hp0 hp1 δ p' hδ hp'0 hlt A B hworld hst.product_codes
      (fun n v hv => hst.product_reflected n v hv) hst.confidence_codes
      (fun n v hv => hst.confidence_reflected n v hv) hq.sentence_codes
      (defDiag_present_price_of_quote Q P market p f hp0 hp1 hworld Y hq),
    soft_self_trust_deferredDiagonal P market p f δ p' A B hworld hst⟩

end Schemata

end Cleanroom.Li.LiDiagonal
