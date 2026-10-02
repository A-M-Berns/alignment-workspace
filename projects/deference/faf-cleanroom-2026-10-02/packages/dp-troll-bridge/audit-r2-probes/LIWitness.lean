/-
  Audit round 2, adversarial lens: LI-level probes against `dp-troll-bridge` after repair
  round 1 (`LILesion.lean`, `FlowerLI.lean`).

  Not imported by the library. Elaborated with `scripts/lean-check`. The audit file
  `dp-troll-bridge-audit-r2-adversarial.md` reads the results.

  Probes:
  1. Target 10's hypothesis package (`hthm` + the two code hypotheses) has a non-degenerate
     inhabitant: `cross n := incon n ⋏ χ n` for any codeable `incon`, `χ`. The ledger's
     Witness column says `n/a` for the four target-10 rows; this is what should be there
     (modulo FAF's own inductor, which FAF constructs under `Construction/`).
  2. The OPEN statement `li_responsive_lesion_open` has a degenerate inhabitant of its whole
     hypothesis package — the never-crossing agent `cross := ⊥`, `incon := ⊥` — for which the
     conclusion holds for the trivial reason, under two extra assumptions on the instance
     (`P n ⊥ = 0` every day; a completed-theory world exists). This confirms, kernel-checked,
     the ledger's caveat that the junk value sits on the satisfying side, and shows the
     package is not empty for a trivial reason.
  3. `flower_liminf_of_portfolio`: (a) `hrefl` at `ψ := ⊥` is FAF's `diagonal_reflected`
     shape; (b) `hvalue` subsumes `port.current_price`; (c) without `hrefl`, `port` + `hvalue`
     do NOT give `theory_coherent` — at any world falsifying `S n` the value is
     `scale · gate`, positive whenever the gate fires. So `hrefl` is load-bearing (no
     squeeze), and the hypothesis package is FAF's `gatedComplementAffine` value law
     (`Construction/Quotation/Packages.lean:712`), which FAF's
     `paradoxResistanceQuoteOfDiagonal` builds for the diagonal sentence.
-/

import Cleanroom.Decision.DpTrollBridge.LILesion
import Cleanroom.Decision.DpTrollBridge.FlowerLI

open LO
open LogicalInduction
open scoped LogicalInduction
open Filter Topology

namespace Cleanroom.Decision.DpTrollBridge.AuditR2

/-! ## Probe 1: a non-degenerate inhabitant of target 10's hypothesis package -/

/-- `cross n := incon n ⋏ χ n` satisfies the lesion hypothesis `hthm` in every world, for
every deductive process. -/
theorem lesion_hyp_of_conj (DP : DeductiveProcess) (incon χ : ℕ → Sentence) :
    ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.Holds ((incon n ⋏ χ n) 🡒 incon n) := by
  intro n v _
  rw [holds_imp]
  intro h
  exact ((PCWorld.holds_and v _ _).mp h).1

/-- Its codes are FAF's `MachineSentenceCodes.and`. -/
theorem lesion_codes_of_conj (incon χ : ℕ → Sentence)
    (hi : MachineSentenceCodes incon) (hχ : MachineSentenceCodes χ) :
    MachineSentenceCodes (fun n => incon n ⋏ χ n) :=
  hi.and hχ

/-- The target-10 composite, instantiated: for any inductor and any codeable `incon`, `χ`,
eventually on days with `P n (incon n ⋏ χ n) ≥ ε`, `P_n(incon n | incon n ⋏ χ n) ≥ 1 − δ`.
A genuine coherence fact, not a constant-sequence instance. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (incon χ : ℕ → Sentence) (hi : MachineSentenceCodes incon) (hχ : MachineSentenceCodes χ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ε ≤ P n (incon n ⋏ χ n) →
      1 - δ ≤ conditionalQuote (P n) (incon n) (incon n ⋏ χ n) :=
  li_lesion_conditional_of_theory P DP (fun n => incon n ⋏ χ n) incon
    (lesion_codes_of_conj incon χ hi hχ) hi (lesion_hyp_of_conj DP incon χ) hworld ε hε δ hδ

/-! ## Probe 2: a degenerate inhabitant of the OPEN statement's hypothesis package -/

/-- `v.Holds ⊥` is `False`. -/
lemma holds_bot (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := fun h => h

/-- The never-crossing agent `cross := ⊥`, `incon := ⊥` inhabits the whole hypothesis
package of `li_responsive_lesion_open` — `hβ`, `hcon`, `hworld`, both code hypotheses — given
an inductor with `P n ⊥ = 0` on every day and a completed-theory world, and the conclusion
then holds for the trivial reason (`⊥ 🡒 ⊥`). The capped quote is `1` on the `else` branch
(`P n (⊥ ⋏ ⊥) < 0` is impossible), so the rule says "stay" every day: the junk-value side. -/
theorem responsive_open_never_crosser (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hbot : ∀ n, P n (⊥ : Sentence) = 0) (hcw : ∃ v : PCWorld, v.ConsistentWithTheory DP) :
    MachineSentenceCodes (fun _ : ℕ => (⊥ : Sentence)) ∧
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (v.Holds (⊥ : Sentence) ↔
        0 < 10 - 20 * conditionalQuote (P n) (⊥ : Sentence) (⊥ : Sentence))) ∧
    (∀ _n : ℕ, ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (⊥ : Sentence)) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
    (∀ᶠ n : ℕ in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.Holds ((⊥ : Sentence) 🡒 ⊥)) := by
  obtain ⟨v₀, hv₀⟩ := hcw
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hq : ∀ n, conditionalQuote (P n) (⊥ : Sentence) (⊥ : Sentence) = 1 := by
    intro n
    apply conditionalQuote_eq_one
    rw [hbot n]
    exact (hP n _).1
  refine ⟨MachineSentenceCodes.const ⊥, ?_, ?_, ?_, ?_⟩
  · intro n v _
    rw [hq n]
    constructor
    · intro h; exact absurd h (holds_bot v)
    · intro h; linarith
  · intro _; exact ⟨v₀, hv₀, holds_bot v₀⟩
  · intro n; exact ⟨v₀, hv₀ n⟩
  · exact Filter.Eventually.of_forall (fun _ v _ => (holds_imp v _ _).mpr (fun h => h))

/-! ## Probe 3: the flower hypothesis package -/

/-- (a) `hrefl` at `ψ := ⊥` is FAF's `diagonal_reflected` shape: `S n ↔ P n (S n) < p`. -/
example (P : History) (p : ℚ) (S : ℕ → Sentence) (n : ℕ) (v : PCWorld) :
    (v.Holds (S n) ↔ ((p : ℝ) ≤ P n (S n) → v.Holds (⊥ : Sentence))) ↔
      (v.Holds (S n) ↔ P n (S n) < (p : ℝ)) := by
  have : ¬ v.Holds (⊥ : Sentence) := holds_bot v
  simp [this, not_le]

/-- (b) `hvalue` subsumes `port.current_price`: the value law at `w := P n` is the day-`n`
price identity. -/
example (P : History) (p : ℚ) (S : ℕ → Sentence) (width : ℕ → ℚ)
    (port : AffineQuotePortfolio P
      (fun n => ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - P n (S n))))
    (hvalue : ∀ n (w : Valuation), (port.family n).value P w =
      (port.scale : ℝ) * (ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - w (S n)))) (n : ℕ) :
    (port.family n).price P n =
      (port.scale : ℝ) * (ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - P n (S n))) := by
  rw [AffineCombination.price, hvalue]

/-- (c) Without `hrefl`, `port` + `hvalue` do not give `theory_coherent`: at any world
falsifying `S n`, the portfolio's value is `scale · gate`. -/
theorem flower_value_at_refuting_world (P : History) (p : ℚ) (S : ℕ → Sentence)
    (width : ℕ → ℚ)
    (port : AffineQuotePortfolio P
      (fun n => ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - P n (S n))))
    (hvalue : ∀ n (w : Valuation), (port.family n).value P w =
      (port.scale : ℝ) * (ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - w (S n))))
    (n : ℕ) (v : PCWorld) (hv : ¬ v.Holds (S n)) :
    (port.family n).value P v.payout = (port.scale : ℝ) * ctsInd (width n) (p : ℝ) (P n (S n)) := by
  rw [hvalue]
  simp [PCWorld.payout, hv]

/-- So when the gate fires (`P n (S n) ≤ p − width n`) that value is `scale > 0`: the
coherence field genuinely needs every completed-theory world to hold `S n` below the
threshold, which is what `hrefl` supplies. -/
example (P : History) (p : ℚ) (S : ℕ → Sentence) (width : ℕ → ℚ) (hwidth_pos : ∀ n, 0 < width n)
    (port : AffineQuotePortfolio P
      (fun n => ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - P n (S n))))
    (hvalue : ∀ n (w : Valuation), (port.family n).value P w =
      (port.scale : ℝ) * (ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - w (S n))))
    (n : ℕ) (v : PCWorld) (hv : ¬ v.Holds (S n))
    (hgate : (width n : ℝ) ≤ (p : ℝ) - P n (S n)) :
    0 < (port.family n).value P v.payout := by
  rw [flower_value_at_refuting_world P p S width port hvalue n v hv,
    ctsInd_eq_one_of_le_sub (width n) (p : ℝ) (P n (S n)) (hwidth_pos n) hgate, mul_one]
  exact_mod_cast port.scale_pos

end Cleanroom.Decision.DpTrollBridge.AuditR2
