import Cleanroom.Bli.BliMeasure.Introspective

/-!
# Audit r3 (adversarial) probe — `IntroQuoteProcess` does not say when a quote literal enters

`coherentIntrospective_open`'s adjoined process requires each true quote literal about day `m`
to be in `DP'.D n` for all large `n`, and nothing more. This probe machine-checks the first
step of the consequence audit r3 (fidelity) N4 describes: if the literal about `(m, φ, lo, hi)`
has already entered `DP'` by a day `n` on which the atom (and its negation) is small, then the
base's day-`n` price of the quote atom is `0` or `1` — so for `n < m` the conjecture's equation
would force the whole day-`n` superbelief mass on the day-`m` candidates to sit on one side of
`(lo, hi]`, for every interval: every charged candidate would have to agree with `𝐐_m(φ)` on
`φ`. The existential over `DP'` lets a prover avoid this by entering the literal at or after
day `m`; the statement does not say so.

Not imported by the library.
-/

namespace Cleanroom.Bli.BliMeasure.AuditR3

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliMeasure

/-- The marginal of a negation. -/
lemma wMarginal_neg {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    wMarginal w (∼φ) = ∑ u, w u - wMarginal w φ := by
  unfold wMarginal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [payoutRat_eq_ite, payoutRat_eq_ite]
  by_cases h : (worldOf u).Holds φ
  · have hn : ¬ (worldOf u).Holds (∼φ) := by rw [PCWorld.holds_neg]; exact not_not.mpr h
    rw [if_pos h, if_neg hn]; ring
  · have hn : (worldOf u).Holds (∼φ) := by rw [PCWorld.holds_neg]; exact h
    rw [if_neg h, if_pos hn]; ring

/-- Early entry pins the base's price of the quote atom to `{0, 1}` on every day on which the
atom and its negation are small. -/
theorem Q_introQuote_zero_or_one {DP DP' : DeductiveProcess} {base : CoherentBase DP'}
    (_h : IntroQuoteProcess DP DP' base) (m : ℕ) (φ : Sentence) (lo hi : ℚ) (n : ℕ)
    (hsmall : introQuote m φ lo hi ∈ smallSet n)
    (hsmall' : ∼introQuote m φ lo hi ∈ smallSet n)
    (hin : introQuoteLit base m φ lo hi ∈ DP'.D n) :
    base.Q n (introQuote m φ lo hi) = 0 ∨ base.Q n (introQuote m φ lo hi) = 1 := by
  unfold introQuoteLit at hin
  split_ifs at hin with hc
  · right
    exact base.Q_eq_one_of_mem n hsmall hin
  · left
    have h1 := base.Q_eq_one_of_mem n hsmall' hin
    rw [base.Q_eq n _ hsmall', wMarginal_neg, base.w_sum] at h1
    rw [base.Q_eq n _ hsmall]
    linarith

end Cleanroom.Bli.BliMeasure.AuditR3
