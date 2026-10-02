import Cleanroom.Corrigibility.CorrCautionPower.Delegation

/-!
Audit r2 (adversarial) probe for `corr-caution-power` T8(a), the round-1 repair `s12_refuted_d8`.
Its ledger row says the trigger's second clause `P_t(c_ω(a) > λ) ≥ η′` is "moot since the first
never holds". Two checks on `s12State` with the intended action `b = 2`:

1. the *develop's own* D8 delegation clause (`caution.md` l. 49: delegate when `ĉ_t(a) > η` and
   `a` is irreversible) does not fire either — `ĉ(b) = 1/16 ≤ 1/4 = η`;
2. S12's second clause is **not** empty on its own: for every `0 ≤ λ < 1/4` the posterior
   probability that `b` is harmful is `P(ω*) = 1/4` — the trigger is silent only because the
   clause is conjoined with non-reversibility (which a single-state world never violates).

So the "moot" remark is right for the conjunction the source writes, and would be wrong for a
disjunctive reading. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-- D8's own delegation clause does not fire on `b`: `ĉ(b) = 1/16 ≤ η = 1/4`. -/
theorem s12State_estHarm_b_le_eta : s12State.estHarm 2 ≤ 1 / 4 := by
  rw [s12State_estHarm]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The harm of `b` under `ω*` is `1/4` (it is `trueHarm 2`). -/
lemma s12State_harm_target_b : s12State.harm 0 2 = 1 / 4 := by
  have : s12State.harm 0 2 = s12State.trueHarm 2 := rfl
  rw [this, s12State_trueHarm]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The harm of `b` under `ω′` is `0` (`b` is `ω′`-optimal). -/
lemma s12State_harm_other_b : s12State.harm 1 2 = 0 := by
  simp [CautionState.harm, harmOf, s12State, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  norm_num

/-- S12's second trigger clause is not empty: `P(c_ω(b) > λ) = P(ω*) = 1/4` for `0 ≤ λ < 1/4`. -/
theorem s12State_prob_harm_b (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1 / 4) :
    expect s12State.P (fun ω => if lam < s12State.harm ω 2 then (1 : ℝ) else 0) = 1 / 4 := by
  rw [expect_fin2, s12State_harm_target_b, s12State_harm_other_b, if_pos h1,
    if_neg (not_lt.mpr h0)]
  simp [s12State]; norm_num

end Cleanroom.Corrigibility.CorrCautionPower.AuditR2
