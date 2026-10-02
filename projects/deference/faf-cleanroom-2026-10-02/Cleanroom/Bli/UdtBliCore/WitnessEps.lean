import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-bli-core` · WitnessEps: the ε-form of the updateful-behaviour lemma exercised at `ε > 0`
(repair round 1; audit r1 adversarial N3)

The package's only witness for `eps_updateful` was the tent prior at `ε = 0`, which exercises
none of the approximate content. Here: `epsPrior`, a two-table prior whose point at `T1` is
slightly correlated with the state (`branchProb T1 T1 true = 13/25`, `false = 12/25`, so
`ε = 1/25`), no cross-branch utility (`U = 0` on `T2`), home values `1` (`true`) and `21/20`
(`false`). The one-step rule picks `true` (`13/25 > 63/125`), the updateful rule picks `false`
(`21/20 > 1`), the updateful regret of the one-step choice is `1/20`, and `eps_updateful` bounds
it by `δ = (1/25)(1 + 5·21/20)/(13/25) = 25/52`. The bound is loose (`1/20 ≤ 25/52`), as F-10
says of the constant.

Promoted from the audit's probe `audit-r1-probes/EpsWitness.lean`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-- Masses on `(state, point at T1)`: `13/50` on the diagonal, `12/50` off it.
Source: none: infrastructure (an ε-reflective law, `ε = 1/25`)
Kind: D
Fidelity: n/a -/
def epsMass : Fin 2 × Bool → ℚ := fun ω =>
  if (ω.1 = 0) = (ω.2 = true) then 13 / 50 else 12 / 50

/-- Utility: `1` for `true`, `21/20` for `false` on `T1`; `0` on `T2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def epsU : Fin 2 × Bool → ℚ := fun ω =>
  if ω.1 = 0 then (if ω.2 then 1 else 21 / 20) else 0

/-- **The ε-prior**: the point at `T1` is the single coordinate `ω.2` (both tables read it), the
state is `ε`-correlated with it.
Source: bli-slides-037 ("significantly"); mandate T5 (the ε-form); audit r1 adversarial N3
Kind: D
Fidelity: exact (an inhabitant of `eps_updateful`'s package with `ε = 1/25 > 0`) -/
def epsPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool) epsMass
    (fun ω => by unfold epsMass; split_ifs <;> norm_num)
    (by unfold epsMass; simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]; norm_num)
    (fun ω => twoState ω.1) two_zeroOne (fun ω _ => ω.2) epsU

namespace Eps

/-- The point masses at `T1` are `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_T1 (c : Bool) : epsPrior.ppMass T1 c = 1 / 2 := by
  unfold FiniteBLIPrior.ppMass epsPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  cases c <;> norm_num [massOf, epsMass, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fintype.sum_bool]

/-- The branch probabilities given the point at `T1`: `13/25` on the diagonal, `12/25` off it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_eq (T' : ↥twoTables) (c : Bool) :
    epsPrior.branchProb T' T1 c = if (T' = T1) = (c = true) then 13 / 25 else 12 / 25 := by
  rcases eq_T1_or_T2 T' with rfl | rfl <;> cases c <;>
  · unfold FiniteBLIPrior.branchProb FiniteBLIPrior.jointMass FiniteBLIPrior.ppMass epsPrior
    rw [handPrior_massOf, handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, epsMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- No cross-branch utility: `T2`'s value is `0` under either point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_T2 (c : Bool) : epsPrior.condEU T2 T1 c = 0 := by
  cases c <;>
  · unfold FiniteBLIPrior.condEU epsPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, epsMass, epsU, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- The home values at `T1`: `1` (`true`), `21/20` (`false`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma homeEU_T1 (a : Bool) : epsPrior.homeEU T1 a = if a then 1 else 21 / 20 := by
  cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU epsPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, epsMass, epsU, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- The one-step values at `T1`: `13/25` (`true`), `63/125` (`false`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_T1 (a : Bool) : epsPrior.EU T1 a = if a then 13 / 25 else 63 / 125 := by
  cases a <;>
  · unfold FiniteBLIPrior.EU epsPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, epsMass, epsU, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- `|U| ≤ 21/20`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma absU_le (ω : Fin 2 × Bool) : |epsPrior.U ω| ≤ 21 / 20 := by
  rcases ω with ⟨s, b⟩
  show |epsU (s, b)| ≤ 21 / 20
  match s, b with
  | 0, true => norm_num [epsU]
  | 0, false => norm_num [epsU]
  | 1, true => norm_num [epsU]
  | 1, false => norm_num [epsU]

/-- `|twoTables| = 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma card_twoTables : Fintype.card ↥twoTables = 2 := by
  rw [← Finset.card_univ, univ_twoTables, Finset.card_pair T1_ne_T2]

/-- **The ε-form exercised at `ε = 1/25`**: the rules separate (one-step `true`, updateful
`false`), the updateful regret of the one-step choice is `1/20`, and `eps_updateful` bounds it by
`δ = (1/25)(1 + (2·2 + 1)·21/20)/(13/25) = 25/52`. The N+ for the ε-form (the tent prior is its
`ε = 0` instance). What it exercises: the **re-weighting** half of the hypotheses (`hbp`, the
branch probabilities differ by `ε = 1/25`); the **cross-utility** half (`hcross`) is inhabited
with slack `0`, since `U = 0` on `T2` (`condEU_T2`) — that ε is not exercised here (audit r2
fidelity non-blocking 2, adversarial N3). Also: both tables read one coordinate, so the prior is
neither `NDPOLICY` nor `IndependentPoints`; `eps_updateful` needs neither.
Source: bli-slides-037 ("significantly"); mandate T5; finding F-10; audit r1 adversarial N3
Kind: N+
Fidelity: exact (the theorem's package inhabited with `ε > 0` in the re-weighting clause and
slack `0` in the cross-utility clause, and its bound evaluated)
Hyps: (a) none -/
theorem eps_instance :
    epsPrior.IsOneStepChoice T1 true ∧ ¬ epsPrior.IsUpdatefulChoice T1 true ∧
      epsPrior.homeEU T1 false - epsPrior.homeEU T1 true = 1 / 20 ∧
      epsPrior.homeEU T1 false - epsPrior.homeEU T1 true ≤
        1 / 25 * (1 + (2 * (Fintype.card ↥twoTables : ℚ) + 1) * (21 / 20)) / (13 / 25) ∧
      (1 / 25 * (1 + (2 * (Fintype.card ↥twoTables : ℚ) + 1) * (21 / 20)) / (13 / 25) : ℚ) =
        25 / 52 := by
  have hstar : epsPrior.IsOneStepChoice T1 true := by
    intro b; rw [EU_T1, EU_T1]; cases b <;> norm_num
  have hbp : ∀ T' c d, |epsPrior.branchProb T' T1 c - epsPrior.branchProb T' T1 d| ≤ 1 / 25 := by
    intro T' c d
    rw [branchProb_eq, branchProb_eq]
    rcases eq_T1_or_T2 T' with rfl | rfl <;> cases c <;> cases d <;>
      norm_num [T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, abs_le]
  have hcross : ∀ T' c d, T' ≠ T1 → 0 < epsPrior.jointMass T' T1 c →
      0 < epsPrior.jointMass T' T1 d →
      |epsPrior.condEU T' T1 c - epsPrior.condEU T' T1 d| ≤ 1 / 25 := by
    intro T' c d hne _ _
    rcases eq_T1_or_T2 T' with rfl | rfl
    · exact absurd rfl hne
    · rw [condEU_T2, condEU_T2]; norm_num
  have hbound := epsPrior.eps_updateful T1 (1 / 25) (21 / 20) (13 / 25) (by norm_num) (by norm_num)
    (by norm_num) (fun c => by rw [ppMass_T1]; norm_num) hbp hcross absU_le true hstar
    (by rw [branchProb_eq]; norm_num) false
  refine ⟨hstar, fun h => ?_, ?_, hbound, ?_⟩
  · have := h false; rw [homeEU_T1, homeEU_T1] at this; norm_num at this
  · rw [homeEU_T1, homeEU_T1]; norm_num
  · rw [card_twoTables]; norm_num

end Eps

end Cleanroom.Bli.UdtBliCore
