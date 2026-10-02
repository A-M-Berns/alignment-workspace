import Cleanroom.Corrigibility.CorrIndifference.Witnesses

/-!
# Audit r3 (fidelity) probe: on `MCeil`, under §2.1's cell `v_N`, the certain-press action is the
`v_N`-maximiser *and a global optimum* at `c_high = 12`.

Soares et al. §2.1 define `v_N(a₁) := U_N(a₁, ¬Pr, A₂(a₁, ¬Pr))` — a cell value, no division —
and the sentence after (10) that F2 refutes lives in §2.1; §3's `E[U_N | O ∉ Press ; a₁]` is a
later redefinition, and it is that redefinition the package's quotient `vN` renders. The
adversarial r3 probe `CellMaxGlobalOptimum.lean` proves the general statement (on `O = {Pr, ¬Pr}`
the cell-`v_N`-maximiser is a global optimum at `c_high = silentMax` for *every* press profile,
no `hq1`). This file adds the instance the round-2 witness is built on: `strict_cause_steering_twoObs`
already contains `best UNceil sure silent = 12` and `E[U ; sure] = 12`; packaged with
`EU_mixU_le_of_bound` they say `sure` — §2.1's `v_N`-maximiser — is beaten by nothing. So the
strict `11 < 12` of that witness is the mixture choosing its cell-`v_N`-maximiser (an action that
is not `v_N`-dominated in §2.1's sense), not a case where "no `v_N` attains (10)": that clause,
and F2's "in the source's own terms `v_N(a₁)` is `0/0`", hold only for §3's / the quotient
reading. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel Witnesses

/-- `sure`'s silent cell carries (10) (`12`; `star`'s is `10`), and at `c_high = 12` every action's
expected utility is at most `sure`'s: with §2.1's `v_N`, `sure` is the `v_N`-maximiser and a
global optimum, so the weak global reading of "averts any incentives" holds on this instance
although `sure` presses with certainty. -/
theorem MCeil_sure_is_cell_vN_max_and_global_optimum :
    best UNceil .sure .silent = 12 ∧ best UNceil .star .silent = 10 ∧
      ∀ a, MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} 12 0) a ≤
        MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} 12 0) .sure := by
  obtain ⟨hb, hs12, -, hsure, -⟩ := strict_cause_steering_twoObs
  refine ⟨hs12, by rw [best_UNceil]; rfl, fun a => ?_⟩
  rw [hsure]
  exact MCeil.EU_mixU_le_of_bound UNceil hSh_stop (by norm_num) hb a

end Cleanroom.Corrigibility.CorrIndifference.AuditR3
