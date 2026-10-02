import Cleanroom.Corrigibility.CorrIndifference.Witnesses

/-!
# Audit r3 (adversarial) probe — `vNmax_is_global_optimum`'s `ha₀` is a domain guard, not
decoration

The theorem's proof does not consult `ha₀ : pressMass a₀ < 1` (docstring: "named and unused").
Without it, the same two lemmas certify a certain-press action whose `vN` is the junk `0` as
"the `vN`-maximiser and global optimum at the corrected ceiling": on `Witnesses.MCert`
(`sure` presses w.p. `1`, `quiet` never, `U_N ≡ −5`), `hM` holds for `a₀ = sure` (the only
silent-capable action has `vN(quiet) = −5 ≤ 0 = vN(sure)`), and at `c_high = vN(sure) = 0`,
`c_low = −1`, every action is `≤ EU(sure) = 0` while `EU(quiet) = −5`. So the guard is exactly
what keeps the statement about the conditional value it names (the r1 B-2 pattern); the ledger's
"named, unused: the domain on which `vN(a₀)` is the conditional value" is right. Not imported
by the library.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel Witnesses

theorem junk_guard :
    (∀ a, MCert.pressMass a < 1 → MCert.vN UNneg a ≤ MCert.vN UNneg .sure) ∧
    (∀ a, MCert.EU (MCert.mixU UNneg {TwoAct.stop} (MCert.vN UNneg .sure) (-1)) a ≤
        MCert.EU (MCert.mixU UNneg {TwoAct.stop} (MCert.vN UNneg .sure) (-1)) .sure) ∧
    MCert.EU (MCert.mixU UNneg {TwoAct.stop} (MCert.vN UNneg .sure) (-1)) .quiet = -5 ∧
    MCert.EU (MCert.mixU UNneg {TwoAct.stop} (MCert.vN UNneg .sure) (-1)) .sure = 0 := by
  obtain ⟨h1, h2, -⟩ := certainPress_junk (fun _ _ _ => 0)
  have hM : ∀ a, MCert.pressMass a < 1 → MCert.vN UNneg a ≤ MCert.vN UNneg .sure := by
    intro a _
    cases a
    · exact le_rfl
    · rw [h1, h2]; norm_num
  have hc : (-1 : ℝ) < MCert.vN UNneg .sure := by rw [h1]; norm_num
  have hsure : MCert.pressMass .sure = 1 := by rw [MCert_pressMass]; rfl
  refine ⟨hM, fun a => ?_, ?_, ?_⟩
  · rw [MCert.EU_mixU_eq_of_vN_eq UNneg hSh_stop hc rfl]
    exact MCert.EU_mixU_le_of_vN_bound UNneg hSh_stop hc hM a
  · rw [MCert.EU_mixU_equal_value UNneg hSh_stop hc, h1, h2, MCert_pressMass]
    simp only [qCert]; norm_num
  · exact (MCert.EU_mixU_eq_of_press_one UNneg hSh_stop hc hsure).trans h1

end Cleanroom.Corrigibility.CorrIndifference.AuditR3
