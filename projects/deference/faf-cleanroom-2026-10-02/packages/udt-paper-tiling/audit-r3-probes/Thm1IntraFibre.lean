import Cleanroom.Udt.UdtPaperTiling.Theorem2Witness

/-!
Audit round 3, adversarial lens — probe for Theorem 1's witness of record (T3, load-bearing 1).

The ledger's N+ witness for `thm1_udt11_tiling` / `thm1_no_strict_selfMod` is
`Thm1Wit4.thm1_on_prior4`, where `U4 = f(pp)`: Policy Fairness holds because the utility is a
function of the effective policy, so `procEU π = f(eff π) = procEU (eff π)` holds on that model
*without* Policy Fairness — the hypothesis is not what produces the conclusion there (round 2's
N3). The row points to `Thm2Six.intra_fibre_variance` for a PF witness with intra-fibre variance,
but no Theorem 1 instance is stated on `Thm2Six`. This probe states it: `Thm2Six.Λ` satisfies
Theorem 1's full package (`PolicyFair`, `eff9` idempotent / non-modifying / type-preserving over
`S9z`, every well-typed policy positive) with `U ≠ f(pp)` and `U ≠ f(chosen)`, and Theorem 1's
identity holds on the modifying policy `(m,x)` (worlds of utility `5` and `15`, mean `10`, equal
to `procEU (x,y) = 10`). Cheap to lift. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtPaperTiling.AuditR3Adv

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset CoordWit Thm2Tie Thm2Six

/-- `eff9` is non-modifying over `S9z` (same `𝒜^m = {m}` as `S9`). -/
theorem eff9_nonMod_z (π : Policy twoTables (Fin 4)) : S9z.NonMod (eff9 π) :=
  fun T => eff9_nonMod π T

/-- `eff9` preserves `S9z`-well-typedness. -/
theorem eff9_wellTyped_z (π : Policy twoTables (Fin 4)) (h : S9z.WellTyped π) :
    S9z.WellTyped (eff9 π) := by
  rw [wellTyped_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [eq_pol π, eff9_pol, pol_T1, pol_T2]
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h1, h2, Thm2Six.g01, Thm2Six.g02, Thm2Six.g03, Thm2Six.g12, Thm2Six.g13, Thm2Six.g23,
      Thm2Six.g01.symm, Thm2Six.g02.symm, Thm2Six.g03.symm, Thm2Six.g12.symm, Thm2Six.g13.symm,
      Thm2Six.g23.symm]

/-- **Theorem 1's full package on the intra-fibre-variance model, and its conclusion.** -/
theorem thm1_full_package_intra_fibre :
    (prior.PolicyFair Λ.toProcLayer ∧ (∀ π, S9z.WellTyped π → 0 < Λ.procMass π) ∧
      (∀ π, Λ.eff (Λ.eff π) = Λ.eff π) ∧ (∀ π, S9z.NonMod (Λ.eff π)) ∧
      (∀ π, S9z.WellTyped π → S9z.WellTyped (Λ.eff π))) ∧
    (prior.pp (0, 2) = prior.pp (1, 2) ∧ Λ.chosen (0, 2) = Λ.chosen (1, 2) ∧
      prior.U (0, 2) ≠ prior.U (1, 2)) ∧
    ¬ ∃ π, S9z.WellTyped π ∧ ¬ S9z.NonMod π ∧
      ∀ π', S9z.WellTyped π' → S9z.NonMod π' → Λ.procEU π' < Λ.procEU π :=
  ⟨⟨policyFair, ndproc, eff9_idem, eff9_nonMod_z, eff9_wellTyped_z⟩, intra_fibre_variance,
    thm1_no_strict_selfMod S9z Λ policyFair eff9_idem eff9_nonMod_z eff9_wellTyped_z ndproc⟩

/-- **Theorem 1's identity on the modifying policy `(m,x)`**: `procEU (m,x) = procEU (eff (m,x))
= procEU (x,y)`, both `10`, with `U` taking `5` and `15` inside the `(m,x)` fibre. -/
theorem thm1_identity_on_mx :
    Λ.procEU (pol 2 0) = Λ.procEU (Λ.eff (pol 2 0)) ∧ Λ.procEU (pol 2 0) = 10 ∧
    Λ.eff (pol 2 0) = pol 0 1 := by
  have hwt : S9z.WellTyped (pol 2 0) := (wellTyped_iff _).mpr (by simp)
  obtain ⟨_, _, v20, _, _, _⟩ := procEU
  refine ⟨thm1_udt11_tiling Λ policyFair (pol 2 0) (eff9_idem _) (ndproc _ hwt)
    (ndproc _ (eff9_wellTyped_z _ hwt)), v20, ?_⟩
  simp [Λ, eff9_pol]

end Cleanroom.Udt.UdtPaperTiling.AuditR3Adv
