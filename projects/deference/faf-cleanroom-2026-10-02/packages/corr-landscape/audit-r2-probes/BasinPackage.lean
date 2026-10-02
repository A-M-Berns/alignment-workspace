import Cleanroom.Corrigibility.CorrLandscape.TwoRound

/-!
Audit r2 (adversarial) probe — the full hypothesis packages of `BasinToy.basin_forwardInvariant` and
`TwoRound.phi_isSupermart` are inhabited at the worked numbers on the worked law.

The ledger says this in prose ("the hypotheses are inhabited by `rho_worked`'s law and
`worked_condition`") but no library declaration assembles it. Here: `η = 1/2`, `r = 1`, `ξ̄ = 1/20`,
`σ̄* = 1/50`, `d_0 = 1/2` (the source's start), the joint three-point law. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory BasinToy

theorem probe_basin_package (T : ℕ) :
    forwardInvariantWithHazard (prodLaw T jointLaw) (prefixAtoms T)
      (insideEvents (1 / 2) 1 ((1 / 2 : ℝ), (0 : ℝ)) (xiOf (1 / 20)) (deltaOf (1 / 50)) T) (fun _ => 0) :=
  basin_forwardInvariant (1 / 2) 1 (1 / 20) (1 / 50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    jointLaw _ _ rho_worked.2.1 rho_worked.2.2 (by norm_num) _ T

theorem probe_tworound_package :
    IsSupermart (prod2 jointLaw jointLaw) TwoRound.atoms2
      (TwoRound.Phi (1 / 2) 1 ((1 / 2 : ℝ), (0 : ℝ)) (xiOf (1 / 20)) (deltaOf (1 / 50))
        (rhoDagger (1 / 2) jointLaw (xiOf (1 / 20)) (deltaOf (1 / 50)))) :=
  TwoRound.phi_isSupermart (1 / 2) 1 (1 / 20) (1 / 50) (by norm_num) (by norm_num) jointLaw _ _
    rho_worked.2.1 rho_worked.2.2 (by norm_num) _
    (by show |(1 / 2 : ℝ) - 0| < 1; rw [sub_zero, abs_of_nonneg (by norm_num)]; norm_num)

end Cleanroom.Corrigibility.CorrLandscape
