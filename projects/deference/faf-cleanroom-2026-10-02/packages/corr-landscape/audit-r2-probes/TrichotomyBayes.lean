import Cleanroom.Corrigibility.CorrLandscape.Trichotomy

/-!
Audit r2 (adversarial) probe — `Trichotomy.anti_informative_worse`'s hypothesis discriminates: on Toy T's
mixed column the Bayes rule (which beats both constants) has `D_A · p_R = 7/40 > D_R · p_A = −1/40`, so
the anti-informativeness hypothesis `D_A p_R < D_R p_A` fails for it. The theorem is not "every
non-constant rule is worse than the better constant". Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape.Trichotomy

open Map Finset

theorem probe_bayes_not_anti_informative :
    DR toyMixed (bayesRule toyMixed 1 4 0) 1 4 0 = -(1 / 20) ∧
      DA toyMixed (bayesRule toyMixed 1 4 0) 1 4 0 = 7 / 20 ∧
      ¬ (DA toyMixed (bayesRule toyMixed 1 4 0) 1 4 0 * pR toyMixed (bayesRule toyMixed 1 4 0) <
          DR toyMixed (bayesRule toyMixed 1 4 0) 1 4 0 * pA toyMixed (bayesRule toyMixed 1 4 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := toyMixed_mass
  have hb1 : bayesRule toyMixed 1 4 0 true = false := by simp [bayesRule, qk, sigMass, h1, h3]; norm_num
  have hb0 : bayesRule toyMixed 1 4 0 false = true := by simp [bayesRule, qk, sigMass, h2, h4]; norm_num
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [DA, DR, pR, pA, signed, Fintype.sum_bool, hb1, hb0, qk, sigMass, h1, h2, h3, h4,
      Finset.sum_filter] <;>
    norm_num

end Cleanroom.Corrigibility.CorrLandscape.Trichotomy
