import Cleanroom.Bli.UdtBliTiling.Refreeze

/-!
# Audit r1 (adversarial) probe · Vacuity: the single-coin tiling headlines without their
positivity hypotheses

Checks that `hγ : ∀ k, 0 < γ k` and `hg : 0 < gain p` are load-bearing in `SingleCoin`'s
headlines (`noStrictPrecommit_iff_payOnAsk`, `refreeze_dilemma`, `stability_*`): with zero round
weights, or with `gain = 0` (the coin prior exactly at the threshold `V/(V+c)`), **every** policy
has `NoStrictPrecommit` and is prior-optimal — including every `refrozen t` — so the predicate
is trivial on the model there. The headlines exclude both by hypothesis; this probe records that
the exclusion is what gives them content. Not imported by the library.
-/

namespace Cleanroom.Bli.UdtBliTiling.AuditR1

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist Finset
open Cleanroom.Bli.UdtBliSist.Iter SingleCoin

variable {K : ℕ} (p : Params K)

/-- With zero round weights every policy ties on `scPrior p`: tiling is trivial. -/
theorem noStrictPrecommit_all_of_zero_weights (hγ : ∀ k, p.γ k = 0)
    (π : Policy (iterTables K) Bool) :
    NoStrictPrecommit (scPrior p) π ∧ (scPrior p).IsPriorOptimal π := by
  have hrs : ∀ π' : Policy (iterTables K) Bool, roundSum p.γ π' = 0 := by
    intro π'; unfold roundSum; simp [hγ]
  have hopt : (scPrior p).IsPriorOptimal π := by
    intro π'; rw [exAnteValue_eq, exAnteValue_eq, hrs, hrs]
  exact ⟨noStrictPrecommit_of_priorOptimal (structure_facts p).1 hopt, hopt⟩

/-- With `gain = 0` every policy ties too, whatever the weights. -/
theorem noStrictPrecommit_all_of_gain_zero (hg : gain p = 0) (π : Policy (iterTables K) Bool) :
    NoStrictPrecommit (scPrior p) π ∧ (scPrior p).IsPriorOptimal π := by
  have hopt : (scPrior p).IsPriorOptimal π := by
    intro π'; rw [exAnteValue_eq, exAnteValue_eq, hg]; simp
  exact ⟨noStrictPrecommit_of_priorOptimal (structure_facts p).1 hopt, hopt⟩

/-- In particular every re-frozen policy then tiles at every `t`: the dilemma's `hg` (strict) is
exactly what excludes this. -/
theorem refrozen_tiles_of_gain_zero (hg : gain p = 0) (t : ℕ) :
    NoStrictPrecommit (scPrior p) (refrozen t) :=
  (noStrictPrecommit_all_of_gain_zero p hg _).1

/-- `gain = 0` is attained: at `q = V/(V+c)` exactly (positive stakes), the threshold case. -/
theorem gain_zero_at_threshold (hc : 0 < p.c) (hV : 0 < p.V) (hq : p.q = p.V / (p.V + p.c)) :
    gain p = 0 := by
  unfold gain
  rw [hq]
  have hne : p.V + p.c ≠ 0 := by linarith
  field_simp
  ring

end Cleanroom.Bli.UdtBliTiling.AuditR1
