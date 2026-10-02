import Cleanroom.Decision.DpFirstpersonSc

/-!
# Audit round 3 (fidelity) probe — F7's OC/SSC clause has a false positive

F7 (after repair round 2) says SC open question 1's measure "is neither a test of
expressibility (false positives: radical label) nor a test of the OC/SSC difference (false
negatives: `B₁`, TN-V2)", and that "the measure sees the OC/SSC difference iff `occ(d)` is not
a.s. a union of observation atoms". The second sentence is about the two *leaf-level posteriors*;
read as a statement about the two *states on `Ω`* it has a false positive the package already
contains: on `blindTree'` the per-run state and the strict-OC state at `⊤` **agree as states**
(`blind'_agree`, the Dead-1 witness), yet `occ(d)` is not occurrence-expressible
(`blind'_not_occExpressible`), so by the repair-round-2 theorem `not_occExpressible_measure_fires`
the measure **fires** for the per-run posterior — relative to *every* observation structure
`obs`, in particular the trivial one — while it is silent for the strict-OC posterior at `⊤`
(`density_const_obs`). So the measure has false positives for the OC/SSC *state* difference too.

Second cell: the `radicalLabel` "fires" claim of F7/the T10(a) row is stated in the package as
`¬ OccUnionOfObsAtoms` alone; passing through `density_const_iff_occ_union` needs
`0 < μ(occ(d))`, which no package lemma discharges. It is `½` (`radicalLabel_leafLaw`), proved
here, and the `¬ JeffreyOnA` form follows.

Elaboration note (the package's documented `whnf` limit): a `¬ JeffreyOnA (runPMF C B) …
(condOn (runPMF C B) …)` statement *written out* at the concrete point/act types times out at
200000 heartbeats, exactly as the report's §Elaboration notes say for the T7(b) cells; the two
firing cells are therefore stated with their types inferred from the proof terms (`example :=`),
the form the package itself uses for `lambdaCI_compatible_model_exists` at `anThree`.

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

/-- **`blindTree'`: the per-run state and the strict-OC state at `⊤` agree** (the package's
`blind'_agree`, restated here so the two halves of the cell sit together). -/
theorem probe_blind'_states_agree :
    State.Agree (occState cfProcA blindTree' .d blind'_occ_pos)
      (calibratedState cfProcA blindTree' Finset.univ (nu_univ_pos _ _)) :=
  blind'_agree

/-- **`blindTree'`: the measure fires for the per-run posterior**, relative to every observation
structure `obs` — `¬ JeffreyOnA (runPMF cfProcA blindTree') (obsAtom obs blindTree')
(condOn (runPMF cfProcA blindTree') ↑(occ .d blindTree') _)`, the type inferred from the term. -/
example (obs : CfPt → Finset Bool) :=
  not_occExpressible_measure_fires obs cfProcA blindTree' .d blind'_occ_pos
    blind'_not_occExpressible

/-- Leaf sums on `radicalLabel` (the shape of `coverFail_sum`). -/
theorem radicalLabel_sum {M : Type} [AddCommMonoid M] (f : radicalLabel.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold radicalLabel at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `μ(occ(d)) = ½ > 0` on the radical-label tree — the guard F7's "fires" cell needs. -/
theorem probe_radicalLabel_occ_pos : 0 < Tree.mass cfUnif radicalLabel (occ .d radicalLabel) := by
  rw [mass_eq_sum_ite', radicalLabel_sum]
  simp only [mem_occ, radicalLabel_count_d, radicalLabel_leafLaw]
  simp [Fin.sum_univ_two]
  exact Fintype.card_pos

/-- **The measure fires on the radical-label tree**, in the `¬ JeffreyOnA` form (type inferred
from the term: `¬ JeffreyOnA (runPMF cfUnif radicalLabel) (obsAtom radObs radicalLabel)
(condOn (runPMF cfUnif radicalLabel) ↑(occ .d radicalLabel) _)`). -/
example :=
  fun hJ => radicalLabel_not_occUnion
    ((density_const_iff_occ_union radObs cfUnif radicalLabel .d probe_radicalLabel_occ_pos).mp hJ)

end Cleanroom.Decision.DpFirstpersonSc
