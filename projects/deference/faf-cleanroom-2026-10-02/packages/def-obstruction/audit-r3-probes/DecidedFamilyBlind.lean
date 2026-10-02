import Cleanroom.Deference.DefObstruction.BlindWitness

/-!
# Audit r3 (fidelity) probe: on a decided quote-free e.c. family the advised reader's credence is
asymptotically table-independent

Not imported by the library. One claim.

Two FAF LIAs over the same stronger base `paperAdjoin` and next-day publication, one recording the
alternating table (`adjPair`, the package's), one the constant-`½` table (`adjHalfPair`, here). On
the benign family `obsFamily` — decided in the base at stage `0`, parity-dispatched, so its
true/false split is e.c. — both readers' day-`(n+1)` expectations tend to the truth value, hence
the two credence streams are asymptotically equal (`obsFamily_credence_table_independent`):
settlement-blind in the `≈ₙ` sense, for two different tables.

Sharpens findings F-Dichotomy (iii): the source's "`Y_n = H⁺_{F(n)}(P^{(n)})` depends on `A`'s run
through the ledger `H⁺` has absorbed by `F(n)`, *whatever `P^{(n)}` is*"
([[self-referential-settlement-target]] §2.5) can hold at most for undecided families or for exact
finite-day values; on decided quote-free families with an e.c. split the criterion fixes the
asymptotic credence independently of the table (`lic_provind` through `thm:ei`), so there the
credence reading of blindness *agrees* with the Lean's truth-value reading. The two senses part
only on the undecided fragment.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-- The constant-`½` pair over the stronger base `paperAdjoin` (the sibling of `adjPair` with the
table swapped). -/
noncomputable def adjHalfPair : TablePair :=
  TablePair.ofLIA paperAdjoin paperAdjoin_computable aHalf aHalf_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable
    (paperAdjoin_freeOf_ledger _ _) paperAdjoin_hworld aHalf_range

/-- The two tables differ (day `0`: `0` vs `½`). -/
theorem adjPair_adjHalfPair_tables_differ : adjPair.a 0 0 ≠ adjHalfPair.a 0 0 := by
  show aAlt 0 0 ≠ aHalf 0 0
  norm_num [aAlt, aHalf]

/-- The truth indicator of the benign family: `0` on even days (`∼obsAtom`, false), `1` on odd
days (`obsAtom`, true). -/
noncomputable def obsTruth (n : ℕ) : ℝ := if n % 2 = 0 then 0 else 1

/-- Over any table-only pair whose process decides `obsAtom` true at some stage, the day-`(n+1)`
expectation of the benign family tends to its truth value — the table enters nowhere. (The proof
is `adjPair_tracks_obsFamily`'s with the table replaced by the truth indicator.) -/
theorem obsFamily_expect_tendsto_truth (T : TablePair) (hdec : DecidedTrueAt T.process obsAtom) :
    Tendsto (fun n => (LUV.indicatorOf (obsFamily n)).expect T.H (n + 1) - obsTruth n)
      atTop (𝓝 0) := by
  haveI := T.H_inductor
  have hneg : DecidedFalseAt T.process (∼ obsAtom) := by
    obtain ⟨k, hk⟩ := hdec
    exact ⟨k, fun v hv h => ((PCWorld.holds_neg v obsAtom).mp h) (hk v hv)⟩
  have hei : Tendsto (fun m => (LUV.indicatorOf (obsFamilyPred m)).expect T.H m
      - T.H m (obsFamilyPred m)) atTop (𝓝 0) :=
    lic_expectation_indicator_unconditional T.H T.process obsFamilyPred obsFamilyPred_codes
      T.hworld
  have h1 : Tendsto (fun m => T.H m obsAtom) atTop (𝓝 1) :=
    price_tendsto_one_of_decidedTrue T.H T.process T.hworld obsAtom hdec
  have h0 : Tendsto (fun m => T.H m (∼ obsAtom)) atTop (𝓝 0) :=
    price_tendsto_zero_of_decidedFalse T.H T.process T.hworld (∼ obsAtom) hneg
  have hei' : Tendsto (fun n => (LUV.indicatorOf (obsFamily n)).expect T.H (n + 1)
      - T.H (n + 1) (obsFamily n)) atTop (𝓝 0) := by
    have := hei.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have h1' : Tendsto (fun n => T.H (n + 1) obsAtom) atTop (𝓝 1) := by
    have := h1.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have h0' : Tendsto (fun n => T.H (n + 1) (∼ obsAtom)) atTop (𝓝 0) := by
    have := h0.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have hsq : Tendsto (fun n => T.H (n + 1) (obsFamily n) - obsTruth n) atTop (𝓝 0) := by
    have hb : Tendsto
        (fun n => |T.H (n + 1) obsAtom - 1| + |T.H (n + 1) (∼ obsAtom)|) atTop (𝓝 0) := by
      have := ((h1'.sub_const 1).abs).add (h0'.abs)
      simpa using this
    refine squeeze_zero_norm (fun n => ?_) hb
    unfold obsFamily obsTruth
    split_ifs with h
    · simp only [sub_zero, Real.norm_eq_abs]
      exact le_add_of_nonneg_left (abs_nonneg _)
    · simp only [Real.norm_eq_abs]
      exact le_add_of_nonneg_right (abs_nonneg _)
  have := hei'.add hsq
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring

/-- `obsAtom` is decided true in the constant-`½` pair's process too (the decidedness lives in the
base, transferred through the ledger as for `adjPair`). -/
theorem adjHalfPair_obsAtom_decided : DecidedTrueAt adjHalfPair.process obsAtom :=
  paperAdjoin_decided.ledger (a := aHalf) (e := fun _ => PublicationSchedule.succ)
    (paperAdjoin_freeOf_ledger _ _) obsAtom_tagFree

/-- **The probe's claim**: on the decided quote-free family `obsFamily`, the advised reader's
credence streams under two different tables are asymptotically equal — settlement-blind in the
`≈ₙ` sense. -/
theorem obsFamily_credence_table_independent :
    (fun n => (LUV.indicatorOf (obsFamily n)).expect adjPair.H (n + 1)) ≈ₙ
      (fun n => (LUV.indicatorOf (obsFamily n)).expect adjHalfPair.H (n + 1)) := by
  have h1 := obsFamily_expect_tendsto_truth adjPair adjPair_obsAtom_decided
  have h2 := obsFamily_expect_tendsto_truth adjHalfPair adjHalfPair_obsAtom_decided
  unfold AsympEq
  have := h1.sub h2
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  ring

end Cleanroom.Deference.DefObstruction

#print axioms Cleanroom.Deference.DefObstruction.obsFamily_credence_table_independent
#print axioms Cleanroom.Deference.DefObstruction.adjPair_adjHalfPair_tables_differ
