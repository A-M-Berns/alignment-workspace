import Cleanroom.Deference.DefObstruction.BlindWitness
import Cleanroom.Deference.DefObstruction.SelfTrust

/-!
# def-obstruction · audit r3 (adversarial) · probe: the round-2 Tracking witness, placed

Three checks on repair round 2's additions, none of which the library states:

1. **The ledger's "`hT` is inhabited" claim type-checks.** The T12 row and the
   `externalized_self_trust` docstring say the Tracking antecedent `hT` is inhabited by
   `adjPair_tracks_obsFamily` at `X n := 𝟙 (obsFamily n)`. `TracksFamily` is FAF's `AsympEq` and
   `hT` is a `Tendsto (a − 𝔼) atTop (𝓝 0)`; they are definitionally the same, and
   `externalized_self_trust_at_benign` below is the theorem with that slot filled.
2. **The benign family sits in the dichotomy's blind branch.** `obsFamily` is tag-free, so it is
   `Blind` over `paperAdjoin` by `blind_of_tagFree`, hence `¬ QuoteRef` by
   `not_quoteRef_of_blind`. With `adjPair_tracks_obsFamily` this gives, on one FAF inductor,
   `Tracks ∧ Blind ∧ ¬ QuoteRef` (`benign_tracks_blind_not_quoteRef`): the predicted-and-
   uninfluenced corner of "predictable iff uninfluenced" is inhabited, which the library's
   round-2 witness shows only for `Tracks`. This is a strengthening of the record, not a defect.
3. **`SettlementBlind` has content**: the map that settles to the quote itself is not
   settlement-blind (`quote_not_settlementBlind`), so the definition of record is not vacuously
   true of every map; the library only ever proves it *of* the trivial autonomous map.

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## 1. The `hT` slot is filled by the round-2 witness -/

/-- `externalized_self_trust` at `adjPair`, `succDeferral`, `X n := 𝟙 (obsFamily n)`, with the
Tracking antecedent discharged by `adjPair_tracks_obsFamily`; only the three packages remain. -/
theorem externalized_self_trust_at_benign (B Q : ℕ → LUV) (p : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hcee : (fun n => (B n).expect adjPair.H n) ≈ₙ (fun n => (Q n).expect adjPair.H n))
    (hQ : (fun n => (Q n).expect adjPair.H n) ≈ₙ
      (fun n => (B n).expect adjPair.H (succDeferral n)))
    (hres : (fun n => (B n).expect adjPair.H (succDeferral n)) ≈ₙ
      (fun n => rampAbove δ (p n) (adjPair.a 0 n) *
        ((LUV.indicatorOf (obsFamily n)).expect adjPair.H (succDeferral n) - p n))) :
    (fun n => (B n).expect adjPair.H n) ≳ₙ fun _ => (0 : ℝ) :=
  externalized_self_trust adjPair succDeferral B Q (fun n => LUV.indicatorOf (obsFamily n)) p hδ
    hcee hQ hres adjPair_tracks_obsFamily

/-! ## 2. The benign family is blind and not quote-referencing -/

/-- The stronger process is tag-free for the ledger family: its only non-paper sentence is the
obstruction atom, of family `5`. -/
theorem paperAdjoin_tagFree : TagFreeProcess (cleanroomBaseTag + ledgerFamily) paperAdjoin := by
  intro k φ hφ
  unfold paperAdjoin adjoinAtom at hφ
  rw [extendBy_D, Finset.mem_union] at hφ
  rcases hφ with h | h
  · exact paperDP_tagFree 𝗜𝚺₁ (Nat.le_add_right _ _) k φ h
  · rw [Finset.mem_image] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp only [atomSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
      List.mem_singleton] at hx
    subst hx
    rw [literalOf_true]
    exact obsAtom_tagFree

/-- Every member of the benign family is tag-free. -/
theorem obsFamily_tagFree (n : ℕ) :
    TagFreeSentence (cleanroomBaseTag + ledgerFamily) (obsFamily n) := by
  unfold obsFamily
  split_ifs
  · exact obsAtom_tagFree.neg
  · exact obsAtom_tagFree

/-- The benign family is (truth-value) blind over the stronger base. -/
theorem obsFamily_blind : Blind paperAdjoin (fun _ => PublicationSchedule.succ) obsFamily :=
  blind_of_tagFree paperAdjoin_tagFree obsFamily obsFamily_tagFree

/-- The benign family never contains the diagonal. -/
theorem obsFamily_not_quoteRef : ¬ QuoteRef obsFamily :=
  not_quoteRef_of_blind (e := fun _ => PublicationSchedule.succ) paperAdjoin_tagFree
    paperAdjoin_hworld obsFamily obsFamily_blind

/-- **Predicted and uninfluenced, on one FAF inductor**: over `adjPair` the benign family is
tracked, truth-value blind, and not quote-referencing. -/
theorem benign_tracks_blind_not_quoteRef :
    TracksFamily adjPair succDeferral obsFamily ∧
      Blind adjPair.DPH adjPair.e obsFamily ∧ ¬ QuoteRef obsFamily :=
  ⟨adjPair_tracks_obsFamily, obsFamily_blind, obsFamily_not_quoteRef⟩

/-! ## 3. `SettlementBlind` is not vacuous -/

/-- Settling to the published quote itself is not settlement-blind. -/
theorem quote_not_settlementBlind : ¬ SettlementBlind (fun a n => (a 0 n : ℝ)) := by
  intro h
  have := h zeroTable oneTable 0
  norm_num [zeroTable, oneTable] at this

end Cleanroom.Deference.DefObstruction
