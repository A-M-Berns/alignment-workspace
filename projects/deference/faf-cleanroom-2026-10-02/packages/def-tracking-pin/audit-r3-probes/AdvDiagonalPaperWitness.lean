import Cleanroom.Deference.DefTrackingPin.Witnesses

/-!
# Audit round 3 (adversarial) probe: `deferred_diagonal_subsequence`'s full package at the paper pair

The ledger row for `deferred_diagonal_subsequence` (proved at repair round 2) grades its witness
N+ with the sentence "the paper pair with `φ` any computable enumeration inhabits every hypothesis
…; no separate instance shipped". STANDARDS §3 asks every headline whose hypotheses are not
trivially satisfiable to *ship* a witness of its full package. This probe is that witness: the
diagonal quoted table `quoted _ n := witnessSentence n.unpair.1` over `DPA = DPH = paperDP 𝗜𝚺₁`
with the witness lookahead `F n = n + 1` and the witness schedule, FAF's LIA as the reader. Every
hypothesis is discharged from the same FAF facts `paperDeferred_*` uses, so the row's claim is
machine-checked here; the formalizer may lift it. Not imported by the library.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- The diagonal quoted table: a single item whose day-`n` sentence is `witnessSentence (unpair₁ n)`,
the pairing enumeration of anson-043 over the fresh atoms `witnessQuoted i 0`. -/
abbrev paperDiagonalQuoted (_j n : ℕ) : Sentence := witnessSentence n.unpair.1

/-- The diagonal quoted table is computable in `(j, n)`. -/
theorem paperDiagonalQuoted_computable :
    Computable fun p : ℕ × ℕ => paperDiagonalQuoted p.1 p.2 :=
  (witnessSentence_computable.comp
    (Computable.fst.comp (Computable.unpair.comp Computable.snd))).of_eq fun _ => rfl

/-- The deferred ledger process over `paperDP 𝗜𝚺₁` with the diagonal table. -/
noncomputable abbrev paperDiagonalProcess : DeductiveProcess :=
  deferredProcess (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) witnessLookahead paperDiagonalQuoted
    witnessSchedule

/-- FAF's LIA over the diagonal process: the reader. -/
noncomputable abbrev paperDiagonalReader : History :=
  deferredReader (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) witnessLookahead paperDiagonalQuoted
    witnessSchedule

/-- The reader is an inductor over the diagonal process (T5 at the diagonal table). -/
theorem paperDiagonal_inductor : IsLogicalInductor paperDiagonalReader paperDiagonalProcess :=
  deferred_inductor (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) witnessLookahead witnessLookahead_computable paperDiagonalQuoted
    paperDiagonalQuoted_computable witnessSchedule witnessSchedule_computable

/-- The base is free of the diagonal ledger's family. -/
theorem paperDiagonal_free :
    ProcessFreeOf (ledgerSchedule (deferredTable (paperDP 𝗜𝚺₁) witnessLookahead
      paperDiagonalQuoted) witnessSchedule) (paperDP 𝗜𝚺₁) :=
  processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁)

/-- **`deferred_diagonal_subsequence`'s full package inhabited at the paper pair**: for every `i`,
the reader's day-`⟨i,k⟩` expectation of the day-`⟨i,k⟩` contract tends in `k` to the fixed
market's limiting belief in `witnessSentence i`. Same grade as `paperDeferred_column_tendsto`
(real limit with no computable description; the quote values are not shown to vary). -/
theorem paperDiagonal_subsequence (i : ℕ) :
    Tendsto (fun k => (ledgerLuv 0 (Nat.pair i k)).expect paperDiagonalReader (Nat.pair i k))
      atTop (𝓝 (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (witnessSentence i))) :=
  haveI := paperDiagonal_inductor
  deferred_diagonal_subsequence (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    witnessLookahead witnessLookahead_le witnessSentence witnessSchedule paperDiagonalReader
    paperDiagonal_free (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) i

end Cleanroom.Deference.DefTrackingPin
