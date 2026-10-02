import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Bli.BliFound.PaperInstances
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `li-quote-lane` · PaperWitness: the one-way pair over a real base (T6.2, N+)

The witness over FAF's paper process: `DPA := DPH := paperDP 𝗜𝚺₁` (the LI paper's own deductive
process over `IΣ₁`), quoted sentences the day-varying atoms `⟨0, ⟨j, n⟩⟩`, next-day publication.
`hfree` is `paperDP_cleanroomFree` (every atom of `paperDP` has a FAF tag `< 9`), `hworld` is
`paperDP_hworld` (consistency of `IΣ₁`).

**What "day-varying quotes" can and cannot mean here.** The quoted *sentences* and the ledger
*atoms* vary with the item and the day (`witnessQuoted_injective`, `ledgerLuv_gt_ne`); both
polarities occur in the ledger (`paperOneWayPair_both_polarities`: `r = -1` affirmed, `r = 2`
denied, by `liaHistory_range`); the ledger is not a constant schedule. The *values*
`liaQuote (paperDP 𝗜𝚺₁) n φ_n` are not shown to vary — that would evaluate the LIA. Graded N+
on those grounds; no claim `a_n ≠ a_m` is made. Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc

/-- The quoted family of the witness: the atom `⟨0, ⟨j, n⟩⟩` for item `j`, day `n` (FAF tag `0`;
a sentence of the base language, disjoint from every fresh family). "Of the base language" means
only that the atom carries a FAF public tag; whether `paperDP 𝗜𝚺₁` decides any of these atoms is
not claimed either way (audit r1 adversarial 7) — the N+ grading of `paperOneWayPair` rests on
the process/inductor structure, the varying atoms and both polarities, not on undecidedness.
Source: mandate T6.2
Kind: D
Fidelity: n/a -/
def witnessQuoted (j n : ℕ) : Sentence := Formula.atom (Nat.pair 0 (Nat.pair j n))

/-- `witnessQuoted` is computable (primitive recursive) in `(j, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma witnessQuoted_computable : Computable fun p : ℕ × ℕ => witnessQuoted p.1 p.2 :=
  (sentenceAtom_prim.comp (Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd))).to_comp

/-- The quoted sentences vary with the item and the day.
Source: mandate T6.2 (N+ grounds)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
lemma witnessQuoted_injective {j n j' n' : ℕ} (h : witnessQuoted j n = witnessQuoted j' n') :
    j = j' ∧ n = n' := by
  unfold witnessQuoted at h
  have h1 := Nat.pair_eq_pair.mp (LO.Propositional.Formula.atom.inj h)
  exact Nat.pair_eq_pair.mp h1.2

/-- Next-day publication for every item is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma succSchedule_computable :
    Computable fun p : ℕ × ℕ => ((fun _ : ℕ => PublicationSchedule.succ) p.1).e p.2 :=
  (Primrec.succ.comp Primrec.snd).to_comp

/-- **T6.2 (N+). The one-way pair over `paperDP 𝗜𝚺₁`**: `A = liaHistory (paperDP 𝗜𝚺₁)` reads
nothing; `H⁺ = liaHistory (paperDP 𝗜𝚺₁ ⊕ ledger)` reads `A`'s day-`n` prices of the day-varying
atoms `⟨0, ⟨j, n⟩⟩`, published the next day. Every field of `OneWayPair` is inhabited from FAF's
own facts (`paperDP_computable`, `paperDP_cleanroomFree`, `paperDP_hworld`,
`LIA_is_logical_inductor`). Scope: one-way.
Source: mandate T6.2; [[route-sparse-schedule]] §9 (vq-wiki-067's non-vacuity obligation)
Kind: N+
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def paperOneWayPair : OneWayPair :=
  OneWayPair.ofLIA (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) witnessQuoted witnessQuoted_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁)

/-- The witness's fixed market is FAF's paper LIA.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperOneWayPair_A : paperOneWayPair.A = liaHistory (paperDP 𝗜𝚺₁) := rfl

/-- The witness's table is `A`'s exact day-`n` prices of the quoted atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperOneWayPair_a (j n : ℕ) :
    paperOneWayPair.a j n = liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n) := rfl

/-- **N+ grounds: both polarities occur in the witness's ledger**, for every item and day
(`r = -1` affirmed, `r = 2` denied), so the ledger is not a one-sided or constant schedule.
Source: mandate T6.2
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperOneWayPair_both_polarities (j n : ℕ) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule paperOneWayPair.a paperOneWayPair.e).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule paperOneWayPair.a paperOneWayPair.e).lits s :=
  ledgerSchedule_both_polarities _ _
    (fun j n => liaQuote_mem (paperDP 𝗜𝚺₁) n (witnessQuoted j n)) j n

/-- **N+ grounds: the witness's ledger atoms vary with the item and the day.**
Source: mandate T6.2
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperOneWayPair_atoms_vary {j n j' n' : ℕ} (h : n ≠ n' ∨ j ≠ j') (r r' : ℚ) :
    (ledgerLuv j n).gt r ≠ (ledgerLuv j' n').gt r' :=
  ledgerLuv_gt_ne h r r'

end Cleanroom.Found.LiQuoteLane
