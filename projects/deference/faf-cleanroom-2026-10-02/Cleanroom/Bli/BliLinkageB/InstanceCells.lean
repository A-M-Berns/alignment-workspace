import Cleanroom.Bli.BliLinkageB.InstanceB2
import Cleanroom.Bli.BliLinkageB.DegenerateCells

/-!
# bli-linkage, angle B — K3's conclusion of record at FAF's LIA over `paperDP 𝗜𝚺₁`

The honest K3 at the real construction. `Q := liaHistory (paperDP 𝗜𝚺₁)` is a logical inductor
(FAF's `paperLIA`, unconditional); the B2 cell literals `cellSentence 𝗜𝚺₁ halfRound` quote *its*
rounded prices, so every hypothesis of `DegenerateCells.no_degenerate_linked_bli_cells` other
than the coordinate's "rounded price moves infinitely often" (`hmove`) and the shape of the
degenerate table is discharged here:

* `hψ` — the paired literal family `z ↦ cellSentence (z.unpair.1 + 1) c z.unpair.2` is
  machine-metered (`cellSentence_pair_machineSentenceCodes`: an atom over a `Nat.pair`-nest of
  constants, `unpairFst + 1` and `unpairSnd`); nothing about today's cell enters it (FB-14);
* `hdec` — a moved day's literal of today's cell is false, so its negation enters a stage of
  `paperDP 𝗜𝚺₁` (`cellSentence_neg_enters`), and every world consistent with that stage refutes
  it;
* `hworld` — `paperDP_hworld 𝗜𝚺₁`;
* the cells are `{0, 1} = Finset.range 2`.

`hmove` is the sole non-(a) hypothesis — exactly as mandate § K3 prescribes — and it is about
the LIA's own rounded prices (`marketValue 𝗜𝚺₁`), not about `bli-leak`'s `leakQ` (whose
inductor certificate is OPEN, li-pseudorandom T7). Discharging `hmove` for an explicit
coordinate of the LIA is the OPEN statement `leakQ_rounded_price_moves` of the mandate; it is
not stated here (no cross-package import of `BliLeak`), see the report.

Also here, closing handoff item 4: the negated B2 literal family is machine-metered
(`MachineSentenceCodes.neg`, FAF) and hence eventually day-small, which discharges `hneg` of
`Degenerate.no_degenerate_linked_bli` for a *fixed* cell index — the case in which `hmove`
fails, which is why that theorem needed replacing (FB-14).
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-- **The paired B2 literal family is machine-metered**: `z ↦ cellSentence (z.unpair.1 + 1) c
z.unpair.2` at `𝗜𝚺₁`, `halfRound`, for a fixed coordinate code `c`. The atom's code is a
`Nat.pair`-nest of constants, `z.unpair.1 + 1` and `z.unpair.2`.
Source: FAF `MachineDigits.natPair`/`ofUnaryRuler`, `UnaryRuler.unpairFst`/`unpairSnd`; bli-found `cellSentence`
Kind: L
Fidelity: n/a -/
theorem cellSentence_pair_machineSentenceCodes (c : ℕ) :
    MachineSentenceCodes fun z =>
      cellSentence 𝗜𝚺₁ halfRound halfRound_computable (z.unpair.1 + 1) c z.unpair.2 := by
  have hd : MachineDigits fun z => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
        (Nat.pair (z.unpair.1 + 1) (Nat.pair c z.unpair.2))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.unpairFst).add (MachineDigits.const 1))
              (MachineDigits.natPair (MachineDigits.const c)
                (MachineDigits.ofUnaryRuler UnaryRuler.unpairSnd))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- **The negated B2 literal family is machine-metered** (handoff item 4; FAF's
`MachineSentenceCodes.neg` closes the family under `∼`).
Source: FAF `MachineSentenceCodes.neg` (`Framework/Machine/SentenceMachine.lean:172`)
Kind: L
Fidelity: n/a -/
theorem neg_cellSentence_machineSentenceCodes (c r : ℕ) :
    MachineSentenceCodes fun n =>
      ∼ cellSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) c r :=
  MachineSentenceCodes.neg (cellSentence_machineSentenceCodes c r)

/-- The negated literal of a fixed coordinate and cell is eventually day-small — `hneg` of
`Degenerate.no_degenerate_linked_bli` for a fixed cell index.
Source: bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem neg_cellSentence_eventually_small (c r : ℕ) :
    ∃ N, ∀ n ≥ N, (∼ cellSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) c r) ∈ smallSet n := by
  obtain ⟨N, hN⟩ := machineSentenceCodes_eventually_small (neg_cellSentence_machineSentenceCodes c r)
  exact ⟨N, fun n hn => by rw [mem_smallSet]; exact hN n hn⟩

/-- `halfRound` takes values in `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfRound_lt_two (m : ℕ) (x : ℚ) : halfRound m x < 2 := by
  unfold halfRound; split_ifs <;> norm_num

/-- The B2 cells are `Finset.range 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCells_eq_range (m : ℕ) : twoCells m = Finset.range 2 := by
  show ({0, 1} : Finset ℕ) = Finset.range 2
  decide

/-- **K3 at FAF's LIA over `paperDP 𝗜𝚺₁` (the instance of record).** Let `Q` be the paper's
logical inductor `liaHistory (paperDP 𝗜𝚺₁)`, the cell family the B2 one at `halfRound` with
representatives `rep` (`fixedCF rep`), `c` a coordinate code listed and pinned from day `N` on,
and `deg n` the degenerate table, which lists `c` at today's rounded price
`halfRound n (marketValue 𝗜𝚺₁ ⟨n, ⌜sentenceOfCode c⌝⟩)` (`hentry`). If the LIA's rounded price
of the coordinate **moves infinitely often** (`hmove`), then no superbelief satisfies
`PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate` at the B2 state sentence `stateOf (fixedCF rep)` on a grid
with `SpuriousEntails`. Every other hypothesis of `no_degenerate_linked_bli_cells` is discharged
from FAF and bli-found (metering of the literal family, stage entry of the refuted literal,
`paperDP_hworld`); the inductor certificate is FAF's unconditional `paperLIA`, so no
`li-pseudorandom` T7 is involved. `hmove` is the honest conditional of mandate § K3.
Source: [[bli-program]] §3.6(iii); [[bli-program-desiderata]] I2; bli-paper-043; mandate K3 (conclusion of record, "with `χ n` listed and pinned eventually")
Kind: C
Fidelity: exact (stage level; `hmove` the only hypothesis not derived; the degenerate table's shape `hentry` and the grid conditions are instance data)
Hyps: (a); `hmove` is the honest conditional of mandate § K3 -/
theorem no_degenerate_linked_bli_LIA (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ) (S : StateSystem)
    {atoms : ℕ → Finset ℕ} {P : History} (c : ℕ) (deg : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, c ∈ pinned (fixedCF rep) index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hentry : ∀ n, entryOf c (tableOfCode (deg n)) =
      some (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))))))
    (hsp : ∀ n, SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal S index
      (fixedCF rep).cells n)
    (hatoms : ∀ n, stateAtoms (stateOf (fixedCF rep)) S n ⊆ atoms n)
    (hmove : Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode c)))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))))}) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P deg) := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) := paperLIA 𝗜𝚺₁
  refine no_degenerate_linked_bli_cells (fixedCF rep) deg (fun _ => c)
    (fun n => halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c)))))
    2 N (fun n => twoCells_eq_range (n + 1)) hpin hdegS (fun n => halfRound_lt_two _ _) hentry hsp
    hatoms (cellSentence_pair_machineSentenceCodes (Encodable.encode (sentenceOfCode c)))
    (paperDP_hworld 𝗜𝚺₁) ?_ hmove
  intro n hn
  obtain ⟨k, hk⟩ := cellSentence_neg_enters 𝗜𝚺₁ halfRound halfRound_computable hn
  exact ⟨k, fun v hv => (PCWorld.holds_neg v _).1 (hv _ hk)⟩

end Cleanroom.Bli.BliLinkageB
