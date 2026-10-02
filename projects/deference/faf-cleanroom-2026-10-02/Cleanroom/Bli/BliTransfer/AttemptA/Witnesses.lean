import Cleanroom.Bli.BliTransfer.AttemptA.Defs
import Cleanroom.Bli.BliFound.Witnesses
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `bli-transfer` (attempt A) · Witnesses: T2's class witness and the separation (light)

* **N+ for the restricted class.** `restrictedWitness` trades, on every day `n ≥ 1`, one share of
  `⌜aₙ⌝` at the coefficient `price ⌜aₙ⌝ n` — a genuine, day-varying price leaf — and nothing on
  day `0` (the only day-`0` small sentence is `⊥`, `Size.three_le_tokenSize_atom`). It is
  efficiently computable through FAF's `EfficientlyComputable.ofTradeBlocksBig` at the atom family
  (`machineSentenceCodes_atom`, reindexed by `Nat.unpair.1`) and the price-leaf splice stream
  `MachineSpliceStream.serialize_price`, and it is `RestrictedEC` because `⌜aₙ⌝` is small on day
  `n ≥ 1` (`smallOn_atom_self`).
* **The separation.** `largeReader` reads, on every day, the day-`0` price of the atom
  `⌜a_{4^{sizeBound 0}}⌝`, which is large on day `0` (`largeOn_witness 0`) — so it is efficiently
  computable (its coefficient is a fixed feature) but not `RestrictedEC`. Without this, T2's `(c)`
  would be undocumented.

Sources: mandate T2 (witnesses); FAF `Framework/Machine/Witnesses.lean`, `SpliceMachine.lean`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The restricted-class witness -/

/-- One trade on every day `≥ 1`, none on day `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrictedCount (n : ℕ) : ℕ := if n = 0 then 0 else 1

/-- **The restricted-class witness**: on day `n ≥ 1`, one share of `⌜aₙ⌝` at the coefficient
`price ⌜aₙ⌝ n`; nothing on day `0`. Written in `ofTradeBlocksBig`'s trade-block shape so the
certificate is definitional.
Source: mandate T2 (N+ for the class)
Kind: D
Fidelity: n/a -/
def restrictedWitness : Trader where
  strat n :=
    { trades := (List.range (restrictedCount n)).map fun j =>
        (EF.price (Formula.atom (Nat.pair n j).unpair.1) (Nat.pair n j).unpair.1,
          (Formula.atom (Nat.pair n j).unpair.1 : Sentence))
      rank_le := by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank] }

/-- The witness is efficiently computable (FAF's trade-block constructor at the atom family and
the price-leaf splice stream).
Source: mandate T2 (N+ for the class); FAF `EfficientlyComputable.ofTradeBlocksBig`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma restrictedWitness_ec : EfficientlyComputable restrictedWitness :=
  EfficientlyComputable.ofTradeBlocksBig restrictedWitness restrictedCount
    (fun z => EF.price (Formula.atom z.unpair.1) z.unpair.1)
    (fun z => (Formula.atom z.unpair.1 : Sentence))
    (UnaryRuler.ifZero UnaryRuler.id (UnaryRuler.const 0) (UnaryRuler.const 1))
    (MachineSpliceStream.serialize_price machineSentenceCodes_atom UnaryRuler.unpairFst
      (MachineDigits.ofUnaryRuler UnaryRuler.unpairFst))
    (MachineSentenceCodes.comp machineSentenceCodes_atom UnaryRuler.unpairFst)
    (fun _ => rfl)

/-- **N+ for `RestrictedEC`**: the witness is in the class, with a genuine day-varying price
leaf (`price ⌜aₙ⌝ n` on day `n ≥ 1`).
Source: mandate T2 (N+ for the class)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem restrictedWitness_restricted : RestrictedEC restrictedWitness := by
  refine ⟨restrictedWitness_ec, fun n p hp q hq => ?_⟩
  simp only [restrictedWitness, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  have hn : n ≠ 0 := by
    intro h0
    simp [restrictedCount, h0] at hj
  simp only [EF.priceQueries, List.mem_singleton, Nat.unpair_pair] at hq
  subst hq
  exact smallOn_atom_self (Nat.one_le_iff_ne_zero.mpr hn)

/-- The witness genuinely reads a price on day `1`: its day-`1` coefficient is `price ⌜a₁⌝ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictedWitness_day_one :
    (restrictedWitness.strat 1).trades =
      [(EF.price (Formula.atom 1) 1, (Formula.atom 1 : Sentence))] := by
  simp [restrictedWitness, restrictedCount]

/-! ## The separation -/

/-- **The large reader**: on every day, one share of `⊥` at the coefficient
`price ⌜a_{4^{sizeBound 0}}⌝ 0` — a day-`0` price of a sentence large on day `0`.
Source: mandate T2 (separation)
Kind: D
Fidelity: n/a -/
def largeReader : Trader where
  strat n :=
    { trades := (List.range 1).map fun _ =>
        (EF.price (Formula.atom (4 ^ sizeBound 0)) 0, (⊥ : Sentence))
      rank_le := by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank] }

/-- The large reader is efficiently computable: its coefficient is a fixed feature.
Source: mandate T2 (separation); FAF `EfficientlyComputable.ofTradeBlocksBig`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma largeReader_ec : EfficientlyComputable largeReader :=
  EfficientlyComputable.ofTradeBlocksBig largeReader (fun _ => 1)
    (fun _ => EF.price (Formula.atom (4 ^ sizeBound 0)) 0) (fun _ => (⊥ : Sentence))
    (UnaryRuler.const 1)
    (MachineSpliceStream.serialize_price (MachineSentenceCodes.const (Formula.atom (4 ^ sizeBound 0)))
      (UnaryRuler.const 0) (MachineDigits.const 0))
    (MachineSentenceCodes.const ⊥)
    (fun _ => rfl)

/-- **The separation**: `RestrictedEC` is a proper subclass of `EfficientlyComputable` — the
large reader is efficiently computable but reads a day-`0` price of a sentence large on day `0`.
Source: mandate T2 (separation)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem restrictedEC_separation :
    EfficientlyComputable largeReader ∧ ¬ RestrictedEC largeReader := by
  refine ⟨largeReader_ec, fun h => ?_⟩
  have hleaf := h.2 0 (EF.price (Formula.atom (4 ^ sizeBound 0)) 0, (⊥ : Sentence))
    (by simp [largeReader]) (0, Formula.atom (4 ^ sizeBound 0)) (by simp [EF.priceQueries])
  exact largeOn_witness 0 hleaf

end Cleanroom.Bli.BliTransfer.AttemptA
