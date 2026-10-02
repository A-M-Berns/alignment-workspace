import Cleanroom.Bli.BliTransfer.AttemptB.Splice
import Cleanroom.Bli.BliFound.Witnesses
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `bli-transfer` · attempt B · Witnesses: T2's non-vacuity and the separation (light)

* `restrictedWitness` — a `RestrictedEC` trader with a genuine, day-varying price leaf: on day
  `n ≥ 1` the single trade `(price ⌜aₙ⌝ n, ⌜aₙ⌝)` (small on day `n` by `smallOn_atom_self`),
  nothing on day `0` (where only `⊥` is small). Certified through
  `EfficientlyComputable.ofTradeBlocksBig` with `machineSentenceCodes_atom` and
  `MachineSpliceStream.serialize_price` (grade N+: the leaf and the traded sentence change
  every day).
* `largeReader` — the separation: an `EfficientlyComputable` trader that is **not**
  `RestrictedEC`. It reads `price ⌜a_{4^{sizeBound 0}}⌝ 0` every day — large on day `0`
  (`largeOn_witness 0`) — with a fixed coefficient, so it is e.c. by the same capstone. Without
  it the `(c)` of T2 would be undocumented.
* `spliceOn_ne_self` — the splice is not the identity on `largeReader` for any map that fires
  on `(0, ⌜a_{4^{sizeBound 0}}⌝)`: the trader side of T1's non-vacuity (the map side is
  `WitnessLia.lean`'s).

Sources: mandate T2 (witness paragraph); `Framework/Machine/Witnesses.lean`;
`Cleanroom/Bli/BliFound/Witnesses.lean`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The restricted witness -/

/-- One trade on every day `≥ 1`, none on day `0`: `n − (n − 1)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrictedCount (n : ℕ) : ℕ := n - (n - 1)

/-- No trade on day `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictedCount_zero : restrictedCount 0 = 0 := rfl

/-- One trade on every day `≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictedCount_of_pos {n : ℕ} (hn : 1 ≤ n) : restrictedCount n = 1 := by
  unfold restrictedCount; omega

/-- The count is a unary ruler (two truncated subtractions of rulers).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unaryRuler_restrictedCount : UnaryRuler restrictedCount :=
  UnaryRuler.id.sub (UnaryRuler.id.sub (UnaryRuler.const 1))

/-- The coefficient family, indexed by `z = ⟨n, j⟩`: the day-`n` price of `⌜aₙ⌝`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrictedCoeff (z : ℕ) : LogicalInduction.EF :=
  .price (Formula.atom z.unpair.1) z.unpair.1

/-- The traded-sentence family: `⌜aₙ⌝` on day `n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrictedSentence (z : ℕ) : Sentence := Formula.atom z.unpair.1

/-- **The restricted witness trader**: day `n ≥ 1` plays `(price ⌜aₙ⌝ n, ⌜aₙ⌝)`, day `0` nothing.
Source: mandate T2 (witness paragraph)
Kind: D
Fidelity: n/a -/
def restrictedWitness : Trader where
  strat n :=
    { trades := (List.range (restrictedCount n)).map fun j =>
        (restrictedCoeff (Nat.pair n j), restrictedSentence (Nat.pair n j))
      rank_le := by
        intro p hp
        rw [List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [restrictedCoeff, Nat.unpair_pair] }

/-- On day `n ≥ 1` the witness trades exactly `(price ⌜aₙ⌝ n, ⌜aₙ⌝)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictedWitness_trades_of_pos {n : ℕ} (hn : 1 ≤ n) :
    (restrictedWitness.strat n).trades = [(.price (Formula.atom n) n, Formula.atom n)] := by
  simp [restrictedWitness, restrictedCount_of_pos hn, restrictedCoeff, restrictedSentence,
    Nat.unpair_pair]

/-- The witness is efficiently computable (machine data throughout: the atom family, the
`unpairFst` ruler for both the sentence index and the written-out day, the count ruler).
Source: mandate T2 (witness paragraph)
Kind: N+
Fidelity: n/a -/
lemma restrictedWitness_ec : EfficientlyComputable restrictedWitness :=
  EfficientlyComputable.ofTradeBlocksBig restrictedWitness restrictedCount restrictedCoeff
    restrictedSentence unaryRuler_restrictedCount
    ((MachineSpliceStream.serialize_price machineSentenceCodes_atom UnaryRuler.unpairFst
      (MachineDigits.ofUnaryRuler UnaryRuler.unpairFst)).of_eq (fun _ => rfl))
    (machineSentenceCodes_atom.comp UnaryRuler.unpairFst)
    (fun _ => rfl)

/-- **N+ for the restricted class**: `restrictedWitness` is `RestrictedEC`, with a genuine
day-varying price leaf (`price ⌜aₙ⌝ n`, small on day `n` from day `1`; day `0` trades nothing).
Source: mandate T2 (witness paragraph)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem restrictedWitness_restrictedEC : RestrictedEC restrictedWitness := by
  refine ⟨restrictedWitness_ec, fun n p hp q hq => ?_⟩
  simp only [restrictedWitness, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  simp only [restrictedCoeff, LogicalInduction.EF.priceQueries, List.mem_singleton] at hq
  subst hq
  simp only [Nat.unpair_pair]
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    simp [restrictedCount_zero] at hj
  exact smallOn_atom_self hn

/-- The witness's strategy varies with the day (days `1` and `2` trade different sentences).
Source: none: infrastructure
Kind: N+
Fidelity: n/a -/
lemma restrictedWitness_nonconstant :
    (restrictedWitness.strat 1).trades ≠ (restrictedWitness.strat 2).trades := by
  rw [restrictedWitness_trades_of_pos (by norm_num), restrictedWitness_trades_of_pos (by norm_num)]
  simp

/-! ## The separation -/

/-- The day-`0`-large atom `⌜a_{4^{sizeBound 0}}⌝` (`largeOn_witness 0`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def largeAtom : Sentence := Formula.atom (4 ^ sizeBound 0)

/-- **The separation trader**: every day, one trade of `⊥` with coefficient
`price ⌜a_{4^{sizeBound 0}}⌝ 0` — a leaf reading a sentence large on the day read.
Source: mandate T2 (separation)
Kind: D
Fidelity: n/a -/
def largeReader : Trader where
  strat _ := { trades := [(.price largeAtom 0, ⊥)], rank_le := by simp }

/-- `largeReader` is efficiently computable: constant families throughout.
Source: mandate T2 (separation)
Kind: N+
Fidelity: n/a -/
lemma largeReader_ec : EfficientlyComputable largeReader :=
  EfficientlyComputable.ofTradeBlocksBig largeReader (fun _ => 1) (fun _ => .price largeAtom 0)
    (fun _ => ⊥) (UnaryRuler.const 1)
    ((MachineSpliceStream.serialize_price (MachineSentenceCodes.const largeAtom)
      (UnaryRuler.const 0) (MachineDigits.const 0)).of_eq (fun _ => rfl))
    (MachineSentenceCodes.const ⊥)
    (fun _ => by simp [largeReader])

/-- **The separation**: `largeReader` is e.c. but not `RestrictedEC` — its leaf reads a
sentence large on day `0`. So `RestrictedEC ⊊ EfficientlyComputable`, and T2 is not the
criterion.
Source: mandate T2 (separation)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem largeReader_not_restrictedEC : ¬ RestrictedEC largeReader := by
  intro h
  have := h.2 0 (.price largeAtom 0, ⊥) (by simp [largeReader]) (0, largeAtom)
    (by simp [LogicalInduction.EF.priceQueries])
  exact largeOn_witness 0 this

/-- **The trader side of T1's non-vacuity**: any map firing on `(0, ⌜a_{4^{sizeBound 0}}⌝)`
rewrites `largeReader` non-trivially (its day-`n` coefficient becomes an administrative
`letE`).
Source: mandate T1.5 ("the trader side is exercised")
Kind: N+
Fidelity: n/a -/
theorem spliceOn_largeReader_ne (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (e : LogicalInduction.EF)
    (hfire : expr 0 largeAtom = some e) :
    Trader.spliceOn expr hr largeReader ≠ largeReader := by
  intro heq
  have h0 := congrArg (fun Tr : Trader => (Tr.strat 0).trades) heq
  simp [largeReader, Trader.spliceOn_strat, Strategy.spliceOn_trades,
    EF.spliceLeaf_some hfire] at h0

end Cleanroom.Bli.BliTransfer.AttemptB
