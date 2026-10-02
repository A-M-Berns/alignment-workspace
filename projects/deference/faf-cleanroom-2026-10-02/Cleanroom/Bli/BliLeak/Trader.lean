import Cleanroom.Bli.BliLeak.Leak
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.SentenceMachine
import LogicalInduction.Framework.Machine.Ruler
import LogicalInduction.Framework.Machine.WriteOutMachine

/-!
# `bli-leak` · Trader: the leak-reading trader is efficiently computable (L3.2)

The machine certificate for `leakTrader ℓ e χ` (`Leak.lean`), by FAF's variable-count
realization theorem `EfficientlyComputable.ofTradeBlocksBig` at count `1` on the days `e n ≤ n`
and `0` otherwise, with the coefficient stream assembled from `MachineSpliceStream.serialize_price`
— the route FAF's own `adviceTrader_efficient` takes. The single-trade entry point
`ofSingleTradeBlocksBig` is *not* usable: it demands price-free coefficients, and the leak
coefficient is a price read (findings K1).

Also here, because the certificate needs them: the atom-family lemma
`machineSentenceCodes_atom_of_machineDigits` (FAF has it only at the identity placement,
`machineSentenceCodes_atom`; an FAF API request), and the write-out certificates of the package's
two families, `member` and `leakAtom K`, as `MachineDigits.natPair`s of constants and the identity
ruler.

No Construction import: everything here is `Framework.Machine`.
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Li.LiPseudorandom

/-! ## Atom families over a machine-written index -/

/-- **An atom family over a machine-written index is machine-metered**: the canonical Polish
word of `atom (c n)` is the one token `c n + 5`, so `MachineDigits.add` with the constant `5`
and `MachineSentenceCodes.ofCanonical` certify it. FAF proves this at `c = id` only
(`machineSentenceCodes_atom`); the general form is an FAF API request.
Source: mandate L3.2 (`machineSentenceCodes_atom_of_machineDigits`); FAF `machineSentenceCodes_atom`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem machineSentenceCodes_atom_of_machineDigits {c : ℕ → ℕ} (hc : MachineDigits c) :
    MachineSentenceCodes (fun n => (Formula.atom (c n) : Sentence)) :=
  MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hc.add (MachineDigits.const 5)) (fun _ => rfl))

/-- The identity is a machine-written value (through the identity ruler).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem machineDigits_id : MachineDigits (fun n => n) :=
  MachineDigits.ofUnaryRuler UnaryRuler.id

/-- The member placement `member n = ⟨cleanroomBaseTag + memberFamily, ⟨n, 0⟩⟩` is machine-written.
Source: mandate L3.2 (the atom-family certificates)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem machineDigits_member : MachineDigits member :=
  (MachineDigits.natPair (MachineDigits.const (cleanroomBaseTag + memberFamily))
    (MachineDigits.natPair machineDigits_id (MachineDigits.const 0))).of_eq (fun _ => rfl)

/-- The leak-atom index `⟨cleanroomBaseTag + leakFamily, ⟨n, K⟩⟩` is machine-written, for any
fixed pad `K` (a constant token, however large as a number: `MachineDigits` meters length).
Source: mandate L3.2 (the atom-family certificates)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem machineDigits_leakCode (K : ℕ) :
    MachineDigits (fun n => freshAtomCode leakFamily (Nat.pair n K)) :=
  (MachineDigits.natPair (MachineDigits.const (cleanroomBaseTag + leakFamily))
    (MachineDigits.natPair machineDigits_id (MachineDigits.const K))).of_eq (fun _ => rfl)

/-- The pseudorandom family's atoms are machine-metered: `MachineSentenceCodes memberAtom`.
Source: mandate L3.2, L3.5 (`MachineSentenceCodes χ` by the atom lemma)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem machineSentenceCodes_memberAtom : MachineSentenceCodes memberAtom :=
  machineSentenceCodes_atom_of_machineDigits machineDigits_member

/-- The leak atoms of pad `K` are machine-metered: `MachineSentenceCodes (leakAtom K)`. This is
what lets the trader *name* the leak atom on its reading day — and what forbids a pad so large
that the atom is never nameable (mandate L3.1's trap).
Source: mandate L3.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem machineSentenceCodes_leakAtom (K : ℕ) : MachineSentenceCodes (leakAtom K) :=
  (machineSentenceCodes_atom_of_machineDigits (machineDigits_leakCode K)).of_eq (fun _ => rfl)

/-! ## L3.2: the certificate -/

/-- **L3.2. The leak-reading trader is efficiently computable**, for every leak family `ℓ` and
traded family `χ` that are machine-metered, every machine-written edit-day function `e`, and a
unary-ruler count `if e n ≤ n then 1 else 0` (the days on which the trader holds its position).
Route: `EfficientlyComputable.ofTradeBlocksBig` at that count, coefficient stream
`serialize_add (serialize_mul (serialize_const 2) (serialize_price hℓ unpairFst hd)) (serialize_const (-1))`
with `hd : MachineDigits (fun z ↦ e z.unpair.1)`, sentence family `χ ∘ unpair.1`.
Source: mandate L3.2; [[bli-program]] §4 row L3 (certificate corrected, K1); FAF
`adviceTrader_efficient` (the same route)
Kind: C
Fidelity: exact
Hyps: (a); the count ruler is discharged below for the two edit-day functions the package uses -/
theorem leakTrader_ec {ℓ χ : ℕ → Sentence} {e : ℕ → ℕ}
    (hℓ : MachineSentenceCodes ℓ) (hχ : MachineSentenceCodes χ) (he : MachineDigits e)
    (hcount : UnaryRuler (fun n => if e n ≤ n then 1 else 0)) :
    EfficientlyComputable (leakTrader ℓ e χ) := by
  have hprice : MachineSpliceStream
      (fun z : ℕ => (EF.price (ℓ z.unpair.1) (e z.unpair.1)).serialize) :=
    MachineSpliceStream.serialize_price hℓ UnaryRuler.unpairFst (he.comp UnaryRuler.unpairFst)
  have hcoef : MachineSpliceStream (fun z : ℕ => (leakCoef ℓ e z.unpair.1).serialize) :=
    MachineSpliceStream.serialize_add
      (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const 2) hprice)
      (MachineSpliceStream.serialize_const (-1))
  refine EfficientlyComputable.ofTradeBlocksBig (leakTrader ℓ e χ)
    (fun n => if e n ≤ n then 1 else 0) (fun z => leakCoef ℓ e z.unpair.1)
    (fun z => χ z.unpair.1) hcount hcoef (hχ.comp UnaryRuler.unpairFst) (fun n => ?_)
  rw [leakTrader_trades]
  split_ifs with hen
  · simp [List.range_succ, Nat.unpair_pair]
  · simp

/-- L3.2 when the edit day never exceeds the reading day (`∀ n, e n ≤ n`): the count is the
constant `1`.
Source: mandate L3.2 (`hen : ∀ n, e n ≤ n`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakTrader_ec_of_le {ℓ χ : ℕ → Sentence} {e : ℕ → ℕ}
    (hℓ : MachineSentenceCodes ℓ) (hχ : MachineSentenceCodes χ) (he : MachineDigits e)
    (hen : ∀ n, e n ≤ n) :
    EfficientlyComputable (leakTrader ℓ e χ) :=
  leakTrader_ec hℓ hχ he ((UnaryRuler.const 1).of_eq (fun n => by simp [hen n]))

/-- L3.2 at a fixed edit day `N₀` (the finite-prefix retreat, L3.4): the count is
`if N₀ ≤ n then 1 else 0`, a ruler by `UnaryRuler.ifZero` on the truncated difference `n + 1 − N₀`.
Source: mandate L3.2, L3.4 (`e := fun _ ↦ N₀`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakTrader_ec_const {ℓ χ : ℕ → Sentence} (N₀ : ℕ)
    (hℓ : MachineSentenceCodes ℓ) (hχ : MachineSentenceCodes χ) :
    EfficientlyComputable (leakTrader ℓ (fun _ => N₀) χ) := by
  refine leakTrader_ec hℓ hχ (MachineDigits.const N₀) ?_
  have h : UnaryRuler (fun n => if n + 1 - N₀ = 0 then 0 else 1) :=
    UnaryRuler.ifZero (UnaryRuler.id.succ.sub (UnaryRuler.const N₀))
      (UnaryRuler.const 0) (UnaryRuler.const 1)
  exact h.of_eq (fun n => by split_ifs <;> omega)

/-- The leak trader of record — leak atoms of pad `K`, edit day `N₀`, the member atoms traded —
is efficiently computable.
Source: mandate L3.4/L3.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakTrader_record_ec (K N₀ : ℕ) :
    EfficientlyComputable (leakTrader (leakAtom K) (fun _ => N₀) memberAtom) :=
  leakTrader_ec_const N₀ (machineSentenceCodes_leakAtom K) machineSentenceCodes_memberAtom

end Cleanroom.Bli.BliLeak
