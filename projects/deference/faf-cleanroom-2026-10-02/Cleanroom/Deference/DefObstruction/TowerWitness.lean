import Cleanroom.Deference.DefObstruction.Tower
import Cleanroom.Deference.DefObstruction.Witness

/-!
# `def-obstruction` · TowerWitness: no timely tower on the alternating pair, hypothesis-free (T4, N+)

The read-off certificates for the alternating table: its values along the deferral,
`m ↦ aAlt 0 (m − 1)`, and at day `n`, `n ↦ aAlt 0 n`, are `P`-generable for every market
(`aAlt_pred_generable`, `aAlt_generable`) — a constant-leaf feature progression whose leaf code
is a unary-ruler dispatch on the parity of the day (the recipe of `li-diagonal`'s
`evenIndicator_pgenerable`). With them, both forms of T4 are **hypothesis-free** on the
alternating pair: the deferred-day tower instance fails by `½` (`altPair_tower_fails`) and so
does the notes' same-day instance (`altPair_tower_fails_sameDay`), with FAF's LIA over the paper
process plus the alternating ledger as the reader.

Scope: one-way.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. Generability of the alternating table -/

/-- The parity of the day is a unary ruler.
Source: none: infrastructure (FAF `MachineDigits.mod_two`)
Kind: L
Fidelity: n/a -/
theorem parity_ruler : UnaryRuler (fun n : ℕ => n % 2) :=
  (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two

/-- **The alternating table along the deferral is generable from any market**: the constant-leaf
feature `EF.const (aAlt 0 (m − 1))`, whose leaf code is a ruler dispatch on the parity of
`m − 1`.
Scope: one-way (the table alone).
Source: mandate T4(a) (the read-off certificate at the witness); `li-diagonal` `evenIndicator_pgenerable` (the recipe)
Kind: C
Fidelity: n/a (a certificate)
Hyps: (a) none -/
theorem aAlt_pred_generable (P : History) : PGenerableRat P (fun m => aAlt 0 (m - 1)) := by
  refine ⟨fun m => EF.const (aAlt 0 (m - 1)), ?_⟩
  have hr : UnaryRuler (fun m : ℕ =>
      if (m - 1) % 2 = 0 then Encodable.encode (0 : ℚ) else Encodable.encode (1 : ℚ)) :=
    UnaryRuler.ifZero predParity_ruler (UnaryRuler.const _) (UnaryRuler.const _)
  have hdig : MachineDigits (fun m : ℕ => Encodable.encode (aAlt 0 (m - 1))) := by
    refine (MachineDigits.ofUnaryRuler hr).of_eq fun m => ?_
    unfold aAlt
    split_ifs <;> rfl
  exact { rank_le := fun n => by simp
          polyTok := MachineSpliceStream.serialize_const_write hdig
          closed := fun n ρ V => by simp [EF.denoteWith, EF.denote]
          denote := fun n => by simp [EF.denote_const] }

/-- **The alternating table at day `n` is generable from any market.**
Scope: one-way (the table alone).
Source: mandate T4(b) (the day-`n` read-off certificate at the witness)
Kind: C
Fidelity: n/a (a certificate)
Hyps: (a) none -/
theorem aAlt_generable (P : History) : PGenerableRat P (fun n => aAlt 0 n) := by
  refine ⟨fun n => EF.const (aAlt 0 n), ?_⟩
  have hr : UnaryRuler (fun n : ℕ =>
      if n % 2 = 0 then Encodable.encode (0 : ℚ) else Encodable.encode (1 : ℚ)) :=
    UnaryRuler.ifZero parity_ruler (UnaryRuler.const _) (UnaryRuler.const _)
  have hdig : MachineDigits (fun n : ℕ => Encodable.encode (aAlt 0 n)) := by
    refine (MachineDigits.ofUnaryRuler hr).of_eq fun n => ?_
    unfold aAlt
    split_ifs <;> rfl
  exact { rank_le := fun n => by simp
          polyTok := MachineSpliceStream.serialize_const_write hdig
          closed := fun n ρ V => by simp [EF.denoteWith, EF.denote]
          denote := fun n => by simp [EF.denote_const] }

/-- The day-`n` true side of the alternating table is e.c.
Source: mandate T4(b) (certificates)
Kind: L
Fidelity: n/a -/
theorem trueSide_aAlt_codes : MachineSentenceCodes (trueSide aAlt) := by
  have h := MachineSentenceCodes.ifZero gDiag_codes gDiag_codes.neg parity_ruler
  refine MachineSentenceCodes.of_eq h fun n => ?_
  unfold trueSide
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos ((aAlt_le_half_iff n).2 hn)]
  · rw [if_neg hn, if_neg (fun h' => hn ((aAlt_le_half_iff n).1 h'))]

/-- The day-`n` false side of the alternating table is e.c.
Source: mandate T4(b) (certificates)
Kind: L
Fidelity: n/a -/
theorem falseSide_aAlt_codes : MachineSentenceCodes (falseSide aAlt) := by
  have h := MachineSentenceCodes.ifZero gDiag_codes.neg gDiag_codes parity_ruler
  refine MachineSentenceCodes.of_eq h fun n => ?_
  unfold falseSide
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos ((aAlt_le_half_iff n).2 hn)]
  · rw [if_neg hn, if_neg (fun h' => hn ((aAlt_le_half_iff n).1 h'))]

/-! ## B. T4 on the alternating pair, hypothesis-free -/

/-- **The deferred-day read-off on the alternating pair, hypothesis-free**:
`𝔼^H_{n+1}(α_{0,n}) ≈ₙ aAlt 0 n`.
Scope: one-way.
Source: mandate T4(a) witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_readoff :
    (fun n => (ledgerLuv 0 n).expect altPair.H (n + 1)) ≈ₙ (fun n => (aAlt 0 n : ℝ)) :=
  readoff_deferred altPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padLedger_codes_succ (by simpa [invDef_succ] using aAlt_pred_generable altPair.H)

/-- **No timely tower on the alternating pair (deferred day), hypothesis-free (headline 3's
witness)**: for every `ε > 0` eventually
`½ − ε ≤ |𝔼^H_{n+1}(𝟙 g_n) − 𝔼^H_{n+1}(α_{0,n})|`, with `H` FAF's LIA over the paper process plus
the alternating ledger.
Scope: one-way.
Source: [[no-timely-pointwise-tower]] §3 (anson-014); mandate T4(a) witness
Kind: N+
Fidelity: exact (at the deferred day `n + 1`)
Hyps: (a) none -/
theorem altPair_tower_fails :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |altPair.Y succDeferral n - (ledgerLuv 0 n).expect altPair.H (n + 1)| :=
  tower_fails_diagonal altPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aAlt_codes padFalseSide_aAlt_codes padG_codes_succ padLedger_codes_succ
    (by simpa [invDef_succ] using aAlt_pred_generable altPair.H)

/-- **No timely tower on the alternating pair (same day), hypothesis-free**: the notes' literal
`𝔼^H_n(g_n) ≈ₙ 𝔼^H_n(⌜a_n⌝)` fails by `½` — with next-day publication, so the day-`n` form does
not need the quote to be in the process at day `n`.
Scope: one-way.
Source: [[no-timely-pointwise-tower]] §3 (anson-014, the day-`n` statement); mandate T4(b)
Kind: N+
Fidelity: exact (the notes' indices)
Hyps: (a) none -/
theorem altPair_tower_fails_sameDay :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |(LUV.indicatorOf (gDiag n)).expect altPair.H n -
        (ledgerLuv 0 n).expect altPair.H n| :=
  tower_fails_diagonal_sameDay altPair trueSide_aAlt_codes falseSide_aAlt_codes
    (aAlt_generable altPair.H)

end Cleanroom.Deference.DefObstruction
