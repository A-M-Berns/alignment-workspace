import Cleanroom.Uea.UeaColeShadow.Floored
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Open statements of the `uea-cole-shadow` package

Precise statements left open (listed in `run/wp/uea-cole-shadow/uea-cole-shadow-open.txt`): the `ln⁺` form of
Theorem C, and pure fixed points at `T ≥ 3` for the plain and for the floored agent (the note's CONJECTURE; the
`T = 2` case of both is proved in `PureT2.lean`). The attainment question of Theorem B's tightness class, listed
here as an open statement in the first version of this package, was a classical tautology (`P ∨ ¬P`, round-1
audits); it is resolved in `Strict.lean` (`theoremB_strict`, `gap_eq_odds_not_attained`: never attained).

This module is a leaf: nothing in the library imports it (`IsPure` lives in `Defs.lean` since repair round 2), so
no proved declaration can rest on a `sorry` here — the gate would report it anyway.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

/-- **OPEN — Theorem C, `ln⁺` form**: `ε(h) ≤ O_h (3 + ln⁺(1/O_h))` for every floored fixed point and every decision
node with `0 < w_h` ([[sequential-self-game]] §4.1, Steps 5–7). The horizon form `theoremC` is proved; the
horizon-free form needs the telescoping of the `β`-sum and the `1 - x ≤ ln(1/x)` estimate on the `α`-sum along
the `π⋆`-path, which the node-local induction of `theoremC_depth` does not organise. Corner: at `w_h = 1` the
odds are `0` and Mathlib's `Real.log (1/0) = Real.log 0 = 0`, so the right-hand side is `0`; the statement then
says `gap ≤ 0`, which is true (`Vpi_eq_Vstar_of_xins_eq_zero`) — junk-free but worth knowing for the prover.
Source: [[sequential-self-game]] §4.1 (Theorem C)
Kind: OPEN
Fidelity: exact
Hyps: (a) -/
theorem theoremC_log_open (hfp : M.IsFlooredFP π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hw : 0 < M.wS π n h) :
    M.gap π n h ≤ M.odds π n h * (3 + max (Real.log (1 / M.odds π n h)) 0) := by
  sorry

/-- **OPEN — pure plain fixed points always exist** (the plain half of the note's CONJECTURE, credence ~0.6,
search evidence only; the `T = 2` case is `PureT2.exists_pure_isPlainFP`).
Source: [[sequential-self-game]] §4.5, §5
Kind: OPEN
Fidelity: exact (plain agent)
Hyps: (a) -/
theorem pure_exists_open : ∃ π, M.IsPure π ∧ M.IsPlainFP π := by
  sorry

/-- **OPEN — pure floored fixed points always exist** (the floored half of the note's CONJECTURE "for both
agents"; the `T = 2` case is `PureT2.exists_pure_isFlooredFP`).
Source: [[sequential-self-game]] §4.5, §5
Kind: OPEN
Fidelity: exact (floored agent)
Hyps: (a) -/
theorem pure_floored_exists_open : ∃ π, M.IsPure π ∧ M.IsFlooredFP π := by
  sorry

end Model

end Cleanroom.Uea.UeaColeShadow
