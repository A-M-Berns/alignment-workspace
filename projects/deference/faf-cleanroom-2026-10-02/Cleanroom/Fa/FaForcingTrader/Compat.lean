import Cleanroom.Fa.FaForcingTrader.Defs
import Cleanroom.Fa.FaForcingTrader.B.Defs

/-!
# `fa-forcing-trader` · Compat: angle B's duplicated definitions against the definitions of record

Angle B started before angle A's shared `Defs.lean` was committed and carries its own copies of
the shared definitions under `Cleanroom.Fa.FaForcingTrader.B` (its report, § Shared definitions).
The reconciler keeps B's files unchanged as evidence and relates every duplicated notion to the
definition of record here, so that B's headlines can be restated over the record definitions in
`TheoremSS.lean` without touching B:

* `LegibleOn` and `WindowDisjoint` are **syntactically identical** in the two namespaces (`rfl`).
* `scheduleIndicator` differs in its ruler — A's counts matches with its own `schedCount`, B's
  wraps FAF's `deferralImageFlag` — but the two denote the same real `schedInd d m` in every
  market (`B_scheduleIndicator_denote`), so `schedGate` / `schedGateBelow` denote the same
  numbers (`B_schedGate_denote`, `B_schedGateBelow_denote`) and legibility, divergence and
  schedule support transfer both ways.

Nothing here is a headline; kind `L` throughout.
-/

namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

/-- Angle B's `LegibleOn` is the definition of record, syntactically.
Source: none: infrastructure (reconciler; mandate § Definitions)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_legibleOn_eq : B.LegibleOn = LegibleOn := rfl

/-- Angle B's `WindowDisjoint` is the definition of record, syntactically.
Source: none: infrastructure (reconciler; mandate § Definitions)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_windowDisjoint_eq : B.WindowDisjoint = WindowDisjoint := rfl

/-- Angle B's schedule indicator (FAF's `deferralImageFlag` as a constant feature) denotes the
record's real indicator `schedInd d m` (`1` on `im d`, `0` off it) in every market.
Source: none: infrastructure (reconciler; mandate T1)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_scheduleIndicator_denote (d : DeferralFunction) (P : History) (m : ℕ) :
    (B.scheduleIndicator d m).denote P = schedInd d m := by
  by_cases h : ∃ k, d.f k = m
  · obtain ⟨k, hk⟩ := h
    subst hk
    rw [B.scheduleIndicator_denote_of_mem, schedInd_of_mem]
  · rw [B.scheduleIndicator_denote_of_not_mem d P h,
      schedInd_of_not_mem d (fun k hk => h ⟨k, hk⟩)]

/-- Angle B's scheduled upper gate denotes the record's `schedGate` in every market.
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedGate_denote (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History)
    (n : ℕ) : (B.schedGate Y d t δ n).denote A = (schedGate Y d t δ n).denote A := by
  unfold B.schedGate schedGate
  rw [EF.denote_mul, EF.denote_mul, Pi.mul_apply, Pi.mul_apply, B_scheduleIndicator_denote,
    scheduleIndicator_denote]

/-- Angle B's scheduled lower gate denotes the record's `schedGateBelow` in every market.
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedGateBelow_denote (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History)
    (n : ℕ) : (B.schedGateBelow Y d t δ n).denote A = (schedGateBelow Y d t δ n).denote A := by
  unfold B.schedGateBelow schedGateBelow
  rw [EF.denote_mul, EF.denote_mul, Pi.mul_apply, Pi.mul_apply, B_scheduleIndicator_denote,
    scheduleIndicator_denote]

/-- The real values of B's upper gate and of the record's are the same function.
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedGate_denote_fun (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History) :
    (fun n => (B.schedGate Y d t δ n).denote A) = fun n => (schedGate Y d t δ n).denote A :=
  funext (B_schedGate_denote Y d t δ A)

/-- The real values of B's lower gate and of the record's are the same function.
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedGateBelow_denote_fun (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ)
    (A : History) :
    (fun n => (B.schedGateBelow Y d t δ n).denote A) =
      fun n => (schedGateBelow Y d t δ n).denote A :=
  funext (B_schedGateBelow_denote Y d t δ A)

/-- Divergence of the record's upper gate transfers to B's copy (same numbers).
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedGate_divergent {Y : ℕ → LUV} {d : DeferralFunction} {t δ : ℚ} {A : History}
    (hdiv : DivergentWeighting (schedGate Y d t δ) A) :
    DivergentWeighting (B.schedGate Y d t δ) A :=
  B.DivergentWeighting.transfer (B_schedGate_denote Y d t δ A) hdiv

/-- Divergence of the record's lower gate transfers to B's copy (same numbers).
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedGateBelow_divergent {Y : ℕ → LUV} {d : DeferralFunction} {t δ : ℚ}
    {A : History} (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A) :
    DivergentWeighting (B.schedGateBelow Y d t δ) A :=
  B.DivergentWeighting.transfer (B_schedGateBelow_denote Y d t δ A) hdiv

end Cleanroom.Fa.FaForcingTrader
