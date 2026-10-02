import Cleanroom.Uea.UeaSinkSwim.BestOnPathPolicy
import Cleanroom.Uea.UeaSinkSwim.TrapChain
import Cleanroom.Uea.UeaSinkSwim.NewcombOpaque
import Cleanroom.Uea.UeaSinkSwim.TheoremA

/-!
# Corollaries that need D1 and D2 together: D1 at the root, D1 on the trap chain, the chain's `π^R`, and the
printed 2025 Theorem 1 under the existential reading

Added in repair round 1 (audit r1: fidelity N2, N8; adversarial N1, N2). Everything here is a short composition
of theorems already in the package; the point is that the ledger's prose cells ("the chain (nearly tight)",
"`π^R` on the chain is `stay`") become theorems, and that the 2025 refutation does not depend on reading
"`π_S`" as *every* fixed point.

* `BestOnPath.gap_piB_root_le`: at the root of **every** model D1's trust hypothesis `w ≥ 1 - δ` is automatic
  (`w_root = 1 - δ` under every policy), so `gap(π^B, root) ≤ 1 - (1-δ)^(T-1)` with no hypothesis at all.
* `BestOnPath.piB_on_chain`: on the trap chain `π^B` is trusted at the root, loses exactly `1 - (1-δ')^K` there
  (by D2's uniqueness it is the stay policy), and D1's bound there is `1 - (1-δ)^K`, `δ' < δ`: the bound is
  attained up to `δ' → δ`. This is the D1 witness (N+: the bound is neither `0` nor slack).
* `TrapChain.piR_stay`, `TrapChain.piB_stay`: on the chain both canonical fixed points play `stay` at every chain
  node (D0/D1 + D2).
* `Printed2025.ReadingExists`, `Printed2025.readingExists_false`: the charitable reading of the printed theorem —
  for every small `δ` and every deterministic-percept model *some* plain fixed point is `ε`-optimal at the root —
  is also false, from `TrapChain.no_horizon_free_delta` (every fixed point of the chain loses more than `ε`).

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespaces `Cleanroom.Uea.UeaSinkSwim.BestOnPath`,
`…TrapChain`, `…Printed2025` (faf-cleanroom run, `uea-sink-swim`, repair round 1, 2026-10-01).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Cleanroom.Uea.UeaColeShadow
open Cleanroom.Uea.UeaColeShadow.Chain (goH)

namespace BestOnPath

/-- **D1 at the root needs no trust hypothesis**: `w_root = 1 - δ` for every policy of every model, so
`gap(π^B, root) ≤ 1 - (1-δ)^(T-1)` unconditionally — the sentence 2-010 (+) uses.
Source: [[uea-2-inventory]] 2-009, 2-010 (+); audit r1 (adversarial) N1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gap_piB_root_le {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
    (h : Hist A E 0) (hnt : M.nonterminal 0 h) :
    M.gap (piB M) 0 h ≤ 1 - (1 - M.δ) ^ (M.T - 1) :=
  (gap_piB_le_horizon M hnt (by rw [T1.wS_root])).1

/-- **D1 exercised on the trap chain (the D1 witness, N+)**: `π^B` is trusted at the root (`w = 1 - δ`), its root
loss is exactly `1 - (1-δ')^K` (it is the stay policy, by D2's uniqueness), and D1 bounds that loss by
`1 - (1-δ)^K` with `δ' < δ` — the bound is attained up to `δ' → δ`, so it is neither `0` nor slack there.
Source: [[uea-2-inventory]] 2-009, 2-011; audit r1 (fidelity) N2, (adversarial) N1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem piB_on_chain (P : TrapChain.TP) :
    1 - (TrapChain.model P).δ ≤ (TrapChain.model P).wS (piB (TrapChain.model P)) 0 (goH 0) ∧
    (TrapChain.model P).gap (piB (TrapChain.model P)) 0 (goH 0) = 1 - (1 - P.δ') ^ P.K ∧
    (TrapChain.model P).gap (piB (TrapChain.model P)) 0 (goH 0) ≤ 1 - (1 - P.δ) ^ P.K := by
  have hfp := (piB_isPlainFP (TrapChain.model P)).2
  have hw : 1 - (TrapChain.model P).δ ≤ (TrapChain.model P).wS (piB (TrapChain.model P)) 0 (goH 0) := by
    rw [TrapChain.wS_root]; simp
  refine ⟨hw, (TrapChain.gap_root_of_isPlainFP P hfp).1, ?_⟩
  have h := gap_piB_root_le (TrapChain.model P) (goH 0) (TrapChain.nt_goH P (Nat.zero_le _))
  simpa using h

end BestOnPath

namespace TrapChain

/-- **`π^R` on the chain is `stay`** at every chain node: D0 makes it a plain fixed point, D2 makes every plain
fixed point stay-everywhere.
Source: mandate target 6 (non-vacuity remark: "on the D2 chain is `stay`"); audit r1 (fidelity) N8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem piR_stay (P : TP) : ∀ n, n ≤ P.K → ResidualArgmax.piR (model P) n (goH n) 0 = 1 :=
  ((isPlainFP_iff P).1 (ResidualArgmax.piR_isPlainFP (model P)).2).2

/-- **`π^B` on the chain is `stay`** at every chain node (D1 + D2).
Source: [[uea-2-inventory]] 2-009, 2-011
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem piB_stay (P : TP) : ∀ n, n ≤ P.K → BestOnPath.piB (model P) n (goH n) 0 = 1 :=
  ((isPlainFP_iff P).1 (BestOnPath.piB_isPlainFP (model P)).2).2

end TrapChain

namespace Printed2025

/-- **The printed 2025 Theorem 1, charitable (existential) reading** (ATTRIBUTION-UNVETTED): "`π_S` is `ε`-optimal"
read as *some* plain fixed point is `ε`-optimal at the root — the weakest finite-shadow reading, in which the
oracle may select the fixed point. Same quantifiers as `Reading` otherwise.
Source: [[lesswrong-post--live-2026-08-22]] line 236; [[uea-inventory]] 021; audit r1 (adversarial) N2
Kind: D
Fidelity: variant: the finite shadow; the existential in place of `Reading`'s universal over fixed points
Hyps: n/a -/
def ReadingExists : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (A E ι : Type) [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] [Unique E] (M : Model A E ι),
      M.δ < δ₀ → ∃ π, M.IsPlainFP π ∧ ∀ h : Hist A E 0, M.gap π 0 h ≤ ε

/-- **Even the charitable reading is false** (at `ε = 1/4`): for every `δ₀` the trap chain with `δ < δ₀` has a plain
fixed point (so the existential is not refuted by emptiness) and every plain fixed point loses more than `1/4` at
the root (`TrapChain.no_horizon_free_delta`). So `printed_theorem1_refuted` does not depend on reading "`π_S`" as
every fixed point: at `γ = 1` no selection of the fixed point rescues the printed theorem.
Source: [[lesswrong-post--live-2026-08-22]] line 236; [[uea-2-inventory]] 2-010 (−); audit r1 (adversarial) N2
Kind: P
Fidelity: exact (against `ReadingExists`)
Hyps: (a) -/
theorem readingExists_false : ¬ ReadingExists := by
  intro H
  obtain ⟨δ₀, hδ₀, H⟩ := H (1 / 4) (by norm_num)
  set δ := min (δ₀ / 2) (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδδ₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨K, M, hMδ, _, _, hall⟩ := TrapChain.no_horizon_free_delta δ hδ hδ1 (1 / 4) (by norm_num)
  obtain ⟨π, hfp, hgap⟩ := H (Fin 2) Unit Unit M (by rw [hMδ]; exact hδδ₀)
  have h1 := (hall π hfp (fun i => Fin.elim0 i)).2.2
  have h2 := hgap (fun i => Fin.elim0 i)
  linarith

/-- The two readings refuted side by side: neither the universal (`Reading`) nor the existential (`ReadingExists`)
finite-shadow reading of the printed theorem holds.
Source: [[lesswrong-post--live-2026-08-22]] line 236; [[uea-inventory]] 021
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem both_readings_false : ¬ Reading ∧ ¬ ReadingExists :=
  ⟨printed_theorem1_refuted, readingExists_false⟩

end Printed2025

end Cleanroom.Uea.UeaSinkSwim
