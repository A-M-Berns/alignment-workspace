import Cleanroom.Corrigibility.LegitNegPricing.Scoring
import Cleanroom.Corrigibility.LegitNegPricing.Thinning

/-!
# legit-neg-pricing, audit round 1, lens `fidelity`: probes

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is evidence for
one non-blocking item of `legit-neg-pricing-audit-r1-fidelity.md`:

1. `S2cell_witness4` advertises cells "strictly between" the full-state partition and `L_a`'s
   own; for `a₁` its cells *are* `L_{a₁}`'s partition, and for `a₀` (legitimate everywhere)
   purity is automatic. `probe_S2cell_strict` gives a witness where the action with non-trivial
   legitimacy (`a₁`, legitimate on three states) has a cell `{0, 1}` that is strictly coarser
   than a singleton and strictly finer than `L_{a₁} = {0, 1, 2}`, and the collapse still holds.
2. `B1_witness`'s cdot clause is one-directional (`ε (1/2 + η) < 1/2 → argmax P1 = {keep}`),
   while the ledger and finding 28 say "iff"/"the exact condition". `probe_B1_converse` proves
   the missing direction, so the wording is true; it should be stated or the wording softened.

Elaboration note (2026-09-30, Lean v4.31 via `scripts/lean-check`): exit 0, no errors. Lean prints
non-fatal `simp` simproc `PANIC at Lean.Expr.appArg!` lines during elaboration and the
`unreachableTactic` linter then claims the `norm_num` on the `25/48` goal "is never executed";
that is an artefact — removing it leaves the goal `4⁻¹ + 4⁻¹ * (3/4) + 4⁻¹ * 3⁻¹ = 25/48` unsolved.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing.AuditR1

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

/-- Probe 1: a partition with a cell strictly between the singletons and `L_{a₁}` for an action
whose legitimacy is non-trivial, on which the generalised collapse (`P1_S2cell_eq_P1_S1_of_pure`)
still applies and gives `P1 (S2cell) a₁ = P1 (S1) a₁` with a non-constant `u`.
Source: audit probe
Kind: N+
Fidelity: n/a -/
theorem probe_S2cell_strict :
    let P : Problem (Fin 4) (Fin 2) :=
      { prior := fun _ => 1/4
        prior_nonneg := fun _ => by norm_num
        prior_sum := by simp
        leg := fun s a => !(decide (s = 3) && decide (a = 1))
        u := fun s a => ![![1/2, 1], ![1/4, 3/4], ![0, 1/3], ![1, 1/5]] s a }
    let cellOf : Fin 4 → Finset (Fin 4) := fun s => if s.val < 2 then {0, 1} else {s}
    (∀ s, s ∈ cellOf s) ∧ (∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    ∧ (∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    ∧ (∀ s t, t ∈ cellOf s → P.leg t 1 = P.leg s 1)
    ∧ (cellOf 0).card = 2
    ∧ (univ.filter fun t => P.leg t 1 = P.leg 0 1).card = 3
    ∧ P.P1 (P.S2cell cellOf) 1 = P.P1 (S1 P.u) 1
    ∧ P.P1 (S1 P.u) 1 = 25/48 := by
  intro P cellOf
  have hmem : ∀ s, s ∈ cellOf s := by decide
  have hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s := by decide
  have hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t := by
    intro s; fin_cases s <;> simp [cellOf, P] <;> norm_num
  have hpure : ∀ s t, t ∈ cellOf s → P.leg t 1 = P.leg s 1 := by decide
  refine ⟨hmem, hcell, hpos, hpure, by decide, by decide, ?_, ?_⟩
  · exact P1_S2cell_eq_P1_S1_of_pure P cellOf 1 hmem hcell hpos hpure
  · simp [P, Problem.P1, Fin.sum_univ_four]; norm_num

/-- Probe 2: the converse of `B1_witness`'s cdot clause — when `ε (1/2 + η) ≥ 1/2`, cdot does
not keep alone (`thin+` ties or wins), so "cdot keeps iff `ε (1/2 + η) < 1/2`" is true.
Source: audit probe
Kind: P
Fidelity: n/a -/
theorem probe_B1_converse (ε η : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hη : 0 < η)
    (hge : 1/2 ≤ ε * (1/2 + η)) :
    argmax ((thinInstance ε η h0 h1).P1 (S1 (thinInstance ε η h0 h1).u)) ≠ {0} := by
  have hP1 : ∀ a, (thinInstance ε η h0 h1).P1 (S1 (thinInstance ε η h0 h1).u) a
      = (if a = 0 then 1 else ε) * (1/2 + (if a = 2 then η else 0)) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [thinInstance, thin_P1_of_unselected _ _ _ _ _ _ 0 (by simp) (S1 (thinBase η).u) _
        (fun s c _ => by simp), thinBase_P1]
      simp
    · rw [thinInstance, thin_P1_of_selected _ _ _ _ _ _ a (by simp [ha]) (S1 (thinBase η).u) _
        (fun s _ => by simp), thinBase_P1]
      simp [ha]
  intro h
  have h2 : (2 : Fin 3) ∉ argmax ((thinInstance ε η h0 h1).P1 (S1 (thinInstance ε η h0 h1).u)) := by
    rw [h]; simp
  rw [mem_argmax] at h2
  apply h2
  intro b
  rw [hP1, hP1]
  fin_cases b <;> simp <;> nlinarith [mul_nonneg h0 hη.le]

end Cleanroom.Corrigibility.LegitNegPricing.AuditR1
