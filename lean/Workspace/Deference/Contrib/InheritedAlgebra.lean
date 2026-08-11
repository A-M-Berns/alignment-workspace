/-
# The inherited deference algebra, re-elaborated against the pinned dependency

Provisional namespace and provisional names (`AGENTS.md` §6).

`projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` records Movement I's rows as
`inherited-established` **on the strength of the inherited development's own audit**, with
its own toolchain, and states that confirming them against the source is
`PRIORITIES.md` item 14. This file discharges part of that: the ledger's top rows,
transcribed from `projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean` and
re-elaborated here.

Nothing is strengthened. Two deliberate changes, both recorded in this round's `REPORT.md`:

1. The inherited modules define their own `Approx` / `AsympLE`. Those are **definitionally
   the pinned dependency's** `LogicalInduction.AsympEq` (`≈ₙ`) and
   `LogicalInduction.AsympLE` (`≲ₙ`), together with `AsympEq.finsetSum` for the inherited
   `approx_sum` and `AsympLE.trans_asympEq` for the inherited `AsympLE.trans_approx`. The
   port uses the dependency's vocabulary and re-proves none of that calculus.
2. `Deference.value_of_defects` / `soft_nonneg` / `value_of_CM` and
   `DeferenceExtra.softmax_lower_bound` are *not* transcribed here. See `REPORT.md` §4 for
   what that leaves unconfirmed.
-/
import LogicalInduction.Framework.Asymptotics
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic

namespace Workspace.Deference.Contrib.InheritedAlgebra

open Finset Filter Topology LogicalInduction

/-! ## Ledger row: `decomposition` -/

/-- Ported from inherited `Deference.decomposition`. The keystone identity
`gap i = D_CM + D_UM i + soft i`, for every finite frame, menu and weight family. Pure
linearity: no hypothesis on the frame. -/
theorem decomposition
    {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (Pr : W → W → K) (O : J → W → K) (α : J → W → K) (i : J) :
    (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * O i w)
      =
      (∑ w, π w * (∑ j, α j w * (O j w - ∑ v, Pr w v * O j v)))
    + ((∑ w, π w * (∑ v, Pr w v * O i v)) - (∑ w, π w * O i w))
    + (∑ w, π w * ((∑ j, α j w * (∑ v, Pr w v * O j v)) - (∑ v, Pr w v * O i v))) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ## Ledger row: `value_iff_totalTrust` (finite-exact) -/

/-- Ported from inherited `DeferenceConverse.witness_identity`. The two-option
witness-menu identity: the followed-strategy Value gap over the constant option `s` equals
the conditional Total-Trust mass. -/
theorem witness_identity {W : Type*} [Fintype W]
    (π : W → ℝ) (Pr : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (∑ w, π w * (if s ≤ (∑ v, Pr w v * X v) then X w else s)) - s * (∑ w, π w)
      = ∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w * (X w - s) else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : s ≤ (∑ v, Pr w v * X v)
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- Ported from inherited `DeferenceConverse.value_witness_iff_totalTrust`. -/
theorem value_witness_iff_totalTrust {W : Type*} [Fintype W]
    (π : W → ℝ) (Pr : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, Pr w v * X v) then X w else s))
      ↔ (0 ≤ ∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w * (X w - s) else 0)) := by
  rw [← sub_nonneg, witness_identity π Pr X s]

/-- Ported from inherited `DeferenceConverse.totalTrust_sum_split`. -/
theorem totalTrust_sum_split {W : Type*} [Fintype W]
    (π : W → ℝ) (Pr : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w * (X w - s) else 0))
      = (∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w * X w else 0))
        - s * (∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w else 0)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : s ≤ (∑ v, Pr w v * X v)
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- Ported from inherited `DeferenceConverse.value_witness_iff_totalTrust_mass`. -/
theorem value_witness_iff_totalTrust_mass {W : Type*} [Fintype W]
    (π : W → ℝ) (Pr : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, Pr w v * X v) then X w else s))
      ↔ (s * (∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w else 0))
          ≤ ∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w * X w else 0)) := by
  rw [value_witness_iff_totalTrust π Pr X s, totalTrust_sum_split π Pr X s, sub_nonneg]

/-- Ported from inherited `DeferenceConverse.value_iff_totalTrust`: the ledger's first
Movement-I row. Note the exact shape — it is the universal closure of the *pointwise*
equivalence `value_witness_iff_totalTrust_mass`, not a derivation relating two independently
stated global properties. -/
theorem value_iff_totalTrust {W : Type*} [Fintype W]
    (π : W → ℝ) (Pr : W → W → ℝ) :
    (∀ (X : W → ℝ) (s : ℝ),
        s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, Pr w v * X v) then X w else s))
      ↔ (∀ (X : W → ℝ) (s : ℝ),
          s * (∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w else 0))
            ≤ ∑ w, (if s ≤ (∑ v, Pr w v * X v) then π w * X w else 0)) :=
  ⟨fun h X s => (value_witness_iff_totalTrust_mass π Pr X s).mp (h X s),
   fun h X s => (value_witness_iff_totalTrust_mass π Pr X s).mpr (h X s)⟩

/-! ### The anti-expert frame — the inherited non-vacuity witness

Ported from inherited `DeferenceConverse.AntiExpert`. Worlds `Fin 2`; `π = (½,½)`;
`Pr = ⅕` on the diagonal, `⅘` off; `X = 1[world 0]`; `s = ½`. The unconditional martingale
holds yet Total Trust fails, so Value fails on the witness: the equivalence is non-vacuous
and marginal-martingale is not Value.
-/

namespace AntiExpert

noncomputable def π : Fin 2 → ℝ := fun _ => 1/2
noncomputable def Pr : Fin 2 → Fin 2 → ℝ := fun w v => if w = v then 1/5 else 4/5
noncomputable def X : Fin 2 → ℝ := fun w => if w = 0 then 1 else 0

theorem E0_lt : ¬ ((1/2 : ℝ) ≤ (∑ v, Pr (0 : Fin 2) v * X v)) := by
  norm_num [Pr, X, Fin.sum_univ_two]

theorem E1_ge : (1/2 : ℝ) ≤ (∑ v, Pr (1 : Fin 2) v * X v) := by
  norm_num [Pr, X, Fin.sum_univ_two]

theorem stationary : ∀ v : Fin 2, (∑ w, π w * Pr w v) = π v := by
  intro v
  fin_cases v <;> norm_num [π, Pr, Fin.sum_univ_two]

theorem TT_negative :
    (∑ w, (if (1/2 : ℝ) ≤ (∑ v, Pr w v * X v) then π w * (X w - 1/2) else 0)) = -1/4 := by
  rw [Fin.sum_univ_two, if_neg E0_lt, if_pos E1_ge]
  norm_num [π, X]

theorem value_fails :
    ¬ ((1/2 : ℝ) * (∑ w, π w)
        ≤ ∑ w, π w * (if (1/2 : ℝ) ≤ (∑ v, Pr w v * X v) then X w else (1/2 : ℝ))) := by
  rw [value_witness_iff_totalTrust π Pr X (1/2), TT_negative]
  norm_num

end AntiExpert

/-! ## Ledger row: `value_iff_totalTrust_asymptotic`

The inherited statement, in the pinned dependency's `≈ₙ` / `≲ₙ` vocabulary. `hLoe` is
`thm:loe` — linearity of the present expectation over the soft followed strategy
`Ŝ_soft = X·w + s·1 − s·w`.
-/

/-- Ported from inherited `DeferenceConverseAsymp.totalTrust_of_value_asymptotic`. -/
theorem totalTrust_of_value_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : ESsoft ≈ₙ (fun n => Exw n + s * E1 n - s * Ew n))
    (hVal : (fun n => s * E1 n) ≲ₙ ESsoft) :
    (fun n => s * Ew n) ≲ₙ Exw := by
  have h1 : (fun n => s * E1 n) ≲ₙ (fun n => Exw n + s * E1 n - s * Ew n) :=
    hVal.trans_asympEq hLoe
  intro ε hε
  filter_upwards [h1 ε hε] with n hn
  show s * Ew n ≤ Exw n + ε
  linarith

/-- Ported from inherited `DeferenceConverseAsymp.value_of_totalTrust_asymptotic`. -/
theorem value_of_totalTrust_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : ESsoft ≈ₙ (fun n => Exw n + s * E1 n - s * Ew n))
    (hTT : (fun n => s * Ew n) ≲ₙ Exw) :
    (fun n => s * E1 n) ≲ₙ ESsoft := by
  have h1 : (fun n => s * E1 n) ≲ₙ (fun n => Exw n + s * E1 n - s * Ew n) := by
    intro ε hε
    filter_upwards [hTT ε hε] with n hn
    show s * E1 n ≤ (Exw n + s * E1 n - s * Ew n) + ε
    linarith
  exact h1.trans_asympEq hLoe.symm

/-- Ported from inherited `DeferenceConverseAsymp.value_iff_totalTrust_asymptotic`: the
ledger's second Movement-I row. Both arrows from linearity alone; neither hypothesis is the
conclusion. -/
theorem value_iff_totalTrust_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : ESsoft ≈ₙ (fun n => Exw n + s * E1 n - s * Ew n)) :
    ((fun n => s * E1 n) ≲ₙ ESsoft) ↔ ((fun n => s * Ew n) ≲ₙ Exw) :=
  ⟨totalTrust_of_value_asymptotic s Exw Ew E1 ESsoft hLoe,
   value_of_totalTrust_asymptotic s Exw Ew E1 ESsoft hLoe⟩

/-! ## Ledger row: tower ⟹ Value, asymptotic -/

/-- Ported from inherited `DeferenceAsymp.value_asymptotic`. The hypotheses are the named
Logical-Induction results (`thm:loe`, `thm:ccee`, `thm:cee`, `thm:expprovind` through the
softmax gap); the content is the chain. Every calculus step it needs is already in the
pinned dependency's `Framework/Asymptotics`. -/
theorem value_asymptotic
    {J : Type*} [Fintype J] (i : J)
    (ES c δ : ℕ → ℝ) (a b Eo Ee : J → ℕ → ℝ)
    (hAdd1 : ES ≈ₙ (fun n => ∑ j, a j n))
    (hCcee : ∀ j, a j ≈ₙ b j)
    (hAdd2 : (fun n => ∑ j, b j n) ≈ₙ c)
    (hCee : ∀ j, Ee j ≈ₙ Eo j)
    (hδ : ConvergesTo δ 0)
    (hSoft : ∀ᶠ n in atTop, Ee i n ≤ c n + δ n) :
    Eo i ≲ₙ ES := by
  have hES_c : ES ≈ₙ c := hAdd1.trans ((AsympEq.finsetSum hCcee).trans hAdd2)
  have hEd_c : Ee i ≲ₙ c := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hδ ε hε
    filter_upwards [hSoft, eventually_atTop.2 ⟨N, hN⟩] with n hn1 hn2
    have hlt : |δ n| < ε := by simpa [Real.dist_eq] using hn2
    have := (abs_lt.1 hlt).2
    linarith
  exact (((hCee i).symm).asympLE.trans hEd_c).trans_asympEq hES_c.symm

#print axioms decomposition
#print axioms witness_identity
#print axioms value_witness_iff_totalTrust
#print axioms totalTrust_sum_split
#print axioms value_witness_iff_totalTrust_mass
#print axioms value_iff_totalTrust
#print axioms AntiExpert.stationary
#print axioms AntiExpert.TT_negative
#print axioms AntiExpert.value_fails
#print axioms totalTrust_of_value_asymptotic
#print axioms value_of_totalTrust_asymptotic
#print axioms value_iff_totalTrust_asymptotic
#print axioms value_asymptotic

end Workspace.Deference.Contrib.InheritedAlgebra
