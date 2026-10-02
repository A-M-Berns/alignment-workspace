import Cleanroom.Decision.DpWorldsJb.Defs
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Annihilation (T6): the abstract theorem

Appendix A argues on the Lebesgue measure algebra with countable joins designated: atomlessness
gives a decreasing chain of halves of measures `2⁻ⁿ`; a world following the chain holds every
element, and constraint 4 puts the meet (`⊥`) in it. The abstract version here needs only a
**finitely additive** probability that is **strictly positive** with **exact halving**, and the
designation `Jω` of every countable family that has an infimum; no σ-additivity and no quotient
algebra. The chain is built *inside* the world by recursion (the inventory's flag on the
appendix's "a world following the chain"), choosing at each step whichever half the world holds.

`Dyadic.lean` supplies the N+ witness (the dyadic algebra on `[0,1)`).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-- The maximal countable designation: every countable family that has an infimum (including
the empty and the finite families, harmlessly: their infima are finite meets, already members
of every world by constraint 3).
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("with countable joins designated") | dp-core-2-058
Kind: D
Fidelity: exact
Hyps: n/a -/
def Jω (E : Type*) [BooleanAlgebra E] : Designation E :=
  ⟨{D | D.Countable ∧ ∃ m, IsGLB D m}, fun _ hD => hD.2⟩

/-- Strict positivity of a finitely additive probability: `X ≠ ⊥ → 0 < μ X`.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (the measure algebra: Borel mod null)
Kind: D
Fidelity: exact
Hyps: n/a -/
def StrictlyPositive (μ : Prob (∅ : Designation E)) : Prop := ∀ X, X ≠ ⊥ → 0 < μ.P X

/-- Exact halving: every non-`⊥` event contains an event of exactly half its measure.
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("atomlessness yields a decreasing chain of halves")
Kind: D
Fidelity: exact
Hyps: n/a -/
def ExactHalving (μ : Prob (∅ : Designation E)) : Prop :=
  ∀ X, X ≠ ⊥ → ∃ Y, Y ≤ X ∧ μ.P Y = μ.P X / 2

/-- **T6.** If `E` carries a finitely additive probability that is strictly positive with exact
halving, then `(E, Jω)` has **no worlds**: a chain `I 0 = ⊤ ≥ I 1 ≥ ⋯` of members of the
world with `μ (I n) = 2⁻ⁿ` is built by recursion (at each step the world holds exactly one of
the two halves); any lower bound of the chain has measure `0`, hence is `⊥`; so the chain is a
countable family with infimum `⊥`, designated by `Jω`, and constraint 4 puts `⊥` in the world.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (line 327) | dp-core-2-058
Kind: P
Fidelity: stronger: no σ-additivity, no quotient algebra; any countable designation containing
the chain suffices (the appendix's instance is the Lebesgue measure algebra)
Hyps: (a) — strict positivity and exact halving are hypotheses of the theorem, discharged by
the witness in `Dyadic.lean` -/
theorem no_world_of_halving (μ : Prob (∅ : Designation E)) (hpos : StrictlyPositive μ)
    (hhalf : ExactHalving μ) : IsEmpty (World (Jω E)) := by
  refine ⟨fun ω => ?_⟩
  have step : ∀ X : {X : E // X ∈ ω}, ∃ Y : {X : E // X ∈ ω}, Y.1 ≤ X.1 ∧ μ.P Y.1 = μ.P X.1 / 2 := by
    rintro ⟨X, hX⟩
    have hXne : X ≠ ⊥ := fun h => ω.bot_notMem (h ▸ hX)
    obtain ⟨Y, hYX, hμY⟩ := hhalf X hXne
    have hsplit : Y ⊔ (X \ Y) = X := sup_sdiff_cancel_right hYX
    have hXω : Y ⊔ (X \ Y) ∈ ω := by rw [hsplit]; exact hX
    rcases ω.mem_or_mem_of_sup_mem hXω with hY | hY
    · exact ⟨⟨Y, hY⟩, hYX, hμY⟩
    · refine ⟨⟨X \ Y, hY⟩, sdiff_le, ?_⟩
      have := μ.add Y (X \ Y) disjoint_sdiff_self_right
      rw [hsplit] at this
      show μ.P (X \ Y) = μ.P X / 2
      linarith
  choose next hnext using step
  let I : ℕ → {X : E // X ∈ ω} := fun n => next^[n] ⟨⊤, ω.top_mem⟩
  have hI : ∀ n, μ.P (I n).1 = (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      show μ.P ⊤ = _
      rw [μ.top, pow_zero]
    | succ n ih =>
      have hstep : I (n + 1) = next (I n) := Function.iterate_succ_apply' next n _
      rw [hstep, (hnext _).2, pow_succ, ih]
      ring
  have hglb : IsGLB (Set.range fun n => (I n).1) ⊥ := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact bot_le
    · intro b hb
      by_contra hcon
      have hbne : b ≠ ⊥ := fun h => hcon (le_of_eq h)
      have hpos' := hpos b hbne
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos' (by norm_num : (1 / 2 : ℝ) < 1)
      have := μ.mono (hb ⟨n, rfl⟩)
      rw [hI n] at this
      linarith
  have hD : Set.range (fun n => (I n).1) ∈ (Jω E).1 := ⟨Set.countable_range _, ⊥, hglb⟩
  have := ω.designated _ hD (by rintro _ ⟨n, rfl⟩; exact (I n).2) ⊥ hglb
  exact ω.bot_notMem this

/-- Under strict positivity and exact halving, `E` is atomless: every non-`⊥` event has a
non-`⊥` proper sub-event (so the annihilation hypotheses are not an artifact of atoms).
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("atomlessness")
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem atomless_of_halving (μ : Prob (∅ : Designation E)) (hpos : StrictlyPositive μ)
    (hhalf : ExactHalving μ) : ∀ X : E, X ≠ ⊥ → ∃ Y, Y ≤ X ∧ Y ≠ ⊥ ∧ Y ≠ X := by
  intro X hX
  obtain ⟨Y, hYX, hμ⟩ := hhalf X hX
  have hpX := hpos X hX
  refine ⟨Y, hYX, ?_, ?_⟩
  · intro h
    rw [h, μ.bot] at hμ
    linarith
  · intro h
    rw [h] at hμ
    linarith

end

end Cleanroom.Decision.DpWorldsJb
