import Cleanroom.Decision.DpWorldsJb

/-!
# dp-worlds-jb — audit round 2, adversarial lens: T6's witness annihilates probabilities too

Not imported by the library.

**Claim probed.** Round 1 (N2) observed that the N+ witness for `no_world_of_halving` is the
*countable* dyadic algebra `Dy`, on which annihilation of worlds needs no measure
(`no_world_of_countable_atomless`, now in the library). This probe sharpens that: on a countable
atomless Boolean algebra the designation `Jω` (every countable family with an infimum) leaves
**no probabilities at all**, not just no worlds — `IsEmpty (Prob (Jω E))`. In particular
`Prob (Jω Dy)` is empty: Lebesgue measure on `Dy` (`dyProb : Prob ∅`) is not continuous along
the designated meets, and nothing else is either.

Why it matters for the record. Appendix A's annihilation runs on the Lebesgue measure algebra,
where Lebesgue measure *is* a `Jω`-probability (σ-additivity on a σ-complete algebra), and v2 §1
(line 24) describes that "pointless regime" as one where `Δ(Ω)` names distributions on an empty
set **while `Δ(𝒜)` is nonempty**. The package's variant witness `Dy` is not in that regime: on
`Dy` the designation kills `Δ(𝒜)` as well, so the worlds/probabilities contrast that Appendix A
is about is exhibited by no witness in the package. The theorem below is offered as the record
of that (the same diagonal argument as `exists_atom_mem_of_countable`, run twice: once to show a
`Jω`-probability puts arbitrarily small mass below every non-`⊥` event, once to build a chain of
mass `> 1/2` with infimum `⊥`).

Proof sketch. Enumerate `E = range e`. (1) For `a ≠ ⊥`: build `a = Y₀ ≥ Y₁ ≥ ⋯` of non-`⊥`
elements with `eₙ ≰ Yₙ₊₁` whenever `eₙ ≠ ⊥` (cut a proper non-`⊥` part of `eₙ` out of `Yₙ` when
`eₙ ≤ Yₙ`); the chain's only lower bound is `⊥`, so `cont` forces `inf P (Yₙ) = 0`. (2) Build
`⊤ = Z₀ ≥ Z₁ ≥ ⋯` with `eₙ ≰ Zₙ₊₁` whenever `eₙ ≠ ⊥`, cutting out a part of mass `< 2⁻ⁿ⁻²` by
(1), so `P (Zₙ) > 1/2` throughout; the chain's only lower bound is `⊥`, so `cont` forces
`inf P (Zₙ) = 0`. Contradiction.
-/

namespace Cleanroom.Decision.DpWorldsJb.AuditR2

open Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-- Every finite sub-meet of an antitone chain is bounded below by a member of the chain. -/
theorem chain_finset_inf {Z : ℕ → E} (hZ : Antitone Z) (F : Finset E)
    (hF : ↑F ⊆ Set.range Z) : ∃ N, Z N ≤ F.inf id := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by rw [Finset.inf_empty]; exact le_top⟩
  | insert a s _ ih =>
    obtain ⟨N, hN⟩ := ih fun x hx =>
      hF (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
    obtain ⟨k, hk⟩ := hF (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    refine ⟨max k N, ?_⟩
    rw [Finset.inf_insert]
    have h1 : Z (max k N) ≤ a := by rw [← hk]; exact hZ (le_max_left k N)
    exact le_inf h1 (le_trans (hZ (le_max_right k N)) hN)

/-- A chain that dodges every element of an enumeration (`eₙ ≰ Zₙ₊₁` for non-`⊥` `eₙ`) has
infimum `⊥`. -/
theorem isGLB_bot_of_dodge {e : ℕ → E} (he : Function.Surjective e) {Z : ℕ → E}
    (hdodge : ∀ n, e n ≠ ⊥ → ¬ e n ≤ Z (n + 1)) : IsGLB (Set.range Z) ⊥ := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact bot_le
  · intro b hb
    by_contra hcon
    have hbne : b ≠ ⊥ := fun h => hcon (le_of_eq h)
    obtain ⟨n, rfl⟩ := he b
    exact hdodge n hbne (hb ⟨n + 1, rfl⟩)

/-- Along an antitone chain with infimum `⊥`, a `Jω`-probability takes values below any
`ε > 0` (continuity along the designated meet). -/
theorem exists_lt_of_chain (P : Prob (Jω E)) {Z : ℕ → E} (hZ : Antitone Z)
    (hglb : IsGLB (Set.range Z) ⊥) {ε : ℝ} (hε : 0 < ε) : ∃ N, P.P (Z N) < ε := by
  have hD : Set.range Z ∈ (Jω E).1 := ⟨Set.countable_range _, ⊥, hglb⟩
  have hc := P.cont _ hD ⊥ hglb
  rw [P.bot] at hc
  by_contra hcon
  push Not at hcon
  have hlb : ε ∈ lowerBounds {r | ∃ F : Finset E, ↑F ⊆ Set.range Z ∧ r = P.P (F.inf id)} := by
    rintro _ ⟨F, hF, rfl⟩
    obtain ⟨N, hN⟩ := chain_finset_inf hZ F hF
    exact le_trans (hcon N) (P.mono hN)
  have := hc.2 hlb
  linarith

/-- `Y ≤ Z \ Y` forces `Y = ⊥`. -/
theorem eq_bot_of_le_sdiff {Y Z : E} (h : Y ≤ Z \ Y) : Y = ⊥ := by
  have h2 : Y ≤ Yᶜ := le_trans h (by rw [sdiff_eq]; exact inf_le_right)
  have h3 : Y ≤ Y ⊓ Yᶜ := le_inf le_rfl h2
  rw [inf_compl_eq_bot] at h3
  exact le_bot_iff.1 h3

/-- **Step (1).** On a countable atomless algebra a `Jω`-probability puts arbitrarily small mass
below every non-`⊥` event. -/
theorem exists_small_below [Countable E] (hat : ∀ X : E, X ≠ ⊥ → ∃ Y, Y < X ∧ Y ≠ ⊥)
    (P : Prob (Jω E)) (a : E) (ha : a ≠ ⊥) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y, Y ≤ a ∧ Y ≠ ⊥ ∧ P.P Y < ε := by
  haveI : Nonempty E := ⟨⊤⟩
  obtain ⟨e, he⟩ := exists_surjective_nat E
  have step : ∀ (n : ℕ) (Y : {Y : E // Y ≤ a ∧ Y ≠ ⊥}),
      ∃ Y' : {Y : E // Y ≤ a ∧ Y ≠ ⊥}, Y'.1 ≤ Y.1 ∧ (e n ≠ ⊥ → ¬ e n ≤ Y'.1) := by
    rintro n ⟨Y, hYa, hY⟩
    by_cases h : e n ≠ ⊥ ∧ e n ≤ Y
    · obtain ⟨Z, hZlt, hZne⟩ := hat (e n) h.1
      have hne : Y \ Z ≠ ⊥ := by
        intro h0
        have hle : e n \ Z ≤ Y \ Z := sdiff_le_sdiff_right h.2
        rw [h0] at hle
        exact lt_irrefl _ (lt_of_le_of_lt (sdiff_eq_bot_iff.1 (le_bot_iff.1 hle)) hZlt)
      refine ⟨⟨Y \ Z, le_trans sdiff_le hYa, hne⟩, sdiff_le, fun _ hle => ?_⟩
      exact hZne (eq_bot_of_le_sdiff (le_trans hZlt.le hle))
    · push Not at h
      exact ⟨⟨Y, hYa, hY⟩, le_rfl, h⟩
  choose next hnext using step
  let Y : ℕ → {Y : E // Y ≤ a ∧ Y ≠ ⊥} := fun n =>
    Nat.rec (motive := fun _ => {Y : E // Y ≤ a ∧ Y ≠ ⊥}) ⟨a, le_rfl, ha⟩ (fun n Yn => next n Yn) n
  have hanti : Antitone (fun n => (Y n).1) := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hnext n (Y n)).1
  have hdodge : ∀ n, e n ≠ ⊥ → ¬ e n ≤ (Y (n + 1)).1 := fun n => (hnext n (Y n)).2
  obtain ⟨N, hN⟩ := exists_lt_of_chain P hanti (isGLB_bot_of_dodge he hdodge) hε
  exact ⟨(Y N).1, (Y N).2.1, (Y N).2.2, hN⟩

/-- **A countable atomless Boolean algebra with `Jω` designated has no probabilities at all**
(so, through T1, no worlds either — `no_world_of_countable_atomless` is the two-valued case). -/
theorem no_prob_of_countable_atomless [Countable E]
    (hat : ∀ X : E, X ≠ ⊥ → ∃ Y, Y < X ∧ Y ≠ ⊥) : IsEmpty (Prob (Jω E)) := by
  refine ⟨fun P => ?_⟩
  haveI : Nonempty E := ⟨⊤⟩
  obtain ⟨e, he⟩ := exists_surjective_nat E
  have step : ∀ (n : ℕ) (Z : E), ∃ Z', Z' ≤ Z ∧
      P.P Z - (1 / 2 : ℝ) ^ (n + 2) < P.P Z' ∧ (e n ≠ ⊥ → ¬ e n ≤ Z') := by
    intro n Z
    have hpow : (0 : ℝ) < (1 / 2) ^ (n + 2) := by positivity
    by_cases h : e n ≠ ⊥ ∧ e n ≤ Z
    · obtain ⟨W, hWe, hWne, hWlt⟩ := exists_small_below hat P (e n) h.1 hpow
      refine ⟨Z \ W, sdiff_le, ?_, fun _ hle => ?_⟩
      · have hadd := P.add (Z \ W) W disjoint_sdiff_self_left
        rw [sdiff_sup_cancel (le_trans hWe h.2)] at hadd
        linarith
      · exact hWne (eq_bot_of_le_sdiff (le_trans hWe hle))
    · push Not at h
      exact ⟨Z, le_rfl, by linarith, h⟩
  choose next hnext using step
  let Z : ℕ → E := fun n => Nat.rec (motive := fun _ => E) ⊤ (fun n Zn => next n Zn) n
  have hanti : Antitone Z := antitone_nat_of_succ_le fun n => (hnext n (Z n)).1
  have hdodge : ∀ n, e n ≠ ⊥ → ¬ e n ≤ Z (n + 1) := fun n => (hnext n (Z n)).2.2
  have hlow : ∀ n, (1 / 2 : ℝ) + (1 / 2) ^ (n + 1) ≤ P.P (Z n) := by
    intro n
    induction n with
    | zero =>
      show (1 / 2 : ℝ) + (1 / 2) ^ 1 ≤ P.P ⊤
      rw [P.top]
      norm_num
    | succ n ih =>
      have h1 := (hnext n (Z n)).2.1
      have e1 : (1 / 2 : ℝ) ^ (n + 1) - (1 / 2) ^ (n + 2) = (1 / 2) ^ (n + 2) := by ring
      show (1 / 2 : ℝ) + (1 / 2) ^ (n + 2) ≤ P.P (next n (Z n))
      linarith
  obtain ⟨N, hN⟩ := exists_lt_of_chain P hanti (isGLB_bot_of_dodge he hdodge)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h1 := hlow N
  have h2 : (0 : ℝ) < (1 / 2) ^ (N + 1) := by positivity
  linarith

/-- The two-valued case re-derived through T1: no worlds either. -/
theorem no_world_of_no_prob [Countable E] (hat : ∀ X : E, X ≠ ⊥ → ∃ Y, Y < X ∧ Y ≠ ⊥) :
    IsEmpty (World (Jω E)) :=
  ⟨fun ω => (no_prob_of_countable_atomless hat).false ω.toProb⟩

/-- **The dyadic witness is outside Appendix A's regime.** On `Dy` with `Jω` designated there are
no worlds *and no probabilities*: `Δ(Ω)` and `Δ(𝒜)` are both empty, whereas v2 §1 (line 24)
describes the pointless regime of Appendix A (the Lebesgue measure algebra) as `Δ(Ω)` empty
with `Δ(𝒜)` nonempty. In particular Lebesgue measure on `Dy` (`dyProb`) is not a `Jω`-probability. -/
theorem dyadic_no_prob : IsEmpty (Prob (Jω Dy)) :=
  no_prob_of_countable_atomless fun X hX =>
    let ⟨Y, h1, h2, h3⟩ := dyadic_atomless X hX
    ⟨Y, lt_of_le_of_ne h1 h3, h2⟩

theorem dyadic_both_empty : IsEmpty (World (Jω Dy)) ∧ IsEmpty (Prob (Jω Dy)) :=
  ⟨dyadic_no_world, dyadic_no_prob⟩

theorem dyProb_not_Jω_continuous : ¬ ∃ Q : Prob (Jω Dy), Q.P = dyProb.P :=
  fun ⟨Q, _⟩ => dyadic_no_prob.false Q

end

end Cleanroom.Decision.DpWorldsJb.AuditR2
