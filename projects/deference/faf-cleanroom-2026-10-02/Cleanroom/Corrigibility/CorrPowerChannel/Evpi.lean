import Cleanroom.Corrigibility.CorrPowerChannel.Power
import Mathlib.Data.Fin.VecNotation

/-!
# `corr-power-channel` — T2: S1 — `VOI ≤ EVPI`, non-monotonicity, the coarsened ceiling

* **(a)** `voiExp_le_evpi`: the VOI of every experiment is at most the EVPI of the continuation
  set (signal-wise maximum ≤ pointwise maximum, summed); `voiExp_nonneg` (Good's theorem: the
  constant decision rule is feasible). Consequence `j3_of_coverage`: D18's coverage form implies
  J3 for every new option.
* **(b)** `power_mono` (Power.lean) against `evpi_not_mono`: E1 — two equiprobable hypotheses,
  `b₁ = (1,0)`, `b₂ = (0,1)`, `c = (1,1)`: `EVPI{b₁,b₂} = 1/2`, `EVPI{b₁,b₂,c} = 0`.
* **(c)** `evpi_le_one_sub_prob_class`: the coarsened concentration ceiling — for values in
  `[0,1]` and a class `C` on which `V_ω` agrees on `B`, `EVPI(B) ≤ 1 − P(C)`; singleton corollary
  `evpi_le_one_sub_mass`; witness R1 (six uniform hypotheses, two classes, `EVPI = 1/2`, naive
  bound `5/6`, coarsened `1/2`).
* **(d)** `d17_not_power_le_wisdom`: `EVPI = 0` with `reach = 1` — D17 is not "power ≤ f(wisdom)".
* **(e)** `capObjAvg_admits_catastrophe`: the develop file's time-averaged `Π^obj` passes a
  trajectory with one unit-regret step among 100 (`1/100 ≤ 1/50`) that the sup-norm form
  `CapObjTraj` rejects.

Sources: power-wisdom-final.md S1 (l. 99), P1 (l. 143–155); power-wisdom-adversary.md D.3, D.4,
S1.1–S1.3 (l. 10–26); scripts E1, E2c, A3, A5, R1, R4; the develop file `power-wisdom.md` D17
(l. 77).
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrCautionPower (harmOf harmOf_nonneg harmOf_nul)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

variable {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω]

/-! ## (a) `VOI ≤ EVPI` and `0 ≤ VOI` -/

/-- Rows of an experiment sum to one: `∑ s, k ω s = 1`. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem experiment_row_sum {S : Type} [Fintype S] (k : Experiment Ω S) (ω : Ω) :
    ∑ s, k.k ω s = 1 := (k.k_mem ω).2

/-- Rows of an experiment are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem experiment_nonneg {S : Type} [Fintype S] (k : Experiment Ω S) (ω : Ω) (s : S) :
    0 ≤ k.k ω s := (k.k_mem ω).1 s

/-- The informed value of an experiment is at most `POWER_P(B)`: for each signal, the maximum of
the signal-weighted mixture is at most the signal-weighted maximum (Jensen), and the signal
weights sum to one.
Source: power-wisdom-final.md P1 (l. 143, "VOI bound")
Kind: L
Fidelity: n/a -/
theorem informed_le_power {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ)
    (k : Experiment Ω S) {B : Finset A} (hB : B.Nonempty) :
    (∑ s, B.sup' hB (fun b => ∑ ω, P.mass ω * k.k ω s * V ω b)) ≤ power P V B hB := by
  have h1 : ∀ s, B.sup' hB (fun b => ∑ ω, P.mass ω * k.k ω s * V ω b) ≤
      ∑ ω, P.mass ω * k.k ω s * attainable V B hB ω := fun s =>
    sup'_sum_le_sum_sup'_finset hB (p := fun ω => P.mass ω * k.k ω s)
      (fun ω => mul_nonneg (P.nonneg ω) (experiment_nonneg k ω s)) (fun ω b => V ω b)
  refine le_trans (sum_le_sum fun s _ => h1 s) (le_of_eq ?_)
  unfold power expect
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [show ∑ s, P.mass ω * k.k ω s * attainable V B hB ω =
      P.mass ω * attainable V B hB ω * ∑ s, k.k ω s by
    rw [mul_sum]; exact sum_congr rfl fun s _ => by ring]
  rw [experiment_row_sum, mul_one]

/-- **S1: `VOI_t(a) ≤ EVPI_t(A′)` for every experiment** — the signal-wise maximum is at most the
pointwise maximum, summed over signals.
Source: power-wisdom-final.md S1 (l. 99, "`VOI_t(a) ≤ EVPI_t(A′)`"); D16 (l. 73)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_le_evpi {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ) (k : Experiment Ω S)
    {B : Finset A} (hB : B.Nonempty) : voiExp P V k B hB ≤ evpi P V B hB :=
  sub_le_sub_right (informed_le_power P V k hB) _

/-- **Good's theorem for `voiExp`: `0 ≤ VOI`** — the constant decision rule that picks the best
mixture act on every signal is feasible.
Source: power-wisdom-final.md D16 (l. 73, "`0 ≤ VOI_t(a)`"); Good 1967
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_nonneg {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ) (k : Experiment Ω S)
    {B : Finset A} (hB : B.Nonempty) : 0 ≤ voiExp P V k B hB := by
  unfold voiExp bestMix
  rw [sub_nonneg, sup'_le_iff]
  intro b hb
  have e : mixValue P V b = ∑ s, ∑ ω, P.mass ω * k.k ω s * V ω b := by
    unfold mixValue expect
    rw [sum_comm]
    refine sum_congr rfl fun ω _ => ?_
    rw [show ∑ s, P.mass ω * k.k ω s * V ω b = P.mass ω * V ω b * ∑ s, k.k ω s by
      rw [mul_sum]; exact sum_congr rfl fun s _ => by ring]
    rw [experiment_row_sum, mul_one]
  rw [e]
  exact sum_le_sum fun s _ => le_sup' (fun b => ∑ ω, P.mass ω * k.k ω s * V ω b) hb

/-- **The coverage form of J3 is sufficient**: if `EVPI_t(B) < min_{a∈N}(E[harm] − E[g])` then
J3 holds for every `a ∈ N` and every experiment `k` (since `VOI ≤ EVPI`). Plumbing on
`voiExp_le_evpi` (`inf'_le` and `linarith`): the content is that theorem's.
Source: power-wisdom-final.md D18 (l. 83, "Coverage form (sufficient, from `VOI ≤ EVPI`)")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem j3_of_coverage {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ) (k : Experiment Ω S)
    (nul : A) {N : Finset A} (hN : N.Nonempty) {B : Finset A} (hB : B.Nonempty)
    (h : J3Coverage P V nul N hN B hB) {a : A} (ha : a ∈ N) : J3 P V k a nul B hB := by
  unfold J3Coverage at h
  unfold J3
  have h1 := voiExp_le_evpi P V k hB
  have h2 : N.inf' hN (fun a => expect P (fun ω => harmOf nul (V ω) a) -
      expect P (fun ω => gainOf nul (V ω) a)) ≤
      expect P (fun ω => harmOf nul (V ω) a) - expect P (fun ω => gainOf nul (V ω) a) :=
    inf'_le _ ha
  linarith

/-! ## Finite helpers -/

/-- Expectation on `Fin 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_fin2 (μ : Distr (Fin 2)) (X : Fin 2 → ℝ) :
    expect μ X = μ.mass 0 * X 0 + μ.mass 1 * X 1 := by
  simp [expect, Fin.sum_univ_two]

/-- The uniform mass on `Fin n`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem uniform_mass_fin {n : ℕ} [NeZero n] (a : Fin n) :
    (Distr.uniform : Distr (Fin n)).mass a = (n : ℝ)⁻¹ := by
  simp [Distr.uniform]

/-- `sup'` over a pair is `max`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_pair' {a b : A} (f : A → ℝ) (h : ({a, b} : Finset A).Nonempty) :
    ({a, b} : Finset A).sup' h f = max (f a) (f b) := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (by simp)) (le_sup' f (by simp))

/-- `sup'` over a triple is an iterated `max`. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem sup'_triple {a b c : A} (f : A → ℝ) (h : ({a, b, c} : Finset A).Nonempty) :
    ({a, b, c} : Finset A).sup' h f = max (f a) (max (f b) (f c)) := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact max_le (le_sup' f (by simp)) (max_le (le_sup' f (by simp)) (le_sup' f (by simp)))

/-- Index `2` of a three-vector. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

/-- `![a, b, c] ⟨0, _⟩ = a` (the `Fin.mk` form `fin_cases` produces).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec3_mk_zero {α : Type} (a b c : α) (h : 0 < 3) :
    (![a, b, c] : Fin 3 → α) ⟨0, h⟩ = a := rfl

/-- `![a, b, c] ⟨1, _⟩ = b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec3_mk_one {α : Type} (a b c : α) (h : 1 < 3) :
    (![a, b, c] : Fin 3 → α) ⟨1, h⟩ = b := rfl

/-- `![a, b, c] ⟨2, _⟩ = c`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec3_mk_two {α : Type} (a b c : α) (h : 2 < 3) :
    (![a, b, c] : Fin 3 → α) ⟨2, h⟩ = c := rfl

/-- `![a, b, c] 2 = c` for any `α`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec3_two' {α : Type} (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl

/-! ## (b) E1 — POWER monotone, EVPI not -/

/-- E1's value table on `Ω = Fin 2`, `A = Fin 3`: `b₁ = 0 ↦ (1, 0)`, `b₂ = 1 ↦ (0, 1)`,
`c = 2 ↦ (1, 1)` (hypothesis-indexed rows).
Source: power-wisdom-final.md P1 (l. 143, E1); script E1
Kind: D
Fidelity: n/a (witness) -/
def e1V : Fin 2 → Fin 3 → ℝ := ![![1, 0, 1], ![0, 1, 1]]

/-- **E1 (N+):** under the uniform posterior, `EVPI{b₁, b₂} = 1/2` and `EVPI{b₁, b₂, c} = 0`: a
dominant option sends the residual to `0` while the option set grew. Non-degenerate: two
hypotheses of positive weight, a value-contested pair, a strict drop.
Source: power-wisdom-final.md S1(ii) (l. 99); P1 (l. 143); script E1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e1_evpi :
    evpi (Distr.uniform : Distr (Fin 2)) e1V {0, 1} (by simp) = 1 / 2 ∧
      evpi (Distr.uniform : Distr (Fin 2)) e1V {0, 1, 2} (by simp) = 0 := by
  constructor
  · simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, uniform_mass_fin,
      sup'_pair', e1V]
    norm_num
  · simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, uniform_mass_fin,
      sup'_triple, e1V]
    norm_num

/-- **S1(ii): EVPI is not monotone in the option set** (while POWER is, `power_mono`): there are
a posterior, a value table and nested option sets with the residual strictly decreasing.
Source: power-wisdom-final.md S1(ii) (l. 99, "a dominant option sends it to `0`")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem evpi_not_mono :
    ¬ ∀ {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω] (P : Distr Ω) (V : Ω → A → ℝ)
      (B B' : Finset A) (hB : B.Nonempty) (hB' : B'.Nonempty), B ⊆ B' →
        evpi P V B hB ≤ evpi P V B' hB' := by
  intro h
  have := h (Distr.uniform : Distr (Fin 2)) e1V {0, 1} {0, 1, 2} (by simp) (by simp)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp)
  rw [e1_evpi.1, e1_evpi.2] at this
  norm_num at this

/-! ## (c) The coarsened concentration ceiling -/

/-- `P(C) = ∑_{ω∈C} P ω` for a `Finset` event. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem prob_finset (P : Distr Ω) (C : Finset Ω) : P.prob (↑C : Set Ω) = ∑ ω ∈ C, P.mass ω := by
  classical
  unfold Distr.prob
  rw [← sum_filter_add_sum_filter_not univ (fun ω => ω ∈ C)]
  rw [sum_eq_zero (s := univ.filter (fun ω => ¬ ω ∈ C)) (fun ω hω => by
    simp only [mem_filter, mem_univ, true_and] at hω
    simp [Set.indicator_apply, hω]), add_zero]
  rw [filter_mem_eq_inter, univ_inter]
  exact sum_congr rfl fun ω hω => by simp [Set.indicator_apply, hω]

/-- `POWER ≤ 1` for values in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem power_le_one (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A}
    (hV : ∀ ω, ∀ a ∈ B, V ω a ∈ Set.Icc (0 : ℝ) 1) (hB : B.Nonempty) : power P V B hB ≤ 1 := by
  unfold power
  calc expect P (attainable V B hB) ≤ expect P (fun _ => 1) :=
        expect_mono P fun ω => by
          unfold attainable; rw [sup'_le_iff]; intro a ha; exact (hV ω a ha).2
    _ = 1 := expect_const P 1

/-- `0 ≤ bestMix` for values in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem bestMix_nonneg (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A}
    (hV : ∀ ω, ∀ a ∈ B, V ω a ∈ Set.Icc (0 : ℝ) 1) (hB : B.Nonempty) : 0 ≤ bestMix P V B hB := by
  obtain ⟨a, ha⟩ := hB
  exact le_trans (expect_nonneg P fun ω => (hV ω a ha).1) (le_sup' (mixValue P V) ha)

/-- **S1(iii′): the coarsened concentration ceiling.** For values in `[0, 1]` on `B` and any class
`C ⊆ Ω` on which the value profile agrees on `B` (`V_ω = V_ω′` on `B` for `ω, ω′ ∈ C`),
`EVPI_t(B) ≤ 1 − P(C)`. Proof as P1(iii′): the class-optimal act `aDag` is feasible for the
mixture, so `EVPI ≤ ∑_{ω∉C} P(ω)(AV(ω) − V_ω(aDag)) ≤ 1 − P(C)`; the class's own terms vanish. The
class is the *user's* choice of `C` — "maximal mass" is not computed here.
Source: power-wisdom-final.md S1(iii′) (l. 99); P1 (l. 143); power-wisdom-adversary.md S1.3
Kind: P
Fidelity: exact
Hyps: (a) the range hypothesis (on `B` only — repair round 1, fidelity N11) and the agreement
property of `C` are named -/
theorem evpi_le_one_sub_prob_class (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A}
    (hV : ∀ ω, ∀ a ∈ B, V ω a ∈ Set.Icc (0 : ℝ) 1) (hB : B.Nonempty) (C : Finset Ω)
    (hC : ∀ ω ∈ C, ∀ ω' ∈ C, ∀ a ∈ B, V ω a = V ω' a) :
    evpi P V B hB ≤ 1 - P.prob (↑C : Set Ω) := by
  classical
  rw [prob_finset]
  rcases C.eq_empty_or_nonempty with hCe | ⟨ω₀, hω₀⟩
  · subst hCe
    simp only [sum_empty, sub_zero]
    unfold evpi
    linarith [power_le_one P V hV hB, bestMix_nonneg P V hV hB]
  -- the class-optimal act
  obtain ⟨aDag, haDag, hatt⟩ := exists_mem_eq_sup' hB (V ω₀)
  have hle : bestMix P V B hB ≥ mixValue P V aDag := le_sup' (mixValue P V) haDag
  have hstep : evpi P V B hB ≤ expect P (fun ω => attainable V B hB ω - V ω aDag) := by
    rw [expect_sub]
    have hp : power P V B hB = expect P (attainable V B hB) := rfl
    have hm : mixValue P V aDag = expect P (fun ω => V ω aDag) := rfl
    unfold evpi; linarith
  refine le_trans hstep ?_
  unfold expect
  rw [← sum_filter_add_sum_filter_not univ (fun ω => ω ∈ C)]
  have hin : ∑ ω ∈ univ.filter (fun ω => ω ∈ C), P.mass ω * (attainable V B hB ω - V ω aDag) = 0 := by
    refine sum_eq_zero fun ω hω => ?_
    simp only [mem_filter, mem_univ, true_and] at hω
    have e1 : attainable V B hB ω = attainable V B hB ω₀ := by
      unfold attainable
      exact sup'_congr hB rfl fun a ha => hC ω hω ω₀ hω₀ a ha
    have e2 : V ω aDag = V ω₀ aDag := hC ω hω ω₀ hω₀ aDag haDag
    rw [e1, e2, attainable, ← hatt, sub_self, mul_zero]
  rw [hin, zero_add]
  have hout : ∑ ω ∈ univ.filter (fun ω => ¬ ω ∈ C), P.mass ω * (attainable V B hB ω - V ω aDag) ≤
      ∑ ω ∈ univ.filter (fun ω => ¬ ω ∈ C), P.mass ω := by
    refine sum_le_sum fun ω _ => ?_
    have h1 : attainable V B hB ω ≤ 1 := by
      unfold attainable; rw [sup'_le_iff]; intro a ha; exact (hV ω a ha).2
    have h2 : 0 ≤ V ω aDag := (hV ω aDag haDag).1
    calc P.mass ω * (attainable V B hB ω - V ω aDag) ≤ P.mass ω * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (P.nonneg ω)
      _ = P.mass ω := mul_one _
  refine le_trans hout (le_of_eq ?_)
  have htot := P.sum_eq_one
  rw [← sum_filter_add_sum_filter_not univ (fun ω => ω ∈ C)] at htot
  rw [filter_mem_eq_inter, univ_inter] at htot
  linarith

/-- **The develop file's bound as the singleton case**: `EVPI_t(B) ≤ 1 − P(ω₀)` for every
`ω₀` (the class `{ω₀}`); hence `≤ 1 − max_ω P(ω)`. Vacuous under non-dogmatism over a rich `W`
(S1.3) — the coarsened form is the one that carries content. One instantiation of
`evpi_le_one_sub_prob_class` at the class `{ω₀}`.
Source: power-wisdom-final.md S1(iii′) (l. 99, "the develop file's bound … special case")
Kind: L
Fidelity: exact
Hyps: (a) the range hypothesis -/
theorem evpi_le_one_sub_mass (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A}
    (hV : ∀ ω, ∀ a ∈ B, V ω a ∈ Set.Icc (0 : ℝ) 1) (hB : B.Nonempty) (ω₀ : Ω) :
    evpi P V B hB ≤ 1 - P.mass ω₀ := by
  have := evpi_le_one_sub_prob_class P V hV hB {ω₀} (by
    intro ω hω ω' hω' a _
    simp only [mem_singleton] at hω hω'
    rw [hω, hω'])
  rwa [prob_finset, sum_singleton] at this

/-- R1's value table on `Ω = Fin 6`, `A = Fin 3` (`b₁ = 0`, `b₂ = 1`, `∅ = 2`): hypotheses `0,1,2`
value `b₁`, hypotheses `3,4,5` value `b₂`; the null is worth `0`.
Source: power-wisdom-final.md P1 (l. 143, R1); script R1
Kind: D
Fidelity: n/a (witness) -/
def r1V : Fin 6 → Fin 3 → ℝ := fun ω => if (ω : ℕ) < 3 then ![1, 0, 0] else ![0, 1, 0]

/-- Expectation on `Fin 6`, expanded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_fin6 (μ : Distr (Fin 6)) (X : Fin 6 → ℝ) :
    expect μ X = μ.mass 0 * X 0 + μ.mass 1 * X 1 + μ.mass 2 * X 2 + μ.mass 3 * X 3 +
      μ.mass 4 * X 4 + μ.mass 5 * X 5 := by
  simp [expect, Fin.sum_univ_succ]
  ring

/-- **R1 (N+): the coarsened ceiling is tight where the naive one is loose.** Six equiprobable
hypotheses collapsing to two decision-equivalence classes on `B = {b₁, b₂, ∅}`:
`EVPI = 1/2`; the naive bound `1 − max_ω P(ω) = 5/6`; the coarsened bound with `C = {0,1,2}` is
`1 − 1/2 = 1/2` and is attained. The class `{0,1,2}` is verified to satisfy the agreement
hypothesis of `evpi_le_one_sub_prob_class`.
Source: power-wisdom-final.md S1(iii′) (l. 99, "R1"); script R1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem r1_coarsened :
    evpi (Distr.uniform : Distr (Fin 6)) r1V {0, 1, 2} (by simp) = 1 / 2 ∧
      (∀ ω ∈ ({0, 1, 2} : Finset (Fin 6)), ∀ ω' ∈ ({0, 1, 2} : Finset (Fin 6)),
        ∀ a ∈ ({0, 1, 2} : Finset (Fin 3)), r1V ω a = r1V ω' a) ∧
      (Distr.uniform : Distr (Fin 6)).prob (↑({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6)) = 1 / 2 ∧
      1 - (Distr.uniform : Distr (Fin 6)).mass 0 = 5 / 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evpi, power, bestMix, attainable, mixValue, expect_fin6, uniform_mass_fin,
      sup'_triple, r1V]
    norm_num
  · intro ω hω ω' hω' a _
    simp only [mem_insert, mem_singleton] at hω hω'
    rcases hω with rfl | rfl | rfl <;> rcases hω' with rfl | rfl | rfl <;> rfl
  · rw [prob_finset]
    simp [uniform_mass_fin]
    norm_num
  · simp [uniform_mass_fin]
    norm_num

/-! ## (d) D17 is not "power ≤ f(wisdom)" -/

/-- The D.4 value table: `Ω = Fin 2`, `A = Fin 3` with `∅ = 0` worth `0`, `c = 1` worth `1` under
both hypotheses, `t = 2` worth `0` under `ω₀` and `−1` under `ω₁`.
Source: power-wisdom-adversary.md D.4 (l. 21)
Kind: D
Fidelity: n/a (witness) -/
def d4V : Fin 2 → Fin 3 → ℝ := ![![0, 1, 0], ![0, 1, -1]]

/-- **D.4 (N+): the subjective cap passes an agent of total ignorance with maximal reach.** Under
the uniform posterior with one option worth `1` under both hypotheses, `EVPI(A) = 0 ≤ θ` for
every `θ ≥ 0`, while `reach = 1` (option `t` harms goal `ω₁` by `1`). So `CapSubj` holds at
every tolerance and says nothing about reach: D17 is not of the form "power ≤ f(wisdom)".
Source: power-wisdom-adversary.md D.4 (l. 21); power-wisdom-final.md D17 (l. 79, "two-sided form")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem d17_not_power_le_wisdom :
    evpi (Distr.uniform : Distr (Fin 2)) d4V univ univ_nonempty = 0 ∧
      reach d4V 0 univ univ_nonempty univ univ_nonempty = 1 ∧
      ∀ θ : ℝ, 0 ≤ θ → CapSubj (Distr.uniform : Distr (Fin 2)) d4V univ univ_nonempty θ := by
  have hu3 : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hu2 : (univ : Finset (Fin 2)) = {0, 1} := by decide
  have he : evpi (Distr.uniform : Distr (Fin 2)) d4V univ univ_nonempty = 0 := by
    simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, uniform_mass_fin, hu3,
      sup'_triple, d4V]
    norm_num
  refine ⟨he, ?_, fun θ hθ => by unfold CapSubj; rw [he]; exact hθ⟩
  simp only [reach, hu3, hu2, sup'_triple, sup'_pair', harmOf, d4V]
  norm_num

/-! ## (e) Average versus sup along a trajectory -/

/-- **The develop file's time-averaged objective cap** — quoted from `power-wisdom.md` D17
(l. 77–79): "`Π^obj_t(θ): E[Reg*_t(A_t)] ≤ θ`, where the outer expectation in `Π^obj` is over the
reference class of situations (or over the trajectory's steps)". Read as the time average over
steps `0..T` of a regret trajectory `r`. **Defined only to be refuted** (`capObjAvg_admits_catastrophe`);
the surviving neighbour is `CapObjTraj` (sup form, power-wisdom-final.md D17).
Source: `power-wisdom.md` D17 (l. 79–79), the develop reading; power-wisdom-adversary.md D.3
Kind: D
Fidelity: exact (the develop file's reading "over the trajectory's steps") -/
def CapObjAvg (r : ℕ → ℝ) (T : ℕ) (θ : ℝ) : Prop := (∑ t ∈ range (T + 1), r t) / (T + 1) ≤ θ

/-- **The objective cap along a trajectory, sup form**: `∀ t ≤ T, Reg*_t ≤ θ`.
Source: power-wisdom-final.md D17 (l. 79, "along a trajectory: `sup_t Reg*_t(A_t) ≤ θ`")
Kind: D
Fidelity: exact -/
def CapObjTraj (r : ℕ → ℝ) (T : ℕ) (θ : ℝ) : Prop := ∀ t ≤ T, r t ≤ θ

/-- A5's regret trajectory: `0` on 99 steps and `1` on step `99`.
Source: power-wisdom-adversary.md D.3 (l. 19), A5
Kind: D
Fidelity: n/a (witness) -/
def a5Regret : ℕ → ℝ := fun t => if t = 99 then 1 else 0

/-- **A5/R4 (N+): the time-averaged cap admits one catastrophic step; the sup form rejects it.**
On A5's trajectory (100 steps, regret `0` on 99 and `1` on one), the average is
`1/100 ≤ 1/50` so `CapObjAvg` holds, while some step has regret `1 > 1/50`, so `CapObjTraj`
fails.
Source: power-wisdom-adversary.md D.3 (l. 19); scripts A5, R4; power-wisdom-final.md D17 (l. 79)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem capObjAvg_admits_catastrophe :
    CapObjAvg a5Regret 99 (1 / 50) ∧ ¬ CapObjTraj a5Regret 99 (1 / 50) := by
  constructor
  · unfold CapObjAvg a5Regret
    rw [sum_ite_eq' (range 100) 99 (fun _ => (1 : ℝ))]
    simp only [mem_range, show (99 : ℕ) < 100 by norm_num, if_true]
    norm_num
  · intro h
    have := h 99 le_rfl
    simp [a5Regret] at this
    norm_num at this

end

end Cleanroom.Corrigibility.CorrPowerChannel
