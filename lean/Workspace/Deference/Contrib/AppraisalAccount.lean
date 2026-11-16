/-
# The appraisal account — its finite identities

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-8.md` §2.5),
against `ATTENTION.md` item 137.  Result numbers are those of §2.2 of that prompt.

**Setting.**  A finite space `X` with a weight `μ : X → ℝ`, `0 ≤ μ`.  Expectation is the
workspace's finite credence `LICorrigibility.expectR μ f = ∑ x, μ x * f x`.  The conditional
expectation of `T` given a labelling `g : X → Y` is `condExp μ g T x`: the `μ`-weighted mean
of `T` over the cell `{x' | g x' = g x}`, and `0` on a cell of zero mass (Lean's `0 / 0 = 0`).
No statement assumes cells have positive mass.

**Pythagoras** (`pythagoras`): for `W` constant on the cells of `g`,
`E[(W − T)²] = E[(W − E[T | g])²] + E[(E[T | g] − T)²]`.

**Result 1, the split** (`mse_split`, `mse_split_minimal`): for an appraisal `xhat` constant
on the cells of `g`, `E[(xhat − T)²] = E[(T − E[T | g])²] + E[(xhat − E[T | g])²]`; at
`g := xhat` this is mean squared error = what the appraisal cannot tell apart + its minimal
miscalibration.

**Result 2, three channels** (`attained_eq`, `ignorance_nonneg`, `misuse_nonneg`,
`three_channels`): with moves `A`, true utilities `U a x`, an observation `s`, a choice
`c : S → A`, `ubar a = E[U a | s]` and `best f x = max_a f a x`:
`E[U_c] = E[best U] − (E[best U] − E[best ubar]) − E[best ubar − ubar_c]`, the two
subtracted terms non-negative.

**Result 3, the cost of mistakes** (`misuse_le`): with valuations `uhat a (s x)`,
`regret x = max_a uhat a (s x) − uhat (c (s x)) (s x)` and
`valuationError = Σ_a E[(uhat a ∘ s − ubar a)²]`:
`E[best ubar − ubar_c] ≤ E[regret] + √(2 · valuationError)`.

**Result 7, deferring** (`deferring`, `deferring_determined`, `deferring_identity`): with the
adviser's information `k`, true utility `U`, verdict `V`, `y = E[U | k]` and
`z = E[U | k, V]`: `E[(y − U)²] − E[(V − U)²] = E[(y − z)²] − E[(V − z)²]`, and if `V` is
constant on the cells of `k` then `E[(y − z)²] = 0`.

**Hypotheses.**  Every theorem assumes `0 ≤ μ` except `deferring_determined`, which assumes
nothing of `μ`.  `∑ x, μ x = 1` is assumed only by `expectR_sqrt_le` and `misuse_le`; the
other statements hold for any non-negative weight.

**Witnesses** (`Witness`): instances on `Bool` at `μ = 1/2`, one per headline, each
`…_instance` theorem conjoining the hypothesis package with the conclusion on the instance.

**Reused.**  `LICorrigibility.expectR`; `DeconfusingCorrigibility.expectR_mono` and
`expectR_sub`.

**Not established here.**  Results 4–6 and 8–11 of §2.2 are not stated.  Nothing here says
that `condExp` agrees with Mathlib's measure-theoretic conditional expectation; it is the
finite cell average, defined in this file.  The witnesses inhabit the hypothesis packages;
that the terms of the identities are non-zero on them is not proved, except that the
verdict of `Witness.deferring_instance` is shown not to be determined by the adviser's
information.  That these identities are the right formal reading of the account in the
round's `ACCOUNT.md` is a matter of reference and is not a theorem.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.DeconfusingCorrigibility

namespace Workspace.Deference.Contrib.AppraisalAccount

open Workspace.Deference.Contrib.LICorrigibility (expectR)
open Workspace.Deference.Contrib.DeconfusingCorrigibility (expectR_mono expectR_sub)

/-! ## Conditional expectation over a finite space -/

section CondExp

variable {X : Type*} [Fintype X] {Y : Type*} [DecidableEq Y]

/-- **Conditional expectation given a labelling.**  The `μ`-weighted mean of `T` over the
cell of `x` under `g`; `0` when the cell has zero mass. -/
noncomputable def condExp (μ : X → ℝ) (g : X → Y) (T : X → ℝ) (x : X) : ℝ :=
  (∑ x' ∈ Finset.univ.filter (fun x' => g x' = g x), μ x' * T x') /
    (∑ x' ∈ Finset.univ.filter (fun x' => g x' = g x), μ x')

variable (μ : X → ℝ)

/-- The conditional expectation is constant on cells. -/
theorem condExp_congr {g : X → Y} (T : X → ℝ) {x x' : X} (h : g x = g x') :
    condExp μ g T x = condExp μ g T x' := by
  unfold condExp
  rw [h]

/-- Two labellings with the same cell at `x` give the same conditional expectation at `x`. -/
theorem condExp_eq_of_iff {Y' : Type*} [DecidableEq Y'] {g : X → Y} {g' : X → Y'}
    (T : X → ℝ) (x : X) (h : ∀ x', g x' = g x ↔ g' x' = g' x) :
    condExp μ g T x = condExp μ g' T x := by
  unfold condExp
  rw [Finset.filter_congr (fun x' _ => h x')]

/-- Cell mass times the conditional expectation is the cell's weighted sum.  On a cell of
zero mass both sides vanish, since `0 ≤ μ` makes `μ` zero at each of its points. -/
theorem cell_mul_condExp (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) (T : X → ℝ) (x : X) :
    (∑ x' ∈ Finset.univ.filter (fun x' => g x' = g x), μ x') * condExp μ g T x
      = ∑ x' ∈ Finset.univ.filter (fun x' => g x' = g x), μ x' * T x' := by
  unfold condExp
  by_cases h : (∑ x' ∈ Finset.univ.filter (fun x' => g x' = g x), μ x') = 0
  · have h0 : ∀ x' ∈ Finset.univ.filter (fun x' => g x' = g x), μ x' = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hμ i).1 h
    rw [h, zero_mul]
    exact (Finset.sum_eq_zero fun x' hx' => by rw [h0 x' hx', zero_mul]).symm
  · field_simp

/-- Monotonicity of the conditional expectation under a nonnegative weight. -/
theorem condExp_mono (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) {T T' : X → ℝ}
    (h : ∀ x, T x ≤ T' x) (x : X) : condExp μ g T x ≤ condExp μ g T' x := by
  unfold condExp
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (h x') (hμ x'))
    (inv_nonneg.2 (Finset.sum_nonneg fun x' _ => hμ x'))

/-- Two sums over `X` agree when they agree on every cell of a labelling. -/
theorem sum_eq_of_cells (g : X → Y) (f f' : X → ℝ)
    (h : ∀ x₀, ∑ x ∈ Finset.univ.filter (fun x => g x = g x₀), f x
      = ∑ x ∈ Finset.univ.filter (fun x => g x = g x₀), f' x) :
    ∑ x, f x = ∑ x, f' x := by
  have hmaps : ∀ x ∈ (Finset.univ : Finset X), g x ∈ Finset.univ.image g :=
    fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)
  have hmid : ∑ y ∈ Finset.univ.image g, ∑ x ∈ Finset.univ.filter (fun x => g x = y), f x
      = ∑ y ∈ Finset.univ.image g, ∑ x ∈ Finset.univ.filter (fun x => g x = y), f' x := by
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 hy
    exact h x₀
  calc ∑ x, f x
      = ∑ y ∈ Finset.univ.image g, ∑ x ∈ Finset.univ.filter (fun x => g x = y), f x :=
        (Finset.sum_fiberwise_of_maps_to hmaps f).symm
    _ = ∑ y ∈ Finset.univ.image g, ∑ x ∈ Finset.univ.filter (fun x => g x = y), f' x := hmid
    _ = ∑ x, f' x := Finset.sum_fiberwise_of_maps_to hmaps f'

/-- **Pulling out what is known.**  For `F` constant on the cells of `g`,
`E[F · E[T | g]] = E[F · T]`. -/
theorem expectR_mul_condExp (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) (T F : X → ℝ)
    (hF : ∀ x x', g x = g x' → F x = F x') :
    expectR μ (fun x => F x * condExp μ g T x) = expectR μ (fun x => F x * T x) := by
  refine sum_eq_of_cells g (fun x => μ x * (F x * condExp μ g T x))
    (fun x => μ x * (F x * T x)) fun x₀ => ?_
  have h1 : ∀ x ∈ Finset.univ.filter (fun x => g x = g x₀),
      μ x * (F x * condExp μ g T x) = F x₀ * condExp μ g T x₀ * μ x := by
    intro x hx
    have hx' : g x = g x₀ := (Finset.mem_filter.1 hx).2
    rw [hF x x₀ hx', condExp_congr μ T hx']
    ring
  have h2 : ∀ x ∈ Finset.univ.filter (fun x => g x = g x₀),
      μ x * (F x * T x) = F x₀ * (μ x * T x) := by
    intro x hx
    rw [hF x x₀ (Finset.mem_filter.1 hx).2]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
    ← cell_mul_condExp μ hμ g T x₀]
  ring

/-- **The tower property**: `E[E[T | g]] = E[T]`. -/
theorem expectR_condExp (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) (T : X → ℝ) :
    expectR μ (condExp μ g T) = expectR μ T := by
  have h := expectR_mul_condExp μ hμ g T (fun _ => 1) (fun _ _ _ => rfl)
  simp only [one_mul] at h
  exact h

/-- **The tower property for a selection.**  For a family `U a` and a selection `c'`
constant on the cells of `g`, `E[E[U_{c'} | g]] = E[U_{c'}]`. -/
theorem expectR_condExp_choice {A : Type*} (hμ : ∀ x, 0 ≤ μ x) (g : X → Y)
    (U : A → X → ℝ) (c' : X → A) (hc : ∀ x x', g x = g x' → c' x = c' x') :
    expectR μ (fun x => condExp μ g (U (c' x)) x) = expectR μ (fun x => U (c' x) x) := by
  refine sum_eq_of_cells g (fun x => μ x * condExp μ g (U (c' x)) x)
    (fun x => μ x * U (c' x) x) fun x₀ => ?_
  have h1 : ∀ x ∈ Finset.univ.filter (fun x => g x = g x₀),
      μ x * condExp μ g (U (c' x)) x = μ x * condExp μ g (U (c' x₀)) x₀ := by
    intro x hx
    have hx' : g x = g x₀ := (Finset.mem_filter.1 hx).2
    rw [hc x x₀ hx', condExp_congr μ (U (c' x₀)) hx']
  have h2 : ∀ x ∈ Finset.univ.filter (fun x => g x = g x₀),
      μ x * U (c' x) x = μ x * U (c' x₀) x := by
    intro x hx
    rw [hc x x₀ (Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.sum_mul]
  exact cell_mul_condExp μ hμ g (U (c' x₀)) x₀

/-- A nonnegative function has nonnegative expectation under a nonnegative weight. -/
theorem expectR_nonneg (hμ : ∀ x, 0 ≤ μ x) {f : X → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ expectR μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (h x)

/-- **Pythagoras.**  For `W` constant on the cells of `g`,
`E[(W − T)²] = E[(W − E[T | g])²] + E[(E[T | g] − T)²]`. -/
theorem pythagoras (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) (T W : X → ℝ)
    (hW : ∀ x x', g x = g x' → W x = W x') :
    expectR μ (fun x => (W x - T x) ^ 2)
      = expectR μ (fun x => (W x - condExp μ g T x) ^ 2)
        + expectR μ (fun x => (condExp μ g T x - T x) ^ 2) := by
  have hF : ∀ x x', g x = g x' →
      W x - condExp μ g T x = W x' - condExp μ g T x' := fun x x' h => by
    rw [hW x x' h, condExp_congr μ T h]
  have h : ∑ x, μ x * ((W x - condExp μ g T x) * condExp μ g T x)
      = ∑ x, μ x * ((W x - condExp μ g T x) * T x) :=
    expectR_mul_condExp μ hμ g T (fun x => W x - condExp μ g T x) hF
  have e : ∑ x, μ x * (W x - T x) ^ 2
      = ∑ x, μ x * (W x - condExp μ g T x) ^ 2 + ∑ x, μ x * (condExp μ g T x - T x) ^ 2
        + 2 * (∑ x, μ x * ((W x - condExp μ g T x) * condExp μ g T x)
          - ∑ x, μ x * ((W x - condExp μ g T x) * T x)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  show ∑ x, μ x * (W x - T x) ^ 2
      = ∑ x, μ x * (W x - condExp μ g T x) ^ 2 + ∑ x, μ x * (condExp μ g T x - T x) ^ 2
  rw [e, h, sub_self, mul_zero, add_zero]

/-! ## Result 1 — the split -/

/-- **Result 1, the split**, at any labelling the appraisal is constant on the cells of:
`E[(xhat − T)²] = E[(T − E[T | g])²] + E[(xhat − E[T | g])²]`. -/
theorem mse_split (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) (T xhat : X → ℝ)
    (hx : ∀ x x', g x = g x' → xhat x = xhat x') :
    expectR μ (fun x => (xhat x - T x) ^ 2)
      = expectR μ (fun x => (T x - condExp μ g T x) ^ 2)
        + expectR μ (fun x => (xhat x - condExp μ g T x) ^ 2) := by
  have e : expectR μ (fun x => (condExp μ g T x - T x) ^ 2)
      = expectR μ (fun x => (T x - condExp μ g T x) ^ 2) :=
    congrArg (expectR μ) (funext fun x => by ring)
  rw [pythagoras μ hμ g T xhat hx, e, add_comm]

/-- **Result 1 at the appraisal's own cells**: mean squared error = what her appraisal
cannot tell apart, `E[(T − E[T | xhat])²]`, + its minimal miscalibration,
`E[(xhat − E[T | xhat])²]`. -/
theorem mse_split_minimal (hμ : ∀ x, 0 ≤ μ x) (T xhat : X → ℝ) :
    expectR μ (fun x => (xhat x - T x) ^ 2)
      = expectR μ (fun x => (T x - condExp μ xhat T x) ^ 2)
        + expectR μ (fun x => (xhat x - condExp μ xhat T x) ^ 2) :=
  mse_split μ hμ xhat T xhat fun _ _ h => h

end CondExp

/-! ## Result 2 — three channels -/

section Channels

variable {X : Type*} [Fintype X] {A : Type*} [Fintype A] [Nonempty A]

/-- The best value over the moves, pointwise: `best f x = max_a f a x`. -/
noncomputable def best (f : A → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => f a x)

variable {S : Type*} [DecidableEq S]

/-- Her true utility of each move, averaged over what she cannot observe:
`ubar a = E[U a | s]`. -/
noncomputable def ubar (μ : X → ℝ) (s : X → S) (U : A → X → ℝ) (a : A) (x : X) : ℝ :=
  condExp μ s (U a) x

variable (μ : X → ℝ)

/-- **Result 2(a).**  What she attains is the best attainable, less what she cannot know,
less what she loses by her choice:
`E[U_c] = E[best U] − (E[best U] − E[best ubar]) − E[best ubar − ubar_c]`. -/
theorem attained_eq (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S) (c : S → A) :
    expectR μ (fun x => U (c (s x)) x)
      = expectR μ (best U) - (expectR μ (best U) - expectR μ (best (ubar μ s U)))
        - expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x) := by
  have h1 : expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x)
      = expectR μ (best (ubar μ s U)) - expectR μ (fun x => ubar μ s U (c (s x)) x) :=
    expectR_sub μ _ _
  have h2 : expectR μ (fun x => ubar μ s U (c (s x)) x)
      = expectR μ (fun x => U (c (s x)) x) :=
    expectR_condExp_choice μ hμ s U (fun x => c (s x)) fun x x' h => by rw [h]
  rw [h1, h2]
  ring

/-- Pointwise, the best averaged utility is at most the average of the best utility. -/
theorem best_ubar_le (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S) (x : X) :
    best (ubar μ s U) x ≤ condExp μ s (best U) x :=
  Finset.sup'_le _ _ fun a _ =>
    condExp_mono μ hμ s (fun x' => Finset.le_sup' (fun a => U a x') (Finset.mem_univ a)) x

/-- **Result 2(b).**  What she cannot know costs a non-negative amount. -/
theorem ignorance_nonneg (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S) :
    0 ≤ expectR μ (best U) - expectR μ (best (ubar μ s U)) := by
  have h := expectR_mono μ hμ (best_ubar_le μ hμ U s)
  rw [expectR_condExp μ hμ s (best U)] at h
  exact sub_nonneg.2 h

/-- **Result 2(c).**  Her choice costs a non-negative amount. -/
theorem misuse_nonneg (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S) (c : S → A) :
    0 ≤ expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x) :=
  expectR_nonneg μ hμ fun x =>
    sub_nonneg.2 (Finset.le_sup' (fun a => ubar μ s U a x) (Finset.mem_univ (c (s x))))

/-- **Result 2, three channels.** -/
theorem three_channels (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S) (c : S → A) :
    expectR μ (fun x => U (c (s x)) x)
        = expectR μ (best U) - (expectR μ (best U) - expectR μ (best (ubar μ s U)))
          - expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x)
      ∧ 0 ≤ expectR μ (best U) - expectR μ (best (ubar μ s U))
      ∧ 0 ≤ expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x) :=
  ⟨attained_eq μ hμ U s c, ignorance_nonneg μ hμ U s, misuse_nonneg μ hμ U s c⟩

/-! ## Result 3 — the cost of mistakes -/

/-- Her regret by her own lights at `x`: the best of her valuations less the valuation of
the move she chooses. -/
noncomputable def regret (uhat : A → S → ℝ) (s : X → S) (c : S → A) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => uhat a (s x)) - uhat (c (s x)) (s x)

/-- The summed mean squared distance of her valuations from the averaged true utilities:
`Σ_a E[(uhat a ∘ s − ubar a)²]`. -/
noncomputable def valuationError (μ : X → ℝ) (s : X → S) (U : A → X → ℝ)
    (uhat : A → S → ℝ) : ℝ :=
  ∑ a, expectR μ (fun x => (uhat a (s x) - ubar μ s U a x) ^ 2)

omit [Nonempty A] [DecidableEq S] in
/-- Expanding a mean square about a constant. -/
theorem expectR_sqrt_sub_sq (Y : X → ℝ) (hY : ∀ x, 0 ≤ Y x) (t : ℝ) :
    expectR μ (fun x => (Real.sqrt (Y x) - t) ^ 2)
      = expectR μ Y - 2 * t * expectR μ (fun x => Real.sqrt (Y x)) + t ^ 2 * ∑ x, μ x := by
  simp only [expectR]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  calc μ x * (Real.sqrt (Y x) - t) ^ 2
      = μ x * Real.sqrt (Y x) ^ 2 - 2 * t * (μ x * Real.sqrt (Y x)) + t ^ 2 * μ x := by ring
    _ = μ x * Y x - 2 * t * (μ x * Real.sqrt (Y x)) + t ^ 2 * μ x := by
        rw [Real.sq_sqrt (hY x)]

omit [Nonempty A] [DecidableEq S] in
/-- **Jensen for the square root**, under a weight summing to one: `E[√Y] ≤ √E[Y]`. -/
theorem expectR_sqrt_le (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1) (Y : X → ℝ)
    (hY : ∀ x, 0 ≤ Y x) :
    expectR μ (fun x => Real.sqrt (Y x)) ≤ Real.sqrt (expectR μ Y) := by
  have h0 : 0 ≤ expectR μ
      (fun x => (Real.sqrt (Y x) - expectR μ (fun x => Real.sqrt (Y x))) ^ 2) :=
    expectR_nonneg μ hμ fun x => sq_nonneg _
  rw [expectR_sqrt_sub_sq μ Y hY, hsum] at h0
  have h1 : expectR μ (fun x => Real.sqrt (Y x)) ^ 2 ≤ expectR μ Y := by nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

/-- The pointwise bound behind Result 3. -/
theorem misuse_pointwise (U : A → X → ℝ) (s : X → S) (c : S → A) (uhat : A → S → ℝ)
    (x : X) :
    best (ubar μ s U) x - ubar μ s U (c (s x)) x
      ≤ regret uhat s c x
        + Real.sqrt (2 * ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2) := by
  classical
  have hsq : ∀ a, 0 ≤ (uhat a (s x) - ubar μ s U a x) ^ 2 := fun a => sq_nonneg _
  have hD : 0 ≤ ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2 :=
    Finset.sum_nonneg fun a _ => hsq a
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => ubar μ s U a x)
  have hbest : best (ubar μ s U) x = ubar μ s U a x := ha
  have hup : uhat a (s x) ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => uhat a (s x)) :=
    Finset.le_sup' (fun a => uhat a (s x)) (Finset.mem_univ a)
  have hkey : ((uhat (c (s x)) (s x) - ubar μ s U (c (s x)) x)
      - (uhat a (s x) - ubar μ s U a x)) ^ 2
      ≤ 2 * ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2 := by
    by_cases hac : a = c (s x)
    · rw [← hac, sub_self]
      nlinarith
    · have hpair : (uhat a (s x) - ubar μ s U a x) ^ 2
          + (uhat (c (s x)) (s x) - ubar μ s U (c (s x)) x) ^ 2
          ≤ ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2 := by
        rw [← Finset.sum_pair (f := fun a => (uhat a (s x) - ubar μ s U a x) ^ 2) hac]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => hsq i
      nlinarith [sq_nonneg ((uhat (c (s x)) (s x) - ubar μ s U (c (s x)) x)
        + (uhat a (s x) - ubar μ s U a x))]
  have hsqrt := (le_abs_self _).trans (Real.abs_le_sqrt hkey)
  rw [hbest]
  unfold regret
  linarith

/-- **Result 3, the cost of mistakes.**  What her choice costs is at most her regret by her
own lights plus `√(2 · valuationError)`. -/
theorem misuse_le (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1) (U : A → X → ℝ) (s : X → S)
    (c : S → A) (uhat : A → S → ℝ) :
    expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x)
      ≤ expectR μ (regret uhat s c) + Real.sqrt (2 * valuationError μ s U uhat) := by
  have h1 := expectR_mono μ hμ (misuse_pointwise μ U s c uhat)
  have h2 : expectR μ (fun x => regret uhat s c x
        + Real.sqrt (2 * ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2))
      = expectR μ (regret uhat s c)
        + expectR μ (fun x => Real.sqrt (2 * ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2)) := by
    simp only [expectR]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h3 := expectR_sqrt_le μ hμ hsum
    (fun x => 2 * ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2)
    fun x => mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => sq_nonneg _)
  have h4 : expectR μ (fun x => 2 * ∑ a, (uhat a (s x) - ubar μ s U a x) ^ 2)
      = 2 * valuationError μ s U uhat := by
    simp only [expectR, valuationError, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => by ring
  rw [h4] at h3
  linarith

end Channels

/-! ## Result 7 — deferring -/

section Deferring

variable {X : Type*} [Fintype X] {K : Type*} [DecidableEq K] (μ : X → ℝ)

/-- **Result 7, deferring.**  With `y = E[U | k]` the adviser's best estimate of her true
utility, `V` her verdict and `z = E[U | k, V]` the best estimate given both:
`E[(y − U)²] − E[(V − U)²] = E[(y − z)²] − E[(V − z)²]`. -/
theorem deferring (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
    expectR μ (fun x => (condExp μ k U x - U x) ^ 2) - expectR μ (fun x => (V x - U x) ^ 2)
      = expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
        - expectR μ (fun x => (V x - condExp μ (fun x => (k x, V x)) U x) ^ 2) := by
  have hy := pythagoras μ hμ (fun x => (k x, V x)) U (condExp μ k U)
    fun x x' h => condExp_congr μ U (congrArg Prod.fst h)
  have hV := pythagoras μ hμ (fun x => (k x, V x)) U V fun x x' h => congrArg Prod.snd h
  rw [hy, hV]
  ring

/-- **Result 7, the determined case.**  If her verdict is constant on the cells of the
adviser's information, the adviser's estimate is already the estimate given both.  No
hypothesis on `μ` is used. -/
theorem deferring_determined (k : X → K) (U V : X → ℝ)
    (hV : ∀ x x', k x = k x' → V x = V x') :
    expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
      = 0 := by
  have h : ∀ x, condExp μ k U x = condExp μ (fun x => (k x, V x)) U x := fun x =>
    condExp_eq_of_iff μ U x fun x' =>
      ⟨fun h => Prod.ext h (hV x' x h), fun h => congrArg Prod.fst h⟩
  have e : (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
      = fun _ => (0 : ℝ) := funext fun x => by rw [h x]; ring
  rw [e]
  simp [expectR]

/-- **Result 7, deferring**, both parts. -/
theorem deferring_identity (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
    (expectR μ (fun x => (condExp μ k U x - U x) ^ 2) - expectR μ (fun x => (V x - U x) ^ 2)
        = expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
          - expectR μ (fun x => (V x - condExp μ (fun x => (k x, V x)) U x) ^ 2))
      ∧ ((∀ x x', k x = k x' → V x = V x') →
        expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
          = 0) :=
  ⟨deferring μ hμ k U V, deferring_determined μ k U V⟩

end Deferring

/-! ## Witnesses -/

namespace Witness

/-- Two equally weighted worlds. -/
noncomputable def μ : Bool → ℝ := fun _ => 1 / 2

theorem μ_nonneg : ∀ x, 0 ≤ μ x := fun _ => by
  unfold μ
  norm_num

theorem μ_sum : ∑ x, μ x = 1 := by
  rw [Fintype.sum_bool]
  unfold μ
  norm_num

/-- The target: `1` in one world, `0` in the other. -/
noncomputable def T : Bool → ℝ := fun x => if x then 1 else 0

/-- An appraisal that cannot tell the worlds apart, and is off by `1/4` from the mean. -/
noncomputable def xhat : Bool → ℝ := fun _ => 3 / 4

/-- A labelling that does not separate the worlds. -/
def coarse : Bool → Unit := fun _ => ()

theorem xhat_factors : ∀ x x', coarse x = coarse x' → xhat x = xhat x' := fun _ _ _ => rfl

/-- **Result 1's hypothesis package is inhabited**, by an appraisal that does not separate
the worlds; its conclusions hold on the instance. -/
theorem mse_split_instance :
    (∀ x, 0 ≤ μ x) ∧ (∀ x x', coarse x = coarse x' → xhat x = xhat x') ∧
      expectR μ (fun x => (xhat x - T x) ^ 2)
        = expectR μ (fun x => (T x - condExp μ coarse T x) ^ 2)
          + expectR μ (fun x => (xhat x - condExp μ coarse T x) ^ 2) ∧
      expectR μ (fun x => (xhat x - T x) ^ 2)
        = expectR μ (fun x => (T x - condExp μ xhat T x) ^ 2)
          + expectR μ (fun x => (xhat x - condExp μ xhat T x) ^ 2) :=
  ⟨μ_nonneg, xhat_factors, mse_split μ μ_nonneg coarse T xhat xhat_factors,
    mse_split_minimal μ μ_nonneg T xhat⟩

/-- Two moves; a move pays `1` in the world it names and `0` in the other. -/
noncomputable def U : Bool → Bool → ℝ := fun a x => if a = x then 1 else 0

/-- She observes the world. -/
def s : Bool → Bool := fun x => x

/-- She chooses the same move whatever she observes: the best move in one world only. -/
def c : Bool → Bool := fun _ => true

/-- **Result 2's hypothesis package is inhabited**, with two moves and a choice that is not
always the best; its conclusions hold on the instance. -/
theorem three_channels_instance :
    (∀ x, 0 ≤ μ x) ∧
      expectR μ (fun x => U (c (s x)) x)
        = expectR μ (best U) - (expectR μ (best U) - expectR μ (best (ubar μ s U)))
          - expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x) ∧
      0 ≤ expectR μ (best U) - expectR μ (best (ubar μ s U)) ∧
      0 ≤ expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x) :=
  ⟨μ_nonneg, three_channels μ μ_nonneg U s c⟩

/-- Valuations that rate the two moves equally whatever she observes. -/
noncomputable def uhat : Bool → Bool → ℝ := fun _ _ => 1 / 2

/-- **Result 3's hypothesis package is inhabited**; its conclusion holds on the instance. -/
theorem misuse_le_instance :
    (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1 ∧
      expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x)
        ≤ expectR μ (regret uhat s c) + Real.sqrt (2 * valuationError μ s U uhat) :=
  ⟨μ_nonneg, μ_sum, misuse_le μ μ_nonneg μ_sum U s c uhat⟩

/-- A verdict that separates the worlds, as the adviser's information `coarse` does not. -/
noncomputable def V : Bool → ℝ := T

theorem V_not_determined : ¬ ∀ x x', coarse x = coarse x' → V x = V x' := by
  intro h
  have h' := h true false rfl
  simp [V, T] at h'

/-- **Result 7's hypothesis package is inhabited**, by a verdict not determined by the
adviser's information; its conclusion holds on the instance. -/
theorem deferring_instance :
    (∀ x, 0 ≤ μ x) ∧ (¬ ∀ x x', coarse x = coarse x' → V x = V x') ∧
      expectR μ (fun x => (condExp μ coarse T x - T x) ^ 2)
          - expectR μ (fun x => (V x - T x) ^ 2)
        = expectR μ (fun x => (condExp μ coarse T x
            - condExp μ (fun x => (coarse x, V x)) T x) ^ 2)
          - expectR μ (fun x => (V x - condExp μ (fun x => (coarse x, V x)) T x) ^ 2) :=
  ⟨μ_nonneg, V_not_determined, deferring μ μ_nonneg coarse T V⟩

/-- A verdict that is the same in both worlds. -/
noncomputable def Vconst : Bool → ℝ := fun _ => 1 / 2

theorem Vconst_determined : ∀ x x', coarse x = coarse x' → Vconst x = Vconst x' :=
  fun _ _ _ => rfl

/-- **The determined case's hypothesis package is inhabited**; its conclusion holds on the
instance. -/
theorem deferring_determined_instance :
    (∀ x x', coarse x = coarse x' → Vconst x = Vconst x') ∧
      expectR μ (fun x => (condExp μ coarse T x
        - condExp μ (fun x => (coarse x, Vconst x)) T x) ^ 2) = 0 :=
  ⟨Vconst_determined, deferring_determined μ coarse T Vconst Vconst_determined⟩

/-- **Result 7's bundled statement on both instances.** -/
theorem deferring_identity_instance :
    (∀ x, 0 ≤ μ x) ∧ (∀ x x', coarse x = coarse x' → Vconst x = Vconst x') ∧
      expectR μ (fun x => (condExp μ coarse T x
        - condExp μ (fun x => (coarse x, Vconst x)) T x) ^ 2) = 0 :=
  ⟨μ_nonneg, Vconst_determined,
    (deferring_identity μ μ_nonneg coarse T Vconst).2 Vconst_determined⟩

end Witness

end Workspace.Deference.Contrib.AppraisalAccount

#print axioms Workspace.Deference.Contrib.AppraisalAccount.condExp
#print axioms Workspace.Deference.Contrib.AppraisalAccount.condExp_congr
#print axioms Workspace.Deference.Contrib.AppraisalAccount.condExp_eq_of_iff
#print axioms Workspace.Deference.Contrib.AppraisalAccount.cell_mul_condExp
#print axioms Workspace.Deference.Contrib.AppraisalAccount.condExp_mono
#print axioms Workspace.Deference.Contrib.AppraisalAccount.sum_eq_of_cells
#print axioms Workspace.Deference.Contrib.AppraisalAccount.expectR_mul_condExp
#print axioms Workspace.Deference.Contrib.AppraisalAccount.expectR_condExp
#print axioms Workspace.Deference.Contrib.AppraisalAccount.expectR_condExp_choice
#print axioms Workspace.Deference.Contrib.AppraisalAccount.expectR_nonneg
#print axioms Workspace.Deference.Contrib.AppraisalAccount.pythagoras
#print axioms Workspace.Deference.Contrib.AppraisalAccount.mse_split
#print axioms Workspace.Deference.Contrib.AppraisalAccount.mse_split_minimal
#print axioms Workspace.Deference.Contrib.AppraisalAccount.best
#print axioms Workspace.Deference.Contrib.AppraisalAccount.ubar
#print axioms Workspace.Deference.Contrib.AppraisalAccount.attained_eq
#print axioms Workspace.Deference.Contrib.AppraisalAccount.best_ubar_le
#print axioms Workspace.Deference.Contrib.AppraisalAccount.ignorance_nonneg
#print axioms Workspace.Deference.Contrib.AppraisalAccount.misuse_nonneg
#print axioms Workspace.Deference.Contrib.AppraisalAccount.three_channels
#print axioms Workspace.Deference.Contrib.AppraisalAccount.regret
#print axioms Workspace.Deference.Contrib.AppraisalAccount.valuationError
#print axioms Workspace.Deference.Contrib.AppraisalAccount.expectR_sqrt_sub_sq
#print axioms Workspace.Deference.Contrib.AppraisalAccount.expectR_sqrt_le
#print axioms Workspace.Deference.Contrib.AppraisalAccount.misuse_pointwise
#print axioms Workspace.Deference.Contrib.AppraisalAccount.misuse_le
#print axioms Workspace.Deference.Contrib.AppraisalAccount.deferring
#print axioms Workspace.Deference.Contrib.AppraisalAccount.deferring_determined
#print axioms Workspace.Deference.Contrib.AppraisalAccount.deferring_identity
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.μ
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.μ_nonneg
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.μ_sum
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.T
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.xhat
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.coarse
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.xhat_factors
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.mse_split_instance
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.U
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.s
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.c
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.three_channels_instance
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.uhat
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.misuse_le_instance
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.V
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.V_not_determined
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.deferring_instance
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.Vconst
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.Vconst_determined
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.deferring_determined_instance
#print axioms Workspace.Deference.Contrib.AppraisalAccount.Witness.deferring_identity_instance
