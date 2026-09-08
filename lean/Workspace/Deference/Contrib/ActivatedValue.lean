/-
# Authority-activated value securities: the common-activation algebra

Round `projects/deference/rounds/2026-09-07-authority-activated-value/`.

A finite credence `π` over worlds, one activation event `c : W → Bool` shared by the whole
menu, and a menu `V : Q → W → ℚ` of `[0,1]`-valued payoffs.  The **activated security** of
candidate `a` is `U a = c · V a`.  Everything below is finite exact algebra over `π`; the
Logical-Induction reading (prices in place of `π`, `≈ₙ` in place of `=`) is the section at
the end, stated as `value_asymptotic` is: over real sequences with the LI facts as named
hypotheses.

* `pairwise` — `E[U a] − E[U b] = E[c · (V a − V b)]`: the difference of two activated
  securities is a common-activation difference.
* `argmax_iff` — with positive activation mass, `E[U a] ≤ E[U b]` iff
  `E[V a | c] ≤ E[V b | c]`: the activated argmax is the conditional argmax.
* `availability_transfer` — `V ∈ [0,1]`, `E[1 − c] ≤ η`, and activated regret `≤ ε` at
  the selection give unactivated regret `≤ ε + η`.  `availability_transfer_range` is the
  general form with the payoff range `D` in place of `1`: `ε + D·η`.
* `transfer_sharp` — a two-world fixture attaining `ε + η` exactly, with `ε = 0`; the
  constant is `1`, not `2`.
* `per_action_transfer` — with a certification event per candidate the transfer survives
  at `ε + max_a η_a`; `PerAction.argmax_breaks` is the fixture on which the conditional
  argmax identity fails.
* `vacuous` — `c ≡ 0` gives activated regret `0` for every selection.
* `availability_transfer_asymptotic` — the LI-shaped form over sequences.

**What this does not establish.**  That any market prices `U a`; that `E[1 − c]` is small;
that `c` is measurable, sound, or complete.  Those are the semantics of `c`, which is the
Normativity-side module `AuthorityActivation.lean`.  Names are provisional (`AGENTS.md`
standard 6).
-/
import LogicalInduction.Framework.Asymptotics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace Workspace.Deference.Contrib.ActivatedValue

open Finset

variable {W Q : Type*} [Fintype W]

/-- Expectation of a payoff under a credence. -/
def expect (π : W → ℚ) (X : W → ℚ) : ℚ := ∑ w, π w * X w

/-- The activation indicator as a rational. -/
def ind (c : W → Bool) (w : W) : ℚ := if c w then 1 else 0

/-- The activated security of candidate `a`. -/
def activated (c : W → Bool) (V : Q → W → ℚ) (a : Q) (w : W) : ℚ := ind c w * V a w

/-- Activation mass `P(c = 1)`. -/
def mass (π : W → ℚ) (c : W → Bool) : ℚ := expect π (ind c)

/-- Conditional expectation given activation (defined when the mass is positive). -/
def condExpect (π : W → ℚ) (c : W → Bool) (X : W → ℚ) : ℚ :=
  expect π (fun w => ind c w * X w) / mass π c

omit [Fintype W] in
lemma ind_nonneg (c : W → Bool) (w : W) : 0 ≤ ind c w := by
  unfold ind; split_ifs <;> norm_num

omit [Fintype W] in
lemma ind_le_one (c : W → Bool) (w : W) : ind c w ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-! ## Common activation: pairwise differences and the conditional argmax -/

/-- **Pairwise.**  Two activated securities differ by the activation of the difference. -/
theorem pairwise (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ) (a b : Q) :
    expect π (activated c V a) - expect π (activated c V b)
      = expect π (fun w => ind c w * (V a w - V b w)) := by
  simp only [expect, activated, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- The activated expectation is the activation mass times the conditional expectation. -/
theorem expect_activated_eq (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ) (a : Q)
    (hm : 0 < mass π c) :
    expect π (activated c V a) = mass π c * condExpect π c (V a) := by
  unfold condExpect activated
  rw [mul_div_cancel₀ _ hm.ne']

/-- **Conditional argmax.**  With positive activation mass, the activated order is the
conditional order: `argmax_a E[c · V a] = argmax_a E[V a | c]`. -/
theorem argmax_iff (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ) (a b : Q)
    (hm : 0 < mass π c) :
    expect π (activated c V a) ≤ expect π (activated c V b)
      ↔ condExpect π c (V a) ≤ condExpect π c (V b) := by
  rw [expect_activated_eq π c V a hm, expect_activated_eq π c V b hm]
  exact mul_le_mul_iff_right₀ hm

/-! ## The availability transfer inequality -/

omit [Fintype W] in
/-- `V − U = (1 − c) · V`: the unactivated excess is the payoff on the void branch. -/
theorem sub_activated (c : W → Bool) (V : Q → W → ℚ) (a : Q) (w : W) :
    V a w - activated c V a w = (1 - ind c w) * V a w := by
  unfold activated; ring

/-- Under a nonnegative credence and a payoff in `[L, L + D]`, the unactivated excess of
any candidate lies between `L · E[1 − c]` and `(L + D) · E[1 − c]`. -/
theorem excess_bounds (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ) (a : Q) (L D : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hlo : ∀ w, L ≤ V a w) (hhi : ∀ w, V a w ≤ L + D) :
    L * expect π (fun w => 1 - ind c w)
      ≤ expect π (V a) - expect π (activated c V a) ∧
    expect π (V a) - expect π (activated c V a)
      ≤ (L + D) * expect π (fun w => 1 - ind c w) := by
  have hexp : expect π (V a) - expect π (activated c V a)
      = ∑ w, π w * ((1 - ind c w) * V a w) := by
    simp only [expect, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← mul_sub, sub_activated]
  have h1c : ∀ w, 0 ≤ 1 - ind c w := fun w => by linarith [ind_le_one c w]
  rw [hexp]
  constructor
  · unfold expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have := mul_le_mul_of_nonneg_left (hlo w) (h1c w)
    nlinarith [hπ w]
  · unfold expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have := mul_le_mul_of_nonneg_left (hhi w) (h1c w)
    nlinarith [hπ w]

/-- **Availability transfer, general range.**  Payoffs in `[L, L + D]`, void mass
`E[1 − c] ≤ η`, and activated regret `≤ ε` at the selection `â` give unactivated regret
`≤ ε + D · η`.  The two uses of the void mass are one-sided: the competitor's excess is at
most `(L + D) η'`, the selection's is at least `L η'`, and the difference is `D η'`. -/
theorem availability_transfer_range (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ)
    (â : Q) (L D ε η : ℚ) (hD : 0 ≤ D)
    (hπ : ∀ w, 0 ≤ π w) (hlo : ∀ a w, L ≤ V a w) (hhi : ∀ a w, V a w ≤ L + D)
    (hη : expect π (fun w => 1 - ind c w) ≤ η)
    (hreg : ∀ a, expect π (activated c V a) - expect π (activated c V â) ≤ ε) :
    ∀ a, expect π (V a) - expect π (V â) ≤ ε + D * η := by
  intro a
  obtain ⟨_, ha_hi⟩ := excess_bounds π c V a L D hπ (hlo a) (hhi a)
  obtain ⟨hâ_lo, _⟩ := excess_bounds π c V â L D hπ (hlo â) (hhi â)
  have := hreg a
  nlinarith

/-- **Availability transfer.**  `V ∈ [0,1]`: unactivated regret `≤ ε + η`. -/
theorem availability_transfer (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ)
    (â : Q) (ε η : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hlo : ∀ a w, 0 ≤ V a w) (hhi : ∀ a w, V a w ≤ 1)
    (hη : expect π (fun w => 1 - ind c w) ≤ η)
    (hreg : ∀ a, expect π (activated c V a) - expect π (activated c V â) ≤ ε) :
    ∀ a, expect π (V a) - expect π (V â) ≤ ε + η := by
  have := availability_transfer_range π c V â 0 1 ε η zero_le_one hπ hlo
    (fun a w => by simpa using hhi a w) hη hreg
  simpa using this

/-! ### Followed strategies

The Logical-Induction selection is a computation read off the world: a hard selector
`â(w)`, or the soft mixture `Σ_a α_a(w) · O_a(w)` of the ported `value_asymptotic`.  Both
are world-dependent probability vectors over the menu, and the transfer holds for any
such strategy with the same constant. -/

/-- The followed strategy's payoff under a world-dependent mixture `α`. -/
def followed [Fintype Q] (α : W → Q → ℚ) (X : Q → W → ℚ) (w : W) : ℚ :=
  ∑ a, α w a * X a w

/-- **Availability transfer for a followed strategy.**  For any world-dependent
probability vector `α` over the menu — a hard selector or a soft mixture — activated
regret `≤ ε` and void mass `≤ η` give unactivated regret `≤ ε + η`. -/
theorem availability_transfer_strategy [Fintype Q] (π : W → ℚ) (c : W → Bool)
    (V : Q → W → ℚ) (α : W → Q → ℚ) (ε η : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hlo : ∀ a w, 0 ≤ V a w) (hhi : ∀ a w, V a w ≤ 1)
    (hα : ∀ w a, 0 ≤ α w a) (hα1 : ∀ w, ∑ a, α w a = 1)
    (hη : expect π (fun w => 1 - ind c w) ≤ η)
    (hreg : ∀ a, expect π (activated c V a) - expect π (followed α (activated c V)) ≤ ε) :
    ∀ a, expect π (V a) - expect π (followed α V) ≤ ε + η := by
  intro a
  obtain ⟨_, ha_hi⟩ := excess_bounds π c V a 0 1 hπ (hlo a) (fun w => by simpa using hhi a w)
  -- the followed strategy's unactivated payoff dominates its activated payoff
  have hfoll : expect π (followed α (activated c V)) ≤ expect π (followed α V) := by
    unfold expect
    refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (hπ w)
    unfold followed
    refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hα w b)
    unfold activated
    have := hlo b w
    have := ind_le_one c w
    nlinarith
  have := hreg a
  simp only [zero_mul, zero_add, one_mul] at ha_hi
  linarith

/-! ## Sharpness: the constant is `1`

Two worlds.  In world `0` (mass `1 − η`) the contract is activated and both candidates are
worth `v`; in world `1` (mass `η`) it is void and candidate `0` is worth `1`, candidate `1`
worth `0`.  Activated regret at the selection `1` is `0`; unactivated regret is exactly
`η`.  So `ε + η` is attained with `ε = 0`, and no bound of the form `ε + κ η` with `κ < 1`
holds. -/

namespace Sharp

def π (η : ℚ) : Fin 2 → ℚ := ![1 - η, η]
def c : Fin 2 → Bool := ![true, false]
def V (v : ℚ) : Fin 2 → Fin 2 → ℚ := ![![v, 1], ![v, 0]]

theorem activated_regret_zero (η v : ℚ) (a : Fin 2) :
    expect (π η) (activated c (V v) a) - expect (π η) (activated c (V v) 1) = 0 := by
  fin_cases a <;> simp [expect, activated, ind, π, c, V, Fin.sum_univ_two]

theorem void_mass (η : ℚ) : expect (π η) (fun w => 1 - ind c w) = η := by
  simp [expect, ind, π, c, Fin.sum_univ_two]

theorem unactivated_regret (η v : ℚ) :
    expect (π η) (V v 0) - expect (π η) (V v 1) = η := by
  simp [expect, π, V, Fin.sum_univ_two]

/-- **The transfer bound is attained.**  With `ε = 0` and void mass exactly `η`, the
unactivated regret is exactly `η`. -/
theorem transfer_sharp (η v : ℚ) :
    (∀ a, expect (π η) (activated c (V v) a) - expect (π η) (activated c (V v) 1) ≤ 0) ∧
    expect (π η) (fun w => 1 - ind c w) ≤ η ∧
    expect (π η) (V v 0) - expect (π η) (V v 1) = 0 + η := by
  refine ⟨fun a => (activated_regret_zero η v a).le, (void_mass η).le, ?_⟩
  rw [unactivated_regret]; ring

end Sharp

/-! ## Per-candidate certification

With an activation event per candidate, `U a = c a · V a`.  The transfer inequality
survives with the worst void mass in place of the common one; the conditional-argmax
identity does not. -/

namespace PerAction

/-- Per-candidate activated security. -/
def activatedPA (c : Q → W → Bool) (V : Q → W → ℚ) (a : Q) (w : W) : ℚ := ind (c a) w * V a w

/-- **Per-action transfer.**  Unactivated regret `≤ ε + max_a η_a`, where `η_a` bounds the
void mass of candidate `a`'s own certification. -/
theorem per_action_transfer (π : W → ℚ) (c : Q → W → Bool) (V : Q → W → ℚ)
    (â : Q) (ε : ℚ) (η : Q → ℚ) (ηmax : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hlo : ∀ a w, 0 ≤ V a w) (hhi : ∀ a w, V a w ≤ 1)
    (hη : ∀ a, expect π (fun w => 1 - ind (c a) w) ≤ η a) (hmax : ∀ a, η a ≤ ηmax)
    (hreg : ∀ a, expect π (activatedPA c V a) - expect π (activatedPA c V â) ≤ ε) :
    ∀ a, expect π (V a) - expect π (V â) ≤ ε + ηmax := by
  intro a
  have hA : ∀ b, expect π (activatedPA c V b) = expect π (activated (c b) V b) := fun b => rfl
  obtain ⟨_, ha_hi⟩ := excess_bounds π (c a) V a 0 1 hπ (hlo a)
    (fun w => by simpa using hhi a w)
  obtain ⟨hâ_lo, _⟩ := excess_bounds π (c â) V â 0 1 hπ (hlo â)
    (fun w => by simpa using hhi â w)
  have h1 := hreg a
  rw [hA a, hA â] at h1
  have h2 := hη a
  have h3 := hmax a
  nlinarith

/-- **The conditional argmax breaks.**  One world; candidate `0` is worth `3/5` and
always certified, candidate `1` is worth `1` and certified with mass `1/2`.  Activated
expectations order `0 > 1`; the payoffs order `1 > 0`. -/
def π₂ : Fin 2 → ℚ := ![1/2, 1/2]
def c₂ : Fin 2 → Fin 2 → Bool := ![![true, true], ![true, false]]
def V₂ : Fin 2 → Fin 2 → ℚ := ![![3/5, 3/5], ![1, 1]]

theorem argmax_breaks :
    expect π₂ (activatedPA c₂ V₂ 1) < expect π₂ (activatedPA c₂ V₂ 0) ∧
    expect π₂ (V₂ 0) < expect π₂ (V₂ 1) := by
  constructor <;> norm_num [expect, activatedPA, ind, π₂, c₂, V₂, Fin.sum_univ_two]

end PerAction

/-! ## Vacuity -/

/-- **Vacuous activation.**  If the contract is always void, every selection has zero
activated regret, whatever the payoffs. -/
theorem vacuous (π : W → ℚ) (V : Q → W → ℚ) (â a : Q) :
    expect π (activated (fun _ => false) V a) - expect π (activated (fun _ => false) V â)
      = 0 := by
  simp [expect, activated, ind]

/-! ## The Logical-Induction-shaped form

Prices replace `π` and the finite identities become asymptotic relations over real
sequences, exactly as `InheritedAlgebra.value_asymptotic` is stated.  The three named
inputs are what linearity of expectation (`thm:loe`) and provability induction over the
provable pointwise inequalities `0 ≤ V − U ≤ 1 − c` (`thm:expprovind`) supply; nothing
here derives them. -/

open LogicalInduction

/-- **Availability transfer, asymptotic.**  `EV a`, `EU a`, `Evoid` are the novice's
day-`n` expectations of `V a`, `U a = c · V a`, and `1 − c`.  `hLower`: the activated
security is never worth more than the payoff.  `hUpper`: the excess is at most the void
mass.  `hη`: void mass at most `η`.  `hreg`: activated regret at most `ε` at the
selection.  Conclusion: unactivated regret at most `ε + η`, asymptotically. -/
theorem availability_transfer_asymptotic {Q : Type*}
    (EV EU : Q → ℕ → ℝ) (Evoid : ℕ → ℝ) (â : Q) (ε η : ℝ)
    (hLower : ∀ a, EU a ≲ₙ EV a)
    (hUpper : ∀ a, (fun n => EV a n - EU a n) ≲ₙ Evoid)
    (hη : Evoid ≲ₙ fun _ => η)
    (hreg : ∀ a, (fun n => EU a n - EU â n) ≲ₙ fun _ => ε) :
    ∀ a, (fun n => EV a n - EV â n) ≲ₙ fun _ => ε + η := by
  intro a δ hδ
  have hδ4 : 0 < δ / 4 := by positivity
  filter_upwards [hLower â (δ/4) hδ4, hUpper a (δ/4) hδ4, hη (δ/4) hδ4, hreg a (δ/4) hδ4]
    with n h1 h2 h3 h4
  show EV a n - EV â n ≤ ε + η + δ
  linarith

end Workspace.Deference.Contrib.ActivatedValue

#print axioms Workspace.Deference.Contrib.ActivatedValue.pairwise
#print axioms Workspace.Deference.Contrib.ActivatedValue.argmax_iff
#print axioms Workspace.Deference.Contrib.ActivatedValue.availability_transfer_range
#print axioms Workspace.Deference.Contrib.ActivatedValue.availability_transfer
#print axioms Workspace.Deference.Contrib.ActivatedValue.availability_transfer_strategy
#print axioms Workspace.Deference.Contrib.ActivatedValue.Sharp.transfer_sharp
#print axioms Workspace.Deference.Contrib.ActivatedValue.PerAction.per_action_transfer
#print axioms Workspace.Deference.Contrib.ActivatedValue.PerAction.argmax_breaks
#print axioms Workspace.Deference.Contrib.ActivatedValue.vacuous
#print axioms Workspace.Deference.Contrib.ActivatedValue.availability_transfer_asymptotic
