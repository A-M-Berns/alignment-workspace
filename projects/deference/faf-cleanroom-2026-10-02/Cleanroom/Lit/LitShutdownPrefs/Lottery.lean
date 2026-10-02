import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# `lit-shutdown-prefs` — the lottery carrier (Target 1)

Finitely supported probability distributions over an arbitrary type `T` (the trajectory type
is `List ℝ`, which is infinite, so the support is a `Finsupp`), with:

* `expect X g = ∑_{t ∈ supp X} X t · g t` — every quantity in the package is an `expect`;
* **product-form conditioning**: `mass X q = ∑_{t ∈ q} X t` and `condSum X q φ = ∑_{t ∈ q} X t · φ t`.
  "The sublottery of `X` on `q` has expected `φ` at least `s`" is *defined* as
  `condSum X q φ ≥ s · mass X q`, and "`E[φ | q; X] ≥ E[φ | q; Y]`" as
  `condSum X q φ · mass Y q ≥ condSum Y q φ · mass X q`; ratio forms are lemmas. This keeps
  Timestep Dominance's footnoted condition (0) (mandate, Carrier §) from becoming a junk value.
* `dirac`, `mix a ha X Y = a • X + (1 − a) • Y` (the membership proof `ha : a ∈ [0,1]` is an
  explicit argument: there is no clamping), `map φ X` (push-forward), `condOn X q h` (the
  sublottery on `q`, defined only under `h : 0 < mass X q`), and the two-part decomposition
  `X = mass X q • condOn X q + mass X ¬q • condOn X ¬q`.

Nothing here is FAF's: FAF has no lotteries over an arbitrary type (mandate, Header).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

open Finset

/-- A lottery on `T`: a finitely supported real function with nonnegative values summing
to one. Over the infinite type `List ℝ` this is the only finite-support option.
Source: [[lit-shutdown-prefs-mandate]] Carrier § (Thornley 2023 §5 "lotteries are
probability distributions over trajectories")
Kind: D
Fidelity: exact -/
@[ext]
structure Lottery (T : Type) where
  /-- the probability mass function -/
  p : T →₀ ℝ
  /-- masses are nonnegative -/
  nonneg : ∀ t, 0 ≤ p t
  /-- masses sum to one -/
  sum_one : ∑ t ∈ p.support, p t = 1

/-! ## Weighted sums over a finsupp (infrastructure) -/

/-- `wsum f g = ∑_{t ∈ supp f} f t · g t`. Definitionally `f.sum (fun t x => x * g t)`.
Source: none: infrastructure
Kind: D -/
noncomputable def wsum {T : Type} (f : T →₀ ℝ) (g : T → ℝ) : ℝ := ∑ t ∈ f.support, f t * g t

section wsum

variable {T T' : Type}

/-- The weighted sum may be taken over any finite set containing the support.
Source: none: infrastructure
Kind: L -/
theorem wsum_eq_sum_of_subset (f : T →₀ ℝ) (g : T → ℝ) {S : Finset T} (hS : f.support ⊆ S) :
    wsum f g = ∑ t ∈ S, f t * g t := by
  unfold wsum
  refine sum_subset hS fun t _ ht => ?_
  have : f t = 0 := by simpa [Finsupp.mem_support_iff] using ht
  simp [this]

/-- `wsum` is additive in the finsupp.
Source: none: infrastructure
Kind: L -/
theorem wsum_add (f₁ f₂ : T →₀ ℝ) (g : T → ℝ) : wsum (f₁ + f₂) g = wsum f₁ g + wsum f₂ g := by
  classical
  rw [wsum_eq_sum_of_subset (f₁ + f₂) g Finsupp.support_add,
    wsum_eq_sum_of_subset f₁ g (subset_union_left (s₂ := f₂.support)),
    wsum_eq_sum_of_subset f₂ g (subset_union_right (s₁ := f₁.support)), ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  simp [add_mul]

/-- `wsum` is homogeneous in the finsupp.
Source: none: infrastructure
Kind: L -/
theorem wsum_smul (a : ℝ) (f : T →₀ ℝ) (g : T → ℝ) : wsum (a • f) g = a * wsum f g := by
  rw [wsum_eq_sum_of_subset (a • f) g Finsupp.support_smul, wsum, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  simp [mul_assoc]

/-- `wsum` of a point mass.
Source: none: infrastructure
Kind: L -/
theorem wsum_single (t : T) (c : ℝ) (g : T → ℝ) : wsum (Finsupp.single t c) g = c * g t := by
  by_cases hc : c = 0
  · subst hc; simp [wsum]
  · rw [wsum, Finsupp.support_single t hc, sum_singleton, Finsupp.single_eq_same]

/-- `wsum` is linear in the weight function.
Source: none: infrastructure
Kind: L -/
theorem wsum_add_right (f : T →₀ ℝ) (g₁ g₂ : T → ℝ) :
    wsum f (fun t => g₁ t + g₂ t) = wsum f g₁ + wsum f g₂ := by
  unfold wsum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  dsimp only
  ring

/-- `wsum` is homogeneous in the weight function.
Source: none: infrastructure
Kind: L -/
theorem wsum_smul_right (f : T →₀ ℝ) (c : ℝ) (g : T → ℝ) :
    wsum f (fun t => c * g t) = c * wsum f g := by
  unfold wsum
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  dsimp only
  ring

/-- `wsum` of a push-forward.
Source: none: infrastructure
Kind: L -/
theorem wsum_mapDomain (φ : T → T') (f : T →₀ ℝ) (g : T' → ℝ) :
    wsum (f.mapDomain φ) g = wsum f (fun t => g (φ t)) := by
  change (f.mapDomain φ).sum (fun t x => x * g t) = f.sum (fun t x => x * g (φ t))
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- `wsum` of a filtered finsupp is the weighted sum against the indicator-weighted function.
Source: none: infrastructure
Kind: L -/
theorem wsum_filter (q : T → Prop) [DecidablePred q] (f : T →₀ ℝ) (g : T → ℝ) :
    wsum (f.filter q) g = wsum f (fun t => if q t then g t else 0) := by
  unfold wsum
  rw [Finsupp.support_filter, sum_filter]
  refine sum_congr rfl fun t _ => ?_
  by_cases h : q t <;> simp [h]

/-- Monotonicity of `wsum` in the weight function, for nonnegative finsupps.
Source: none: infrastructure
Kind: L -/
theorem wsum_le_wsum (f : T →₀ ℝ) (hf : ∀ t, 0 ≤ f t) (g₁ g₂ : T → ℝ) (h : ∀ t, g₁ t ≤ g₂ t) :
    wsum f g₁ ≤ wsum f g₂ :=
  sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (hf t)

/-- Nonnegativity of `wsum` for nonnegative finsupp and nonnegative weight.
Source: none: infrastructure
Kind: L -/
theorem wsum_nonneg (f : T →₀ ℝ) (hf : ∀ t, 0 ≤ f t) (g : T → ℝ) (hg : ∀ t, 0 ≤ g t) :
    0 ≤ wsum f g :=
  sum_nonneg fun t _ => mul_nonneg (hf t) (hg t)

/-- `wsum` against the constant `1` is the total mass.
Source: none: infrastructure
Kind: L -/
theorem wsum_one (f : T →₀ ℝ) : wsum f (fun _ => 1) = ∑ t ∈ f.support, f t := by
  unfold wsum; simp

/-- `wsum` of the zero finsupp.
Source: none: infrastructure
Kind: L -/
@[simp] theorem wsum_zero (g : T → ℝ) : wsum (0 : T →₀ ℝ) g = 0 := by
  simp [wsum]

/-- `wsum` of a finite sum of finsupps.
Source: none: infrastructure
Kind: L -/
theorem wsum_finset_sum {ι : Type} (s : Finset ι) (f : ι → T →₀ ℝ) (g : T → ℝ) :
    wsum (∑ i ∈ s, f i) g = ∑ i ∈ s, wsum (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, wsum_add, ih]

end wsum

namespace Lottery

variable {T T' : Type}

/-- The finite support of a lottery.
Source: [[lit-shutdown-prefs-mandate]] Carrier §
Kind: D -/
def support (X : Lottery T) : Finset T := X.p.support

/-- Support membership is positive mass.
Source: none: infrastructure
Kind: L -/
theorem mem_support_iff_pos (X : Lottery T) (t : T) : t ∈ X.support ↔ 0 < X.p t := by
  unfold support
  rw [Finsupp.mem_support_iff]
  exact ⟨fun h => lt_of_le_of_ne (X.nonneg t) (Ne.symm h), fun h => h.ne'⟩

/-- Expectation `E_X[g] = ∑_{t ∈ supp X} X t · g t`.
Source: [[lit-shutdown-prefs-mandate]] Carrier § ("expected sum-total utility", Thornley 2024 §11)
Kind: D
Fidelity: exact -/
noncomputable def expect (X : Lottery T) (g : T → ℝ) : ℝ := wsum X.p g

/-- Mass of a decidable event: `mass X q = ∑_{t ∈ supp X, q t} X t`.
Source: [[lit-shutdown-prefs-mandate]] Carrier § (product-form conditioning)
Kind: D
Fidelity: exact -/
noncomputable def mass (X : Lottery T) (q : T → Prop) [DecidablePred q] : ℝ :=
  X.expect (fun t => if q t then 1 else 0)

/-- The event-restricted sum `condSum X q φ = ∑_{t ∈ q} X t · φ t` — the numerator of the
conditional expectation `E[φ | q; X]`, kept in product form (no division).
Source: [[lit-shutdown-prefs-mandate]] Carrier § (product-form conditioning)
Kind: D
Fidelity: exact -/
noncomputable def condSum (X : Lottery T) (q : T → Prop) [DecidablePred q] (φ : T → ℝ) : ℝ :=
  X.expect (fun t => if q t then φ t else 0)

/-- Total mass is one.
Source: none: infrastructure
Kind: L -/
theorem expect_const_one (X : Lottery T) : X.expect (fun _ => 1) = 1 := by
  rw [expect, wsum_one, X.sum_one]

/-- Every mass lies in `[0, 1]`.
Source: none: infrastructure
Kind: L -/
theorem mass_nonneg (X : Lottery T) (q : T → Prop) [DecidablePred q] : 0 ≤ X.mass q :=
  wsum_nonneg _ X.nonneg _ fun t => by split_ifs <;> norm_num

/-- Every mass lies in `[0, 1]`.
Source: none: infrastructure
Kind: L -/
theorem mass_le_one (X : Lottery T) (q : T → Prop) [DecidablePred q] : X.mass q ≤ 1 := by
  rw [← X.expect_const_one]
  exact wsum_le_wsum _ X.nonneg _ _ fun t => by split_ifs <;> norm_num

/-- The mass of the whole space.
Source: none: infrastructure
Kind: L -/
theorem mass_true (X : Lottery T) : X.mass (fun _ => True) = 1 := by
  simp [mass, expect_const_one]

/-- Complementary masses sum to one.
Source: none: infrastructure
Kind: L -/
theorem mass_add_mass_not (X : Lottery T) (q : T → Prop) [DecidablePred q] :
    X.mass q + X.mass (fun t => ¬ q t) = 1 := by
  unfold mass expect
  rw [← wsum_add_right]
  have : (fun t => (if q t then (1 : ℝ) else 0) + (if ¬ q t then 1 else 0)) = fun _ => 1 := by
    funext t; by_cases h : q t <;> simp [h]
  rw [this, wsum_one, X.sum_one]

/-- The event-restricted sum is bounded by the mass times a bound on `φ`.
Source: none: infrastructure
Kind: L -/
theorem condSum_le_mass_mul (X : Lottery T) (q : T → Prop) [DecidablePred q] (φ : T → ℝ) (M : ℝ)
    (hM : ∀ t, q t → φ t ≤ M) : X.condSum q φ ≤ M * X.mass q := by
  unfold condSum mass expect
  rw [← wsum_smul_right]
  refine wsum_le_wsum _ X.nonneg _ _ fun t => ?_
  by_cases h : q t <;> simp [h, hM t]

/-! ## Dirac, mixture, push-forward -/

/-- The point mass at `t`.
Source: [[lit-shutdown-prefs-mandate]] Carrier §
Kind: D
Fidelity: exact -/
noncomputable def dirac (t : T) : Lottery T where
  p := Finsupp.single t 1
  nonneg := fun s => by
    classical
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  sum_one := by
    rw [Finsupp.support_single t one_ne_zero, sum_singleton, Finsupp.single_eq_same]

/-- `E_{dirac t}[g] = g t`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem expect_dirac (t : T) (g : T → ℝ) : (dirac t).expect g = g t := by
  simp [expect, dirac, wsum_single]

/-- The mixture `a • X + (1 − a) • Y`, for `a ∈ [0, 1]` (proof-carrying; no clamping).
Source: [[lit-shutdown-prefs-mandate]] Carrier §; Thornley 2023 §6 (`pX + (1−p)Y`)
Kind: D
Fidelity: exact -/
noncomputable def mix (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (X Y : Lottery T) : Lottery T where
  p := a • X.p + (1 - a) • Y.p
  nonneg := fun t => by
    have hX := X.nonneg t; have hY := Y.nonneg t
    obtain ⟨h0, h1⟩ := ha
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : 0 ≤ 1 - a := by linarith
    positivity
  sum_one := by
    have h := wsum_add (a • X.p) ((1 - a) • Y.p) (fun _ => 1)
    rw [wsum_one, wsum_smul, wsum_smul, wsum_one, wsum_one, X.sum_one, Y.sum_one] at h
    rw [h]; ring

/-- `E_{a X + (1−a) Y}[g] = a E_X[g] + (1−a) E_Y[g]`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem expect_mix (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (X Y : Lottery T) (g : T → ℝ) :
    (mix a ha X Y).expect g = a * X.expect g + (1 - a) * Y.expect g := by
  simp [expect, mix, wsum_add, wsum_smul]

/-- The mass function of a mixture.
Source: none: infrastructure
Kind: L -/
theorem mix_p (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (X Y : Lottery T) :
    (mix a ha X Y).p = a • X.p + (1 - a) • Y.p := rfl

/-- Mixing is symmetric: `a X + (1−a) Y = (1−a) Y + a X`.
Source: none: infrastructure
Kind: L -/
theorem mix_comm (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (ha' : 1 - a ∈ Set.Icc (0 : ℝ) 1)
    (X Y : Lottery T) : mix a ha X Y = mix (1 - a) ha' Y X := by
  ext1; simp [mix_p, sub_sub_cancel, add_comm]

/-- Mixing with weight one returns the first lottery.
Source: none: infrastructure
Kind: L -/
theorem mix_one (X Y : Lottery T) : mix 1 (by norm_num) X Y = X := by
  ext1; simp [mix_p]

/-- Mixing with weight zero returns the second lottery.
Source: none: infrastructure
Kind: L -/
theorem mix_zero (X Y : Lottery T) : mix 0 (by norm_num) X Y = Y := by
  ext1; simp [mix_p]

/-- Mixing a lottery with itself is the identity.
Source: none: infrastructure
Kind: L -/
theorem mix_self (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (X : Lottery T) : mix a ha X X = X := by
  ext1; simp only [mix_p, ← add_smul]; simp

/-- Push-forward of a lottery along a map of outcomes.
Source: [[lit-shutdown-prefs-mandate]] Target 2 (`P a := P₀.map (a, ·)`)
Kind: D
Fidelity: exact -/
noncomputable def map (φ : T → T') (X : Lottery T) : Lottery T' where
  p := X.p.mapDomain φ
  nonneg := fun s => by
    have h0 : (0 : T →₀ ℝ) ≤ X.p := Finsupp.le_def.mpr fun t => by simpa using X.nonneg t
    simpa using Finsupp.le_def.mp (Finsupp.mapDomain_nonneg (f := φ) h0) s
  sum_one := by
    have h := wsum_mapDomain φ X.p (fun _ => 1)
    rw [wsum_one, wsum_one, X.sum_one] at h
    exact h

/-- `E_{map φ X}[g] = E_X[g ∘ φ]`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem expect_map (φ : T → T') (X : Lottery T) (g : T' → ℝ) :
    (map φ X).expect g = X.expect (fun t => g (φ t)) := by
  simp [expect, map, wsum_mapDomain]

/-- The mass function of a push-forward.
Source: none: infrastructure
Kind: L -/
theorem map_p (φ : T → T') (X : Lottery T) : (map φ X).p = X.p.mapDomain φ := rfl

/-- Push-forward commutes with mixing.
Source: none: infrastructure
Kind: L -/
theorem map_mix (φ : T → T') (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (X Y : Lottery T) :
    map φ (mix a ha X Y) = mix a ha (map φ X) (map φ Y) := by
  ext1; simp [map_p, mix_p, Finsupp.mapDomain_add, Finsupp.mapDomain_smul]

/-- Push-forward of a point mass.
Source: none: infrastructure
Kind: L -/
theorem map_dirac (φ : T → T') (t : T) : map φ (dirac t) = dirac (φ t) := by
  ext1; simp [map_p, dirac, Finsupp.mapDomain_single]

/-- Distinct point masses are distinct lotteries.
Source: none: infrastructure
Kind: L -/
theorem dirac_injective : Function.Injective (dirac (T := T)) := by
  intro s t h
  have := congrArg (fun X : Lottery T => X.p t) h
  simp only [dirac, Finsupp.single_eq_same] at this
  by_contra hne
  classical
  simp [hne] at this

/-! ## Conditioning (defined only on positive-mass events) -/

/-- The sublottery of `X` on the event `q`, defined only when `0 < mass X q`
(Thornley 2023 §6 / 2024 §11: "probabilities scaled up proportionally so that they add to 1").
Source: [[lit-shutdown-prefs-mandate]] Carrier §; Thornley 2024 §11 (sublottery)
Kind: D
Fidelity: exact (the positivity hypothesis is explicit: no junk value at mass 0) -/
noncomputable def condOn (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q) :
    Lottery T where
  p := (X.mass q)⁻¹ • X.p.filter q
  nonneg := fun t => by
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.filter_apply]
    have := X.nonneg t
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr h.le) this
    · simp
  sum_one := by
    have e := wsum_smul (X.mass q)⁻¹ (X.p.filter q) (fun _ => 1)
    rw [wsum_filter, wsum_one] at e
    rw [e]
    change (X.mass q)⁻¹ * X.mass q = 1
    exact inv_mul_cancel₀ h.ne'

/-- Conditional expectation in ratio form: `E_{condOn X q}[g] = condSum X q g / mass X q`.
Source: [[lit-shutdown-prefs-mandate]] Carrier § ("ratio forms are lemmas")
Kind: L -/
theorem expect_condOn (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q)
    (g : T → ℝ) : (X.condOn q h).expect g = X.condSum q g / X.mass q := by
  simp only [expect, condOn, condSum, wsum_smul, wsum_filter]
  rw [div_eq_inv_mul]

/-- The product-form identity `mass X q · E_{condOn X q}[g] = condSum X q g`.
Source: [[lit-shutdown-prefs-mandate]] Carrier §
Kind: L -/
theorem mass_mul_expect_condOn (X : Lottery T) (q : T → Prop) [DecidablePred q]
    (h : 0 < X.mass q) (g : T → ℝ) : X.mass q * (X.condOn q h).expect g = X.condSum q g := by
  rw [expect_condOn, mul_div_cancel₀ _ h.ne']

/-- The conditioned lottery lives on `q`.
Source: none: infrastructure
Kind: L -/
theorem mass_condOn_self (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q) :
    (X.condOn q h).mass q = 1 := by
  unfold mass
  rw [expect_condOn, condSum]
  have : X.expect (fun t => if q t then (if q t then (1 : ℝ) else 0) else 0) = X.mass q := by
    unfold mass; congr 1; funext t; by_cases hq : q t <;> simp [hq]
  rw [this, div_self h.ne']

/-- The mass function of the conditioned lottery, scaled back: `mass X q • condOn = filter`.
Source: none: infrastructure
Kind: L -/
theorem mass_smul_condOn_p (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q) :
    X.mass q • (X.condOn q h).p = X.p.filter q := by
  simp only [condOn, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

/-- Two-part decomposition: `X = mass X q • condOn X q + mass X ¬q • condOn X ¬q`
(as mass functions), when both parts have positive mass.
Source: [[lit-shutdown-prefs-mandate]] Target 2 (pointwise lift), Target 8(a) (length decomposition)
Kind: L -/
theorem p_eq_decomp (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q)
    (h' : 0 < X.mass (fun t => ¬ q t)) :
    X.p = X.mass q • (X.condOn q h).p + X.mass (fun t => ¬ q t) • (X.condOn (fun t => ¬ q t) h').p := by
  rw [mass_smul_condOn_p, mass_smul_condOn_p]
  ext t
  simp only [Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hq : q t <;> simp [hq]

/-- The two-part decomposition as a mixture: `X = mix (mass X q) (condOn X q) (condOn X ¬q)`.
Source: [[lit-shutdown-prefs-mandate]] Target 2 (pointwise lift)
Kind: L -/
theorem eq_mix_condOn (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q)
    (h' : 0 < X.mass (fun t => ¬ q t)) :
    X = mix (X.mass q) ⟨X.mass_nonneg q, X.mass_le_one q⟩ (X.condOn q h)
      (X.condOn (fun t => ¬ q t) h') := by
  ext1
  rw [mix_p, X.p_eq_decomp q h h']
  congr 2
  have := X.mass_add_mass_not q
  linarith

/-- The mass of a point-event is the point's probability.
Source: none: infrastructure
Kind: L -/
theorem mass_eq_point [DecidableEq T] (X : Lottery T) (t : T) : X.mass (fun s => s = t) = X.p t := by
  unfold mass expect wsum
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hs; simp [hs]
  · intro ht
    have : X.p t = 0 := by simpa [Finsupp.mem_support_iff] using ht
    simp [this]

/-- The sublottery on a positive-mass point is the point mass.
Source: none: infrastructure
Kind: L -/
theorem condOn_point [DecidableEq T] (X : Lottery T) (t : T) (h : 0 < X.mass (fun s => s = t)) :
    X.condOn (fun s => s = t) h = dirac t := by
  ext1
  have hpt : X.p t ≠ 0 := by rw [mass_eq_point] at h; exact h.ne'
  have hf : X.p.filter (fun s => s = t) = Finsupp.single t (X.p t) := by
    ext s
    rw [Finsupp.filter_apply, Finsupp.single_apply]
    by_cases hs : s = t
    · subst hs; simp
    · simp [hs, Ne.symm hs]
  show (X.mass (fun s => s = t))⁻¹ • X.p.filter (fun s => s = t) = Finsupp.single t 1
  rw [mass_eq_point, hf, Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ hpt]

/-- The support of a lottery is nonempty.
Source: none: infrastructure
Kind: L -/
theorem support_nonempty (X : Lottery T) : X.support.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := X.sum_one
  rw [show X.p.support = ∅ from h, sum_empty] at this
  exact zero_ne_one this

/-- An event containing a support point has positive mass.
Source: none: infrastructure
Kind: L -/
theorem mass_pos_of_mem (X : Lottery T) (q : T → Prop) [DecidablePred q] (t : T)
    (ht : t ∈ X.support) (hq : q t) : 0 < X.mass q := by
  unfold mass expect wsum
  have ht' : t ∈ X.p.support := ht
  have h1 : X.p t * (if q t then (1 : ℝ) else 0) ≤
      ∑ s ∈ X.p.support, X.p s * (if q s then 1 else 0) :=
    Finset.single_le_sum (f := fun s => X.p s * (if q s then (1 : ℝ) else 0))
      (fun s _ => mul_nonneg (X.nonneg s) (by split_ifs <;> norm_num)) ht'
  rw [if_pos hq, mul_one] at h1
  exact lt_of_lt_of_le ((X.mem_support_iff_pos t).mp ht) h1

/-- The support of the conditioned lottery is the support filtered by the event.
Source: none: infrastructure
Kind: L -/
theorem support_condOn (X : Lottery T) (q : T → Prop) [DecidablePred q] (h : 0 < X.mass q) :
    (X.condOn q h).support = X.support.filter q := by
  show ((X.mass q)⁻¹ • X.p.filter q).support = X.p.support.filter q
  rw [Finsupp.support_smul_eq (inv_ne_zero h.ne'), Finsupp.support_filter]

/-- A lottery whose support is a singleton is that point mass.
Source: none: infrastructure
Kind: L -/
theorem eq_dirac_of_support_eq (X : Lottery T) (t : T) (h : X.support = {t}) : X = dirac t := by
  have h1 : X.p t = 1 := by
    have := X.sum_one
    rw [show X.p.support = {t} from h, sum_singleton] at this
    exact this
  ext1
  ext s
  classical
  show X.p s = Finsupp.single t 1 s
  rw [Finsupp.single_apply]
  by_cases hs : t = s
  · subst hs; simp [h1]
  · rw [if_neg hs]
    have : s ∉ X.p.support := by rw [show X.p.support = {t} from h]; simpa using Ne.symm hs
    exact Finsupp.notMem_support_iff.mp this

/-- Expectation is monotone in the weight.
Source: none: infrastructure
Kind: L -/
theorem expect_mono (X : Lottery T) {g₁ g₂ : T → ℝ} (h : ∀ t, g₁ t ≤ g₂ t) :
    X.expect g₁ ≤ X.expect g₂ :=
  wsum_le_wsum _ X.nonneg _ _ h

/-- Expectation is additive in the weight.
Source: none: infrastructure
Kind: L -/
theorem expect_add (X : Lottery T) (g₁ g₂ : T → ℝ) :
    X.expect (fun t => g₁ t + g₂ t) = X.expect g₁ + X.expect g₂ :=
  wsum_add_right _ _ _

/-- Expectation is homogeneous in the weight.
Source: none: infrastructure
Kind: L -/
theorem expect_smul (X : Lottery T) (c : ℝ) (g : T → ℝ) :
    X.expect (fun t => c * g t) = c * X.expect g :=
  wsum_smul_right _ _ _

/-- Expectation of a constant.
Source: none: infrastructure
Kind: L -/
theorem expect_const (X : Lottery T) (c : ℝ) : X.expect (fun _ => c) = c := by
  have := X.expect_smul c (fun _ => 1)
  simp only [mul_one] at this
  rw [this, expect_const_one, mul_one]

/-- Expectation depends only on the weight's values on the support.
Source: none: infrastructure
Kind: L -/
theorem expect_congr (X : Lottery T) {g₁ g₂ : T → ℝ} (h : ∀ t ∈ X.support, g₁ t = g₂ t) :
    X.expect g₁ = X.expect g₂ :=
  sum_congr rfl fun t ht => by rw [h t ht]

end Lottery

end Cleanroom.Lit.LitShutdownPrefs
