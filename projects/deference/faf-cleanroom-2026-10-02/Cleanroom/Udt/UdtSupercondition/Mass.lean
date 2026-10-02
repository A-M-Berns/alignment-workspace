import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Event mass, conditioning and the fibre toolkit for `udt-supercondition`

Representation of record (mandate, "Representation of record"): a countable discrete probability
space is a type `Ω` with `P : PMF Ω` (values in `ℝ≥0∞`, sums are `tsum`, no summability side
conditions). Atoms are points. This file defines

* `mass P s` — the mass of an event, `P.toOuterMeasure s = ∑' x, s.indicator P x`;
* `condOn P s h` — Bayesian conditioning on an event of positive mass (SC §0.8), the *only*
  place a division by an event mass occurs; every division in the package sits behind the
  positivity hypothesis `h`;
* the fibre toolkit: `tsum_fiber` (a sum over `X` is the sum over the fibres of `g : X → Y`),
  `mass_inter_preimage_eq_tsum` (mass of `U ∩ g ⁻¹' T` is the sum over `y ∈ T` of the
  masses of `U ∩ g ⁻¹' {y}`), and `map_apply_eq_mass` (`P.map f y = mass P (f ⁻¹' {y})`).

SC's random variables (σ-algebra homomorphisms `Q̄ → P̄`) are point functions `q : Ω → Q`
(SC §0.2: in the countable discrete setting every homomorphism is induced by a point function),
pushforward is `P.map q`, and probability preservation is `P.map q = Q`. A point function need
not be surjective: a homomorphism may send a nonempty event to `⊥`.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω X Y : Type*}

/-! ### Event mass -/

/-- The mass `P(s)` of an event `s` under `P`: `P.toOuterMeasure s`, i.e. `∑' x, s.indicator P x`.
Source: [[superconditioning-mismatched-ontologies]] §0.4, §0.7 (sums over atoms)
Kind: D
Fidelity: exact (countable discrete: an event's measure is the sum of its atoms' masses)
Hyps: n/a -/
noncomputable def mass (P : PMF Ω) (s : Set Ω) : ℝ≥0∞ := P.toOuterMeasure s

/-- `mass P s` is the sum of `P` over `s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_eq_tsum (P : PMF Ω) (s : Set Ω) : mass P s = ∑' x, s.indicator P x :=
  P.toOuterMeasure_apply s

/-- The mass of a singleton is the point mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_singleton (P : PMF Ω) (x : Ω) : mass P {x} = P x :=
  P.toOuterMeasure_apply_singleton x

/-- The whole space has mass `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_univ (P : PMF Ω) : mass P univ = 1 := by
  rw [mass_eq_tsum, indicator_univ, P.tsum_coe]

/-- The empty event has mass `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_empty (P : PMF Ω) : mass P ∅ = 0 := P.toOuterMeasure.empty

/-- Mass is monotone in the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_mono (P : PMF Ω) {s t : Set Ω} (h : s ⊆ t) : mass P s ≤ mass P t :=
  P.toOuterMeasure.mono h

/-- Every event has mass at most `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_le_one (P : PMF Ω) (s : Set Ω) : mass P s ≤ 1 := by
  rw [← mass_univ P]; exact mass_mono P (subset_univ s)

/-- Event masses are finite.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_ne_top (P : PMF Ω) (s : Set Ω) : mass P s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one P s)

/-- A point of an event weighs at most the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem apply_le_mass (P : PMF Ω) {s : Set Ω} {x : Ω} (hx : x ∈ s) : P x ≤ mass P s := by
  rw [← mass_singleton]; exact mass_mono P (singleton_subset_iff.2 hx)

/-- An event has mass `0` iff every point of it has mass `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_eq_zero_iff (P : PMF Ω) (s : Set Ω) : mass P s = 0 ↔ ∀ x ∈ s, P x = 0 := by
  rw [mass_eq_tsum, ENNReal.tsum_eq_zero]
  constructor
  · intro h x hx
    have := h x
    rwa [indicator_of_mem hx] at this
  · intro h x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]; exact h x hx
    · exact indicator_of_notMem hx _

/-- An event has positive mass iff some point of it has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_pos_iff (P : PMF Ω) (s : Set Ω) : 0 < mass P s ↔ ∃ x ∈ s, 0 < P x := by
  constructor
  · intro h
    by_contra hne
    apply h.ne'
    rw [mass_eq_zero_iff]
    intro x hx
    by_contra hx0
    exact hne ⟨x, hx, pos_iff_ne_zero.2 hx0⟩
  · rintro ⟨x, hx, hpos⟩
    exact lt_of_lt_of_le hpos (apply_le_mass P hx)

/-- An event has mass `1` iff it contains the support.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_eq_one_iff (P : PMF Ω) (s : Set Ω) : mass P s = 1 ↔ ∀ x, P x ≠ 0 → x ∈ s := by
  rw [mass, PMF.toOuterMeasure_apply_eq_one_iff]
  constructor
  · intro h x hx; exact h ((P.mem_support_iff x).2 hx)
  · intro h x hx; exact h x ((P.mem_support_iff x).1 hx)

/-- Disjoint events have additive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_union_of_disjoint (P : PMF Ω) {s t : Set Ω} (h : Disjoint s t) :
    mass P (s ∪ t) = mass P s + mass P t := by
  simp only [mass_eq_tsum, indicator_union_of_disjoint h, ENNReal.tsum_add]

/-- An event and its complement split the mass of any event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_inter_add_mass_inter_compl (P : PMF Ω) (s t : Set Ω) :
    mass P (s ∩ t) + mass P (s ∩ tᶜ) = mass P s := by
  rw [← mass_union_of_disjoint P (disjoint_of_subset inter_subset_right inter_subset_right
    disjoint_compl_right), ← inter_union_distrib_left, union_compl_self, inter_univ]

/-- The mass of `s ∩ {x}` is the indicator of `s` at `x` times `P x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_inter_singleton (P : PMF Ω) (s : Set Ω) (x : Ω) :
    mass P (s ∩ {x}) = s.indicator P x := by
  by_cases hx : x ∈ s
  · rw [inter_eq_right.2 (singleton_subset_iff.2 hx), mass_singleton, indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    have : s ∩ {x} = ∅ := by
      ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hy, rfl⟩; exact hx hy
    rw [this, mass_empty]

/-- Mass under a pushforward is mass of the preimage.
Source: [[superconditioning-mismatched-ontologies]] §0.4 (pushforward)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mass_map (P : PMF X) (f : X → Y) (s : Set Y) : mass (P.map f) s = mass P (f ⁻¹' s) :=
  PMF.toOuterMeasure_map_apply f P s

/-- The pushforward evaluated at a point is the mass of its fibre.
Source: [[superconditioning-mismatched-ontologies]] §0.4 (pushforward)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem map_apply_eq_mass (P : PMF X) (f : X → Y) (y : Y) : P.map f y = mass P (f ⁻¹' {y}) := by
  rw [← mass_singleton, mass_map]

/-- Mass under a bind is the `P`-average of the kernel masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_bind (P : PMF X) (f : X → PMF Y) (s : Set Y) :
    mass (P.bind f) s = ∑' x, P x * mass (f x) s :=
  PMF.toOuterMeasure_bind_apply P f s

/-! ### The fibre toolkit -/

/-- A sum over `X` is the sum over the fibres of `g : X → Y` (indicator form).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_fiber (g : X → Y) (f : X → ℝ≥0∞) :
    ∑' x, f x = ∑' y, ∑' x, (g ⁻¹' {y}).indicator f x := by
  have h : ∀ x, f x = ∑' y, (g ⁻¹' {y}).indicator f x := fun x => by
    rw [tsum_eq_single (g x)]
    · rw [indicator_of_mem (by simp)]
    · intro y hy
      exact indicator_of_notMem (fun h => hy (by simpa using h.symm)) f
  rw [tsum_congr h, ENNReal.tsum_comm]

/-- The mass of `U ∩ g ⁻¹' T` is the sum over `y ∈ T` of the masses of `U ∩ g ⁻¹' {y}`.
Source: [[superconditioning-mismatched-ontologies]] §0.7 (sums over atoms of a sub-algebra)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mass_inter_preimage_eq_tsum (μ : PMF X) (U : Set X) (g : X → Y) (T : Set Y) :
    mass μ (U ∩ g ⁻¹' T) = ∑' y, T.indicator (fun y => mass μ (U ∩ g ⁻¹' {y})) y := by
  rw [mass_eq_tsum, tsum_fiber g]
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ T
  · rw [indicator_of_mem hy, mass_eq_tsum]
    refine tsum_congr fun x => ?_
    rw [indicator_indicator]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2 ▸ hy⟩
  · rw [indicator_of_notMem hy]
    refine ENNReal.tsum_eq_zero.2 fun x => ?_
    rw [indicator_indicator]
    apply indicator_of_notMem
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, not_and]
    intro hx _ hT; exact hy (hx ▸ hT)

/-- The mass of a preimage is the sum of the fibre masses over the target set.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_preimage_eq_tsum (μ : PMF X) (g : X → Y) (T : Set Y) :
    mass μ (g ⁻¹' T) = ∑' y, T.indicator (fun y => mass μ (g ⁻¹' {y})) y := by
  simpa using mass_inter_preimage_eq_tsum μ univ g T

/-- The mass of `U` is the sum over all fibres of `g` of the masses of `U ∩ g ⁻¹' {y}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_eq_tsum_fiber (μ : PMF X) (U : Set X) (g : X → Y) :
    mass μ U = ∑' y, mass μ (U ∩ g ⁻¹' {y}) := by
  simpa using mass_inter_preimage_eq_tsum μ U g univ

/-- The pushforward's mass on `T` is the sum of the pushforward over `T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_map_eq_tsum (P : PMF X) (f : X → Y) (T : Set Y) :
    mass (P.map f) T = ∑' y, T.indicator (P.map f) y :=
  mass_eq_tsum _ _

/-- A sum of `u (g x) * P x` over a fibre of `g` factors as `u y * mass P (g ⁻¹' {y})`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_indicator_fiber_mul (P : PMF X) (g : X → Y) (u : Y → ℝ≥0∞) (y : Y) :
    ∑' x, (g ⁻¹' {y}).indicator (fun x => u (g x) * P x) x = u y * mass P (g ⁻¹' {y}) := by
  rw [mass_eq_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ g ⁻¹' {y}
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    have : g x = y := hx
    rw [this]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- A sum of `u (g x) * P x` over `X` regroups as the sum over `y` of `u y * mass P (g ⁻¹' {y})`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_comp_mul_eq_tsum_fiber (P : PMF X) (g : X → Y) (u : Y → ℝ≥0∞) :
    ∑' x, u (g x) * P x = ∑' y, u y * mass P (g ⁻¹' {y}) := by
  rw [tsum_fiber g]
  exact tsum_congr fun y => tsum_indicator_fiber_mul P g u y

/-- Fibre masses of the pushforward sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_mass_fiber (P : PMF X) (g : X → Y) : ∑' y, mass P (g ⁻¹' {y}) = 1 := by
  have := (P.map g).tsum_coe
  simpa only [map_apply_eq_mass] using this

/-! ### Conditioning -/

/-- Bayesian conditioning `P(· | s)` on an event of positive mass (SC §0.8):
`condOn P s h x = s.indicator P x * (mass P s)⁻¹`. The positivity hypothesis `h` is the
only licence for the division in the package.
Source: [[superconditioning-mismatched-ontologies]] §0.8
Kind: D
Fidelity: exact (defined only under `0 < P(s)`, as the source)
Hyps: n/a -/
noncomputable def condOn (P : PMF Ω) (s : Set Ω) (h : 0 < mass P s) : PMF Ω :=
  PMF.normalize (s.indicator P) (by rw [← mass_eq_tsum]; exact h.ne')
    (P.tsum_coe_indicator_ne_top s)

/-- The conditioned mass function.
Source: [[superconditioning-mismatched-ontologies]] §0.8
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condOn_apply (P : PMF Ω) (s : Set Ω) (h : 0 < mass P s) (x : Ω) :
    condOn P s h x = s.indicator P x * (mass P s)⁻¹ := by
  show s.indicator P x * (∑' y, s.indicator P y)⁻¹ = _
  rw [mass_eq_tsum]

/-- The conditioned mass function on a point of the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condOn_apply_of_mem (P : PMF Ω) {s : Set Ω} (h : 0 < mass P s) {x : Ω} (hx : x ∈ s) :
    condOn P s h x = P x * (mass P s)⁻¹ := by
  rw [condOn_apply, indicator_of_mem hx]

/-- The conditioned mass function vanishes off the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condOn_apply_of_notMem (P : PMF Ω) {s : Set Ω} (h : 0 < mass P s) {x : Ω} (hx : x ∉ s) :
    condOn P s h x = 0 := by
  rw [condOn_apply, indicator_of_notMem hx, zero_mul]

/-- Mass under the conditioned measure: `P(t | s) = P(t ∩ s) / P(s)`.
Source: [[superconditioning-mismatched-ontologies]] §0.8
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mass_condOn (P : PMF Ω) (s : Set Ω) (h : 0 < mass P s) (t : Set Ω) :
    mass (condOn P s h) t = mass P (t ∩ s) * (mass P s)⁻¹ := by
  rw [mass_eq_tsum, mass_eq_tsum, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  have hc : ⇑(condOn P s h) = fun x => s.indicator P x * (mass P s)⁻¹ := funext (condOn_apply P s h)
  rw [hc, indicator_mul_const, indicator_indicator]

/-- The multiplicative form of conditioning: `P(t | s) · P(s) = P(t ∩ s)`.
Source: [[superconditioning-mismatched-ontologies]] §0.8
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mass_condOn_mul (P : PMF Ω) (s : Set Ω) (h : 0 < mass P s) (t : Set Ω) :
    mass (condOn P s h) t * mass P s = mass P (t ∩ s) := by
  rw [mass_condOn, mul_assoc, ENNReal.inv_mul_cancel h.ne' (mass_ne_top P s), mul_one]

/-- The conditioning event has conditional mass `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_condOn_self (P : PMF Ω) (s : Set Ω) (h : 0 < mass P s) :
    mass (condOn P s h) s = 1 := by
  rw [mass_condOn, inter_self, ENNReal.mul_inv_cancel h.ne' (mass_ne_top P s)]

/-- Conditioning on the whole space does nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condOn_univ (P : PMF Ω) (h : 0 < mass P univ) : condOn P univ h = P := by
  refine PMF.ext fun x => ?_
  rw [condOn_apply, indicator_univ, mass_univ, inv_one, mul_one]

/-- Positivity of a conditional mass forces positivity of the intersection.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pos_of_mass_condOn_pos (P : PMF Ω) {s : Set Ω} (h : 0 < mass P s) {t : Set Ω}
    (ht : 0 < mass (condOn P s h) t) : 0 < mass P (s ∩ t) := by
  rw [mass_condOn] at ht
  rw [inter_comm]
  exact (ENNReal.mul_pos_iff.1 ht).1

/-- Conditioning twice is conditioning on the intersection.
Source: [[superconditioning-mismatched-ontologies]] §14 (chain rule for conditioning, needed for
transitivity of "downstream")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condOn_condOn (P : PMF Ω) {s t : Set Ω} (hs : 0 < mass P s)
    (ht : 0 < mass (condOn P s hs) t) (hst : 0 < mass P (s ∩ t)) :
    condOn (condOn P s hs) t ht = condOn P (s ∩ t) hst := by
  refine PMF.ext fun x => ?_
  rw [condOn_apply, condOn_apply, mass_condOn, inter_comm t s]
  by_cases hx : x ∈ s ∩ t
  · rw [indicator_of_mem hx, indicator_of_mem hx.2, condOn_apply_of_mem P hs hx.1,
      ENNReal.mul_inv (Or.inl hst.ne') (Or.inl (mass_ne_top P _)), inv_inv]
    calc P x * (mass P s)⁻¹ * ((mass P (s ∩ t))⁻¹ * mass P s)
        = P x * (mass P (s ∩ t))⁻¹ * ((mass P s)⁻¹ * mass P s) := by ring
      _ = P x * (mass P (s ∩ t))⁻¹ := by
        rw [ENNReal.inv_mul_cancel hs.ne' (mass_ne_top P s), mul_one]
  · rw [indicator_of_notMem hx, zero_mul]
    by_cases hxt : x ∈ t
    · have hxs : x ∉ s := fun hxs => hx ⟨hxs, hxt⟩
      rw [indicator_of_mem hxt, condOn_apply_of_notMem P hs hxs, zero_mul]
    · rw [indicator_of_notMem hxt, zero_mul]

/-- Conditioning on a pulled-back event commutes with the pushforward:
`(μ(· | p⁻¹ S))_* p = (p_* μ)(· | S)`.
Source: [[superconditioning-mismatched-ontologies]] §4.6 (the `Ā`-compatible posterior)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condOn_map_preimage (μ : PMF X) (p : X → Y) (S : Set Y) (h : 0 < mass μ (p ⁻¹' S))
    (h' : 0 < mass (μ.map p) S) :
    (condOn μ (p ⁻¹' S) h).map p = condOn (μ.map p) S h' := by
  refine PMF.ext fun y => ?_
  rw [map_apply_eq_mass, mass_condOn, condOn_apply, mass_map, ← preimage_inter]
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, map_apply_eq_mass, inter_eq_left.2 (singleton_subset_iff.2 hy)]
  · rw [indicator_of_notMem hy, zero_mul]
    have : ({y} : Set Y) ∩ S = ∅ := by
      ext z; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hz⟩; exact hy hz
    rw [this, preimage_empty, mass_empty, zero_mul]

end Cleanroom.Udt.UdtSupercondition
