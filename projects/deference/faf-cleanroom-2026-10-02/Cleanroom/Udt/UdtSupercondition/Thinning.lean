import Cleanroom.Udt.UdtSupercondition.Mass

/-!
# The one construction: couplings, thinning and density steering

Every existence theorem of SC Part I (Thm 1.2, Thm 2.4 (⇐), Remark 2.5, Thm 4.5, Prop 4.7) is the
same move (mandate, "The one construction"): start from a coupling `M` on a product carrier, and
*thin* it — enlarge the carrier by a `Bool` layer and put weight `w x · M x` on `(x, true)` and
`(1 − w x) · M x` on `(x, false)`. Then the first marginal is still `M` (`thin_map_fst`), the
evidence `{·.2 = true}` has mass `∑ w · M` (`mass_thin_evTrue`), and conditioning on it gives
`normalize (w · M)` (`thin_condOn_map`). With the *steering weight*
`w x = Q (g x) / (B · (M.map g) (g x))` (and `0` on null fibres) the conditional pushforward
along `g` is exactly the prescribed `Q` (`steerThin_condOn_map`), for any `Q` with
`BoundedDensity Q (M.map g) B`.

This replaces SC's residual measure `C″ = (B·C − C′)/(B − 1)` (SC §2.5, audit finding 7): the
weight is in `[0, 1]` by the bound, and when `B = 1` the `false` layer simply has mass `0`; no
division by `B − 1` occurs anywhere.

Also here: `BoundedDensity Q P B` (the junk-free form of "`Q ≪ P` with `‖dQ/dP‖_∞ ≤ B`"),
`couple P f` (the product coupling `(x, y) ↦ P x · f x y`, the form of every `M` above), and
`toSubtype` (restricting a PMF to a set carrying all its mass — needed because SC's
compatibility `c ∘ p = c′ ∘ p′` is an exact function equality, so a compatible carrier must
exclude off-diagonal points).

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {X Y : Type*}

/-! ### Bounded density -/

/-- `Q ≪ P` with density bounded by `B`, in multiplicative form: `Q x ≤ B * P x` for every atom.
Absolute continuity is included (`P x = 0 → Q x = 0`). This is the junk-free rendering of SC's
"`Q ≪ P` and `‖dQ/dP‖_∞ < ∞`" (SC §0.9): no `rnDeriv`, no `⨆`.
Source: [[superconditioning-mismatched-ontologies]] §0.9
Kind: D
Fidelity: exact (given `B ≠ ⊤`, `∃ B, BoundedDensity Q P B` is SC's condition)
Hyps: n/a -/
def BoundedDensity (Q P : PMF X) (B : ℝ≥0∞) : Prop := ∀ x, Q x ≤ B * P x

/-- Bounded density packages absolute continuity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BoundedDensity.absolutelyContinuous {Q P : PMF X} {B : ℝ≥0∞} (h : BoundedDensity Q P B)
    (x : X) (hx : P x = 0) : Q x = 0 := by
  have := h x
  rw [hx, mul_zero] at this
  exact le_antisymm this zero_le

/-- A density bound is at least `1` (both are probability measures).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BoundedDensity.one_le {Q P : PMF X} {B : ℝ≥0∞} (h : BoundedDensity Q P B) : 1 ≤ B :=
  calc (1 : ℝ≥0∞) = ∑' x, Q x := Q.tsum_coe.symm
    _ ≤ ∑' x, B * P x := ENNReal.tsum_le_tsum h
    _ = B * ∑' x, P x := ENNReal.tsum_mul_left
    _ = B := by rw [P.tsum_coe, mul_one]

/-- A density bound is nonzero.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BoundedDensity.ne_zero {Q P : PMF X} {B : ℝ≥0∞} (h : BoundedDensity Q P B) : B ≠ 0 := by
  intro hB
  have := h.one_le
  rw [hB] at this
  exact (zero_lt_one.not_ge this).elim

/-- Bounded density transfers to event masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BoundedDensity.mass_le {Q P : PMF X} {B : ℝ≥0∞} (h : BoundedDensity Q P B) (s : Set X) :
    mass Q s ≤ B * mass P s := by
  rw [mass_eq_tsum, mass_eq_tsum, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx]; exact h x
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- Bounded density is preserved by pushforward.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BoundedDensity.map {Q P : PMF X} {B : ℝ≥0∞} (h : BoundedDensity Q P B) (f : X → Y) :
    BoundedDensity (Q.map f) (P.map f) B := fun y => by
  rw [map_apply_eq_mass, map_apply_eq_mass]; exact h.mass_le _

/-- Every PMF has bounded density `1` with respect to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem boundedDensity_self (P : PMF X) : BoundedDensity P P 1 := fun x => by rw [one_mul]

/-! ### Product couplings -/

/-- The coupling `(x, y) ↦ P x · f x y` of `P` with a kernel `f` (SC's `P(p̄) · κ_{ā(p̄)}(q̄)`
and `P ⊗ P′` are instances).
Source: [[superconditioning-mismatched-ontologies]] §1.3, §4.4 (the joint on `P̄ ⊗ Q̄`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def couple (P : PMF X) (f : X → PMF Y) : PMF (X × Y) :=
  P.bind fun x => (f x).map (Prod.mk x)

/-- The coupling's mass function.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem couple_apply (P : PMF X) (f : X → PMF Y) (x : X) (y : Y) :
    couple P f (x, y) = P x * f x y := by
  simp only [couple, PMF.bind_apply, map_apply_eq_mass]
  rw [tsum_eq_single x]
  · have : (Prod.mk x) ⁻¹' {(x, y)} = {y} := by ext z; simp [Prod.ext_iff]
    rw [this, mass_singleton]
  · intro a ha
    have : (Prod.mk a) ⁻¹' {(x, y)} = ∅ := by ext z; simp [Prod.ext_iff, ha]
    rw [this, mass_empty, mul_zero]

/-- The first marginal of a coupling is `P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem couple_map_fst (P : PMF X) (f : X → PMF Y) : (couple P f).map Prod.fst = P := by
  rw [couple, PMF.map_bind]
  have h : ∀ x, ((f x).map (Prod.mk x)).map Prod.fst = PMF.pure x := fun x => by
    rw [PMF.map_comp]; exact PMF.map_const (f x) x
  simp_rw [h]
  exact PMF.bind_pure P

/-- The second marginal of a coupling is `P.bind f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem couple_map_snd (P : PMF X) (f : X → PMF Y) : (couple P f).map Prod.snd = P.bind f := by
  rw [couple, PMF.map_bind]
  refine congrArg _ (funext fun x => ?_)
  rw [PMF.map_comp]; exact PMF.map_id (f x)

/-- Mass under a coupling.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_couple (P : PMF X) (f : X → PMF Y) (s : Set (X × Y)) :
    mass (couple P f) s = ∑' x, P x * mass (f x) ((Prod.mk x) ⁻¹' s) := by
  rw [couple, mass_bind]; simp only [mass_map]

/-- Mass of a rectangle under a coupling.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_couple_prod (P : PMF X) (f : X → PMF Y) (U : Set X) (V : Set Y) :
    mass (couple P f) (Prod.fst ⁻¹' U ∩ Prod.snd ⁻¹' V) =
      ∑' x, U.indicator (fun x => P x * mass (f x) V) x := by
  rw [mass_couple]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx]
    have : (Prod.mk x) ⁻¹' (Prod.fst ⁻¹' U ∩ Prod.snd ⁻¹' V) = V := by ext y; simp [hx]
    rw [this]
  · rw [indicator_of_notMem hx]
    have : (Prod.mk x) ⁻¹' (Prod.fst ⁻¹' U ∩ Prod.snd ⁻¹' V) = ∅ := by ext y; simp [hx]
    rw [this, mass_empty, mul_zero]

/-! ### Restriction to a full-measure set -/

/-- A sum over a set `S` of a function vanishing off `S` is the sum over the whole type
(indicator form on the subtype).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_subtype_indicator_comp_val {S : Set X} (g : X → ℝ≥0∞) (hg : ∀ x, x ∉ S → g x = 0)
    (U : Set X) :
    ∑' z : S, (Subtype.val ⁻¹' U).indicator (fun z : S => g z) z = ∑' x, U.indicator g x := by
  have h1 : ∀ z : S, (Subtype.val ⁻¹' U).indicator (fun z : S => g z) z = U.indicator g z :=
    fun z => by
      by_cases hz : (z : X) ∈ U
      · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ Subtype.val ⁻¹' U from hz)]
      · rw [indicator_of_notMem hz, indicator_of_notMem (show z ∉ Subtype.val ⁻¹' U from hz)]
  rw [tsum_congr h1]
  exact tsum_subtype_eq_of_support_subset fun x hx => by
    by_contra hs
    exact hx (indicator_apply_eq_zero.2 fun _ => hg x hs)

/-- Restrict a PMF to a set `S` off which it vanishes: a PMF on the subtype `S`.
Source: none: infrastructure (the compatibility diagonal of SC §2.5 is a subtype carrier)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def toSubtype (M : PMF X) (S : Set X) (h : ∀ x, x ∉ S → M x = 0) : PMF S :=
  ⟨fun z => M z, by
    rw [ENNReal.summable.hasSum_iff, tsum_subtype_eq_of_support_subset (s := S) ?_]
    · exact M.tsum_coe
    · intro x hx
      by_contra hs
      exact hx (h x hs)⟩

/-- The restricted PMF's mass function.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem toSubtype_apply (M : PMF X) (S : Set X) (h : ∀ x, x ∉ S → M x = 0) (z : S) :
    toSubtype M S h z = M z := rfl

/-- Mass of a pulled-back event under the restriction is the mass under `M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_toSubtype_preimage (M : PMF X) (S : Set X) (h : ∀ x, x ∉ S → M x = 0) (T : Set X) :
    mass (toSubtype M S h) (Subtype.val ⁻¹' T) = mass M T := by
  rw [mass_eq_tsum, mass_eq_tsum]
  exact tsum_subtype_indicator_comp_val (S := S) M h T

/-- The restriction pushes forward to `M` along the inclusion.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem toSubtype_map_val (M : PMF X) (S : Set X) (h : ∀ x, x ∉ S → M x = 0) :
    (toSubtype M S h).map Subtype.val = M :=
  PMF.ext fun x => by rw [map_apply_eq_mass, mass_toSubtype_preimage, mass_singleton]

/-- A weighted sum over the restriction is the weighted sum over `X` (weights composed with the
inclusion).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_toSubtype_indicator (M : PMF X) (S : Set X) (h : ∀ x, x ∉ S → M x = 0)
    (w : X → ℝ≥0∞) (U : Set X) :
    ∑' z : S, (Subtype.val ⁻¹' U).indicator (fun z : S => w z * toSubtype M S h z) z =
      ∑' x, U.indicator (fun x => w x * M x) x :=
  tsum_subtype_indicator_comp_val (S := S) (fun x => w x * M x)
    (fun x hx => by rw [h x hx, mul_zero]) U

/-! ### Thinning -/

/-- **Thinning.** Enlarge the carrier by a `Bool` layer: `(x, true) ↦ w x · M x`,
`(x, false) ↦ (1 − w x) · M x`, for a weight `w` with values in `[0, 1]`.
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 (the `D̄`-enrichment
`L̄ = … ⊗ D̄`); mandate, "The one construction"
Kind: D
Fidelity: variant: SC's `D̄`-layer constructions with the weight in `[0, 1]` in place of the
residual measure `C″` (no `B − 1` division; audit finding 7)
Hyps: n/a -/
noncomputable def thin (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) : PMF (X × Bool) :=
  ⟨fun p => if p.2 = true then w p.1 * M p.1 else (1 - w p.1) * M p.1, by
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_prod']
    refine (tsum_congr fun x => ?_).trans M.tsum_coe
    rw [tsum_bool]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [← add_mul, tsub_add_cancel_of_le (hw x), one_mul]⟩

/-- The evidence layer `{p | p.2 = true}` of a thinned carrier.
Source: [[superconditioning-mismatched-ontologies]] §2.5 (`l̄ = d(d̄)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def evTrue (X : Type*) : Set (X × Bool) := {p | p.2 = true}

/-- Thinned mass on the `true` layer.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thin_apply_true (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) (x : X) :
    thin M w hw (x, true) = w x * M x := by
  show (if (true : Bool) = true then w x * M x else (1 - w x) * M x) = w x * M x
  exact if_pos rfl

/-- Thinned mass on the `false` layer.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thin_apply_false (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) (x : X) :
    thin M w hw (x, false) = (1 - w x) * M x := by
  show (if (false : Bool) = true then w x * M x else (1 - w x) * M x) = (1 - w x) * M x
  exact if_neg Bool.false_ne_true

/-- The mass of `U × {true}` under the thinning is `∑_{x ∈ U} w x · M x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_thin_inter_evTrue (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) (U : Set X) :
    mass (thin M w hw) (Prod.fst ⁻¹' U ∩ evTrue X) = ∑' x, U.indicator (fun x => w x * M x) x := by
  rw [mass_eq_tsum, ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  rw [tsum_bool]
  have h1 : (x, false) ∉ Prod.fst ⁻¹' U ∩ evTrue X := fun h => Bool.false_ne_true h.2
  rw [indicator_of_notMem h1, zero_add]
  by_cases hx : x ∈ U
  · rw [indicator_of_mem (show (x, true) ∈ Prod.fst ⁻¹' U ∩ evTrue X from ⟨hx, rfl⟩),
      indicator_of_mem hx, thin_apply_true]
  · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem hx]

/-- The evidence mass of a thinning is `∑ w · M` (thinning lemma (ii)).
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 ("Evidence")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mass_thin_evTrue (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) :
    mass (thin M w hw) (evTrue X) = ∑' x, w x * M x := by
  have := mass_thin_inter_evTrue M w hw univ
  simpa using this

/-- The mass of `U × Bool` under the thinning is `M(U)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_thin_fst (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) (U : Set X) :
    mass (thin M w hw) (Prod.fst ⁻¹' U) = mass M U := by
  rw [mass_eq_tsum, ENNReal.tsum_prod', mass_eq_tsum]
  refine tsum_congr fun x => ?_
  rw [tsum_bool]
  by_cases hx : x ∈ U
  · rw [indicator_of_mem (show (x, false) ∈ Prod.fst ⁻¹' U from hx),
      indicator_of_mem (show (x, true) ∈ Prod.fst ⁻¹' U from hx), indicator_of_mem hx,
      thin_apply_false, thin_apply_true, ← add_mul, tsub_add_cancel_of_le (hw x), one_mul]
  · rw [indicator_of_notMem (show (x, false) ∉ Prod.fst ⁻¹' U from hx),
      indicator_of_notMem (show (x, true) ∉ Prod.fst ⁻¹' U from hx), indicator_of_notMem hx,
      zero_add]

/-- The first marginal of a thinning is `M` (thinning lemma (i)).
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 ("Measure-preservation")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem thin_map_fst (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) :
    (thin M w hw).map Prod.fst = M :=
  PMF.ext fun x => by rw [map_apply_eq_mass, mass_thin_fst, mass_singleton]

/-- Positive total weight gives positive evidence mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thin_evTrue_pos (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1)
    (hpos : 0 < ∑' x, w x * M x) : 0 < mass (thin M w hw) (evTrue X) := by
  rw [mass_thin_evTrue]; exact hpos

/-- Conditioning a thinning on its evidence layer and pushing forward along `g ∘ fst` gives the
`w · M`-weighted fibre masses of `g`, normalized (thinning lemma (iii)).
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 ("Posterior")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem thin_condOn_map (M : PMF X) (w : X → ℝ≥0∞) (hw : ∀ x, w x ≤ 1)
    (hpos : 0 < ∑' x, w x * M x) (g : X → Y) (y : Y) :
    ((condOn (thin M w hw) (evTrue X) (thin_evTrue_pos M w hw hpos)).map (g ∘ Prod.fst)) y =
      (∑' x, (g ⁻¹' {y}).indicator (fun x => w x * M x) x) * (∑' x, w x * M x)⁻¹ := by
  rw [map_apply_eq_mass, mass_condOn, preimage_comp, mass_thin_inter_evTrue, mass_thin_evTrue]

/-! ### Density steering -/

/-- The steering weight `x ↦ Q (g x) / (B · (M.map g) (g x))`, set to `0` on null fibres of
`g` (explicitly, not via `0 / 0 = 0`).
Source: [[superconditioning-mismatched-ontologies]] §2.5 (`(1/B) · C′(c̄)/C(c̄)`), §4.4
(`(1/B) · Q(q̄)/Q₀(q̄)`)
Kind: D
Fidelity: exact (the weight of SC's `d̄` layer, with the null-fibre convention made explicit)
Hyps: n/a -/
noncomputable def steerWeight (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  if M.map g (g x) = 0 then 0 else Q (g x) / (B * M.map g (g x))

/-- The steering weight lies in `[0, 1]` under the density bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerWeight_le_one (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞)
    (h : BoundedDensity Q (M.map g) B) (x : X) : steerWeight M g Q B x ≤ 1 := by
  unfold steerWeight
  split_ifs with h0
  · exact zero_le
  · apply ENNReal.div_le_of_le_mul'
    rw [mul_one]; exact h (g x)

/-- Over the fibre of `g` at `y`, the steered weight-mass sums to `Q y / B`.
Source: [[superconditioning-mismatched-ontologies]] §4.4 (the `Q/Q₀` density cancels
against `Q₀`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem steerWeight_fiber_sum (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q (M.map g) B) (y : Y) :
    ∑' x, (g ⁻¹' {y}).indicator (fun x => steerWeight M g Q B x * M x) x = Q y * B⁻¹ := by
  refine (tsum_indicator_fiber_mul M g
    (fun y => if M.map g y = 0 then 0 else Q y / (B * M.map g y)) y).trans ?_
  show (if M.map g y = 0 then 0 else Q y / (B * M.map g y)) * mass M (g ⁻¹' {y}) = Q y * B⁻¹
  rw [← map_apply_eq_mass]
  by_cases h0 : M.map g y = 0
  · rw [if_pos h0, h0, zero_mul, h.absolutelyContinuous y h0, zero_mul]
  · rw [if_neg h0, div_eq_mul_inv, ENNReal.mul_inv (Or.inl h.ne_zero) (Or.inl hB)]
    calc Q y * (B⁻¹ * (M.map g y)⁻¹) * M.map g y
        = Q y * B⁻¹ * ((M.map g y)⁻¹ * M.map g y) := by ring
      _ = Q y * B⁻¹ := by rw [ENNReal.inv_mul_cancel h0 (PMF.apply_ne_top _ _), mul_one]

/-- The total steered weight-mass is `1 / B`.
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 (`L(l̄) = 1/B`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem steerWeight_total (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q (M.map g) B) :
    ∑' x, steerWeight M g Q B x * M x = B⁻¹ := by
  rw [tsum_fiber g, tsum_congr fun y => steerWeight_fiber_sum M g Q B hB h y,
    ENNReal.tsum_mul_right, Q.tsum_coe, one_mul]

/-- The total steered weight-mass is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerWeight_total_pos (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q (M.map g) B) :
    0 < ∑' x, steerWeight M g Q B x * M x := by
  rw [steerWeight_total M g Q B hB h]; exact ENNReal.inv_pos.2 hB

/-- The steered thinning of `M` towards `Q` along `g`.
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 (the constructed `L`)
Kind: D
Fidelity: variant: see `thin`
Hyps: n/a -/
noncomputable def steerThin (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞)
    (h : BoundedDensity Q (M.map g) B) : PMF (X × Bool) :=
  thin M (steerWeight M g Q B) (steerWeight_le_one M g Q B h)

/-- The steered thinning's first marginal is `M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerThin_map_fst (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞)
    (h : BoundedDensity Q (M.map g) B) : (steerThin M g Q B h).map Prod.fst = M :=
  thin_map_fst _ _ _

/-- The steered thinning's evidence mass is `1 / B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerThin_mass_evTrue (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q (M.map g) B) : mass (steerThin M g Q B h) (evTrue X) = B⁻¹ := by
  rw [steerThin, mass_thin_evTrue, steerWeight_total M g Q B hB h]

/-- The steered thinning's evidence has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerThin_evTrue_pos (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q (M.map g) B) : 0 < mass (steerThin M g Q B h) (evTrue X) :=
  thin_evTrue_pos _ _ _ (steerWeight_total_pos M g Q B hB h)

/-- **Density steering.** Conditioning the steered thinning on its evidence layer and pushing
forward along `g ∘ fst` yields exactly the prescribed `Q`.
Source: [[superconditioning-mismatched-ontologies]] §2.5, §4.4 ("Posterior")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem steerThin_condOn_map (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q (M.map g) B) :
    (condOn (steerThin M g Q B h) (evTrue X) (steerThin_evTrue_pos M g Q B hB h)).map
      (g ∘ Prod.fst) = Q :=
  PMF.ext fun y => by
    have e := thin_condOn_map M (steerWeight M g Q B) (steerWeight_le_one M g Q B h)
      (steerWeight_total_pos M g Q B hB h) g y
    rw [steerWeight_fiber_sum M g Q B hB h, steerWeight_total M g Q B hB h, inv_inv, mul_assoc,
      ENNReal.inv_mul_cancel h.ne_zero hB, mul_one] at e
    exact e

/-- The weighted fibre-mass of the steered thinning over an arbitrary set `U`, in terms of the
weight `v y = Q y / (B · (M.map g) y)`: what the posterior along another projection needs.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerThin_mass_inter_evTrue (M : PMF X) (g : X → Y) (Q : PMF Y) (B : ℝ≥0∞)
    (h : BoundedDensity Q (M.map g) B) (U : Set X) :
    mass (steerThin M g Q B h) (Prod.fst ⁻¹' U ∩ evTrue X) =
      ∑' x, U.indicator (fun x => steerWeight M g Q B x * M x) x :=
  mass_thin_inter_evTrue _ _ _ U

end Cleanroom.Udt.UdtSupercondition
