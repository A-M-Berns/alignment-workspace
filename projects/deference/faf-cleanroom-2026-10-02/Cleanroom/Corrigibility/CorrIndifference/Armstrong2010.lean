import Cleanroom.Corrigibility.CorrIndifference.Estimators

/-!
# Armstrong 2010, Proposition 2.2 and Theorem 2.3 (T10)

The FHI technical report's construction: a finite `Ω` with prior `P`, an event `ΩX` (the
worlds where the probabilistic event `X` happens), its outcome `X : Ω → Bool`, and the
partition `[ΩX]` of `ΩX` into "same history up to `X`" classes, here the classes of a label map
`π` (with `ΩX` a union of classes). `E₁ := E ∩ {X = 1}`, `E₀ := E ∩ {X = 0}`, the intrinsic
utility `U(S) := E_P[u | S]`, and the rescaled `v := u` off `E₁`, `u − U(E₁) + U(E₀)` on `E₁`.
Proposition 2.2: `V(E₁) = V(E₀)`. Theorem 2.3, in its precise form: for every class `E`,
`∑_{ω ∈ E} P(ω) v_P(ω) = P(E) · U_P(E₀)` — the contribution of a class to any `v`-expectation
depends only on the class mass and on `P`'s conditional within `E₀`, not on `P(E₁ | E)` — so two
priors agreeing on those quantities give the same `v`-expectation on every *saturated* set (a
union of classes plus a subset of `ΩXᶜ` on which they agree). The source's "indifferent to the
value of `p`" conflates the probability `p` with the outcome `X`; this is the claim it supports
(finding F10). The `/0` singularity §3 names is a hypothesis where it matters, never junk in a
headline.

Source: [[corr-refs-inventory]] 013 / armstrong-2010-utility-indifference-fhi-technical-report §2
(l. 40–80).
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Armstrong2010

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Estimators

set_option linter.unusedSectionVars false

variable {Ω C : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq C]

/-- **The intrinsic utility of a set** `U(S) := (∑_{ω ∈ S} P(ω) u(ω)) / P(S)` (the report's
`u(S | S)`; junk `0` at `P(S) = 0` — the singularity the report's §3 warns of; disclosed).
Source: [[corr-refs-inventory]] 013 / armstrong-2010 §2 (`U(S)`)
Kind: D
Fidelity: exact (division convention disclosed) -/
noncomputable def U (P : Distr Ω) (u : Ω → ℝ) (S : Finset Ω) : ℝ :=
  (∑ ω ∈ S, P.mass ω * u ω) / ∑ ω ∈ S, P.mass ω

/-- `E₁(ω) := [ω] ∩ {X = 1}` for the class `[ω]` of `π`. Source: armstrong-2010 §2. Kind: D. Fidelity: exact -/
def E1 (π : Ω → C) (X : Ω → Bool) (ω : Ω) : Finset Ω := (cls π ω).filter (fun ω' => X ω' = true)

/-- `E₀(ω) := [ω] ∩ {X = 0}`. Source: armstrong-2010 §2. Kind: D. Fidelity: exact -/
def E0 (π : Ω → C) (X : Ω → Bool) (ω : Ω) : Finset Ω := (cls π ω).filter (fun ω' => X ω' = false)

/-- **The rescaled utility `v`:** `u` off `ΩX ∩ {X = 1}`, `u − U(E₁) + U(E₀)` on it.
Source: [[corr-refs-inventory]] 013 / armstrong-2010 §2 (the definition of `v`)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def v (P : Distr Ω) (u : Ω → ℝ) (ΩX : Finset Ω) (π : Ω → C) (X : Ω → Bool) :
    Ω → ℝ := fun ω =>
  if ω ∈ ΩX ∧ X ω = true then u ω - U P u (E1 π X ω) + U P u (E0 π X ω) else u ω

/-- `E₁` and `E₀` are constant on a class. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma E1_eq_of_mem (π : Ω → C) (X : Ω → Bool) {ω ω' : Ω} (h : ω' ∈ cls π ω) :
    E1 π X ω' = E1 π X ω := by unfold E1; rw [cls_eq_of_mem π h]

/-- `E₀` is constant on a class. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma E0_eq_of_mem (π : Ω → C) (X : Ω → Bool) {ω ω' : Ω} (h : ω' ∈ cls π ω) :
    E0 π X ω' = E0 π X ω := by unfold E0; rw [cls_eq_of_mem π h]

/-- **`ΩX` is a union of classes** (the classes are histories *up to `X`*, so membership in `ΩX`
is a class property).
Source: [[corr-refs-inventory]] 013 / armstrong-2010 §2 ("partition of `ΩX`")
Kind: D
Fidelity: exact -/
def Saturated (π : Ω → C) (S : Finset Ω) : Prop := ∀ ω ∈ S, cls π ω ⊆ S

/-- A class of a point of a saturated set lies in it. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_of_saturated {π : Ω → C} {S : Finset Ω} (hS : Saturated π S) {ω ω' : Ω} (hω : ω ∈ S)
    (h : ω' ∈ cls π ω) : ω' ∈ S := hS ω hω h

/-- The mass-weighted sum of a constant over `S` is the constant times the mass.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_mass_mul_const (P : Distr Ω) (S : Finset Ω) (k : ℝ) :
    ∑ ω ∈ S, P.mass ω * k = (∑ ω ∈ S, P.mass ω) * k := by rw [sum_mul]

/-- `P(S) · U(S) = ∑_{S} P u`, junk-safe (at `P(S) = 0` every point of `S` has mass `0`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mass_mul_U (P : Distr Ω) (u : Ω → ℝ) (S : Finset Ω) :
    (∑ ω ∈ S, P.mass ω) * U P u S = ∑ ω ∈ S, P.mass ω * u ω := by
  unfold U
  by_cases h : ∑ ω ∈ S, P.mass ω = 0
  · rw [h, zero_mul]
    rw [sum_eq_zero_iff_of_nonneg (fun ω _ => P.nonneg ω)] at h
    exact (sum_eq_zero fun ω hω => by rw [h ω hω, zero_mul]).symm
  · field_simp

/-- **Proposition 2.2: `V(E₁) = V(E₀)`** — `v` is indifferent between the two outcomes of `X`
within a class, for `ω ∈ ΩX` with `P(E₁), P(E₀) > 0`.
Source: [[corr-refs-inventory]] 013 / armstrong-2010 Proposition 2.2
Kind: L
Fidelity: exact
Hyps: (a) positivity of the two masses (the report's implicit assumption; §3 names the singularity) -/
theorem prop_2_2 (P : Distr Ω) (u : Ω → ℝ) (ΩX : Finset Ω) (π : Ω → C) (X : Ω → Bool) {ω : Ω}
    (hω : ω ∈ ΩX) (hΩX : Saturated π ΩX)
    (h1 : 0 < ∑ ω' ∈ E1 π X ω, P.mass ω') (h0 : 0 < ∑ ω' ∈ E0 π X ω, P.mass ω') :
    U P (v P u ΩX π X) (E1 π X ω) = U P (v P u ΩX π X) (E0 π X ω) := by
  have hv1 : ∀ ω' ∈ E1 π X ω, v P u ΩX π X ω' = u ω' - U P u (E1 π X ω) + U P u (E0 π X ω) := by
    intro ω' hω'
    have hc : ω' ∈ cls π ω := (mem_filter.mp hω').1
    have hX : X ω' = true := (mem_filter.mp hω').2
    have hcond : ω' ∈ ΩX ∧ X ω' = true := ⟨mem_of_saturated hΩX hω hc, hX⟩
    simp only [v, if_pos hcond, E1_eq_of_mem π X hc, E0_eq_of_mem π X hc]
  have hv0 : ∀ ω' ∈ E0 π X ω, v P u ΩX π X ω' = u ω' := by
    intro ω' hω'
    have hX : X ω' = false := (mem_filter.mp hω').2
    simp only [v, hX, Bool.false_eq_true, and_false, if_false]
  have hU1 : U P (v P u ΩX π X) (E1 π X ω) = U P u (E0 π X ω) := by
    change (∑ ω' ∈ E1 π X ω, P.mass ω' * v P u ΩX π X ω') / (∑ ω' ∈ E1 π X ω, P.mass ω') =
      U P u (E0 π X ω)
    rw [sum_congr rfl (fun ω' (h : ω' ∈ E1 π X ω) => by rw [hv1 ω' h])]
    rw [div_eq_iff (ne_of_gt h1)]
    have : ∑ ω' ∈ E1 π X ω, P.mass ω' * (u ω' - U P u (E1 π X ω) + U P u (E0 π X ω)) =
        ∑ ω' ∈ E1 π X ω, P.mass ω' * u ω' -
          (∑ ω' ∈ E1 π X ω, P.mass ω') * U P u (E1 π X ω) +
          (∑ ω' ∈ E1 π X ω, P.mass ω') * U P u (E0 π X ω) := by
      simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, sum_mul]
    rw [this, mass_mul_U]; ring
  have hU0 : U P (v P u ΩX π X) (E0 π X ω) = U P u (E0 π X ω) := by
    change (∑ ω' ∈ E0 π X ω, P.mass ω' * v P u ΩX π X ω') / (∑ ω' ∈ E0 π X ω, P.mass ω') =
      U P u (E0 π X ω)
    rw [sum_congr rfl (fun ω' (h : ω' ∈ E0 π X ω) => by rw [hv0 ω' h])]
    rfl
  rw [hU1, hU0]

/-- **Theorem 2.3, the per-class identity:** for `ω ∈ ΩX`,
`∑_{ω' ∈ [ω]} P(ω') v_P(ω') = P([ω]) · U_P(E₀(ω))` — a class's contribution to any
`v`-expectation depends only on the class mass and on `P`'s conditional within `E₀`, whatever
`P(E₁ | E)` is. Unconditional (junk-safe at either mass `0`).
Source: [[corr-refs-inventory]] 013 / armstrong-2010 Theorem 2.3 (the content of its proof)
Kind: P
Fidelity: exact (the precise claim behind "indifferent to the value of `p`")
Hyps: (a) -/
theorem class_sum_v (P : Distr Ω) (u : Ω → ℝ) (ΩX : Finset Ω) (π : Ω → C) (X : Ω → Bool) {ω : Ω}
    (hω : ω ∈ ΩX) (hΩX : Saturated π ΩX) :
    ∑ ω' ∈ cls π ω, P.mass ω' * v P u ΩX π X ω' = classMass P π ω * U P u (E0 π X ω) := by
  have hsplit : cls π ω = E1 π X ω ∪ E0 π X ω := by
    ext ω'; simp only [E1, E0, mem_union, mem_filter]
    constructor
    · intro h; cases hX : X ω' <;> simp [h, hX]
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint (E1 π X ω) (E0 π X ω) := by
    rw [disjoint_left]; intro ω' h1 h0
    have := (mem_filter.mp h1).2; have := (mem_filter.mp h0).2; simp_all
  have hv1 : ∀ ω' ∈ E1 π X ω, v P u ΩX π X ω' = u ω' - U P u (E1 π X ω) + U P u (E0 π X ω) := by
    intro ω' hω'
    have hc : ω' ∈ cls π ω := (mem_filter.mp hω').1
    have hX : X ω' = true := (mem_filter.mp hω').2
    have hcond : ω' ∈ ΩX ∧ X ω' = true := ⟨mem_of_saturated hΩX hω hc, hX⟩
    simp only [v, if_pos hcond, E1_eq_of_mem π X hc, E0_eq_of_mem π X hc]
  have hv0 : ∀ ω' ∈ E0 π X ω, v P u ΩX π X ω' = u ω' := by
    intro ω' hω'
    have hX : X ω' = false := (mem_filter.mp hω').2
    simp only [v, hX, Bool.false_eq_true, and_false, if_false]
  unfold classMass
  rw [hsplit, sum_union hdisj, sum_union hdisj,
    sum_congr rfl (fun ω' (h : ω' ∈ E1 π X ω) => by rw [hv1 ω' h]),
    sum_congr rfl (fun ω' (h : ω' ∈ E0 π X ω) => by rw [hv0 ω' h])]
  have : ∑ ω' ∈ E1 π X ω, P.mass ω' * (u ω' - U P u (E1 π X ω) + U P u (E0 π X ω)) =
      ∑ ω' ∈ E1 π X ω, P.mass ω' * u ω' -
        (∑ ω' ∈ E1 π X ω, P.mass ω') * U P u (E1 π X ω) +
        (∑ ω' ∈ E1 π X ω, P.mass ω') * U P u (E0 π X ω) := by
    simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, sum_mul]
  rw [this, mass_mul_U, ← mass_mul_U P u (E0 π X ω)]; ring

/-- **Theorem 2.3, the invariance:** two priors with the same class masses on `ΩX`, the same
`E₀`-conditionals (`U_P(E₀) = U_{P'}(E₀)`) and equal masses off `ΩX` give the same
`v`-expectation on every saturated `S` (a union of classes and a subset of `ΩXᶜ`), *with each
prior's own `v`*: `∑_{ω ∈ S} P v_P = ∑_{ω ∈ S} P' v_{P'}`. `P(E₁ | E)` is arbitrary — this is the
"indifference to `p`" the report's Theorem 2.3 asserts, stated precisely (`v` depends on the
prior through `U`; the report's `p` is `P(E₁ | E)`, not the outcome `X`).
Source: [[corr-refs-inventory]] 013 / armstrong-2010 Theorem 2.3
Kind: C
Fidelity: exact (the precise form; finding F10)
Hyps: (a) the three agreement hypotheses and saturation name the theorem's scope -/
theorem theorem_2_3 (P P' : Distr Ω) (u : Ω → ℝ) (ΩX : Finset Ω) (π : Ω → C) (X : Ω → Bool)
    (hΩX : Saturated π ΩX)
    (hmass : ∀ ω ∈ ΩX, classMass P π ω = classMass P' π ω)
    (hcond : ∀ ω ∈ ΩX, U P u (E0 π X ω) = U P' u (E0 π X ω))
    (hoff : ∀ ω ∉ ΩX, P.mass ω = P'.mass ω)
    (S : Finset Ω) (hS : Saturated π S) :
    ∑ ω ∈ S, P.mass ω * v P u ΩX π X ω = ∑ ω ∈ S, P'.mass ω * v P' u ΩX π X ω := by
  -- group each side by classes: sum over the image of `π`, then over fibres
  have key : ∀ (Q : Distr Ω), ∑ ω ∈ S, Q.mass ω * v Q u ΩX π X ω =
      ∑ c ∈ S.image π, ∑ ω ∈ S.filter (fun ω => π ω = c), Q.mass ω * v Q u ΩX π X ω := fun Q =>
    (sum_fiberwise_of_maps_to (fun ω hω => mem_image_of_mem π hω) _).symm
  rw [key P, key P']
  apply sum_congr rfl
  intro c hc
  obtain ⟨ω₀, hω₀, rfl⟩ := mem_image.mp hc
  have hfib : S.filter (fun ω => π ω = π ω₀) = cls π ω₀ := by
    ext ω; simp only [mem_filter, mem_cls]
    exact ⟨fun h => h.2, fun h => ⟨hS ω₀ hω₀ ((mem_cls π ω₀ ω).mpr h), h⟩⟩
  rw [hfib]
  by_cases hX : ω₀ ∈ ΩX
  · rw [class_sum_v P u ΩX π X hX hΩX, class_sum_v P' u ΩX π X hX hΩX, hmass ω₀ hX, hcond ω₀ hX]
  · -- off `ΩX` the whole class is off `ΩX` (saturation of `ΩX`), so `v = u` and the masses agree
    apply sum_congr rfl
    intro ω hω
    have hnot : ω ∉ ΩX := fun h => hX (hΩX ω h ((mem_cls π ω ω₀).mpr ((mem_cls π ω₀ ω).mp hω).symm))
    simp only [v, hnot, false_and, if_false, hoff ω hnot]

end Cleanroom.Corrigibility.CorrIndifference.Armstrong2010
