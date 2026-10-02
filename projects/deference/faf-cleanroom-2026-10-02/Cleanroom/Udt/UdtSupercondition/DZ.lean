import Cleanroom.Udt.UdtSupercondition.Defs

/-!
# The common-information Diaconis–Zabell theorem (SC §1–§2): T1–T6

* T1 `condModel_exists` (SC Thm 1.2): a conditioning model always exists (kind T).
* T2 `compatible_boundedDensity` (SC Thm 2.4 ⇒): a `Ĉ`-compatible model forces
  `C′ ≤ C / μ(ev)`; with SC §2.4's identities `CondModel.map_cL`, `Compatible.post_map_cL`.
* T3 `compatible_range_subset` (the quotient obstruction, dp-cf-105 / AN-22′): a compatible model
  forces `C₁ y = 0` off the range of `c′`; `thm24_sufficiency_refuted` (in `Witnesses.lean`)
  is the `Fin` instance refuting SC Thm 2.4 (⇐) as stated.
* T4 `commonInfo_condModel_iff` (SC Thm 2.4, **repaired**): a compatible model exists iff
  `C′` has bounded density w.r.t. `C` *and* every `C`-positive `y` is in the range of `c′`.
  The construction (`diagModel`) is a thinning of the fibre-diagonal coupling on the subtype
  `{(x, x′) | c x = c′ x′}` — the carrier must be the diagonal because SC's compatibility is an
  exact function equality — with the steering weight `C′(c̄)/(B·C(c̄))`; there is no residual
  measure and no `B − 1` (audit finding 7).
* T5 `sameOntology_condModel_iff` (SC Remark 2.5, classical Diaconis–Zabell) with the finite
  corollary `sameOntology_condModel_iff_of_fintype` and the mixture identity (★_C).
* T6 `trivialCI_condition` (SC Remark 2.6): the trivial common information satisfies T4's
  condition for every pair, recovering T1.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω Ω' : Type} {P : PMF Ω} {P' : PMF Ω'}

/-! ### T1: unconstrained existence -/

/-- **A conditioning model always exists** (SC Thm 1.2): the product coupling with evidence `⊤`.
Source: [[superconditioning-mismatched-ontologies]] §1.3 Thm 1.2 | udt-rep-054 | bli-soto-b-054
Kind: T
Fidelity: exact: point-set over countable types (SC §0.2)
Scope: countable discrete (SC §0.10)
Hyps: (a) none -/
theorem condModel_exists [Countable Ω] [Countable Ω'] (P : PMF Ω) (P' : PMF Ω') :
    HasCondModel P P' :=
  ⟨productModel P P'⟩

/-! ### SC §2.4: consequences of compatibility -/

/-- SC §2.4, first identity: `(c ∘ p)_* μ = C` (needs only preservation).
Source: [[superconditioning-mismatched-ontologies]] §2.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem CondModel.map_cL (m : CondModel P P') (ci : CommonInfo Ω Ω') :
    m.μ.map (ci.c ∘ m.p) = ci.C₁ P := by
  rw [← PMF.map_comp, m.hp]; rfl

/-- SC §2.4, second identity, before compatibility: `(c′ ∘ p′)_* μ(· | ev) = C′`.
Source: [[superconditioning-mismatched-ontologies]] §2.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem CondModel.post_map_c'p' (m : CondModel P P') (ci : CommonInfo Ω Ω') :
    (condOn m.μ m.ev m.hev).map (ci.c' ∘ m.p') = ci.C₂ P' := by
  rw [← PMF.map_comp, m.hp']; rfl

/-- SC §2.4, second identity: for a compatible model, `(c_L)_* μ(· | ev) = C′` with
`c_L = c ∘ p`.
Source: [[superconditioning-mismatched-ontologies]] §2.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem Compatible.post_map_cL {m : CondModel P P'} {ci : CommonInfo Ω Ω'} (hm : Compatible m ci) :
    (condOn m.μ m.ev m.hev).map (ci.c ∘ m.p) = ci.C₂ P' := by
  rw [show ci.c ∘ m.p = ci.c' ∘ m.p' from hm]; exact m.post_map_c'p' ci

/-! ### T2: necessity -/

/-- The multiplicative form of SC Thm 2.4 (⇒): `C′(c̄) · μ(ev) ≤ C(c̄)`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 (⇒)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem Compatible.C₂_mul_le {m : CondModel P P'} {ci : CommonInfo Ω Ω'} (hm : Compatible m ci)
    (y : ci.C) : ci.C₂ P' y * mass m.μ m.ev ≤ ci.C₁ P y := by
  rw [← hm.post_map_cL, map_apply_eq_mass, mass_condOn_mul, ← m.map_cL ci, map_apply_eq_mass]
  exact mass_mono _ inter_subset_left

/-- **SC Thm 2.4 (⇒), necessity:** a `Ĉ`-compatible conditioning model forces `C′ ≪ C` with
density bounded by `1 / μ(ev)`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 (⇒) | udt-rep-055
Kind: P
Fidelity: exact: point-set over countable types (SC §0.2); bound stated multiplicatively
Scope: countable discrete (SC §0.10)
Hyps: (a) all -/
theorem compatible_boundedDensity {m : CondModel P P'} {ci : CommonInfo Ω Ω'}
    (hm : Compatible m ci) : BoundedDensity (ci.C₂ P') (ci.C₁ P) (mass m.μ m.ev)⁻¹ := fun y => by
  rw [mul_comm, ← div_eq_mul_inv]
  exact (ENNReal.le_div_iff_mul_le (Or.inl m.hev.ne') (Or.inl (mass_ne_top _ _))).2
    (hm.C₂_mul_le y)

/-- The bound of `compatible_boundedDensity` is finite.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CondModel.inv_mass_ev_ne_top (m : CondModel P P') : (mass m.μ m.ev)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.2 m.hev.ne'

/-! ### T3: the quotient obstruction -/

/-- **The quotient obstruction:** a `Ĉ`-compatible model forces every `C`-positive shared
proposition to be in the range of `c′`. Proof: `c⁻¹{y}` pulled to `L` equals
`p′⁻¹(c′⁻¹{y}) = ∅` by compatibility, so its `μ`-mass is `0`, but preservation makes it `C(y)`.
Source: dp-cf-105 (AN-22′) | [[cleanup-audit-2026-08-05]] finding 7 ("empty fibres") |
[[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 (⇐) as stated, refuted by
`thm24_sufficiency_refuted`
Kind: P
Fidelity: exact: point-set over countable types; homomorphisms may send events to `⊥` (SC §0.2)
Scope: countable discrete (SC §0.10)
Hyps: (a) all -/
theorem compatible_range_subset {m : CondModel P P'} {ci : CommonInfo Ω Ω'} (hm : Compatible m ci)
    (y : ci.C) (hy : 0 < ci.C₁ P y) : y ∈ Set.range ci.c' := by
  by_contra hr
  apply hy.ne'
  rw [← m.map_cL ci, map_apply_eq_mass, show ci.c ∘ m.p = ci.c' ∘ m.p' from hm]
  have : (ci.c' ∘ m.p') ⁻¹' {y} = ∅ := by
    ext l
    simp only [mem_preimage, Function.comp, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro h; exact hr ⟨m.p' l, h⟩
  rw [this, mass_empty]

/-- Contrapositive form: off the range of `c′`, `C` vanishes.
Source: dp-cf-105 (the stated missing hypothesis "`c′(c̄) = ⊥ ⟹ C(c̄) = 0`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem compatible_C₁_eq_zero_of_notMem_range {m : CondModel P P'} {ci : CommonInfo Ω Ω'}
    (hm : Compatible m ci) (y : ci.C) (hy : y ∉ Set.range ci.c') : ci.C₁ P y = 0 := by
  by_contra h
  exact hy (compatible_range_subset hm y (pos_iff_ne_zero.2 h))

/-- The obstruction persists under a.e. compatibility (AN-22′'s remark: a `μ`-null fibre
instead of an empty one is the same obstruction).
Source: dp-cf-105 (AN-22′)
Kind: L
Fidelity: variant: a.e. compatibility
Hyps: (a) -/
theorem compatibleAE_range_subset {m : CondModel P P'} {ci : CommonInfo Ω Ω'}
    (hm : CompatibleAE m ci) (y : ci.C) (hy : 0 < ci.C₁ P y) : y ∈ Set.range ci.c' := by
  rw [← m.map_cL ci, map_apply_eq_mass, mass_pos_iff] at hy
  obtain ⟨l, hl, hpos⟩ := hy
  exact ⟨m.p' l, (hm l hpos.ne').symm.trans hl⟩

/-! ### T4: the repaired theorem, sufficiency direction -/

section Construction

variable (ci : CommonInfo Ω Ω') (P : PMF Ω) (P' : PMF Ω')

open Classical in
/-- The distribution on `Ω′` in the `c′`-fibre over `y`: `P′(· | c′ = y)` when that fibre has
positive mass, a point mass on the fibre when it is nonempty but null (a choice, disclosed), and
`P′` itself when the fibre is empty (never used: then `C(y) = 0` under the range hypothesis).
Source: [[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 (⇐) proof, `P′(p̄′ | c′ = c̄)`
Kind: D
Fidelity: exact on positive fibres; the null-fibre branch is the repair's choice
Hyps: n/a -/
noncomputable def fibreDist (y : ci.C) : PMF Ω' :=
  if h : 0 < mass P' (ci.c' ⁻¹' {y}) then condOn P' (ci.c' ⁻¹' {y}) h
  else if h' : ∃ x', ci.c' x' = y then PMF.pure (Classical.choose h') else P'

/-- On a positive fibre, `fibreDist` is the conditional.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem fibreDist_of_pos {y : ci.C} (h : 0 < mass P' (ci.c' ⁻¹' {y})) :
    fibreDist ci P' y = condOn P' (ci.c' ⁻¹' {y}) h :=
  dif_pos h

/-- On a nonempty fibre, `fibreDist` is supported in the fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem fibreDist_apply_of_ne {y : ci.C} (hy : y ∈ Set.range ci.c') (x' : Ω')
    (hx' : ci.c' x' ≠ y) : fibreDist ci P' y x' = 0 := by
  unfold fibreDist
  split_ifs with h h'
  · exact condOn_apply_of_notMem P' h hx'
  · rw [PMF.pure_apply, if_neg]
    intro e
    exact hx' (e ▸ Classical.choose_spec h')
  · exact absurd hy h'

/-- The fibre-diagonal set `{(x, x′) | c x = c′ x′}` of SC §2.5.
Source: [[superconditioning-mismatched-ontologies]] §2.5 ("supported on the diagonal")
Kind: D
Fidelity: exact
Hyps: n/a -/
def diagSet : Set (Ω × Ω') := {z | ci.c z.1 = ci.c' z.2}

/-- The fibre-diagonal coupling `(x, x′) ↦ P x · fibreDist (c x) x′`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 (the diagonal coupling, before the
`D̄` layer)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def diagCouple : PMF (Ω × Ω') := couple P fun x => fibreDist ci P' (ci.c x)

/-- Under the range hypothesis the diagonal coupling vanishes off the diagonal.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem diagCouple_vanish (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') :
    ∀ z, z ∉ diagSet ci → diagCouple ci P P' z = 0 := by
  rintro ⟨x, x'⟩ hz
  rw [diagCouple, couple_apply]
  by_cases hx : P x = 0
  · rw [hx, zero_mul]
  · have hpos : 0 < ci.C₁ P (ci.c x) :=
      lt_of_lt_of_le (pos_iff_ne_zero.2 hx)
        (by rw [ci.C₁_apply]; exact apply_le_mass P (show x ∈ ci.c ⁻¹' {ci.c x} from rfl))
    rw [fibreDist_apply_of_ne ci P' (hr _ hpos) x' (fun e => hz e.symm), mul_zero]

/-- The diagonal coupling restricted to the diagonal subtype.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def diagPMF (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') : PMF (diagSet ci) :=
  toSubtype (diagCouple ci P P') (diagSet ci) (diagCouple_vanish ci P P' hr)

/-- The shared-language coordinate on the diagonal.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def diagC : diagSet ci → ci.C := fun z => ci.c z.val.1

/-- The diagonal PMF pushes forward to `P` along the first coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem diagPMF_map_fst (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') :
    (diagPMF ci P P' hr).map (fun z => z.val.1) = P := by
  show (diagPMF ci P P' hr).map (Prod.fst ∘ Subtype.val) = P
  rw [← PMF.map_comp, diagPMF, toSubtype_map_val, diagCouple, couple_map_fst]

/-- The diagonal PMF pushes forward to `C` along the shared coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem diagPMF_map_diagC (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') :
    (diagPMF ci P P' hr).map (diagC ci) = ci.C₁ P := by
  show (diagPMF ci P P' hr).map (ci.c ∘ fun z => z.val.1) = P.map ci.c
  rw [← PMF.map_comp, diagPMF_map_fst]

/-- The steering weight on `C`: `C′(y)/(B·C(y))`, and `0` on null atoms.
Source: [[superconditioning-mismatched-ontologies]] §2.5 (`(1/B)·C′(c̄)/C(c̄)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def vWeight (B : ℝ≥0∞) (y : ci.C) : ℝ≥0∞ :=
  if ci.C₁ P y = 0 then 0 else ci.C₂ P' y / (B * ci.C₁ P y)

/-- The steering weight of the diagonal PMF is `vWeight` of the shared coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerWeight_diagPMF (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') (B : ℝ≥0∞)
    (z : diagSet ci) :
    steerWeight (diagPMF ci P P' hr) (diagC ci) (ci.C₂ P') B z = vWeight ci P P' B (ci.c z.val.1) := by
  unfold steerWeight vWeight
  rw [diagPMF_map_diagC]; rfl

/-- The bounded-density hypothesis, transported to the diagonal PMF.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem boundedDensity_diagPMF (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') {B : ℝ≥0∞}
    (hBD : BoundedDensity (ci.C₂ P') (ci.C₁ P) B) :
    BoundedDensity (ci.C₂ P') ((diagPMF ci P P' hr).map (diagC ci)) B := by
  rw [diagPMF_map_diagC]; exact hBD

/-- The `vWeight`-weighted mass of the diagonal coupling over `{x′}` is `P′ x′ / B`: the
posterior computation of SC Thm 2.4 (⇐), term by term.
Source: [[superconditioning-mismatched-ontologies]] §2.5 ("Posterior on `P̄′`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem diagCouple_weighted_fibre (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hBD : BoundedDensity (ci.C₂ P') (ci.C₁ P) B) (x' : Ω') :
    ∑' z : Ω × Ω', (Prod.snd ⁻¹' {x'}).indicator
      (fun z => vWeight ci P P' B (ci.c z.1) * diagCouple ci P P' z) z = P' x' * B⁻¹ := by
  rw [ENNReal.tsum_prod']
  have e1 : ∀ x, (∑' x'', (Prod.snd ⁻¹' {x'}).indicator
      (fun z => vWeight ci P P' B (ci.c z.1) * diagCouple ci P P' z) (x, x'')) =
      (vWeight ci P P' B (ci.c x) * fibreDist ci P' (ci.c x) x') * P x := fun x => by
    rw [tsum_eq_single x']
    · rw [indicator_of_mem (show (x, x') ∈ Prod.snd ⁻¹' {x'} from rfl), diagCouple, couple_apply]
      ring
    · intro x'' hx''
      exact indicator_of_notMem (s := Prod.snd ⁻¹' {x'}) (a := (x, x''))
        (fun h => hx'' (mem_singleton_iff.1 h))
        (fun z => vWeight ci P P' B (ci.c z.1) * diagCouple ci P P' z)
  rw [tsum_congr e1, tsum_comp_mul_eq_tsum_fiber P ci.c
    (fun y => vWeight ci P P' B y * fibreDist ci P' y x'), tsum_eq_single (ci.c' x')]
  · rw [← ci.C₁_apply, vWeight]
    by_cases h0 : ci.C₁ P (ci.c' x') = 0
    · rw [if_pos h0, zero_mul, zero_mul]
      have : P' x' = 0 := by
        have h1 := hBD (ci.c' x')
        rw [h0, mul_zero] at h1
        have h2 : P' x' ≤ ci.C₂ P' (ci.c' x') := by
          rw [ci.C₂_apply]; exact apply_le_mass P' (show x' ∈ ci.c' ⁻¹' {ci.c' x'} from rfl)
        exact le_antisymm (h2.trans h1) zero_le
      rw [this, zero_mul]
    · rw [if_neg h0]
      by_cases h2 : 0 < mass P' (ci.c' ⁻¹' {ci.c' x'})
      · rw [fibreDist_of_pos ci P' h2, condOn_apply_of_mem P' h2 rfl, ← ci.C₂_apply,
          div_eq_mul_inv, ENNReal.mul_inv (Or.inl hBD.ne_zero) (Or.inl hB)]
        have hC₂ : ci.C₂ P' (ci.c' x') ≠ 0 := by rw [ci.C₂_apply]; exact h2.ne'
        calc ci.C₂ P' (ci.c' x') * (B⁻¹ * (ci.C₁ P (ci.c' x'))⁻¹) *
              (P' x' * (ci.C₂ P' (ci.c' x'))⁻¹) * ci.C₁ P (ci.c' x')
            = P' x' * B⁻¹ * (ci.C₂ P' (ci.c' x') * (ci.C₂ P' (ci.c' x'))⁻¹) *
              ((ci.C₁ P (ci.c' x'))⁻¹ * ci.C₁ P (ci.c' x')) := by ring
          _ = P' x' * B⁻¹ := by
            rw [ENNReal.mul_inv_cancel hC₂ (PMF.apply_ne_top _ _),
              ENNReal.inv_mul_cancel h0 (PMF.apply_ne_top _ _), mul_one, mul_one]
      · have hm : mass P' (ci.c' ⁻¹' {ci.c' x'}) = 0 := le_antisymm (not_lt.1 h2) zero_le
        have hP' : P' x' = 0 := le_antisymm
          ((apply_le_mass P' (show x' ∈ ci.c' ⁻¹' {ci.c' x'} from rfl)).trans hm.le) zero_le
        have hC₂ : ci.C₂ P' (ci.c' x') = 0 := by rw [ci.C₂_apply, hm]
        rw [hC₂, hP', ENNReal.zero_div, zero_mul, zero_mul, zero_mul]
  · intro y hy
    by_cases h0 : ci.C₁ P y = 0
    · rw [← ci.C₁_apply, h0, mul_zero]
    · rw [fibreDist_apply_of_ne ci P' (hr y (pos_iff_ne_zero.2 h0)) x' (Ne.symm hy), mul_zero,
        zero_mul]

/-- **The repaired Thm 2.4 (⇐) model:** the steered thinning of the diagonal coupling, on the
carrier `diagSet ci × Bool`, with `p = (·.1.val.1)`, `p′ = (·.1.val.2)`, evidence the `true`
layer. Compatibility holds pointwise by the carrier; `μ(ev) = 1/B`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 (⇐), repaired (dp-cf-105)
Kind: D
Fidelity: variant: thinning of the fibre-diagonal coupling in place of SC's residual measure
`C″` (no `B − 1` division; audit finding 7); carrier is the diagonal subtype
Hyps: n/a -/
noncomputable def diagModel [Countable Ω] [Countable Ω']
    (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hBD : BoundedDensity (ci.C₂ P') (ci.C₁ P) B) : CondModel P P' where
  L := diagSet ci × Bool
  μ := steerThin (diagPMF ci P P' hr) (diagC ci) (ci.C₂ P') B (boundedDensity_diagPMF ci P P' hr hBD)
  p := fun l => l.1.val.1
  p' := fun l => l.1.val.2
  ev := evTrue (diagSet ci)
  hp := by
    show (steerThin _ _ _ _ _).map ((fun z : diagSet ci => z.val.1) ∘ Prod.fst) = P
    rw [← PMF.map_comp, steerThin_map_fst, diagPMF_map_fst]
  hev := steerThin_evTrue_pos _ _ _ _ hB (boundedDensity_diagPMF ci P P' hr hBD)
  hp' := PMF.ext fun x' => by
    have e := thin_condOn_map (diagPMF ci P P' hr)
      (steerWeight (diagPMF ci P P' hr) (diagC ci) (ci.C₂ P') B)
      (steerWeight_le_one _ _ _ _ (boundedDensity_diagPMF ci P P' hr hBD))
      (steerWeight_total_pos _ _ _ _ hB (boundedDensity_diagPMF ci P P' hr hBD))
      (fun z : diagSet ci => z.val.2) x'
    rw [steerWeight_total _ _ _ _ hB (boundedDensity_diagPMF ci P P' hr hBD)] at e
    have e2 : (∑' z : diagSet ci, ((fun z : diagSet ci => z.val.2) ⁻¹' {x'}).indicator
        (fun z => steerWeight (diagPMF ci P P' hr) (diagC ci) (ci.C₂ P') B z *
          diagPMF ci P P' hr z) z) = P' x' * B⁻¹ := by
      rw [← diagCouple_weighted_fibre ci P P' hr hB hBD x']
      have e3 : (fun z : diagSet ci => steerWeight (diagPMF ci P P' hr) (diagC ci) (ci.C₂ P') B z *
          diagPMF ci P P' hr z) = fun z => (fun z₀ : Ω × Ω' => vWeight ci P P' B (ci.c z₀.1)) z.val *
          toSubtype (diagCouple ci P P') (diagSet ci) (diagCouple_vanish ci P P' hr) z := by
        funext z; rw [steerWeight_diagPMF]; rfl
      rw [e3]
      exact tsum_toSubtype_indicator (diagCouple ci P P') (diagSet ci)
        (diagCouple_vanish ci P P' hr) (fun z₀ => vWeight ci P P' B (ci.c z₀.1))
        (Prod.snd ⁻¹' {x'})
    rw [e2, inv_inv, mul_assoc, ENNReal.inv_mul_cancel hBD.ne_zero hB, mul_one] at e
    exact e

/-- The repaired model is `Ĉ`-compatible (by the carrier).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem diagModel_compatible [Countable Ω] [Countable Ω']
    (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hBD : BoundedDensity (ci.C₂ P') (ci.C₁ P) B) :
    Compatible (diagModel ci P P' hr hB hBD) ci :=
  funext fun l => l.1.property

/-- The repaired model's evidence has mass `1/B`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 ("Evidence: `L(l̄) = 1/B`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem diagModel_mass_ev [Countable Ω] [Countable Ω']
    (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hBD : BoundedDensity (ci.C₂ P') (ci.C₁ P) B) :
    mass (diagModel ci P P' hr hB hBD).μ (diagModel ci P P' hr hB hBD).ev = B⁻¹ :=
  steerThin_mass_evTrue _ _ _ _ hB (boundedDensity_diagPMF ci P P' hr hBD)

end Construction

/-- **SC Thm 2.4, repaired, as an iff:** a `Ĉ`-compatible conditioning model for `(P, P′)`
exists iff `C′` has bounded density w.r.t. `C` **and** every `C`-positive shared proposition is
in the range of `c′`. The second conjunct is absent from SC's statement, which is false without
it (`thm24_sufficiency_refuted`). This is also the answer to bli-soto-b-054's break-off
("what structure on `(P̂, P̂′)` makes existence non-trivial"): a common-information structure,
with this right-hand side as the exact condition.
Source: [[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 (repaired) | udt-rep-055/056 |
dp-cf-105 | bli-soto-b-054
Kind: P
Fidelity: variant: point-set over countable types (SC §0.2); adds the hypothesis
`∀ y, 0 < C₁ y → y ∈ range c′` absent from SC's statement, which is false without it (see
`thm24_sufficiency_refuted`); the (⇐) construction is a thinning (no residual measure)
Scope: countable discrete (SC §0.10); `Compatible` is exact function equality (SC Def 2.3)
Hyps: (a) all -/
theorem commonInfo_condModel_iff [Countable Ω] [Countable Ω'] (ci : CommonInfo Ω Ω') (P : PMF Ω)
    (P' : PMF Ω') :
    (∃ m : CondModel P P', Compatible m ci) ↔
      (∃ B, B ≠ ⊤ ∧ BoundedDensity (ci.C₂ P') (ci.C₁ P) B) ∧
        ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c' := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨_, m.inv_mass_ev_ne_top, compatible_boundedDensity hm⟩,
      fun y hy => compatible_range_subset hm y hy⟩
  · rintro ⟨⟨B, hB, hBD⟩, hr⟩
    exact ⟨diagModel ci P P' hr hB hBD, diagModel_compatible ci P P' hr hB hBD⟩

/-- The evidence mass of the repaired model is the bound's reciprocal, so the bound of
necessity (`1/μ(ev)`) is attained: `B = 1/μ(ev)`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 (the two directions' bounds coincide)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem commonInfo_condModel_exists_with_mass [Countable Ω] [Countable Ω'] (ci : CommonInfo Ω Ω')
    (P : PMF Ω) (P' : PMF Ω') {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hBD : BoundedDensity (ci.C₂ P') (ci.C₁ P) B) (hr : ∀ y, 0 < ci.C₁ P y → y ∈ Set.range ci.c') :
    ∃ m : CondModel P P', Compatible m ci ∧ mass m.μ m.ev = B⁻¹ :=
  ⟨diagModel ci P P' hr hB hBD, diagModel_compatible ci P P' hr hB hBD,
    diagModel_mass_ev ci P P' hr hB hBD⟩

/-! ### T5: same-ontology recovery (classical Diaconis–Zabell) -/

/-- `idCI`'s `C₁` is `P` itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem idCI_C₁ [Countable Ω] (P : PMF Ω) : (idCI Ω).C₁ P = P := PMF.map_id P

/-- `idCI`'s `C₂` is `P′` itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem idCI_C₂ [Countable Ω] (P' : PMF Ω) : (idCI Ω).C₂ P' = P' := PMF.map_id P'

/-- Necessity for same-ontology models: `P′ ≤ P / μ(ev)`.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem SameOntologyModel.boundedDensity [Countable Ω] {P P' : PMF Ω} (m : SameOntologyModel P P') :
    BoundedDensity P' P (mass m.μ m.ev)⁻¹ := by
  have := compatible_boundedDensity m.toCondModel_compatible
  rwa [idCI_C₁, idCI_C₂] at this

/-- **Classical Diaconis–Zabell** (SC Remark 2.5, Diaconis–Zabell 1982): a same-ontology
conditioning model for `P ⟶ P′` exists iff `P′ ≪ P` with bounded density. The range condition
of `commonInfo_condModel_iff` is automatic for `c′ = id`.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5 | udt-rep-056 |
corr-wf13-032 (I3.1)
Kind: P
Fidelity: exact: point-set over countable types (SC §0.2); the (⇐) model is a thinning of the
trivial model
Scope: countable discrete (SC §0.10)
Hyps: (a) all -/
theorem sameOntology_condModel_iff [Countable Ω] (P P' : PMF Ω) :
    Nonempty (SameOntologyModel P P') ↔ ∃ B, B ≠ ⊤ ∧ BoundedDensity P' P B :=
  ⟨fun ⟨m⟩ => ⟨_, m.toCondModel.inv_mass_ev_ne_top, m.boundedDensity⟩,
    fun ⟨B, hB, h⟩ => ⟨SameOntologyModel.dz P P' B hB h⟩⟩

/-- On a finite carrier, bounded density is just absolute continuity.
Source: none: infrastructure (the finite corollary corr-wf13-032 needs)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem boundedDensity_iff_of_fintype [Fintype Ω] (P P' : PMF Ω) :
    (∃ B, B ≠ ⊤ ∧ BoundedDensity P' P B) ↔ ∀ x, P x = 0 → P' x = 0 := by
  classical
  constructor
  · rintro ⟨B, -, h⟩ x hx
    exact h.absolutelyContinuous x hx
  · intro h
    refine ⟨∑ x, if P x = 0 then 0 else P' x / P x, ENNReal.sum_ne_top.2 fun x _ => ?_,
      fun x => ?_⟩
    · split_ifs with hx
      · exact ENNReal.zero_ne_top
      · exact (ENNReal.div_lt_top (PMF.apply_ne_top _ _) hx).ne
    · by_cases hx : P x = 0
      · rw [h x hx]; exact zero_le
      · have h1 : P' x / P x ≤ ∑ y, if P y = 0 then 0 else P' y / P y := by
          have := Finset.single_le_sum (f := fun y => if P y = 0 then 0 else P' y / P y)
            (fun y _ => zero_le) (Finset.mem_univ x)
          simpa [hx] using this
        calc P' x = P' x / P x * P x := (ENNReal.div_mul_cancel hx (PMF.apply_ne_top _ _)).symm
          _ ≤ (∑ y, if P y = 0 then 0 else P' y / P y) * P x := mul_le_mul' h1 le_rfl

/-- **Finite Diaconis–Zabell** (the corollary corr-wf13-032's I3.1 needs): on a finite carrier a
same-ontology conditioning model exists iff `P′ ≪ P`.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5 | corr-wf13-032 (I3.1)
Kind: C
Fidelity: exact (finite case)
Scope: finite carrier
Hyps: (a) all -/
theorem sameOntology_condModel_iff_of_fintype [Fintype Ω] (P P' : PMF Ω) :
    Nonempty (SameOntologyModel P P') ↔ ∀ x, P x = 0 → P' x = 0 := by
  rw [sameOntology_condModel_iff, boundedDensity_iff_of_fintype]

/-! ### The mixture identity (★_C) -/

/-- **SC (★_C), multiplicative form:** for a compatible model,
`C(y) = C′(y) · μ(ev) + μ(c_L⁻¹{y} ∩ evᶜ)` — `C` is the `μ(ev)`-weighted mixture of `C′` and
the complementary branch (the raw mass; its `condOn` form is `Compatible.C₁_eq_mixture_condOn`).
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.8 (★_C)
Kind: L
Fidelity: exact (multiplicative; SC's `(B−1)/B · C″` is the complementary branch)
Hyps: (a) -/
theorem Compatible.C₁_eq_mixture {m : CondModel P P'} {ci : CommonInfo Ω Ω'}
    (hm : Compatible m ci) (y : ci.C) :
    ci.C₁ P y = ci.C₂ P' y * mass m.μ m.ev + mass m.μ ((ci.c ∘ m.p) ⁻¹' {y} ∩ m.evᶜ) := by
  rw [← m.map_cL ci, map_apply_eq_mass, ← hm.post_map_cL, map_apply_eq_mass, mass_condOn_mul,
    mass_inter_add_mass_inter_compl]

/-- (★_C) with the complementary branch as a conditional measure, when `evᶜ` has positive mass.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.8 (★_C)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem Compatible.C₁_eq_mixture_condOn {m : CondModel P P'} {ci : CommonInfo Ω Ω'}
    (hm : Compatible m ci) (hc : 0 < mass m.μ m.evᶜ) (y : ci.C) :
    ci.C₁ P y = ci.C₂ P' y * mass m.μ m.ev +
      ((condOn m.μ m.evᶜ hc).map (ci.c ∘ m.p)) y * mass m.μ m.evᶜ := by
  rw [hm.C₁_eq_mixture y, map_apply_eq_mass, mass_condOn_mul]

/-- The same-ontology mixture identity: `P x = P′ x · μ(ev) + μ(p⁻¹{x} ∩ evᶜ)` (the
"complementary branch" `corr-reflect-frames` cites).
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.8 (★_C), same ontology
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem SameOntologyModel.mixture [Countable Ω] {P P' : PMF Ω} (m : SameOntologyModel P P')
    (x : Ω) : P x = P' x * mass m.μ m.ev + mass m.μ (m.p ⁻¹' {x} ∩ m.evᶜ) := by
  have := m.toCondModel_compatible.C₁_eq_mixture x
  rwa [idCI_C₁, idCI_C₂] at this

/-! ### T6: trivial common information -/

/-- **Trivial common information** (SC Remark 2.6): for `C = Unit` the right-hand side of
`commonInfo_condModel_iff` holds for every pair, so a compatible model exists — recovering
Thm 1.2.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.6 | udt-rep-056
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem trivialCI_condition (P : PMF Ω) (P' : PMF Ω') :
    (∃ B, B ≠ ⊤ ∧ BoundedDensity ((trivialCI Ω Ω').C₂ P') ((trivialCI Ω Ω').C₁ P) B) ∧
      ∀ y, 0 < (trivialCI Ω Ω').C₁ P y → y ∈ Set.range (trivialCI Ω Ω').c' := by
  obtain ⟨x', -⟩ := P'.support_nonempty
  refine ⟨⟨1, ENNReal.one_ne_top, fun y => ?_⟩, fun y _ => ⟨x', rfl⟩⟩
  rw [CommonInfo.C₁_apply, CommonInfo.C₂_apply, one_mul]
  have h1 : (trivialCI Ω Ω').c ⁻¹' {y} = univ :=
    eq_univ_of_forall fun _ => mem_singleton_iff.2 (@Subsingleton.elim Unit _ () y)
  have h2 : (trivialCI Ω Ω').c' ⁻¹' {y} = univ :=
    eq_univ_of_forall fun _ => mem_singleton_iff.2 (@Subsingleton.elim Unit _ () y)
  rw [h1, h2, mass_univ, mass_univ]

/-- Thm 1.2 recovered from the repaired Thm 2.4 through the trivial common information.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.6 ("We recover Theorem 1.2")
Kind: T
Fidelity: exact
Hyps: (a) -/
theorem trivialCI_condModel_exists [Countable Ω] [Countable Ω'] (P : PMF Ω) (P' : PMF Ω') :
    ∃ m : CondModel P P', Compatible m (trivialCI Ω Ω') :=
  (commonInfo_condModel_iff (trivialCI Ω Ω') P P').2 (trivialCI_condition P P')

end Cleanroom.Udt.UdtSupercondition
