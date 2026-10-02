import Cleanroom.Udt.UdtSupercondition.Anticipation
import Cleanroom.Udt.UdtSupercondition.DZ

/-!
# The landscape of evidence constraints (SC §4.6, §6.2, §8.4, §8.5 Q1/Q5): T12, T19, T20

* `JeffreyOnA P a P′`: `P′` is a Jeffrey update of `P` on the atoms of `a` — a mixture of the
  prior's own conditionals `condKernel P a ā` with weights supported on positive atoms.
* T12 (a) `jeffrey_of_anticipationEvidence` (SC §4.6): anticipation-expressible evidence
  `ev = p⁻¹(a⁻¹ T)` gives a Jeffrey posterior; under calibration the conditionals are the `κ_ā`.
* T12 (b) `jeffrey_of_evidenceCI` (SC §6.2, Candidate B): evidence conditionally independent of
  `p(P̄)` given `p(Ā)` gives a Jeffrey posterior.
* T19 `jeffreyOnA_iff_density_const` (SC §8.5 Q1, the Lean-light half): `P′` is Jeffrey on `a`
  iff `P′ ≪ P` and the density `P′/P` is constant on each atom (multiplicative form), on
  countable `Ω` (no finiteness needed).
* T20 (a) `jeffrey_iff_evidenceCI`: **with a density bound**, Jeffrey-on-`a` posteriors are
  exactly the posteriors of CI-evidence models. The bound is needed (`Witnesses.lean`,
  `jeffrey_not_evidenceCI_witness`): a Jeffrey update whose weights are not dominated by the atom
  masses is not a superconditioning at all.
* T20 (b) `thinningClosed_nonrestrictive`: every thinning-closed constraint on the *model* that
  holds of the trivial model is non-restrictive — its reachable posteriors are the full
  Diaconis–Zabell set. Calibration is thinning-closed (`CMCalibrated.thin`,
  `sameOntology_cmCalibrated_thinningClosed`), which is the structural reason behind Thm 4.5; a
  restrictive semantic constraint must fail thinning-closure, i.e. constrain how the evidence
  sits relative to the anticipation layer (SC's own guess in Q5, now a theorem).

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω : Type} {P P' : PMF Ω}

/-! ### Jeffrey conditioning on the atoms of `a` -/

/-- **Jeffrey conditioning on `Ā`:** `P′ = ∑_ā w_ā · P(· | ā)` for weights `w` summing to one and
supported on positive atoms (where `condKernel P a ā = P(· | ā)`).
Source: [[superconditioning-mismatched-ontologies]] §4.6 ("a Jeffrey conditioning update on
`Ā`") | udt-rep-067
Kind: D
Fidelity: exact (Jeffrey 1965 on the partition of `a`; weights on positive atoms only)
Hyps: n/a -/
def JeffreyOnA (P : PMF Ω) {A : Type} (a : Ω → A) (P' : PMF Ω) : Prop :=
  ∃ w : A → ℝ≥0∞, (∑' ā, w ā = 1) ∧ (∀ ā, w ā ≠ 0 → 0 < mass P (a ⁻¹' {ā})) ∧
    ∀ x, P' x = ∑' ā, w ā * condKernel P a ā x

/-- A mixture of the conditionals with weights on positive atoms, evaluated at `x`, has one
nonzero term: the atom of `x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_mul_condKernel_apply (P : PMF Ω) {A : Type} (a : Ω → A) (w : A → ℝ≥0∞)
    (hw : ∀ ā, w ā ≠ 0 → 0 < mass P (a ⁻¹' {ā})) (x : Ω) :
    ∑' ā, w ā * condKernel P a ā x = w (a x) * condKernel P a (a x) x := by
  rw [tsum_eq_single (a x)]
  intro ā hā
  by_cases hw0 : w ā = 0
  · rw [hw0, zero_mul]
  · rw [condKernel_of_pos P a ā (hw ā hw0),
      condOn_apply_of_notMem P (hw ā hw0) (fun h => hā (mem_singleton_iff.1 h).symm), mul_zero]

/-- The multiplicative identity `w_ā · P(x | ā) · P(ā) = w_ā · 𝟙[a x = ā] · P x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mul_condKernel_mul_mass (P : PMF Ω) {A : Type} (a : Ω → A) (c : ℝ≥0∞) (ā : A) (x : Ω) :
    c * condKernel P a ā x * mass P (a ⁻¹' {ā}) = c * (a ⁻¹' {ā}).indicator P x := by
  rw [mul_assoc, condKernel_apply_mul]

/-- If the density `P′/P` is constant on the atom of `x`, then
`P′(ā) · P x = P′ x · P(ā)` for that atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_atom_mul_of_density_const (P P' : PMF Ω) {A : Type} (a : Ω → A)
    (hconst : ∀ x y, a x = a y → P' x * P y = P' y * P x) (x : Ω) :
    mass P' (a ⁻¹' {a x}) * P x = P' x * mass P (a ⁻¹' {a x}) := by
  rw [mass_eq_tsum, mass_eq_tsum, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ a ⁻¹' {a x}
  · rw [indicator_of_mem hy, indicator_of_mem hy, hconst y x (mem_singleton_iff.1 hy)]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul, mul_zero]

/-- Under calibration, the conditional kernel on a positive atom is `κ_ā`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Def 3.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem AnticipationStructure.Calibrated.condKernel_eq {as : AnticipationStructure P Ω}
    (h : as.Calibrated) (ā : as.A) (hā : 0 < mass P (as.a ⁻¹' {ā})) :
    condKernel P as.a ā = as.κ ā := by
  rw [condKernel_of_pos P as.a ā hā]; exact h.condOn_eq ā hā

/-- Under calibration, a Jeffrey update on `Ā` is a mixture of the intended kernels `κ_ā`
(SC §4.6: "a restricted mixture of the `κ_ā`").
Source: [[superconditioning-mismatched-ontologies]] §4.6
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem JeffreyOnA.eq_tsum_kappa {as : AnticipationStructure P Ω} (hc : as.Calibrated)
    (hJ : JeffreyOnA P as.a P') :
    ∃ w : as.A → ℝ≥0∞, (∑' ā, w ā = 1) ∧ (∀ ā, w ā ≠ 0 → 0 < mass P (as.a ⁻¹' {ā})) ∧
      ∀ x, P' x = ∑' ā, w ā * as.κ ā x := by
  obtain ⟨w, h1, h2, h3⟩ := hJ
  refine ⟨w, h1, h2, fun x => ?_⟩
  rw [h3 x]
  refine tsum_congr fun ā => ?_
  by_cases hw : w ā = 0
  · rw [hw, zero_mul, zero_mul]
  · rw [hc.condKernel_eq ā (h2 ā hw)]

/-! ### T12 (a): anticipation-expressible evidence gives Jeffrey -/

/-- Conditioning `P` on a union of atoms `a⁻¹ T` is Jeffrey on `a` with weights
`P(ā)/P(a⁻¹ T)` on `T`.
Source: [[superconditioning-mismatched-ontologies]] §4.6 (the displayed posterior)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem jeffreyOnA_condOn_preimage (P : PMF Ω) {A : Type} (a : Ω → A) (T : Set A)
    (h : 0 < mass P (a ⁻¹' T)) : JeffreyOnA P a (condOn P (a ⁻¹' T) h) := by
  have hsupp : ∀ ā, T.indicator (fun ā => mass P (a ⁻¹' {ā})) ā * (mass P (a ⁻¹' T))⁻¹ ≠ 0 →
      0 < mass P (a ⁻¹' {ā}) := fun ā hā => by
    by_contra hm
    apply hā
    have h0 : mass P (a ⁻¹' {ā}) = 0 := le_antisymm (not_lt.1 hm) zero_le
    by_cases hT : ā ∈ T
    · rw [indicator_of_mem hT, h0, zero_mul]
    · rw [indicator_of_notMem hT, zero_mul]
  refine ⟨fun ā => T.indicator (fun ā => mass P (a ⁻¹' {ā})) ā * (mass P (a ⁻¹' T))⁻¹, ?_, hsupp,
    fun x => ?_⟩
  · beta_reduce
    rw [ENNReal.tsum_mul_right, ← mass_preimage_eq_tsum,
      ENNReal.mul_inv_cancel h.ne' (mass_ne_top _ _)]
  · beta_reduce
    rw [tsum_mul_condKernel_apply P a _ hsupp, condOn_apply]
    by_cases hT : a x ∈ T
    · rw [indicator_of_mem hT, indicator_of_mem (show x ∈ a ⁻¹' T from hT)]
      by_cases hm : 0 < mass P (a ⁻¹' {a x})
      · rw [condKernel_of_pos P a _ hm, condOn_apply_of_mem P hm rfl]
        calc P x * (mass P (a ⁻¹' T))⁻¹
            = P x * (mass P (a ⁻¹' T))⁻¹ * (mass P (a ⁻¹' {a x}) * (mass P (a ⁻¹' {a x}))⁻¹) := by
              rw [ENNReal.mul_inv_cancel hm.ne' (mass_ne_top _ _), mul_one]
          _ = mass P (a ⁻¹' {a x}) * (mass P (a ⁻¹' T))⁻¹ * (P x * (mass P (a ⁻¹' {a x}))⁻¹) := by
              ring
      · have h0 : mass P (a ⁻¹' {a x}) = 0 := le_antisymm (not_lt.1 hm) zero_le
        have hx : P x = 0 :=
          le_antisymm ((apply_le_mass P (show x ∈ a ⁻¹' {a x} from rfl)).trans h0.le) zero_le
        simp only [h0, hx, zero_mul]
    · rw [indicator_of_notMem hT, indicator_of_notMem (show x ∉ a ⁻¹' T from hT), zero_mul,
        zero_mul]

/-- **SC §4.6 — `Ā`-compatible evidence gives Jeffrey conditioning on `Ā`:** if a same-ontology
model's evidence is `p⁻¹(a⁻¹ T)` (expressible in terms of the anticipation), its posterior is
a Jeffrey update of `P` on the atoms of `a`, with weights `P(ā)/P(a⁻¹ T)` on `T`. Under
calibration the conditionals are the `κ_ā` (`JeffreyOnA.eq_tsum_kappa`).
Source: [[superconditioning-mismatched-ontologies]] §4.6 | udt-rep-067
Kind: P
Fidelity: exact: point-set over countable types (SC §0.2)
Scope: same ontology
Hyps: (a) all -/
theorem jeffrey_of_anticipationEvidence (m : SameOntologyModel P P') {A : Type} (a : Ω → A)
    (T : Set A) (hev : m.ev = m.p ⁻¹' (a ⁻¹' T)) : JeffreyOnA P a P' := by
  have hT : 0 < mass P (a ⁻¹' T) := by
    have := m.hev
    rwa [hev, ← mass_map, m.hp] at this
  have key : ∀ (ev : Set m.L) (hev' : 0 < mass m.μ ev), ev = m.p ⁻¹' (a ⁻¹' T) →
      (condOn m.μ ev hev').map m.p = condOn P (a ⁻¹' T) hT := by
    intro ev hev' e
    subst e
    have h2 : 0 < mass (m.μ.map m.p) (a ⁻¹' T) := by rw [mass_map]; exact hev'
    rw [condOn_map_preimage m.μ m.p (a ⁻¹' T) hev' h2]
    have key2 : ∀ (Q : PMF Ω) (hQ : 0 < mass Q (a ⁻¹' T)), Q = P →
        condOn Q (a ⁻¹' T) hQ = condOn P (a ⁻¹' T) hT := by
      intro Q hQ hQP
      subst hQP
      rfl
    exact key2 _ h2 m.hp
  have hP' : P' = condOn P (a ⁻¹' T) hT := by
    rw [← m.hp']
    exact key m.ev m.hev hev
  rw [hP']
  exact jeffreyOnA_condOn_preimage P a T hT

/-! ### T12 (b): conditionally independent evidence gives Jeffrey -/

/-- **Evidence conditionally independent of `p(P̄)` given `p(Ā)`** (SC §6.2, Candidate B), in
multiplicative form: for `x` in atom `ā`,
`μ(ev ∩ p⁻¹{x}) · μ(p⁻¹ ā) = μ(ev ∩ p⁻¹ ā) · μ(p⁻¹{x})`.
Source: [[superconditioning-mismatched-ontologies]] §6.2 ("`l̄ ⊥ p(P̄) | p(Ā)`") | udt-rep-067
Kind: D
Fidelity: exact (multiplicative form of the conditional independence on each atom)
Hyps: n/a -/
def EvidenceCI (m : SameOntologyModel P P') {A : Type} (a : Ω → A) : Prop :=
  ∀ ā x, a x = ā →
    mass m.μ (m.ev ∩ m.p ⁻¹' {x}) * mass m.μ (m.p ⁻¹' (a ⁻¹' {ā})) =
      mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {ā})) * mass m.μ (m.p ⁻¹' {x})

/-- Fibre masses of `p` under `μ` are the prior's masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SameOntologyModel.mass_preimage (m : SameOntologyModel P P') (S : Set Ω) :
    mass m.μ (m.p ⁻¹' S) = mass P S := by
  rw [← mass_map, m.hp]

/-- The posterior of a same-ontology model at `x`, as a mass ratio.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SameOntologyModel.post_apply (m : SameOntologyModel P P') (x : Ω) :
    P' x = mass m.μ (m.ev ∩ m.p ⁻¹' {x}) * (mass m.μ m.ev)⁻¹ := by
  have e : P' x = ((condOn m.μ m.ev m.hev).map m.p) x := by rw [m.hp']
  rw [e, map_apply_eq_mass, mass_condOn, inter_comm]

/-- **SC §6.2 — CI evidence gives Jeffrey conditioning on `Ā`:** if the evidence is conditionally
independent of `p(P̄)` given `p(Ā)`, the posterior is a Jeffrey update on the atoms of `a`, with
weights `μ(ev ∩ p⁻¹ ā)/μ(ev)`.
Source: [[superconditioning-mismatched-ontologies]] §6.2, §8.4 | udt-rep-067
Kind: P
Fidelity: exact: point-set over countable types (SC §0.2)
Scope: same ontology
Hyps: (a) all -/
theorem jeffrey_of_evidenceCI (m : SameOntologyModel P P') {A : Type} (a : Ω → A)
    (h : EvidenceCI m a) : JeffreyOnA P a P' := by
  have hsupp : ∀ ā, mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {ā})) * (mass m.μ m.ev)⁻¹ ≠ 0 →
      0 < mass P (a ⁻¹' {ā}) := fun ā hā => by
    rw [← m.mass_preimage]
    have h1 : mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {ā})) ≠ 0 := fun h0 => hā (by rw [h0, zero_mul])
    exact lt_of_lt_of_le (pos_iff_ne_zero.2 h1) (mass_mono _ inter_subset_right)
  refine ⟨fun ā => mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {ā})) * (mass m.μ m.ev)⁻¹, ?_, hsupp,
    fun x => ?_⟩
  · beta_reduce
    rw [ENNReal.tsum_mul_right]
    have e : ∀ ā, mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {ā})) = mass m.μ (m.ev ∩ (a ∘ m.p) ⁻¹' {ā}) :=
      fun ā => rfl
    rw [tsum_congr e, ← mass_eq_tsum_fiber m.μ m.ev (a ∘ m.p),
      ENNReal.mul_inv_cancel m.hev.ne' (mass_ne_top _ _)]
  · beta_reduce
    rw [tsum_mul_condKernel_apply P a _ hsupp, m.post_apply x]
    have hci := h (a x) x rfl
    simp only [m.mass_preimage, mass_singleton] at hci
    by_cases hm : 0 < mass P (a ⁻¹' {a x})
    · rw [condKernel_of_pos P a _ hm, condOn_apply_of_mem P hm rfl]
      calc mass m.μ (m.ev ∩ m.p ⁻¹' {x}) * (mass m.μ m.ev)⁻¹
          = mass m.μ (m.ev ∩ m.p ⁻¹' {x}) * mass P (a ⁻¹' {a x}) * (mass P (a ⁻¹' {a x}))⁻¹ *
            (mass m.μ m.ev)⁻¹ := by
              rw [mul_assoc _ (mass P _), ENNReal.mul_inv_cancel hm.ne' (mass_ne_top _ _), mul_one]
        _ = mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {a x})) * P x * (mass P (a ⁻¹' {a x}))⁻¹ *
            (mass m.μ m.ev)⁻¹ := by rw [hci]
        _ = mass m.μ (m.ev ∩ m.p ⁻¹' (a ⁻¹' {a x})) * (mass m.μ m.ev)⁻¹ *
            (P x * (mass P (a ⁻¹' {a x}))⁻¹) := by ring
    · have h0 : mass P (a ⁻¹' {a x}) = 0 := le_antisymm (not_lt.1 hm) zero_le
      have hx : P x = 0 :=
        le_antisymm ((apply_le_mass P (show x ∈ a ⁻¹' {a x} from rfl)).trans h0.le) zero_le
      have hx' : mass m.μ (m.ev ∩ m.p ⁻¹' {x}) = 0 := by
        refine le_antisymm ?_ zero_le
        calc mass m.μ (m.ev ∩ m.p ⁻¹' {x}) ≤ mass m.μ (m.p ⁻¹' {x}) :=
              mass_mono _ inter_subset_right
          _ = 0 := by rw [m.mass_preimage, mass_singleton, hx]
      rw [hx', zero_mul, condKernel, dif_neg hm, hx, mul_zero]

/-! ### T19: Jeffrey on `Ā` iff the density is constant on atoms -/

/-- **Quantifying refinement, Lean-light half (SC §8.5 Q1):** `P′` is a Jeffrey update of `P`
on the atoms of `a` iff `P′ ≪ P` and the density `P′/P` is constant on each atom, in the
multiplicative form `P′ x · P y = P′ y · P x` for `a x = a y`. Countable `Ω`; no finiteness.
Source: [[superconditioning-mismatched-ontologies]] §8.5 item 1 | udt-rep-065
Kind: P
Fidelity: stronger: countable carrier (the mandate asked for `Fintype Ω`); multiplicative form
Scope: same ontology
Hyps: (a) all -/
theorem jeffreyOnA_iff_density_const (P P' : PMF Ω) {A : Type} (a : Ω → A) :
    JeffreyOnA P a P' ↔
      (∀ x, P x = 0 → P' x = 0) ∧ ∀ x y, a x = a y → P' x * P y = P' y * P x := by
  constructor
  · rintro ⟨w, -, hw, hP'⟩
    have key : ∀ x, P' x * mass P (a ⁻¹' {a x}) = w (a x) * P x := fun x => by
      rw [hP' x, tsum_mul_condKernel_apply P a w hw, mul_condKernel_mul_mass,
        indicator_of_mem (show x ∈ a ⁻¹' {a x} from rfl)]
    constructor
    · intro x hx
      by_cases hm : 0 < mass P (a ⁻¹' {a x})
      · have := key x
        rw [hx, mul_zero] at this
        exact (mul_eq_zero.1 this).resolve_right hm.ne'
      · have h0 : mass P (a ⁻¹' {a x}) = 0 := le_antisymm (not_lt.1 hm) zero_le
        rw [hP' x, tsum_mul_condKernel_apply P a w hw]
        by_cases hw0 : w (a x) = 0
        · rw [hw0, zero_mul]
        · exact absurd h0 (hw _ hw0).ne'
    · intro x y hxy
      have kx := key x
      have ky := key y
      rw [hxy] at kx
      by_cases hm : 0 < mass P (a ⁻¹' {a y})
      · have hne := hm.ne'
        have ht := mass_ne_top P (a ⁻¹' {a y})
        calc P' x * P y = P' x * mass P (a ⁻¹' {a y}) * (mass P (a ⁻¹' {a y}))⁻¹ * P y := by
              rw [mul_assoc _ (mass P _), ENNReal.mul_inv_cancel hne ht, mul_one]
          _ = w (a y) * P x * (mass P (a ⁻¹' {a y}))⁻¹ * P y := by rw [kx]
          _ = (w (a y) * P y) * (mass P (a ⁻¹' {a y}))⁻¹ * P x := by ring
          _ = P' y * mass P (a ⁻¹' {a y}) * (mass P (a ⁻¹' {a y}))⁻¹ * P x := by rw [ky]
          _ = P' y * P x := by
              rw [mul_assoc _ (mass P _), ENNReal.mul_inv_cancel hne ht, mul_one]
      · have h0 : mass P (a ⁻¹' {a y}) = 0 := le_antisymm (not_lt.1 hm) zero_le
        have hy : P y = 0 :=
          le_antisymm ((apply_le_mass P (show y ∈ a ⁻¹' {a y} from rfl)).trans h0.le) zero_le
        have hx : P x = 0 := le_antisymm ((apply_le_mass P (show x ∈ a ⁻¹' {a y} from hxy)).trans
          h0.le) zero_le
        rw [hx, hy, mul_zero, mul_zero]
  · rintro ⟨hac, hconst⟩
    refine ⟨fun ā => mass P' (a ⁻¹' {ā}), tsum_mass_fiber P' a, fun ā hā => ?_, fun x => ?_⟩
    · rw [mass_pos_iff]
      obtain ⟨y, hy, hpos⟩ := (mass_pos_iff P' _).1 (pos_iff_ne_zero.2 hā)
      exact ⟨y, hy, pos_iff_ne_zero.2 fun h0 => hpos.ne' (hac y h0)⟩
    · beta_reduce
      rw [tsum_mul_condKernel_apply P a _ (fun ā hā => by
        rw [mass_pos_iff]
        obtain ⟨y, hy, hpos⟩ := (mass_pos_iff P' _).1 (pos_iff_ne_zero.2 hā)
        exact ⟨y, hy, pos_iff_ne_zero.2 fun h0 => hpos.ne' (hac y h0)⟩)]
      have hsum := mass_atom_mul_of_density_const P P' a hconst x
      by_cases hm : 0 < mass P (a ⁻¹' {a x})
      · rw [condKernel_of_pos P a _ hm, condOn_apply_of_mem P hm rfl, ← mul_assoc, hsum, mul_assoc,
          ENNReal.mul_inv_cancel hm.ne' (mass_ne_top _ _), mul_one]
      · have h0 : mass P (a ⁻¹' {a x}) = 0 := le_antisymm (not_lt.1 hm) zero_le
        have hx : P x = 0 :=
          le_antisymm ((apply_le_mass P (show x ∈ a ⁻¹' {a x} from rfl)).trans h0.le) zero_le
        rw [condKernel, dif_neg hm, hx, mul_zero, hac x hx]

/-! ### T20 (b): thinning-closed model constraints are non-restrictive -/

/-- A predicate `Φ` on same-ontology models of `P` is **thinning-closed** if it survives every
thinning (any weight `w ≤ 1` on `L` with positive thinned evidence), with the thinned posterior
read off the model. This is the *strong* form: closure under every `w : L → ℝ≥0∞`, not only
weights factoring through `(p, p′)` as SC Remark 4.6's mechanism needs; it makes
`thinningClosed_nonrestrictive` apply to fewer `Φ`, at no loss — calibration satisfies the
strong form (`sameOntology_cmCalibrated_thinningClosed`).
Source: mandate T20 (b); [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6, §8.5 Q5
Kind: D
Fidelity: n/a (a new notion, the formal shape of SC's "constraint on the model, not the
evidence")
Hyps: n/a -/
def ThinningClosed (P : PMF Ω) (Φ : ∀ P' : PMF Ω, SameOntologyModel P P' → Prop) : Prop :=
  ∀ (P' : PMF Ω) (m : SameOntologyModel P P'), Φ P' m →
    ∀ (w : m.L → ℝ≥0∞) (hw : ∀ l, w l ≤ 1) (hpos : 0 < ∑' l, m.ev.indicator (fun l => w l * m.μ l) l)
      (P'' : PMF Ω) (hP'' : ∀ x, P'' x = thinPostFun m.μ w m.ev m.p x),
      Φ P'' (m.thin w hw hpos P'' hP'')

/-- **Every thinning-closed model constraint holding of the trivial model is non-restrictive**
(the structural answer to SC's Q5): if `Φ` is thinning-closed and holds of the trivial model, the
posteriors reachable under `Φ` are exactly the Diaconis–Zabell set. Hence a constraint that
restricts posteriors must take one of two exits: fail thinning-closure (constrain how the
evidence sits relative to the model, not the model alone) or fail on the trivial model (the
canonical-`L̄` constraint of T13 takes both). The proof composes T5 necessity with "`dz` is a
thinning of `trivial`".
Source: [[superconditioning-mismatched-ontologies]] §8.5 item 5, §4.4 Remark 4.6 | udt-rep-067
Kind: C
Fidelity: n/a (new theorem; SC states the guess in prose)
Scope: same ontology; countable discrete
Hyps: (a) all -/
theorem thinningClosed_nonrestrictive [Countable Ω] (P : PMF Ω)
    (Φ : ∀ P' : PMF Ω, SameOntologyModel P P' → Prop) (hΦ : ThinningClosed P Φ)
    (h0 : Φ P (SameOntologyModel.trivial P)) (P' : PMF Ω) :
    (∃ m : SameOntologyModel P P', Φ P' m) ↔ ∃ B, B ≠ ⊤ ∧ BoundedDensity P' P B := by
  constructor
  · rintro ⟨m, -⟩
    exact (sameOntology_condModel_iff P P').1 ⟨m⟩
  · rintro ⟨B, hB, h⟩
    exact ⟨SameOntologyModel.dz P P' B hB h, hΦ P (SameOntologyModel.trivial P) h0 _ _ _ P' _⟩

/-- The thinned same-ontology model, viewed as a conditioning model, has the joint law of the
original.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SameOntologyModel.jointLaw_thin_toCondModel (m : SameOntologyModel P P') (w : m.L → ℝ≥0∞)
    (hw : ∀ l, w l ≤ 1) (hpos : 0 < ∑' l, m.ev.indicator (fun l => w l * m.μ l) l) (P'' : PMF Ω)
    (hP'' : ∀ x, P'' x = thinPostFun m.μ w m.ev m.p x) :
    (m.thin w hw hpos P'' hP'').toCondModel.jointLaw = m.toCondModel.jointLaw := by
  show (Cleanroom.Udt.UdtSupercondition.thin m.μ w hw).map
    ((fun l => (m.p l, m.p l)) ∘ Prod.fst) = _
  rw [← PMF.map_comp, thin_map_fst]; rfl

/-- **Calibration is a thinning-closed model constraint** (SC Remark 4.6, made precise): the
predicate "calibrated w.r.t. `as`" on same-ontology models is thinning-closed. With
`thinningClosed_nonrestrictive` this re-derives the same-ontology content of Thm 4.5 from the
closure property alone *for calibrated `as`*: the trivial-model hypothesis `h0` is
`CMCalibrated (trivial P) as`, which for `p′ = p = id` is `as.Calibrated` — and then `Q₀ = P`
and the D–Z set relative to `Q₀` is the one relative to `P`. For a non-calibrated `as` Thm 4.5 is
`calModel`'s, not a corollary of closure.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6 | mandate T20
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem sameOntology_cmCalibrated_thinningClosed (P : PMF Ω) (as : AnticipationStructure P Ω) :
    ThinningClosed P fun _ m => CMCalibrated m.toCondModel as := by
  intro P' m hm w hw hpos P'' hP''
  rw [cmCalibrated_iff_jointCalibrated, SameOntologyModel.jointLaw_thin_toCondModel]
  exact (cmCalibrated_iff_jointCalibrated _ as).1 hm

/-! ### T20 (a): Jeffrey posteriors are the CI-evidence posteriors, given a density bound -/

/-- The steering weight of the trivial model times `P` is `P′ / B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerWeight_id_mul (P P' : PMF Ω) {B : ℝ≥0∞} (hB : B ≠ ⊤) (h : BoundedDensity P' P B)
    (y : Ω) : steerWeight P id P' B y * P y = P' y * B⁻¹ := by
  have := steerWeight_fiber_sum P id P' B hB (by rw [PMF.map_id]; exact h) y
  rw [tsum_eq_single y] at this
  · rwa [indicator_of_mem (show y ∈ id ⁻¹' {y} from rfl)] at this
  · intro z hz
    exact indicator_of_notMem (s := id ⁻¹' {y}) (a := z) hz _

/-- The Diaconis–Zabell model of a Jeffrey-on-`a` posterior has CI evidence: the steering weight
`P′ x / (B · P x)` is constant on positive atoms exactly when `P′` is Jeffrey on `a`.
Source: mandate T20 (a) ("thinning with `w x = w_{a x} / (B · P(a x))`")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem evidenceCI_dz_of_jeffrey [Countable Ω] (P P' : PMF Ω) {A : Type} (a : Ω → A)
    (hJ : JeffreyOnA P a P') {B : ℝ≥0∞} (hB : B ≠ ⊤) (h : BoundedDensity P' P B) :
    EvidenceCI (SameOntologyModel.dz P P' B hB h) a := by
  intro ā x hx
  subst hx
  have hconst := ((jeffreyOnA_iff_density_const P P' a).1 hJ).2
  have e1 : ∀ S : Set Ω, mass (SameOntologyModel.dz P P' B hB h).μ
      ((SameOntologyModel.dz P P' B hB h).ev ∩ (SameOntologyModel.dz P P' B hB h).p ⁻¹' S) =
      ∑' y, S.indicator (fun y => P' y * B⁻¹) y := fun S => by
    show mass (Cleanroom.Udt.UdtSupercondition.thin P (steerWeight P id P' B)
      (steerWeight_id_le_one P P' B h)) (thinEv univ ∩ (id ∘ Prod.fst) ⁻¹' S) = _
    rw [inter_comm, preimage_inter_thinEv, mass_thin_inter_evTrue, inter_univ, preimage_id]
    simp only [steerWeight_id_mul P P' hB h]
  have e2 : ∀ S : Set Ω, mass (SameOntologyModel.dz P P' B hB h).μ
      ((SameOntologyModel.dz P P' B hB h).p ⁻¹' S) = mass P S := fun S => by
    show mass (Cleanroom.Udt.UdtSupercondition.thin P (steerWeight P id P' B)
      (steerWeight_id_le_one P P' B h)) ((id ∘ Prod.fst) ⁻¹' S) = _
    rw [preimage_comp, preimage_id]
    exact mass_thin_fst _ _ _ S
  rw [e1, e1, e2, e2, mass_singleton, tsum_eq_single x, indicator_of_mem (mem_singleton x)]
  · have e3 : (∑' y, (a ⁻¹' {a x}).indicator (fun y => P' y * B⁻¹) y) =
        mass P' (a ⁻¹' {a x}) * B⁻¹ := by
      rw [mass_eq_tsum, ← ENNReal.tsum_mul_right]
      exact tsum_congr fun y => indicator_mul_const _ _ _ _
    rw [e3]
    calc P' x * B⁻¹ * mass P (a ⁻¹' {a x}) = P' x * mass P (a ⁻¹' {a x}) * B⁻¹ := by ring
      _ = mass P' (a ⁻¹' {a x}) * P x * B⁻¹ := by
          rw [mass_atom_mul_of_density_const P P' a hconst x]
      _ = mass P' (a ⁻¹' {a x}) * B⁻¹ * P x := by ring
  · intro y hy
    exact indicator_of_notMem (s := {x}) (a := y) hy _

/-- **T20 (a) — Jeffrey posteriors are the CI-evidence posteriors, given a density bound:** `P′`
is Jeffrey on `a` *and* has bounded density w.r.t. `P` iff some same-ontology model with
CI evidence has posterior `P′`. SC (§6.2) states only (⇐); the bound is needed for (⇒)
(`pairJeffrey_not_evidenceCI_witness` in `WitnessCountable.lean`, N+ on the pair partition; the
finest-partition instance `jeffrey_not_evidenceCI_witness` is N−).
Source: [[superconditioning-mismatched-ontologies]] §6.2, §8.4 | udt-rep-067 | mandate T20 (a)
Kind: C
Fidelity: variant: adds the density bound to the Jeffrey side, which SC's prose omits and which
is necessary
Scope: same ontology; countable discrete
Hyps: (a) all -/
theorem jeffrey_iff_evidenceCI [Countable Ω] (P P' : PMF Ω) {A : Type} (a : Ω → A) :
    (JeffreyOnA P a P' ∧ ∃ B, B ≠ ⊤ ∧ BoundedDensity P' P B) ↔
      ∃ m : SameOntologyModel P P', EvidenceCI m a :=
  ⟨fun ⟨hJ, _, hB, h⟩ => ⟨_, evidenceCI_dz_of_jeffrey P P' a hJ hB h⟩,
    fun ⟨m, hm⟩ => ⟨jeffrey_of_evidenceCI m a hm, _, m.toCondModel.inv_mass_ev_ne_top,
      m.boundedDensity⟩⟩

end Cleanroom.Udt.UdtSupercondition
