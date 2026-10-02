import Cleanroom.Info.InfoVoiLatents.Split
import Cleanroom.Info.InfoVoiLatents.Bridge
import Cleanroom.Info.InfoVoiLatents.Eig

/-!
# info-voi-latents — H_val's information form on the joint measure (Target 4(iv); repair round 2)

The mandate's Target 4(iv) asks for the kernel identity `HVal` *and* the implication to S3(c)'s
information form `I[θ : S | Λ] = 0`, "prove that implication too". Repair round 1 left it as
"not done"; audit r2 (fidelity item 5(c)) asked for at least a precise statement. This file proves
it, by the route the report named: on the joint measure `Bridge.joint μ k hμ` of `(μ, k)` on
`(Λ × θ) × S`, with the named projections `thetaOf`, `sigOf`, `lamOf` (findings F11), the
three-variable cells are `P(λ, ϑ, s) = μ(λ, ϑ) · k((λ, ϑ), s)` (`pm3_joint`), the pair and single
cells are the marginals (`pm2_theta_lam_joint`, `pm2_sig_lam_joint`, `pm1_lam_joint`), and under
`HVal` the joint law *equals* the factorised law `P[Λ]·P[θ | Λ]·P[S | Λ]` cell by cell
(`joint3_eq_fact3_of_hval`), so `Eig.klFin_joint3_fact3_eq_condMutualInfo` gives
**`condMutualInfo_theta_signal_eq_zero_of_hval`**: `I[θ : S | Λ ; joint μ k] = 0`, and FAF's
`condMutualInfo_eq_zero` gives the `CondIndepFun` form (`condIndepFun_theta_signal_of_hval`).

The converse (`I[θ : S | Λ] = 0 → HVal k`) is **false**: `HVal` also constrains null-mass
coordinates (`SplitComposed.nullθ_not_hval`, `nullθ_voi_eq_voiΛ`), which is why `HVal`'s Fidelity
is `stronger`. Mandate: Target 4(iv).
-/

namespace Cleanroom.Info.InfoVoiLatents.Split

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents.Voi Cleanroom.Info.InfoVoiLatents.Eig
open MeasureTheory ProbabilityTheory

noncomputable section

set_option linter.unusedSectionVars false

variable {S Λ Θ : Type} [Fintype S] [Fintype Λ] [Fintype Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace Λ] [MeasurableSingletonClass Λ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

/-! ### Named projections on `(Λ × θ) × S` -/

/-- The `θ`-coordinate of a point of the joint carrier `(Λ × θ) × S` (a named projection, so that
instance search is not stuck — findings F11).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def thetaOf : (Λ × Θ) × S → Θ := fun p => p.1.2

/-- The signal coordinate of a point of the joint carrier.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def sigOf : (Λ × Θ) × S → S := fun p => p.2

/-- The `Λ`-coordinate of a point of the joint carrier.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def lamOf : (Λ × Θ) × S → Λ := fun p => p.1.1

/-- `measurable_thetaOf`: the projections are measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_thetaOf : Measurable (thetaOf : (Λ × Θ) × S → Θ) := measurable_fst.snd

/-- `measurable_sigOf`: the projections are measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_sigOf : Measurable (sigOf : (Λ × Θ) × S → S) := measurable_snd

/-- `measurable_lamOf`: the projections are measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_lamOf : Measurable (lamOf : (Λ × Θ) × S → Λ) := measurable_fst.fst

/-- The three-variable cell `{θ = ϑ} ∩ {S = s} ∩ {Λ = λ}` is the singleton `{((λ, ϑ), s)}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem preimage_triple_eq (ϑ : Θ) (s : S) (l : Λ) :
    ((thetaOf : (Λ × Θ) × S → Θ) ⁻¹' {ϑ} ∩ (sigOf : (Λ × Θ) × S → S) ⁻¹' {s}
      ∩ (lamOf : (Λ × Θ) × S → Λ) ⁻¹' {l}) = {((l, ϑ), s)} := by
  ext ⟨⟨l', ϑ'⟩, s'⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, thetaOf, sigOf, lamOf,
    Prod.mk.injEq]
  tauto

/-! ### The cells of the joint measure -/

variable {μ : Λ × Θ → ℝ} (hμ : μ ∈ stdSimplex ℝ (Λ × Θ)) {k : Experiment (Λ × Θ) S}

/-- `P(λ, ϑ, s) = μ(λ, ϑ) · k((λ, ϑ), s)` on the joint measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm3_joint (ϑ : Θ) (s : S) (l : Λ) :
    pm3 (Bridge.joint μ k hμ) thetaOf sigOf lamOf ϑ s l = μ (l, ϑ) * k.k (l, ϑ) s := by
  unfold pm3
  rw [preimage_triple_eq, Bridge.joint_real_singleton]

/-- `P(ϑ, λ) = μ(λ, ϑ)`: the `(θ, Λ)`-marginal of the joint measure is the prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_theta_lam_joint (ϑ : Θ) (l : Λ) :
    pm2 (Bridge.joint μ k hμ) thetaOf lamOf ϑ l = μ (l, ϑ) := by
  rw [← sum_pm3_y (X := (thetaOf : (Λ × Θ) × S → Θ)) (Z := (lamOf : (Λ × Θ) × S → Λ))
    measurable_sigOf ϑ l]
  simp_rw [pm3_joint hμ]
  rw [← Finset.mul_sum, (k.k_mem (l, ϑ)).2, mul_one]

/-- Under `HVal`, `P(s, λ) = μ_Λ(λ) · k((λ, ϑ), s)` for any reference `ϑ`: the `(S, Λ)`-marginal
factors through the Λ-marginal kernel.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_sig_lam_joint (hk : HVal k) (s : S) (l : Λ) (ϑ : Θ) :
    pm2 (Bridge.joint μ k hμ) sigOf lamOf s l = muΛ μ l * k.k (l, ϑ) s := by
  rw [← sum_pm3_x (Y := (sigOf : (Λ × Θ) × S → S)) (Z := (lamOf : (Λ × Θ) × S → Λ))
    measurable_thetaOf s l]
  simp_rw [pm3_joint hμ]
  unfold muΛ
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ϑ' _ => by rw [hk l ϑ' ϑ s]

/-- `P(λ) = μ_Λ(λ)`: the `Λ`-marginal of the joint measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm1_lam_joint (l : Λ) : pm1 (Bridge.joint μ k hμ) lamOf l = muΛ μ l := by
  rw [← sum_pm2_x (X := (thetaOf : (Λ × Θ) × S → Θ)) (Y := (lamOf : (Λ × Θ) × S → Λ))
    measurable_thetaOf l]
  simp_rw [pm2_theta_lam_joint hμ]
  rfl

/-- **Under `HVal` the joint law equals the factorised law** `P[Λ]·P[θ | Λ]·P[S | Λ]` cell by
cell: `μ(λ, ϑ) · k((λ, ϑ), s) = μ(λ, ϑ) · (μ_Λ(λ) · k((λ, ϑ), s)) / μ_Λ(λ)` (both `0` at a null `λ`).
Source: [[generalization-final]] S3(c) l. 68
Kind: P
Fidelity: exact -/
theorem joint3_eq_fact3_of_hval (hk : HVal k) :
    joint3 (Bridge.joint μ k hμ) thetaOf sigOf lamOf
      = fact3 (Bridge.joint μ k hμ) thetaOf sigOf lamOf := by
  funext ⟨ϑ, s, l⟩
  simp only [joint3, fact3]
  rw [pm3_joint hμ, pm2_theta_lam_joint hμ, pm2_sig_lam_joint hμ hk s l ϑ, pm1_lam_joint hμ]
  by_cases h : muΛ μ l = 0
  · have h0 : μ (l, ϑ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun ϑ' _ => hμ.1 (l, ϑ')).1 h ϑ (Finset.mem_univ ϑ)
    rw [h, h0]
    simp
  · rw [mul_div_assoc, mul_div_cancel_left₀ _ h]

/-- `klFin p p = 0` (each coordinate is `p · log 1` or `0 · log _`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem klFin_self {W : Type} [Fintype W] (p : W → ℝ) : klFin p p = 0 := by
  unfold klFin
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases h : p w = 0
  · rw [h, zero_mul]
  · rw [div_self h, Real.log_one, mul_zero]

/-! ### The information form -/

/-- **H_val's information form** (Target 4(iv), the implication the mandate asks for): under the
kernel identity `HVal k`, `I[θ : S | Λ] = 0` over PFR's `condMutualInfo` on the joint measure of
`(μ, k)`. Route: `Eig.klFin_joint3_fact3_eq_condMutualInfo` renders `I[θ : S | Λ]` as the finite KL
of the joint cells against the factorised cells, and under `HVal` the two laws coincide
(`joint3_eq_fact3_of_hval`), so the KL is `0`.
Source: [[generalization-final]] S3(c) l. 68 (`I(θ_{A>t}; E_a | Λ_{A>t}) = 0`); mandate Target 4(iv)
("prove that implication too")
Kind: P
Fidelity: exact (the kernel form implies the information form; the converse is false —
`SplitComposed.nullθ_not_hval`)
Hyps: (a) all — `hμ` simplex, `hk : HVal k` (the claim's antecedent) -/
theorem condMutualInfo_theta_signal_eq_zero_of_hval (hk : HVal k) :
    I[(thetaOf : (Λ × Θ) × S → Θ) : (sigOf : (Λ × Θ) × S → S) | (lamOf : (Λ × Θ) × S → Λ) ;
      Bridge.joint μ k hμ] = 0 := by
  rw [← klFin_joint3_fact3_eq_condMutualInfo measurable_thetaOf measurable_sigOf measurable_lamOf,
    joint3_eq_fact3_of_hval hμ hk, klFin_self]

/-- **H_val as conditional independence**: under `HVal k`, `θ ⊥ S | Λ` on the joint measure
(FAF's `condMutualInfo_eq_zero`).
Source: [[generalization-final]] S3(c) l. 68; mandate Target 4(iv)
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem condIndepFun_theta_signal_of_hval (hk : HVal k) :
    CondIndepFun (thetaOf : (Λ × Θ) × S → Θ) (sigOf : (Λ × Θ) × S → S)
      (lamOf : (Λ × Θ) × S → Λ) (Bridge.joint μ k hμ) :=
  (ShannonInformation.condMutualInfo_eq_zero measurable_thetaOf measurable_sigOf
    measurable_lamOf).1 (condMutualInfo_theta_signal_eq_zero_of_hval hμ hk)

end

end Cleanroom.Info.InfoVoiLatents.Split
