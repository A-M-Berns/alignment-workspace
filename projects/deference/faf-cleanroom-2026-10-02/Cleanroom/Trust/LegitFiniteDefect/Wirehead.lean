import Cleanroom.Trust.LegitFiniteDefect.Defs

/-!
# The wirehead iff and the red-team correction

Package `legit-finite-defect`, Target 2 (load-bearing 1). The round-1 model proved only
"pointwise overstatement ⇒ defect ≤ 0" (`wirehead_declined`); the red team found that "average
reported utility rises" does not give the sign, and asked for the *converse*: which reports have
nonpositive defect on the model's own weight class. The answer (`defect_nonpos_on_iff`) is a
characterisation: nonpositive defect on every nonnegative weight supported in `S` holds exactly
when the report overstates the target at every positive-mass world of `S`. Necessity is the
direction round 1 never had (point masses). Both mandatory witnesses are compiled: the
euphoric-but-numb report (average rises, defect positive on the model's own gate) and an
`S ⊊ W` report where the localised hypothesis holds but the global one fails.

Register: finite shadow; no theorem here is named `declines` or `wirehead` — "declines" in the
model is a tie (`V_now(drug) = E_π θ = V_now(abstain)`), recorded in the findings, not proved as
a theorem.
-/

namespace Cleanroom.Trust.LegitFiniteDefect

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The wirehead iff.** For a nonnegative prior `π` and a support set `S`: the defect is `≤ 0`
on *every* nonnegative weight supported in `S` **iff** the report overstates the target
(`θ x ≤ R x`) at every world of `S` with positive prior mass. `⟸` is the support-localised sum;
`⟹` uses the point masses `ind {x}`. The weight class *is* the detector, and this says what it
detects.
Source: trust-lab-2-029 (`leg-wirehead-iff`); [[legitimacy-corrigibility-redteam]] "Single most
valuable next step"; `run3/questions/scout-legitimacy.md` Q1
Kind: P
Fidelity: exact
Hyps: (a) `hπ` is nonnegativity of the prior; no other hypothesis -/
theorem defect_nonpos_on_iff {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x) (θ R : W → ℝ) (S : Finset W) :
    (∀ w : W → ℝ, (∀ x, 0 ≤ w x) → (∀ x, x ∉ S → w x = 0) → defect π θ R w ≤ 0) ↔
      ∀ x ∈ S, 0 < π x → θ x ≤ R x := by
  constructor
  · intro h x hxS hx
    have hw := h (ind {x}) (ind_mem_worldGates {x}) (by
      intro y hy
      simp only [ind, mem_singleton]
      rw [if_neg]
      rintro rfl
      exact hy hxS)
    rw [defect_ind_singleton] at hw
    by_contra hlt
    rw [not_le] at hlt
    have := mul_pos hx (sub_pos.2 hlt)
    linarith
  · intro h w hw hS
    rw [defect_decomp]
    apply Finset.sum_nonpos
    intro x _
    by_cases hxS : x ∈ S
    · rcases (hπ x).lt_or_eq with hpos | hzero
      · have hθ := h x hxS hpos
        have h1 : 0 ≤ π x * w x := mul_nonneg (hπ x) (hw x)
        nlinarith [mul_nonneg h1 (sub_nonneg.2 hθ)]
      · rw [← hzero]; simp
    · rw [hS x hxS]; simp

/-- The run-1 instance (`S = univ`): pointwise overstatement everywhere gives nonpositive defect
on every nonnegative weight. A one-line corollary of the iff, not a headline.
Source: [[legitimacy-corrigibility-model]] §2.2 (`wirehead_declined`), `lean/legitimacy.lean`
`drug_defect_sign`; trust-lab-020
Kind: L
Fidelity: exact -/
theorem defect_nonpos_of_overstates {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x) {θ R w : W → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hover : ∀ x, θ x ≤ R x) : defect π θ R w ≤ 0 :=
  (defect_nonpos_on_iff hπ θ R univ).2 (fun x _ _ => hover x) w hw
    (fun x hx => absurd (mem_univ x) hx)

/-- The strict instance: pointwise overstatement plus a strict overshoot at a world of positive
`π·w` mass gives strictly negative defect.
Source: [[legitimacy-corrigibility-model]] §2.2 ("strictly if the overshoot is strict on a
positive-mass, positive-weight world"); trust-lab-020
Kind: L
Fidelity: exact -/
theorem defect_neg_of_strict_overstate {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x) {θ R w : W → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hover : ∀ x, θ x ≤ R x) (x₀ : W) (hx₀ : θ x₀ < R x₀)
    (hpos : 0 < π x₀ * w x₀) : defect π θ R w < 0 := by
  rw [defect_decomp]
  have : ∑ x, π x * w x * (θ x - R x) < ∑ _x : W, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro x _
      nlinarith [mul_nonneg (mul_nonneg (hπ x) (hw x)) (sub_nonneg.2 (hover x))]
    · exact ⟨x₀, mem_univ _, by nlinarith [mul_pos hpos (sub_pos.2 hx₀)]⟩
  simpa using this

/-! ## Witness (a): euphoric-but-numb — the average report rises, the defect is positive -/

namespace Wirehead

/-- The target on two worlds: `θ = (1, 0)` (world `0` is the good one).
Source: [[legitimacy-corrigibility-redteam]] Finding 1
Kind: D
Fidelity: exact -/
def θ₂ : Fin 2 → ℝ := ![1, 0]

/-- The euphoric-but-numb report `(19/20, 1/5)`: slightly under-reports the real good, adds a
little false happiness in the bad world.
Source: [[legitimacy-corrigibility-redteam]] Finding 1
Kind: D
Fidelity: exact -/
def Rnumb : Fin 2 → ℝ := ![19 / 20, 1 / 5]

/-- The average report rises by `3/40` under the uniform prior.
Source: [[legitimacy-corrigibility-redteam]] Finding 1 ("average reported utility rises by +3/40")
Kind: N+
Fidelity: exact -/
theorem numb_average_rises : E Examples.half Rnumb - E Examples.half θ₂ = 3 / 40 := by
  simp only [E, Fin.sum_univ_two, Examples.half, Rnumb, θ₂]
  norm_num

/-- The model's own gate `𝟙[R > 1/2]` on the numb report *is* the point mass `ind {0}`.
Source: [[legitimacy-corrigibility-redteam]] Finding 1 (the witness `w = Ind(E_drug > ½) = (1, 0)`)
Kind: L
Fidelity: exact -/
theorem numb_gate_eq_ind : (fun x => if (1 / 2 : ℝ) < Rnumb x then (1 : ℝ) else 0) = ind {0} := by
  funext x
  fin_cases x <;> simp [Rnumb, ind] <;> norm_num

/-- The model's own gate is a report gate of the numb report (nonnegative and report-measurable).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem numb_gate_mem_reportGates :
    (fun x => if (1 / 2 : ℝ) < Rnumb x then (1 : ℝ) else 0) ∈ reportGates Rnumb :=
  ⟨fun x => by dsimp only; split_ifs <;> norm_num, fun x y h => by simp only [h]⟩

/-- **Witness (a).** On the model's own gate the defect of the numb report is `+1/40 > 0`: a report
that raises average reported utility need not have nonpositive defect. "Reported utility rises"
is not the detected class; overstatement on the firing support is (the iff).
Source: [[legitimacy-corrigibility-redteam]] Finding 1; trust-lab-2-029 witness (a)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem numb_defect_pos : defect Examples.half θ₂ Rnumb (ind {0}) = 1 / 40 := by
  rw [defect_ind_singleton]
  simp only [Examples.half, θ₂, Rnumb]
  norm_num

/-- The numb report fails the iff's right-hand side on `S = {0}` (it under-reports the good
world), which is why the defect on `ind {0}` is positive.
Source: [[legitimacy-corrigibility-redteam]] Finding 1
Kind: N+
Fidelity: exact -/
theorem numb_not_overstating_on_support :
    ¬ ∀ x ∈ ({0} : Finset (Fin 2)), 0 < Examples.half x → θ₂ x ≤ Rnumb x := by
  intro h
  have := h 0 (by simp) (by norm_num [Examples.half])
  simp [θ₂, Rnumb] at this
  norm_num at this

end Wirehead

/-! ## Witness (c): the model's own §2.4 micro-example violates its §2.2 hypothesis -/

namespace WireheadModel

/-- The model's §2.4 prior `(1/4, 3/4)`.
Source: [[legitimacy-corrigibility-model]] §2.4
Kind: D
Fidelity: exact -/
def πM : Fin 2 → ℝ := ![1 / 4, 3 / 4]

/-- The model's §2.4 target `(1, 0)` (world `0` is the good one, `h`).
Source: [[legitimacy-corrigibility-model]] §2.4
Kind: D
Fidelity: exact -/
def θM : Fin 2 → ℝ := ![1, 0]

/-- The model's §2.4 drug report `(9/10, 9/10)`.
Source: [[legitimacy-corrigibility-model]] §2.4
Kind: D
Fidelity: exact -/
def RdrugM : Fin 2 → ℝ := ![9 / 10, 9 / 10]

/-- The prior is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πM_nonneg : ∀ x, 0 ≤ πM x := fun x => by fin_cases x <;> norm_num [πM]

/-- The pointwise-overstatement hypothesis of the model's §2.2 theorem **fails on the model's own
§2.4 example**: at the good world `θ = 1 > 9/10 = R`.
Source: [[legitimacy-corrigibility-model]] §2.2 (hypothesis `θ_x ≤ E_drug,x`) vs §2.4 (the example);
audit round 1 (adversarial probe P1); findings F13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem drug_not_overstating : ¬ ∀ x, θM x ≤ RdrugM x := by
  intro h
  have h0 := h 0
  simp [θM, RdrugM] at h0
  norm_num at h0

/-- The model's number is reproduced: on its gate `w = (1, 1)` the drug's defect is `−13/20`.
Source: [[legitimacy-corrigibility-model]] §2.4 ("defect `−13/20`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem drug_defect_on_ones : defect πM θM RdrugM (fun _ => 1) = -13 / 20 := by
  simp only [defect_decomp, Fin.sum_univ_two, πM, θM, RdrugM]
  norm_num

/-- But on the point mass at the good world the same drug has defect `+1/40 > 0`.
Source: audit round 1 (adversarial probe P1); findings F13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem drug_point_mass_pos : defect πM θM RdrugM (ind {0}) = 1 / 40 := by
  rw [defect_ind_singleton]
  simp only [πM, θM, RdrugM]
  norm_num

/-- **Witness (c).** Through `defect_nonpos_on_iff`, the model's own drug is *not* nonpositive on
the full class of nonnegative gates: the §2.4 example is a witness that the §2.2 hypothesis is
sufficient but not necessary for one fixed gate (`w = (1, 1)`), and is the very kind of drug the
iff says is not declined on the class. The red team's "(b) non-vacuous (micro-example satisfies
it)" is therefore false of the §2.2 hypothesis.
Source: [[legitimacy-corrigibility-model]] §2.4; [[legitimacy-corrigibility-redteam]] (b); audit
round 1 (adversarial probe P1); findings F13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem drug_not_nonpos_on_class :
    ¬ ∀ w : Fin 2 → ℝ, (∀ x, 0 ≤ w x) → (∀ x, x ∉ (univ : Finset (Fin 2)) → w x = 0) →
      defect πM θM RdrugM w ≤ 0 := by
  intro h
  have h0 := (defect_nonpos_on_iff πM_nonneg θM RdrugM univ).1 h 0 (mem_univ _)
    (by norm_num [πM])
  simp [θM, RdrugM] at h0
  norm_num at h0

/-- The model's example **repaired** to satisfy its own §2.2 hypothesis: `E_drug = (1, 9/10)` —
honest in the good world, "happy" in the bad one — overstates `θ = (1, 0)` pointwise, with a
non-constant report.
Source: findings F13 (repair round 1); [[legitimacy-corrigibility-model]] §2.2, §2.4
Kind: D
Fidelity: variant: the §2.4 report with its good-world value raised from `9/10` to `1` -/
def RdrugFix : Fin 2 → ℝ := ![1, 9 / 10]

/-- The repaired drug overstates pointwise, strictly at the bad world.
Source: findings F13
Kind: L
Fidelity: n/a -/
theorem drugFix_overstates : (∀ x, θM x ≤ RdrugFix x) ∧ θM 1 < RdrugFix 1 :=
  ⟨fun x => by fin_cases x <;> norm_num [θM, RdrugFix], by norm_num [θM, RdrugFix]⟩

/-- **N+ witness of `defect_nonpos_of_overstates`** (the earlier ledger rows pointed that instance
at witnesses that fail its global hypothesis): on every nonnegative gate the repaired drug's
defect is `≤ 0`, and on the model's gate `w = (1, 1)` it is `−27/40`.
Source: [[legitimacy-corrigibility-model]] §2.2 (`wirehead_declined`); findings F13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem drugFix_defect_nonpos_on_class :
    (∀ w : Fin 2 → ℝ, (∀ x, 0 ≤ w x) → defect πM θM RdrugFix w ≤ 0) ∧
      defect πM θM RdrugFix (fun _ => 1) = -27 / 40 := by
  refine ⟨fun w hw => defect_nonpos_of_overstates πM_nonneg hw drugFix_overstates.1, ?_⟩
  simp only [defect_decomp, Fin.sum_univ_two, πM, θM, RdrugFix]
  norm_num

/-- **N+ witness of `defect_neg_of_strict_overstate`**: at the bad world `1` the mass `π·w = 3/4`
is positive and the overshoot `0 < 9/10` strict, so the defect on `w = (1, 1)` is strictly
negative (consistent with the computed `−27/40`).
Source: [[legitimacy-corrigibility-model]] §2.2 ("strictly if the overshoot is strict …"); findings F13
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem drugFix_strict : defect πM θM RdrugFix (fun _ => 1) < 0 :=
  defect_neg_of_strict_overstate πM_nonneg (fun _ => zero_le_one) drugFix_overstates.1 1
    drugFix_overstates.2 (by norm_num [πM])

end WireheadModel

/-! ## Witness (b): the localisation to `S ⊊ W` is a real weakening -/

namespace WireheadLocal

/-- The flat report `(1/2, 1/2)` against `θ = (1, 0)`: overstates on world `1`, understates on
world `0`.
Source: mandate Target 2 witness (b)
Kind: D
Fidelity: n/a -/
def Rflat : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The `S = {1}`-restricted overstatement hypothesis holds for the flat report.
Source: mandate Target 2 witness (b)
Kind: L
Fidelity: n/a -/
theorem flat_overstates_on_S :
    ∀ x ∈ ({1} : Finset (Fin 2)), 0 < Examples.half x → Wirehead.θ₂ x ≤ Rflat x := by
  intro x hx _
  simp only [mem_singleton] at hx
  subst hx
  norm_num [Wirehead.θ₂, Rflat]

/-- The global overstatement hypothesis fails for the flat report (at world `0`, of positive
mass).
Source: mandate Target 2 witness (b)
Kind: N+
Fidelity: exact -/
theorem flat_not_overstates_globally :
    ¬ ∀ x ∈ (univ : Finset (Fin 2)), 0 < Examples.half x → Wirehead.θ₂ x ≤ Rflat x := by
  intro h
  have := h 0 (mem_univ _) (by norm_num [Examples.half])
  simp [Wirehead.θ₂, Rflat] at this
  norm_num at this

/-- **Witness (b).** With the hypothesis localised to `S = {1}`, the iff yields nonpositive defect
on the weights supported in `{1}`; on `ind {1}` it is `−1/4 < 0` outright, while the global
hypothesis fails — so the localisation to `S ⊊ W` is a real weakening of round 1's `hover`.
Source: trust-lab-2-029 witness (b); mandate Target 2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem flat_defect_neg_on_S :
    defect Examples.half Wirehead.θ₂ Rflat (ind {1}) = -1 / 4 ∧
      (∀ w : Fin 2 → ℝ, (∀ x, 0 ≤ w x) → (∀ x, x ∉ ({1} : Finset (Fin 2)) → w x = 0) →
        defect Examples.half Wirehead.θ₂ Rflat w ≤ 0) := by
  refine ⟨?_, (defect_nonpos_on_iff (fun x => by fin_cases x <;> norm_num [Examples.half])
    Wirehead.θ₂ Rflat {1}).2 flat_overstates_on_S⟩
  rw [defect_ind_singleton]
  simp only [Examples.half, Wirehead.θ₂, Rflat]
  norm_num

end WireheadLocal

end

end Cleanroom.Trust.LegitFiniteDefect
