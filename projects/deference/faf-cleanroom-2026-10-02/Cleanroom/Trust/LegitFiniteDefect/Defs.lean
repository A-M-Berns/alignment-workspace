import Cleanroom.Found.LitDdbFrames
import Cleanroom.Trust.LegitFiniteDefect.Vec

/-!
# The legitimacy defect in finite shadows — definitions of record

Package `legit-finite-defect` (faf-cleanroom run, 2026-09-29), Target 1. This file holds every
definition the package's theorem files share, and only identities (kind L) about them. It is kept
small and theorem-light on purpose: `legit-li-register` imports the *definition* of the defect and
the gate classes to lift them over FAF histories.

Register: everything here is a **finite shadow** of [[li-deference]] §0.3's legitimacy problem —
one principal `π`, one target `θ`, one report `R`, one selection weight `w` — over the finite
probability frames of `lit-ddb-frames`. No FAF object is used (the LI register is
`legit-li-register`'s); the frame vocabulary (`E`, `mass`, `ind`, `supp`, `Frame`, `TotalTrust`)
is the dependency's, never re-declared.

Carrier: worlds `W` with `[Fintype W] [DecidableEq W]`; priors `π : W → ℝ` with `∀ x, 0 ≤ π x`
carried as a hypothesis where a theorem needs it, and `π ∈ stdSimplex ℝ W` only where the
dependency's cycle needs it.
-/

namespace Cleanroom.Trust.LegitFiniteDefect

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The defect -/

/-- The **legitimacy defect** of a process reporting `R` for the target `θ`, to a principal `π`,
on the selection weight `w`: `E_π(θ·w) − E_π(R·w)`, the principal's expectation of the target on
the weight minus its expectation of the report on the same weight. The report is written `R`
(the model writes `E_Π(θ)`) so as not to collide with the dependency's expectation `E`.
Source: [[legitimacy-corrigibility-model]] §1.1 (Definition, legitimacy defect); trust-lab-019
Kind: D
Fidelity: exact -/
def defect (π θ R w : W → ℝ) : ℝ :=
  E π (fun x => θ x * w x) - E π (fun x => R x * w x)

/-- **Decomposition identity**: the defect is the single signed weighted sum
`∑ x, π x · w x · (θ x − R x)`. Pure linearity.
Source: [[legitimacy-corrigibility-model]] §1.1 (decomposition identity); trust-lab-019
Kind: L
Fidelity: exact -/
theorem defect_decomp (π θ R w : W → ℝ) :
    defect π θ R w = ∑ x, π x * w x * (θ x - R x) := by
  unfold defect E
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Swapping target and report negates the defect.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem defect_swap (π θ R w : W → ℝ) : defect π R θ w = -defect π θ R w := by
  rw [defect_decomp, defect_decomp, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The defect on a point mass `ind {x}` is the single term `π x · (θ x − R x)`.
Source: none: infrastructure (Target 2's necessity direction)
Kind: L
Fidelity: n/a -/
theorem defect_ind_singleton (π θ R : W → ℝ) (x : W) :
    defect π θ R (ind {x}) = π x * (θ x - R x) := by
  rw [defect_decomp]
  rw [Finset.sum_eq_single x]
  · simp [ind]
  · intro y _ hy
    simp [ind, hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- **Endorsement** on a weight class: zero defect on every weight of the class.
Source: [[legitimacy-corrigibility-model]] §1.1 (Definition, `N` endorses `Π`)
Kind: D
Fidelity: exact -/
def Endorses (π θ R : W → ℝ) (𝒲 : Set (W → ℝ)) : Prop := ∀ w ∈ 𝒲, defect π θ R w = 0

/-! ## Gate classes -/

/-- The **world gates**: every nonnegative weight (the principal may select on the world itself).
Source: trust-lab-2-030 (2) ("world-measurable nonneg gates")
Kind: D
Fidelity: exact -/
def worldGates : Set (W → ℝ) := {w | ∀ x, 0 ≤ w x}

/-- A weight `w` is **determined by** a map `Q : W → C` (measurable with respect to the partition
of `Q`): constant on each fibre of `Q`. Unlike the dependency's `MeasurableWrt`, no finiteness of
`C` is required, so `C = ℝ` (a real-valued report) is allowed.
Source: trust-lab-2-030 (1) ("report-measurable weights `w = v ∘ E`"); [[Deference Done Better]]
§5 (measurability with respect to a question)
Kind: D
Fidelity: exact -/
def DeterminedBy {C : Type} (Q : W → C) (w : W → ℝ) : Prop := ∀ x y, Q x = Q y → w x = w y

/-- **Report-measurability**: the weight depends on the world only through the report value.
Source: trust-lab-2-030 (1)
Kind: D
Fidelity: exact -/
abbrev ReportMeasurable (R w : W → ℝ) : Prop := DeterminedBy R w

/-- The **report gates**: nonnegative report-measurable weights — the class a principal who sees
only the report can compute.
Source: trust-lab-2-030 (1); [[legitimacy-corrigibility-model]] §2.4 (the witness `Ind(E_drug > p)`)
Kind: D
Fidelity: exact -/
def reportGates (R : W → ℝ) : Set (W → ℝ) := {w | (∀ x, 0 ≤ w x) ∧ ReportMeasurable R w}

/-- The **question gates** of a question `Q : W → C`: nonnegative `Q`-determined weights.
Source: mandate Target 12; [[Deference Done Better]] §5
Kind: D
Fidelity: exact -/
def questionGates {C : Type} (Q : W → C) : Set (W → ℝ) := {w | (∀ x, 0 ≤ w x) ∧ DeterminedBy Q w}

/-- The report gates are the question gates of the report itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem reportGates_eq_questionGates (R : W → ℝ) : reportGates R = questionGates R := rfl

/-- For a finite question type, `DeterminedBy Q` is the dependency's `MeasurableWrt Q`.
Source: none: infrastructure (Target 1)
Kind: L
Fidelity: n/a -/
theorem determinedBy_iff_measurableWrt {C : Type} [Fintype C] [DecidableEq C] (Q : W → C)
    (w : W → ℝ) : DeterminedBy Q w ↔ MeasurableWrt Q w :=
  Iff.rfl

/-- A composite `v ∘ Q` is determined by `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem determinedBy_comp {C : Type} (Q : W → C) (v : C → ℝ) : DeterminedBy Q (v ∘ Q) :=
  fun _ _ h => by simp only [Function.comp, h]

/-- Every `Q`-determined weight is a composite `v ∘ Q` (with `v` chosen on the image of `Q` and
`0` off it).
Source: none: infrastructure (Target 4(1), "every `ReportMeasurable` `w` is some `v ∘ R`")
Kind: L
Fidelity: n/a -/
theorem DeterminedBy.exists_comp {C : Type} {Q : W → C} {w : W → ℝ} (h : DeterminedBy Q w) :
    ∃ v : C → ℝ, w = v ∘ Q := by
  classical
  refine ⟨fun c => if hc : ∃ x, Q x = c then w (Classical.choose hc) else 0, ?_⟩
  funext x
  have hx : ∃ y, Q y = Q x := ⟨x, rfl⟩
  simp only [Function.comp, dif_pos hx]
  exact (h _ _ (Classical.choose_spec hx)).symm

/-- The indicator of a fibre `{Q = c}` is a question gate of `Q`.
Source: none: infrastructure (Target 4(1)/12, the gates `𝟙[R = e]`)
Kind: L
Fidelity: n/a -/
theorem fibre_ind_mem_questionGates {C : Type} [DecidableEq C] (Q : W → C) (c : C) :
    (fun x => if Q x = c then (1 : ℝ) else 0) ∈ questionGates Q := by
  refine ⟨fun x => by dsimp only; split_ifs <;> norm_num, fun x y h => by simp only [h]⟩

/-- The indicator of a proposition is a world gate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ind_mem_worldGates (q : Finset W) : ind q ∈ worldGates := by
  intro x
  unfold ind
  split_ifs <;> norm_num

/-! ## Calibration -/

/-- **Calibration** of a report `R` for `θ` under `π`, on positive-mass report values, in product
form (no division): for every value `e` with `π(R = e) > 0`,
`∑_{R = e} π x θ x = e · π(R = e)`, i.e. `E_π[θ | R = e] = e`.
Source: trust-lab-2-030 (1) ("calibrated on positive-mass report values")
Kind: D
Fidelity: exact -/
def Calibrated (π θ R : W → ℝ) : Prop :=
  ∀ e : ℝ, 0 < mass π (univ.filter (fun x => R x = e)) →
    ∑ x ∈ univ.filter (fun x => R x = e), π x * θ x = e * mass π (univ.filter (fun x => R x = e))

/-- Ratio form of calibration on a positive-mass report value: `E_π[θ | R = e] = e`.
Source: none: infrastructure (Target 1, "a ratio lemma may follow")
Kind: L
Fidelity: n/a -/
theorem Calibrated.ratio {π θ R : W → ℝ} (h : Calibrated π θ R) (e : ℝ)
    (he : 0 < mass π (univ.filter (fun x => R x = e))) :
    (∑ x ∈ univ.filter (fun x => R x = e), π x * θ x) / mass π (univ.filter (fun x => R x = e))
      = e := by
  rw [h e he]
  exact mul_div_cancel_right₀ e he.ne'

/-! ## The bridge to DDB: an expert's report -/

/-- The **report of a frame expert**: at world `w` the expert `P_w` reports its expectation of `θ`,
`E_{P_w}(θ)`. This is the bridge between the package's `(θ, R)` vocabulary and DDB's frames:
a DDB expert *is* a process whose report of `θ` is this function. (Not spelled `Frame.report`
because dot-notation would look it up in the dependency's namespace.)
Source: [[Deference Done Better]] §1 (the expert's expectations); mandate Target 1
Kind: D
Fidelity: exact -/
def frameReport (F : Frame W) (θ : W → ℝ) : W → ℝ := fun w => E (F.P w) θ

/-- **The `θ`-instance of Total Trust.** Under `TotalTrust π F`, for every threshold `s`,
`0 ≤ ∑ w, π w · (θ w − s) · 𝟙[s ≤ frameReport F θ w]` — the product-form inequality at the
variable `θ` itself, which is literally `h θ s`. This is the one place the package's vocabulary
meets DDB's; `legit-li-register` and `trust-merge` cite this lemma.
Source: [[Deference Done Better]] §2 (Total Trust); mandate Target 1
Kind: L
Fidelity: exact -/
theorem TotalTrust.report_ineq {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) (θ : W → ℝ)
    (s : ℝ) :
    0 ≤ ∑ w, π w * (θ w - s) * (if s ≤ frameReport F θ w then 1 else 0) :=
  h θ s

/-- The **threshold value** of acting on a report: the value of the declared rule "act (take `θ`)
iff `R ≥ c`, else take the constant `c`", minus the constant: `∑ x, π x · (θ x − c) · 𝟙[c ≤ R x]`.
This is the two-option decision value used by the detection hierarchy's coexistence instance.
Source: trust-lab-2-030 (3) ("argmax-following Value on an explicit menu"); mandate Target 4(4)
Kind: D
Fidelity: exact -/
def thresholdValue (π θ R : W → ℝ) (c : ℝ) : ℝ :=
  ∑ x, π x * (θ x - c) * (if c ≤ R x then 1 else 0)

/-- When the report is a frame expert's, the threshold value is the two-option strategy value
of `lit-ddb-frames` (its `stratValue π (F.twoOption θ c) − c`), so the "act iff `R ≥ c`" rule is
DDB's recommended two-option strategy.
Source: [[Deference Done Better]] App. B Lemma 7.1; `lit-ddb-frames` `stratValue_twoOption`
Kind: L
Fidelity: exact -/
theorem thresholdValue_frameReport {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W)
    (θ : W → ℝ) (c : ℝ) :
    thresholdValue π θ (frameReport F θ) c = stratValue π (F.twoOption θ c) - c := by
  rw [stratValue_twoOption hπ]
  rfl

/-! ## The comply-advantage -/

/-- The **comply-advantage** of a shutdown signal with weight `s` against the danger indicator
`d`: the AI's expected value of complying (scored by `d`) minus resisting (scored by `1 − d`),
`E_π(s·d) − E_π(s·(1 − d))`.
Source: [[legitimacy-corrigibility-model]] §3.1 (comply-advantage); trust-lab-021
Kind: D
Fidelity: exact -/
def complyAdv (π s d : W → ℝ) : ℝ :=
  E π (fun x => s x * d x) - E π (fun x => s x * (1 - d x))

/-- The comply-advantage is the signed weighted sum `∑ x, π x · s x · (2 d x − 1)`. Pure linearity.
Source: [[legitimacy-corrigibility-model]] §3.1 (`comply_iff_endorsed`); trust-lab-021
Kind: L
Fidelity: exact -/
theorem complyAdv_decomp (π s d : W → ℝ) :
    complyAdv π s d = ∑ x, π x * s x * (2 * d x - 1) := by
  unfold complyAdv E
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-! ## The trader shadow -/

/-- The **finite trader shadow**: the expected profit, against the principal's prices `π`, of a
trader who buys `θ` at the process's reported price `R x`, `w x` units at world `x`:
`E_π(w · (θ − R))`. This is a *finite shadow only*: the FAF trader (a trading strategy on a market
with budgets and continuity) is not built here — that identification is a modelling substitution
`(c)` disclosed here and in the ledger; the weight class of record is `worldGates`/`reportGates`.
Source: [[legitimacy-corrigibility-model]] §2.2 clause 3 (the drug-trader); trust-lab-020
Kind: D
Fidelity: variant: finite shadow of a trader's expected profit; the FAF trader is not modelled (c) -/
def traderProfit (π θ R w : W → ℝ) : ℝ := E π (fun x => w x * (θ x - R x))

/-- The trader shadow's expected profit *is* the defect.
Source: [[legitimacy-corrigibility-model]] §2.2 clause 3; trust-lab-020
Kind: L
Fidelity: exact (of the finite shadow) -/
theorem traderProfit_eq_defect (π θ R w : W → ℝ) : traderProfit π θ R w = defect π θ R w := by
  rw [defect_decomp]
  unfold traderProfit E
  apply Finset.sum_congr rfl
  intro x _
  ring

end

end Cleanroom.Trust.LegitFiniteDefect
