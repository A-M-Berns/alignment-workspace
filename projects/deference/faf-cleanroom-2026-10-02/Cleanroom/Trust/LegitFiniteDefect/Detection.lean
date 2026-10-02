import Cleanroom.Trust.LegitFiniteDefect.Defs
import Cleanroom.Trust.LegitFiniteDefect.Wirehead

/-!
# The detection hierarchy

Package `legit-finite-defect`, Targets 4 (load-bearing 2) and 12 (extension). Which gate classes
detect which corruptions:

* **Question gates see exactly cellwise conditional agreement** (`endorses_questionGates_iff`,
  Target 12): for a question `Q : W → C`, zero defect on every nonnegative `Q`-determined weight
  holds iff `∑_{Q = c} π θ = ∑_{Q = c} π R` on every positive-mass cell. The engine is the
  conditional-mean regrouping `defect_comp_eq_sum_fibres`, proved as a fibrewise regrouping of
  the sum (not by relabelling `defect_decomp`).
* **Report gates see exactly miscalibration** (`endorses_reportGates_iff_calibrated`, Target 4(1)):
  the case `Q = R`.
* **World gates see exactly pointwise truth** (`endorses_worldGates_iff`, Target 4(2)): the case
  `Q = id`, proved from the wirehead iff applied to `(θ, R)` and `(R, θ)`.
* **Calibrated garblings are calibrated** (`calibrated_calibratedGarbling`, Target 4(3)): the
  conditional-mean report through any signal map is invisible to every report gate.
* **The coexistence instance** (`Coexist`, Target 4(4)): a coarse calibrated garbling with zero
  defect on every report gate, a world gate that sees it, and a strictly lower threshold value
  than the finer (itself garbled) report on an explicit two-option rule.
* **The hierarchy as an order** (`Endorses.of_refines`): a finer question detects more.

Register: finite shadow of v6 §6.3's "checking calibration on everything you can check gives no
guarantee about what you cannot"; the missing ingredient is an access class, not a better defect.
-/

namespace Cleanroom.Trust.LegitFiniteDefect

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The regrouping identity -/

/-- **Conditional-mean regrouping.** For a question `Q : W → C` and a weight `v ∘ Q` determined by
it, the defect regroups over the cells of `Q`:
`defect π θ R (v ∘ Q) = ∑_{c ∈ image Q} v c · (∑_{Q = c} π θ − ∑_{Q = c} π R)`. Proved by
fibrewise regrouping of the sum over worlds (`Finset.sum_fiberwise_of_maps_to`), then constancy
of `v ∘ Q` on each fibre.
Source: trust-lab-2-030 (1) (the identity `defect_{v∘E} = Σ_e v(e)·π{E = e}·(𝔼_π[θ | E = e] − e)`,
here for a general question); mandate Target 4(1)/12
Kind: P
Fidelity: exact (general question; the report case is `defect_comp_report`)
Hyps: (a) none -/
theorem defect_comp_eq_sum_fibres {C : Type} [DecidableEq C] (π θ R : W → ℝ) (Q : W → C)
    (v : C → ℝ) :
    defect π θ R (v ∘ Q) = ∑ c ∈ univ.image Q, v c *
      (∑ x ∈ univ.filter (fun x => Q x = c), π x * θ x -
        ∑ x ∈ univ.filter (fun x => Q x = c), π x * R x) := by
  rw [defect_decomp]
  have h := Finset.sum_fiberwise_of_maps_to (s := (univ : Finset W)) (t := univ.image Q)
    (g := Q) (fun x _ => mem_image_of_mem Q (mem_univ x))
    (fun x => π x * (v ∘ Q) x * (θ x - R x))
  rw [← h]
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_sub, mul_sum, mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mem_filter] at hx
  simp only [Function.comp, hx.2]
  ring

/-- On a fibre `{R = e}` of the report, `∑_{R = e} π x R x = e · π(R = e)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_fibre_mul_report (π R : W → ℝ) (e : ℝ) :
    ∑ x ∈ univ.filter (fun x => R x = e), π x * R x = e * mass π (univ.filter (fun x => R x = e)) := by
  rw [mass, mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mem_filter] at hx
  rw [hx.2]
  ring

/-- **The report-gate identity** (Target 4(1)): for a report gate `v ∘ R`,
`defect π θ R (v ∘ R) = ∑_{e ∈ image R} v e · (∑_{R = e} π θ − e · π(R = e))` — each report value
contributes its conditional miscalibration, weighted by the gate.
Source: trust-lab-2-030 (1); `run3/questions/scout-legitimacy.md` Q2 (1)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem defect_comp_report (π θ R : W → ℝ) (v : ℝ → ℝ) :
    defect π θ R (v ∘ R) = ∑ e ∈ univ.image R, v e *
      (∑ x ∈ univ.filter (fun x => R x = e), π x * θ x -
        e * mass π (univ.filter (fun x => R x = e))) := by
  rw [defect_comp_eq_sum_fibres]
  apply Finset.sum_congr rfl
  intro e _
  rw [sum_fibre_mul_report]

/-- The defect on the fibre indicator `𝟙[Q = c]` is the cell's conditional disagreement.
Source: none: infrastructure (the gates `𝟙[R = e]` of Target 4(1))
Kind: L
Fidelity: n/a -/
theorem defect_fibre_ind {C : Type} [DecidableEq C] (π θ R : W → ℝ) (Q : W → C) (c : C) :
    defect π θ R (fun x => if Q x = c then 1 else 0) =
      ∑ x ∈ univ.filter (fun x => Q x = c), π x * θ x -
        ∑ x ∈ univ.filter (fun x => Q x = c), π x * R x := by
  rw [defect_decomp, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

/-! ## Target 12: question gates detect exactly cellwise conditional agreement -/

/-- **The detection hierarchy as a characterisation.** For a question `Q : W → C` and a
nonnegative prior, endorsement on the question gates of `Q` (every nonnegative `Q`-determined
weight) holds **iff** on every positive-mass cell of `Q` the conditional sums of target and
report agree: `∑_{Q = c} π θ = ∑_{Q = c} π R`. A gate class generated by a question detects
exactly the failures of `Q`-cellwise conditional agreement. `⟹` uses the cell indicators; `⟸`
writes a `Q`-determined weight as `v ∘ Q` and regroups; null cells contribute nothing on either
side (this is where `hπ` enters).
Source: mandate Target 12 (extension of trust-lab-2-030); [[Deference Done Better]] §5 (questions)
Kind: P
Fidelity: exact
Hyps: (a) `hπ` nonnegativity of the prior -/
theorem endorses_questionGates_iff {C : Type} [DecidableEq C] {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (θ R : W → ℝ) (Q : W → C) :
    Endorses π θ R (questionGates Q) ↔
      ∀ c, 0 < mass π (univ.filter (fun x => Q x = c)) →
        ∑ x ∈ univ.filter (fun x => Q x = c), π x * θ x =
          ∑ x ∈ univ.filter (fun x => Q x = c), π x * R x := by
  constructor
  · intro h c _
    have hw := h _ (fibre_ind_mem_questionGates Q c)
    rw [defect_fibre_ind] at hw
    linarith
  · rintro h w ⟨_, hwQ⟩
    obtain ⟨v, rfl⟩ := hwQ.exists_comp
    rw [defect_comp_eq_sum_fibres]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hpos : 0 < mass π (univ.filter (fun x => Q x = c))
    · rw [h c hpos]; ring
    · have hzero : mass π (univ.filter (fun x => Q x = c)) = 0 :=
        le_antisymm (not_lt.1 hpos) (mass_nonneg hπ _)
      have hnull : ∀ x ∈ univ.filter (fun x => Q x = c), π x = 0 :=
        fun x hx => eq_zero_of_mass_eq_zero hπ hzero hx
      rw [Finset.sum_eq_zero (fun x hx => by rw [hnull x hx]; ring),
        Finset.sum_eq_zero (fun x hx => by rw [hnull x hx]; ring)]
      ring

/-! ## Target 4(1): report gates see exactly miscalibration -/

/-- **Report gates = calibration.** Under a nonnegative prior, zero defect on every report gate
(nonnegative, report-measurable weight) holds **iff** the report is calibrated on its
positive-mass values. The case `Q = R` of the characterisation.
Source: trust-lab-2-030 (1) ("`defect = 0` for all report-measurable gates iff `E` is calibrated
on positive-mass report values"); `run3/questions/scout-legitimacy.md` Q2 (1)
Kind: P
Fidelity: exact
Hyps: (a) `hπ` nonnegativity of the prior -/
theorem endorses_reportGates_iff_calibrated {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x) (θ R : W → ℝ) :
    Endorses π θ R (reportGates R) ↔ Calibrated π θ R := by
  rw [reportGates_eq_questionGates, endorses_questionGates_iff hπ]
  unfold Calibrated
  constructor
  · intro h e he
    rw [← sum_fibre_mul_report]
    exact h e he
  · intro h e he
    rw [sum_fibre_mul_report]
    exact h e he

/-! ## Target 4(2): world gates see exactly pointwise truth -/

/-- **World gates = pointwise truth.** Under a nonnegative prior, zero defect on every nonnegative
weight holds **iff** report and target agree at every positive-mass world. From the wirehead iff
(`S = univ`) applied to `(θ, R)` and to `(R, θ)`.
Source: trust-lab-2-030 (2) ("`defect = 0` for all world-measurable gates iff `θ = E` π-a.e.")
Kind: P
Fidelity: exact
Hyps: (a) `hπ` -/
theorem endorses_worldGates_iff {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x) (θ R : W → ℝ) :
    Endorses π θ R worldGates ↔ ∀ x, 0 < π x → θ x = R x := by
  constructor
  · intro h x hx
    have h1 := (defect_nonpos_on_iff hπ θ R univ).1 (fun w hw _ => (h w hw).le) x (mem_univ _) hx
    have h2 := (defect_nonpos_on_iff hπ R θ univ).1
      (fun w hw _ => by rw [defect_swap, h w hw]; simp) x (mem_univ _) hx
    exact le_antisymm h1 h2
  · intro h w _
    rw [defect_decomp]
    apply Finset.sum_eq_zero
    intro x _
    rcases (hπ x).lt_or_eq with hpos | hzero
    · rw [h x hpos]; ring
    · rw [← hzero]; ring

/-! ## Target 4(3): calibrated garblings are calibrated -/

/-- The conditional-mean report through a signal map is constant on the map's fibres.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem calibratedGarbling_const_on_fibres {S : Type} [Fintype S] [DecidableEq S] (π θ : W → ℝ)
    (f : W → S) {x y : W} (hxy : f x = f y) :
    Blackwell.calibratedGarbling π θ f x = Blackwell.calibratedGarbling π θ f y := by
  simp only [Blackwell.calibratedGarbling, Blackwell.fibreMass, hxy]

/-- **Calibrated garblings are calibrated** — in the product form, for every report value with
positive mass. Each report fibre `{R = e}` is a union of `f`-fibres; on a positive-mass `f`-fibre
the conditional-mean identity `calibratedGarbling_mul_fibreMass` gives `∑ π θ = e · mass`; a
null `f`-fibre has every `π x = 0` (nonnegativity), so it contributes `0` to both sides and the
dependency's junk value `0/0 = 0` never matters.
Source: trust-lab-2-030 (3) ("a calibrated garbling `E := 𝔼_π[θ | s]` … has every
report-measurable defect `= 0`"); mandate Target 4(3)
Kind: P
Fidelity: exact
Hyps: (a) `hπ` nonnegativity of the prior -/
theorem calibrated_calibratedGarbling {S : Type} [Fintype S] [DecidableEq S] {π : W → ℝ}
    (hπ : ∀ x, 0 ≤ π x) (θ : W → ℝ) (f : W → S) :
    Calibrated π θ (Blackwell.calibratedGarbling π θ f) := by
  intro e _
  set R := Blackwell.calibratedGarbling π θ f with hR
  set A := univ.filter (fun x => R x = e) with hA
  have key : ∀ s : S, ∑ x ∈ A.filter (fun x => f x = s), π x * θ x =
      e * ∑ x ∈ A.filter (fun x => f x = s), π x := by
    intro s
    by_cases hne : (A.filter (fun x => f x = s)).Nonempty
    · obtain ⟨w, hw⟩ := hne
      rw [mem_filter, hA, mem_filter] at hw
      obtain ⟨⟨_, hRw⟩, hfw⟩ := hw
      have hset : A.filter (fun x => f x = s) = univ.filter (fun v => f v = f w) := by
        ext x
        simp only [hA, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨_, hx⟩
          rw [hx, hfw]
        · intro hx
          refine ⟨?_, by rw [hx, hfw]⟩
          rw [hR, calibratedGarbling_const_on_fibres π θ f hx]
          exact hRw
      rw [hset]
      have hfm : Blackwell.fibreMass π f w = ∑ x ∈ univ.filter (fun v => f v = f w), π x := rfl
      rcases (Finset.sum_nonneg (fun x _ => hπ x) :
          (0 : ℝ) ≤ ∑ x ∈ univ.filter (fun v => f v = f w), π x).lt_or_eq with hpos | hzero
      · have h1 := Blackwell.calibratedGarbling_mul_fibreMass π θ f w (by rw [hfm]; exact hpos)
        rw [← h1, hfm, ← hRw]
      · have hnull : ∀ x ∈ univ.filter (fun v => f v = f w), π x = 0 :=
          fun x hx => (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hπ x)).1 hzero.symm x hx
        rw [Finset.sum_eq_zero (fun x hx => by rw [hnull x hx]; ring), ← hzero]
        ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  calc ∑ x ∈ A, π x * θ x = ∑ s, ∑ x ∈ A.filter (fun x => f x = s), π x * θ x :=
        (Finset.sum_fiberwise_of_maps_to (s := A) (t := (univ : Finset S)) (g := f)
          (fun x _ => mem_univ (f x)) (fun x => π x * θ x)).symm
    _ = ∑ s, e * ∑ x ∈ A.filter (fun x => f x = s), π x := Finset.sum_congr rfl (fun s _ => key s)
    _ = e * ∑ s, ∑ x ∈ A.filter (fun x => f x = s), π x := by rw [mul_sum]
    _ = e * mass π A := by
        rw [Finset.sum_fiberwise_of_maps_to (s := A) (t := (univ : Finset S)) (g := f)
          (fun x _ => mem_univ (f x)) (fun x => π x)]
        rfl

/-- **A calibrated garbling is invisible to every report gate** (the "numbing" reading of 2-030:
a report that is calibrated but coarser than the truth — the conditional mean through any signal
map — has zero defect on every nonnegative report-measurable weight). Composition of Target 4(3)
with Target 4(1).
Source: trust-lab-2-030 (3); mandate stretch list ("numbing" reading, a named corollary of 4(3))
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem calibratedGarbling_endorsed_on_reportGates {S : Type} [Fintype S] [DecidableEq S]
    {π : W → ℝ} (hπ : ∀ x, 0 ≤ π x) (θ : W → ℝ) (f : W → S) :
    Endorses π θ (Blackwell.calibratedGarbling π θ f)
      (reportGates (Blackwell.calibratedGarbling π θ f)) :=
  (endorses_reportGates_iff_calibrated hπ θ _).2 (calibrated_calibratedGarbling hπ θ f)

/-! ## The hierarchy as an order -/

/-- A finer question's gates include a coarser question's gates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem questionGates_subset_of_refines {C D : Type} {Q' : W → C} {Q : W → D}
    (h : Blackwell.Refines Q' Q) : questionGates Q ⊆ questionGates Q' := by
  obtain ⟨g, rfl⟩ := h
  rintro w ⟨hw0, hwQ⟩
  refine ⟨hw0, fun x y hxy => hwQ x y ?_⟩
  simp only [Function.comp, hxy]

/-- **Monotonicity**: endorsement on the gates of a finer question implies endorsement on the gates
of a coarser one — the detection hierarchy is an order (finer questions detect more).
Source: mandate Target 12 (monotonicity `Blackwell.Refines Q' Q → (Q'-endorsed → Q-endorsed)`)
Kind: L
Fidelity: exact -/
theorem Endorses.of_refines {C D : Type} {π θ R : W → ℝ} {Q' : W → C} {Q : W → D}
    (h : Blackwell.Refines Q' Q) (hE : Endorses π θ R (questionGates Q')) :
    Endorses π θ R (questionGates Q) :=
  fun w hw => hE w (questionGates_subset_of_refines h hw)

/-! ## Target 4(4): the coexistence instance -/

namespace Coexist

/-- The uniform prior on four worlds.
Source: mandate Target 4(4)
Kind: D
Fidelity: n/a -/
def π4 : Fin 4 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4]

/-- The target `θ = (1, 0, 1, 0)`.
Source: mandate Target 4(4)
Kind: D
Fidelity: n/a -/
def θ4 : Fin 4 → ℝ := ![1, 0, 1, 0]

/-- The fine signal map, cells `{0}, {1}, {2, 3}`.
Source: mandate Target 4(4)
Kind: D
Fidelity: n/a -/
def fFine : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The coarse signal map, cells `{0, 1}, {2, 3}`.
Source: mandate Target 4(4)
Kind: D
Fidelity: n/a -/
def fCoarse : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The fine report: the calibrated garbling of `θ` through the fine map.
Source: mandate Target 4(4)
Kind: D
Fidelity: n/a -/
def Rfine : Fin 4 → ℝ := Blackwell.calibratedGarbling π4 θ4 fFine

/-- The coarse report: the calibrated garbling of `θ` through the coarse map.
Source: mandate Target 4(4)
Kind: D
Fidelity: n/a -/
def Rcoarse : Fin 4 → ℝ := Blackwell.calibratedGarbling π4 θ4 fCoarse

/-- The prior is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π4_nonneg : ∀ x, 0 ≤ π4 x := fun x => by fin_cases x <;> norm_num [π4]

/-- The fine report computed: `(1, 0, 1/2, 1/2)` — itself a proper garbling, not the truth.
Source: mandate Target 4(4)
Kind: L
Fidelity: n/a -/
theorem Rfine_eq : Rfine = ![1, 0, 1 / 2, 1 / 2] := by
  funext x
  fin_cases x <;>
    simp [Rfine, Blackwell.calibratedGarbling, Blackwell.fibreMass, Finset.sum_filter,
      Fin.sum_univ_four, π4, θ4, fFine, vec4_two, vec4_three] <;> norm_num

/-- The coarse report computed: constantly `1/2`.
Source: mandate Target 4(4)
Kind: L
Fidelity: n/a -/
theorem Rcoarse_eq : Rcoarse = fun _ => 1 / 2 := by
  funext x
  fin_cases x <;>
    simp [Rcoarse, Blackwell.calibratedGarbling, Blackwell.fibreMass, Finset.sum_filter,
      Fin.sum_univ_four, π4, θ4, fCoarse, vec4_two, vec4_three] <;> norm_num

/-- **Coexistence (a): invisible to report gates.** The coarse report has zero defect on every
report gate (by `calibratedGarbling_endorsed_on_reportGates`), and so does the fine one.
Source: trust-lab-2-030 (3); mandate Target 4(4)(a)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reportGates_blind :
    Endorses π4 θ4 Rcoarse (reportGates Rcoarse) ∧ Endorses π4 θ4 Rfine (reportGates Rfine) :=
  ⟨calibratedGarbling_endorsed_on_reportGates π4_nonneg θ4 fCoarse,
    calibratedGarbling_endorsed_on_reportGates π4_nonneg θ4 fFine⟩

/-- **Coexistence (b): a world gate sees it.** On the point mass at world `1` the coarse report's
defect is `−1/8 ≠ 0`.
Source: trust-lab-2-030 (3) ("a world-measurable witness gate has `defect ≠ 0`"); mandate Target 4(4)(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem worldGate_sees : defect π4 θ4 Rcoarse (ind {1}) = -1 / 8 := by
  rw [defect_ind_singleton, Rcoarse_eq]
  simp only [π4, θ4]
  norm_num

/-- **Coexistence (b) for the fine report.** The coarse report is constant (`Rcoarse_eq`), so its
report-gate class is the constant weights and its clause (a) holds for the trivial reason that a
constant report carries no information; the *fine* report has a non-trivial report-gate class
(three cells) and is still seen by a world gate: on the point mass at world `2` its defect is
`+1/8 ≠ 0`. So the triple (a)+(b)+(c) holds for a garbling whose report gates are not all
constant.
Source: audit round 1 (fidelity N1, probe 2a); trust-lab-2-030 (3)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fine_worldGate_sees : defect π4 θ4 Rfine (ind {2}) = 1 / 8 := by
  rw [defect_ind_singleton, Rfine_eq]
  simp only [π4, θ4, vec4_two]
  norm_num

/-- **The ungarbled report's value.** Under the declared rule "act iff `R ≥ 2/5`" the truth `θ`
itself is worth `3/10`: this is the source's actual comparison point ("relative to the ungarbled
report"), so with `value_drop` the chain is `3/10 > 1/5 > 1/10` — both garblings lose value
against the truth, and the coarser one loses more.
Source: trust-lab-2-030 (3) ("Value strictly drops relative to the ungarbled report"); audit
round 1 (fidelity N1, probe 2b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ungarbled_value : thresholdValue π4 θ4 θ4 (2 / 5) = 3 / 10 := by
  simp only [thresholdValue, Fin.sum_univ_four, π4, θ4, vec4_two, vec4_three]
  norm_num

/-- **Coexistence (c): strictly less valuable.** Under the declared rule "act iff `R ≥ 2/5`", the
fine report is worth `1/5` and the coarse report `1/10`; the threshold separates the two
(the fine report does not fire at world `1`, the coarse one does). The source compares each
garbling with the *ungarbled* report, worth `3/10` (`ungarbled_value`); this statement is the
fine-vs-coarse comparison the mandate asked for, and the two together give `3/10 > 1/5 > 1/10`.
The drop is not an artifact of the threshold: `value_drop_other_thresholds` gives `1/8` vs `0` at
`c = 1/2` and `1/16` vs `0` at `c = 3/4`.
Source: trust-lab-2-030 (3) ("Value strictly drops relative to the ungarbled report"); mandate
Target 4(4)(c); the general "a garbling never gains" is `tt-finite-frames`'s (corr-wf13-010)
Kind: N+
Fidelity: variant: fine-vs-coarse garblings (the source's ungarbled comparison is
`ungarbled_value`); the instance only, the general monotonicity is not proved here
Hyps: (a) none -/
theorem value_drop :
    thresholdValue π4 θ4 Rfine (2 / 5) = 1 / 5 ∧ thresholdValue π4 θ4 Rcoarse (2 / 5) = 1 / 10 ∧
      ¬ ((2 / 5 : ℝ) ≤ Rfine 1) ∧ ((2 / 5 : ℝ) ≤ Rcoarse 1) := by
  rw [Rfine_eq, Rcoarse_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [thresholdValue, Fin.sum_univ_four, π4, θ4, vec4_two, vec4_three]
    norm_num
  · simp only [thresholdValue, Fin.sum_univ_four, π4, θ4, vec4_two, vec4_three]
    norm_num
  · simp
  · norm_num

/-- The value drop is robust to the threshold: at `c = 1/2` the fine report is worth `1/8` and the
coarse `0`; at `c = 3/4`, `1/16` and `0`.
Source: audit round 1 (adversarial probe P7); mandate Target 4(4)(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem value_drop_other_thresholds :
    thresholdValue π4 θ4 Rfine (1 / 2) = 1 / 8 ∧ thresholdValue π4 θ4 Rcoarse (1 / 2) = 0 ∧
      thresholdValue π4 θ4 Rfine (3 / 4) = 1 / 16 ∧ thresholdValue π4 θ4 Rcoarse (3 / 4) = 0 := by
  rw [Rfine_eq, Rcoarse_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [thresholdValue, Fin.sum_univ_four, π4, θ4, vec4_two, vec4_three] <;> norm_num

/-- The fine report is not the truth (a proper garbling): they differ at world `2`.
Source: mandate Target 4(4) ("itself a proper garbling, not `θ`")
Kind: N+
Fidelity: exact -/
theorem Rfine_ne_θ : Rfine ≠ θ4 := by
  intro h
  have := congrFun h 2
  rw [Rfine_eq] at this
  simp [θ4, vec4_two] at this

end Coexist

end

end Cleanroom.Trust.LegitFiniteDefect
