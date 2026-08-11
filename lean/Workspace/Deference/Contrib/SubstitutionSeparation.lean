/-
# What an extensional criterion can and cannot separate

Source: `prompts/2026-08-11-deference-channel/REPORT.md` §1.2 (Propositions 1, 2, 6) and
§1.3 (Proposition 7), with the inhabitation witness of that report's §1.1, the model
`M(1/10)` (also carried as data in that round's `CLAIMS-proposed.md`).

A *conduct* is examined only through its selection and the quantity that selection
realizes; a criterion is **extensional** when it is a predicate of exactly that pair. The
delegate's selection is induced by the principal's grade, the simulator's by the model's
grade of the principal, through one and the same tie-breaking maximizer `choice`.

**Read the easy results as easy.** Propositions 1 and 2 are one rewrite each. That is the
finding, not a shortcut: once a criterion sees only the selection, agreement of the two
induced choices settles every such criterion by substitution, and nothing further is
available. The source says the same thing at greater length. Proposition 7(b) is the one
statement here with content in its proof.

Provisional names (`AGENTS.md` §6): `inducedSelection`, `realizedQuantity`,
`ConstantOnCells`, `schemeDelegate`, `schemeSim`, and the theorem names below.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Workspace.Deference.Contrib.SubstitutionSeparation

open Finset

variable {Ω P : Type*}

/-- The selection a grade induces through the tie-breaking maximizer `choice`: `J` when
applied to the principal's grade `v⁺`, `Ĵ` when applied to the model's grade `v̂⁺`. -/
def inducedSelection (choice : (P → ℚ) → P) (g : Ω → P → ℚ) : Ω → P := fun ω => choice (g ω)

/-- The quantity a selection realizes, `ω ↦ X_{n,c(ω)}(ω)`. -/
def realizedQuantity (X : Ω → P → ℚ) (sel : Ω → P) : Ω → ℚ := fun ω => X ω (sel ω)

/-- Measurability at an information time, carried by the time's cell map: `f` is measurable
at `κ` when it is constant on `κ`'s cells. -/
def ConstantOnCells {α Cell : Type*} (κ : Ω → Cell) (f : Ω → α) : Prop :=
  ∀ ω ω', κ ω = κ ω' → f ω = f ω'

/-- A maximizer selector picks a maximizer. This is the only property of `choice` any
statement here uses; in particular no tie-break rule is fixed, so the results hold for
every tie-break. -/
def IsMaximizerSelector (choice : (P → ℚ) → P) : Prop :=
  ∀ (f : P → ℚ) (π : P), f π ≤ f (choice f)

/-- A strict maximum determines the selection whatever the tie-break. -/
theorem choice_eq_of_strictMax {choice : (P → ℚ) → P} (hchoice : IsMaximizerSelector choice)
    (f : P → ℚ) (π₀ : P) (h : ∀ π, π ≠ π₀ → f π < f π₀) :
    choice f = π₀ := by
  by_contra hne
  exact absurd (hchoice f π₀) (not_le.mpr (h (choice f) hne))

/-! ## Propositions 1 and 2 — the extensional register -/

/-- **Proposition 1.** Source: `prompts/2026-08-11-deference-channel/REPORT.md` §1.2.

Where the model's induced choice agrees with the principal's, the two conducts have equal
selections and equal quantities, so *every* extensional criterion admits both or neither.

The proof is a substitution of equals, and that is the content: an extensional criterion
has no access to anything else. `crit` is universally quantified, so the statement is about
all such criteria at once, not about a chosen one. -/
theorem extensional_admits_both (choice : (P → ℚ) → P) (v vh X : Ω → P → ℚ)
    (h : inducedSelection choice vh = inducedSelection choice v)
    (crit : (Ω → P) → (Ω → ℚ) → Prop) :
    crit (inducedSelection choice vh)
        (realizedQuantity X (inducedSelection choice vh))
      ↔ crit (inducedSelection choice v)
        (realizedQuantity X (inducedSelection choice v)) := by
  rw [h]

/-- **Proposition 2, first half.** Source: same report, §1.2. Restricted to the simulator
family, an extensional criterion is a predicate of the induced choice alone: two models
with the same induced choice are indistinguishable, however different their grades. -/
theorem sim_depends_only_on_inducedChoice (choice : (P → ℚ) → P) (vh₁ vh₂ X : Ω → P → ℚ)
    (h : inducedSelection choice vh₁ = inducedSelection choice vh₂)
    (crit : (Ω → P) → (Ω → ℚ) → Prop) :
    crit (inducedSelection choice vh₁)
        (realizedQuantity X (inducedSelection choice vh₁))
      ↔ crit (inducedSelection choice vh₂)
        (realizedQuantity X (inducedSelection choice vh₂)) := by
  rw [h]

/-- **Proposition 2, second half.** Source: same report, §1.2. An extensional criterion
separates the simulator from the delegate only at instances where the induced choices
differ — the contrapositive of Proposition 1. -/
theorem separation_requires_disagreement (choice : (P → ℚ) → P) (v vh X : Ω → P → ℚ)
    (crit : (Ω → P) → (Ω → ℚ) → Prop)
    (hsep : ¬ (crit (inducedSelection choice vh)
          (realizedQuantity X (inducedSelection choice vh))
        ↔ crit (inducedSelection choice v)
          (realizedQuantity X (inducedSelection choice v)))) :
    inducedSelection choice vh ≠ inducedSelection choice v :=
  fun h => hsep (extensional_admits_both choice v vh X h crit)

/-! ## Proposition 6 — the one structural extensional separator -/

/-- **Proposition 6, first half.** Source: same report, §1.2. The simulator's selection is
measurable at the decision time in *every* instance: it is a function of the model's grade,
which is. So the criterion "the selection is not decision-time measurable" excludes every
simulator. -/
theorem sim_selection_constantOnCells {Cell : Type*} (κ : Ω → Cell)
    (choice : (P → ℚ) → P) (vh : Ω → P → ℚ) (h : ConstantOnCells κ vh) :
    ConstantOnCells κ (inducedSelection choice vh) := by
  intro ω ω' hκ
  show choice (vh ω) = choice (vh ω')
  rw [h ω ω' hκ]

/-- **Proposition 6, second half.** Source: same report, §1.2. The criterion admits the
delegate and rejects the simulator exactly when the principal's induced choice is *not*
decision-time measurable — that is, exactly when the principal is unpredictable. Read as a
requirement it is backwards: it excludes delegation precisely in the predictable case. -/
theorem unpredictability_separates {Cell : Type*} (κ : Ω → Cell)
    (choice : (P → ℚ) → P) (v vh : Ω → P → ℚ) (h : ConstantOnCells κ vh) :
    (¬ ConstantOnCells κ (inducedSelection choice v)
        ∧ ConstantOnCells κ (inducedSelection choice vh))
      ↔ ¬ ConstantOnCells κ (inducedSelection choice v) :=
  ⟨fun hc => hc.1, fun hc => ⟨hc, sim_selection_constantOnCells κ choice vh h⟩⟩

/-! ## Proposition 7 — the variation register -/

/-- The delegate as a scheme: a map from the principal's grade to a selection. -/
def schemeDelegate (choice : (P → ℚ) → P) : (Ω → P → ℚ) → (Ω → P) := inducedSelection choice

/-- A fixed-model simulator as a scheme: it ignores the principal's grade entirely. -/
def schemeSim (choice : (P → ℚ) → P) (vh : Ω → P → ℚ) : (Ω → P → ℚ) → (Ω → P) :=
  fun _ => inducedSelection choice vh

/-- **Proposition 7(a), the easy half.** Source: same report, §1.3. A fixed-model simulator
is a constant scheme. True by construction — the scheme takes no argument — so the criterion
"the scheme is nonconstant" excludes it. That the delegate's scheme is *not* constant needs
an instance; see `M.schemeDelegate_not_constant`. -/
theorem schemeSim_constant (choice : (P → ℚ) → P) (vh : Ω → P → ℚ) :
    ∀ v v' : Ω → P → ℚ, schemeSim choice vh v = schemeSim choice vh v' :=
  fun _ _ => rfl

/-- **Proposition 7(b).** Source: same report, §1.3.

A well-timed faithful scheme exists exactly when the decision-time information is already
the settlement-time information. `hπ` supplies the two interventions the construction needs;
`hB` makes the constructed grade a nonzero member of the bounded family.

Left to right is the construction: where two states share a decision-time cell but not a
settlement-time cell, the grade that is `B` on `π₀` over one settlement cell and `B` on `π₁`
elsewhere is admissible and forces the principal's induced choice apart across the shared
decision-time cell. Right to left is immediate. -/
theorem faithful_wellTimed_iff {CT CF : Type*} [DecidableEq CF] [DecidableEq P]
    (choice : (P → ℚ) → P) (hchoice : IsMaximizerSelector choice)
    (κt : Ω → CT) (κF : Ω → CF) (B : ℚ) (hB : 0 < B) (π₀ π₁ : P) (hπ : π₀ ≠ π₁) :
    (∀ v : Ω → P → ℚ, ConstantOnCells κF v → (∀ ω π, |v ω π| ≤ B) →
        ConstantOnCells κt (inducedSelection choice v))
      ↔ ConstantOnCells κt κF := by
  constructor
  · intro h ω ω' hκt
    by_contra hne
    obtain ⟨w, hwF, hwB, hw0, hw1⟩ :
        ∃ w : Ω → P → ℚ, ConstantOnCells κF w ∧ (∀ x π, |w x π| ≤ B) ∧
          choice (w ω) = π₀ ∧ choice (w ω') = π₁ := by
      refine ⟨fun x π => if κF x = κF ω then (if π = π₀ then B else 0)
                          else (if π = π₁ then B else 0), ?_, ?_, ?_, ?_⟩
      · intro x y hxy
        funext π
        simp only [hxy]
      · intro x π
        dsimp only
        by_cases h1 : κF x = κF ω
        · rw [if_pos h1]
          by_cases h2 : π = π₀
          · rw [if_pos h2, abs_of_pos hB]
          · rw [if_neg h2, abs_zero]; exact le_of_lt hB
        · rw [if_neg h1]
          by_cases h2 : π = π₁
          · rw [if_pos h2, abs_of_pos hB]
          · rw [if_neg h2, abs_zero]; exact le_of_lt hB
      · refine choice_eq_of_strictMax hchoice _ _ fun π hp => ?_
        simpa [hp] using hB
      · refine choice_eq_of_strictMax hchoice _ _ fun π hp => ?_
        have hfalse : ¬ (κF ω' = κF ω) := fun hh => hne hh.symm
        simpa [hp, hfalse] using hB
    have hkey : choice (w ω) = choice (w ω') := h w hwF hwB ω ω' hκt
    rw [hw0, hw1] at hkey
    exact hπ hkey
  · intro hdet v hvF _ ω ω' hκt
    show choice (v ω) = choice (v ω')
    rw [hvF ω ω' (hdet ω ω' hκt)]

/-! ## `M(1/10)` — the inhabitation witness

Source: `prompts/2026-08-11-deference-channel/REPORT.md` §1.1. Three states,
`Π_n = {π₀ < π₁}`, `B = 1`, credence `(1/2, 2/5, 1/10)`, quantity `X = v⁺` (grade/report
settlement, the case most favourable to delegation). The model is exact off `ω₂` and wrong
there, and is constant on `{ω₁, ω₂}` — so it is decision-time measurable under the coarse
reading of `𝓕_0` *and* under the fine one, which is what the third state is spent on.

The witness is checked to be the source's instance: the two valuations are `11/20` and
`7/20`, gap `1/5`, and the per-state loss at the critical event is the maximal `2B = 2`.
-/

namespace M

/-- The least maximizer on a two-element menu: the tie-break the source declares. -/
def choice : (Fin 2 → ℚ) → Fin 2 := fun f => if f 1 ≤ f 0 then 0 else 1

theorem choice_isMaximizerSelector : IsMaximizerSelector choice := by
  intro f π
  simp only [choice]
  split <;> (rename_i h; fin_cases π <;> simp_all <;> linarith)

def p : Fin 3 → ℚ := ![1/2, 2/5, 1/10]
def v : Fin 3 → Fin 2 → ℚ := ![![1/2, 0], ![0, 1/2], ![1, -1]]
def vh : Fin 3 → Fin 2 → ℚ := ![![1/2, 0], ![0, 1/2], ![0, 1/2]]
/-- The model made accurate at the critical cell — the source's §3 perturbation table,
first row. It has the same induced choice as the principal everywhere. -/
def vhAccurate : Fin 3 → Fin 2 → ℚ := ![![1/2, 0], ![0, 1/2], ![1, 1/2]]
/-- The coarse reading of `𝓕_0`: the principal holds information the agent lacks. -/
def kt : Fin 3 → Fin 2 := ![0, 1, 1]

theorem delegateSel : inducedSelection choice v = ![0, 1, 0] := by
  funext ω; fin_cases ω <;> norm_num [inducedSelection, choice, v]

theorem simSel : inducedSelection choice vh = ![0, 1, 1] := by
  funext ω; fin_cases ω <;> norm_num [inducedSelection, choice, vh]

theorem accurateSel : inducedSelection choice vhAccurate = inducedSelection choice v := by
  funext ω; fin_cases ω <;> norm_num [inducedSelection, choice, v, vhAccurate]

/-- The model is decision-time measurable under the coarse reading, so Proposition 6
applies to it. -/
theorem vh_constantOnCells : ConstantOnCells kt vh := by
  intro ω ω' h
  fin_cases ω <;> fin_cases ω' <;> first | rfl | (exfalso; revert h; decide)

/-- The principal's induced choice is *not* decision-time measurable here: `ω₁` and `ω₂`
share a cell and the principal chooses differently. So the Proposition 6 criterion
separates under the coarse reading. -/
theorem delegate_not_constantOnCells : ¬ ConstantOnCells kt (inducedSelection choice v) := by
  intro h
  have := h 1 2 (by decide)
  rw [delegateSel] at this
  exact absurd this (by decide)

/-- Proposition 6's separation clause is inhabited. -/
theorem unpredictability_separates_nonvacuous :
    ¬ ConstantOnCells kt (inducedSelection choice v)
      ∧ ConstantOnCells kt (inducedSelection choice vh) :=
  (unpredictability_separates kt choice v vh vh_constantOnCells).mpr
    delegate_not_constantOnCells

/-- Proposition 1's hypothesis package is inhabited by the accurate model: the induced
choices agree, so no extensional criterion separates the simulator from the delegate
there. -/
theorem extensional_admits_both_nonvacuous (crit : (Fin 3 → Fin 2) → (Fin 3 → ℚ) → Prop) :
    crit (inducedSelection choice vhAccurate)
        (realizedQuantity v (inducedSelection choice vhAccurate))
      ↔ crit (inducedSelection choice v)
        (realizedQuantity v (inducedSelection choice v)) :=
  extensional_admits_both choice v vhAccurate v accurateSel crit

/-- Proposition 7(a)'s missing half, by construction: the delegate's scheme is not
constant. `v` and `vhAccurate` are two admissible principals, and the scheme's values
differ at `ω₂`. -/
theorem schemeDelegate_not_constant :
    ¬ (∀ g g' : Fin 3 → Fin 2 → ℚ, schemeDelegate choice g = schemeDelegate choice g') := by
  intro h
  have hcon : inducedSelection choice v = inducedSelection choice vh := h v vh
  rw [delegateSel, simSel] at hcon
  exact absurd (congrFun hcon 2) (by decide)

/-- Proposition 7(b) at the witness, left-to-right: no well-timed faithful scheme exists
under the coarse reading, since `ω₁` and `ω₂` share a decision-time cell but not a
settlement-time one (`κ_F` is the discrete map `id`). -/
theorem no_wellTimed_faithful_scheme :
    ¬ (∀ g : Fin 3 → Fin 2 → ℚ, ConstantOnCells (id : Fin 3 → Fin 3) g →
        (∀ ω π, |g ω π| ≤ 1) → ConstantOnCells kt (inducedSelection choice g)) := by
  intro h
  have hdet := (faithful_wellTimed_iff choice choice_isMaximizerSelector kt
    (id : Fin 3 → Fin 3) 1 (by norm_num) (0 : Fin 2) 1 (by decide)).mp h
  exact absurd (hdet 1 2 (by decide)) (by decide)

/-! ### The valuations of the source's §1.1 -/

def valuation (sel : Fin 3 → Fin 2) : ℚ := ∑ ω, p ω * v ω (sel ω)

theorem valuation_delegate : valuation (inducedSelection choice v) = 11/20 := by
  rw [delegateSel]; norm_num [valuation, p, v, Fin.sum_univ_succ]

theorem valuation_sim : valuation (inducedSelection choice vh) = 7/20 := by
  rw [simSel]; norm_num [valuation, p, v, Fin.sum_univ_succ]

/-- The per-state loss at the critical event is the maximal `2B = 2` the carriers allow, at
this and at every `p`. -/
theorem critical_loss : v 2 0 - v 2 1 = 2 := by
  show (1 : ℚ) - (-1) = 2
  norm_num

end M

#print axioms choice_eq_of_strictMax
#print axioms extensional_admits_both
#print axioms sim_depends_only_on_inducedChoice
#print axioms separation_requires_disagreement
#print axioms sim_selection_constantOnCells
#print axioms unpredictability_separates
#print axioms schemeSim_constant
#print axioms faithful_wellTimed_iff
#print axioms M.choice_isMaximizerSelector
#print axioms M.delegateSel
#print axioms M.simSel
#print axioms M.accurateSel
#print axioms M.vh_constantOnCells
#print axioms M.delegate_not_constantOnCells
#print axioms M.unpredictability_separates_nonvacuous
#print axioms M.extensional_admits_both_nonvacuous
#print axioms M.schemeDelegate_not_constant
#print axioms M.no_wellTimed_faithful_scheme
#print axioms M.valuation_delegate
#print axioms M.valuation_sim
#print axioms M.critical_loss

end Workspace.Deference.Contrib.SubstitutionSeparation
