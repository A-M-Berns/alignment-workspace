import Cleanroom.Udt.UdtEndorsePolicy.Generalize
import Mathlib.Tactic.FinCases

/-!
# Audit r2 (adversarial) probe: udt-rep-2-016's *own* rendering of "updateful" is always endorsed

udt-rep-2-016 (the inventory item behind T5 and F-8) types the utility as `U : Ω × A → ℝ` and
renders the updateful choice as Bayesian conditioning, `C_updateful(o) := argmax_a
E_{P₁(· | O = o)}[U(ω, a)]`, then says "'updateful ⟹ not endorsed' is false in general and true
exactly under cross-situation dependence". The package (following the mandate) formalized the
lab's *kernel* rendering instead and finds the sentence ill-posed there (F-8). Checked here: under
the inventory's own typing the half is false for **every** `U` — a Bayesian-updateful choice,
being measurable in `O`, is conditionally control-endorsed given `O` on each cell and hence
control-endorsed (`controlEndorses_of_condControlEndorses`). "Cross-situation dependence" is not
even expressible with `U : Ω × A → ℝ`: the inventory's "the payoff depends on `f` at other
observations" contradicts its own type, which is why a policy-dependent utility (the kernel
rendering, or `udt-policy-calc`'s `U : Policy S A → ℝ`) is needed to state the claim at all.
Bonus: the construction gives the `CondControlEndorses` inhabitant the ledger's Defs row says the
package lacks (`knowsMoreU` with `O = id`, `Cupd = id`). Not imported by the library.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy.AuditR2

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

variable {Ω T A : Type} [Fintype Ω] [DecidableEq T] [DecidableEq A]

/-- udt-rep-2-016's updateful choice: at each observation value `o` of positive mass, `Cupd o` is
a (set-valued) Bayesian argmax of `a' ↦ E[U(·, a') | O = o]`, written division-free. -/
def BayesUpdateful (w : Ω → ℝ) (U : Ω → A → ℝ) (O : Ω → T) (Cupd : T → A) : Prop :=
  ∀ o, 0 < mass w (cls O o) → IsArgmax (fun a' => wsum w (fun ω => U ω a') (cls O o)) (Cupd o)

/-- A Bayesian-updateful choice is conditionally control-endorsed given its own observation: on a
positive pair-class `{O = x, Cupd ∘ O = y}` we have `y = Cupd x` and the class is the cell `{O = x}`. -/
theorem bayesUpdateful_condControlEndorses {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {U : Ω → A → ℝ}
    {O : Ω → T} {Cupd : T → A} (h : BayesUpdateful w U O Cupd) :
    CondControlEndorses w U O (fun ω => Cupd (O ω)) := by
  intro x y hxy
  obtain ⟨ω, hωE, _⟩ := exists_pos_of_mass_pos hw hxy
  have hω : O ω = x ∧ Cupd (O ω) = y := by simpa using hωE
  have hy : y = Cupd x := by rw [← hω.2, hω.1]
  subst hy
  have hcls : cls2 O x (fun ω => Cupd (O ω)) (Cupd x) = cls O x := by
    ext ω'
    simp only [cls2, cls, mem_event, and_iff_left_iff_imp]
    intro h'
    rw [h']
  rw [hcls] at hxy ⊢
  exact h x hxy

/-- **Under udt-rep-2-016's own typing, every Bayesian-updateful choice is control-endorsed** —
so "updateful ⟹ not endorsed" is false for every `U : Ω → A → ℝ`, and the inventory's "true exactly
under cross-situation dependence" cannot be stated with that type. -/
theorem bayesUpdateful_controlEndorsed {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {U : Ω → A → ℝ}
    {O : Ω → T} {Cupd : T → A} (h : BayesUpdateful w U O Cupd) :
    ControlEndorses w U (fun ω => Cupd (O ω)) :=
  controlEndorses_of_condControlEndorses hw (bayesUpdateful_condControlEndorses hw h)

/-- `id` is the Bayesian-updateful choice for `knowsMoreU` when the observation is the world. -/
theorem knowsMore_bayesUpdateful : BayesUpdateful unif2w knowsMoreU id id := by
  intro o _ a'
  fin_cases o <;> fin_cases a' <;>
  · simp only [wsum_event_eq, Fin.sum_univ_two, knowsMoreU, unif2w, id, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    norm_num

/-- **A concrete inhabitant of `CondControlEndorses`** (the ledger's Defs row says the package has
none): `knowsMoreU`, observation `id`, choice `id`. -/
theorem condControlEndorses_knowsMore : CondControlEndorses unif2w knowsMoreU id id :=
  bayesUpdateful_condControlEndorses (fun _ => by norm_num [unif2w]) knowsMore_bayesUpdateful

end

end Cleanroom.Udt.UdtEndorsePolicy.AuditR2

#print axioms Cleanroom.Udt.UdtEndorsePolicy.AuditR2.bayesUpdateful_controlEndorsed
#print axioms Cleanroom.Udt.UdtEndorsePolicy.AuditR2.condControlEndorses_knowsMore
