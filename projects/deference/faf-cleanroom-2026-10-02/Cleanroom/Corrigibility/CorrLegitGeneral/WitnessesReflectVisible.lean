import Cleanroom.Corrigibility.CorrLegitGeneral.Reflection
import Cleanroom.Corrigibility.CorrLegitGeneral.Eval

/-!
# corr-legit-general — T2(a) local: a visible-modesty witness on three worlds

`legitReflectsWrt_unsat_of_visible` (`Reflection.lean`) says: a modest legitimate candidate
whose self-cell is a partial answer to `Q` breaks `L`-conditioned local Reflection. Its ledger
row had no witness through repair round 2 (audit r3 adversarial N2); here is one with a genuinely
coarser question (`Q ≠ id`, two cells of positive mass) and a nontrivial legitimacy event.

`W = Fin 3`, rows `P₀ = P₁ = (1/2, 1/4, 1/4)`, `P₂ = δ₂`, uniform `π`, `Q = questionOf {0, 1}`,
`L = {0, 2}`: the self-cell of world `0` is `{0, 1} = answer Q {true}`, and `P₀({0, 1}) = 3/4 < 1`,
so world `0` is modest with its modesty visible on `Q`; `0 ∈ L`, `π 0 = 1/3 > 0`. The same
instance inhabits the null-world form `legitReflectsWrt_unsat_of_visible_ae` (exact equality is
its special case; `rv3_not_legitReflectsWrt_ae`).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSimpArgs false

/-- The three-world frame: rows `(1/2, 1/4, 1/4)` at worlds `0, 1` and `δ₂` at world `2`.
Source: audit r3 adversarial N2 (the suggested instance); this package (T2(a), local form)
Kind: D
Fidelity: n/a -/
def rv3 : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 4, 1 / 4] ![1 / 2, 1 / 4, 1 / 4] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The uniform deferrer on three worlds.
Source: audit r3 adversarial N2
Kind: D
Fidelity: n/a -/
def πrv : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- The two-cell question's proposition `{0, 1}`.
Source: audit r3 adversarial N2
Kind: D
Fidelity: n/a -/
abbrev qrv : Finset (Fin 3) := {0, 1}

/-- The legitimacy event `{0, 2}` (nontrivial, containing the modest world `0`).
Source: audit r3 adversarial N2
Kind: D
Fidelity: n/a -/
abbrev Lrv : Finset (Fin 3) := {0, 2}

/-- `rv3`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rv3_P : rv3.P 0 = ![1 / 2, 1 / 4, 1 / 4] ∧ rv3.P 1 = ![1 / 2, 1 / 4, 1 / 4] ∧
    rv3.P 2 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

/-- The deferrer is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πrv_nonneg : ∀ w, 0 ≤ πrv w := by
  intro w; fin_cases w <;> norm_num [πrv, vec3_two]

/-- World `0`'s self-cell is `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rv3_cell : rv3.cell (rv3.P 0) = {0, 1} := by
  obtain ⟨h0, h1, h2⟩ := rv3_P
  ext w
  fin_cases w <;> simp [Frame.cell, h0, h1, h2]

/-- The self-cell is the partial answer `answer Q {true}` of the two-cell question.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rv3_cell_eq_answer : rv3.cell (rv3.P 0) = answer (questionOf qrv) {true} := by
  rw [rv3_cell, answer_questionOf_true]

/-- World `0` is modest: `P₀({0, 1}) = 3/4 < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rv3_modestAt_zero : rv3.ModestAt 0 := by
  obtain ⟨h0, _, _⟩ := rv3_P
  unfold Frame.ModestAt Frame.selfMass
  rw [rv3_cell, h0]
  simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num

/-- **`L`-conditioned local Reflection fails** on `rv3` at `Q = questionOf {0, 1}`,
`L = {0, 2}`, through `legitReflectsWrt_unsat_of_visible`.
Source: [[legitimacy]] R2.1 l. 56 (local reading); audit r3 adversarial N2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem rv3_not_legitReflectsWrt : ¬ LegitReflectsWrt (questionOf qrv) πrv rv3 Lrv :=
  legitReflectsWrt_unsat_of_visible πrv_nonneg (by simp) (by norm_num [πrv])
    rv3_modestAt_zero rv3_cell_eq_answer

/-- The same instance through the null-world form `legitReflectsWrt_unsat_of_visible_ae`
(exact equality of the cell and the answer is its special case).
Source: [[legitimacy]] R2.1 l. 56 (local reading); audit r1 adversarial N10; audit r3
adversarial N2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem rv3_not_legitReflectsWrt_ae : ¬ LegitReflectsWrt (questionOf qrv) πrv rv3 Lrv :=
  legitReflectsWrt_unsat_of_visible_ae πrv_nonneg (by simp) (by norm_num [πrv])
    rv3_modestAt_zero (by rw [rv3_cell_eq_answer, inter_self])
    (by rw [← rv3_cell_eq_answer]; exact le_of_eq rfl)

/-- **Packaged witness** for the visible-modesty rows: the deferrer is nonnegative, the modest
world is legitimate with positive mass, its self-cell is the partial answer `answer Q {true}`,
both cells of `Q` have positive mass, the legitimacy event has positive mass, and
`L`-conditioned local Reflection fails.
Source: [[legitimacy]] R2.1 l. 56 (local reading); audit r3 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem rv3_visible_witness :
    (∀ w, 0 ≤ πrv w) ∧ (0 : Fin 3) ∈ Lrv ∧ 0 < πrv 0 ∧ rv3.ModestAt 0 ∧
      rv3.cell (rv3.P 0) = answer (questionOf qrv) {true} ∧
      0 < mass πrv qrv ∧ 0 < mass πrv qrvᶜ ∧ 0 < mass πrv Lrv ∧
      ¬ LegitReflectsWrt (questionOf qrv) πrv rv3 Lrv := by
  refine ⟨πrv_nonneg, by simp, by norm_num [πrv], rv3_modestAt_zero, rv3_cell_eq_answer, ?_, ?_,
    ?_, rv3_not_legitReflectsWrt⟩ <;>
    (simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, πrv, vec3_two] <;> norm_num)

end

end Cleanroom.Corrigibility.CorrLegitGeneral
