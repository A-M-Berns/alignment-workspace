import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Estimators, sequential unbiasedness, double indifference (D-5, T14, S7, S8)

Armstrong's "Double indifference is better indifference" (2016): probability estimators `ρ_i`,
the expectation estimators `E_{ρ_i}`, sequential unbiasedness `E_{ρ_i} E_{ρ_j} X = E_{ρ_i} X`
(`i < j`), the compensatory reward `C(ρ') = E_{ρ'}(Y) − E_{ρ'}(Z)` of the one-change model and
the second-layer term `D_t`. Here an estimator is a kernel `W → Distr W` (the agent's beliefs at
each state), `E_ρ X : W → ℝ` is a *function of the state* (the mandate's trap: never a number
until a state is fixed), and the conditioning kernels of one prior `P` along a coarse-to-fine
chain of partitions are the objects for which sequential unbiasedness is a *theorem* (the tower
property, proved here unconditionally with FAF's junk convention at mass-0 classes).

Source: [[corr-refs-inventory]] 016 (armstrong-2016-double-indifference l. 20–86);
[[corr-core-inventory]] 022, 023, 024; [[corr-wf13-2-inventory]] 2-012;
[[corr-wf13-inventory]] 046 (armstrong.md I5.3, I6.2).
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Estimators

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## Estimators and their expectation operators -/

/-- **The expectation estimator of a kernel:** `E_ρ X (w) := E_{ρ w}[X]`, a function of the state.
Source: [[corr-refs-inventory]] 016 / armstrong-2016 "Probability estimators"
Kind: D
Fidelity: exact -/
noncomputable def E (ρ : W → Distr W) (X : W → ℝ) : W → ℝ := fun w => expect (ρ w) X

/-- `E_ρ` is linear: differences. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma E_sub (ρ : W → Distr W) (X Y : W → ℝ) : E ρ (X - Y) = E ρ X - E ρ Y := by
  funext w; simp only [E, Pi.sub_apply]; exact expect_sub _ _ _

/-- `E_ρ` is linear: sums. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma E_add (ρ : W → Distr W) (X Y : W → ℝ) : E ρ (X + Y) = E ρ X + E ρ Y := by
  funext w; simp only [E, Pi.add_apply]; exact expect_add _ _ _

/-- `E_ρ` of a constant. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma E_const (ρ : W → Distr W) (k : ℝ) : E ρ (fun _ => k) = fun _ => k := by
  funext w; simp only [E]; exact expect_const _ _

/-- **Sequential unbiasedness of `ρ_i` toward `ρ_j`:** `E_{ρ_i} (E_{ρ_j} X) = E_{ρ_i} X` for every
`X` — Armstrong's definition for one pair, as an equality of *functions of the state*.
Source: [[corr-refs-inventory]] 016 / armstrong-2016 "Sequentially unbiased estimators";
[[corr-core-inventory]] 023
Kind: D
Fidelity: exact -/
def SeqUnbiased (ρi ρj : W → Distr W) : Prop := ∀ X : W → ℝ, E ρi (E ρj X) = E ρi X

/-- **D-5. A sequentially unbiased chain:** `SeqUnbiased (ρ i) (ρ j)` for all `i < j`.
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("for all `i < j` and all `X`")
Kind: D
Fidelity: exact -/
def SeqUnbiasedChain {ι : Type*} [Preorder ι] (ρ : ι → W → Distr W) : Prop :=
  ∀ i j, i < j → SeqUnbiased (ρ i) (ρ j)

/-! ## Partitions as label maps; the conditioning kernels of one prior -/

section Partition

variable {C C' : Type*} [DecidableEq C] [DecidableEq C']

/-- The class of `w` under the partition labelled by `π`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def cls (π : W → C) (w : W) : Finset W := univ.filter (fun w' => π w' = π w)

/-- Membership in a class. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma mem_cls (π : W → C) (w w' : W) : w' ∈ cls π w ↔ π w' = π w := by simp [cls]

/-- A point is in its own class. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma self_mem_cls (π : W → C) (w : W) : w ∈ cls π w := by simp

/-- Classes of two points in one class coincide. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cls_eq_of_mem (π : W → C) {w w' : W} (h : w' ∈ cls π w) : cls π w' = cls π w := by
  ext x; simp only [mem_cls] at h ⊢; rw [h]

/-- The mass of the class of `w` under `P`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def classMass (P : Distr W) (π : W → C) (w : W) : ℝ := ∑ w' ∈ cls π w, P.mass w'

/-- Class masses are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma classMass_nonneg (P : Distr W) (π : W → C) (w : W) : 0 ≤ classMass P π w :=
  sum_nonneg fun w' _ => P.nonneg w'

/-- A point whose class has mass `0` has mass `0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mass_eq_zero_of_classMass_eq_zero (P : Distr W) (π : W → C) {w : W}
    (h : classMass P π w = 0) : P.mass w = 0 := by
  unfold classMass at h
  rw [sum_eq_zero_iff_of_nonneg (fun w' _ => P.nonneg w')] at h
  exact h w (self_mem_cls π w)

/-- Class masses are constant on a class. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma classMass_eq_of_mem (P : Distr W) (π : W → C) {w w' : W} (h : w' ∈ cls π w) :
    classMass P π w' = classMass P π w := by
  unfold classMass; rw [cls_eq_of_mem π h]

/-- **The conditional expectation of `X` given the partition `π`, under `P`**, as a function of
the state: `E_P[X | π](w) = (∑_{w' ∈ [w]} P(w') X(w')) / P([w])`. Junk `0` at a class of mass `0`
(disclosed; every lemma below is junk-safe because such a class has no mass to weight it).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 (the `E_{ρ_i}` of a conditioning kernel)
Kind: D
Fidelity: exact (division convention disclosed) -/
noncomputable def condExp (P : Distr W) (π : W → C) (X : W → ℝ) (w : W) : ℝ :=
  (∑ w' ∈ cls π w, P.mass w' * X w') / classMass P π w

/-- `condExp` is constant on a class. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condExp_eq_of_mem (P : Distr W) (π : W → C) (X : W → ℝ) {w w' : W} (h : w' ∈ cls π w) :
    condExp P π X w' = condExp P π X w := by
  unfold condExp; rw [cls_eq_of_mem π h, classMass_eq_of_mem P π h]

/-- **The conditioning kernel of `P` along `π`** as a FAF `Distr` at each state (requires every
class to have positive mass — the mandate's D-5 "mass-0 classes excluded by hypothesis"; the
function `condExp` needs no such hypothesis).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("probability estimators")
Kind: D
Fidelity: exact -/
noncomputable def condKernel (P : Distr W) (π : W → C) (hpos : ∀ w, 0 < classMass P π w) :
    W → Distr W := fun w =>
  { mass := fun w' => if π w' = π w then P.mass w' / classMass P π w else 0
    nonneg := fun w' => by
      split_ifs
      · exact div_nonneg (P.nonneg w') (classMass_nonneg P π w)
      · exact le_rfl
    sum_eq_one := by
      rw [← sum_filter, ← sum_div]
      exact div_self (ne_of_gt (hpos w)) }

/-- The expectation estimator of the conditioning kernel is `condExp`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma E_condKernel (P : Distr W) (π : W → C) (hpos : ∀ w, 0 < classMass P π w) (X : W → ℝ) :
    E (condKernel P π hpos) X = condExp P π X := by
  funext w
  simp only [E, Found.CorrThreeStep.expect, condKernel, condExp, ite_mul, zero_mul]
  rw [← sum_filter, sum_div]
  exact sum_congr rfl fun w' _ => by rw [div_mul_eq_mul_div]

/-- **`π'` refines `π`:** points in one `π'`-class are in one `π`-class (coarse-to-fine).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("labelled sequentially")
Kind: D
Fidelity: exact -/
def Refines (π' : W → C') (π : W → C) : Prop := ∀ w w', π' w = π' w' → π w = π w'

/-- Every partition refines itself. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Refines.rfl (π : W → C) : Refines π π := fun _ _ h => h

/-- **T14(a): the tower property — sequential unbiasedness is a theorem for conditioning kernels.**
If `π'` refines `π` then `E_P[E_P[X | π'] | π] = E_P[X | π]`, as functions of the state, for every
`X`, with no positivity hypothesis (a class of mass `0` contributes `0` to both sides).
Source: [[corr-wf13-2-inventory]] 2-012 / armstrong-2016 "Sequentially unbiased estimators"
Kind: P
Fidelity: stronger (junk-safe; no mass-0 exclusion)
Hyps: (a) -/
theorem condExp_condExp (P : Distr W) {π : W → C} {π' : W → C'} (h : Refines π' π) (X : W → ℝ) :
    condExp P π (condExp P π' X) = condExp P π X := by
  funext w
  unfold condExp
  congr 1
  have step1 : ∀ w', P.mass w' * ((∑ w'' ∈ cls π' w', P.mass w'' * X w'') / classMass P π' w') =
      ∑ w'' ∈ cls π' w', P.mass w' * (P.mass w'' * X w'' / classMass P π' w') := by
    intro w'; rw [sum_div, mul_sum]
  rw [sum_congr rfl (fun w' _ => step1 w')]
  rw [sum_comm' (s := cls π w) (t := fun w' => cls π' w') (t' := cls π w)
    (s' := fun w'' => cls π' w'') ?_]
  · apply sum_congr rfl
    intro w'' _
    rw [sum_congr rfl (fun w' hw' => by rw [classMass_eq_of_mem P π' hw'])]
    rw [← sum_mul]
    by_cases hC : classMass P π' w'' = 0
    · rw [mass_eq_zero_of_classMass_eq_zero P π' hC]
      simp
    · unfold classMass at hC ⊢
      field_simp
  · intro w' w''
    simp only [mem_cls]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.symm, (h w'' w' h2).trans h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(h w' w'' h1).trans h2, h1.symm⟩

/-- **Sequential unbiasedness of the conditioning kernels along a refinement** (T14(a) in the
kernel form of D-5).
Source: [[corr-wf13-2-inventory]] 2-012 / armstrong-2016
Kind: C
Fidelity: exact
Hyps: (a) positivity is the kernels' existence condition -/
theorem seqUnbiased_condKernel (P : Distr W) {π : W → C} {π' : W → C'} (h : Refines π' π)
    (hpos : ∀ w, 0 < classMass P π w) (hpos' : ∀ w, 0 < classMass P π' w) :
    SeqUnbiased (condKernel P π hpos) (condKernel P π' hpos') := by
  intro X
  rw [E_condKernel, E_condKernel, E_condKernel, condExp_condExp P h]

end Partition

/-! ## T14(b)–(c). The compensatory reward and the `D`-term (one change) -/

/-- **The compensatory reward of the one-change model as a random variable:**
`C(ρ')(w) := E_{ρ' w}(Y) − E_{ρ' w}(Z)`, with `Y` the value of `u` under the stay-policy and `Z`
that of `v` under the switch-policy. (c): the transition is an independent coin, so the source's
conditionals `E_{ρ'}(u | u → u)`, `E_{ρ'}(v | u → v)` are the unconditional expectations of `Y`, `Z`
(`armstrong.md` I5.3's reduction).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 "Hacking utility indifference";
[[corr-wf13-inventory]] 046 / armstrong.md I5.3
Kind: D
Fidelity: variant: the causal-counterfactual reduction (c) disclosed -/
noncomputable def comp (ρ' : W → Distr W) (Y Z : W → ℝ) : W → ℝ := fun w => E ρ' Y w - E ρ' Z w

/-- `C(ρ') = E_{ρ'}(Y − Z)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma comp_eq (ρ' : W → Distr W) (Y Z : W → ℝ) : comp ρ' Y Z = E ρ' (Y - Z) := by
  rw [E_sub]; rfl

/-- **The single-indifference value of choosing `ρ'` at current beliefs `μ`:** the agent is paid
`C(ρ')` in the future, which it values now at `E_μ[C(ρ')]`. The `E`-channel incentive
(corr-core-022) is that this depends on `ρ'`.
Source: [[corr-core-inventory]] 022 / armstrong-2016 ("it has incentives to change `E` to `E'`")
Kind: D
Fidelity: exact -/
noncomputable def compValue (μ : Distr W) (ρ' : W → Distr W) (Y Z : W → ℝ) : ℝ :=
  expect μ (comp ρ' Y Z)

/-- **The second-layer term `D_t` at current beliefs `μ`, one change:**
`D := −(E_μ[C(ρ_j)] − c_i)` with `c_i := E_μ(Y) − E_μ(Z)` the same quantity as the current
estimator computes it (`armstrong.md` I5.3's form; the post's `E_{ρ_i}(C_{>t}(ρ_i))` with the
current estimate a number at the current state).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 "Double indifference" (`D_t`, one change);
armstrong.md I5.3
Kind: D
Fidelity: exact (one change; the `n`-change recursion is S7) -/
noncomputable def Dterm (μ : Distr W) (ρj : W → Distr W) (Y Z : W → ℝ) : ℝ :=
  -(compValue μ ρj Y Z - (expect μ Y - expect μ Z))

/-- **Double indifference closes the channel by construction:** `E_μ[C(ρ')] + D(ρ') = c_i` for
every candidate `ρ'` — the agent's compensation-plus-correction is the same number whatever
estimator it adopts (linearity; this is what the `D`-term is *for*).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("indifferent to all actual compensatory
rewards"); armstrong.md I6.1 ("totals tie")
Kind: L
Fidelity: exact -/
theorem compValue_add_Dterm (μ : Distr W) (ρ' : W → Distr W) (Y Z : W → ℝ) :
    compValue μ ρ' Y Z + Dterm μ ρ' Y Z = expect μ Y - expect μ Z := by
  unfold Dterm; ring

/-- **`D = 0` iff sequential unbiasedness holds for `Y − Z` at this state.**
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("So `D_t = 0`")
Kind: L
Fidelity: exact -/
theorem Dterm_eq_zero_iff (μ : Distr W) (ρj : W → Distr W) (Y Z : W → ℝ) :
    Dterm μ ρj Y Z = 0 ↔ expect μ (E ρj (Y - Z)) = expect μ (Y - Z) := by
  unfold Dterm compValue
  have hYZ : Found.CorrThreeStep.expect μ (Y - Z) =
      Found.CorrThreeStep.expect μ Y - Found.CorrThreeStep.expect μ Z := by
    unfold Found.CorrThreeStep.expect; simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
  rw [comp_eq, hYZ]
  constructor <;> intro h <;> linarith

/-- **T14(c): `D_t = 0` in one step whenever `ρ_j` is sequentially unbiased from the current
kernel at the current state** — the post's main result, at one change, from the definition: one
evaluation of the SU hypothesis at the single variable `Y − Z` and the single state `w` (graded
L; the composition is `Dterm_condKernel_eq_zero`).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("if it does change `ρ_i → ρ_j`, … `D_t = 0`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem Dterm_eq_zero_of_seqUnbiased {ρi ρj : W → Distr W} (h : SeqUnbiased ρi ρj)
    (Y Z : W → ℝ) (w : W) : Dterm (ρi w) ρj Y Z = 0 := by
  rw [Dterm_eq_zero_iff]
  have := congrFun (h (Y - Z)) w
  simpa [E] using this

/-- **T14(c) for conditioning kernels:** along a refinement of one prior, the `D`-term vanishes
at every state — sequential unbiasedness is derived (the tower), not assumed.
Source: [[corr-refs-inventory]] 016 / armstrong-2016; [[corr-wf13-2-inventory]] 2-012
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem Dterm_condKernel_eq_zero {C C' : Type*} [DecidableEq C] [DecidableEq C'] (P : Distr W)
    {π : W → C} {π' : W → C'} (h : Refines π' π) (hpos : ∀ w, 0 < classMass P π w)
    (hpos' : ∀ w, 0 < classMass P π' w) (Y Z : W → ℝ) (w : W) :
    Dterm (condKernel P π hpos w) (condKernel P π' hpos') Y Z = 0 :=
  Dterm_eq_zero_of_seqUnbiased (seqUnbiased_condKernel P h hpos hpos') Y Z w

end Cleanroom.Corrigibility.CorrIndifference.Estimators
