import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic

/-!
# T16: Good's theorem on a finite partition, with strictness

Over a FAF `Distr W`, a finite nonempty menu `A`, payoffs `V : A → W → ℝ` and evidence
`kOf : W → K` (a finite partition of `W` by its fibres):

* `cellSum P V kOf k b = ∑_{w : kOf w = k} P(w) V(b, w)` — the `k`-weighted value of `b`;
* `partValue P V kOf = ∑_k max_b cellSum k b` — the value of deciding after seeing the cell;
* `priorBest P V = max_b E_P[V(b)]` — the value of deciding on the prior.

**Good's theorem** (`priorBest_le_partValue`): information never hurts. **Monotone under
coarsening** (`partValue_mono_coarsen`): `kOf = g ∘ kOf'` gives `partValue kOf ≤ partValue kOf'`.
**Strictness** (`priorBest_lt_partValue`): if some cell strictly beats every prior-optimal
action, the value of information is positive. The parent's `voiButton_nonneg` is the case
`K = Obs` on the joint `Ω × Obs` (`voiButton_eq_partValue_sub`, `voiButton_nonneg_of_partition`),
re-derived to show the bridge.

Two-option specialisation (`partValue2`, used by T9): with `A = TwoAct`, `V cont = X`,
`V stop = 0`, `partValue2 P X kOf = ∑_k max (cellSum X k) 0`.

Sources: `corrigibility-discussion-outline.md` l. 58 (corr-core-007); `miri.md` I10, Prop. 13.3.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

section Partition

variable {W K A : Type*} [Fintype W] [Fintype K] [DecidableEq K] [Fintype A] [Nonempty A]

/-- The `k`-cell of the partition induced by `kOf`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def cell (kOf : W → K) (k : K) : Finset W := univ.filter (kOf · = k)

/-- `cellSum P V kOf k b = ∑_{w ∈ cell k} P(w) V(b, w)`: the cell-weighted value of action `b`
(product form: the conditional expectation times the cell mass).
Source: [[corr-core-inventory]] 007 / corrigibility-discussion-outline.md l. 58 (Good's theorem); miri.md Prop. 13.3
Kind: D
Fidelity: exact -/
noncomputable def cellSum (P : Distr W) (V : A → W → ℝ) (kOf : W → K) (k : K) (b : A) : ℝ :=
  ∑ w ∈ cell kOf k, P.mass w * V b w

/-- `partValue P V kOf = ∑_k max_b cellSum k b`: the value of the decision problem when the
cell of `kOf` is observed before acting.
Source: [[corr-core-inventory]] 007 / corrigibility-discussion-outline.md l. 58; miri.md Prop. 13.3 ("the two-option decision value of a partition")
Kind: D
Fidelity: exact -/
noncomputable def partValue (P : Distr W) (V : A → W → ℝ) (kOf : W → K) : ℝ :=
  ∑ k, univ.sup' univ_nonempty (fun b => cellSum P V kOf k b)

/-- `priorBest P V = max_b E_P[V(b)]`: the value of acting on the prior.
Source: [[corr-core-inventory]] 007. Kind: D. Fidelity: exact -/
noncomputable def priorBest (P : Distr W) (V : A → W → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun b => expect P (V b))

variable (P : Distr W) (V : A → W → ℝ) (kOf : W → K)

omit [Fintype A] [Nonempty A] in
/-- The prior expectation is the sum of the cell sums (`Finset.sum_fiberwise`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_eq_sum_cellSum (b : A) : expect P (V b) = ∑ k, cellSum P V kOf k b := by
  unfold expect cellSum cell
  exact (sum_fiberwise univ kOf fun w => P.mass w * V b w).symm

/-- **T16, Good's theorem on a finite partition.** `priorBest ≤ partValue`: the value of the
decision problem does not decrease when a partition of the world is observed first
(sum of maxima versus maximum of sums).
Source: [[corr-core-inventory]] 007 / corrigibility-discussion-outline.md l. 58; miri.md I10 (Good's theorem)
Kind: P
Fidelity: exact (finite partition; the LI extension is out of scope)
Hyps: (a) only -/
theorem priorBest_le_partValue : priorBest P V ≤ partValue P V kOf := by
  unfold priorBest partValue
  refine sup'_le _ _ fun b _ => ?_
  rw [expect_eq_sum_cellSum P V kOf b]
  exact sum_le_sum fun k _ => le_sup' (fun b => cellSum P V kOf k b) (mem_univ b)

/-- **T16, strictness.** If some cell strictly beats every prior-optimal action — for every `b₀`
maximising `E_P[V(·)]` there is `b` with `cellSum k b₀ < cellSum k b` — the value of the
partition is strictly positive.
Source: [[corr-core-inventory]] 007 (the strictness clause)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem priorBest_lt_partValue
    (hstrict : ∃ k, ∀ b₀, (∀ b, expect P (V b) ≤ expect P (V b₀)) →
      ∃ b, cellSum P V kOf k b₀ < cellSum P V kOf k b) :
    priorBest P V < partValue P V kOf := by
  obtain ⟨k₀, hk₀⟩ := hstrict
  obtain ⟨b₀, -, hb₀⟩ := exists_mem_eq_sup' (univ_nonempty (α := A)) (fun b => expect P (V b))
  have hopt : ∀ b, expect P (V b) ≤ expect P (V b₀) := fun b => by
    rw [← hb₀]; exact le_sup' (fun b => expect P (V b)) (mem_univ b)
  obtain ⟨b₁, hb₁⟩ := hk₀ b₀ hopt
  unfold priorBest partValue
  rw [hb₀, expect_eq_sum_cellSum P V kOf b₀]
  refine sum_lt_sum (fun k _ => le_sup' (fun b => cellSum P V kOf k b) (mem_univ b₀))
    ⟨k₀, mem_univ _, lt_of_lt_of_le hb₁ (le_sup' (fun b => cellSum P V kOf k₀ b) (mem_univ b₁))⟩

omit [Fintype K] [Fintype A] [Nonempty A] in
/-- A cell sum of the coarsened partition `g ∘ kOf'` is the sum of the finer cell sums over the
fibre of `g`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellSum_coarsen {K' : Type*} [Fintype K'] [DecidableEq K'] (g : K' → K) (kOf' : W → K')
    (k : K) (b : A) :
    cellSum P V (g ∘ kOf') k b = ∑ k' ∈ univ.filter (g · = k), cellSum P V kOf' k' b := by
  unfold cellSum cell
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun w => (g ∘ kOf') w = k))
    (t := univ.filter (g · = k)) (g := kOf') (fun w hw => by simpa using hw)]
  refine sum_congr rfl fun j hj => ?_
  refine sum_congr ?_ fun _ _ => rfl
  ext w
  simp only [mem_filter, mem_univ, true_and, Function.comp]
  rw [mem_filter] at hj
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by rw [h]; exact hj.2, h⟩

/-- The maximum of a sum is at most the sum of the maxima.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_sum_le {ι : Type*} (s : Finset ι) (f : ι → A → ℝ) :
    univ.sup' univ_nonempty (fun b => ∑ i ∈ s, f i b) ≤ ∑ i ∈ s, univ.sup' univ_nonempty (fun b => f i b) :=
  sup'_le _ _ fun b _ => sum_le_sum fun i _ => le_sup' (fun b => f i b) (mem_univ b)

/-- **T16, monotone under coarsening.** If `kOf = g ∘ kOf'` (every cell of `kOf` is a union of
cells of `kOf'`) then `partValue kOf ≤ partValue kOf'`: finer information is worth at least as
much.
Source: [[corr-core-inventory]] 007; miri.md Prop. 13.3 ("any function of `h` is worth at most full knowledge of `h`")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem partValue_mono_coarsen {K' : Type*} [Fintype K'] [DecidableEq K'] (g : K' → K)
    (kOf' : W → K') : partValue P V (g ∘ kOf') ≤ partValue P V kOf' := by
  unfold partValue
  calc ∑ k, univ.sup' univ_nonempty (fun b => cellSum P V (g ∘ kOf') k b)
      = ∑ k, univ.sup' univ_nonempty (fun b => ∑ k' ∈ univ.filter (g · = k), cellSum P V kOf' k' b) := by
        refine sum_congr rfl fun k _ => ?_
        congr 1; funext b; exact cellSum_coarsen P V g kOf' k b
    _ ≤ ∑ k, ∑ k' ∈ univ.filter (g · = k), univ.sup' univ_nonempty (fun b => cellSum P V kOf' k' b) :=
        sum_le_sum fun k _ => sup'_sum_le _ _
    _ = ∑ k', univ.sup' univ_nonempty (fun b => cellSum P V kOf' k' b) :=
        sum_fiberwise univ g fun k' => univ.sup' univ_nonempty (fun b => cellSum P V kOf' k' b)

end Partition

/-! ## The two-option specialisation -/

section TwoOption

variable {W K : Type*} [Fintype W] [Fintype K] [DecidableEq K]

/-- `TwoAct` is nonempty. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Nonempty TwoAct := ⟨TwoAct.cont⟩

/-- The two-option payoff: `cont ↦ X`, `stop ↦ 0`.
Source: miri.md Prop. 13.3 (the binary shutdown act). Kind: D. Fidelity: exact -/
def twoOptionV (X : W → ℝ) : TwoAct → W → ℝ
  | .cont, w => X w
  | .stop, _ => 0

/-- The two-option cell sum of `X`: `∑_{w ∈ cell k} P(w) X(w)`.
Source: miri.md Prop. 13.3. Kind: D. Fidelity: exact -/
noncomputable def cellSumX (P : Distr W) (X : W → ℝ) (kOf : W → K) (k : K) : ℝ :=
  ∑ w ∈ cell kOf k, P.mass w * X w

/-- The two-option value of a partition: `partValue` with the two-option payoff.
Source: miri.md Prop. 13.3 ("the two-option decision value of a partition"). Kind: D. Fidelity: exact -/
noncomputable def partValue2 (P : Distr W) (X : W → ℝ) (kOf : W → K) : ℝ :=
  partValue P (twoOptionV X) kOf

/-- A maximum over `TwoAct` is a `max`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_twoAct (f : TwoAct → ℝ) :
    univ.sup' univ_nonempty f = max (f .cont) (f .stop) := by
  refine le_antisymm (sup'_le _ _ fun b _ => ?_) (max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _)))
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- `partValue2 = ∑_k max (cellSumX k) 0`: continue on cells whose sum is positive, stop
otherwise (the constant `V(stop) = 0` drops).
Source: miri.md Prop. 13.3. Kind: L. Fidelity: exact -/
theorem partValue2_eq (P : Distr W) (X : W → ℝ) (kOf : W → K) :
    partValue2 P X kOf = ∑ k, max (cellSumX P X kOf k) 0 := by
  unfold partValue2 partValue
  refine sum_congr rfl fun k _ => ?_
  rw [sup'_twoAct]
  simp only [cellSum, cellSumX, twoOptionV, mul_zero, sum_const_zero]

end TwoOption

/-! ## The bridge to the parent's `voiButton` -/

section Bridge

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- The parent's value function read on the joint `Ω × Obs`: `V'(b, (ω, o)) = V(a₁, o, b, ω)`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def jointV (a : A₁) : A₂ → Ω × Obs → ℝ := fun b p => S.V a p.2 b p.1

/-- On the joint, the `o`-cell sum of `b` is the parent's `E_P[V(a₁, o, b, ·) 1_o]`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellSum_joint (a : A₁) (o : Obs) (b : A₂) :
    cellSum (jointDistr S a) (jointV S a) Prod.snd o b = S.obsExpect a o (S.V a o b) := by
  haveI : Nonempty A₂ := ⟨S.Sh_nonempty.choose⟩
  unfold cellSum cell obsExpect jointV
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  rw [Obs.sum_eq]
  cases o <;> simp [jointDistr_mass]

/-- On the joint, the prior expectation of `jointV b` is the parent's `E_μ[V(a₁, o₀, b, ·)]` under
A1 (tower property with the observation index removed).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_jointV (hA1 : S.A1) (a : A₁) (o₀ : Obs) (b : A₂) :
    expect (jointDistr S a) (jointV S a b) = S.priorValue a o₀ b := by
  unfold expect jointV priorValue
  rw [Fintype.sum_prod_type]
  unfold expect
  refine sum_congr rfl fun ω _ => ?_
  rw [Obs.sum_eq]
  simp only [jointDistr_mass, obsWeight_press, obsWeight_silent, hA1 a .press o₀ b ω,
    hA1 a .silent o₀ b ω]
  ring

/-- **T16, the bridge.** Under A1 the parent's `voiButton a o₀` is `partValue − priorBest` on the
joint `Ω × Obs` with the observation as the partition.
Source: [[corr-core-inventory]] 007; filler.md F4(b) (`voiButton` as `E_o[max E[V | o]] − max E[V]`)
Kind: L
Fidelity: exact
Hyps: (a) A1 as Dict-5 -/
theorem voiButton_eq_partValue_sub (hA1 : S.A1) (a : A₁) (o₀ : Obs) :
    haveI : Nonempty A₂ := ⟨S.Sh_nonempty.choose⟩
    S.voiButton a o₀ = partValue (jointDistr S a) (jointV S a) Prod.snd - priorBest (jointDistr S a) (jointV S a) := by
  haveI : Nonempty A₂ := ⟨S.Sh_nonempty.choose⟩
  unfold voiButton partValue priorBest obsMax priorMax
  rw [Obs.sum_eq]
  simp only [cellSum_joint, expect_jointV S hA1 a o₀]

/-- **T16, the parent's `voiButton_nonneg` re-derived** from Good's theorem on a partition.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (as the parent proves it directly)
Kind: C
Fidelity: exact
Hyps: (a) A1 -/
theorem voiButton_nonneg_of_partition (hA1 : S.A1) (a : A₁) (o₀ : Obs) : 0 ≤ S.voiButton a o₀ := by
  haveI : Nonempty A₂ := ⟨S.Sh_nonempty.choose⟩
  rw [voiButton_eq_partValue_sub S hA1 a o₀, sub_nonneg]
  exact priorBest_le_partValue _ _ _

end Bridge

end Cleanroom.Corrigibility.CorrThreeStepFacts
