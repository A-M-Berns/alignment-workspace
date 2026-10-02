import Cleanroom.Corrigibility.CorrJointProcess.Cellwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# T9 — Cor. B′: the legitimacy budget as a summability condition

Load-bearing 4.

* **(a) The union bound (`C`).** For events `L t ⊆ Ω` under a `Distr Ω` with `λ_t = 1 − P(L t)`:
  `P(⋂_{t ∈ s} L t) ≥ 1 − ∑_{t ∈ s} λ_t` (`union_bound`), by induction from the two-event
  inclusion–exclusion step `P(A ∩ B) ≥ P(A) + P(B) − 1` (`probOf_inter_ge`).
* **(b) Summability (`P`).** The bound is positive at every horizon iff the partial sums stay
  below `1`; for nonnegative `λ` that is: summable with `∑ λ ≤ 1` (`partial_lt_one_summable`,
  `partial_lt_one_of_tsum_lt`); a constant `λ > 0` kills the bound at a finite horizon
  (`const_bound_dies`). The "limit property in disguise" of A.14.2, as theorems.
* **(c) Sharpness (N+).** Disjoint failures attain the bound (`disjoint_attains`); independent
  failures over the product distribution `bernoulliProd` have `P(⋂ L t) = (1 − λ)^T`
  (`bernoulliProd_all_ok`), large while the bound is negative (`independent_bound_vacuous`:
  `T = 100`, `λ = 1/50`). Numbers: `λ_t = 1/100`: `9/10` at `T = 10`, `0` at `T = 100`
  (`budget_numbers`).
* **(d) The transport clause (`L`/`S`, disclosed).** The source's own verdict is "content nil under
  (i-A)": the inductive step is the identity `Cellwise.mixture_cellwise_iff` — the builder's
  conditional on "successor = `i`" is `ρ_i`, so the builder's cellwise (i) there *is* `ρ_i`'s.
  Nothing on the deep algebra is built (findings).

Sources: joint-final.md Cor. B′; adv A.14.2, (G); joint.md C(iv-R).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

section UnionBound

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The probability of a finite event `A` under `μ`: `∑_{ω ∈ A} μ(ω)`.
Source: none: infrastructure (FAF's `Distr.prob` is on `Set`; this is its `Finset` form)
Kind: D
Fidelity: exact -/
noncomputable def probOf (μ : Distr Ω) (A : Finset Ω) : ℝ := ∑ ω ∈ A, μ.mass ω

/-- `0 ≤ P(A)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma probOf_nonneg (μ : Distr Ω) (A : Finset Ω) : 0 ≤ probOf μ A := sum_nonneg fun ω _ => μ.nonneg ω

/-- `P(A) ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma probOf_le_one (μ : Distr Ω) (A : Finset Ω) : probOf μ A ≤ 1 := by
  unfold probOf
  rw [← μ.sum_eq_one]
  exact sum_le_univ_sum_of_nonneg μ.nonneg

/-- `P(univ) = 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma probOf_univ (μ : Distr Ω) : probOf μ univ = 1 := μ.sum_eq_one

/-- **The two-event step**: `P(A ∩ B) ≥ P(A) + P(B) − 1` (inclusion–exclusion and `P(A ∪ B) ≤ 1`).
Source: [[corr-wf14-inventory]] 065 / joint-final.md Cor. B′ ("the legitimacy bound … `≥ 1 − ∑ λ_t`")
Kind: L
Fidelity: exact -/
lemma probOf_inter_ge (μ : Distr Ω) (A B : Finset Ω) :
    probOf μ A + probOf μ B - 1 ≤ probOf μ (A ∩ B) := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := μ.mass)
  have hle := probOf_le_one μ (A ∪ B)
  unfold probOf at *
  linarith

/-- **T9(a), the union bound (Cor. B′).** For a finite family of events `L t` indexed by a
`Finset s`, with `λ_t := 1 − P(L t)`: `1 − ∑_{t ∈ s} λ_t ≤ P(⋂_{t ∈ s} L t)`.
Source: [[corr-wf14-inventory]] 065, 2-011 / joint-final.md Cor. B′ ("`P°(legitimate through T) ≥ 1 − ∑_{t<T} λ_t`")
Kind: C (`Finset` induction on `probOf_inter_ge`)
Fidelity: exact (legitimacy events are *given* `Finset`s — S.8 has no world-side definition of `L`)
Hyps: (a) only -/
theorem union_bound {ι : Type} [DecidableEq ι] (μ : Distr Ω) (L : ι → Finset Ω) (s : Finset ι) :
    1 - ∑ t ∈ s, (1 - probOf μ (L t)) ≤ probOf μ (s.inf L) := by
  induction s using Finset.induction_on with
  | empty => simp [probOf_univ]
  | insert a s ha ih =>
    rw [sum_insert ha, inf_insert]
    have := probOf_inter_ge μ (L a) (s.inf L)
    have hinf : L a ⊓ s.inf L = L a ∩ s.inf L := rfl
    rw [hinf]
    linarith

/-- **T9(a) on a horizon `T`**: `1 − ∑_{t < T} λ_t ≤ P(⋂_{t < T} L t)`.
Source: [[corr-wf14-inventory]] 065 / joint-final.md Cor. B′
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem union_bound_range (μ : Distr Ω) (L : ℕ → Finset Ω) (T : ℕ) :
    1 - ∑ t ∈ range T, (1 - probOf μ (L t)) ≤ probOf μ ((range T).inf L) :=
  union_bound μ L (range T)

end UnionBound

/-! ## (b) Summability -/

section Summability

/-- **T9(b): the bound is positive at every horizon iff the partial sums stay below `1`** — a
restatement, recorded so the two faces are the same object.
Source: [[corr-wf14-inventory]] 2-011 / adv A.14.2 ("informative only when `∑_{t<T} λ_t < 1`")
Kind: L
Fidelity: exact -/
theorem bound_pos_iff (l : ℕ → ℝ) : (∀ T, 0 < 1 - ∑ t ∈ range T, l t) ↔ ∀ T, ∑ t ∈ range T, l t < 1 := by
  constructor <;> intro H T <;> linarith [H T]

/-- **T9(b), summability (Cor. B′ / A.14.2).** If the bound is informative at every horizon
(`∑_{t<T} λ_t < 1` for all `T`) and `λ ≥ 0`, then `λ` is summable with `∑ λ_t ≤ 1` — the
finite-time statement is a tail condition on the training process.
Source: [[corr-wf14-inventory]] 2-011 / adv A.14.2 ("a summability condition — the limit property in disguise")
Kind: P (bounded partial sums of a nonnegative series)
Fidelity: exact
Hyps: (a) only -/
theorem partial_lt_one_summable (l : ℕ → ℝ) (hl : ∀ t, 0 ≤ l t) (H : ∀ T, ∑ t ∈ range T, l t < 1) :
    Summable l ∧ ∑' t, l t ≤ 1 :=
  ⟨summable_of_sum_range_le hl fun T => (H T).le, Real.tsum_le_of_sum_range_le hl fun T => (H T).le⟩

/-- **T9(b), the converse.** If `λ ≥ 0` is summable with `∑ λ_t < 1`, the bound is positive at
every horizon.
Source: [[corr-wf14-inventory]] 2-011 / adv A.14.2; joint-final.md Cor. B′ ("a summable illegitimacy mass … a potential that must stay below `1`")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem partial_lt_one_of_tsum_lt (l : ℕ → ℝ) (hl : ∀ t, 0 ≤ l t) (hs : Summable l) (H : ∑' t, l t < 1) :
    ∀ T, ∑ t ∈ range T, l t < 1 := fun T =>
  lt_of_le_of_lt (hs.sum_le_tsum (range T) fun t _ => hl t) H

/-- **T9(b): a constant `λ > 0` kills the bound at a finite horizon** (Archimedean).
Source: [[corr-wf14-inventory]] 2-011 / adv A.14.2 ("with `1/1000` it dies at `T ≈ 1000`")
Kind: L
Fidelity: exact -/
theorem const_bound_dies (l : ℝ) (hl : 0 < l) : ∃ T : ℕ, 1 - ∑ _t ∈ range T, l < 0 := by
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / l)
  refine ⟨T, ?_⟩
  rw [sum_const, card_range, nsmul_eq_mul]
  rw [div_lt_iff₀ hl] at hT
  linarith

/-- **T9 numbers (adv (G), the mandate's reading)**: `λ_t = 1/100`: `9/10` at `T = 10`, `0` at
`T = 100`, `−1` at `T = 200`.
Source: [[corr-wf14-inventory]] 065, 2-011 / adv (G)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem budget_numbers :
    (1 : ℝ) - ∑ _t ∈ range 10, (1 / 100 : ℝ) = 9 / 10 ∧ (1 : ℝ) - ∑ _t ∈ range 100, (1 / 100 : ℝ) = 0 ∧
      (1 : ℝ) - ∑ _t ∈ range 200, (1 / 100 : ℝ) = -1 := by
  simp only [sum_const, card_range, nsmul_eq_mul]; norm_num

end Summability

/-! ## (c) Sharpness -/

section Sharpness

/-- The three-point distribution `(1/100, 1/100, 98/100)` on `Fin 3`.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
noncomputable def threeFail : Distr (Fin 3) where
  mass j := if j = 2 then 98 / 100 else 1 / 100
  nonneg j := by
    show 0 ≤ (if j = 2 then (98 / 100 : ℝ) else 1 / 100)
    split_ifs <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- **T9(c), attained**: two disjoint failure events of mass `1/100` each — `L 0 = {j ≠ 0}`,
`L 1 = {j ≠ 1}` — give `P(L 0 ∩ L 1) = 98/100 = 1 − 1/100 − 1/100`: the union bound is tight.
Source: [[corr-wf14-inventory]] 065 / mandate T9(c)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem disjoint_attains :
    probOf threeFail (univ.filter (· ≠ 0) ∩ univ.filter (· ≠ 1)) = 98 / 100 ∧
      1 - ((1 - probOf threeFail (univ.filter (· ≠ 0))) + (1 - probOf threeFail (univ.filter (· ≠ 1)))) =
        98 / 100 := by
  have hset : ((univ : Finset (Fin 3)).filter (· ≠ 0) ∩ univ.filter (· ≠ 1)) = {2} := by decide
  rw [hset]
  simp [probOf, threeFail, Finset.sum_filter, Fin.sum_univ_three]
  norm_num

/-- **The product of `T` independent Bernoulli(`λ`) failures** on `Fin T → Bool` (`true` =
the round fails).
Source: none: infrastructure (witness; the "independent failures over a product `Distr`" of mandate T9(c))
Kind: D
Fidelity: exact -/
noncomputable def bernoulliProd (T : ℕ) (l : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) : Distr (Fin T → Bool) where
  mass f := ∏ i, if f i then l else 1 - l
  nonneg f := prod_nonneg fun i _ => by split_ifs <;> linarith [hl.1, hl.2]
  sum_eq_one := by
    have h := prod_univ_sum (fun _ : Fin T => (univ : Finset Bool))
      (fun _ b => if b then l else 1 - l)
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    simp

/-- **T9(c), independence**: the all-legitimate event `{f ∣ ∀ t, f t = false}` has probability
`(1 − λ)^T` under `bernoulliProd`.
Source: [[corr-wf14-inventory]] 065 / mandate T9(c) ("`P(⋂ L t) = (1−λ)^T`")
Kind: L
Fidelity: exact -/
theorem bernoulliProd_all_ok (T : ℕ) (l : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    probOf (bernoulliProd T l hl) (univ.filter fun f => ∀ t, f t = false) = (1 - l) ^ T := by
  have hsingle : (univ.filter fun f : Fin T → Bool => ∀ t, f t = false) = {fun _ => false} := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hf; funext t; exact hf t
    · intro hf t; rw [hf]
  rw [probOf, hsingle, sum_singleton]
  simp [bernoulliProd]

/-- The intersection over `t < T` of the events `{f ∣ f t = false}` is the all-legitimate event.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma inf_round_ok (T : ℕ) :
    (univ : Finset (Fin T)).inf (fun t => (univ : Finset (Fin T → Bool)).filter fun f => f t = false) =
      univ.filter fun f => ∀ t, f t = false := by
  ext f
  simp [mem_inf]

/-- **T9(c), the bound is vacuous while the truth is large.** `T = 100` independent failures of
rate `λ = 1/50`: the union bound says `P ≥ 1 − 2 = −1` (nothing), while
`P(⋂ L t) = (49/50)^100 > 1/10`.
Source: [[corr-wf14-inventory]] 065, 2-011 / adv A.14.2 (what the bound does and does not say)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem independent_bound_vacuous :
    (1 : ℝ) - ∑ _t : Fin 100, (1 - (1 - (1 / 50 : ℝ))) = -1 ∧
      (1 / 10 : ℝ) < probOf (bernoulliProd 100 (1 / 50) ⟨by norm_num, by norm_num⟩)
        ((univ : Finset (Fin 100)).inf fun t => univ.filter fun f => f t = false) := by
  refine ⟨by simp; norm_num, ?_⟩
  rw [inf_round_ok, bernoulliProd_all_ok]
  norm_num

/-- Each single-round legitimacy event has probability `1 − λ` (so `λ_t = λ`), closing the
witness's hypothesis package: `independent_bound_vacuous`'s left side is `union_bound`'s bound.
Source: none: infrastructure (witness closure)
Kind: L
Fidelity: n/a -/
theorem bernoulliProd_round_ok (T : ℕ) (l : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) :
    probOf (bernoulliProd T l hl) (univ.filter fun f => f t = false) = 1 - l := by
  -- marginalise: the event is a product with one coordinate fixed
  unfold probOf bernoulliProd
  simp only
  have h := prod_univ_sum (fun i : Fin T => if i = t then ({false} : Finset Bool) else univ)
    (fun _ b => if b then l else 1 - l)
  have hpi : Fintype.piFinset (fun i : Fin T => if i = t then ({false} : Finset Bool) else univ) =
      univ.filter fun f : Fin T → Bool => f t = false := by
    ext f
    simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
    constructor
    · intro H; have := H t; simpa using this
    · intro H i; by_cases hi : i = t
      · subst hi; simpa using H
      · simp [hi]
  rw [hpi] at h
  rw [← h, prod_eq_single t]
  · simp
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (mem_univ t) h

end Sharpness

end Cleanroom.Corrigibility.CorrJointProcess
