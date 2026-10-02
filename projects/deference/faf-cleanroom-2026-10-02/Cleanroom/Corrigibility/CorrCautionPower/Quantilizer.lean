import Cleanroom.Corrigibility.CorrCautionPower.Setting
import Mathlib.Data.Finset.Max

/-!
# `corr-caution-power` — Taylor 2016's quantilizer: Definition 1, Lemma 1, Lemma 2, Theorem 1

Taylor's `Q_q` samples from the top-`q` fraction of `γ`-mass ranked by `U`; the paper notes the
ranking needs a canonical tie-break ("assigning as much probability mass as possible to
lexicographically earlier actions", l. 75). Here the tie-break is an **explicit `LinearOrder A`
compatible with `U`** (`Compatible U`: higher in the order ⇒ weakly higher `U`), and `Q_q` is
defined by *water-filling* on the finite type, with no `[0, 1]`-measure:
`qmass γ q a = (min q (aboveEq γ a) − min q (above γ a)) / q`, where `above γ a` is the
`γ`-mass strictly above `a` in the order and `aboveEq γ a = above γ a + γ(a)`.

* `quantilize γ q hq hq1 : Distr A` for `0 < q ≤ 1` (masses nonnegative, sum `1` by a
  telescoping sum along the order, `sum_telescope`). **Junk-value watch:** at `q = 0` the
  formula divides by zero; `0 < q` is a hypothesis everywhere, and D8's `q = 0` case
  (`Witnesses.lean`, T1(v)) is *not* a quantilizer.
* **Lemma 1** `quantilize_cost_bound`: for every nonnegative `c : A → ℝ`,
  `E_{Q_q}[c] ≤ (1/q) E_γ[c]` — no `Ω` in the statement (S4(a)).
* **Lemma 2** `fits_under_base`: constraint (2) forces `p(a) ≤ t γ(a)` for *all* `a`, including
  off the support of `γ` (the paper's printed proof covers only `γ(a) > 0`).
* **Theorem 1** `quantilize_optimal`: for `0 < q ≤ 1` and every `p` with `p(a) ≤ γ(a)/q`,
  `E_p[U] ≤ E_{Q_q}[U]`; corollary `quantilize_optimal_of_constraint` (Taylor's statement).
* Structure lemmas `qmass_of_aboveEq_le` (full atom), `qmass_of_le_above` (empty atom), the
  `U`-level bounds `strictAbove_le_above`, `aboveEq_le_weakAbove` (for witnesses under *any*
  compatible tie-break), and `partial_unique` (at most one partial atom).

Source: [[corr-refs-inventory]] 065 → `taylor-2016-quantilizers-a-safer-alternative-to-maximizers.md`
Definition 1 and the three-action example (l. 60–75), Lemma 1, Lemma 2, Theorem 1 (l. 96–118).
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

section Quantilizer

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- **The tie-break is compatible with `U`:** higher in the order means weakly higher `U`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Def. 1 and l. 75 (the canonical `f`)
Kind: D
Fidelity: variant: canonical (linear-order) tie-break — the paper's `f : [0, 1] → A` may interleave tied actions (only `x > y ⇒ U(f x) ≥ U(f y)`, l. 53), giving mixtures over linear tie-breaks; Lemma 1 and Theorem 1 hold for those too, and `quantilize_expect_tiebreak_indep` covers the linear ones -/
def Compatible (U : A → ℝ) : Prop := ∀ a b, a < b → U a ≤ U b

omit [Fintype A] in
/-- A strictly higher `U` forces a strictly higher position. Source: none: infrastructure.
Kind: L. Fidelity: n/a -/
lemma Compatible.lt_of_lt {U : A → ℝ} (hU : Compatible U) {a b : A} (h : U a < U b) : a < b := by
  by_contra hab
  rcases (not_lt.mp hab).lt_or_eq with hba | hba
  · exact absurd (hU b a hba) (not_le.mpr h)
  · rw [hba] at h; exact lt_irrefl _ h

omit [Fintype A] in
/-- A weakly higher position gives weakly higher `U`. Source: none: infrastructure.
Kind: L. Fidelity: n/a -/
lemma Compatible.le_of_le {U : A → ℝ} (hU : Compatible U) {a b : A} (h : a ≤ b) : U a ≤ U b := by
  rcases h.lt_or_eq with h | rfl
  · exact hU a b h
  · exact le_rfl

/-- The `γ`-mass strictly above `a` in the tie-break order.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Def. 1 (the cumulative rank)
Kind: D
Fidelity: exact -/
noncomputable def above (γ : Distr A) (a : A) : ℝ := ∑ b ∈ univ.filter (a < ·), γ.mass b

/-- The `γ`-mass weakly above `a` (`above γ a + γ(a)`, `aboveEq_eq`).
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Def. 1
Kind: D
Fidelity: exact -/
noncomputable def aboveEq (γ : Distr A) (a : A) : ℝ := ∑ b ∈ univ.filter (a ≤ ·), γ.mass b

/-- `aboveEq = above + own mass`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma aboveEq_eq (γ : Distr A) (a : A) : aboveEq γ a = above γ a + γ.mass a := by
  unfold aboveEq above
  have h : univ.filter (a ≤ ·) = insert a (univ.filter (a < ·)) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hab
      rcases hab.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
  rw [h, sum_insert (by simp), add_comm]

/-- `0 ≤ above`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma above_nonneg (γ : Distr A) (a : A) : 0 ≤ above γ a :=
  sum_nonneg fun b _ => γ.nonneg b

/-- `above ≤ aboveEq`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma above_le_aboveEq (γ : Distr A) (a : A) : above γ a ≤ aboveEq γ a := by
  rw [aboveEq_eq]; exact le_add_of_nonneg_right (γ.nonneg a)

/-- `aboveEq ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma aboveEq_le_one (γ : Distr A) (a : A) : aboveEq γ a ≤ 1 := by
  unfold aboveEq
  rw [← γ.sum_eq_one]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => γ.nonneg b

/-- `above` is antitone in the order. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma above_anti (γ : Distr A) {a b : A} (h : a ≤ b) : above γ b ≤ above γ a := by
  unfold above
  refine sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => γ.nonneg c
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  exact lt_of_le_of_lt h hc

/-- Everything weakly above a strictly higher `a` is strictly above `a₁`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma aboveEq_le_above_of_lt (γ : Distr A) {a₁ a : A} (h : a₁ < a) : aboveEq γ a ≤ above γ a₁ := by
  unfold aboveEq above
  refine sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => γ.nonneg c
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  exact lt_of_lt_of_le h hc

/-- The maximum of the order has nothing above it. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma above_max' (γ : Distr A) (hne : (univ : Finset A).Nonempty) :
    above γ (univ.max' hne) = 0 := by
  unfold above
  refine sum_eq_zero fun b hb => ?_
  simp only [mem_filter, mem_univ, true_and] at hb
  exact absurd (le_max' univ b (mem_univ b)) (not_le.mpr hb)

omit [LinearOrder A] in
/-- A `Distr` lives on a nonempty type. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma univ_nonempty_of_distr (γ : Distr A) : (univ : Finset A).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have := γ.sum_eq_one
  rw [h, sum_empty] at this
  exact zero_ne_one this

omit [Fintype A] in
/-- **Telescoping along a linear order:** for any `f : ℝ → ℝ` and weights `m`,
`∑_{a ∈ s} (f(∑_{b ∈ s, a ≤ b} m b) − f(∑_{b ∈ s, a < b} m b)) = f(∑_{b ∈ s} m b) − f 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_telescope (m : A → ℝ) (s : Finset A) :
    ∀ f : ℝ → ℝ, ∑ a ∈ s, (f (∑ b ∈ s.filter (a ≤ ·), m b) - f (∑ b ∈ s.filter (a < ·), m b))
      = f (∑ b ∈ s, m b) - f 0 := by
  induction s using Finset.induction_on_max with
  | empty => intro f; simp
  | insert a s hlt ih =>
    intro f
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hfle : (insert a s).filter (a ≤ ·) = {a} := by
      ext x
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hx | hx, hax⟩
        · exact hx
        · exact absurd (hlt x hx) (not_lt.mpr hax)
      · rintro rfl; exact ⟨Or.inl rfl, le_rfl⟩
    have hflt : (insert a s).filter (a < ·) = ∅ := by
      ext x
      simp only [mem_filter, mem_insert, notMem_empty, iff_false, not_and]
      rintro (rfl | hx) hax
      · exact lt_irrefl _ hax
      · exact lt_asymm (hlt x hx) hax
    have hle : ∀ x ∈ s, (insert a s).filter (x ≤ ·) = insert a (s.filter (x ≤ ·)) := by
      intro x hx; ext y
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hy | hy, hxy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨hy, hxy⟩
      · rintro (rfl | ⟨hy, hxy⟩)
        · exact ⟨Or.inl rfl, (hlt x hx).le⟩
        · exact ⟨Or.inr hy, hxy⟩
    have hlt' : ∀ x ∈ s, (insert a s).filter (x < ·) = insert a (s.filter (x < ·)) := by
      intro x hx; ext y
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hy | hy, hxy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨hy, hxy⟩
      · rintro (rfl | ⟨hy, hxy⟩)
        · exact ⟨Or.inl rfl, hlt x hx⟩
        · exact ⟨Or.inr hy, hxy⟩
    have hnle : ∀ x, a ∉ s.filter (x ≤ ·) := fun x h => ha (mem_filter.1 h).1
    have hnlt : ∀ x, a ∉ s.filter (x < ·) := fun x h => ha (mem_filter.1 h).1
    rw [sum_insert ha, hfle, hflt, sum_singleton, sum_empty, sum_insert ha]
    rw [sum_congr rfl (fun x hx => by
      rw [hle x hx, hlt' x hx, sum_insert (hnle x), sum_insert (hnlt x)])]
    rw [ih (fun y => f (m a + y))]
    simp only [add_zero]
    ring

/-- **Definition 1, the water-filling mass** `(min q (aboveEq γ a) − min q (above γ a)) / q`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Def. 1 (l. 60–75)
Kind: D
Fidelity: exact (finite water-filling in place of the `[0,1]`-measure; explicit tie-break) -/
noncomputable def qmass (γ : Distr A) (q : ℝ) (a : A) : ℝ :=
  (min q (aboveEq γ a) - min q (above γ a)) / q

/-- The water-filling mass is nonnegative for `0 < q`. Source: none: infrastructure.
Kind: L. Fidelity: n/a -/
lemma qmass_nonneg (γ : Distr A) {q : ℝ} (hq : 0 < q) (a : A) : 0 ≤ qmass γ q a := by
  unfold qmass
  apply div_nonneg _ hq.le
  rw [sub_nonneg]
  exact min_le_min_left q (above_le_aboveEq γ a)

/-- The water-filling masses sum to `1` for `0 < q ≤ 1` (telescoping along the order).
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Def. 1
Kind: L
Fidelity: exact -/
lemma sum_qmass (γ : Distr A) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) : ∑ a, qmass γ q a = 1 := by
  unfold qmass aboveEq above
  rw [← sum_div, sum_telescope γ.mass univ (fun x => min q x), γ.sum_eq_one,
    min_eq_left hq1, min_eq_right hq.le, sub_zero, div_self hq.ne']

/-- **Definition 1, the `q`-quantilizer** `Q_q[U, γ]` as a FAF `Distr`, for `0 < q ≤ 1`.
The ranking is the ambient `LinearOrder A` (compatible with `U` where a theorem needs it).
`q = 0` is excluded: the formula divides by zero and D8's `R̂ = 0` case is not a quantilizer.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Def. 1 (l. 60–75)
Kind: D
Fidelity: variant: finite type, canonical linear-order tie-break (see `Compatible`)
Hyps: n/a (definition) -/
noncomputable def quantilize (γ : Distr A) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) : Distr A where
  mass := qmass γ q
  nonneg := qmass_nonneg γ hq
  sum_eq_one := sum_qmass γ hq hq1

/-- Unfolding the quantilizer's mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma quantilize_mass (γ : Distr A) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (a : A) :
    (quantilize γ q hq hq1).mass a = qmass γ q a := rfl

/-! ### Structure: full, empty and partial atoms -/

/-- **Full atom:** if the whole weak-upper mass fits under `q`, the atom gets `γ(a)/q`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Thm. 1 proof ("assign `γ(a)/q` … to the best actions")
Kind: L
Fidelity: exact -/
lemma qmass_of_aboveEq_le (γ : Distr A) {q : ℝ} {a : A} (h : aboveEq γ a ≤ q) :
    qmass γ q a = γ.mass a / q := by
  unfold qmass
  rw [min_eq_right h, min_eq_right ((above_le_aboveEq γ a).trans h), aboveEq_eq, add_sub_cancel_left]

/-- **Empty atom:** if the strict-upper mass already reaches `q`, the atom gets `0`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Thm. 1 proof ("… and `0` to the rest")
Kind: L
Fidelity: exact -/
lemma qmass_of_le_above (γ : Distr A) {q : ℝ} {a : A} (h : q ≤ above γ a) : qmass γ q a = 0 := by
  unfold qmass
  rw [min_eq_left h, min_eq_left (h.trans (above_le_aboveEq γ a)), sub_self, zero_div]

/-- Every atom is full, empty or *partial* (`above < q < aboveEq`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma qmass_trichotomy (γ : Distr A) (q : ℝ) (a : A) :
    qmass γ q a = γ.mass a / q ∨ qmass γ q a = 0 ∨ (above γ a < q ∧ q < aboveEq γ a) := by
  rcases le_or_gt (aboveEq γ a) q with h | h
  · exact Or.inl (qmass_of_aboveEq_le γ h)
  rcases le_or_gt q (above γ a) with h' | h'
  · exact Or.inr (Or.inl (qmass_of_le_above γ h'))
  · exact Or.inr (Or.inr ⟨h', h⟩)

/-- **At most one partial atom:** two partial atoms coincide (their weak-upper intervals are
disjoint along the order).
Source: none: infrastructure (used by T4(d2))
Kind: L
Fidelity: n/a -/
lemma partial_unique (γ : Distr A) {q : ℝ} {a b : A} (ha : above γ a < q ∧ q < aboveEq γ a)
    (hb : above γ b < q ∧ q < aboveEq γ b) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact absurd (aboveEq_le_above_of_lt γ h) (not_le.mpr (ha.1.trans hb.2))
  · exact absurd (aboveEq_le_above_of_lt γ h) (not_le.mpr (hb.1.trans ha.2))

/-- **`U`-level lower bound on `above`:** under a compatible order, everything with strictly
larger `U` is strictly above.
Source: none: infrastructure (witnesses under any compatible tie-break)
Kind: L
Fidelity: n/a -/
lemma strictAbove_le_above (γ : Distr A) {U : A → ℝ} (hU : Compatible U) (a : A) :
    ∑ b ∈ univ.filter (fun b => U a < U b), γ.mass b ≤ above γ a := by
  unfold above
  refine sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => γ.nonneg c
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  exact hU.lt_of_lt hc

/-- **`U`-level upper bound on `aboveEq`:** under a compatible order, everything weakly above has
weakly larger `U`.
Source: none: infrastructure (witnesses under any compatible tie-break)
Kind: L
Fidelity: n/a -/
lemma aboveEq_le_weakAbove (γ : Distr A) {U : A → ℝ} (hU : Compatible U) (a : A) :
    aboveEq γ a ≤ ∑ b ∈ univ.filter (fun b => U a ≤ U b), γ.mass b := by
  unfold aboveEq
  refine sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => γ.nonneg c
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  exact hU.le_of_le hc

/-! ### Lemma 1 — the cost bound -/

/-- **Lemma 1, pointwise:** `Q_q(a) ≤ γ(a)/q` (the `γ`-mass of `a` inside the top-`q` slice is at
most `γ(a)`; `min q ·` is 1-Lipschitz).
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Lemma 1 (l. 96–104)
Kind: L
Fidelity: exact -/
lemma qmass_le (γ : Distr A) {q : ℝ} (hq : 0 < q) (a : A) : qmass γ q a ≤ γ.mass a / q := by
  unfold qmass
  apply div_le_div_of_nonneg_right _ hq.le
  rw [aboveEq_eq]
  have hm := γ.nonneg a
  rcases le_total q (above γ a) with h | h
  · rw [min_eq_left h, min_eq_left (h.trans (le_add_of_nonneg_right hm))]; linarith
  · rw [min_eq_right h]; linarith [min_le_right q (above γ a + γ.mass a)]

/-- **Taylor 2016, Lemma 1 (cost bound).** For every nonnegative cost `c : A → ℝ`,
`E_{Q_q}[c] ≤ (1/q) · E_γ[c]`. **No `Ω` in the statement:** the cost is arbitrary — a true harm
under a value function outside the agent's algebra is a `c` (this is S4(a), "survives algebra
misspecification").
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Lemma 1 (l. 96–104); [[corr-wf14-inventory]] 096 / caution-final.md S4(a)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem quantilize_cost_bound (γ : Distr A) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a) :
    expect (quantilize γ q hq hq1) c ≤ (1 / q) * expect γ c := by
  unfold expect
  rw [mul_sum]
  refine sum_le_sum fun a _ => ?_
  rw [quantilize_mass, show 1 / q * (γ.mass a * c a) = γ.mass a / q * c a by ring]
  exact mul_le_mul_of_nonneg_right (qmass_le γ hq a) (hc a)

/-! ### Lemma 2 — `p` fits under `γ` -/

/-- Expectation of a scaled indicator. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_single (μ : Distr A) (a : A) (k : ℝ) :
    expect μ (fun b => if b = a then k else 0) = μ.mass a * k := by
  unfold expect
  simp [mul_ite, sum_ite_eq']

/-- **Taylor 2016, Lemma 2 (`p` fits under `γ`), full pointwise form.** If `p` satisfies
constraint (2) — every nonnegative cost with `E_γ[c] ≤ 1` has `E_p[c] ≤ t` — then
`p(a) ≤ t γ(a)` for **all** `a`, including `γ(a) = 0`. The paper's printed proof takes
`c = 1_a/γ(a)`, which needs `γ(a) > 0`; off the support, `c = K·1_a` for every `K > 0` forces
`p(a) = 0` (presentation finding).
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Lemma 2 (l. 105–113)
Kind: P
Fidelity: exact (statement); the proof completes the paper's off-support case
Hyps: (a) only -/
theorem fits_under_base (γ p : Distr A) (t : ℝ)
    (h : ∀ c : A → ℝ, (∀ a, 0 ≤ c a) → expect γ c ≤ 1 → expect p c ≤ t) :
    ∀ a, p.mass a ≤ t * γ.mass a := by
  intro a
  have ht : 0 ≤ t := by
    have := h (fun _ => 0) (fun _ => le_rfl) (by rw [expect_const]; norm_num)
    rwa [expect_const] at this
  rcases (γ.nonneg a).lt_or_eq with hγ | hγ
  · -- on the support: `c = 1_a / γ(a)`
    have := h (fun b => if b = a then 1 / γ.mass a else 0)
      (fun b => by split_ifs <;> positivity)
      (by rw [expect_single, mul_one_div_cancel hγ.ne'])
    rw [expect_single] at this
    rwa [mul_one_div, div_le_iff₀ hγ] at this
  · -- off the support: `c = K · 1_a` for every `K`
    rw [← hγ, mul_zero]
    by_contra hpa
    replace hpa := not_le.mp hpa
    have hK := h (fun b => if b = a then (t + 1) / p.mass a else 0)
      (fun b => by split_ifs <;> positivity)
      (by rw [expect_single, ← hγ, zero_mul]; norm_num)
    rw [expect_single, mul_div_cancel₀ _ hpa.ne'] at hK
    linarith

/-! ### Theorem 1 — optimality -/

/-- **Taylor 2016, Theorem 1 (quantilizer optimality), cap form.** For `0 < q ≤ 1`, a tie-break
compatible with `U`, and every `p : Distr A` with `p(a) ≤ γ(a)/q` for all `a`:
`E_p[U] ≤ E_{Q_q}[U]`. Exchange argument: with `a₁` the lowest action whose strict-upper mass is
below `q` and `u₀ = U a₁`, every atom above `a₁` is full (`Q ≥ p`, `U ≥ u₀`) and every atom below
is empty (`Q = 0 ≤ p`, `U ≤ u₀`), so `∑ (Q − p)(U − u₀) ≥ 0`, and the `u₀` term cancels.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Theorem 1 (l. 114–118)
Kind: P
Fidelity: exact (the tie-break made explicit; the paper's `f` is any compatible order)
Hyps: (a) only -/
theorem quantilize_optimal (γ : Distr A) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (U : A → ℝ)
    (hU : Compatible U) (p : Distr A) (hp : ∀ a, p.mass a ≤ γ.mass a / q) :
    expect p U ≤ expect (quantilize γ q hq hq1) U := by
  set Q := quantilize γ q hq hq1 with hQ
  have hne := univ_nonempty_of_distr γ
  -- the set of atoms not yet exhausted; nonempty because the top atom has nothing above it
  set N := univ.filter (fun a => above γ a < q) with hN
  have hNne : N.Nonempty := ⟨univ.max' hne, by
    simp only [hN, mem_filter, mem_univ, true_and, above_max' γ hne]; exact hq⟩
  set a₁ := N.min' hNne with ha₁
  have ha₁N : a₁ ∈ N := min'_mem N hNne
  have ha₁lt : above γ a₁ < q := (mem_filter.1 ha₁N).2
  -- the sign lemma
  have hsign : ∀ a, 0 ≤ (Q.mass a - p.mass a) * (U a - U a₁) := by
    intro a
    rcases lt_trichotomy a a₁ with h | h | h
    · -- below `a₁`: empty atom, `U ≤ u₀`
      have hnot : a ∉ N := fun haN => absurd (min'_le N a haN) (not_le.mpr h)
      have hemp : q ≤ above γ a := by
        by_contra hc; exact hnot (mem_filter.2 ⟨mem_univ a, not_le.mp hc⟩)
      have hQ0 : Q.mass a = 0 := qmass_of_le_above γ hemp
      rw [hQ0, zero_sub]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (p.nonneg a))
        (sub_nonpos.mpr (hU a a₁ h))
    · rw [h, sub_self, mul_zero]
    · -- above `a₁`: full atom, `U ≥ u₀`
      have hfull : aboveEq γ a ≤ q := (aboveEq_le_above_of_lt γ h).trans ha₁lt.le
      have hQa : Q.mass a = γ.mass a / q := qmass_of_aboveEq_le γ hfull
      rw [hQa]
      exact mul_nonneg (sub_nonneg.mpr (hp a)) (sub_nonneg.mpr (hU a₁ a h))
  have hsum : 0 ≤ ∑ a, (Q.mass a - p.mass a) * (U a - U a₁) := sum_nonneg fun a _ => hsign a
  have hexp : ∑ a, (Q.mass a - p.mass a) * (U a - U a₁) = expect Q U - expect p U := by
    unfold expect
    have h1 : ∑ a, (Q.mass a - p.mass a) * (U a - U a₁)
        = ∑ a, Q.mass a * U a - ∑ a, p.mass a * U a - U a₁ * (∑ a, Q.mass a - ∑ a, p.mass a) := by
      simp only [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [h1, Q.sum_eq_one, p.sum_eq_one, sub_self, mul_zero, sub_zero]
  linarith

/-- **Taylor 2016, Theorem 1 as stated:** with `q = 1/t`, the `q`-quantilizer maximizes expected
`U` among all `p` satisfying constraint (2) at level `t` (Lemma 2 then Theorem 1).
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Theorem 1 (l. 114–118)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem quantilize_optimal_of_constraint (γ : Distr A) {t : ℝ} (ht : 1 ≤ t) (U : A → ℝ)
    (hU : Compatible U) (p : Distr A)
    (h : ∀ c : A → ℝ, (∀ a, 0 ≤ c a) → expect γ c ≤ 1 → expect p c ≤ t) :
    expect p U ≤ expect (quantilize γ (1 / t) (by positivity) (by
      rw [div_le_one (by positivity)]; exact ht)) U := by
  refine quantilize_optimal γ _ _ U hU p fun a => ?_
  rw [div_div_eq_mul_div, div_one, mul_comm]
  exact fits_under_base γ p t h a

/-! ### Tie-break independence -/

/-- **Tie-break independence (stretch).** Two tie-breaks compatible with the same `U` may give
different quantilizers (a tie can be resolved either way), but the *expected `U`* is the same:
each is optimal (Theorem 1) among distributions under the cap, and each satisfies the cap
(Lemma 1), so each bounds the other.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 l. 75 ("this notation is imprecise")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem quantilize_expect_tiebreak_indep (o₁ o₂ : LinearOrder A) (γ : Distr A) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (U : A → ℝ) (hU₁ : @Compatible A o₁ U) (hU₂ : @Compatible A o₂ U) :
    expect (@quantilize A _ o₁ γ q hq hq1) U = expect (@quantilize A _ o₂ γ q hq hq1) U := by
  apply le_antisymm
  · exact @quantilize_optimal A _ o₂ γ q hq hq1 U hU₂ (@quantilize A _ o₁ γ q hq hq1)
      (fun a => @qmass_le A _ o₁ γ q hq a)
  · exact @quantilize_optimal A _ o₁ γ q hq hq1 U hU₁ (@quantilize A _ o₂ γ q hq hq1)
      (fun a => @qmass_le A _ o₂ γ q hq a)

end Quantilizer

end Cleanroom.Corrigibility.CorrCautionPower
