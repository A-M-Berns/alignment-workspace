import Cleanroom.Lit.LitDdbAccuracyMm.Monotone

/-!
# Theorem 3.2 (⟹): Total Trust with respect to `X` gives Epistemic Value (Target 5)

Rothschild's induction, in product form to avoid conditionals on null events. Let
`e := E_π(X)` and `T := {attained estimates a > e}`. For `a ∈ T` and `U_a := [E(X) ≥ a]`:

`Q a`: for every `s < a` with `min X ≤ s`, if `π(U_a) > 0` then
`∑_{w ∈ U_a} π w (I(E_w(X), X w) − I(s, X w)) < 0`.

Strong induction on the number of attained estimates above `a`. On `U_a` write
`I(E_w X, X w) − I(s, X w) = [I(E_w X, X w) − I(a, X w)] + [I(a, X w) − I(s, X w)]`: the second
bracket sums to `< 0` by Lemma 7.7 (lower clause) for the conditional `π(· | U_a)`, whose
estimate is `≥ a` by clause 1 of Total Trust (DDB's (8)); the first bracket vanishes on
`[E(X) = a]` and is `≤ 0` on `U_{a'}` (`a'` the next attained estimate) by the induction
hypothesis at `s := a` (DDB's (10)) — with `= 0`, not `< 0`, when `U_{a'}` is `π`-null (the case
the printed proof does not separate). The part of the frame below `e` is the same argument for
`(−X, I.neg)`; on `[E(X) = e]` both sides agree pointwise. Summing the three parts gives `≤`, with
strictness iff `π(E(X) ≠ e) > 0`, which is the equality clause of Epistemic Value.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The event `[E(X) > e]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def estGt (F : Frame W) (X : W → ℝ) (e : ℝ) : Finset W := univ.filter (fun w => e < E (F.P w) X)

/-- The event `[E(X) < e]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def estLt (F : Frame W) (X : W → ℝ) (e : ℝ) : Finset W := univ.filter (fun w => E (F.P w) X < e)

/-- **DDB's (8), product form.** On an event `U` of positive mass whose conditional estimate of
`X` is at least `a` (clause 1 of Total Trust at `a`, when `U = [E(X) ≥ a]`), the constant
estimate `a` beats every `s < a` with `min X ≤ s`: `∑_U π I(a, X) < ∑_U π I(s, X)`.
Source: [[Deference Done Better]] App. B l. 690 (eq. (8)), l. 686 (base case)
Kind: L
Fidelity: n/a -/
theorem step_ineq {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {I : Rule}
    (hmsp : MonotoneStrictlyProper X I) {U : Finset W} {a s : ℝ} (hm : 0 < mass π U)
    (hTT : 0 ≤ ∑ w ∈ U, π w * (X w - a)) (hs : s < a) (hrange : ∃ w, X w ≤ s) :
    ∑ w ∈ U, π w * I a (X w) < ∑ w ∈ U, π w * I s (X w) := by
  have hρ := condDist_mem_stdSimplex hπ.1 hm
  have hE : a ≤ E (condDist π U) X := by
    rw [E_condDist, le_div_iff₀ hm]
    have : ∑ w ∈ U, π w * (X w - a) = (∑ w ∈ U, π w * X w) - a * mass π U := by
      simp only [mass, mul_sub, sum_sub_distrib, mul_sum]
      congr 1
      apply sum_congr rfl; intro w _; ring
    linarith
  have h := (hmsp _ hρ s a hs).2 hE hrange
  rw [expInacc_condDist, expInacc_condDist, div_lt_div_iff_of_pos_right hm] at h
  exact h

/-- **The induction (DDB's (5)).** For every attained estimate `a > e` and every `s < a` with
`min X ≤ s`: if `π(E(X) ≥ a) > 0` then `∑_{[E(X) ≥ a]} π (I(E(X), X) − I(s, X)) < 0`.
Source: [[Deference Done Better]] App. B l. 680–700 (eqs. (5)–(10))
Kind: P
Fidelity: exact (equal estimates grouped; the null-`U_{a'}` case handled)
Hyps: (a) none -/
theorem induction_ineq {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (htt : TotalTrustOn X π F) {I : Rule} (hmsp : MonotoneStrictlyProper X I) :
    ∀ a, (∃ w, E (F.P w) X = a) → E π X < a →
      ∀ s, (∃ w, X w ≤ s) → s < a → 0 < mass π (F.estEvent X a) →
        ∑ w ∈ F.estEvent X a, π w * (I (E (F.P w) X) (X w) - I s (X w)) < 0 := by
  set T : Finset ℝ := (univ.image (fun w => E (F.P w) X)).filter (fun a => E π X < a) with hT
  have hmemT : ∀ a, a ∈ T ↔ (∃ w, E (F.P w) X = a) ∧ E π X < a := by
    intro a; simp [hT]
  -- strong induction on the number of attained estimates above `a`
  suffices key : ∀ n : ℕ, ∀ a ∈ T, (T.filter (fun b => a < b)).card = n →
      ∀ s, (∃ w, X w ≤ s) → s < a → 0 < mass π (F.estEvent X a) →
        ∑ w ∈ F.estEvent X a, π w * (I (E (F.P w) X) (X w) - I s (X w)) < 0 by
    intro a ha hea
    exact key _ a ((hmemT a).2 ⟨ha, hea⟩) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a haT hcard s hs hsa hm
  set U := F.estEvent X a with hU
  -- split the summand at the constant estimate `a`
  have hsplit : ∑ w ∈ U, π w * (I (E (F.P w) X) (X w) - I s (X w)) =
      ∑ w ∈ U, π w * (I (E (F.P w) X) (X w) - I a (X w)) +
      ∑ w ∈ U, π w * (I a (X w) - I s (X w)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro w _; ring
  have hsecond : ∑ w ∈ U, π w * (I a (X w) - I s (X w)) < 0 := by
    have := step_ineq hπ hmsp hm (htt.event_sum a) hsa hs
    simp only [mul_sub, sum_sub_distrib]
    linarith
  -- the first part: zero on `[E(X) = a]`, `≤ 0` on the next event
  have hfirst : ∑ w ∈ U, π w * (I (E (F.P w) X) (X w) - I a (X w)) ≤ 0 := by
    set B := T.filter (fun b => a < b) with hB
    have hea : E π X < a := ((hmemT a).1 haT).2
    -- every estimate attained on `U` lies in `T`
    have hUT : ∀ w ∈ U, E (F.P w) X ∈ T := by
      intro w hw
      rw [hmemT]
      exact ⟨⟨w, rfl⟩, lt_of_lt_of_le hea (Frame.mem_estEvent.1 hw)⟩
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · -- `a` is the largest attained estimate: the summand vanishes on `U`
      apply le_of_eq
      apply sum_eq_zero
      intro w hw
      have hwa : E (F.P w) X = a := by
        by_contra hne
        have hlt : a < E (F.P w) X := lt_of_le_of_ne (Frame.mem_estEvent.1 hw) (Ne.symm hne)
        have : E (F.P w) X ∈ B := mem_filter.2 ⟨hUT w hw, hlt⟩
        rw [hBe] at this
        exact absurd this (notMem_empty _)
      rw [hwa]; ring
    · obtain ⟨a', ha'B, ha'min⟩ := B.exists_min_image id hBne
      have ha'T : a' ∈ T := (mem_filter.1 ha'B).1
      have haa' : a < a' := (mem_filter.1 ha'B).2
      -- the induction hypothesis at `a'`
      have hcard' : (T.filter (fun b => a' < b)).card < n := by
        rw [← hcard]
        apply card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · intro b hb
          rw [mem_filter] at hb ⊢
          exact ⟨hb.1, lt_trans haa' hb.2⟩
        · intro heq
          have : a' ∈ T.filter (fun b => a' < b) := by rw [heq]; exact ha'B
          exact lt_irrefl _ (mem_filter.1 this).2
      have ih' := ih _ hcard' a' ha'T rfl
      set U' := F.estEvent X a' with hU'
      -- the summand vanishes on `U \ U'`
      have hsub : U' ⊆ U := by
        intro w hw
        rw [hU, Frame.mem_estEvent]
        exact le_trans haa'.le (Frame.mem_estEvent.1 hw)
      have hres : ∑ w ∈ U, π w * (I (E (F.P w) X) (X w) - I a (X w)) =
          ∑ w ∈ U', π w * (I (E (F.P w) X) (X w) - I a (X w)) := by
        symm
        apply sum_subset hsub
        intro w hw hw'
        have hwa : E (F.P w) X = a := by
          by_contra hne
          have hlt : a < E (F.P w) X := lt_of_le_of_ne (Frame.mem_estEvent.1 hw) (Ne.symm hne)
          have hB' : E (F.P w) X ∈ B := mem_filter.2 ⟨hUT w hw, hlt⟩
          have := ha'min _ hB'
          simp only [id] at this
          exact hw' (Frame.mem_estEvent.2 this)
        rw [hwa]; ring
      rw [hres]
      rcases (mass_nonneg hπ.1 U').lt_or_eq with hm' | hm'
      · obtain ⟨w₀, hw₀⟩ := hs
        exact (ih' a ⟨w₀, by linarith⟩ haa' hm').le
      · rw [sum_eq_zero_of_mass_eq_zero hπ.1 hm'.symm]
  rw [hsplit]
  linarith

/-- **The upper half (DDB's (3)).** Under Total Trust with respect to `X`, on `[E(X) > e]` the
expert's estimate is expected to be no more inaccurate than `e`, and strictly less so when the
event has positive mass.
Source: [[Deference Done Better]] App. B l. 676 (eq. (3)), l. 684 ("when `k = p` …")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem upper_half {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (htt : TotalTrustOn X π F) {I : Rule} (hg : IsGspOn X I) :
    ∑ w ∈ estGt F X (E π X), π w * (I (E (F.P w) X) (X w) - I (E π X) (X w)) ≤ 0 ∧
    (0 < mass π (estGt F X (E π X)) →
      ∑ w ∈ estGt F X (E π X), π w * (I (E (F.P w) X) (X w) - I (E π X) (X w)) < 0) := by
  have hmsp := monotoneStrictlyProper_of_isGspOn hg
  set e := E π X with he
  set T : Finset ℝ := (univ.image (fun w => E (F.P w) X)).filter (fun a => e < a) with hT
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · -- nothing above `e`
    have hG : estGt F X e = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      have : E (F.P w) X ∈ T := by
        simp only [hT, mem_filter, mem_image, mem_univ, true_and]
        exact ⟨⟨w, rfl⟩, (mem_filter.1 hw).2⟩
      rw [hTe] at this
      exact notMem_empty _ this
    rw [hG]
    simp [mass]
  · obtain ⟨a₀, ha₀T, ha₀min⟩ := T.exists_min_image id hTne
    have ha₀ : (∃ w, E (F.P w) X = a₀) ∧ e < a₀ := by
      simpa [hT] using ha₀T
    have hG : estGt F X e = F.estEvent X a₀ := by
      ext w
      simp only [estGt, mem_filter, mem_univ, true_and, Frame.mem_estEvent]
      constructor
      · intro hw
        have : E (F.P w) X ∈ T := by
          simp only [hT, mem_filter, mem_image, mem_univ, true_and]
          exact ⟨⟨w, rfl⟩, hw⟩
        simpa using ha₀min _ this
      · intro hw; linarith [ha₀.2]
    rw [hG]
    have hrange : ∃ w, X w ≤ e := exists_le_E hπ X
    constructor
    · rcases (mass_nonneg hπ.1 (F.estEvent X a₀)).lt_or_eq with hm | hm
      · exact (induction_ineq hπ htt hmsp a₀ ha₀.1 ha₀.2 e hrange ha₀.2 hm).le
      · rw [sum_eq_zero_of_mass_eq_zero hπ.1 hm.symm]
    · intro hm
      exact induction_ineq hπ htt hmsp a₀ ha₀.1 ha₀.2 e hrange ha₀.2 hm

/-- **The lower half (DDB's (4))**, by the upper half for `(−X, I.neg)`.
Source: [[Deference Done Better]] App. B l. 678 (eq. (4), "a symmetric argument")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem lower_half {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (htt : TotalTrustOn X π F) {I : Rule} (hg : IsGspOn X I) :
    ∑ w ∈ estLt F X (E π X), π w * (I (E (F.P w) X) (X w) - I (E π X) (X w)) ≤ 0 ∧
    (0 < mass π (estLt F X (E π X)) →
      ∑ w ∈ estLt F X (E π X), π w * (I (E (F.P w) X) (X w) - I (E π X) (X w)) < 0) := by
  have h := upper_half hπ htt.neg hg.neg
  have hset : estGt F (-X) (E π (-X)) = estLt F X (E π X) := by
    ext w
    simp only [estGt, estLt, mem_filter, mem_univ, true_and, E_neg_right]
    exact ⟨fun h => by linarith, fun h => by linarith⟩
  have hterm : ∀ w, π w * (I.neg (E (F.P w) (-X)) ((-X) w) - I.neg (E π (-X)) ((-X) w)) =
      π w * (I (E (F.P w) X) (X w) - I (E π X) (X w)) := by
    intro w
    simp [Rule.neg, E_neg_right]
  simp only [hset, hterm] at h
  exact h

/-- The three-way split of a sum over worlds by the sign of `E(X) − e`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_split_three (F : Frame W) (X : W → ℝ) (e : ℝ) (f : W → ℝ) :
    ∑ w, f w = ∑ w ∈ estGt F X e, f w + ∑ w ∈ estLt F X e, f w + ∑ w ∈ estEq F X e, f w := by
  rw [← sum_filter_add_sum_filter_not univ (fun w => e < E (F.P w) X) f]
  rw [← sum_filter_add_sum_filter_not (univ.filter (fun w => ¬ e < E (F.P w) X))
    (fun w => E (F.P w) X < e) f]
  have h1 : (univ.filter (fun w => ¬ e < E (F.P w) X)).filter (fun w => E (F.P w) X < e) =
      estLt F X e := by
    ext w
    simp only [mem_filter, mem_univ, true_and, estLt, not_lt]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have h2 : (univ.filter (fun w => ¬ e < E (F.P w) X)).filter (fun w => ¬ E (F.P w) X < e) =
      estEq F X e := by
    ext w
    simp only [mem_filter, mem_univ, true_and, estEq, not_lt]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.symm.le⟩⟩
  rw [h1, h2, estGt, add_assoc]

/-- **Theorem 3.2 (⟹), the inequality with its equality clause.** Under Total Trust with respect
to `X`, for every rule gsp on the value range: `E_π(I_X(P)) ≤ E_π(I_X(π))`, with equality iff
`π(E(X) = E_π(X)) = 1`. The class is larger than fn 47's (gsp at all real estimates), and no
value-directedness is assumed: Lemma 7.7 derives it on the range (`IsGspOn.valueDirectedOn`),
which is the only place the induction uses it.
Source: [[Deference Done Better]] §3 Theorem 3.2 l. 273, App. B l. 675–704, fn 48, glossary
l. 424; items 060, 2-014
Kind: C
Fidelity: stronger: gsp on the value range suffices (both the inequality and the "iff" equality
clause); value-indexed rules
Hyps: (a) none -/
theorem totalTrustOn_expInaccP_le {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (htt : TotalTrustOn X π F) {I : Rule} (hg : IsGspOn X I) :
    expInaccP π F X I ≤ expInacc π X I (E π X) ∧
    (expInaccP π F X I = expInacc π X I (E π X) ↔ mass π (estEq F X (E π X)) = 1) := by
  set e := E π X with he
  obtain ⟨hgt, hgt'⟩ := upper_half hπ htt hg
  obtain ⟨hlt, hlt'⟩ := lower_half hπ htt hg
  have hΔ := expInaccP_sub_expInacc π F X I e
  rw [sum_split_three F X e] at hΔ
  have heq : ∑ w ∈ estEq F X e, π w * (I (E (F.P w) X) (X w) - I e (X w)) = 0 := by
    apply sum_eq_zero
    intro w hw
    have : E (F.P w) X = e := (mem_filter.1 hw).2
    rw [this]; ring
  rw [heq, add_zero] at hΔ
  have hmass := sum_split_three F X e π
  rw [hπ.2] at hmass
  have hm1 : 0 ≤ mass π (estGt F X e) := mass_nonneg hπ.1 _
  have hm2 : 0 ≤ mass π (estLt F X e) := mass_nonneg hπ.1 _
  have hm3 : 0 ≤ mass π (estEq F X e) := mass_nonneg hπ.1 _
  simp only [mass] at hm1 hm2 hm3 hgt' hlt' ⊢
  constructor
  · linarith
  · constructor
    · intro h0
      -- both halves vanish, so both events are null
      have hg0 : ∑ w ∈ estGt F X e, π w * (I (E (F.P w) X) (X w) - I e (X w)) = 0 := by
        linarith
      have hl0 : ∑ w ∈ estLt F X e, π w * (I (E (F.P w) X) (X w) - I e (X w)) = 0 := by
        linarith
      have hmg : ∑ w ∈ estGt F X e, π w = 0 := by
        by_contra hne
        have := hgt' (lt_of_le_of_ne hm1 (Ne.symm hne))
        linarith
      have hml : ∑ w ∈ estLt F X e, π w = 0 := by
        by_contra hne
        have := hlt' (lt_of_le_of_ne hm2 (Ne.symm hne))
        linarith
      linarith
    · intro h1
      have hmg : ∑ w ∈ estGt F X e, π w = 0 := by linarith
      have hml : ∑ w ∈ estLt F X e, π w = 0 := by linarith
      have hg0 := sum_eq_zero_of_mass_eq_zero hπ.1 (A := estGt F X e) hmg
        (fun w => I (E (F.P w) X) (X w) - I e (X w))
      have hl0 := sum_eq_zero_of_mass_eq_zero hπ.1 (A := estLt F X e) hml
        (fun w => I (E (F.P w) X) (X w) - I e (X w))
      linarith

end

end Cleanroom.Lit.LitDdbAccuracyMm
