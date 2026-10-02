import Cleanroom.Lit.LitDdbAccuracyMm.Rules

/-!
# Theorem 3.2 (⟸): the witness rule (Target 6), and the failure-interval lemma (Target 1)

If `π` does not totally trust `P` with respect to `X`, some gsp, value-directed, continuous rule
has `E_π(I_X(e)) < E_π(I_X(P))`. Route (integral-free, from the mandate, verified here):

1. **WLOG the failure is clause 1 at a threshold above `e`** (`exists_upper_failure`): a clause-1
   failure at `t₀ ≤ e` forces a clause-2 failure at the largest attained estimate below `t₀`
   (`clause2_fail_of_clause1_fail_le`), and `X ↦ −X` turns clause-2 failures into clause-1
   failures above `−e`.
2. **The interval** (`failure_data`): with `U := [E(X) ≥ t₀]`, `m := π(U) > 0`,
   `S := ∑_U π X < t₀ m`, take `β := min {E_w(X) : w ∈ U}` (so `[E(X) ≥ β] = U`) and `α`
   strictly between `max(e, S/m, max_{w ∉ U} E_w(X))` and `β`: then `e ≤ α`, no attained
   estimate lies in `(α, β)`, and `S < α m`. (DDB's open interval `(α, β)` at l. 710 would allow
   an attained `a_j = β` and gives only `≤ α`; the closed choice repairs 2-015 (ii).)
3. **The inequality** (`exists_ruleC_witness`): for `I := ruleC α β C`,
   `E_π(I_X(P)) − E_π(I_X(e)) = A + (C − 1)·B` with `A` free of `C` and
   `B = (β − α)((α + β) m − 2S) > 0` (DDB's (19) with `E_π(X | E(X) > β) = S/m`); the explicit
   `C := 1 + (|A| + 1)/B` makes it `≥ 1`.
4. The rule is gsp, value-directed and continuous by `Rules.lean` (`C ≥ 1`).
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Failures and the reflection `X ↦ −X` -/

/-- `∑_{w ∈ A} π w (X w − s) = ∑_A π X − s · π(A)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_mul_sub_eq (π X : W → ℝ) (A : Finset W) (s : ℝ) :
    ∑ w ∈ A, π w * (X w - s) = (∑ w ∈ A, π w * X w) - s * mass π A := by
  simp only [mass, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro w _
  ring

/-- `[E(−X) ≥ −s] = [E(X) ≤ s]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem estEvent_neg (F : Frame W) (X : W → ℝ) (s : ℝ) :
    F.estEvent (-X) (-s) = F.estEventLE X s := by
  ext w
  simp only [Frame.mem_estEvent, Frame.mem_estEventLE, E_neg_right]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- The clause-2 sum of `X` at `s` is minus the clause-1 sum of `−X` at `−s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem neg_event_sum (F : Frame W) (π X : W → ℝ) (s : ℝ) :
    ∑ w ∈ F.estEvent (-X) (-s), π w * ((-X) w - -s) =
      -∑ w ∈ F.estEventLE X s, π w * (X w - s) := by
  rw [estEvent_neg, ← sum_neg_distrib]
  apply sum_congr rfl
  intro w _
  simp only [Pi.neg_apply]
  ring

/-- Not totally trusting with respect to `X` is a clause-1 failure or a clause-2 failure at some
real threshold (event-sum form).
Source: none: infrastructure (Target 1)
Kind: L
Fidelity: n/a -/
theorem not_totalTrustOn_iff {X π : W → ℝ} {F : Frame W} :
    ¬ TotalTrustOn X π F ↔
      (∃ t, ∑ w ∈ F.estEvent X t, π w * (X w - t) < 0) ∨
      (∃ t, 0 < ∑ w ∈ F.estEventLE X t, π w * (X w - t)) := by
  unfold TotalTrustOn
  simp only [totalTrust_sum_eq, totalTrust_dual_sum_eq, not_and_or, not_forall, not_le]

/-- **Reduction.** A clause-1 failure at `t₀ ≤ E_π(X)` forces a clause-2 failure at some `a < t₀`
(the largest attained estimate below `t₀`): the complement `[E(X) < t₀]` then carries
`∑ π X > t₀ · π(·)`.
Source: none: infrastructure (mandate Target 1, "my derivation", verified here)
Kind: L
Fidelity: n/a -/
theorem clause2_fail_of_clause1_fail_le {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    {t₀ : ℝ} (ht : t₀ ≤ E π X) (hfail : ∑ w ∈ F.estEvent X t₀, π w * (X w - t₀) < 0) :
    ∃ a, a < t₀ ∧ 0 < ∑ w ∈ F.estEventLE X a, π w * (X w - a) := by
  set U := F.estEvent X t₀ with hU
  set Uc := univ \ U with hUc
  have hsplit : ∀ f : W → ℝ, ∑ w ∈ U, f w + ∑ w ∈ Uc, f w = ∑ w, f w := by
    intro f
    rw [hUc, add_comm, sum_sdiff (subset_univ U)]
  have hc : 0 < ∑ w ∈ Uc, π w * (X w - t₀) := by
    have h1 := hsplit (fun w => π w * (X w - t₀))
    have h2 : ∑ w, π w * (X w - t₀) = E π X - t₀ := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hπ.2, one_mul, E]
    linarith
  have hUcne : Uc.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hc
    exact lt_irrefl _ hc
  obtain ⟨wa, hwa, hmax⟩ := Uc.exists_max_image (fun w => E (F.P w) X) hUcne
  set a := E (F.P wa) X with ha
  have hwa' : ¬ t₀ ≤ E (F.P wa) X := by
    have := (mem_sdiff.1 hwa).2
    simpa [hU, Frame.mem_estEvent] using this
  have hat : a < t₀ := not_le.1 hwa'
  have hev : F.estEventLE X a = Uc := by
    ext w
    simp only [Frame.mem_estEventLE, hUc, mem_sdiff, mem_univ, true_and, hU, Frame.mem_estEvent]
    constructor
    · intro h; linarith
    · intro h
      exact hmax w (by simp [hUc, hU, Frame.mem_estEvent, h])
  refine ⟨a, hat, ?_⟩
  rw [hev, sum_mul_sub_eq]
  rw [sum_mul_sub_eq] at hc
  have hm : 0 ≤ mass π Uc := mass_nonneg hπ.1 _
  nlinarith

/-- **WLOG.** If `π` does not totally trust `P` with respect to `X`, then for `Y = X` or
`Y = −X` clause 1 fails at some threshold strictly above `E_π(Y)`.
Source: none: infrastructure (mandate Target 1)
Kind: L
Fidelity: n/a -/
theorem exists_upper_failure {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : ¬ TotalTrustOn X π F) :
    ∃ Y : W → ℝ, (Y = X ∨ Y = -X) ∧
      ∃ t₀, E π Y < t₀ ∧ ∑ w ∈ F.estEvent Y t₀, π w * (Y w - t₀) < 0 := by
  rcases not_totalTrustOn_iff.1 h with ⟨t₀, h1⟩ | ⟨t₀, h2⟩
  · rcases lt_or_ge (E π X) t₀ with hlt | hle
    · exact ⟨X, Or.inl rfl, t₀, hlt, h1⟩
    · obtain ⟨a, hat, ha⟩ := clause2_fail_of_clause1_fail_le hπ hle h1
      refine ⟨-X, Or.inr rfl, -a, ?_, ?_⟩
      · rw [E_neg_right]; linarith
      · rw [neg_event_sum]; linarith
  · rcases lt_or_ge (E π (-X)) (-t₀) with hlt | hle
    · refine ⟨-X, Or.inr rfl, -t₀, hlt, ?_⟩
      rw [neg_event_sum]; linarith
    · have h2' : ∑ w ∈ F.estEvent (-X) (-t₀), π w * ((-X) w - -t₀) < 0 := by
        rw [neg_event_sum]; linarith
      obtain ⟨a, hat, ha⟩ := clause2_fail_of_clause1_fail_le hπ hle h2'
      refine ⟨X, Or.inl rfl, -a, ?_, ?_⟩
      · rw [E_neg_right] at hle; linarith
      · have := neg_event_sum F π (-X) a
        rw [neg_neg] at this
        rw [this]; linarith

/-! ## The failure interval -/

/-- **The interval `(α, β]` of a clause-1 failure above `e`.** Given a clause-1 failure at
`t₀ > E_π(X)`, there are `α < β` with: `E_π(X) ≤ α`; `U := [E(X) ≥ β]` has positive mass;
every attained estimate off `U` is `≤ α` (so no attained estimate lies in `(α, β)`, and
`[E(X) ≥ t] = U` for every `t ∈ (α, β]`); and `∑_U π X < α · π(U)` (so clause 1 fails at every
`t ∈ (α, β]`, and `(α + β) π(U) > 2 ∑_U π X`, which the witness rule needs).
Source: [[Deference Done Better]] App. B l. 710–714 (the choice of `(α, β)`), Lemma 7.10 (3)–(4)
l. 780; mandate Target 6(iv) (the repair of 2-015 (ii))
Kind: P
Fidelity: stronger: closed interval `(α, β]`, `e ≤ α`, no attained estimate in `(α, β)`
Hyps: (a) none -/
theorem failure_data {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} {t₀ : ℝ}
    (ht : E π X < t₀) (hfail : ∑ w ∈ F.estEvent X t₀, π w * (X w - t₀) < 0) :
    ∃ α β : ℝ, α < β ∧ E π X ≤ α ∧ 0 < mass π (F.estEvent X β) ∧
      (∀ w, w ∉ F.estEvent X β → E (F.P w) X ≤ α) ∧
      ∑ w ∈ F.estEvent X β, π w * X w < α * mass π (F.estEvent X β) := by
  set U := F.estEvent X t₀ with hU
  set m := mass π U with hm_def
  set S := ∑ w ∈ U, π w * X w with hS_def
  have hSm : S < t₀ * m := by
    rw [sum_mul_sub_eq] at hfail
    linarith
  have hm : 0 < m := by
    rcases (mass_nonneg hπ.1 U).lt_or_eq with h | h
    · exact h
    · exfalso
      have := sum_eq_zero_of_mass_eq_zero hπ.1 h.symm (fun w => X w - t₀)
      linarith
  have hUne : U.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : m = 0 := by rw [hm_def, h]; simp [mass]
    linarith
  obtain ⟨wβ, hwβU, hwβmin⟩ := U.exists_min_image (fun w => E (F.P w) X) hUne
  set β := E (F.P wβ) X with hβ
  have ht₀β : t₀ ≤ β := Frame.mem_estEvent.1 hwβU
  have hUβ : F.estEvent X β = U := by
    ext w
    simp only [Frame.mem_estEvent]
    constructor
    · intro h; exact Frame.mem_estEvent.2 (le_trans ht₀β h)
    · intro h; exact hwβmin w h
  set T : Finset ℝ :=
    insert (E π X) (insert (S / m) ((univ \ U).image (fun w => E (F.P w) X))) with hT
  have hTne : T.Nonempty := insert_nonempty _ _
  set α₀ := T.max' hTne with hα₀
  have hα₀β : α₀ < β := by
    rw [hα₀, Finset.max'_lt_iff]
    intro x hx
    simp only [hT, mem_insert, mem_image, mem_sdiff, mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨w, hw, rfl⟩
    · linarith
    · rw [div_lt_iff₀ hm]; nlinarith
    · have : ¬ t₀ ≤ E (F.P w) X := by simpa [hU, Frame.mem_estEvent] using hw
      linarith [not_le.1 this]
  set α := (α₀ + β) / 2 with hα
  have hα₀α : α₀ < α := by rw [hα]; linarith
  have hαβ : α < β := by rw [hα]; linarith
  refine ⟨α, β, hαβ, ?_, ?_, ?_, ?_⟩
  · have : E π X ≤ α₀ := le_max' T _ (by simp [hT])
    linarith
  · rw [hUβ]; exact hm
  · intro w hw
    rw [hUβ] at hw
    have : E (F.P w) X ≤ α₀ := by
      apply le_max' T _
      simp only [hT, mem_insert, mem_image, mem_sdiff, mem_univ, true_and]
      exact Or.inr (Or.inr ⟨w, hw, rfl⟩)
    linarith
  · rw [hUβ]
    have h1 : S / m ≤ α₀ := le_max' T _ (by simp [hT])
    have h2 : S / m < α := by linarith
    rwa [div_lt_iff₀ hm] at h2

/-- **Target 1, the failure-interval lemma** (Lemma 7.10 (3)–(4), strengthened): if `π` does not
totally trust `P` with respect to `X`, there is a nondegenerate closed interval `[x, y]` on
which clause 1 fails throughout, or one on which clause 2 fails throughout.
Source: [[Deference Done Better]] App. B Lemma 7.10 (3)–(4) l. 780
Kind: P
Fidelity: exact (closed interval as in the statement of 7.10)
Hyps: (a) none -/
theorem exists_failure_interval {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : ¬ TotalTrustOn X π F) :
    ∃ x y : ℝ, x < y ∧
      ((∀ t, x ≤ t → t ≤ y → ∑ w ∈ F.estEvent X t, π w * (X w - t) < 0) ∨
       (∀ t, x ≤ t → t ≤ y → 0 < ∑ w ∈ F.estEventLE X t, π w * (X w - t))) := by
  -- the clause-1 interval for a variable `Y` with an upper failure
  have core : ∀ Y : W → ℝ, ∀ t₀, E π Y < t₀ →
      ∑ w ∈ F.estEvent Y t₀, π w * (Y w - t₀) < 0 →
      ∃ x y : ℝ, x < y ∧ ∀ t, x ≤ t → t ≤ y → ∑ w ∈ F.estEvent Y t, π w * (Y w - t) < 0 := by
    intro Y t₀ ht hfail
    obtain ⟨α, β, hαβ, _, hm, hout, hS⟩ := failure_data hπ ht hfail
    refine ⟨(α + β) / 2, β, by linarith, ?_⟩
    intro t hxt hty
    have hev : F.estEvent Y t = F.estEvent Y β := by
      ext w
      simp only [Frame.mem_estEvent]
      constructor
      · intro hw
        by_contra hcon
        have := hout w (by simpa [Frame.mem_estEvent] using hcon)
        linarith
      · intro hw; linarith
    rw [hev, sum_mul_sub_eq]
    have : α * mass π (F.estEvent Y β) ≤ t * mass π (F.estEvent Y β) :=
      mul_le_mul_of_nonneg_right (by linarith) hm.le
    linarith
  obtain ⟨Y, hY, t₀, ht, hfail⟩ := exists_upper_failure hπ h
  rcases hY with rfl | rfl
  · obtain ⟨x, y, hxy, hint⟩ := core Y t₀ ht hfail
    exact ⟨x, y, hxy, Or.inl hint⟩
  · obtain ⟨x, y, hxy, hint⟩ := core (-X) t₀ ht hfail
    refine ⟨-y, -x, by linarith, Or.inr ?_⟩
    intro t hyt htx
    have := hint (-t) (by linarith) (by linarith)
    rw [show (-t) = -t from rfl, neg_event_sum] at this
    linarith

/-! ## The witness rule -/

/-- **The witness inequality.** For a clause-1 failure at `t₀ > E_π(X)` there are `α < β` and an
explicit `C ≥ 1` with `E_π(I_X(e)) < E_π(I_X(P))` for DDB's six-case rule `I := ruleC α β C`:
`E_π(I_X(P)) − E_π(I_X(e)) = A + (C − 1)·B` with `B = (β − α)((α + β) π(U) − 2 ∑_U π X) > 0`.
Source: [[Deference Done Better]] App. B l. 730–748 (eqs. (11)–(19)); mandate Target 6(v)
Kind: P
Fidelity: exact (with the explicit `C := 1 + (|A| + 1)/B`)
Hyps: (a) none -/
theorem exists_ruleC_witness {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} {t₀ : ℝ}
    (ht : E π X < t₀) (hfail : ∑ w ∈ F.estEvent X t₀, π w * (X w - t₀) < 0) :
    ∃ α β C : ℝ, α < β ∧ 1 ≤ C ∧
      expInacc π X (ruleC α β C) (E π X) < expInaccP π F X (ruleC α β C) := by
  obtain ⟨α, β, hαβ, heα, hm, hout, hS⟩ := failure_data hπ ht hfail
  set U := F.estEvent X β with hU
  set e := E π X with he
  set A := ∑ w, π w * ((E (F.P w) X - X w) ^ 2 - (e - X w) ^ 2) with hA
  set B := ∑ w, π w * ((clamp α β (E (F.P w) X) - X w) ^ 2 - (clamp α β e - X w) ^ 2) with hB
  have hΔ : ∀ C, expInaccP π F X (ruleC α β C) - expInacc π X (ruleC α β C) e =
      A + (C - 1) * B := by
    intro C
    rw [expInaccP_sub_expInacc, hA, hB, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro w _
    simp only [ruleC, mixRule, clampTerm]
    ring
  have hce : clamp α β e = α := clamp_eq_left heα
  have hBU : B = ∑ w ∈ U, π w * ((β - X w) ^ 2 - (α - X w) ^ 2) := by
    rw [hB, hce, ← sum_filter_add_sum_filter_not univ (fun w => w ∈ U)]
    have h1 : univ.filter (fun w => w ∈ U) = U := by ext w; simp
    have h2 : ∑ w ∈ univ.filter (fun w => ¬ w ∈ U),
        π w * ((clamp α β (E (F.P w) X) - X w) ^ 2 - (α - X w) ^ 2) = 0 := by
      apply sum_eq_zero
      intro w hw
      have hw' : w ∉ U := (mem_filter.1 hw).2
      rw [clamp_eq_left (hout w hw')]
      ring
    rw [h1, h2, add_zero]
    apply sum_congr rfl
    intro w hw
    rw [clamp_eq_right hαβ.le (Frame.mem_estEvent.1 hw)]
  have hBval : B = (β - α) * ((α + β) * mass π U - 2 * ∑ w ∈ U, π w * X w) := by
    rw [hBU]
    have : ∀ w, π w * ((β - X w) ^ 2 - (α - X w) ^ 2) =
        (β - α) * (α + β) * π w - (β - α) * 2 * (π w * X w) := by
      intro w; ring
    simp only [this]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
    simp only [mass]
    ring
  have hBpos : 0 < B := by
    rw [hBval]
    apply mul_pos (by linarith)
    have : ∑ w ∈ U, π w * X w < β * mass π U :=
      lt_of_lt_of_le hS (mul_le_mul_of_nonneg_right hαβ.le hm.le)
    linarith
  refine ⟨α, β, 1 + (|A| + 1) / B, hαβ, ?_, ?_⟩
  · have : 0 ≤ (|A| + 1) / B := div_nonneg (by positivity) hBpos.le
    linarith
  · have h := hΔ (1 + (|A| + 1) / B)
    have h2 : (1 + (|A| + 1) / B - 1) * B = |A| + 1 := by
      rw [add_sub_cancel_left, div_mul_cancel₀ _ hBpos.ne']
    rw [h2] at h
    have hA1 : -A ≤ |A| := neg_le_abs A
    have hA2 : 0 < A + (|A| + 1) := by linarith
    linarith

/-- **Theorem 3.2 (⟸).** If `π` does not totally trust `P` with respect to `X`, some gsp,
value-directed rule, continuous in the estimate, has `E_π(I_X(π)) < E_π(I_X(P))` — so `π` does
not epistemically value `P` with respect to `X`. The rule is DDB's six-case rule (or its
reflection), and its gsp-ness is *proved* (`Rules.lean`), not left to the reader.
Source: [[Deference Done Better]] §3 Theorem 3.2 l. 273, App. B l. 706–748; items 077, 2-015
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_gsp_rule_of_not_totalTrustOn {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    {F : Frame W} (h : ¬ TotalTrustOn X π F) :
    ∃ I : Rule, IsGsp X I ∧ ValueDirected X I ∧ (∀ k, Continuous (fun x => I x k)) ∧
      expInacc π X I (E π X) < expInaccP π F X I := by
  obtain ⟨Y, hY, t₀, ht, hfail⟩ := exists_upper_failure hπ h
  obtain ⟨α, β, C, hαβ, hC, hlt⟩ := exists_ruleC_witness hπ ht hfail
  rcases hY with rfl | rfl
  · exact ⟨ruleC α β C, isGsp_ruleC hαβ.le hC Y, valueDirected_ruleC hαβ.le hC Y,
      continuous_ruleC α β C, hlt⟩
  · refine ⟨(ruleC α β C).neg, ?_, ?_, ?_, ?_⟩
    · have := (isGsp_ruleC hαβ.le hC (-X)).neg
      rwa [neg_neg] at this
    · have := (valueDirected_ruleC hαβ.le hC (-X)).neg
      rwa [neg_neg] at this
    · exact Rule.neg_continuous (continuous_ruleC α β C)
    · have h1 := expInacc_neg π (-X) (ruleC α β C) (E π X)
      have h2 := expInaccP_neg π F (-X) (ruleC α β C)
      rw [neg_neg] at h1 h2
      rw [h1, h2, ← E_neg_right]
      exact hlt

end

end Cleanroom.Lit.LitDdbAccuracyMm
