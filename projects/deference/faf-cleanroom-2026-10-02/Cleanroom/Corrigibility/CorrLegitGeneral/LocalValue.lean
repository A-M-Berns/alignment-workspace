import Cleanroom.Corrigibility.CorrLegitGeneral.Transfer
import Cleanroom.Lit.LitDdbAccuracyMm.Basic

/-!
# corr-legit-general — T4(a)–(b): local Value ⟹ local Total Trust; the two-cell question

* T4(a): `ValuesWrt Q π F → TotalTrustWrt Q π F` (fn 65's "true and easy" direction): the menu
  `{X, const s}` of a `Q`-measurable `X` is `Q`-measurable, `Frame.twoOption` is recommended
  for it, and `stratValue_twoOption` is the product form of Total Trust.
* T4(b), the Total-Trust half: `TotalTrustWrt (questionOf q) π F ↔ SimpleTrustOn q π F` — a
  `{q, ¬q}`-measurable variable is `β + b·𝟙_q`; splitting on the sign of `b` turns the
  threshold inequality into the above-threshold (`b > 0`) or below-threshold (`b < 0`) cut of
  Simple Trust at `(s − β)/b`. Hence DDB §5 l. 398: Total Trust w.r.t. every two-cell
  question ⟺ Simple Trust.
* T4(b), the Value half: `ValuesWrt (questionOf q) π F → SimpleTrustOn q π F` by (a). **The
  converse, as DDB's fn 64 defines Value (every recommended strategy), is false**: two worlds
  with the same `P_w(q)` but different rows can be given opposite tie-breaks on a menu that
  ties at that probability (`WitnessesFn66.lean`, `tie4`; with full support,
  `WitnessesTieFull.lean`, `tieF`). The surviving neighbours are the weak
  form (`WeakValuesWrt`, some recommended strategy) and the form with rows determined by
  `P_w(q)` on the support (`TwoCell.lean`).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-! ## T4(a): local Value implies local Total Trust -/

/-- **Local Value implies local Total Trust** (fn 65, the "true and easy" direction): for a
`Q`-measurable `X` and threshold `s`, the menu `{X, const s}` is `Q`-measurable and
`Frame.twoOption X s` is recommended for it; Value gives `s = E_π(const s) ≤ E_π(S)`, and
`E_π(S) − s` is the product form of Total Trust at `(X, s)`.
Source: [[Deference Done Better]] fn 65 l. 1237 ("the same reasoning as that in Lemma 7.1");
fixpoint-lit-072; corr-wf14-034
Kind: P
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem valuesWrt_imp_totalTrustWrt {Q : W → C} {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    {F : Frame W} (h : ValuesWrt Q π F) : TotalTrustWrt Q π F := by
  intro X hX s
  have hmenu : ∀ o ∈ ({X, fun _ => s} : DecisionProblem W), MeasurableWrt Q o := by
    intro o ho
    simp only [mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl
    · exact hX
    · exact measurableWrt_const Q s
  have hval := h {X, fun _ => s} (insert_nonempty _ _) hmenu _ (F.twoOption_recommended X s)
    (fun _ => s) (by simp)
  rw [E_const hπ] at hval
  rw [← stratValue_twoOption hπ F X s]
  linarith

/-- **Legitimacy-conditioned local Value implies the local criterion of record.**
Source: [[legitimacy]] R5.1 l. 97; [[ddb]] I5.4 l. 130 ("right-to-left proved")
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L` -/
theorem legitValuesWrt_imp_legitTotalTrustWrt {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} {L : Finset W} (hL : 0 < mass π L) (h : LegitValuesWrt Q π F L) :
    LegitTotalTrustWrt Q π F L := by
  unfold LegitTotalTrustWrt
  unfold LegitValuesWrt at h
  rw [← totalTrustWrt_smul_iff (inv_pos.2 hL) Q]
  rw [← valuesWrt_smul_iff (inv_pos.2 hL) Q] at h
  exact valuesWrt_imp_totalTrustWrt (restrict_normalize_mem hπ hL) h

/-! ## The weak local form -/

/-- **Weak Value with respect to `Q`**: for every nonempty menu of `Q`-measurable options *some*
recommended strategy beats every fixed option. Globally Value and Weak Value coincide (DDB
Lemma 7.5, `value_iff_weakValue`); locally they can differ (`WitnessesFn66.lean`, `tie4`), which is
why fn 65's open direction is stated here in the weak form (`ThreeCell.lean`).
Source: [[Deference Done Better]] App. B l. 472 (Weak Value), fn 64 l. 1235 (the `Q`-relative
reading)
Kind: D
Fidelity: variant: fn 64's Value with "some recommended strategy" in place of "every" -/
def WeakValuesWrt (Q : W → C) (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ 𝒪 : DecisionProblem W, 𝒪.Nonempty → (∀ o ∈ 𝒪, MeasurableWrt Q o) →
    ∃ S, F.Recommended 𝒪 S ∧ ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- Local Value implies weak local Value (the informed strategy is recommended).
Source: [[Deference Done Better]] App. B §7.2 l. 571
Kind: L
Fidelity: exact -/
theorem ValuesWrt.weakValuesWrt {Q : W → C} {π : W → ℝ} {F : Frame W} (h : ValuesWrt Q π F) :
    WeakValuesWrt Q π F :=
  fun 𝒪 hne hm => ⟨F.informedStrategy 𝒪 hne, F.informedStrategy_recommended 𝒪 hne,
    h 𝒪 hne hm _ (F.informedStrategy_recommended 𝒪 hne)⟩

/-- Weak Value with respect to the finest question is weak Value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem weakValue_iff_weakValuesWrt_id {π : W → ℝ} {F : Frame W} :
    WeakValue π F ↔ WeakValuesWrt (id : W → W) π F :=
  ⟨fun h 𝒪 hne _ => h 𝒪 hne, fun h 𝒪 hne => h 𝒪 hne (fun o _ => measurableWrt_id o)⟩

/-! ## T4(b): the two-cell question -/

/-- A `{q, ¬q}`-measurable variable is affine in the indicator: `X = β + b · 𝟙_q`.
Source: [[ddb-mm-authors]] C5 l. 95 ("every `Q`-measurable option is two-valued")
Kind: L
Fidelity: exact -/
theorem exists_affine_of_measurableWrt_questionOf {q : Finset W} {X : W → ℝ}
    (hX : MeasurableWrt (questionOf q) X) : ∃ β b : ℝ, ∀ w, X w = β + b * ind q w := by
  classical
  let β : ℝ := if h : ∃ w, w ∉ q then X h.choose else 0
  let α : ℝ := if h : ∃ w, w ∈ q then X h.choose else 0
  refine ⟨β, α - β, fun w => ?_⟩
  by_cases hw : w ∈ q
  · have hex : ∃ v, v ∈ q := ⟨w, hw⟩
    have hXw : X w = α := by
      simp only [α, dif_pos hex]
      exact hX w _ (by simp [questionOf, hw, hex.choose_spec])
    simp [ind, hw, hXw]
  · have hex : ∃ v, v ∉ q := ⟨w, hw⟩
    have hXw : X w = β := by
      simp only [β, dif_pos hex]
      exact hX w _ (by simp [questionOf, hw, hex.choose_spec])
    simp [ind, hw, hXw]

/-- Expectation of an affine function of the indicator under a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_affine_ind {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (q : Finset W) (β b : ℝ) :
    E ρ (fun w => β + b * ind q w) = β + b * mass ρ q := by
  have e : (fun w => β + b * ind q w) = (fun _ => β) + b • ind q := by
    funext w; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e, E_add_right, E_const hρ, E_smul_right, E_ind]

/-- **Two cells, the Total-Trust half**: Total Trust with respect to `{q, ¬q}` is the pair of
Simple-Trust cuts at `q` (`SimpleTrustOn q`: above-threshold `t · π(P(q) ≥ t) ≤ π(q ∧ P(q) ≥ t)`
and below-threshold `π(q ∧ P(q) ≤ t) ≤ t · π(P(q) ≤ t)`, for every real `t`). A
`{q,¬q}`-measurable `X` is `β + b·𝟙_q`; for `b > 0` the threshold inequality at `(X, s)` is
`b` times the above cut at `(s − β)/b`, for `b < 0` it is `b` times the below cut, and for
`b = 0` it is trivial.
Source: [[Deference Done Better]] §5 l. 398; [[ddb-mm-authors]] C5 l. 95; fixpoint-lit-073;
corr-wf13-2-061
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` (used only for `b = 0`) -/
theorem totalTrustWrt_questionOf_iff {q : Finset W} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} : TotalTrustWrt (questionOf q) π F ↔ SimpleTrustOn q π F := by
  rw [simpleTrustOn_iff_totalTrustOn_ind]
  constructor
  · intro h
    exact (totalTrustWrt_iff_forall_totalTrustOn.1 h) (ind q) (measurableWrt_questionOf_ind q)
  · rintro ⟨h1, h2⟩ X hX s
    obtain ⟨β, b, hXe⟩ := exists_affine_of_measurableWrt_questionOf hX
    have hXf : X = fun w => β + b * ind q w := funext hXe
    subst hXf
    have hE : ∀ w, E (F.P w) (fun v => β + b * ind q v) = β + b * mass (F.P w) q :=
      fun w => E_affine_ind (F.P_mem w) q β b
    simp only [hE]
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · -- below-threshold cut at `t = (s − β)/b`, `b < 0`
      set t := (s - β) / b with ht
      have hb0 : b ≠ 0 := hb.ne
      have hbt : b * t = s - β := by rw [ht]; field_simp
      have key : ∀ w, π w * (β + b * ind q w - s) * (if s ≤ β + b * mass (F.P w) q then 1 else 0)
          = b * (π w * (ind q w - t) * (if E (F.P w) (ind q) ≤ t then 1 else 0)) := by
        intro w
        rw [E_ind]
        have hiff : (s ≤ β + b * mass (F.P w) q) ↔ (mass (F.P w) q ≤ t) := by
          rw [ht, le_div_iff_of_neg hb]
          constructor <;> intro h <;> linarith
        by_cases hc : mass (F.P w) q ≤ t
        · rw [if_pos (hiff.2 hc), if_pos hc]
          linear_combination (π w) * hbt
        · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]
          ring
      rw [sum_congr rfl (fun w _ => key w), ← mul_sum]
      exact mul_nonneg_of_nonpos_of_nonpos hb.le (h2 t)
    · simp only [zero_mul, add_zero]
      apply sum_nonneg
      intro w _
      split_ifs with hs
      · exact mul_nonneg (mul_nonneg (hπ w) (by linarith)) zero_le_one
      · simp
    · -- above-threshold cut at `t = (s − β)/b`, `b > 0`
      set t := (s - β) / b with ht
      have hb0 : b ≠ 0 := hb.ne'
      have hbt : b * t = s - β := by rw [ht]; field_simp
      have key : ∀ w, π w * (β + b * ind q w - s) * (if s ≤ β + b * mass (F.P w) q then 1 else 0)
          = b * (π w * (ind q w - t) * (if t ≤ E (F.P w) (ind q) then 1 else 0)) := by
        intro w
        rw [E_ind]
        have hiff : (s ≤ β + b * mass (F.P w) q) ↔ (t ≤ mass (F.P w) q) := by
          rw [ht, div_le_iff₀ hb]
          constructor <;> intro h <;> linarith
        by_cases hc : t ≤ mass (F.P w) q
        · rw [if_pos (hiff.2 hc), if_pos hc]
          linear_combination (π w) * hbt
        · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]
          ring
      rw [sum_congr rfl (fun w _ => key w), ← mul_sum]
      exact mul_nonneg hb.le (h1 t)

/-- The legitimacy-conditioned two-cell criterion is the pair of Simple-Trust cuts for the
restricted deferrer.
Source: [[legitimacy]] R5.3 l. 100 ("the binary shutdown question stands on proved ground")
Kind: L
Fidelity: exact -/
theorem legitTotalTrustWrt_questionOf_iff {q : Finset W} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} {L : Finset W} :
    LegitTotalTrustWrt (questionOf q) π F L ↔ SimpleTrustOn q (restrict π L) F :=
  totalTrustWrt_questionOf_iff (restrict_nonneg hπ L)

/-- **Two cells, the Value half that holds**: Value with respect to `{q, ¬q}` implies the
Simple-Trust cuts at `q` (by T4(a)). The converse is refuted (`WitnessesFn66.lean`, `tie4`) and
its surviving neighbours are in `TwoCell.lean`.
Source: [[Deference Done Better]] fn 65 l. 1237; [[ddb-mm-authors]] C5 l. 95
Kind: C
Fidelity: weaker: one direction of the sources' claimed equivalence; the other is refuted
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem valuesWrt_questionOf_imp_simpleTrustOn {q : Finset W} {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} (h : ValuesWrt (questionOf q) π F) :
    SimpleTrustOn q π F :=
  (totalTrustWrt_questionOf_iff hπ.1).1 (valuesWrt_imp_totalTrustWrt hπ h)

/-! ## DDB §5 l. 398: Total Trust w.r.t. every two-cell question ⟺ Simple Trust -/

/-- The complement of a proposition has the complementary probability under a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_compl {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (q : Finset W) :
    mass ρ qᶜ = 1 - mass ρ q := by
  have := mass_inter_add_mass_sdiff ρ univ q
  rw [univ_inter, mass_univ hρ, ← compl_eq_univ_sdiff] at this
  linarith

/-- `[P(q) ≤ t] = [P(¬q) ≥ 1 − t]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probEventLE_eq_probEvent_compl (F : Frame W) (q : Finset W) (t : ℝ) :
    probEventLE F q t = F.probEvent qᶜ (1 - t) := by
  ext w
  simp only [probEventLE, Frame.probEvent, mem_filter, mem_univ, true_and,
    mass_compl (F.P_mem w)]
  constructor <;> intro h <;> linarith

/-- The mass of `q ∧ A` is the mass of `A` less the mass of `¬q ∧ A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_eq_sub_compl (π : W → ℝ) (q A : Finset W) :
    mass π (q ∩ A) = mass π A - mass π (qᶜ ∩ A) := by
  have := mass_inter_add_mass_sdiff π A q
  have e : A \ q = qᶜ ∩ A := by
    ext w; simp only [mem_sdiff, mem_inter, mem_compl]; tauto
  rw [inter_comm, e] at this
  linarith

/-- The unguarded above cut follows from the guarded one when the deferrer is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem SimpleTrust.cut_unguarded {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : SimpleTrust π F) (q : Finset W) (t : ℝ) :
    t * mass π (F.probEvent q t) ≤ mass π (q ∩ F.probEvent q t) := by
  rcases (mass_nonneg hπ (F.probEvent q t)).lt_or_eq with hpos | hz
  · exact h q t hpos
  · have h1 : mass π (q ∩ F.probEvent q t) = 0 :=
      le_antisymm (hz ▸ mass_inter_le_right hπ q _) (mass_nonneg hπ _)
    rw [← hz, h1, mul_zero]

/-- **DDB §5 l. 398**: a deferrer totally trusts a frame with respect to every two-cell
question iff it simply trusts it. (⇒) each `q` gives the guarded above cut; (⇐) the above cut
of `q` is Simple Trust at `q`, and the below cut of `q` at `t` is the above cut of `¬q` at
`1 − t`.
Source: [[Deference Done Better]] §5 l. 398; mandate T4(b)
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem forall_totalTrustWrt_questionOf_iff_simpleTrust {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} :
    (∀ q : Finset W, TotalTrustWrt (questionOf q) π F) ↔ SimpleTrust π F := by
  simp only [totalTrustWrt_questionOf_iff hπ]
  constructor
  · intro h q t _
    exact (h q).1 t
  · intro h q
    refine ⟨fun t => SimpleTrust.cut_unguarded hπ h q t, fun t => ?_⟩
    have hc := SimpleTrust.cut_unguarded hπ h qᶜ (1 - t)
    rw [← probEventLE_eq_probEvent_compl] at hc
    rw [mass_inter_eq_sub_compl]
    linarith

end

end Cleanroom.Corrigibility.CorrLegitGeneral
