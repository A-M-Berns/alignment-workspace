import Cleanroom.Corrigibility.CorrLegitModif.Collapse
import Cleanroom.Corrigibility.CorrLegitGeneral.Betweenness
import Cleanroom.Corrigibility.CorrLegitGeneral.Transfer

/-!
# corr-legit-modif — T2(b), T3(b): separation under Total Trust on the P2 frame; the sign

[[approval-final]] S2/P2: on the two-signal frame `p2Frame (3/5) (2/5)` with the deferrer
`p2Def (1/2) (9/10) (1/5)` (masses `(9/20, 1/20, 1/10, 2/5)`, `p_P = 11/20`) and the menu
`{ind xq, const 13/25}`, `π` totally trusts the overseer on the `x`-question (`p2_instance`,
cited) yet does not reflect it (`π(x = 1 | H(x) = 3/5) = 9/10 ≠ 3/5`, new), the value learner
picks `ind xq` (`11/20 > 13/25`), the uninformed approval-directed agent picks the constant
(`E_π(R(ind xq)) = 1/2 < 13/25`), and the informed rule (continue on `s = 1`, stop on `s = 2`) is
worth `71/100`. The chain `13/25 ≤ 11/20 ≤ 71/100`: the first inequality is the argmax
definition, the second is local Value on this menu (`p2_valuesWrt_iff`, cited).

T3(b) (corr-wf14-2-048, A2.3): Total Trust does not fix the sign of `E_π U − E_π R`. The
identity `E_π U − E_π R = σ (p̂₁ − h₁) − (1 − σ)(h₂ − p̂₂)` on the P2 family shows the sign is the
difference of the two shrinkages; `p2Frame (3/5) (2/5)` gives `+1/20`, `p2Frame (9/10) (2/5)`
(betweenness `1/5 ≤ 2/5 ≤ 11/20 ≤ 9/10 ≤ 9/10`, Total Trust by `p2_totalTrustWrt_iff`) gives
`−1/10`. The source asserts the flip without an instance (Known issues 4); the second frame is one.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrLegitGeneral
  Cleanroom.Lit.LitDdbAccuracyMm Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

/-! ## The P2 instance -/

/-- The P2 deferrer `(9/20, 1/20, 1/10, 2/5)`.
Source: [[approval-final]] P2 l. 91
Kind: D
Fidelity: exact -/
abbrev πP2 : Fin 4 → ℝ := p2Def (1 / 2) (9 / 10) (1 / 5)

/-- The P2 overseer `p_H = (3/5, 2/5)`.
Source: [[approval-final]] P2 l. 91
Kind: D
Fidelity: exact -/
abbrev FP2 : Frame (Fin 4) := p2Frame (3 / 5) (2 / 5) (by norm_num) (by norm_num)

/-- The P2 menu `{U(a) = x, U(b) = 13/25}` (`0.52`).
Source: [[approval-final]] P2 l. 91 ("`U(a, ω) = x`, `U(b, ω) = 0.52`")
Kind: D
Fidelity: exact -/
def menuP2 : DecisionProblem (Fin 4) := {ind xq, fun _ => 13 / 25}

/-- The informed rule on P2: `ind xq` at the signal-1 worlds, the constant at the signal-2 worlds.
Source: [[approval-final]] P2 l. 91 ("informed AD picks `a` on `s = 1` and `b` on `s = 2`")
Kind: D
Fidelity: exact -/
def infP2 : Fin 4 → (Fin 4 → ℝ) := fun w => if w.val < 2 then ind xq else fun _ => 13 / 25

/-- The values of the two options under `π`: `11/20` and `13/25`.
Source: [[approval-final]] P2 l. 91
Kind: L
Fidelity: exact -/
theorem p2_E_options : E πP2 (ind xq) = 11 / 20 ∧ E πP2 (fun _ => 13 / 25) = 13 / 25 := by
  constructor <;> simp [E, Fin.sum_univ_four, p2Def, ind, xq, vec4_two, vec4_three] <;> norm_num

/-- The overseer's ratings: `R(ind xq) = (3/5, 3/5, 2/5, 2/5)`, `R(const) = const`.
Source: [[approval-final]] P2 l. 91
Kind: L
Fidelity: exact -/
theorem p2_rating (w : Fin 4) :
    rating FP2 (ind xq) w = (if w.val < 2 then 3 / 5 else 2 / 5) ∧
    rating FP2 (fun _ => 13 / 25) w = 13 / 25 := by
  constructor
  · unfold rating
    rw [E_ind, p2Frame_mass_xq]
  · exact E_const (FP2.P_mem w) _

/-- `E_π(R(ind xq)) = 1/2`.
Source: [[approval-final]] P2 l. 91 ("uninformed AD picks `b` (`½(0.6 + 0.4) = 0.5 < 0.52`)")
Kind: L
Fidelity: exact -/
theorem p2_E_rating : E πP2 (rating FP2 (ind xq)) = 1 / 2 := by
  simp only [E, Fin.sum_univ_four]
  simp only [(p2_rating _).1]
  simp [p2Def, vec4_two, vec4_three]; norm_num

/-- The two options are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2_options_ne : (ind xq : Fin 4 → ℝ) ≠ fun _ => 13 / 25 := by
  intro h
  have := congrFun h 0
  simp [ind, xq] at this
  norm_num at this

/-- `answer (questionOf xq) {true} = xq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem answer_sQ_true_p2 : answer (questionOf xq) {true} = xq := by
  ext w; simp [answer, questionOf]

/-- **Reflection fails on P2**: `π(x = 1 ∧ H(x) = 3/5) = 9/20 ≠ (1/2)(3/5) = π(H(x) = 3/5) · 3/5`
— the Reflection clause at the signal-1 row and the partial answer `x = 1`.
Source: [[approval-final]] P2 l. 91 ("Reflection fails (`E_P[x | H(x) = 0.6] = 0.9`)")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_not_reflectsWrt : ¬ ReflectsWrt (questionOf xq) πP2 FP2 := by
  intro h
  have hρ : FP2.P 0 ∈ FP2.cands πP2 := Frame.P_mem_cands _ (by norm_num [p2Def])
  have hcell : FP2.cell (FP2.P 0) = {0, 1} := by
    ext w
    simp only [Frame.mem_cell, p2Frame_P]
    fin_cases w <;> simp
  have := h _ hρ {true}
  rw [hcell, answer_sQ_true_p2] at this
  rw [p2Frame_P] at this
  simp [mass, p2Def, xq, vec4_two] at this
  norm_num at this

/-- **The value learner picks `a`**: `vlChoice = {ind xq}`.
Source: [[approval-final]] P2 l. 91 ("VL picks `a` (`0.55`)")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_vlChoice : vlChoice menuP2 πP2 = {ind xq} := by
  ext o
  rw [mem_maximizers, mem_singleton]
  obtain ⟨h1, h2⟩ := p2_E_options
  constructor
  · rintro ⟨ho, hmax⟩
    simp only [menuP2, mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl
    · rfl
    · have := hmax (ind xq) (by simp [menuP2])
      rw [h1, h2] at this; norm_num at this
  · rintro rfl
    refine ⟨by simp [menuP2], ?_⟩
    intro o' ho'
    simp only [menuP2, mem_insert, mem_singleton] at ho'
    rcases ho' with rfl | rfl
    · exact le_rfl
    · rw [h1, h2]; norm_num

/-- **The uninformed approval-directed agent picks `b`**: `adUninformed = {const 13/25}`.
Source: [[approval-final]] P2 l. 91 ("uninformed AD picks `b`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_adUninformed : adUninformed menuP2 πP2 FP2 = {fun _ => 13 / 25} := by
  ext o
  unfold adUninformed
  rw [mem_filter, mem_singleton]
  have hr : E πP2 (rating FP2 (fun _ => 13 / 25)) = 13 / 25 := by
    have : rating FP2 (fun _ => 13 / 25) = fun _ => 13 / 25 := funext (fun w => (p2_rating w).2)
    rw [this]; exact (p2_E_options).2
  constructor
  · rintro ⟨ho, hmax⟩
    simp only [menuP2, mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl
    · have := hmax (fun _ => 13 / 25) (by simp [menuP2])
      rw [hr, p2_E_rating] at this; norm_num at this
    · rfl
  · rintro rfl
    refine ⟨by simp [menuP2], ?_⟩
    intro o' ho'
    simp only [menuP2, mem_insert, mem_singleton] at ho'
    rcases ho' with rfl | rfl
    · rw [hr, p2_E_rating]; norm_num
    · exact le_rfl

/-- The informed rule is recommended: at the signal-1 worlds the overseer rates `ind xq` at
`3/5 > 13/25`, at the signal-2 worlds at `2/5 < 13/25`.
Source: [[approval-final]] P2 l. 91
Kind: L
Fidelity: exact -/
theorem infP2_recommended : FP2.Recommended menuP2 infP2 := by
  refine ⟨⟨fun w => ?_, fun w v e => ?_⟩, fun w o ho => ?_⟩
  · unfold infP2; split_ifs <;> simp [menuP2]
  · have : (w.val < 2) ↔ (v.val < 2) := by
      rw [p2Frame_P, p2Frame_P] at e
      constructor
      · intro hw; by_contra hv; rw [if_pos hw, if_neg hv] at e
        have := congrFun e 0; norm_num at this
      · intro hv; by_contra hw; rw [if_neg hw, if_pos hv] at e
        have := congrFun e 0; norm_num at this
    unfold infP2; simp only [this]
  · have hw := (p2_rating w).1
    have hc := (p2_rating w).2
    unfold rating at hw hc
    simp only [menuP2, mem_insert, mem_singleton] at ho
    unfold infP2
    rcases ho with rfl | rfl <;> split_ifs with hs <;>
      simp only [hs, if_true, if_false, Bool.false_eq_true] at hw <;> linarith [hw, hc]

/-- The informed rule is worth `71/100`.
Source: [[approval-final]] P2 l. 91 ("worth `0.71`")
Kind: L
Fidelity: exact -/
theorem infP2_value : stratValue πP2 infP2 = 71 / 100 := by
  simp [stratValue, Fin.sum_univ_four, infP2, p2Def, ind, xq, vec4_two, vec4_three]; norm_num

/-- **S2, separation under Total Trust on P2** (`separation_p2`): `π` totally trusts the
overseer with respect to the `x`-question, does not reflect it, the value learner's and the
uninformed approval-directed agent's choice sets differ (`{a}` against `{b}`), the informed rule
is worth `71/100`, and the chain `13/25 ≤ 11/20 ≤ 71/100` holds — the first inequality by the
argmax definition, the second by local Value (`p2_valuesWrt_iff`). Both `x`-cells have positive
mass (`11/20`, `9/20`) and the rows differ (`3/5 ≠ 2/5`), so the separation is not an artifact of
a constant overseer. "Total Trust on `𝒟` given `ℐ`" is read as `TotalTrustWrt` with the `x`-question
(Known issues 12); `TotalTrustOn` for the single option `ind xq` follows (`separation_p2_on`).
Source: [[approval-final]] S2 l. 53, P2 l. 91, P2′ l. 93; corr-wf14-115
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem separation_p2 :
    TotalTrustWrt (questionOf xq) πP2 FP2 ∧ ¬ ReflectsWrt (questionOf xq) πP2 FP2 ∧
    vlChoice menuP2 πP2 = {ind xq} ∧ adUninformed menuP2 πP2 FP2 = {fun _ => 13 / 25} ∧
    vlChoice menuP2 πP2 ≠ adUninformed menuP2 πP2 FP2 ∧
    FP2.Recommended menuP2 infP2 ∧ stratValue πP2 infP2 = 71 / 100 ∧
    E πP2 (fun _ => 13 / 25) ≤ E πP2 (ind xq) ∧ E πP2 (ind xq) ≤ stratValue πP2 infP2 ∧
    mass πP2 xq = 11 / 20 ∧ mass πP2 xqᶜ = 9 / 20 := by
  obtain ⟨-, hTT, hV, hm1, hm2⟩ := p2_instance
  refine ⟨hTT, p2_not_reflectsWrt, p2_vlChoice, p2_adUninformed, ?_, infP2_recommended,
    infP2_value, ?_, ?_, hm1, hm2⟩
  · rw [p2_vlChoice, p2_adUninformed]
    intro h
    have := singleton_inj.1 h
    exact p2_options_ne this
  · rw [(p2_E_options).1, (p2_E_options).2]; norm_num
  · exact domination_of_valuesWrt (𝒪 := menuP2) hV ⟨_, mem_insert_self _ _⟩
      (fun o ho => by
        simp only [menuP2, mem_insert, mem_singleton] at ho
        rcases ho with rfl | rfl
        · exact measurableWrt_questionOf_ind xq
        · exact measurableWrt_const _ _)
      (by show ind xq ∈ vlChoice menuP2 πP2; rw [p2_vlChoice]; exact mem_singleton_self _)
      infP2_recommended

/-- Total Trust with respect to the `x`-question gives Total Trust on the single variable `ind xq`.
Source: none: infrastructure (Known issues 12: the map from `TotalTrustWrt` to `TotalTrustOn`)
Kind: L
Fidelity: n/a -/
theorem separation_p2_on : TotalTrustOn (ind xq) πP2 FP2 :=
  totalTrustWrt_iff_forall_totalTrustOn.1 (p2_instance).2.1 (ind xq) (measurableWrt_questionOf_ind xq)

/-! ## T3(b): the sign of `E_π U − E_π R` is not fixed by Total Trust -/

/-- **The two-signal identity**: on the P2 family, `E_π(U) − E_π(R(U))` for `U = ind xq` is
`σ (p̂₁ − h₁) + (1 − σ)(p̂₂ − h₂)` — the difference of the overseer's two shrinkages, with
betweenness making the first term nonnegative and the second nonpositive.
Source: [[approval-adversary]] A2.3 l. 29 ("both candidates are shrunk toward the middle; with
candidates shrunk in one direction the sign flips")
Kind: L
Fidelity: exact -/
theorem p2_sign_identity (σ q₁ q₂ h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1) :
    E (p2Def σ q₁ q₂) (ind xq) - E (p2Def σ q₁ q₂) (rating (p2Frame h₁ h₂ hh₁ hh₂) (ind xq)) =
      σ * (q₁ - h₁) + (1 - σ) * (q₂ - h₂) := by
  have hr : ∀ w, rating (p2Frame h₁ h₂ hh₁ hh₂) (ind xq) w = if w.val < 2 then h₁ else h₂ := by
    intro w; unfold rating; rw [E_ind, p2Frame_mass_xq]
  simp only [E, Fin.sum_univ_four, hr]
  simp [p2Def, ind, xq, vec4_two, vec4_three]
  ring

/-- The sharper overseer `p_H = (9/10, 2/5)` at the same deferrer: Total Trust with respect to the
`x`-question by betweenness `1/5 ≤ 2/5 ≤ 11/20 ≤ 9/10 ≤ 9/10`.
Source: mandate T3(b)(ii)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_sharp_totalTrustWrt :
    TotalTrustWrt (questionOf xq) πP2 (p2Frame (9 / 10) (2 / 5) (by norm_num) (by norm_num)) :=
  (p2_totalTrustWrt_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2 (by norm_num [Betweenness, p2Prior])

/-- **`sign_undetermined`** (corr-wf14-2-048, A2.3): two frames of the P2 family, both totally
trusted by `πP2` with respect to the `x`-question (hence on `U = ind xq`), with opposite signs of
`E_π U − E_π R`: `(3/5, 2/5)` gives `11/20 − 1/2 = +1/20`; `(9/10, 2/5)` gives
`11/20 − 13/20 = −1/10`. The direction of the agent's disagreement with the overseer's expected
rating is not determined by Total Trust; the source asserts this without an instance (Known
issues 4).
Source: [[approval-adversary]] A2.3 l. 29; [[approval-final]] S2 l. 53 ("Dropped (A2.3) …
under Total Trust alone the sign … is undetermined"); corr-wf14-2-048
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sign_undetermined :
    (TotalTrustOn (ind xq) πP2 FP2 ∧
      E πP2 (ind xq) - E πP2 (rating FP2 (ind xq)) = 1 / 20) ∧
    (TotalTrustOn (ind xq) πP2 (p2Frame (9 / 10) (2 / 5) (by norm_num) (by norm_num)) ∧
      E πP2 (ind xq) - E πP2 (rating (p2Frame (9 / 10) (2 / 5) (by norm_num) (by norm_num)) (ind xq))
        = -1 / 10) := by
  refine ⟨⟨separation_p2_on, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [p2_sign_identity]; norm_num
  · exact totalTrustWrt_iff_forall_totalTrustOn.1 p2_sharp_totalTrustWrt (ind xq)
      (measurableWrt_questionOf_ind xq)
  · rw [p2_sign_identity]; norm_num

/-- **The layer-cake witness on P2**: `E_π[U R] = 31/100 ≥ 13/100 = ½ E_π[R²]` at `U = ind xq`.
Source: mandate T3(a) (witness)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_layer_cake_numbers :
    ∑ w, πP2 w * (ind xq w * rating FP2 (ind xq) w) = 31 / 100 ∧
    ∑ w, πP2 w * (rating FP2 (ind xq) w ^ 2 / 2) = 13 / 100 := by
  constructor <;> simp only [Fin.sum_univ_four, (p2_rating _).1] <;>
    simp [p2Def, ind, xq, vec4_two, vec4_three] <;> norm_num

/-! ## A concrete instance of the collapse (T2(a)) on P2's data -/

/-- Nonnegativity of the P2 deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πP2_nonneg : ∀ w, 0 ≤ πP2 w := by
  intro w; fin_cases w <;> norm_num [p2Def, vec4_two, vec4_three]

/-- The signal map on P2's four worlds (`x = 1` on the first two).
Source: mandate T2(a) (the calibrated-refining case)
Kind: D
Fidelity: exact -/
def sig : Fin 4 → Bool := fun w => decide (w.val < 2)

/-- **The collapse, exercised** (T2(a), N+): with the overseer replaced by the *calibrated*
refinement of `πP2` along the signal, the uninformed approval-directed choice set is `{ind xq}` —
the value learner's choice (`p2_vlChoice`), and a proper subset of the menu
(`collapse_on_p2_strict`). So the collapse of S1 is shown on a non-degenerate frame with two
distinct candidates and a strict argmax, on the same data where `separation_p2` shows the modest
overseer separates. Added at audit round 1 (adversarial N7; the auditor's probe
`CollapseWitness.lean`).
Source: [[approval-final]] S1 l. 51; mandate T2(a)
Kind: N+ (`collapse_refineFrame` at P2)
Fidelity: exact
Hyps: (a) none -/
theorem collapse_on_p2_refined :
    adUninformed menuP2 πP2 (CorrReflectFrames.refineFrame πP2 πP2_nonneg sig) = {ind xq} := by
  rw [← collapse_refineFrame πP2_nonneg sig menuP2, p2_vlChoice]

/-- Non-degeneracy of the instance: the menu has two options and the choice set is a proper subset.
Source: mandate T2(a) (witness)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem collapse_on_p2_strict :
    adUninformed menuP2 πP2 (CorrReflectFrames.refineFrame πP2 πP2_nonneg sig) ≠ menuP2 := by
  rw [collapse_on_p2_refined]
  intro h
  have : (fun _ : Fin 4 => (13 : ℝ) / 25) ∈ ({ind xq} : Finset (Fin 4 → ℝ)) := by
    rw [h]; simp [menuP2]
  rw [mem_singleton] at this
  exact p2_options_ne this.symm

end

end Cleanroom.Corrigibility.CorrLegitModif
