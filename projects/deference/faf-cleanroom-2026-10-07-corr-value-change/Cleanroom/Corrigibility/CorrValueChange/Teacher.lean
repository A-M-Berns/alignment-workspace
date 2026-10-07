import Cleanroom.Corrigibility.CorrValueChange.Fine
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# corr-value-change — the worked example and its variants (T6(e), T7, T12(h), the numbers)

Source: [[value-change-as-epistemic-update]] §2.5, §3.2, §6.5; fixture
`value_change_journey.py`. The parametrized teacher: `Ω` trivial, value hypotheses `Θ = Bool`
(`true` = `A`), signal `I = Bool` (`true` = "`A`"), three acts `a₁, a₂, a₃` with `u_A = (1, 0, s)`,
`u_B = (0, 1, s)`; the source has `P(i = θ) = r`; the installed state is `Q_i(θ = i) = r'`
(`r' = r` is reflection). The coin is the teacher at `r = 1/2`; the pill installs `(9/10, 1/10)`
regardless of the signal. All numbers are rational literals in ℝ, checked by `norm_num`.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-! ## The parametrized teacher -/

/-- The candidate utilities of §2.5: `u_A = (1, 0, s)`, `u_B = (0, 1, s)` on `(a₁, a₂, a₃)`.
Source: [[value-change-as-epistemic-update]] §2.5
Kind: D
Fidelity: exact -/
def uT (s : ℝ) : Bool → Fin 3 → Unit → ℝ :=
  fun θ a _ => ![if θ then 1 else 0, if θ then 0 else 1, s] a

/-- The agent's joint `P(θ, i) = ½ · (r if i = θ else 1 − r)`.
Source: [[value-change-as-epistemic-update]] §2.5; fixture `joint`
Kind: D
Fidelity: exact -/
def teacherJoint (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Joint (Unit × Bool) Bool where
  P := fun x i => 1 / 2 * (if x.2 = i then r else 1 - r)
  nonneg := fun x i => by
    have : 0 ≤ 1 - r := by linarith
    split_ifs <;> positivity
  sum_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- The installed state `Q_i(θ) = r'` if `θ = i`, else `1 − r'`.
Source: [[value-change-as-epistemic-update]] §2.5; fixture `installed`
Kind: D
Fidelity: exact -/
def installedOf (r' : ℝ) (h0 : 0 ≤ r') (h1 : r' ≤ 1) : Installed (Unit × Bool) Bool where
  Q := fun i x => if x.2 = i then r' else 1 - r'
  nonneg := fun i x => by
    have : 0 ≤ 1 - r' := by linarith
    split_ifs <;> linarith
  sum_one := fun i => by cases i <;> simp [Fintype.sum_prod_type, Fintype.sum_bool]

/-- `π_i = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem teacher_π (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (i : Bool) :
    (teacherJoint r hr0 hr1).π i = 1 / 2 := by
  cases i <;> simp [Joint.π, teacherJoint, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

/-- **Reflection holds by construction** at `r' = r`: `P(θ ∣ i) = Q_i(θ)`.
Source: [[value-change-as-epistemic-update]] §2.5 ("so (R⁺) holds by construction")
Kind: N+
Fidelity: exact -/
theorem teacher_reflection (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Reflection (teacherJoint r hr0 hr1) (installedOf r hr0 hr1) := by
  intro i _ x
  rw [teacher_π]
  simp [teacherJoint, installedOf]

/-- The branch values: `S(a, i) = ½ · (r, 1−r, s)` for `i = A` and `½ · (1−r, r, s)` for `i = B`.
Source: [[value-change-as-epistemic-update]] §2.5 (the branch computation)
Kind: L
Fidelity: exact -/
theorem teacher_S (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (a : Fin 3) (i : Bool) :
    S (teacherJoint r hr0 hr1) (uT s) a i =
      1 / 2 * ![if i then r else 1 - r, if i then 1 - r else r, s] a := by
  fin_cases a <;> cases i <;>
    simp [S, Uplus, uT, teacherJoint, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

/-- The installed values: `E_{Q_i}[U_a] = (r', 1−r', s)` for `i = A`, `(1−r', r', s)` for `i = B`.
Source: [[value-change-as-epistemic-update]] §2.5
Kind: L
Fidelity: exact -/
theorem teacher_EQ (r' s : ℝ) (h0 : 0 ≤ r') (h1 : r' ≤ 1) (i : Bool) (a : Fin 3) :
    EQ (installedOf r' h0 h1) (uT s) i a =
      ![if i then r' else 1 - r', if i then 1 - r' else r', s] a := by
  fin_cases a <;> cases i <;>
    simp [EQ, Uplus, uT, installedOf, Fintype.sum_prod_type] <;> ring

/-- `E_P[U_a] = (1/2, 1/2, s)`.
Source: [[value-change-as-epistemic-update]] §2.5 ("Decline: `max(0.5, 0.5, 0.6)`")
Kind: L
Fidelity: exact -/
theorem teacher_EU (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (a : Fin 3) :
    EU (teacherJoint r hr0 hr1) (uT s) a = ![1 / 2, 1 / 2, s] a := by
  unfold EU
  rw [Fintype.sum_bool, teacher_S, teacher_S]
  fin_cases a <;> simp <;> ring

/-- A value that is one of three numbers and at least each of them is their maximum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eq_max3_of_mem {x y z w : ℝ} (hw : w = x ∨ w = y ∨ w = z) (hx : x ≤ w) (hy : y ≤ w)
    (hz : z ≤ w) : w = max (max x y) z := by
  apply le_antisymm
  · rcases hw with h | h | h <;> rw [h]
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_right _ _
  · exact max_le (max_le hx hy) hz

/-- The same with the three numbers halved.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eq_half_max3_of_mem {x y z w : ℝ} (hw : w = 1 / 2 * x ∨ w = 1 / 2 * y ∨ w = 1 / 2 * z)
    (hx : 1 / 2 * x ≤ w) (hy : 1 / 2 * y ≤ w) (hz : 1 / 2 * z ≤ w) :
    w = 1 / 2 * max (max x y) z := by
  have := eq_max3_of_mem hw hx hy hz
  rw [this, mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]

/-- **`Val(decline) = max(1/2, s)`**, for every `P`-maximizer `a^K` and every `s`.
Source: [[value-change-as-epistemic-update]] §2.5 ("`Val(decline) = max(½, s)`")
Kind: P
Fidelity: exact
Hyps: (a) `hK` -/
theorem decline_eq (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (aK : Fin 3)
    (hK : ∀ a, EU (teacherJoint r hr0 hr1) (uT s) a ≤ EU (teacherJoint r hr0 hr1) (uT s) aK) :
    ValDecline (teacherJoint r hr0 hr1) (uT s) aK = max (1 / 2) s := by
  unfold ValDecline
  have hmem : EU (teacherJoint r hr0 hr1) (uT s) aK = 1 / 2 ∨
      EU (teacherJoint r hr0 hr1) (uT s) aK = 1 / 2 ∨
      EU (teacherJoint r hr0 hr1) (uT s) aK = s := by
    rw [teacher_EU]; fin_cases aK <;> simp
  have h0 := hK 0; have h1 := hK 1; have h2 := hK 2
  rw [teacher_EU] at h0 h1 h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  have := eq_max3_of_mem hmem h0 h1 h2
  rw [this, max_self]

/-- Each branch of the reflective teacher is worth `½ · max(r, 1 − r, s)` under any installed
maximizer.
Source: [[value-change-as-epistemic-update]] §2.5
Kind: L
Fidelity: exact -/
theorem teacher_branch (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r hr0 hr1) (uT s) i a ≤
      EQ (installedOf r hr0 hr1) (uT s) i (astar i)) (i : Bool) :
    S (teacherJoint r hr0 hr1) (uT s) (astar i) i = 1 / 2 * max (max r (1 - r)) s := by
  have hb := branch_opt_of_reflection (teacher_reflection r hr0 hr1) (uT s) astar hstar
  have h0 := hb i 0; have h1 := hb i 1; have h2 := hb i 2
  rw [teacher_S] at h0 h1 h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  have hmem : S (teacherJoint r hr0 hr1) (uT s) (astar i) i = 1 / 2 * (if i then r else 1 - r) ∨
      S (teacherJoint r hr0 hr1) (uT s) (astar i) i = 1 / 2 * (if i then 1 - r else r) ∨
      S (teacherJoint r hr0 hr1) (uT s) (astar i) i = 1 / 2 * s := by
    rw [teacher_S]
    generalize astar i = b
    fin_cases b <;> simp
  cases i
  · simp only [Bool.false_eq_true, if_false] at hmem h0 h1 h2
    rw [eq_half_max3_of_mem hmem h0 h1 h2, max_comm (1 - r) r]
  · simp only [if_true] at hmem h0 h1 h2
    exact eq_half_max3_of_mem hmem h0 h1 h2

/-- **T7, `Val(accept)` in general**: under reflection (`r' = r`), for every family of installed
maximizers, `Val(accept) = max(r, 1 − r, s)` — for all `r ∈ [0, 1]` and all `s`. An anti-reliable
source (`r < 1/2`) is used by flipping the signal.
Source: [[value-change-as-epistemic-update]] §2.5 ("`Val(accept) = max(r, s)`"); findings F8
Kind: P
Fidelity: stronger: all `r ∈ [0,1]` (the note's formula is the case `r ≥ 1/2`, `accept_eq`)
Hyps: (a) `hstar` -/
theorem accept_eq_general (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r hr0 hr1) (uT s) i a ≤
      EQ (installedOf r hr0 hr1) (uT s) i (astar i)) :
    ValAccept (teacherJoint r hr0 hr1) (uT s) astar = max (max r (1 - r)) s := by
  unfold ValAccept
  rw [Fintype.sum_bool, teacher_branch r s hr0 hr1 astar hstar, teacher_branch r s hr0 hr1 astar hstar]
  ring

/-- **T7, the note's form**: for `r ≥ 1/2`, `Val(accept) = max(r, s)`.
Source: [[value-change-as-epistemic-update]] §2.5 ("General reliability: `Val(accept) = max(r,s)`")
Kind: P
Fidelity: exact on `r ≥ 1/2` (F8: the range the note does not state)
Hyps: (a) `hstar`, `1/2 ≤ r` -/
theorem accept_eq (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr : 1 / 2 ≤ r) (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r hr0 hr1) (uT s) i a ≤
      EQ (installedOf r hr0 hr1) (uT s) i (astar i)) :
    ValAccept (teacherJoint r hr0 hr1) (uT s) astar = max r s := by
  rw [accept_eq_general r s hr0 hr1 astar hstar, max_eq_left (by linarith : 1 - r ≤ r)]

/-- **T7, the verdict**: for `r ≥ 1/2`, the agent wants the modification iff
`r > max(1/2, s)` — the source must beat both the prior and the safe act.
Source: [[value-change-as-epistemic-update]] §2.5 ("iff `r > max(½, s)`")
Kind: P
Fidelity: exact on `r ≥ 1/2`
Hyps: (a) `hstar`, `hK` -/
theorem accept_gt_decline_iff (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr : 1 / 2 ≤ r)
    (astar : Bool → Fin 3) (aK : Fin 3)
    (hstar : ∀ i a, EQ (installedOf r hr0 hr1) (uT s) i a ≤
      EQ (installedOf r hr0 hr1) (uT s) i (astar i))
    (hK : ∀ a, EU (teacherJoint r hr0 hr1) (uT s) a ≤ EU (teacherJoint r hr0 hr1) (uT s) aK) :
    ValDecline (teacherJoint r hr0 hr1) (uT s) aK < ValAccept (teacherJoint r hr0 hr1) (uT s) astar
      ↔ max (1 / 2) s < r := by
  rw [decline_eq r s hr0 hr1 aK hK, accept_eq r s hr0 hr1 hr astar hstar]
  constructor
  · intro h
    by_contra hc
    have hc' : r ≤ max (1 / 2) s := not_lt.1 hc
    have : max r s ≤ max (1 / 2) s := max_le hc' (le_max_right _ _)
    linarith
  · intro h; exact lt_of_lt_of_le h (le_max_left _ _)

/-! ## Mismatch: installed `r'`, true `r` -/

/-- **Mismatch, the installed confidence beats the safe act**: if `s < r'` and `1 − r' < r'`, the
modified agent acts on the signal (forced), and the current agent values that at `r`:
`Val(accept) = r`, for the true reliability `r` whatever it is.
Source: [[value-change-as-epistemic-update]] §2.5 ("The modified agent acts on the signal iff
`r' ≥ s`, and the current agent values acting on it at `r`"); findings F8
Kind: P
Fidelity: exact on `s < r'`, `1/2 < r'` (the tie `r' = s` is `mismatch_tie`)
Hyps: (a) `hstar` -/
theorem mismatch_high (r r' s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h0 : 0 ≤ r') (h1 : r' ≤ 1)
    (hs : s < r') (hhalf : 1 - r' < r') (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r' h0 h1) (uT s) i a ≤
      EQ (installedOf r' h0 h1) (uT s) i (astar i)) :
    ValAccept (teacherJoint r hr0 hr1) (uT s) astar = r := by
  have hA : astar true = 0 := by
    have ha := hstar true 0; have hb := hstar true 1; have hc := hstar true 2
    rw [teacher_EQ, teacher_EQ] at ha hb hc
    generalize astar true = b at *
    fin_cases b <;> simp at ha hb hc <;> first | rfl | linarith
  have hB : astar false = 1 := by
    have ha := hstar false 0; have hb := hstar false 1; have hc := hstar false 2
    rw [teacher_EQ, teacher_EQ] at ha hb hc
    generalize astar false = b at *
    fin_cases b <;> simp at ha hb hc <;> first | rfl | linarith
  unfold ValAccept
  rw [Fintype.sum_bool, hA, hB, teacher_S, teacher_S]
  simp; ring

/-- **Mismatch, the installed confidence loses to the safe act**: if `max(r', 1 − r') < s`, the
modified agent takes the safe act (forced) and `Val(accept) = s`.
Source: [[value-change-as-epistemic-update]] §2.5 ("An installed confidence below the safe act's
value wastes a good source")
Kind: P
Fidelity: exact
Hyps: (a) `hstar` -/
theorem mismatch_low (r r' s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h0 : 0 ≤ r') (h1 : r' ≤ 1)
    (hs : r' < s) (hs' : 1 - r' < s) (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r' h0 h1) (uT s) i a ≤
      EQ (installedOf r' h0 h1) (uT s) i (astar i)) :
    ValAccept (teacherJoint r hr0 hr1) (uT s) astar = s := by
  have hA : astar true = 2 := by
    have ha := hstar true 0; have hb := hstar true 1; have hc := hstar true 2
    rw [teacher_EQ, teacher_EQ] at ha hb hc
    generalize astar true = b at *
    fin_cases b <;> simp at ha hb hc <;> first | rfl | linarith
  have hB : astar false = 2 := by
    have ha := hstar false 0; have hb := hstar false 1; have hc := hstar false 2
    rw [teacher_EQ, teacher_EQ] at ha hb hc
    generalize astar false = b at *
    fin_cases b <;> simp at ha hb hc <;> first | rfl | linarith
  unfold ValAccept
  rw [Fintype.sum_bool, hA, hB, teacher_S, teacher_S]
  simp; ring

/-- **Mismatch at the tie `r' = s`** (with `1 − r' < r'`): both the signal act and the safe act
maximize the installed state in each branch, so `Val(accept) = (t_A + t_B)/2` with each
`t_i ∈ {r, s}` — `r`, `s` or `(r + s)/2` according to the tie-breaking. The note's "iff `r' ≥ s`"
and the fixture's `max` pick the signal act by convention.
Source: [[value-change-as-epistemic-update]] §2.5; findings F8
Kind: P
Fidelity: variant: the tie case made explicit
Hyps: (a) `hstar` -/
theorem mismatch_tie (r r' s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h0 : 0 ≤ r') (h1 : r' ≤ 1)
    (hs : s = r') (hhalf : 1 - r' < r') (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r' h0 h1) (uT s) i a ≤
      EQ (installedOf r' h0 h1) (uT s) i (astar i)) :
    ∃ tA tB : ℝ, (tA = r ∨ tA = s) ∧ (tB = r ∨ tB = s) ∧
      ValAccept (teacherJoint r hr0 hr1) (uT s) astar = (tA + tB) / 2 := by
  have hA : astar true = 0 ∨ astar true = 2 := by
    have hb := hstar true 1; have hc := hstar true 2
    rw [teacher_EQ, teacher_EQ] at hb hc
    generalize astar true = b at *
    fin_cases b <;> simp at hb hc ⊢ <;> linarith
  have hB : astar false = 1 ∨ astar false = 2 := by
    have ha := hstar false 0; have hc := hstar false 2
    rw [teacher_EQ, teacher_EQ] at ha hc
    generalize astar false = b at *
    fin_cases b <;> simp at ha hc ⊢ <;> linarith
  unfold ValAccept
  rw [Fintype.sum_bool]
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB, teacher_S, teacher_S]
  · exact ⟨r, r, Or.inl rfl, Or.inl rfl, by simp; ring⟩
  · exact ⟨r, s, Or.inl rfl, Or.inr rfl, by simp; ring⟩
  · exact ⟨s, r, Or.inr rfl, Or.inl rfl, by simp; ring⟩
  · exact ⟨s, s, Or.inr rfl, Or.inr rfl, by simp; ring⟩


/-- **Mismatch, the anti-reliable installation** (the case the three declarations above omit): if
`max(r', s) < 1 − r'`, the modified agent flips the signal (`a₂` on `A`, `a₁` on `B`; forced), and the
current agent values that at `1 − r`: `Val(accept) = 1 − r`. With `mismatch_high`, `mismatch_low`
and `mismatch_tie` this covers every `(r', s)` except the boundary ties `1 − r' = s` (the flip-side
analogue of `mismatch_tie`) and `r' = 1/2` (the signal act and its flip tie), where the value is
again an average of two numbers from `{r, 1 − r, s}` chosen by the tie-breaking.
Source: [[value-change-as-epistemic-update]] §2.5; findings F8 (the note's formula needs `r' ≥ 1/2`)
Kind: P
Fidelity: variant: the note has no flip case (its mismatch formula is stated for `r' ≥ 1/2`)
Hyps: (a) `hstar` -/
theorem mismatch_flip (r r' s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h0 : 0 ≤ r') (h1 : r' ≤ 1)
    (hs : s < 1 - r') (hhalf : r' < 1 - r') (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (installedOf r' h0 h1) (uT s) i a ≤
      EQ (installedOf r' h0 h1) (uT s) i (astar i)) :
    ValAccept (teacherJoint r hr0 hr1) (uT s) astar = 1 - r := by
  have hA : astar true = 1 := by
    have ha := hstar true 0; have hb := hstar true 1; have hc := hstar true 2
    rw [teacher_EQ, teacher_EQ] at ha hb hc
    generalize astar true = b at *
    fin_cases b <;> simp at ha hb hc <;> first | rfl | linarith
  have hB : astar false = 0 := by
    have ha := hstar false 0; have hb := hstar false 1; have hc := hstar false 2
    rw [teacher_EQ, teacher_EQ] at ha hb hc
    generalize astar false = b at *
    fin_cases b <;> simp at ha hb hc <;> first | rfl | linarith
  unfold ValAccept
  rw [Fintype.sum_bool, hA, hB, teacher_S, teacher_S]
  simp; ring

end

end Cleanroom.Corrigibility.CorrValueChange
