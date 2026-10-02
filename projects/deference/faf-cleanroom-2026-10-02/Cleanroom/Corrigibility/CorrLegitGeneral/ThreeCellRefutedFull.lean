import Cleanroom.Corrigibility.CorrLegitGeneral.ThreeCellRefuted

/-!
# corr-legit-general — T4(d): the three-cell refutation with full-support rows

`ThreeCellRefuted.lean` realises each expert type with one representative world per cell, so
every expert is certain of three worlds. The refutation does not depend on that (both predicates
read only `(Q w, Q_* P_w, π w)`), but — as `tieF` did for `tie4` — this file shows it directly:
the same question `Q7`, deferrer `π7`, types and menu, with every row of **full support**
(repair round 3, pushing further after audit r3 adversarial B1, which proposed the construction).

Rows: `P_w(v) = p_{t(w)}(Q v) · π_v / π(cell Q v)` — type `t`'s mass on cell `c` spread over the
worlds of `c` in proportion to `π`. The cells are `{2, 3, 5}` (`π`-mass `1/4`), `{0, 4, 6}`
(`1/3`) and `{1}` (`5/12`), so a row is `(5/16·p(1), p(2), 5/12·p(0), 1/2·p(0), 7/16·p(1),
1/12·p(0), 1/4·p(1))`:

| type | row |
|---|---|
| `p₁ = (1/25, 3/10, 33/50)` | `(3/32, 33/50, 1/60, 1/50, 21/160, 1/300, 3/40)` |
| `p₂ = (23/50, 8/25, 11/50)` | `(1/10, 11/50, 23/120, 23/100, 7/50, 23/600, 2/25)` |
| `p₃ = (4/25, 8/25, 13/25)` | `(1/10, 13/25, 1/15, 2/25, 7/50, 1/75, 2/25)` |
| `p₄ = (9/50, 17/25, 7/50)` | `(17/80, 7/50, 3/40, 9/100, 119/400, 3/200, 17/100)` |

The pushforwards are the four types again, so the expert expectations of `Q7`-measurable
variables are the same linear forms, local Total Trust is the same 16-pattern `linarith` proof,
the recommended strategy on the menu is the same forced `S7`, and `S7_value`/`x7_1_value` are
reused unchanged: weak local Value fails by `1/15` on a frame in which every expert gives every
world positive probability.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Type `p₁` spread over the cells in proportion to `π7`.
Source: this package (repair round 3; audit r3 adversarial B1's "full-support realisation")
Kind: D
Fidelity: n/a -/
def f7a : Fin 7 → ℝ := ![3 / 32, 33 / 50, 1 / 60, 1 / 50, 21 / 160, 1 / 300, 3 / 40]

/-- Type `p₂` spread over the cells.
Source: this package (repair round 3)
Kind: D
Fidelity: n/a -/
def f7b : Fin 7 → ℝ := ![1 / 10, 11 / 50, 23 / 120, 23 / 100, 7 / 50, 23 / 600, 2 / 25]

/-- Type `p₃` spread over the cells.
Source: this package (repair round 3)
Kind: D
Fidelity: n/a -/
def f7c : Fin 7 → ℝ := ![1 / 10, 13 / 25, 1 / 15, 2 / 25, 7 / 50, 1 / 75, 2 / 25]

/-- Type `p₄` spread over the cells.
Source: this package (repair round 3)
Kind: D
Fidelity: n/a -/
def f7d : Fin 7 → ℝ := ![17 / 80, 7 / 50, 3 / 40, 9 / 100, 119 / 400, 3 / 200, 17 / 100]

/-- The full-support rows by world: types `p₁, p₁, p₂, p₃, p₃, p₄, p₄`, as in `P7`.
Source: this package (repair round 3)
Kind: D
Fidelity: n/a -/
def P7F : Fin 7 → Fin 7 → ℝ := ![f7a, f7a, f7b, f7c, f7c, f7d, f7d]

/-- `P7F` at world 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_0 : P7F 0 = f7a := rfl

/-- `P7F` at world 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_1 : P7F 1 = f7a := rfl

/-- `P7F` at world 2.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_2 : P7F 2 = f7b := rfl

/-- `P7F` at world 3.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_3 : P7F 3 = f7c := rfl

/-- `P7F` at world 4.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_4 : P7F 4 = f7c := rfl

/-- `P7F` at world 5.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_5 : P7F 5 = f7d := rfl

/-- `P7F` at world 6.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7F_6 : P7F 6 = f7d := rfl

/-- `f7a` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem f7a_mem : f7a ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [f7a, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, f7a, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `f7b` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem f7b_mem : f7b ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [f7b, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, f7b, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `f7c` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem f7c_mem : f7c ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [f7c, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, f7c, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `f7d` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem f7d_mem : f7d ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [f7d, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, f7d, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- The full-support seven-world frame.
Source: this package (repair round 3; audit r3 adversarial B1)
Kind: D
Fidelity: n/a -/
def F7F : Frame (Fin 7) :=
  ⟨P7F, fun w => by
    fin_cases w
    · exact f7a_mem
    · exact f7a_mem
    · exact f7b_mem
    · exact f7c_mem
    · exact f7c_mem
    · exact f7d_mem
    · exact f7d_mem⟩

/-- Every row of `F7F` gives every world positive probability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem F7F_rows_pos : ∀ w v, 0 < F7F.P w v := by
  have hP : ∀ w, F7F.P w = P7F w := fun _ => rfl
  intro w v
  rw [hP]
  -- `P7F` is unfolded rather than rewritten by `P7F_k`: after `fin_cases` the index is `⟨k, _⟩`,
  -- which the vector simprocs reduce but the literal-indexed lemmas do not match.
  fin_cases w <;> fin_cases v <;>
    norm_num [P7F, f7a, f7b, f7c, f7d, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]

/-- Expert expectation of `x ∘ Q7` at the full-support row of type `p₁`: the same pairing
`⟨p₁, x⟩` as `E_r7a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_f7a (x : Fin 3 → ℝ) : E f7a (x ∘ Q7) = 1 / 25 * x 0 + 3 / 10 * x 1 + 33 / 50 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, f7a, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- Expert expectation at the full-support row of type `p₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_f7b (x : Fin 3 → ℝ) : E f7b (x ∘ Q7) = 23 / 50 * x 0 + 8 / 25 * x 1 + 11 / 50 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, f7b, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- Expert expectation at the full-support row of type `p₃`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_f7c (x : Fin 3 → ℝ) : E f7c (x ∘ Q7) = 4 / 25 * x 0 + 8 / 25 * x 1 + 13 / 25 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, f7c, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- Expert expectation at the full-support row of type `p₄`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_f7d (x : Fin 3 → ℝ) : E f7d (x ∘ Q7) = 9 / 50 * x 0 + 17 / 25 * x 1 + 7 / 50 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, f7d, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- **Local Total Trust holds** on the full-support frame: the same 16 sign patterns as
`F7_totalTrustWrt`, since the expert expectations of `Q7`-measurable variables are the same.
Source: this package (repair round 3); [[Deference Done Better]] §5 l. 396
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem F7F_totalTrustWrt : TotalTrustWrt Q7 π7 F7F := by
  intro X hX s
  obtain ⟨x, rfl⟩ := (measurableWrt_iff_exists_comp Q7 X).1 hX
  have hP : ∀ w, F7F.P w = P7F w := fun _ => rfl
  simp only [Fin.sum_univ_seven, hP, P7F_0, P7F_1, P7F_2, P7F_3, P7F_4, P7F_5, P7F_6, E_f7a,
    E_f7b, E_f7c, E_f7d, Function.comp, Q7_0, Q7_1, Q7_2, Q7_3, Q7_4, Q7_5, Q7_6, π7, vec7_two,
    vec7_three, vec7_four, vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  by_cases h1 : s ≤ 1 / 25 * x 0 + 3 / 10 * x 1 + 33 / 50 * x 2 <;>
  by_cases h2 : s ≤ 23 / 50 * x 0 + 8 / 25 * x 1 + 11 / 50 * x 2 <;>
  by_cases h3 : s ≤ 4 / 25 * x 0 + 8 / 25 * x 1 + 13 / 25 * x 2 <;>
  by_cases h4 : s ≤ 9 / 50 * x 0 + 17 / 25 * x 1 + 7 / 50 * x 2 <;>
  simp only [h1, h2, h3, h4, if_true, if_false, mul_one, mul_zero] <;>
  linarith

/-- Expert scores at the four full-support rows: the same numbers as `scores7`, unique
maximiser everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem scores7F :
    (E f7a x7_0 = 11 / 500 ∧ E f7a x7_1 = -21 / 125 ∧ E f7a x7_2 = 9 / 500) ∧
    (E f7b x7_0 = -111 / 250 ∧ E f7b x7_1 = 74 / 125 ∧ E f7b x7_2 = 139 / 500) ∧
    (E f7c x7_0 = -21 / 250 ∧ E f7c x7_1 = 13 / 250 ∧ E f7c x7_2 = 17 / 250) ∧
    (E f7d x7_0 = 72 / 125 ∧ E f7d x7_1 = 4 / 25 ∧ E f7d x7_2 = -53 / 100) := by
  simp only [x7_0, x7_1, x7_2, E_f7a, E_f7b, E_f7c, E_f7d, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, vec3_two]
  norm_num

/-- Any recommended strategy for the menu on the full-support frame is `S7`.
Source: this package (repair round 3); [[Deference Done Better]] §1 l. 117
Kind: L
Fidelity: n/a -/
theorem S7F_recommended_eq {S : Fin 7 → (Fin 7 → ℝ)}
    (hS : F7F.Recommended {x7_0, x7_1, x7_2} S) : ∀ w, S w = S7 w := by
  obtain ⟨⟨hmem, _⟩, hopt⟩ := hS
  obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩, ⟨d0, d1, d2⟩⟩ := scores7F
  have hP : ∀ w, F7F.P w = P7F w := fun _ => rfl
  have w0 : S 0 = S7 0 := by
    have hm := hmem 0
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 0 x7_0 (by simp)
    have h1 := hopt 0 x7_1 (by simp)
    have h2 := hopt 0 x7_2 (by simp)
    simp only [hP, P7F_0] at h0 h1 h2
    rw [S7_0]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [a0, a1, a2] at h1; done)
            | (norm_num [a0, a1, a2] at h2; done)
            | (norm_num [a0, a1, a2] at h0; done))
  have w1 : S 1 = S7 1 := by
    have hm := hmem 1
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 1 x7_0 (by simp)
    have h1 := hopt 1 x7_1 (by simp)
    have h2 := hopt 1 x7_2 (by simp)
    simp only [hP, P7F_1] at h0 h1 h2
    rw [S7_1]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [a0, a1, a2] at h1; done)
            | (norm_num [a0, a1, a2] at h2; done)
            | (norm_num [a0, a1, a2] at h0; done))
  have w2 : S 2 = S7 2 := by
    have hm := hmem 2
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 2 x7_0 (by simp)
    have h1 := hopt 2 x7_1 (by simp)
    have h2 := hopt 2 x7_2 (by simp)
    simp only [hP, P7F_2] at h0 h1 h2
    rw [S7_2]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [b0, b1, b2] at h1; done)
            | (norm_num [b0, b1, b2] at h2; done)
            | (norm_num [b0, b1, b2] at h0; done))
  have w3 : S 3 = S7 3 := by
    have hm := hmem 3
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 3 x7_0 (by simp)
    have h1 := hopt 3 x7_1 (by simp)
    have h2 := hopt 3 x7_2 (by simp)
    simp only [hP, P7F_3] at h0 h1 h2
    rw [S7_3]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [c0, c1, c2] at h1; done)
            | (norm_num [c0, c1, c2] at h2; done)
            | (norm_num [c0, c1, c2] at h0; done))
  have w4 : S 4 = S7 4 := by
    have hm := hmem 4
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 4 x7_0 (by simp)
    have h1 := hopt 4 x7_1 (by simp)
    have h2 := hopt 4 x7_2 (by simp)
    simp only [hP, P7F_4] at h0 h1 h2
    rw [S7_4]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [c0, c1, c2] at h1; done)
            | (norm_num [c0, c1, c2] at h2; done)
            | (norm_num [c0, c1, c2] at h0; done))
  have w5 : S 5 = S7 5 := by
    have hm := hmem 5
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 5 x7_0 (by simp)
    have h1 := hopt 5 x7_1 (by simp)
    have h2 := hopt 5 x7_2 (by simp)
    simp only [hP, P7F_5] at h0 h1 h2
    rw [S7_5]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [d0, d1, d2] at h1; done)
            | (norm_num [d0, d1, d2] at h2; done)
            | (norm_num [d0, d1, d2] at h0; done))
  have w6 : S 6 = S7 6 := by
    have hm := hmem 6
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 6 x7_0 (by simp)
    have h1 := hopt 6 x7_1 (by simp)
    have h2 := hopt 6 x7_2 (by simp)
    simp only [hP, P7F_6] at h0 h1 h2
    rw [S7_6]
    rcases hm with hw | hw | hw <;> rw [hw] at h0 h1 h2 ⊢ <;>
      first
        | rfl
        | (exfalso; first
            | (norm_num [d0, d1, d2] at h1; done)
            | (norm_num [d0, d1, d2] at h2; done)
            | (norm_num [d0, d1, d2] at h0; done))
  intro w
  fin_cases w
  · exact w0
  · exact w1
  · exact w2
  · exact w3
  · exact w4
  · exact w5
  · exact w6

/-- **Weak local Value fails** on the full-support frame: the only recommended strategy is `S7`,
worth `3/20 < 13/60 = E_π(x₁)` (`S7_value`, `x7_1_value`, which depend only on `π7` and the
options).
Source: this package (repair round 3); [[Deference Done Better]] App. B l. 472, fn 64 l. 1235
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem F7F_not_weakValuesWrt : ¬ WeakValuesWrt Q7 π7 F7F := by
  intro h
  obtain ⟨S, hS, hall⟩ := h {x7_0, x7_1, x7_2} (insert_nonempty _ _) menu7_meas
  have h1 := hall x7_1 (by simp)
  have hSv : stratValue π7 S = stratValue π7 S7 := by
    simp only [stratValue]
    apply sum_congr rfl
    intro w _
    rw [S7F_recommended_eq hS w]
  rw [hSv, S7_value, x7_1_value] at h1
  norm_num at h1

/-- **fn 65's weak reading is refuted at three cells by a frame with full-support rows**: the
same question, deferrer (full support), types and menu as `localTotalTrust_imp_weakLocalValue_refuted`,
with every expert giving every world positive probability — the refutation is not an artifact
of experts certain of one world per cell (as `tieF_witness` showed for `tie4` at two cells).
Source: [[Deference Done Better]] fn 65 l. 1237, fn 64 l. 1235, App. B l. 472; audit r3
adversarial B1 (the proposed full-support realisation); this package (repair round 3)
Kind: N+
Fidelity: exact (refutation by one instance; weak reading; full support of deferrer and rows
stated as conjuncts)
Hyps: (a) none -/
theorem localTotalTrust_imp_weakLocalValue_refuted_fullSupport :
    ∃ (Q : Fin 7 → Fin 3) (π : Fin 7 → ℝ) (F : Frame (Fin 7)),
      Function.Surjective Q ∧ π ∈ stdSimplex ℝ (Fin 7) ∧ (∀ w, 0 < π w) ∧
        (∀ w v, 0 < F.P w v) ∧ TotalTrustWrt Q π F ∧ ¬ WeakValuesWrt Q π F :=
  ⟨Q7, π7, F7F, Q7_surjective, π7_mem, π7_pos, F7F_rows_pos, F7F_totalTrustWrt,
    F7F_not_weakValuesWrt⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
