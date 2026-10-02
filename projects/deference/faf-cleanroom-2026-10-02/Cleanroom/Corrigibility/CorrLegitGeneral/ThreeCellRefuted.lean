import Cleanroom.Corrigibility.CorrLegitGeneral.LocalValue
import Cleanroom.Found.LitDdbFrames.ExamplesFact21
import Mathlib.Data.Fin.VecNotation

-- Deliberately not importing `Eval`: its simp attributes `fin4_mk_two`/`fin4_mk_three` stop the
-- coordinate reduction of `Fin 7` vectors at `⟨2, _⟩ : Fin 4` / `⟨3, _⟩ : Fin 4` (the first
-- elaboration of this file failed exactly there); only `vec3_two` is needed from the examples.

/-!
# corr-legit-general — T4(d): fn 65's weak reading is refuted at three cells

DDB's one stated open problem (fn 65): local Total Trust with respect to `Q` ⟹ local Value with
respect to `Q`. In fn 64's literal reading it fails already at two cells (`tie4`,
`localTotalTrust_imp_localValue_refuted`, `ThreeCell.lean`); the package's extension of record
was the **weak** reading (`WeakValuesWrt`: some recommended strategy beats every fixed option),
which is a theorem at two cells (`weakValuesWrt_questionOf_of_simpleTrustOn`) and for the finest
question (`totalTrust_imp_weakValuesWrt_id`), and was stated OPEN for three or more cells through
repair round 2. **It is false at three cells**: the round-3 adversarial audit found the frame
below by a direct LP (fix a three-option menu, minimise the forced recommended strategy's Value
slack over the polytope cut out by the finitely many local-Total-Trust constraints; the search
scripts and the exact rational certificate are in `run/wp/corr-legit-general/audit-r3-probes/`),
and its probe `WeakOpenRefuted.lean` is adopted here with the package's names.

Seven worlds, the three-cell question `Q7 = (1, 2, 0, 0, 1, 0, 1)` (onto `Fin 3`), the deferrer
`π7 = (5/48, 5/12, 5/48, 1/8, 7/48, 1/48, 1/12)` (full support), and four expert *types*
`p₁..p₄ ∈ Δ(3)`, read as the pushforwards `Q_* P_w` — the only thing either predicate sees, since
every `Q`-measurable `X` is `x ∘ Q`:

| world | type `Q_* P_w` | cell | `π7` |
|---|---|---|---|
| 0 | `p₁ = (1/25, 3/10, 33/50)` | 1 | 5/48 |
| 1 | `p₁` | 2 | 5/12 |
| 2 | `p₂ = (23/50, 8/25, 11/50)` | 0 | 5/48 |
| 3 | `p₃ = (4/25, 8/25, 13/25)` | 0 | 1/8 |
| 4 | `p₃` | 1 | 7/48 |
| 5 | `p₄ = (9/50, 17/25, 7/50)` | 0 | 1/48 |
| 6 | `p₄` | 1 | 1/12 |

Rows are realised with one representative world per cell (`r_t = (p_t(1), p_t(2), p_t(0), 0, 0,
0, 0)`); any rows with these pushforwards give the same two predicates. Menu, as functions of the
cell: `x₀ = (−17/10, 7/5, −1/2)`, `x₁ = (3/2, −1/10, −3/10)`, `x₂ = (6/5, −6/5, 1/2)`. The expert
scores `⟨p_t, x_o⟩` have a **unique** maximiser at every type (`p₁ ↦ x₀`, `p₂ ↦ x₁`, `p₃ ↦ x₂`,
`p₄ ↦ x₀`), so `Recommended` forces the strategy `S7` — no tie is involved, and the weak reading's
"some recommended strategy" coincides with the literal reading's "every recommended strategy".
`E_π(S7) = 3/20` while `E_π(x₁) = 13/60`: weak local Value fails by `1/15`. Local Total Trust
holds: for `X = x ∘ Q7` and any `s` the threshold sum splits into 16 sign patterns on the four
expert expectations, and every pattern is a linear inequality in `(x 0, x 1, x 2, s)` that
`linarith` closes from the four sign hypotheses (unrealisable patterns are inconsistent).

Consequences, all in this file: the weak reading is refuted
(`localTotalTrust_imp_weakLocalValue_refuted`); the frame is an `hdet`-frame for `Q7` (rows on
the support determined by the pushforward), so the literal reading restricted to `hdet`-frames —
the report's other surviving form — is refuted at three cells too
(`localTotalTrust_imp_localValue_hdet_refuted`); and the former OPEN's statement, specialised to
`W = Fin 7`, `C = Fin 3`, is false (`weakLocalValue_open_statement_false`). With the two-cell
theorems, fn 65's conjecture now breaks exactly at three cells.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Index lemma for `Fin 7` vectors (`simp` does not reliably reduce `![…] k` for `k ≥ 2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec7_two (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → ℝ) 2 = a2 := rfl

/-- Index lemma for `Fin 7` vectors, coordinate 3.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec7_three (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → ℝ) 3 = a3 := rfl

/-- Index lemma for `Fin 7` vectors, coordinate 4.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec7_four (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → ℝ) 4 = a4 := rfl

/-- Index lemma for `Fin 7` vectors, coordinate 5.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec7_five (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → ℝ) 5 = a5 := rfl

/-- Index lemma for `Fin 7` vectors, coordinate 6.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec7_six (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → ℝ) 6 = a6 := rfl

/-- The three-cell question on seven worlds: the cell of each world, `(1, 2, 0, 0, 1, 0, 1)`.
Source: audit r3 adversarial B1 (probe `WeakOpenRefuted.lean`); this package (T4(d))
Kind: D
Fidelity: n/a -/
def Q7 : Fin 7 → Fin 3 := ![1, 2, 0, 0, 1, 0, 1]

/-- `Q7` at world 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_0 : Q7 0 = 1 := rfl

/-- `Q7` at world 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_1 : Q7 1 = 2 := rfl

/-- `Q7` at world 2.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_2 : Q7 2 = 0 := rfl

/-- `Q7` at world 3.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_3 : Q7 3 = 0 := rfl

/-- `Q7` at world 4.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_4 : Q7 4 = 1 := rfl

/-- `Q7` at world 5.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_5 : Q7 5 = 0 := rfl

/-- `Q7` at world 6.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_6 : Q7 6 = 1 := rfl

/-- `Q7` is onto `Fin 3`: the question has three cells.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Q7_surjective : Function.Surjective Q7 := fun c => by
  fin_cases c
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- Type `p₁ = (1/25, 3/10, 33/50)` as a row: `p₁(0)` on world 2, `p₁(1)` on world 0, `p₁(2)` on
world 1 (one representative world per cell).
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def r7a : Fin 7 → ℝ := ![3 / 10, 33 / 50, 1 / 25, 0, 0, 0, 0]

/-- Type `p₂ = (23/50, 8/25, 11/50)` as a row.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def r7b : Fin 7 → ℝ := ![8 / 25, 11 / 50, 23 / 50, 0, 0, 0, 0]

/-- Type `p₃ = (4/25, 8/25, 13/25)` as a row.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def r7c : Fin 7 → ℝ := ![8 / 25, 13 / 25, 4 / 25, 0, 0, 0, 0]

/-- Type `p₄ = (9/50, 17/25, 7/50)` as a row.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def r7d : Fin 7 → ℝ := ![17 / 25, 7 / 50, 9 / 50, 0, 0, 0, 0]

/-- The rows by world: types `p₁, p₁, p₂, p₃, p₃, p₄, p₄`.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def P7 : Fin 7 → Fin 7 → ℝ := ![r7a, r7a, r7b, r7c, r7c, r7d, r7d]

/-- `P7` at world 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_0 : P7 0 = r7a := rfl

/-- `P7` at world 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_1 : P7 1 = r7a := rfl

/-- `P7` at world 2.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_2 : P7 2 = r7b := rfl

/-- `P7` at world 3.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_3 : P7 3 = r7c := rfl

/-- `P7` at world 4.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_4 : P7 4 = r7c := rfl

/-- `P7` at world 5.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_5 : P7 5 = r7d := rfl

/-- `P7` at world 6.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P7_6 : P7 6 = r7d := rfl

/-- `r7a` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem r7a_mem : r7a ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [r7a, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, r7a, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `r7b` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem r7b_mem : r7b ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [r7b, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, r7b, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `r7c` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem r7c_mem : r7c ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [r7c, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, r7c, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `r7d` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem r7d_mem : r7d ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [r7d, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, r7d, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- The seven-world frame of the refutation.
Source: audit r3 adversarial B1 (probe `WeakOpenRefuted.lean`); this package (T4(d))
Kind: D
Fidelity: n/a -/
def F7 : Frame (Fin 7) :=
  ⟨P7, fun w => by
    fin_cases w
    · exact r7a_mem
    · exact r7a_mem
    · exact r7b_mem
    · exact r7c_mem
    · exact r7c_mem
    · exact r7d_mem
    · exact r7d_mem⟩

/-- The deferrer `(5/48, 5/12, 5/48, 1/8, 7/48, 1/48, 1/12)`, full support.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def π7 : Fin 7 → ℝ := ![5 / 48, 5 / 12, 5 / 48, 1 / 8, 7 / 48, 1 / 48, 1 / 12]

/-- `π7` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π7_mem : π7 ∈ stdSimplex ℝ (Fin 7) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [π7, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]
  · simp only [Fin.sum_univ_seven, π7, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num

/-- `π7` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π7_pos : ∀ w, 0 < π7 w := by
  intro w; fin_cases w <;> norm_num [π7, vec7_two, vec7_three, vec7_four, vec7_five, vec7_six]

/-- Expert expectation of a `Q7`-measurable variable `x ∘ Q7` at type `p₁`: the pairing
`⟨p₁, x⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_r7a (x : Fin 3 → ℝ) : E r7a (x ∘ Q7) = 1 / 25 * x 0 + 3 / 10 * x 1 + 33 / 50 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, r7a, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- Expert expectation at type `p₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_r7b (x : Fin 3 → ℝ) : E r7b (x ∘ Q7) = 23 / 50 * x 0 + 8 / 25 * x 1 + 11 / 50 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, r7b, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- Expert expectation at type `p₃`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_r7c (x : Fin 3 → ℝ) : E r7c (x ∘ Q7) = 4 / 25 * x 0 + 8 / 25 * x 1 + 13 / 25 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, r7c, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- Expert expectation at type `p₄`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_r7d (x : Fin 3 → ℝ) : E r7d (x ∘ Q7) = 9 / 50 * x 0 + 17 / 25 * x 1 + 7 / 50 * x 2 := by
  simp only [E, Fin.sum_univ_seven, Function.comp, r7d, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6]
  ring

/-- **Local Total Trust holds** on the seven-world frame: for every `Q7`-measurable `X` and every
threshold `s`, the threshold sum is nonnegative — 16 sign patterns on the four expert
expectations, each a linear inequality closed by `linarith`.
Source: audit r3 adversarial B1; [[Deference Done Better]] §5 l. 396 (the predicate)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem F7_totalTrustWrt : TotalTrustWrt Q7 π7 F7 := by
  intro X hX s
  obtain ⟨x, rfl⟩ := (measurableWrt_iff_exists_comp Q7 X).1 hX
  have hP : ∀ w, F7.P w = P7 w := fun _ => rfl
  simp only [Fin.sum_univ_seven, hP, P7_0, P7_1, P7_2, P7_3, P7_4, P7_5, P7_6, E_r7a, E_r7b,
    E_r7c, E_r7d, Function.comp, Q7_0, Q7_1, Q7_2, Q7_3, Q7_4, Q7_5, Q7_6, π7, vec7_two,
    vec7_three, vec7_four, vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  by_cases h1 : s ≤ 1 / 25 * x 0 + 3 / 10 * x 1 + 33 / 50 * x 2 <;>
  by_cases h2 : s ≤ 23 / 50 * x 0 + 8 / 25 * x 1 + 11 / 50 * x 2 <;>
  by_cases h3 : s ≤ 4 / 25 * x 0 + 8 / 25 * x 1 + 13 / 25 * x 2 <;>
  by_cases h4 : s ≤ 9 / 50 * x 0 + 17 / 25 * x 1 + 7 / 50 * x 2 <;>
  simp only [h1, h2, h3, h4, if_true, if_false, mul_one, mul_zero] <;>
  linarith

/-- Menu option `x₀ = (−17/10, 7/5, −1/2)`, as a function of the cell.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def x7_0 : Fin 7 → ℝ := (![-17 / 10, 7 / 5, -1 / 2] : Fin 3 → ℝ) ∘ Q7

/-- Menu option `x₁ = (3/2, −1/10, −3/10)`.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def x7_1 : Fin 7 → ℝ := (![3 / 2, -1 / 10, -3 / 10] : Fin 3 → ℝ) ∘ Q7

/-- Menu option `x₂ = (6/5, −6/5, 1/2)`.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def x7_2 : Fin 7 → ℝ := (![6 / 5, -6 / 5, 1 / 2] : Fin 3 → ℝ) ∘ Q7

/-- The three options are `Q7`-measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem menu7_meas : ∀ o ∈ ({x7_0, x7_1, x7_2} : DecisionProblem (Fin 7)), MeasurableWrt Q7 o := by
  intro o ho
  simp only [mem_insert, mem_singleton] at ho
  rcases ho with rfl | rfl | rfl <;> exact (measurableWrt_iff_exists_comp Q7 _).2 ⟨_, rfl⟩

/-- Expert scores `⟨p_t, x_o⟩` at the four types: the maximiser is unique everywhere
(`p₁ ↦ x₀`, `p₂ ↦ x₁`, `p₃ ↦ x₂`, `p₄ ↦ x₀`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem scores7 :
    (E r7a x7_0 = 11 / 500 ∧ E r7a x7_1 = -21 / 125 ∧ E r7a x7_2 = 9 / 500) ∧
    (E r7b x7_0 = -111 / 250 ∧ E r7b x7_1 = 74 / 125 ∧ E r7b x7_2 = 139 / 500) ∧
    (E r7c x7_0 = -21 / 250 ∧ E r7c x7_1 = 13 / 250 ∧ E r7c x7_2 = 17 / 250) ∧
    (E r7d x7_0 = 72 / 125 ∧ E r7d x7_1 = 4 / 25 ∧ E r7d x7_2 = -53 / 100) := by
  simp only [x7_0, x7_1, x7_2, E_r7a, E_r7b, E_r7c, E_r7d, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, vec3_two]
  norm_num

/-- The forced recommended strategy: `x₀` at the `p₁`- and `p₄`-worlds, `x₁` at the `p₂`-world,
`x₂` at the `p₃`-worlds.
Source: audit r3 adversarial B1
Kind: D
Fidelity: n/a -/
def S7 : Fin 7 → (Fin 7 → ℝ) := ![x7_0, x7_0, x7_1, x7_2, x7_2, x7_0, x7_0]

/-- `S7` at world 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_0 : S7 0 = x7_0 := rfl

/-- `S7` at world 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_1 : S7 1 = x7_0 := rfl

/-- `S7` at world 2.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_2 : S7 2 = x7_1 := rfl

/-- `S7` at world 3.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_3 : S7 3 = x7_2 := rfl

/-- `S7` at world 4.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_4 : S7 4 = x7_2 := rfl

/-- `S7` at world 5.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_5 : S7 5 = x7_0 := rfl

/-- `S7` at world 6.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_6 : S7 6 = x7_0 := rfl

/-- **Any recommended strategy for the menu is `S7`** (unique maximiser at every world, `π`-null
or not): no tie-break is available, so the weak and the literal reading of Value agree here.
Source: audit r3 adversarial B1; [[Deference Done Better]] §1 l. 117 (recommended strategies)
Kind: L
Fidelity: n/a -/
theorem S7_recommended_eq {S : Fin 7 → (Fin 7 → ℝ)} (hS : F7.Recommended {x7_0, x7_1, x7_2} S) :
    ∀ w, S w = S7 w := by
  obtain ⟨⟨hmem, _⟩, hopt⟩ := hS
  obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩, ⟨d0, d1, d2⟩⟩ := scores7
  have hP : ∀ w, F7.P w = P7 w := fun _ => rfl
  have w0 : S 0 = S7 0 := by
    have hm := hmem 0
    simp only [mem_insert, mem_singleton] at hm
    have h0 := hopt 0 x7_0 (by simp)
    have h1 := hopt 0 x7_1 (by simp)
    have h2 := hopt 0 x7_2 (by simp)
    simp only [hP, P7_0] at h0 h1 h2
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
    simp only [hP, P7_1] at h0 h1 h2
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
    simp only [hP, P7_2] at h0 h1 h2
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
    simp only [hP, P7_3] at h0 h1 h2
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
    simp only [hP, P7_4] at h0 h1 h2
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
    simp only [hP, P7_5] at h0 h1 h2
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
    simp only [hP, P7_6] at h0 h1 h2
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

/-- The forced strategy is worth `3/20` to the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S7_value : stratValue π7 S7 = 3 / 20 := by
  simp only [stratValue, Fin.sum_univ_seven, S7_0, S7_1, S7_2, S7_3, S7_4, S7_5, S7_6]
  simp only [π7, x7_0, x7_1, x7_2, Function.comp, vec7_two, vec7_three, vec7_four, vec7_five,
    vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1, Q7_2, Q7_3,
    Q7_4, Q7_5, Q7_6, vec3_two]
  norm_num

/-- The fixed option `x₁` is worth `13/60` to the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem x7_1_value : E π7 x7_1 = 13 / 60 := by
  simp only [E, Fin.sum_univ_seven, π7, x7_1, Function.comp, vec7_two, vec7_three, vec7_four,
    vec7_five, vec7_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Q7_0, Q7_1,
    Q7_2, Q7_3, Q7_4, Q7_5, Q7_6, vec3_two]
  norm_num

/-- **Weak local Value fails**: on the three-option menu the only recommended strategy is worth
`3/20 < 13/60 = E_π(x₁)`.
Source: audit r3 adversarial B1; [[Deference Done Better]] App. B l. 472, fn 64 l. 1235
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem F7_not_weakValuesWrt : ¬ WeakValuesWrt Q7 π7 F7 := by
  intro h
  obtain ⟨S, hS, hall⟩ := h {x7_0, x7_1, x7_2} (insert_nonempty _ _) menu7_meas
  have h1 := hall x7_1 (by simp)
  have hSv : stratValue π7 S = stratValue π7 S7 := by
    simp only [stratValue]
    apply sum_congr rfl
    intro w _
    rw [S7_recommended_eq hS w]
  rw [hSv, S7_value, x7_1_value] at h1
  norm_num at h1

/-- **The frame is an `hdet`-frame for `Q7`**: rows on the support (here: everywhere, `π7` has
full support) are determined by the pushforward `Q_* P_w` — two rows with the same expert
expectation on every `Q7`-measurable variable are equal. So the report's other surviving form of
fn 65 (the literal reading restricted to `hdet`-frames) applies to this frame.
Source: audit r3 adversarial B1; this package (TwoCell's `hdet`)
Kind: L
Fidelity: n/a -/
theorem F7_hdet : ∀ w v, 0 < π7 w → 0 < π7 v →
    (∀ x : Fin 3 → ℝ, E (F7.P w) (x ∘ Q7) = E (F7.P v) (x ∘ Q7)) → F7.P w = F7.P v := by
  intro w v _ _ h
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have hP : ∀ w, F7.P w = P7 w := fun _ => rfl
  simp only [hP] at h0 h1 ⊢
  fin_cases w <;> fin_cases v <;>
    simp [P7_0, P7_1, P7_2, P7_3, P7_4, P7_5, P7_6, E_r7a, E_r7b, E_r7c, E_r7d, vec3_two]
      at h0 h1 ⊢ <;>
    first
      | (norm_num at h0; done)
      | (norm_num at h1; done)

/-- **Literal local Value fails** a fortiori (`ValuesWrt → WeakValuesWrt`).
Source: audit r3 adversarial B1; [[Deference Done Better]] fn 64 l. 1235
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem F7_not_valuesWrt : ¬ ValuesWrt Q7 π7 F7 :=
  fun h => F7_not_weakValuesWrt (ValuesWrt.weakValuesWrt h)

/-- **fn 65's conjecture in the weak reading is refuted at three cells**: there is a question
with three cells (`Q7` is onto `Fin 3`), a simplex deferrer with full support and a frame with
local Total Trust and without weak local Value. Replaces the OPEN
`localTotalTrust_imp_weakLocalValue_open` of repair rounds 0–2 (its statement is false:
`weakLocalValue_open_statement_false`). With `weakValuesWrt_questionOf_of_simpleTrustOn` (two
cells, true) and `totalTrust_imp_weakValuesWrt_id` (the finest question, true), the conjecture
breaks exactly at three cells.
Source: [[Deference Done Better]] fn 65 l. 1237 (the open direction), fn 64 l. 1235, App. B
l. 472 (weak Value); [[ddb-mm-authors]] T2 l. 139; [[legitimacy-general-final]] Open problem 4
l. 205; [[approval-final]] O1 l. 197; audit r3 adversarial B1 (probe `WeakOpenRefuted.lean`)
Kind: N+
Fidelity: exact (refutation of the universal statement by one instance; weak reading)
Hyps: (a) none -/
theorem localTotalTrust_imp_weakLocalValue_refuted :
    ∃ (Q : Fin 7 → Fin 3) (π : Fin 7 → ℝ) (F : Frame (Fin 7)),
      Function.Surjective Q ∧ π ∈ stdSimplex ℝ (Fin 7) ∧ (∀ w, 0 < π w) ∧
        TotalTrustWrt Q π F ∧ ¬ WeakValuesWrt Q π F :=
  ⟨Q7, π7, F7, Q7_surjective, π7_mem, π7_pos, F7_totalTrustWrt, F7_not_weakValuesWrt⟩

/-- **fn 65's literal reading restricted to `hdet`-frames is refuted at three cells**: the same
frame has its rows determined by the pushforward on the support, local Total Trust, and no
local Value. (At two cells this form is a theorem: `valuesWrt_questionOf_of_simpleTrustOn`.)
Source: [[Deference Done Better]] fn 65 l. 1237, fn 64 l. 1235; this package (the `hdet` form,
report T4(d)); audit r3 adversarial B1
Kind: N+
Fidelity: exact (refutation by one instance; the `hdet` restriction stated as a conjunct)
Hyps: (a) none -/
theorem localTotalTrust_imp_localValue_hdet_refuted :
    ∃ (Q : Fin 7 → Fin 3) (π : Fin 7 → ℝ) (F : Frame (Fin 7)),
      Function.Surjective Q ∧ π ∈ stdSimplex ℝ (Fin 7) ∧
        (∀ w v, 0 < π w → 0 < π v →
          (∀ x : Fin 3 → ℝ, E (F.P w) (x ∘ Q) = E (F.P v) (x ∘ Q)) → F.P w = F.P v) ∧
        TotalTrustWrt Q π F ∧ ¬ ValuesWrt Q π F :=
  ⟨Q7, π7, F7, Q7_surjective, π7_mem, F7_hdet, F7_totalTrustWrt, F7_not_valuesWrt⟩

/-- **The former OPEN's statement is false**: `localTotalTrust_imp_weakLocalValue_open` of repair
rounds 0–2 (`∀ Q π F, π ∈ stdSimplex → TotalTrustWrt Q π F → WeakValuesWrt Q π F`), specialised
to `W = Fin 7`, `C = Fin 3`, negated.
Source: audit r3 adversarial B1; `corr-legit-general-open.txt` through repair round 2
Kind: N+
Fidelity: exact (the OPEN's statement at one `(W, C)`, negated)
Hyps: (a) none -/
theorem weakLocalValue_open_statement_false :
    ¬ ∀ (Q : Fin 7 → Fin 3) (π : Fin 7 → ℝ) (F : Frame (Fin 7)),
      π ∈ stdSimplex ℝ (Fin 7) → TotalTrustWrt Q π F → WeakValuesWrt Q π F := by
  intro h
  exact F7_not_weakValuesWrt (h Q7 π7 F7 π7_mem F7_totalTrustWrt)

end

end Cleanroom.Corrigibility.CorrLegitGeneral
