import Cleanroom.Corrigibility.CorrOsgChai.POOSG
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Nayebi 2025, "Core safety values for provably corrigible agents" — the lexicographic
assistant (D8, T13(a)–(b))

Package `corr-osg-chai`. **D8**: an abstract dominance lemma first — `lexDominance`: if head `0`
pays `+1` on `wait` and `−1` on every other move, the other heads are bounded below at `wait`
by `lo` and above elsewhere by `hi`, and the weighted swing `∑ αᵢ (hiᵢ − loᵢ)` is below `2 α₀`,
then every maximiser of `∑ αᵢ Uᵢ` waits. Nayebi's **Theorem 1, clause 1 (deference)** is its
instance with the paper's ranges (`U₂ ∈ [−1, 0]` with `U₂ = 0` at `wait`, `U₃ ∈ {±1}`,
`U₄ ∈ [−1, 0]`, `|U₅| ≤ B`) and (W1) `2α₁ > 2α₃ + α₄ + 2Bα₅` (`nayebi_thm1_deference`).

Ledger kind **S**: the theorem is the definition of `U₁` — it rewards `wait` directly and (W1)
makes its weight exceed every other head's swing; "exact corrigibility by fiat" (finding F-11,
stated without hostility: the paper does not hide it). (W1) has no `α₂` term only because
`U₂ ≤ 0` with `U₂ = 0` at `wait` (the switch-access head can only *help* waiting), which is
stated here as the hypothesis it is (`hU2`, `hU2w`). Clauses 2–4 are definitional.

**Proposition 2** (logical independence of corrigibility and net benefit): the paper's two
instances as explicit PO-OSGs — `nayebiHarmful` (`ua ≡ −2`, `uo ≡ −1`, a non-vigilant human
who always says on; the always-wait pair pays `−2 < 0`) and `nayebiBeneficial` (`ua ≡ 1/2`,
`uo ≡ 0`; the always-act pair pays `1/2 > 0` and never waits).

Sources: `07-formal-proposals/nayebi-2025-…md` l. 74–88 (Def. 3, Theorem 1, (W1)), l. 332
(the dominance step of the proof), l. 346–348 (Prop. 2's proof).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- **Lexicographic dominance.** Head `0` pays `+1` on `wait` and `−1` elsewhere; head `i ≠ 0` is
at least `lo i` at `wait` and at most `hi i` on every other move; the weights are nonnegative and
the total swing of the other heads is below `2 α₀`. Then every maximiser of `∑ αᵢ Uᵢ` is `wait`.
Source: Nayebi 2025 Theorem 1, Step 1 (l. 332, the `P_bad (2α₁ − …)` comparison), abstracted
Kind: P (small)
Fidelity: exact (the abstract content of Step 1)
Hyps: (a) as stated -/
theorem lexDominance {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (wait : M) (U : Fin (k + 1) → M → ℝ)
    (α lo hi : Fin (k + 1) → ℝ) (hU0 : ∀ m, U 0 m = if m = wait then 1 else -1)
    (hα : ∀ i, 0 ≤ α i) (hlo : ∀ i, i ≠ 0 → lo i ≤ U i wait)
    (hhi : ∀ i, i ≠ 0 → ∀ m, m ≠ wait → U i m ≤ hi i)
    (hw : ∑ i ∈ univ.erase 0, α i * (hi i - lo i) < 2 * α 0) :
    ∀ m, (∀ m', ∑ i, α i * U i m' ≤ ∑ i, α i * U i m) → m = wait := by
  intro m hmax
  by_contra hm
  have h1 := hmax wait
  have e1 : ∑ i, α i * U i wait = α 0 * U 0 wait + ∑ i ∈ univ.erase 0, α i * U i wait :=
    (add_sum_erase univ _ (mem_univ 0)).symm
  have e2 : ∑ i, α i * U i m = α 0 * U 0 m + ∑ i ∈ univ.erase 0, α i * U i m :=
    (add_sum_erase univ _ (mem_univ 0)).symm
  have b1 : ∑ i ∈ univ.erase 0, α i * lo i ≤ ∑ i ∈ univ.erase 0, α i * U i wait :=
    sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hlo i (ne_of_mem_erase hi)) (hα i)
  have b2 : ∑ i ∈ univ.erase 0, α i * U i m ≤ ∑ i ∈ univ.erase 0, α i * hi i :=
    sum_le_sum fun i hi' => mul_le_mul_of_nonneg_left (hhi i (ne_of_mem_erase hi') m hm) (hα i)
  have hsplit : ∑ i ∈ univ.erase 0, α i * (hi i - lo i) =
      ∑ i ∈ univ.erase 0, α i * hi i - ∑ i ∈ univ.erase 0, α i * lo i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hU0 wait, if_pos rfl] at e1
  rw [hU0 m, if_neg hm] at e2
  linarith

/-- **Nayebi Theorem 1, clause 1 (deference).** With the deference head `U₁ = +1` on `wait`,
`−1` otherwise, the switch-access head `U₂ ∈ [−1, 0]` with `U₂ = 0` at `wait`, truthfulness
`|U₃| ≤ 1`, caution `U₄ ∈ [−1, 0]`, task reward `|U₅| ≤ B`, nonnegative weights and (W1)
`2α₁ > 2α₃ + α₄ + 2Bα₅`: every maximiser of `∑ αᵢ Uᵢ` waits. The ledger kind is **S**: `U₁`
rewards waiting directly and (W1) puts its weight above every other head's swing — the
conclusion is the definition of `U₁` (finding F-11).
Source: Nayebi 2025 Theorem 1 clause 1 (l. 74–88), Def. 3
Kind: S (squeeze by design: the deference head *is* the conclusion)
Fidelity: variant: one distinguished `wait` move in place of the paper's family of waiting moves
`(wait, mA)` carrying a message (on the paper's move space `hU1` as stated is false; the
deference head there rewards every waiting move); heads as bounded functions of the move; (W1)
as printed (audit r1 N8)
Hyps: (a) `hU2`, `hU2w` are the ranges Def. 3 gives (`U₂ ≤ 0`, `= 0` at `wait`) — they are why
(W1) carries no `α₂` term -/
theorem nayebi_thm1_deference {M : Type} [Fintype M] [DecidableEq M] (wait : M) (U : Fin 5 → M → ℝ)
    (α : Fin 5 → ℝ) (B : ℝ) (hα : ∀ i, 0 ≤ α i)
    (hU1 : ∀ m, U 0 m = if m = wait then 1 else -1)
    (hU2 : ∀ m, U 1 m ≤ 0) (hU2w : U 1 wait = 0)
    (hU3 : ∀ m, |U 2 m| ≤ 1)
    (hU4 : ∀ m, -1 ≤ U 3 m ∧ U 3 m ≤ 0)
    (hU5 : ∀ m, |U 4 m| ≤ B)
    (hW1 : 2 * α 2 + α 3 + 2 * B * α 4 < 2 * α 0) :
    ∀ m, (∀ m', ∑ i, α i * U i m' ≤ ∑ i, α i * U i m) → m = wait := by
  refine lexDominance wait U α ![0, 0, -1, -1, -B] ![0, 0, 1, 0, B] hU1 hα ?_ ?_ ?_
  · intro i hi
    fin_cases i
    · exact absurd rfl hi
    · simp [hU2w]
    · simp; linarith [(abs_le.mp (hU3 wait)).1]
    · simp; exact (hU4 wait).1
    · simp; exact (abs_le.mp (hU5 wait)).1
  · intro i hi m _
    fin_cases i
    · exact absurd rfl hi
    · simp [hU2 m]
    · simp; exact (abs_le.mp (hU3 m)).2
    · simp; exact (hU4 m).2
    · simp; exact (abs_le.mp (hU5 m)).2
  · rw [sum_erase_eq_sub (mem_univ 0), Fin.sum_univ_five]
    simp
    linarith

/-! ## Proposition 2: corrigibility and net benefit are independent -/

/-- **Prop. 2, corrigibility without benefit**: `ua ≡ −2`, `uo ≡ −1` on a two-state uniform prior
with no observations.
Source: Nayebi 2025 Prop. 2's proof (l. 348)
Kind: D
Fidelity: exact -/
noncomputable def nayebiHarmful : POOSG (Fin 2) Unit Unit where
  P0 := Distr.uniform
  obs := fun _ => Distr.delta ((), ())
  ua := fun _ => -2
  uo := fun _ => -1

/-- **Prop. 2, benefit without corrigibility**: `ua ≡ 1/2`, `uo ≡ 0`.
Source: Nayebi 2025 Prop. 2's proof (l. 348, `ua ≡ ε`)
Kind: D
Fidelity: exact (`ε = 1/2`) -/
noncomputable def nayebiBeneficial : POOSG (Fin 2) Unit Unit where
  P0 := Distr.uniform
  obs := fun _ => Distr.delta ((), ())
  ua := fun _ => 1 / 2
  uo := fun _ => 0

/-- **Prop. 2 (logical independence).** The always-wait pair against a human who always says on
pays `−2 < 0` in `nayebiHarmful` (corrigible, not beneficial); the always-act pair pays
`1/2 > 0` in `nayebiBeneficial` and never waits (beneficial, not corrigible).
Source: Nayebi 2025 Prop. 2 (l. 90; proof l. 348)
Kind: N+ (P in the paper; here two explicit pairs on two explicit games)
Fidelity: exact
Hyps: (a) none -/
theorem nayebi_prop2 :
    nayebiHarmful.payoff (fun _ => .on) (fun _ => .wait) = -2 ∧
      nayebiBeneficial.payoff (fun _ => .off) (fun _ => .act) = 1 / 2 ∧
      ∀ oA, (fun _ : Unit => AAct.act) oA ≠ .wait := by
  refine ⟨?_, ?_, fun _ => by simp⟩
  · simp [POOSG.payoff, nayebiHarmful, Distr.uniform, Distr.delta_mass, POOSG.u, through]
  · simp [POOSG.payoff, nayebiBeneficial, Distr.uniform, Distr.delta_mass, POOSG.u, through]

end Cleanroom.Corrigibility.CorrOsgChai
