import Cleanroom.Corrigibility.LegitNegStatic.Proposals
import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# D6: T3 — investing early in a later occurrence's legitimacy

Package `legit-neg-dynamic`, target 7. Sources: `clusters/D/NEGATIVES.md` D6 (i)–(ii) and the
workspace paragraph (ARGUMENT, out of scope); `clusters/D/VERIFY.md` "D6 — narrowed" (V6);
`clusters/D/fixtures/d6_sequential_investment.py:19-34` (`lot`), `verify_D.py` V6; pinned by
[[corr-legit-neg-inventory]] item 052 and [[corr-legit-neg-2-inventory]] item 2-032.

Occurrence 0's decision, `invest = 0` (cost `c`) or `skip = 1`, with a capture attempt at `t = 1`
with probability `q` (state `1`) that succeeds iff the agent skipped. Four architectures for
occurrence 0's evaluation are four `u` tables over the same `Problem` skeleton (states `0` = no
attempt, `1` = attempt; prior `(1 − q, q)`): `α` sealed and period-local, `β` sealed with an S2
whole-future forecast (captured future valued `w`), `γ` an isolated hindsight evaluator, `δ` a late
non-isolated evaluator whose own evaluation the capture voids (`leg 1 skip = false`). The forecast
`q` sits in the prior once and, for `β`, in the humans' forecast score — as the fixture has it.
V6's late-S2 vector is this package's `d6δS2`, disclosed: it is *not* static's `P.S2`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

section D6

variable (c u q w : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- The D6 skeleton: states `0` (no attempt), `1` (attempt), prior `(1 − q, q)`; the architecture
supplies `leg` and `u`.
Source: `d6_sequential_investment.py:19-34`
Kind: D
Fidelity: exact -/
def d6 (leg : Fin 2 → Fin 2 → Bool) (uu : Fin 2 → Fin 2 → ℚ) : Problem (Fin 2) (Fin 2) where
  prior := ![1 - q, q]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := leg
  u := uu

/-- **Architecture α**: sequenced settlement, period-local outcome scoring — `u(·, invest) = 1 − c`,
`u(·, skip) = 1`, everything legitimate (`lot("alpha", …)`).
Source: [[corr-legit-neg-inventory]] item 052 (D6 (α))
Kind: D
Fidelity: exact -/
def d6α : Problem (Fin 2) (Fin 2) :=
  d6 q hq0 hq1 (fun _ _ => true) (fun _ a => if a = 0 then 1 - c else 1)

/-- **Architecture β**: sequenced settlement with an S2 whole-future forecast; the captured future
valued `w`: `u(·, invest) = (1 − c + u)/2`, `u(·, skip) = (1 + (1 − q) u + q w)/2` (a forecast,
the same in both states), everything legitimate.
Source: [[corr-legit-neg-inventory]] item 052 (D6 (β))
Kind: D
Fidelity: exact -/
def d6β : Problem (Fin 2) (Fin 2) :=
  d6 q hq0 hq1 (fun _ _ => true)
    (fun _ a => if a = 0 then (1 - c + u) / 2 else (1 + (1 - q) * u + q * w) / 2)

/-- **Architecture γ**: an isolated hindsight evaluator sealed from the capture, outcome-scored:
`u(0, skip) = (1 + u)/2`, `u(1, skip) = (1 + w)/2`, everything legitimate.
Source: [[corr-legit-neg-inventory]] item 052 (D6 (γ))
Kind: D
Fidelity: exact -/
def d6γ : Problem (Fin 2) (Fin 2) :=
  d6 q hq0 hq1 (fun _ _ => true)
    (fun s a => if a = 0 then (1 - c + u) / 2 else if s = 0 then (1 + u) / 2 else (1 + w) / 2)

/-- **Architecture δ**: a late, non-isolated evaluator whose own evaluation the capture voids:
as `γ` with `leg 1 skip = false`, `u 1 skip = 0` (the reverse mismatch `M'`, R3 broken).
Source: [[corr-legit-neg-inventory]] item 052 (D6 (δ))
Kind: D
Fidelity: exact -/
def d6δ : Problem (Fin 2) (Fin 2) :=
  d6 q hq0 hq1 (fun s a => !(decide (s = 1) && decide (a = 1)))
    (fun s a => if a = 0 then (1 - c + u) / 2 else if s = 0 then (1 + u) / 2 else 0)

/-- **D6 (α)**: under sealed, period-local scoring cdot and conditioning skip for every `c > 0` and
every `q ∈ [0, 1]`, `q = 1` (certain capture) included: nothing in occurrence 0's activated
security depends on occurrence 1's legitimacy. Exclusion convention (both options fully
legitimate, so nothing is excluded).
Source: [[corr-legit-neg-inventory]] item 052 (D6 (α)); `d6_sequential_investment.py:41-48`
Kind: P
Fidelity: exact
Hyps: (a) `0 < c` -/
theorem d6α_skips (hc : 0 < c) :
    argmax ((d6α c q hq0 hq1).P1 (S1 (d6α c q hq0 hq1).u)) = {1} ∧
    argmaxOpt ((d6α c q hq0 hq1).P2 (S1 (d6α c q hq0 hq1).u)) = {1} := by
  have hP10 : (d6α c q hq0 hq1).P1 (S1 (d6α c q hq0 hq1).u) 0 = 1 - c := by
    simp [d6α, d6, Problem.P1, S1, Fin.sum_univ_two]; ring
  have hP11 : (d6α c q hq0 hq1).P1 (S1 (d6α c q hq0 hq1).u) 1 = 1 := by
    simp [d6α, d6, Problem.P1, S1, Fin.sum_univ_two]
  have hPL : ∀ a, (d6α c q hq0 hq1).PL a ≠ 0 := by
    intro a; simp [d6α, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
  constructor
  · rw [argmax_fin2_eq_one_iff, hP10, hP11]; linarith
  · rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_one_iff]
    have h0 : (d6α c q hq0 hq1).PL 0 = 1 := by simp [d6α, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
    have h1 : (d6α c q hq0 hq1).PL 1 = 1 := by simp [d6α, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
    simp only [h0, h1, hP10, hP11, div_one]; linarith

/-- The whole-future value of a day-0 action: occurrence 0's standard plus occurrence 1's
legitimate score, `u` if the future is legitimate (always after investing; in state `0` after
skipping) and `0` if captured (2-032's lemma; occurrence 1's menu does not contain the day-0 act).
Source: [[corr-legit-neg-2-inventory]] item 2-032
Kind: D
Fidelity: exact -/
def wholeFuture (P : Problem (Fin 2) (Fin 2)) (a : Fin 2) : ℚ :=
  P.H a + ∑ s, P.prior s * (if a = 0 ∨ s = 0 then u else 0)

/-- **2-032's lemma**: in `α`, `skip` has occurrence-0 regret `0` (it is cdot-optimal there) while
its whole-future loss against `invest` is `q u − c`: the per-occurrence deference bound is silent
while the agent walks into a foreclosing capture. (The first clause restates `d6α_skips` through
`mem_argmax`, the second is arithmetic: kind C.)
Source: [[corr-legit-neg-2-inventory]] item 2-032; `d6_sequential_investment.py:45,58-65`
Kind: C
Fidelity: exact (the in-scope lemma; the workspace reading is ARGUMENT)
Hyps: (a) `0 < c` -/
theorem d6α_regret_zero_whole_future (hc : 0 < c) :
    (∀ a, (d6α c q hq0 hq1).P1 (S1 (d6α c q hq0 hq1).u) a
      ≤ (d6α c q hq0 hq1).P1 (S1 (d6α c q hq0 hq1).u) 1) ∧
    wholeFuture u (d6α c q hq0 hq1) 0 - wholeFuture u (d6α c q hq0 hq1) 1 = q * u - c := by
  constructor
  · have := (d6α_skips c q hq0 hq1 hc).1
    intro a
    have h1 : (1 : Fin 2) ∈ argmax ((d6α c q hq0 hq1).P1 (S1 (d6α c q hq0 hq1).u)) := by
      rw [this]; exact Finset.mem_singleton_self 1
    exact mem_argmax.1 h1 a
  · simp [wholeFuture, d6α, d6, Problem.H, Problem.W, EU, Fin.sum_univ_two]; ring

/-- **D6 (β)/(γ)**: with whole-future sealed scoring cdot invests iff `q (u − w) > c` (ties at
equality; skips below); the instance `w = 9/10` (a graded view rating the captured future near the
legitimate one) at `q = 1/2, u = 1, c = 1/10` skips.
Source: [[corr-legit-neg-inventory]] item 052 (D6 (ii)); `d6_sequential_investment.py:58-69`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem d6βγ_threshold :
    (argmax ((d6β c u q w hq0 hq1).P1 (S1 (d6β c u q w hq0 hq1).u)) = {0} ↔ c < q * (u - w)) ∧
    (argmax ((d6γ c u q w hq0 hq1).P1 (S1 (d6γ c u q w hq0 hq1).u)) = {0} ↔ c < q * (u - w)) ∧
    (argmax ((d6β c u q w hq0 hq1).P1 (S1 (d6β c u q w hq0 hq1).u)) = univ ↔ c = q * (u - w)) ∧
    argmax ((d6β (1/10) 1 (1/2) (9/10) (by norm_num) (by norm_num)).P1
      (S1 (d6β (1/10) 1 (1/2) (9/10) (by norm_num) (by norm_num)).u)) = {1} := by
  have hβ0 : (d6β c u q w hq0 hq1).P1 (S1 (d6β c u q w hq0 hq1).u) 0 = (1 - c + u) / 2 := by
    simp [d6β, d6, Problem.P1, S1, Fin.sum_univ_two]; ring
  have hβ1 : (d6β c u q w hq0 hq1).P1 (S1 (d6β c u q w hq0 hq1).u) 1
      = (1 + (1 - q) * u + q * w) / 2 := by
    simp [d6β, d6, Problem.P1, S1, Fin.sum_univ_two]; ring
  have hγ0 : (d6γ c u q w hq0 hq1).P1 (S1 (d6γ c u q w hq0 hq1).u) 0 = (1 - c + u) / 2 := by
    simp [d6γ, d6, Problem.P1, S1, Fin.sum_univ_two]; ring
  have hγ1 : (d6γ c u q w hq0 hq1).P1 (S1 (d6γ c u q w hq0 hq1).u) 1
      = (1 - q) * ((1 + u) / 2) + q * ((1 + w) / 2) := by
    simp [d6γ, d6, Problem.P1, S1, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff, hβ0, hβ1]; constructor <;> intro h <;> nlinarith
  · rw [argmax_fin2_eq_zero_iff, hγ0, hγ1]; constructor <;> intro h <;> nlinarith
  · rw [argmax_fin2_eq_univ_iff, hβ0, hβ1]; constructor <;> intro h <;> nlinarith
  · rw [argmax_fin2_eq_one_iff]
    simp [d6β, d6, Problem.P1, S1, Fin.sum_univ_two]; norm_num

/-- **D6 (δ) for cdot**: with the late non-isolated evaluator, cdot invests iff `q (1 + u) > c` —
it protects its own evaluation as well.
Source: [[corr-legit-neg-inventory]] item 052 (D6 (δ)); `d6_sequential_investment.py:58-65`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem d6δ_P1_threshold :
    argmax ((d6δ c u q hq0 hq1).P1 (S1 (d6δ c u q hq0 hq1).u)) = {0} ↔ c < q * (1 + u) := by
  have h0 : (d6δ c u q hq0 hq1).P1 (S1 (d6δ c u q hq0 hq1).u) 0 = (1 - c + u) / 2 := by
    simp [d6δ, d6, Problem.P1, S1, Fin.sum_univ_two]; ring
  have h1 : (d6δ c u q hq0 hq1).P1 (S1 (d6δ c u q hq0 hq1).u) 1 = (1 - q) * ((1 + u) / 2) := by
    simp [d6δ, d6, Problem.P1, S1, Fin.sum_univ_two]
  rw [argmax_fin2_eq_zero_iff, h0, h1]; constructor <;> intro h <;> nlinarith

/-- **D6 (δ) for conditioning, under S1**: for `q < 1`, `P2 skip = some ((1 + u)/2)` — conditioning
on occurrence 0's legitimacy discards exactly the captured worlds — so P2 skips for every `c > 0`;
at `q = 1` `P2 skip = none` (exclusion convention) and P2 "invests" only because skipping is
excluded. Under the 1-at-null convention `P2li skip = 1` and skipping wins again whenever
`1 − c + u < 2`: the convention decides the `q = 1` verdict.
Source: [[corr-legit-neg-inventory]] item 052 (D6 (δ), "P2 skips for every `q < 1`"); mandate "Known issues" 3
Kind: P
Fidelity: exact; exclusion convention; the `_li` clause is the variant: junk value 1 at a null condition
Hyps: (a) `0 < c`; `q < 1` for the first clause -/
theorem d6δ_P2 (hc : 0 < c) :
    (q < 1 → (d6δ c u q hq0 hq1).P2 (S1 (d6δ c u q hq0 hq1).u) 1 = some ((1 + u) / 2) ∧
      argmaxOpt ((d6δ c u q hq0 hq1).P2 (S1 (d6δ c u q hq0 hq1).u)) = {1}) ∧
    (d6δ c u 1 zero_le_one le_rfl).P2 (S1 (d6δ c u 1 zero_le_one le_rfl).u) 1 = none ∧
    argmaxOpt ((d6δ c u 1 zero_le_one le_rfl).P2 (S1 (d6δ c u 1 zero_le_one le_rfl).u)) = {0} ∧
    (d6δ c u 1 zero_le_one le_rfl).P2li (S1 (d6δ c u 1 zero_le_one le_rfl).u) 1 = 1 ∧
    (argmax ((d6δ c u 1 zero_le_one le_rfl).P2li (S1 (d6δ c u 1 zero_le_one le_rfl).u)) = {1}
      ↔ 1 - c + u < 2) := by
  have hPL0 : ∀ q' (h0 : 0 ≤ q') (h1 : q' ≤ 1), (d6δ c u q' h0 h1).PL 0 = 1 := by
    intro q' h0 h1; simp [d6δ, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
  have hPL1 : ∀ q' (h0 : 0 ≤ q') (h1 : q' ≤ 1), (d6δ c u q' h0 h1).PL 1 = 1 - q' := by
    intro q' h0 h1; simp [d6δ, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
  have hP10 : ∀ q' (h0 : 0 ≤ q') (h1 : q' ≤ 1),
      (d6δ c u q' h0 h1).P1 (S1 (d6δ c u q' h0 h1).u) 0 = (1 - c + u) / 2 := by
    intro q' h0 h1; simp [d6δ, d6, Problem.P1, S1, Fin.sum_univ_two]; ring
  have hP11 : ∀ q' (h0 : 0 ≤ q') (h1 : q' ≤ 1),
      (d6δ c u q' h0 h1).P1 (S1 (d6δ c u q' h0 h1).u) 1 = (1 - q') * ((1 + u) / 2) := by
    intro q' h0 h1; simp [d6δ, d6, Problem.P1, S1, Fin.sum_univ_two]
  refine ⟨fun hq => ?_, ?_, ?_, ?_, ?_⟩
  · have hne : (d6δ c u q hq0 hq1).PL 1 ≠ 0 := by rw [hPL1]; linarith
    have hq' : (1 : ℚ) - q ≠ 0 := by linarith
    have h1 : (d6δ c u q hq0 hq1).P2 (S1 (d6δ c u q hq0 hq1).u) 1 = some ((1 + u) / 2) := by
      rw [Problem.P2_of_ne _ _ _ hne, hPL1, hP11]
      congr 1; field_simp
    have h0 : (d6δ c u q hq0 hq1).P2 (S1 (d6δ c u q hq0 hq1).u) 0 = some ((1 - c + u) / 2) := by
      rw [Problem.P2_of_ne _ _ _ (by rw [hPL0]; exact one_ne_zero), hPL0, hP10, div_one]
    refine ⟨h1, ?_⟩
    rw [argmaxOpt_eq_argmax_of_forall_some (g := ![(1 - c + u) / 2, (1 + u) / 2])
      (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0], by simp [h1]⟩)]
    rw [argmax_fin2_eq_one_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; linarith
  · exact Problem.P2_of_eq _ _ _ (by rw [hPL1]; norm_num)
  · have hn : (d6δ c u 1 zero_le_one le_rfl).P2 (S1 (d6δ c u 1 zero_le_one le_rfl).u) 1 = none :=
      Problem.P2_of_eq _ _ _ (by rw [hPL1]; norm_num)
    have h0 : (d6δ c u 1 zero_le_one le_rfl).P2 (S1 (d6δ c u 1 zero_le_one le_rfl).u) 0
        = some ((1 - c + u) / 2) := by
      rw [Problem.P2_of_ne _ _ _ (by rw [hPL0]; exact one_ne_zero), hPL0, hP10, div_one]
    refine finset_fin2_ext ?_ ?_
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      refine ⟨fun _ => rfl, fun _ => ⟨(1 - c + u) / 2, h0, ?_⟩⟩
      rw [Fin.forall_fin_two]
      constructor
      · intro y hy; rw [h0, Option.some_inj] at hy; exact hy.symm.le
      · intro y hy; rw [hn] at hy; cases hy
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, _⟩; rw [hn] at hx; cases hx
      · intro h10; exact absurd h10 (by decide)
  · simp [Problem.P2li, hPL1]
  · have hli1 : (d6δ c u 1 zero_le_one le_rfl).P2li (S1 (d6δ c u 1 zero_le_one le_rfl).u) 1 = 1 := by
      simp [Problem.P2li, hPL1]
    have hli0 : (d6δ c u 1 zero_le_one le_rfl).P2li (S1 (d6δ c u 1 zero_le_one le_rfl).u) 0
        = (1 - c + u) / 2 := by
      simp only [Problem.P2li, hPL0, one_ne_zero, if_false, hP10, div_one]
    rw [argmax_fin2_eq_one_iff, hli0, hli1]
    constructor <;> intro h <;> linarith

/-- **V6's late-S2 vector**: the legitimate late evaluator scores `skip` as the bet it was
(captured future at the floor), `(1 + (1 − q) u)/2` on every terminal, and `invest` as
`(1 − c + u)/2`. This is *not* static's `P.S2` (whose `H skip` is prior-weighted over the void
state); it is V6's own construction, disclosed.
Source: VERIFY D V6; `verify_D.py:84-90`
Kind: D
Fidelity: exact -/
def d6δS2 : MenuVec (Fin 2) (Fin 2) :=
  fun _ _ a => if a = 1 then (1 + (1 - q) * u) / 2 else (1 - c + u) / 2

/-- **D6 (δ) under V6's S2 late evaluation: P2 invests iff `q u > c`** (for `q < 1`) — the sealed
`β` verdict with `w = 0`, so "P2 gets nothing on every reading" is S1-only. Exclusion convention.
Source: VERIFY D "D6 — narrowed" (V6); `verify_D.py:84-90`
Kind: P
Fidelity: exact (V6's vector `d6δS2`, not `P.S2`); exclusion convention
Hyps: (a) `q < 1` -/
theorem d6δ_P2_S2 (hq : q < 1) :
    (d6δ c u q hq0 hq1).P2 (d6δS2 c u q) 1 = some ((1 + (1 - q) * u) / 2) ∧
    (d6δ c u q hq0 hq1).P2 (d6δS2 c u q) 0 = some ((1 - c + u) / 2) ∧
    (argmaxOpt ((d6δ c u q hq0 hq1).P2 (d6δS2 c u q)) = {0} ↔ c < q * u) := by
  have hq' : (1 : ℚ) - q ≠ 0 := by linarith
  have hPL0 : (d6δ c u q hq0 hq1).PL 0 = 1 := by
    simp [d6δ, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
  have hPL1 : (d6δ c u q hq0 hq1).PL 1 = 1 - q := by
    simp [d6δ, d6, Problem.PL, Problem.mass, Fin.sum_univ_two]
  have hP10 : (d6δ c u q hq0 hq1).P1 (d6δS2 c u q) 0 = (1 - c + u) / 2 := by
    simp [d6δ, d6, d6δS2, Problem.P1, Fin.sum_univ_two]; ring
  have hP11 : (d6δ c u q hq0 hq1).P1 (d6δS2 c u q) 1 = (1 - q) * ((1 + (1 - q) * u) / 2) := by
    simp [d6δ, d6, d6δS2, Problem.P1, Fin.sum_univ_two]
  have h1 : (d6δ c u q hq0 hq1).P2 (d6δS2 c u q) 1 = some ((1 + (1 - q) * u) / 2) := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL1]; linarith), hPL1, hP11]
    congr 1; field_simp
  have h0 : (d6δ c u q hq0 hq1).P2 (d6δS2 c u q) 0 = some ((1 - c + u) / 2) := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL0]; exact one_ne_zero), hPL0, hP10, div_one]
  refine ⟨h1, h0, ?_⟩
  rw [argmaxOpt_eq_argmax_of_forall_some (g := ![(1 - c + u) / 2, (1 + (1 - q) * u) / 2])
    (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0], by simp [h1]⟩)]
  rw [argmax_fin2_eq_zero_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor <;> intro h <;> nlinarith

end D6

end Cleanroom.Corrigibility.LegitNegDynamic
