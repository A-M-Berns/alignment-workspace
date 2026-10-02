import Cleanroom.Corrigibility.LegitNegPricing.Inertness

/-!
# R2's fixed-point structure: B14 (+ 2-013, 2-030's converse), B16's closed forms, B17, B15

Package `legit-neg-pricing`, targets 12–14 and 28 (load-bearing 4 and 5). Sources:
`clusters/B/NEGATIVES.md` B14–B17, `clusters/B/VERIFY.md` (B14 narrowed by V14, B15 narrowed
to R1 by V15, B16/B17 survive), `clusters/B/fixtures/fx_readouts.py`, `verify_B.py` (V14),
pinned by [[corr-legit-neg-inventory]] items 026–029 and [[corr-legit-neg-2-inventory]] items
2-013, 2-030.

R2 with action-dependent legitimacy is a fixed-point condition; the `ratifiable` set of
`legit-neg-static` may be empty or plural, and **nothing here assumes existence**. The
workspace reading of item 2-030 is ARGUMENT; the in-scope lemma is `legit-neg-static`'s
`ratifiable_eq_argmax_of_SelectionBlind`, cited, not re-proved. Every R2-S1 statement holds with
*sighted evaluators* (`S1` prices the void terminal of an unchosen option; static finding 1).
Exclusion convention for every P2 statement.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### B14 (a), (b): what ratifiability reads -/

/-- **B14 (a)**: P1 and P2 ratify the same actions when `P(L | a*) > 0`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 026 (B14 (1)); C3
Kind: C
Fidelity: exact
Hyps: (a) `P(L | a*) ≠ 0` -/
theorem mem_ratifiable_iff_mem_ratifiableP2 (P : Problem S A) (V : MenuVec S A) (astar : A)
    (h : P.PL astar ≠ 0) : astar ∈ P.ratifiable V ↔ astar ∈ P.ratifiableP2 V := by
  simp only [Problem.ratifiable, Problem.ratifiableP2, mem_filter, mem_univ, true_and]
  rw [argmaxOpt_R2scoresP2_eq P V astar h]

/-- R2 scores from `a*` read the vector only at `a*`'s own legitimate terminals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma R2scores_congr (P : Problem S A) {V V' : MenuVec S A} (astar : A)
    (hV : ∀ s c, P.leg s astar = true → V s astar c = V' s astar c) (c : A) :
    P.R2scores V astar c = P.R2scores V' astar c := by
  unfold Problem.R2scores
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : P.leg s astar = true
  · rw [hV s c hs]
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- **B14 (b), the congruence**: whether `a*` ratifies itself depends only on the numbers at
`a*`'s own legitimate terminals — nothing on the worlds `a*` voids can matter.
Source: [[corr-legit-neg-inventory]] item 026 (B14 (2))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem mem_ratifiable_congr (P : Problem S A) {V V' : MenuVec S A} (astar : A)
    (hV : ∀ s c, P.leg s astar = true → V s astar c = V' s astar c) :
    astar ∈ P.ratifiable V ↔ astar ∈ P.ratifiable V' := by
  simp only [mem_ratifiable, R2scores_congr P astar hV]

/-- **B14 (b) on the toy** (`toyB v w ug0 1 π_b`, `ug0 ≤ 1`, `π_b < 1`): `a₁` is R2-S1-ratifiable
for every `w` (only the `g` humans score it, where it is best), and `a₀` iff it is `H`-optimal
(static's lemma instantiated). Sighted evaluators.
Source: [[corr-legit-neg-inventory]] item 026 (B14 (2), toy); `fx_readouts.py` B14
Kind: N+
Fidelity: exact -/
theorem B14_toy (v w ug0 πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1) (hu : ug0 ≤ 1) :
    1 ∈ (toyB v w ug0 1 πb h0 h1).ratifiable (S1 (toyB v w ug0 1 πb h0 h1).u)
    ∧ (0 ∈ (toyB v w ug0 1 πb h0 h1).ratifiable (S1 (toyB v w ug0 1 πb h0 h1).u)
        ↔ (toyB v w ug0 1 πb h0 h1).H 1 ≤ (toyB v w ug0 1 πb h0 h1).H 0) := by
  constructor
  · rw [mem_ratifiable]
    intro b
    rw [toyB_R2scores_S1_one, toyB_R2scores_S1_one]
    fin_cases b <;> simp <;> nlinarith
  · rw [(toyB v w ug0 1 πb h0 h1).mem_ratifiable_S1_iff_of_allLeg 0 (fun s => by fin_cases s <;> rfl),
      mem_argmax, Fin.forall_fin_two]
    simp

/-! ### B14 (c): the all-void action (V1) -/

/-- **B14 (c)**: in `withAllvoid P w` the all-void action is always P1-ratifiable (every option
scores `0` against its empty evaluation, a tie) and never P2-ratifiable (`none`; exclusion
convention).
Source: [[corr-legit-neg-inventory]] item 026 (B14 (3)); VERIFY C V1; `fx_readouts.py` B14 (`ax`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem allvoid_ratifiable (P : Problem S A) (wval : ℚ) (V : MenuVec S (Option A)) :
    none ∈ (withAllvoid P wval).ratifiable V ∧ none ∉ (withAllvoid P wval).ratifiableP2 V := by
  have hPL : (withAllvoid P wval).PL none = 0 := by
    simp [Problem.PL, Problem.mass, withAllvoid]
  have h := R2_at_void (withAllvoid P wval) V none hPL
  constructor
  · simp only [Problem.ratifiable, mem_filter, mem_univ, true_and, h.1, mem_univ]
  · simp only [Problem.ratifiableP2, mem_filter, mem_univ, true_and, h.2, Finset.notMem_empty,
      not_false_eq_true]

/-! ### B14 (d): mixed fixed points (V14) -/

/-- **`MixedRatifiable P V q`** (definition of record, this package's completion of B VERIFY
V14): a credence `q` over the menu is a mixed fixed point iff every action in its support
maximises the forecast menu `∑_{a*} q(a*) · R2scores V a* c`. The pure credence at `a`
recovers `a ∈ ratifiable V` (`mixedRatifiable_pure_iff`). No existence is claimed.
Source: [[corr-legit-neg-2-inventory]] item 2-013 (V14); `verify_B.py:108-129`
Kind: D
Fidelity: exact (V14's linear-solve construction, stated as a predicate) -/
def MixedRatifiable (P : Problem S A) (V : MenuVec S A) (q : A → ℚ) : Prop :=
  (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1
    ∧ ∀ a, 0 < q a → a ∈ argmax (fun c => ∑ astar, q astar * P.R2scores V astar c)

/-- The pure credence at `a` is mixed-ratifiable iff `a` is ratifiable.
Source: [[corr-legit-neg-2-inventory]] item 2-013
Kind: L
Fidelity: exact -/
theorem mixedRatifiable_pure_iff [DecidableEq A] (P : Problem S A) (V : MenuVec S A) (a : A) :
    MixedRatifiable P V (fun b => if b = a then 1 else 0) ↔ a ∈ P.ratifiable V := by
  have hsum : ∀ c, (∑ astar, (if astar = a then (1 : ℚ) else 0) * P.R2scores V astar c)
      = P.R2scores V a c := by
    intro c; simp [Finset.sum_ite_eq']
  unfold MixedRatifiable
  simp only [hsum, Problem.ratifiable, mem_filter, mem_univ, true_and]
  constructor
  · intro h; exact h.2.2 a (by simp)
  · intro h
    refine ⟨fun b => by split_ifs <;> norm_num, by simp, fun b hb => ?_⟩
    by_cases hba : b = a
    · subst hba; exact h
    · simp [hba] at hb

/-- **V14, scenario N** (`toyB (1/4) 0 (9/10) 1 (1/2)`): both pure actions are R2-S1 fixed points
and the credence `(2/5, 3/5)` is an interior mixed fixed point (the forecast menu ties at `1/2`).
Source: [[corr-legit-neg-2-inventory]] item 2-013 (V14); `verify_B.py` V14 ("N")
Kind: N+
Fidelity: exact -/
theorem V14_scenario_N :
    let P := toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)
    P.ratifiable (S1 P.u) = univ ∧ MixedRatifiable P (S1 P.u) ![2/5, 3/5] := by
  intro P
  constructor
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_ratifiable, mem_univ, iff_true, Fin.forall_fin_two, P, toyB_R2scores_S1_zero,
        toyB_R2scores_S1_one, toyB_H_zero, toyB_H_one] <;> norm_num
  · refine ⟨fun a => by fin_cases a <;> norm_num, by simp [Fin.sum_univ_two]; norm_num, ?_⟩
    rw [Fin.forall_fin_two]
    simp only [mem_argmax, Fin.forall_fin_two, Fin.sum_univ_two, P, toyB_R2scores_S1_zero,
      toyB_R2scores_S1_one, toyB_H_zero, toyB_H_one]
    norm_num

/-- **V14, scenario C** (`toyB (1/20) (-1) (9/10) 1 (1/2)`): both pure actions are fixed points
and `(2/21, 19/21)` is an interior mixed fixed point (`q(a₁) = 19/21`).
Source: [[corr-legit-neg-2-inventory]] item 2-013 (V14); `verify_B.py` V14 ("C")
Kind: N+
Fidelity: exact -/
theorem V14_scenario_C :
    let P := toyB (1/20) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num)
    P.ratifiable (S1 P.u) = univ ∧ MixedRatifiable P (S1 P.u) ![2/21, 19/21] := by
  intro P
  constructor
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_ratifiable, mem_univ, iff_true, Fin.forall_fin_two, P, toyB_R2scores_S1_zero,
        toyB_R2scores_S1_one, toyB_H_zero, toyB_H_one] <;> norm_num
  · refine ⟨fun a => by fin_cases a <;> norm_num, by simp [Fin.sum_univ_two]; norm_num, ?_⟩
    rw [Fin.forall_fin_two]
    simp only [mem_argmax, Fin.forall_fin_two, Fin.sum_univ_two, P, toyB_R2scores_S1_zero,
      toyB_R2scores_S1_one, toyB_H_zero, toyB_H_one]
    norm_num

/-! ### B14 (e): selection by own-diagonal value (instance only) -/

/-- Selection among the ratifiable actions by their own diagonal `P1` value (V14's `sel`).
Source: [[corr-legit-neg-2-inventory]] item 2-013 (V14)
Kind: D
Fidelity: exact -/
noncomputable def selectDiag (P : Problem S A) (V : MenuVec S A) : Finset A :=
  (P.ratifiable V).filter fun a => ∀ b ∈ P.ratifiable V, P.P1 V b ≤ P.P1 V a

/-- **V14 (e), scenario N (instance only)**: the own-diagonal selection is exactly R1-P1's
argmax, `{a₀}`, which is `H`'s choice. Not generalised (the mandate forbids it).
Source: [[corr-legit-neg-2-inventory]] item 2-013 (V14, `sel == r1`, "N")
Kind: N+
Fidelity: exact (instance) -/
theorem V14_selectDiag_N :
    let P := toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)
    selectDiag P (S1 P.u) = argmax (P.P1 (S1 P.u)) ∧ argmax (P.P1 (S1 P.u)) = {0}
      ∧ argmax P.H = {0} := by
  intro P
  have hr := V14_scenario_N.1
  refine ⟨?_, ?_, ?_⟩
  · unfold selectDiag; rw [hr]; ext a; simp [mem_argmax]
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, toyB_H_zero, toyB_H_one]; norm_num

/-- **V14 (e), scenario C**: the own-diagonal selection reproduces R1-P1's verdict `{a₁}` while
`H` keeps — R1's distortion on C, inherited by the selection. Instance only.
Source: [[corr-legit-neg-2-inventory]] item 2-013 (V14, `sel == r1`, "C")
Kind: N+
Fidelity: exact (instance) -/
theorem V14_selectDiag_C :
    let P := toyB (1/20) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num)
    selectDiag P (S1 P.u) = argmax (P.P1 (S1 P.u)) ∧ argmax (P.P1 (S1 P.u)) = {1}
      ∧ argmax P.H = {0} := by
  intro P
  have hr := V14_scenario_C.1
  refine ⟨?_, ?_, ?_⟩
  · unfold selectDiag; rw [hr]; ext a; simp [mem_argmax]
  · rw [argmax_fin2_eq_one_iff]; simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, toyB_H_zero, toyB_H_one]; norm_num

/-! ### B16: the counterfactual penalty each cell needs (load-bearing 5) -/

section B16

variable (v w δ πb p : ℚ) (h0 : 0 ≤ πb) (h1 : πb < 1)

/-- **B16 (a), cdot under R1 (hybrid S1)**: cdot picks `a₀` alone iff `p > δ − (π_b/π_g) v`
(`a₁` alone iff `<`, tie iff `=`).
Source: [[corr-legit-neg-inventory]] item 028 (B16, row P1-R1); NEGATIVES B16 proof
Kind: P
Fidelity: exact
Hyps: (a) `π_b < 1` -/
theorem B16_P1 :
    (argmax ((toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)) = {0}
        ↔ δ - πb / (1 - πb) * v < p)
    ∧ (argmax ((toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)) = {1}
        ↔ p < δ - πb / (1 - πb) * v)
    ∧ (argmax ((toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)) = univ
        ↔ p = δ - πb / (1 - πb) * v) := by
  have hg : 0 < 1 - πb := by linarith
  rw [argmax_fin2_eq_zero_iff, argmax_fin2_eq_one_iff, argmax_fin2_eq_univ_iff,
    toyB_P1_hybrid_zero, toyB_P1_hybrid_one]
  have key : ((1 - πb) * (1 - δ) + πb * v) - (1 - πb) * (1 - p)
      = (1 - πb) * (p - (δ - πb / (1 - πb) * v)) := by
    field_simp; ring
  have key2 : (1 - πb) * (1 - p) - ((1 - πb) * (1 - δ) + πb * v)
      = (1 - πb) * ((δ - πb / (1 - πb) * v) - p) := by linarith [key]
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_pos, key, mul_pos_iff_of_pos_left hg, sub_pos]
  · rw [← sub_pos, key2, mul_pos_iff_of_pos_left hg, sub_pos]
  · rw [← sub_eq_zero, key, mul_eq_zero, or_iff_right (by linarith : (1 - πb) ≠ 0), sub_eq_zero]

/-- **B16 (a), cdot's `H`-tracking penalty**: `P1 a₁ − P1 a₀ = H a₁ − H a₀` iff `p = −(π_b/π_g) w`
(a *bonus* when `w > 0`).
Source: [[corr-legit-neg-inventory]] item 028 (B16, `H`-tracking P1)
Kind: P
Fidelity: exact
Hyps: (a) `π_b < 1` -/
theorem B16_P1_tracking :
    (toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p) 1
        - (toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p) 0
      = (toyB v w (1 - δ) 1 πb h0 h1.le).H 1 - (toyB v w (1 - δ) 1 πb h0 h1.le).H 0
    ↔ p = -(πb / (1 - πb)) * w := by
  have hg : (1 - πb) ≠ 0 := by linarith
  rw [toyB_P1_hybrid_zero, toyB_P1_hybrid_one, toyB_H_zero, toyB_H_one]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **B16 (b), conditioning under R1 (hybrid S1)**: P2 picks `a₀` alone iff
`p > π_g δ + π_b (1 − v)` (`a₁` alone iff `<`, tie iff `=`). Exclusion convention (both defined).
Source: [[corr-legit-neg-inventory]] item 028 (B16, row P2-R1); `hybrid_P2_news` for the `<` half
Kind: P
Fidelity: exact
Hyps: (a) `π_b < 1` -/
theorem B16_P2 :
    (argmaxOpt ((toyB v w (1 - δ) 1 πb h0 h1.le).P2 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)) = {0}
        ↔ (1 - πb) * δ + πb * (1 - v) < p)
    ∧ (argmaxOpt ((toyB v w (1 - δ) 1 πb h0 h1.le).P2 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)) = {1}
        ↔ p < (1 - πb) * δ + πb * (1 - v))
    ∧ (argmaxOpt ((toyB v w (1 - δ) 1 πb h0 h1.le).P2 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)) = univ
        ↔ p = (1 - πb) * δ + πb * (1 - v)) := by
  have hg : 0 < 1 - πb := by linarith
  have hPL : ∀ a, (toyB v w (1 - δ) 1 πb h0 h1.le).PL a ≠ 0 :=
    Fin.forall_fin_two.2 ⟨by rw [toyB_PL_zero]; norm_num, by rw [toyB_PL_one]; linarith⟩
  rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_zero_iff, argmax_fin2_eq_one_iff,
    argmax_fin2_eq_univ_iff]
  simp only [toyB_PL_zero, toyB_PL_one, toyB_P1_hybrid_zero, toyB_P1_hybrid_one, div_one,
    mul_div_cancel_left₀ _ hg.ne']
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;>
    linarith

/-- **B16 (b), conditioning's `H`-tracking penalty**: `P2 a₁ − P2 a₀ = H a₁ − H a₀` iff
`p = π_b (1 − w)` — `a₁`'s ex-ante shortfall, the S2-accurate bet-score. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 028 (B16, `H`-tracking P2)
Kind: P
Fidelity: exact
Hyps: (a) `π_b < 1` -/
theorem B16_P2_tracking :
    (toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p) 1
          / (toyB v w (1 - δ) 1 πb h0 h1.le).PL 1
        - (toyB v w (1 - δ) 1 πb h0 h1.le).P1 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p) 0
          / (toyB v w (1 - δ) 1 πb h0 h1.le).PL 0
      = (toyB v w (1 - δ) 1 πb h0 h1.le).H 1 - (toyB v w (1 - δ) 1 πb h0 h1.le).H 0
    ↔ p = πb * (1 - w) := by
  have hg : 0 < 1 - πb := by linarith
  rw [toyB_PL_zero, toyB_PL_one, toyB_P1_hybrid_zero, toyB_P1_hybrid_one, toyB_H_zero, toyB_H_one,
    div_one, mul_div_cancel_left₀ _ hg.ne']
  constructor <;> intro h <;> linarith

/-- **B16 (c), R2**: `a₁` is ratifiable iff `p ≤ δ` (the `(g, a₁)` humans must mark down their
own realized option by at least its advantage there); `a₀` is ratifiable iff `H`-optimal, for
every `p`. Hence the ratifiable set is empty iff `p > δ` and `H` voids, and is `{a₀}` iff
`p > δ` and `H` keeps. Sighted evaluators.
Source: [[corr-legit-neg-inventory]] item 028 (B16, row R2); [[corr-legit-neg-2-inventory]] item 2-013 (iii)
Kind: P
Fidelity: exact
Hyps: (a) `π_b < 1` -/
theorem B16_R2 :
    (1 ∈ (toyB v w (1 - δ) 1 πb h0 h1.le).ratifiable (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)
        ↔ p ≤ δ)
    ∧ (0 ∈ (toyB v w (1 - δ) 1 πb h0 h1.le).ratifiable (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)
        ↔ (toyB v w (1 - δ) 1 πb h0 h1.le).H 1 ≤ (toyB v w (1 - δ) 1 πb h0 h1.le).H 0)
    ∧ ((toyB v w (1 - δ) 1 πb h0 h1.le).ratifiable (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p) = ∅
        ↔ δ < p ∧ (toyB v w (1 - δ) 1 πb h0 h1.le).H 0 < (toyB v w (1 - δ) 1 πb h0 h1.le).H 1)
    ∧ ((toyB v w (1 - δ) 1 πb h0 h1.le).ratifiable (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p) = {0}
        ↔ δ < p ∧ (toyB v w (1 - δ) 1 πb h0 h1.le).H 1 ≤ (toyB v w (1 - δ) 1 πb h0 h1.le).H 0) := by
  have hg : 0 < 1 - πb := by linarith
  have h1mem : 1 ∈ (toyB v w (1 - δ) 1 πb h0 h1.le).ratifiable (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)
      ↔ p ≤ δ := by
    rw [mem_ratifiable, Fin.forall_fin_two, toyB_R2scores_hybrid_one, toyB_R2scores_hybrid_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, le_refl, and_true]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have h0mem : 0 ∈ (toyB v w (1 - δ) 1 πb h0 h1.le).ratifiable (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p)
      ↔ (toyB v w (1 - δ) 1 πb h0 h1.le).H 1 ≤ (toyB v w (1 - δ) 1 πb h0 h1.le).H 0 := by
    rw [mem_ratifiable, Fin.forall_fin_two, toyB_R2scores_hybrid_zero, toyB_R2scores_hybrid_zero]
    simp
  refine ⟨h1mem, h0mem, ?_, ?_⟩
  · rw [Finset.eq_empty_iff_forall_notMem, Fin.forall_fin_two, h0mem, h1mem]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨not_le.1 hb, not_le.1 ha⟩
    · rintro ⟨ha, hb⟩; exact ⟨not_le.2 hb, not_le.2 ha⟩
  · constructor
    · intro h
      have hm0 : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := mem_singleton_self 0
      have hm1 : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by simp
      rw [← h, h0mem] at hm0
      rw [← h, h1mem] at hm1
      exact ⟨not_le.1 hm1, hm0⟩
    · rintro ⟨hp, hH⟩
      refine finset_fin2_ext ?_ ?_
      · rw [h0mem]; simp [hH]
      · rw [h1mem]; simp; linarith

end B16

/-- **B16's four table rows** (`π_b = 1/2`): the closed forms evaluate to the fixture's numbers
`(v, w, δ) ↦ (P1 threshold, P2 threshold, R2 threshold δ, H-tracking P1 / P2)`:
`(1/4, 0, 0) ↦ (−1/4, 3/8, 0, 0 / 1/2)`, `(1/4, 0, 1/10) ↦ (−3/20, 17/40, 1/10, 0 / 1/2)`,
`(1/20, −1, 1/10) ↦ (1/20, 21/40, 1/10, 1 / 1)`, `(1/2, 9/10, 1/10) ↦ (−2/5, 3/10, 1/10, −9/10 / 1/20)`;
and on the fourth row `H` voids, so at `p = δ + 1/400` the ratifiable set is empty.
Source: [[corr-legit-neg-inventory]] item 028 (B16, table); `fx_readouts.py` B16
Kind: N+
Fidelity: exact -/
theorem B16_rows :
    ((0 : ℚ) - (1/2) / (1 - 1/2) * (1/4) = -1/4 ∧ (1 - 1/2 : ℚ) * 0 + 1/2 * (1 - 1/4) = 3/8
      ∧ -((1/2 : ℚ) / (1 - 1/2)) * 0 = 0 ∧ (1/2 : ℚ) * (1 - 0) = 1/2)
    ∧ ((1/10 : ℚ) - (1/2) / (1 - 1/2) * (1/4) = -3/20 ∧ (1 - 1/2 : ℚ) * (1/10) + 1/2 * (1 - 1/4) = 17/40)
    ∧ ((1/10 : ℚ) - (1/2) / (1 - 1/2) * (1/20) = 1/20 ∧ (1 - 1/2 : ℚ) * (1/10) + 1/2 * (1 - 1/20) = 21/40
      ∧ -((1/2 : ℚ) / (1 - 1/2)) * (-1) = 1 ∧ (1/2 : ℚ) * (1 - (-1)) = 1)
    ∧ ((1/10 : ℚ) - (1/2) / (1 - 1/2) * (1/2) = -2/5 ∧ (1 - 1/2 : ℚ) * (1/10) + 1/2 * (1 - 1/2) = 3/10
      ∧ -((1/2 : ℚ) / (1 - 1/2)) * (9/10) = -9/10 ∧ (1/2 : ℚ) * (1 - 9/10) = 1/20)
    ∧ (toyB (1/2) (9/10) (1 - 1/10) 1 (1/2) (by norm_num) (by norm_num)).ratifiable
        (hybridV (toyB (1/2) (9/10) (1 - 1/10) 1 (1/2) (by norm_num) (by norm_num)) (1/10 + 1/400)) = ∅ := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [(B16_R2 (1/2) (9/10) (1/10) (1/2) (1/10 + 1/400) (by norm_num) (by norm_num)).2.2.1,
    toyB_H_zero, toyB_H_one]
  norm_num

/-! ### B17: R2 under S2 and S2sel; R2-ref -/

/-- **B17, R2-S2 scores**: from any realized `a*`, `R2scores (S2) a* c = P(L | a*) · H c`.
Source: [[corr-legit-neg-inventory]] item 029 (B17)
Kind: L
Fidelity: exact -/
theorem R2scores_S2 (P : Problem S A) (astar c : A) :
    P.R2scores P.S2 astar c = P.PL astar * P.H c := by
  unfold Problem.R2scores Problem.S2 Problem.PL Problem.mass
  rw [Finset.sum_mul]

/-- `a ∈ ratifiableP2 V ↔ a ∈ ratifiable V ∧ P(L | a) ≠ 0` (C3's corollary, unpacked).
Exclusion convention.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_ratifiableP2_iff (P : Problem S A) (V : MenuVec S A) (a : A) :
    a ∈ P.ratifiableP2 V ↔ a ∈ P.ratifiable V ∧ P.PL a ≠ 0 := by
  by_cases h : P.PL a = 0
  · simp only [h, ne_eq, not_true_eq_false, and_false, iff_false]
    simp only [Problem.ratifiableP2, mem_filter, mem_univ, true_and, (R2_at_void P V a h).2]
    exact Finset.notMem_empty a
  · rw [mem_ratifiable_iff_mem_ratifiableP2 P V a h]; simp [h]

/-- **B17, R2-S2 ratifiability**: `a*` is P1-ratifiable under S2 iff `P(L | a*) = 0` or `a*` is
`H`-optimal; as sets, `ratifiable (S2) = argmax H ∪ {P(L | ·) = 0}` and
`ratifiableP2 (S2) = argmax H ∩ {P(L | ·) ≠ 0}` (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 029 (B17, R2-S2); `fx_readouts.py` B17 ("R2-S2 general")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ratifiable_S2 [DecidableEq A] (P : Problem S A) :
    (∀ astar, astar ∈ P.ratifiable P.S2 ↔ P.PL astar = 0 ∨ astar ∈ argmax P.H)
    ∧ P.ratifiable P.S2 = argmax P.H ∪ univ.filter (fun a => P.PL a = 0)
    ∧ P.ratifiableP2 P.S2 = (argmax P.H).filter (fun a => P.PL a ≠ 0) := by
  have hmem : ∀ astar, astar ∈ P.ratifiable P.S2 ↔ P.PL astar = 0 ∨ astar ∈ argmax P.H := by
    intro astar
    rw [mem_ratifiable, mem_argmax]
    simp only [R2scores_S2]
    by_cases h : P.PL astar = 0
    · simp [h]
    · have hpos : 0 < P.PL astar := lt_of_le_of_ne (P.mass_nonneg _) (Ne.symm h)
      simp only [h, false_or]
      constructor
      · intro hb b; exact le_of_mul_le_mul_left (hb b) hpos
      · intro hb b; exact mul_le_mul_of_nonneg_left (hb b) hpos.le
  refine ⟨hmem, ?_, ?_⟩
  · ext a; rw [hmem]; simp [or_comm]
  · ext a
    rw [mem_ratifiableP2_iff, hmem, mem_filter]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩

/-- **B17, R2-S2sel scores**: `R2scores (S2sel) a* c = P(L | a*) · 𝔼[u_c | L_{a*}]`.
Source: [[corr-legit-neg-inventory]] item 029 (B17)
Kind: L
Fidelity: exact -/
theorem R2scores_S2sel (P : Problem S A) (astar c : A) :
    P.R2scores P.S2sel astar c = P.PL astar * P.Hcond (fun t => P.leg t astar) c := by
  unfold Problem.R2scores Problem.S2sel Problem.PL Problem.mass
  rw [Finset.sum_mul]

/-- **B17, R2-S2sel on the toy**: `a₁` self-ratifies for every `w` (B11 returns: the `g` humans'
conditional bet is `u(g, ·)`, where `a₁` is best).
Source: [[corr-legit-neg-inventory]] item 029 (B17, R2-S2sel); `fx_readouts.py` B17
Kind: N+
Fidelity: exact -/
theorem B17_S2sel_toy (w : ℚ) :
    1 ∈ (toyB (1/4) w (9/10) 1 (1/2) (by norm_num) (by norm_num)).ratifiable
      (toyB (1/4) w (9/10) 1 (1/2) (by norm_num) (by norm_num)).S2sel := by
  rw [mem_ratifiable, Fin.forall_fin_two]
  simp only [R2scores_S2sel, toyB_PL_one]
  have hc : ∀ c, (toyB (1/4) w (9/10) 1 (1/2) (by norm_num) (by norm_num)).Hcond
      (fun t => (toyB (1/4) w (9/10) 1 (1/2) (by norm_num) (by norm_num)).leg t 1) c
      = ![9/10, 1] c := by
    intro c; unfold Problem.Hcond Problem.mass
    fin_cases c <;> simp [Fin.sum_univ_two] <;> norm_num
  rw [hc, hc]; norm_num

/-- **B17, R2-ref (ii) and (iii)** on `toyB (1/4) (-1) (9/10) 1 (1/2)`: (ii) the blind reference
readout from `a₀` with `y = 1/2` ranks `a₁` first (`3/4 > 23/40`) while `H` keeps; (iii) the
reference `a₁`, which voids `b`, lets `a₁` win on `g` alone (`9/20 < 1/2`). (R2-ref from a
fully legitimate reference with sighted evaluators is `H`: static's `R2ref_S1_eq_H_of_allLeg`.)
Source: [[corr-legit-neg-inventory]] item 029 (B17 (ii), (iii)); `fx_readouts.py` B17
Kind: N+
Fidelity: exact -/
theorem B17_R2ref :
    let P := toyB (1/4) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num)
    argmax (P.R2ref (P.blindImpute (1/2)) 0) = {1} ∧ argmax P.H = {0}
    ∧ argmax (P.R2ref (S1 P.u) 1) = {1} := by
  intro P
  have hb : ∀ c, P.R2ref (P.blindImpute (1/2)) 0 c = ![23/40, 3/4] c := by
    intro c; unfold Problem.R2ref Problem.R2scores
    fin_cases c <;> simp [P, Problem.blindImpute, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff, hb, hb]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, toyB_H_zero, toyB_H_one]; norm_num
  · rw [argmax_fin2_eq_one_iff]
    unfold Problem.R2ref
    simp only [P, toyB_R2scores_S1_one]; norm_num

/-! ### B15: the mismatch term (R1 only, per V15) -/

/-- The mismatch mass `M = π(c_raw ∧ ¬c_corr)` of the R1 per-option activations.
Source: [[corr-legit-neg-inventory]] item 027 (B15)
Kind: D
Fidelity: exact (R1 reading; V15) -/
def mismatchMass (P : Problem S A) (raw corr : A) : ℚ :=
  P.mass fun s => P.leg s raw && !P.leg s corr

/-- **B15 on the toy** (`v = 1/4, u(g,a₀) = 9/10, w = 0`; `raw = a₁`, `corr = a₀`): `M = 0`,
`M' = π_b = 1/2`; cdot's premium `P1 a₁ − P1 a₀ = 1/20 − M' · u(b, a₀) = −3/40`; conditioning's
is `+17/40`, unbounded by `M`. No R2 claim (V15: the fixture's R2 check was a tautology).
Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 027 (B15); `fx_readouts.py` B15
Kind: N+
Fidelity: exact (R1 only) -/
theorem B15_toy :
    let P := toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)
    mismatchMass P 1 0 = 0 ∧ mismatchMass P 0 1 = 1/2
    ∧ P.P1 (S1 P.u) 1 - P.P1 (S1 P.u) 0 = 1/20 - mismatchMass P 0 1 * P.u 1 0
    ∧ P.P1 (S1 P.u) 1 - P.P1 (S1 P.u) 0 = -3/40
    ∧ P.P1 (S1 P.u) 1 / P.PL 1 - P.P1 (S1 P.u) 0 / P.PL 0 = 17/40 := by
  intro P
  have hM : mismatchMass P 1 0 = 0 := by
    simp [mismatchMass, Problem.mass, P, Fin.sum_univ_two]
  have hM' : mismatchMass P 0 1 = 1/2 := by
    simp [mismatchMass, Problem.mass, P, Fin.sum_univ_two]
  refine ⟨hM, hM', ?_, ?_, ?_⟩
  · rw [hM']; simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one, toyB_u]; norm_num
  · simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one, toyB_PL_zero, toyB_PL_one]; norm_num

end Cleanroom.Corrigibility.LegitNegPricing
