import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# C3: α-cancellation — under R2 the floor, the lexical tier and the gap are inert

Package `legit-neg-pricing`, target 18 (load-bearing 3). Sources: `clusters/C/NEGATIVES.md` C3,
`clusters/C/VERIFY.md` "C3: narrowed" (V1: the `P1 ≡ P2` half needs `P(L | a*) > 0`),
`clusters/C/fixtures/c03_r2_inertness.py`, pinned by [[corr-legit-neg-inventory]] item 036.

The theorem is for **arbitrary legitimacy** `leg` at a fixed realized action `a*`: the realized
legitimacy `ℓ(·, a*)` is common to every option scored, so any term of the form
`∑ π(s) α(ℓ(s, a*))` cancels from every comparison. The R3 case is `legit-neg-static`'s
`SelectionBlind` lemmas (`ratifiable_eq_argmax_of_SelectionBlind`), cited, not re-proved.
Exclusion convention throughout for the P2 forms.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-- **C3, P1 ≡ P2 under R2** at a realized action with `P(L | a*) > 0`: the P2 menu scores are
the P1 scores divided by the common `P(L | a*)`, so the argmaxes agree. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 036 (C3); VERIFY C "C3: narrowed" (V1)
Kind: P
Fidelity: exact
Hyps: (a) `P(L | a*) ≠ 0` (V1's narrowing) -/
theorem argmaxOpt_R2scoresP2_eq (P : Problem S A) (V : MenuVec S A) (astar : A)
    (h : P.PL astar ≠ 0) :
    argmaxOpt (P.R2scoresP2 V astar) = argmax (P.R2scores V astar) := by
  rw [argmaxOpt_eq_argmax_of_forall_some (g := fun c => P.R2scores V astar c / P.PL astar)
    (fun c => by simp [Problem.R2scoresP2, h])]
  exact argmax_div_pos _ (lt_of_le_of_ne (P.mass_nonneg _) (Ne.symm h))

/-- **C3 at `P(L | a*) = 0` (V1)**: every R2-P1 menu score is `0`, so the whole menu is
P1-ratifying (a vacuous fixed point), while under P2 nothing is defined and the argmax is empty.
Exclusion convention.
Source: VERIFY C "C3: narrowed" (V1); [[corr-legit-neg-inventory]] item 036
Kind: P
Fidelity: exact -/
theorem R2_at_void (P : Problem S A) (V : MenuVec S A) (astar : A) (h : P.PL astar = 0) :
    argmax (P.R2scores V astar) = univ ∧ argmaxOpt (P.R2scoresP2 V astar) = ∅ := by
  constructor
  · have hz : ∀ c, P.R2scores V astar c = 0 := by
      intro c
      unfold Problem.R2scores
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases hs : P.leg s astar = true
      · rw [P.prior_eq_zero_of_mass_eq_zero h s hs]; ring
      · simp [Bool.not_eq_true] at hs; simp [hs]
    rw [argmax_congr hz]; exact argmax_const 0
  · exact argmaxOpt_none _ fun c => by simp [Problem.R2scoresP2, h]

/-- The void part of the R2 vector: `∑ s, π s · [¬leg s a*] · W s a* c`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def R2void (P : Problem S A) (Wg : MenuVec S A) (astar c : A) : ℚ :=
  ∑ s, P.prior s * ind (!P.leg s astar) * Wg s astar c

/-- `R2scoresP4b = κ · P(L | a*) + (1 − κ) · R2scoresP3 (κ'/(1 − κ))` for `κ ≠ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma R2scoresP4b_eq (P : Problem S A) (Wg : MenuVec S A) (κ κ' : ℚ) (hκ : κ ≠ 1)
    (V : MenuVec S A) (astar c : A) :
    P.R2scoresP4b Wg κ κ' V astar c
      = P.R2scoresP3 Wg (κ' / (1 - κ)) V astar c * (1 - κ) + κ * P.PL astar := by
  unfold Problem.R2scoresP4b Problem.R2scoresP3
  have : (1 - κ) ≠ 0 := sub_ne_zero.2 (Ne.symm hκ)
  field_simp
  ring

/-- **C3, P4b ≡ P3 under R2**: for `κ < 1` the cardinal gap's R2 argmax is the graded rule's at
void weight `λ = κ'/(1 − κ)`, whatever `κ` — the gap is inert.
Source: [[corr-legit-neg-inventory]] item 036 (C3)
Kind: P
Fidelity: exact
Hyps: (a) `κ < 1` (`κ = 1` makes `κ'/(1 − κ)` junk) -/
theorem argmax_R2scoresP4b_eq_P3 (P : Problem S A) (Wg : MenuVec S A) (κ κ' : ℚ) (hκ : κ < 1)
    (V : MenuVec S A) (astar : A) :
    argmax (P.R2scoresP4b Wg κ κ' V astar) = argmax (P.R2scoresP3 Wg (κ' / (1 - κ)) V astar) := by
  rw [argmax_congr (fun c => R2scoresP4b_eq P Wg κ κ' hκ.ne V astar c), argmax_add_const,
    argmax_mul_pos _ (by linarith)]

/-- **C3, P4b(κ, 0) ≡ P1 under R2**: with no void weight the gap's R2 argmax is cdot's.
Source: [[corr-legit-neg-inventory]] item 036 (C3)
Kind: C
Fidelity: exact
Hyps: (a) `κ < 1` -/
theorem argmax_R2scoresP4b_zero_eq_P1 (P : Problem S A) (Wg : MenuVec S A) (κ : ℚ) (hκ : κ < 1)
    (V : MenuVec S A) (astar : A) :
    argmax (P.R2scoresP4b Wg κ 0 V astar) = argmax (P.R2scores V astar) := by
  rw [argmax_R2scoresP4b_eq_P3 P Wg κ 0 hκ, zero_div]
  refine argmax_congr fun c => ?_
  unfold Problem.R2scoresP3; ring

/-- **P4a's R2 form** (this package's definition, disclosed): the pair `(P(L | a*), R2scoresP3 (λ = 1))`
compared lexicographically, the first coordinate menu-common (C `model.py:114-115`'s reading of
the lexical rule at a realized terminal).
Source: [[corr-legit-neg-inventory]] item 036 (C3); mandate target 18
Kind: D
Fidelity: exact -/
def R2scoresP4a (P : Problem S A) (Wg V : MenuVec S A) (astar c : A) : ℚ ×ₗ ℚ :=
  toLex (P.PL astar, P.R2scoresP3 Wg 1 V astar c)

/-- **C3, P4a ≡ P3 under R2**: the tier is menu-common, so the lexicographic argmax is
`argmax (R2scoresP3 (λ = 1))`.
Source: [[corr-legit-neg-inventory]] item 036 (C3)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem argmaxLex_R2scoresP4a_eq (P : Problem S A) (Wg V : MenuVec S A) (astar : A) :
    argmaxLex (R2scoresP4a P Wg V astar) = argmax (P.R2scoresP3 Wg 1 V astar) := by
  ext a
  simp only [mem_argmaxLex, mem_argmax, R2scoresP4a, Prod.Lex.toLex_le_toLex, lt_self_iff_false,
    true_and, false_or]

/-- **C3's corollary for ratifiability**: `ratifiable V = ratifiableP2 V ∪ {a | P(L | a) = 0}` —
P1 and P2 ratify the same actions except that P1 also ratifies every all-void action (V1).
Exclusion convention.
Source: [[corr-legit-neg-inventory]] items 026 (B14 (1), (3)), 036; VERIFY C V1
Kind: C
Fidelity: exact -/
theorem ratifiable_eq_ratifiableP2_union [DecidableEq A] (P : Problem S A) (V : MenuVec S A) :
    P.ratifiable V = P.ratifiableP2 V ∪ univ.filter (fun a => P.PL a = 0) := by
  ext a
  simp only [Problem.ratifiable, Problem.ratifiableP2, mem_union, mem_filter, mem_univ, true_and]
  by_cases h : P.PL a = 0
  · rw [(R2_at_void P V a h).1]; simp [h]
  · rw [argmaxOpt_R2scoresP2_eq P V a h]; simp [h]

/-- **C3's N−**: under R1 with action-dependent legitimacy the identities fail: on C's toy with
`v = 1/10, p = 0, x = 1/2`, `argmax P1 ≠ argmaxOpt P2` and `argmax P3 ≠ argmaxLex P4a`.
Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 036 (C3, N−); NEGATIVES C1 worked point
Kind: N-
Fidelity: exact -/
theorem C3_R1_not_inert :
    let P := toyC (1/10) 0 (1/2)
    argmax (P.P1 (S1 P.u)) = {0} ∧ argmaxOpt (P.P2 (S1 P.u)) = {1}
    ∧ argmax (P.P3 (toyC_W (1/2)) 1 (S1 P.u)) = {1}
    ∧ argmaxLex (P.P4a (toyC_W (1/2)) (S1 P.u)) = {0} := by
  intro P
  have hPL : ∀ a, P.PL a = ![1, 1/2] a := by
    intro a; fin_cases a <;> simp [P, toyC, Problem.PL, Problem.mass, Fin.sum_univ_two] <;> norm_num
  have hP3 : ∀ a, P.P3 (toyC_W (1/2)) 1 (S1 P.u) a = ![11/20, 3/4] a := by
    intro a; fin_cases a <;> simp [P, toyC, toyC_W, Problem.P3, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, toyC, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · rw [argmaxOpt_P2_eq_argmax_div _ _ (fun a => by rw [hPL]; fin_cases a <;> simp),
      argmax_fin2_eq_one_iff]
    simp only [P, toyC, toyB_PL_zero, toyB_PL_one, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · rw [argmax_fin2_eq_one_iff, hP3, hP3]; norm_num
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two, Problem.P4a,
        Prod.Lex.toLex_le_toLex, hPL, hP3] <;> norm_num

end Cleanroom.Corrigibility.LegitNegPricing
