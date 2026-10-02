import Cleanroom.Corrigibility.LegitNegPricing.Timing

/-!
# C11: S2-accurate evaluators collapse every conditional proposal to the agent's EU; S3 erases stakes

Package `legit-neg-pricing`, target 27 (`stretch`). Sources: `clusters/C/NEGATIVES.md` C11,
`clusters/C/VERIFY.md` "C11: survives" and the C5 note (P4b double-counts under S2 like P1),
`clusters/C/fixtures/c11_scorings.py`, `clusters/B/NEGATIVES.md` §3 (item 032's
identification), pinned by [[corr-legit-neg-inventory]] items 044 and 032.

(a) With `V = Wg = K = S2` every consulted number is `H c`, so `P2 = P3 = P5 = H` (as values) and
`P1 = P(L | a) · H`; `P4b` puts a premium on an EU that already counts `¬L`. Item 032's
identification — S2-accurate conditioning *is* P5 with an accurate cross-branch `K` — is a
one-line value identity here (`P5_accurateK_eq_H`); the composition around it in NEGATIVES B §3
("rescuing P2 by decision-scoring is rescuing it by cross-branch reflection") is ARGUMENT and not
claimed. (b) C11's S3 is a min–max normalisation, a different object from `legit-neg-static`'s
`S3`: `S3norm` below (junk at `max = min`). Exclusion convention for P2/P5.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### (a) S2-accurate collapse -/

/-- **C11 (a), P3 under S2**: `P3 (S2) λ (S2) a = P(L | a) H a + λ (1 − P(L | a)) H a`.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (a))
Kind: L
Fidelity: exact -/
theorem P3_S2_eq (P : Problem S A) (lam : ℚ) (a : A) :
    P.P3 P.S2 lam P.S2 a = P.PL a * P.H a + lam * (1 - P.PL a) * P.H a := by
  unfold Problem.P3 Problem.S2
  have e : ∀ s, P.prior s * (ind (P.leg s a) * P.H a + ind (!P.leg s a) * lam * P.H a)
      = (P.prior s * ind (P.leg s a)) * P.H a + lam * ((P.prior s * ind (!P.leg s a)) * P.H a) :=
    fun s => by ring
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  change P.PL a * P.H a + lam * (P.mass (fun s => !P.leg s a) * P.H a) = _
  rw [P.mass_not]; unfold Problem.PL; ring

/-- **C11 (a), P3 under S2 at `λ = 1`** is `H a` exactly.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (a))
Kind: L
Fidelity: exact -/
theorem P3_S2_one (P : Problem S A) (a : A) : P.P3 P.S2 1 P.S2 a = P.H a := by
  rw [P3_S2_eq]; ring

/-- **C11 (a), P5 under S2**: `P5 (S2) (S2) a = some (H a)` wherever defined. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (a))
Kind: L
Fidelity: exact
Hyps: (a) `P(L | a) ≠ 0` -/
theorem P5_S2_eq (P : Problem S A) (a : A) (h : P.PL a ≠ 0) :
    P.P5 P.S2 P.S2 a = some (P.H a) := by
  rw [P5_of_ne _ _ _ _ h, P1_S2_eq]
  congr 1
  have hK : P.Kbar P.S2 a = P.H a := by
    unfold Problem.Kbar Problem.S2
    change (∑ s, P.prior s * ind (P.leg s a) * P.H a) / P.PL a = P.H a
    rw [← Finset.sum_mul]
    change P.PL a * P.H a / P.PL a = P.H a
    rw [mul_div_cancel_left₀ _ h]
  rw [hK]; ring

/-- **Item 032's identification**: `P5 K (S1 u) a = some (H a)` when the legitimate humans'
cross-branch assessment at `a`'s legitimate terminals is the accurate `𝔼[u_a | ¬L_a]` and
`0 < P(L | a) < 1` — S2-accurate conditioning is P5 with an accurate cross-branch `K`. The
composition around this identity (NEGATIVES B §3) is ARGUMENT. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 032; VERIFY B "B10 — narrowed" ("the P5 identification stays ARGUMENT")
Kind: L
Fidelity: exact (the value identity only)
Hyps: (a) `0 < P(L | a) < 1`; the accuracy hypothesis on `K` -/
theorem P5_accurateK_eq_H (P : Problem S A) (K : MenuVec S A) (a : A) (hL : P.PL a ≠ 0)
    (hN : 1 - P.PL a ≠ 0)
    (hK : ∀ s, P.leg s a = true → K s a a = P.Hcond (fun t => !P.leg t a) a) :
    P.P5 K (S1 P.u) a = some (P.H a) := by
  rw [P5_of_ne _ _ _ _ hL]
  congr 1
  have hKbar : P.Kbar K a = P.Hcond (fun t => !P.leg t a) a := by
    unfold Problem.Kbar
    have : ∑ s, P.prior s * ind (P.leg s a) * K s a a
        = ∑ s, P.prior s * ind (P.leg s a) * P.Hcond (fun t => !P.leg t a) a := by
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : P.leg s a = true
      · rw [hK s hs]
      · simp [Bool.not_eq_true] at hs; simp [hs]
    rw [this, ← Finset.sum_mul]
    change P.PL a * P.Hcond (fun t => !P.leg t a) a / P.PL a = _
    rw [mul_div_cancel_left₀ _ hL]
  rw [hKbar, ← PL_mul_Hcond_self, H_eq_mix P a hL hN]

/-- **C11 (a)'s instance** (`H = (1/2, 3/5)`; `toyB (1/2) (1/5) (1/2) 1 (1/2)`): under S2,
`P2` and `P5` pick `a₁` at `3/5`, while `P1` refuses it (`1/2 > 3/10`) and so does `P4b(1/2, 1/4)`
(`3/4 > 19/40`; the C5 note: P4b double-counts `¬L` under S2 like P1). Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (a)); VERIFY C "C5" note; `c11_scorings.py` C11(a)
Kind: N+
Fidelity: exact -/
theorem C11a_instance :
    let P := toyB (1/2) (1/5) (1/2) 1 (1/2) (by norm_num) (by norm_num)
    P.H 0 = 1/2 ∧ P.H 1 = 3/5
    ∧ argmaxOpt (P.P2 P.S2) = {1}
    ∧ argmaxOpt (P.P5 P.S2 P.S2) = {1}
    ∧ argmax (P.P1 P.S2) = {0}
    ∧ argmax (P.P4b P.S2 (1/2) (1/4) P.S2) = {0} := by
  intro P
  have hH0 : P.H 0 = 1/2 := by simp only [P, toyB_H_zero]; norm_num
  have hH1 : P.H 1 = 3/5 := by simp only [P, toyB_H_one]; norm_num
  have hPL : ∀ a, P.PL a ≠ 0 :=
    Fin.forall_fin_two.2 ⟨by simp only [P]; rw [toyB_PL_zero]; norm_num,
      by simp only [P]; rw [toyB_PL_one]; norm_num⟩
  refine ⟨hH0, hH1, ?_, ?_, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some fun a => P2_S2_eq P a (hPL a), argmax_fin2_eq_one_iff,
      hH0, hH1]; norm_num
  · rw [argmaxOpt_eq_argmax_of_forall_some fun a => P5_S2_eq P a (hPL a), argmax_fin2_eq_one_iff,
      hH0, hH1]; norm_num
  · rw [argmax_fin2_eq_zero_iff, P1_S2_eq, P1_S2_eq, hH0, hH1]
    simp only [P, toyB_PL_zero, toyB_PL_one]; norm_num
  · rw [argmax_fin2_eq_zero_iff]
    simp only [Problem.P4b, Problem.S2, Fin.sum_univ_two, hH0, hH1]
    simp [P] <;> norm_num

/-! ### (b) min–max normalisation erases stakes -/

/-- The within-state minimum of the standard, `min_{c'} u s c'`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def umin (P : Problem S A) [Nonempty A] (s : S) : ℚ := univ.inf' univ_nonempty (fun c => P.u s c)

/-- **C11 (b)'s scoring**: min–max normalisation of `u` over the menu at each terminal,
`(u s c − min u s)/(max u s − min u s)` — a *different* object from `Problem.S3` (the
hindsight-regret form), disclosed as such; junk `/0` at a state where the menu ties.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (b)); `c11_scorings.py` (`rel`)
Kind: D
Fidelity: exact (C11 (b)'s normalisation; not `S3`) -/
def S3norm (P : Problem S A) [Nonempty A] : MenuVec S A :=
  fun s _ c => (P.u s c - umin P s) / (P.umax s - umin P s)

/-- `inf'_fin2`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inf'_fin2 (f : Fin 2 → ℚ) : univ.inf' univ_nonempty f = min (f 0) (f 1) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le f (mem_univ 0)) (Finset.inf'_le f (mem_univ 1))
  · exact Finset.le_inf' _ _ fun c _ => by fin_cases c <;> simp

/-- C11 (b)'s sealed problem: states `g` (`2/5`), `b` (`3/5`), both options legitimate
everywhere; `u(g, ·) = (1, 0)`, `u(b, ·) = (49/100, 1/2)`.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (b)); `c11_scorings.py`
Kind: D
Fidelity: exact -/
def c11b : Problem (Fin 2) (Fin 2) where
  prior := ![2/5, 3/5]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> norm_num
  prior_sum := by simp [Fin.sum_univ_two]; norm_num
  leg := fun _ _ => true
  u := fun s a => ![![1, 0], ![49/100, 1/2]] s a

/-- **C11 (b), S3 erases stakes**: under `S3norm` every proposal picks `y` (the option best in
the low-stakes state `b`) — `P1 = (2/5, 3/5)`, and `P2`, `P3`, `P4b`, `P5` reduce to it in a
fully legitimate problem (`proposals_of_allLeg`) — while `H` prefers `x` by `197/500`.
Source: [[corr-legit-neg-inventory]] item 044 (C11 (b)); `c11_scorings.py` ("S3 regret 197/500")
Kind: N+
Fidelity: exact -/
theorem C11b_stakes_erased :
    argmax (c11b.P1 (S3norm c11b)) = {1}
    ∧ argmax c11b.H = {0}
    ∧ c11b.H 0 - c11b.H 1 = 197/500
    ∧ (∀ a, c11b.P3 (S3norm c11b) 1 (S3norm c11b) a = c11b.P1 (S3norm c11b) a)
    ∧ (∀ a, c11b.P5 (S3norm c11b) (S3norm c11b) a = some (c11b.P1 (S3norm c11b) a)) := by
  have hnorm : ∀ s c, S3norm c11b s c c = ![![1, 0], ![0, 1]] s c := by
    intro s c; unfold S3norm umin Problem.umax
    fin_cases s <;> fin_cases c <;> simp [c11b, sup'_fin2, inf'_fin2] <;> norm_num
  refine ⟨?_, ?_, ?_, fun a => ?_, fun a => ?_⟩
  · rw [argmax_fin2_eq_one_iff]
    simp only [Problem.P1, Fin.sum_univ_two, hnorm]
    simp [c11b]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp [c11b, Problem.H, Problem.W, EU, Fin.sum_univ_two]; norm_num
  · simp [c11b, Problem.H, Problem.W, EU, Fin.sum_univ_two]; norm_num
  · exact (proposals_of_allLeg c11b a (fun _ => rfl) (S3norm c11b) (S3norm c11b) (S3norm c11b)
      1 0 0).2.1
  · exact (proposals_of_allLeg c11b a (fun _ => rfl) (S3norm c11b) (S3norm c11b) (S3norm c11b)
      0 0 0).2.2.2

end Cleanroom.Corrigibility.LegitNegPricing
