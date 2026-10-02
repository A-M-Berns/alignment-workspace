import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# B1: conditioning is invariant to thinning `P(L | a)`, and discontinuous at 0

Package `legit-neg-pricing`, target 1. Sources: `clusters/B/NEGATIVES.md` B1, `clusters/B/VERIFY.md`
"B1 — survives", `clusters/B/fixtures/fx_conditioning.py` (B1), pinned by
[[corr-legit-neg-inventory]] item 015.

`thin P t ε wv` multiplies the legitimacy of every action selected by `t` by an independent
coin of probability `ε` (states `S × Bool`, the coin's `true` branch keeping legitimacy), leaves
every other action untouched, keeps every number on the surviving branch, and lets the humans
value the new void branch at `wv` (the fixture's `0`). The general theorem is stated for any
menu vector whose numbers at the thinned action's legitimate terminals are pulled back from the
original problem's; `S1`, `S2sel` and `S3` are instances. **S2 is not invariant** (B10): it reads
`H`, which the coin changes; the scoring class here is exactly the one B1 names.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-- **Thinning** the legitimacy of the actions selected by `t` by an independent coin of
probability `ε`: states `(s, c)` with prior `π s · (ε if c else 1 − ε)`; a selected action is
legitimate at `(s, c)` iff it was at `s` and `c = true`; numbers unchanged on the surviving
branch and `wv` on the new void branch; unselected actions untouched.
Source: [[corr-legit-neg-inventory]] item 015 (B1); `fx_conditioning.py` B1 (`thin`, `thin+`)
Kind: D
Fidelity: exact (the fixture's void value `0` is `wv = 0`) -/
def thin (P : Problem S A) (t : A → Bool) (ε wv : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Problem (S × Bool) A where
  prior := fun sc => P.prior sc.1 * (if sc.2 then ε else 1 - ε)
  prior_nonneg := fun sc => mul_nonneg (P.prior_nonneg _) (by split_ifs <;> linarith)
  prior_sum := by
    rw [Fintype.sum_prod_type]
    have : ∀ s, ∑ b : Bool, P.prior s * (if b then ε else 1 - ε) = P.prior s := fun s => by
      simp [Fintype.sum_bool]; ring
    simp only [this, P.prior_sum]
  leg := fun sc a => if t a then (P.leg sc.1 a && sc.2) else P.leg sc.1 a
  u := fun sc a => if t a && !sc.2 then wv else P.u sc.1 a

section Thin

variable (P : Problem S A) (t : A → Bool) (ε wv : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)

/-- Sums over the thinned states reduce to the original states with the coin integrated out.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thin_sum (f : S × Bool → ℚ) :
    ∑ sc, (thin P t ε wv h0 h1).prior sc * f sc
      = ∑ s, P.prior s * (ε * f (s, true) + (1 - ε) * f (s, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [thin]
  ring

/-- `thin_leg`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma thin_leg (sc : S × Bool) (a : A) :
    (thin P t ε wv h0 h1).leg sc a = if t a then (P.leg sc.1 a && sc.2) else P.leg sc.1 a := rfl

/-- `thin_u`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma thin_u (sc : S × Bool) (a : A) :
    (thin P t ε wv h0 h1).u sc a = if t a && !sc.2 then wv else P.u sc.1 a := rfl

/-- `P(L | a)` of a thinned action is multiplied by `ε`.
Source: [[corr-legit-neg-inventory]] item 015 (B1)
Kind: L
Fidelity: exact -/
theorem thin_PL_of_selected (a : A) (ha : t a = true) :
    (thin P t ε wv h0 h1).PL a = ε * P.PL a := by
  unfold Problem.PL Problem.mass
  rw [thin_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false]
  ring

/-- `P(L | a)` of an unselected action is unchanged.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem thin_PL_of_unselected (a : A) (ha : t a = false) :
    (thin P t ε wv h0 h1).PL a = P.PL a := by
  unfold Problem.PL Problem.mass
  rw [thin_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false]
  ring

/-- **B1 for cdot**: a menu vector whose diagonal at the thinned action's surviving legitimate
terminals is pulled back from `V` gives `P1 (thin) V' a = ε · P1 P V a`.
Source: [[corr-legit-neg-inventory]] item 015 (B1)
Kind: P
Fidelity: exact
Hyps: (a) the pullback hypothesis is the scoring class B1 names -/
theorem thin_P1_of_selected (a : A) (ha : t a = true) (V : MenuVec S A) (V' : MenuVec (S × Bool) A)
    (hV : ∀ s, P.leg s a = true → V' (s, true) a a = V s a a) :
    (thin P t ε wv h0 h1).P1 V' a = ε * P.P1 V a := by
  unfold Problem.P1
  have : ∀ sc, (thin P t ε wv h0 h1).prior sc * ind ((thin P t ε wv h0 h1).leg sc a) * V' sc a a
      = (thin P t ε wv h0 h1).prior sc * (ind ((thin P t ε wv h0 h1).leg sc a) * V' sc a a) :=
    fun sc => by ring
  simp only [this]
  rw [thin_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : P.leg s a = true
  · simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false, hs, hV s hs]
    ring
  · simp only [Bool.not_eq_true] at hs
    simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false, hs]
    ring

/-- Unselected actions: `P1` unchanged when the diagonal is pulled back on both coin branches.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem thin_P1_of_unselected (a : A) (ha : t a = false) (V : MenuVec S A) (V' : MenuVec (S × Bool) A)
    (hV : ∀ s c, P.leg s a = true → V' (s, c) a a = V s a a) :
    (thin P t ε wv h0 h1).P1 V' a = P.P1 V a := by
  unfold Problem.P1
  have : ∀ sc, (thin P t ε wv h0 h1).prior sc * ind ((thin P t ε wv h0 h1).leg sc a) * V' sc a a
      = (thin P t ε wv h0 h1).prior sc * (ind ((thin P t ε wv h0 h1).leg sc a) * V' sc a a) :=
    fun sc => by ring
  simp only [this]
  rw [thin_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : P.leg s a = true
  · simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false, hs, hV s true hs, hV s false hs]
    ring
  · simp only [Bool.not_eq_true] at hs
    simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false, hs]
    ring

/-- **B1 (headline): conditioning is invariant to thinning.** For `ε > 0` and any menu vector
pulled back at the thinned action's surviving legitimate terminals, `P2 (thin) V' a = P2 P V a`
(the `ε` cancels; `none` on both sides when `P(L | a) = 0`). Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 015 (B1); NEGATIVES B1; VERIFY B "B1 — survives"
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε`; the pullback hypothesis is B1's scoring class -/
theorem thin_P2_of_selected (a : A) (ha : t a = true) (hε : 0 < ε) (V : MenuVec S A)
    (V' : MenuVec (S × Bool) A) (hV : ∀ s, P.leg s a = true → V' (s, true) a a = V s a a) :
    (thin P t ε wv h0 h1).P2 V' a = P.P2 V a := by
  unfold Problem.P2
  rw [thin_PL_of_selected P t ε wv h0 h1 a ha, thin_P1_of_selected P t ε wv h0 h1 a ha V V' hV]
  by_cases hPL : P.PL a = 0
  · simp [hPL]
  · rw [if_neg (mul_ne_zero hε.ne' hPL), if_neg hPL, mul_div_mul_left _ _ hε.ne']

/-- **B1, the discontinuity at 0**: at `ε = 0` the thinned action has no legitimate terminal and
`P2 = none` for every menu vector (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 015 (B1)
Kind: L
Fidelity: exact -/
theorem thin_P2_zero (a : A) (ha : t a = true) (V' : MenuVec (S × Bool) A) :
    (thin P t 0 wv le_rfl zero_le_one).P2 V' a = none := by
  apply P2_of_eq
  rw [thin_PL_of_selected P t 0 wv le_rfl zero_le_one a ha, zero_mul]

/-- **B1 under S1**: `S1` of the thinned problem is pulled back on surviving terminals, so
`P2 (thin) (S1 u') a = P2 P (S1 u) a` for `ε > 0`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 015 (B1, cell S1)
Kind: C
Fidelity: exact -/
theorem thin_P2_S1 (a : A) (ha : t a = true) (hε : 0 < ε) :
    (thin P t ε wv h0 h1).P2 (S1 (thin P t ε wv h0 h1).u) a = P.P2 (S1 P.u) a :=
  thin_P2_of_selected P t ε wv h0 h1 a ha hε (S1 P.u) _ fun s _ => by simp

/-- **B1 under S3**: the thinned problem's `S3` at a surviving terminal is the original's (the
within-state maximum is over the same numbers), so `P2` is invariant. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 015 (B1, cell S3)
Kind: C
Fidelity: exact -/
theorem thin_P2_S3 [Nonempty A] (a : A) (ha : t a = true) (hε : 0 < ε) (D : ℚ) :
    (thin P t ε wv h0 h1).P2 ((thin P t ε wv h0 h1).S3 D) a = P.P2 (P.S3 D) a :=
  thin_P2_of_selected P t ε wv h0 h1 a ha hε (P.S3 D) _ fun s _ => by
    simp [Problem.S3, Problem.umax]

/-- The thinned problem's `S2sel` at a surviving terminal of a thinned action is the original's:
conditioning on `L_a` integrates the coin out.
Source: [[corr-legit-neg-inventory]] item 015 (B1, cell S2sel)
Kind: L
Fidelity: exact -/
theorem thin_S2sel_pullback (a : A) (ha : t a = true) (hε : 0 < ε) (s : S) (c : A) :
    (thin P t ε wv h0 h1).S2sel (s, true) a c = P.S2sel s a c := by
  simp only [Problem.S2sel, Problem.Hcond]
  have hnum : ∑ sc, (thin P t ε wv h0 h1).prior sc * ind ((thin P t ε wv h0 h1).leg sc a)
        * (thin P t ε wv h0 h1).u sc c
      = ε * ∑ s, P.prior s * ind (P.leg s a) * P.u s c := by
    have : ∀ sc, (thin P t ε wv h0 h1).prior sc * ind ((thin P t ε wv h0 h1).leg sc a)
        * (thin P t ε wv h0 h1).u sc c
        = (thin P t ε wv h0 h1).prior sc * (ind ((thin P t ε wv h0 h1).leg sc a)
            * (thin P t ε wv h0 h1).u sc c) := fun sc => by ring
    simp only [this]
    rw [thin_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : P.leg s a = true
    · simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false, hs]
      ring
    · simp only [Bool.not_eq_true] at hs
      simp only [thin_leg, thin_u, ha, Bool.and_true, Bool.and_false, ind_true, ind_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, eq_self_iff_true, if_true, if_false, ite_true, ite_false, hs]
      ring
  have hden : (thin P t ε wv h0 h1).mass (fun sc => (thin P t ε wv h0 h1).leg sc a)
      = ε * P.mass (fun s => P.leg s a) :=
    thin_PL_of_selected P t ε wv h0 h1 a ha
  rw [hnum, hden, mul_div_mul_left _ _ hε.ne']

/-- **B1 under S2sel**: hence `P2 (thin) (S2sel) a = P2 P (S2sel) a` for `ε > 0`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 015 (B1, cell S2sel)
Kind: C
Fidelity: exact -/
theorem thin_P2_S2sel (a : A) (ha : t a = true) (hε : 0 < ε) :
    (thin P t ε wv h0 h1).P2 (thin P t ε wv h0 h1).S2sel a = P.P2 P.S2sel a :=
  thin_P2_of_selected P t ε wv h0 h1 a ha hε P.S2sel _ fun s _ =>
    thin_S2sel_pullback P t ε wv h0 h1 a ha hε s a

end Thin

/-! ### The fixture's instance: `keep`, `thin`, `thin+` -/

/-- The base problem of B1's fixture before thinning: states `g, b` (`1/2` each), three actions
all legitimate everywhere, `keep` and `thin` scoring `x = (3/4, 1/4)`, `thin+` scoring `x + η`.
Source: `fx_conditioning.py` B1
Kind: D
Fidelity: exact -/
def thinBase (η : ℚ) : Problem (Fin 2) (Fin 3) where
  prior := ![1/2, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp
  prior_sum := by simp [Fin.sum_univ_two]; norm_num
  leg := fun _ _ => true
  u := fun s a => ![3/4, 1/4] s + (if a = 2 then η else 0)

/-- B1's instance: `thin` and `thin+` (actions `1`, `2`) thinned by the coin `ε`, void value `0`.
Source: `fx_conditioning.py` B1
Kind: D
Fidelity: exact -/
def thinInstance (ε η : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Problem (Fin 2 × Bool) (Fin 3) :=
  thin (thinBase η) (fun a => decide (a ≠ 0)) ε 0 h0 h1

/-- `thinBase_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thinBase_PL (η : ℚ) (a : Fin 3) : (thinBase η).PL a = 1 := by
  simp [thinBase, Problem.PL, Problem.mass, Fin.sum_univ_two]; norm_num

/-- `thinBase_P1`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thinBase_P1 (η : ℚ) (a : Fin 3) :
    (thinBase η).P1 (S1 (thinBase η).u) a = 1/2 + (if a = 2 then η else 0) := by
  simp [thinBase, Problem.P1, Fin.sum_univ_two]; ring

/-- **B1's N+ witness**: for every `ε > 0` and `η > 0`, conditioning picks `thin+` alone
(`P2 = 1/2, 1/2, 1/2 + η`), while cdot keeps for `ε (1/2 + η) < 1/2` (`P1 = 1/2, ε/2, ε(1/2 + η)`);
at `ε = 0` both thinned options are `none`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 015 (B1); `fx_conditioning.py` B1 (`η = 10⁻⁶`, `ε` down to `10⁻¹²`)
Kind: N+
Fidelity: exact (the P1 clause carries the exact condition the fixture's `η = 10⁻⁶` satisfies) -/
theorem B1_witness (ε η : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (0 < ε → 0 < η →
      argmaxOpt ((thinInstance ε η h0 h1).P2 (S1 (thinInstance ε η h0 h1).u)) = {2})
    ∧ (0 < η → ε * (1/2 + η) < 1/2 →
        argmax ((thinInstance ε η h0 h1).P1 (S1 (thinInstance ε η h0 h1).u)) = {0})
    ∧ (ε = 0 → (thinInstance ε η h0 h1).P2 (S1 (thinInstance ε η h0 h1).u) 1 = none
        ∧ (thinInstance ε η h0 h1).P2 (S1 (thinInstance ε η h0 h1).u) 2 = none) := by
  have hP1 : ∀ a, (thinInstance ε η h0 h1).P1 (S1 (thinInstance ε η h0 h1).u) a
      = (if a = 0 then 1 else ε) * (1/2 + (if a = 2 then η else 0)) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [thinInstance, thin_P1_of_unselected _ _ _ _ _ _ 0 (by simp) (S1 (thinBase η).u) _
        (fun s c _ => by simp), thinBase_P1]
      simp
    · rw [thinInstance, thin_P1_of_selected _ _ _ _ _ _ a (by simp [ha]) (S1 (thinBase η).u) _
        (fun s _ => by simp), thinBase_P1]
      simp [ha]
  have hPL : ∀ a, (thinInstance ε η h0 h1).PL a = if a = 0 then 1 else ε := by
    intro a
    by_cases ha : a = 0
    · subst ha; rw [thinInstance, thin_PL_of_unselected _ _ _ _ _ _ 0 (by simp), thinBase_PL]; simp
    · rw [thinInstance, thin_PL_of_selected _ _ _ _ _ _ a (by simp [ha]), thinBase_PL]; simp [ha]
  refine ⟨fun hε hη => ?_, fun hη hlt => ?_, fun hε0 => ?_⟩
  · have hne : ∀ a, (thinInstance ε η h0 h1).PL a ≠ 0 := by
      intro a; rw [hPL]; split_ifs <;> linarith
    rw [argmaxOpt_P2_eq_argmax_div _ _ hne]
    apply argmax_eq_singleton_of_lt
    intro b hb
    simp only [hP1, hPL]
    fin_cases b <;> simp at hb ⊢ <;> field_simp <;> linarith
  · apply argmax_eq_singleton_of_lt
    intro b hb
    simp only [hP1]
    fin_cases b <;> simp at hb ⊢ <;> nlinarith [mul_nonneg h0 hη.le]
  · subst hε0
    constructor <;> apply P2_of_eq <;> rw [hPL] <;> simp

end Cleanroom.Corrigibility.LegitNegPricing
