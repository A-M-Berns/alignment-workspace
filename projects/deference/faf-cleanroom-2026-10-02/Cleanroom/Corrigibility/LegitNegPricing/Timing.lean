import Cleanroom.Corrigibility.LegitNegPricing.Scoring

/-!
# Timing: B18/B19/B20 (T2 voiding, the despair gamble, the T2 policy) and C9 (late decisions)

Package `legit-neg-pricing`, targets 15 and 25. Sources: `clusters/B/NEGATIVES.md` B18–B20,
`clusters/B/VERIFY.md` (B18/B20 survive, B19 narrowed by V19), `clusters/B/fixtures/fx_timing.py`,
`verify_B.py` (V19), `clusters/C/NEGATIVES.md` C9, `clusters/C/VERIFY.md` "C9" (V5),
`clusters/C/fixtures/c09_late_decision.py`, pinned by [[corr-legit-neg-inventory]] items 030, 042
and [[corr-legit-neg-2-inventory]] item 2-014 (V19).

T2 is `Problem.restrict {s} _` (the prior renormalised to one state). `gambleProblem` keeps a
mass-`0` coin state at `ε = 0`; `Hcond`'s junk there is exactly why `P2 = none` (exclusion
convention). B19's S3 rescue is a distortion relative to `H` at the floor (V19).
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### The T2 point mass -/

section Singleton

variable [DecidableEq S] (P : Problem S A) (s : S)

/-- `restrict_singleton_mass_pos`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_singleton_mass_pos (hs : 0 < P.prior s) : 0 < ∑ t ∈ ({s} : Finset S), P.prior t := by
  simpa using hs

/-- Sums under the point mass at `s` evaluate at `s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_singleton_sum (hs : 0 < P.prior s) (f : S → ℚ) :
    ∑ t, (P.restrict {s} (restrict_singleton_mass_pos P s hs)).prior t * f t = f s := by
  simp only [restrict_prior, P.cellprior_singleton s hs]
  simp [Finset.sum_ite_eq']

/-- At T2 in state `s`, `P1 V a = [leg s a] · V s a a`.
Source: [[corr-legit-neg-inventory]] item 030 (B18)
Kind: L
Fidelity: exact -/
theorem restrict_singleton_P1 (hs : 0 < P.prior s) (V : MenuVec S A) (a : A) :
    (P.restrict {s} (restrict_singleton_mass_pos P s hs)).P1 V a = ind (P.leg s a) * V s a a := by
  unfold Problem.P1
  have : ∀ t, (P.restrict {s} (restrict_singleton_mass_pos P s hs)).prior t
      * ind ((P.restrict {s} (restrict_singleton_mass_pos P s hs)).leg t a) * V t a a
      = (P.restrict {s} (restrict_singleton_mass_pos P s hs)).prior t
        * (ind (P.leg t a) * V t a a) := fun t => by rw [restrict_leg]; ring
  simp only [this]
  exact restrict_singleton_sum P s hs _

/-- At T2 in state `s`, `P(L | a) = [leg s a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_singleton_PL (hs : 0 < P.prior s) (a : A) :
    (P.restrict {s} (restrict_singleton_mass_pos P s hs)).PL a = ind (P.leg s a) := by
  unfold Problem.PL Problem.mass
  simp only [restrict_leg]
  exact restrict_singleton_sum P s hs _

/-- At T2 in state `s`, `H a = u s a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_singleton_H (hs : 0 < P.prior s) (a : A) :
    (P.restrict {s} (restrict_singleton_mass_pos P s hs)).H a = P.u s a := by
  unfold Problem.H Problem.W EU
  simp only [restrict_u]
  exact restrict_singleton_sum P s hs _

/-- At T2 in state `s`, `P3 Wg λ V a = [leg s a] · V s a a + [¬leg s a] · λ · Wg s a a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_singleton_P3 (hs : 0 < P.prior s) (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A) (a : A) :
    (P.restrict {s} (restrict_singleton_mass_pos P s hs)).P3 Wg lam V a
      = ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam * Wg s a a := by
  unfold Problem.P3
  simp only [restrict_leg]
  exact restrict_singleton_sum P s hs _

/-- At T2 in state `s`, `P4b Wg κ κ' V a = [leg] (κ + (1 − κ) V s a a) + [¬leg] κ' Wg s a a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_singleton_P4b (hs : 0 < P.prior s) (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A) (a : A) :
    (P.restrict {s} (restrict_singleton_mass_pos P s hs)).P4b Wg κ κ' V a
      = ind (P.leg s a) * (κ + (1 - κ) * V s a a) + ind (!P.leg s a) * κ' * Wg s a a := by
  unfold Problem.P4b
  simp only [restrict_leg]
  exact restrict_singleton_sum P s hs _

end Singleton

/-! ### B18: deterministic voiding at T2 -/

section B18

variable (v w ug0 ug1 πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1) (hb : 0 < πb)

/-- `toyB_b_mass_pos`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyB_b_mass_pos (hb : 0 < πb) : 0 < (toyB v w ug0 ug1 πb h0 h1).prior 1 := by simpa using hb

/-- **B18**: in the known state `b`, `P1 a₀ = v`, `P1 a₁ = 0` (cdot keeps iff `v > 0`, ties at
`v = 0`); `P2 a₁ = none` (exclusion convention) and `P2 a₀ = some v`; under the 1-at-null
variant `P2li a₁ = 1` beats `a₀` whenever `v < 1` — the convention decides the T2 verdict.
Source: [[corr-legit-neg-inventory]] item 030 (B18); `fx_timing.py` B18
Kind: P
Fidelity: exact (`_li` clause: variant, 1-at-null)
Hyps: (a) `0 < π_b` (so the cell has mass) -/
theorem B18 :
    let P := toyB v w ug0 ug1 πb h0 h1
    let Pb := P.restrict {1} (restrict_singleton_mass_pos P 1 (toyB_b_mass_pos v w ug0 ug1 πb h0 h1 hb))
    Pb.P1 (S1 P.u) 0 = v
    ∧ Pb.P1 (S1 P.u) 1 = 0
    ∧ (argmax (Pb.P1 (S1 P.u)) = {0} ↔ 0 < v)
    ∧ (argmax (Pb.P1 (S1 P.u)) = univ ↔ v = 0)
    ∧ Pb.P2 (S1 P.u) 1 = none
    ∧ Pb.P2 (S1 P.u) 0 = some v
    ∧ Pb.P2li (S1 P.u) 1 = 1
    ∧ (argmax (Pb.P2li (S1 P.u)) = {1} ↔ v < 1) := by
  intro P Pb
  have hP1 : ∀ a, Pb.P1 (S1 P.u) a = ![v, 0] a := by
    intro a; simp only [Pb]
    rw [restrict_singleton_P1 P 1 (toyB_b_mass_pos v w ug0 ug1 πb h0 h1 hb)]
    fin_cases a <;> simp [P]
  have hPL : ∀ a, Pb.PL a = ![1, 0] a := by
    intro a; simp only [Pb]
    rw [restrict_singleton_PL P 1 (toyB_b_mass_pos v w ug0 ug1 πb h0 h1 hb)]
    fin_cases a <;> simp [P]
  refine ⟨by rw [hP1]; rfl, by rw [hP1]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff, hP1, hP1]; simp
  · rw [argmax_fin2_eq_univ_iff, hP1, hP1]; simp [eq_comm]
  · apply P2_of_eq; rw [hPL]; rfl
  · rw [P2_of_ne _ _ _ (by rw [hPL]; simp), hP1, hPL]; simp
  · unfold Problem.P2li; rw [hPL]; simp
  · unfold Problem.P2li
    rw [argmax_fin2_eq_one_iff]
    simp only [hPL, hP1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    simp

end B18

/-! ### B19: the despair gamble -/

section B19

variable (v ε w : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)

/-- `gamble_P1`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gamble_P1 (a : Fin 2) :
    (gambleProblem v 1 ε w h0 h1).P1 (S1 (gambleProblem v 1 ε w h0 h1).u) a = ![v, ε] a := by
  fin_cases a <;> simp [gambleProblem, Problem.P1, Fin.sum_univ_two] <;> ring

/-- `gamble_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gamble_PL (a : Fin 2) : (gambleProblem v 1 ε w h0 h1).PL a = ![1, ε] a := by
  fin_cases a <;> simp [gambleProblem, Problem.PL, Problem.mass, Fin.sum_univ_two]

/-- `gamble_H`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gamble_H (a : Fin 2) :
    (gambleProblem v 1 ε w h0 h1).H a = ![v, ε + (1 - ε) * w] a := by
  fin_cases a <;> simp [gambleProblem, Problem.H, Problem.W, EU, Fin.sum_univ_two] <;> ring

/-- **B19, cdot and conditioning on the despair gamble**: cdot gambles iff `ε > v`; for `ε > 0`
conditioning scores the gamble `1` and takes it iff `v < 1`, and at `ε = 0` the gamble is
`none` (B1's discontinuity at T2). At the floor (`w = 0`) cdot's choice is `H`'s. Exclusion
convention.
Source: [[corr-legit-neg-inventory]] item 030 (B19); VERIFY B "B19 — narrowed"
Kind: P
Fidelity: exact
Hyps: (a) none beyond the coin's range -/
theorem B19 :
    (argmax ((gambleProblem v 1 ε w h0 h1).P1 (S1 (gambleProblem v 1 ε w h0 h1).u)) = {1} ↔ v < ε)
    ∧ (0 < ε → (gambleProblem v 1 ε w h0 h1).P2 (S1 (gambleProblem v 1 ε w h0 h1).u) 1 = some 1)
    ∧ (0 < ε → (argmaxOpt ((gambleProblem v 1 ε w h0 h1).P2 (S1 (gambleProblem v 1 ε w h0 h1).u)) = {1}
        ↔ v < 1))
    ∧ (ε = 0 → (gambleProblem v 1 ε w h0 h1).P2 (S1 (gambleProblem v 1 ε w h0 h1).u) 1 = none)
    ∧ (w = 0 → argmax ((gambleProblem v 1 ε w h0 h1).P1 (S1 (gambleProblem v 1 ε w h0 h1).u))
        = argmax (gambleProblem v 1 ε w h0 h1).H) := by
  refine ⟨?_, fun hε => ?_, fun hε => ?_, fun hε => ?_, fun hw => ?_⟩
  · rw [argmax_fin2_eq_one_iff, gamble_P1, gamble_P1]; simp
  · rw [P2_of_ne _ _ _ (by rw [gamble_PL]; simpa using hε.ne'), gamble_P1, gamble_PL]
    simp [div_self hε.ne']
  · rw [argmaxOpt_P2_eq_argmax_div _ _
        (fun a => by rw [gamble_PL]; fin_cases a <;> simp <;> exact hε.ne'), argmax_fin2_eq_one_iff]
    simp only [gamble_P1, gamble_PL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      div_one, div_self hε.ne']
  · apply P2_of_eq; rw [gamble_PL]; simp [hε]
  · subst hw
    refine argmax_congr fun a => ?_
    rw [gamble_P1, gamble_H]; fin_cases a <;> simp

/-- **B19 below the floor, and the S3 rescue** (`v = 1/100, ε = 1/20, w = −1`): cdot gambles while
`H` keeps; under `S3 1` cdot keeps (`1901/2000 > 1/20`).
Source: [[corr-legit-neg-inventory]] item 030 (B19); `fx_timing.py` B19 (S3)
Kind: N+
Fidelity: exact -/
theorem B19_below_floor :
    let P := gambleProblem (1/100) 1 (1/20) (-1) (by norm_num) (by norm_num)
    argmax (P.P1 (S1 P.u)) = {1} ∧ argmax P.H = {0} ∧ argmax (P.P1 (P.S3 1)) = {0} := by
  intro P
  have hS3 : ∀ s, P.S3 1 s 0 0 = ![1/100, 1] s := by
    intro s; unfold Problem.S3 Problem.umax
    fin_cases s <;> simp [P, gambleProblem, sup'_fin2] <;> norm_num
  have hS3' : P.S3 1 0 1 1 = 1 := by
    unfold Problem.S3 Problem.umax; simp [P, gambleProblem, sup'_fin2] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff]; simp only [P, gamble_P1]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp only [P, gamble_H]; norm_num
  · rw [argmax_fin2_eq_zero_iff]
    simp only [Problem.P1, Fin.sum_univ_two, hS3, hS3']
    simp [P, gambleProblem] <;> norm_num

/-- **V19, the S3 rescue over-protects at the floor** (`v = 1/100, ε = 1/2, w = 0`): `H` and
cdot-S1 gamble while cdot-S3 keeps (a distortion relative to `H`).
Source: [[corr-legit-neg-2-inventory]] item 2-014 (V19); VERIFY B "B19 — narrowed"
Kind: N+
Fidelity: exact -/
theorem V19_S3_overprotects :
    let P := gambleProblem (1/100) 1 (1/2) 0 (by norm_num) (by norm_num)
    argmax P.H = {1} ∧ argmax (P.P1 (S1 P.u)) = {1} ∧ argmax (P.P1 (P.S3 1)) = {0} := by
  intro P
  have hS3 : ∀ s, P.S3 1 s 0 0 = ![1/100, 1] s := by
    intro s; unfold Problem.S3 Problem.umax
    fin_cases s <;> simp [P, gambleProblem, sup'_fin2] <;> norm_num
  have hS3' : P.S3 1 0 1 1 = 1 := by
    unfold Problem.S3 Problem.umax; simp [P, gambleProblem, sup'_fin2] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff]; simp only [P, gamble_H]; norm_num
  · rw [argmax_fin2_eq_one_iff]; simp only [P, gamble_P1]; norm_num
  · rw [argmax_fin2_eq_zero_iff]
    simp only [Problem.P1, Fin.sum_univ_two, hS3, hS3']
    simp [P, gambleProblem] <;> norm_num

/-- **B19, S2 rescues both**: for `ε > 0`, `P2 (S2)` is `H` on the gamble, so its argmax is
`argmax H`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 030 (B19, S2 escape); `fx_timing.py` B19 ("S2 at T2: P2 = H")
Kind: C
Fidelity: exact
Hyps: (a) `0 < ε` -/
theorem B19_S2 (hε : 0 < ε) :
    argmaxOpt ((gambleProblem v 1 ε w h0 h1).P2 (gambleProblem v 1 ε w h0 h1).S2)
      = argmax (gambleProblem v 1 ε w h0 h1).H := by
  have hPL : ∀ a, (gambleProblem v 1 ε w h0 h1).PL a ≠ 0 := by
    intro a; rw [gamble_PL]; fin_cases a <;> simp <;> exact hε.ne'
  exact argmaxOpt_eq_argmax_of_forall_some fun a => P2_S2_eq _ a (hPL a)

end B19

/-! ### B20: the T2 policy weakly beats every T1 option -/

/-- **B20**: on `toyB v w (1 − δ) 1 π_b` with `w ≤ v` and `δ ≥ 0`, the T2 policy (`a₁` in `g`,
`a₀` in `b`) has `H`-value `π_g · 1 + π_b · v`, at least `H a₀` and `H a₁`; and it *is* cdot's
T2 policy (`a₁` in `g` iff `δ > 0`, `a₀` in `b` iff `v > 0`) with no penalty consulted.
Source: [[corr-legit-neg-inventory]] item 030 (B20); `fx_timing.py` B20
Kind: L
Fidelity: exact (an inequality about `H`, not a new object)
Hyps: (a) `w ≤ v`, `0 ≤ δ` -/
theorem B20 (v w δ πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1) (hw : w ≤ v) (hδ : 0 ≤ δ) (hb : 0 < πb)
    (hg : πb < 1) :
    let P := toyB v w (1 - δ) 1 πb h0 h1
    P.H 0 ≤ (1 - πb) * 1 + πb * v
    ∧ P.H 1 ≤ (1 - πb) * 1 + πb * v
    ∧ (argmax ((P.restrict {0} (restrict_singleton_mass_pos P 0 (by simp [P]; linarith))).P1 (S1 P.u))
        = {1} ↔ 0 < δ)
    ∧ (argmax ((P.restrict {1} (restrict_singleton_mass_pos P 1 (toyB_b_mass_pos v w (1 - δ) 1 πb h0 h1 hb))).P1 (S1 P.u))
        = {0} ↔ 0 < v) := by
  intro P
  have hg0 : 0 < P.prior 0 := by simp [P]; linarith
  have hb1 : 0 < P.prior 1 := toyB_b_mass_pos v w (1 - δ) 1 πb h0 h1 hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [P]; rw [toyB_H_zero]; nlinarith
  · simp only [P]; rw [toyB_H_one]; nlinarith
  · rw [argmax_fin2_eq_one_iff, restrict_singleton_P1 P 0 hg0, restrict_singleton_P1 P 0 hg0]
    simp [P]
  · rw [argmax_fin2_eq_zero_iff, restrict_singleton_P1 P 1 hb1, restrict_singleton_P1 P 1 hb1]
    simp [P]

/-- **B20's numbers** (`v = 1/100, w = −1, δ = 1/10, π_b = 1/2`): the T2 policy's `H`-value is
`101/200` against the best T1 option's `91/200`.
Source: [[corr-legit-neg-inventory]] item 030 (B20)
Kind: N+
Fidelity: exact -/
theorem B20_numbers :
    let P := toyB (1/100) (-1) (1 - 1/10) 1 (1/2) (by norm_num) (by norm_num)
    (1 - 1/2 : ℚ) * 1 + 1/2 * (1/100) = 101/200 ∧ P.H 0 = 91/200 ∧ P.H 1 = 0 := by
  intro P
  refine ⟨by norm_num, ?_, ?_⟩
  · simp only [P, toyB_H_zero]; norm_num
  · simp only [P, toyB_H_one]; norm_num

/-! ### C9: late decisions -/

/-- In a fully legitimate problem every graded proposal is the diagonal value: `P3 = P1`,
`P4b = κ P(L) + (1 − κ) P1` (with `P(L) = 1`), `P5 = some P1`.
Source: [[corr-legit-neg-inventory]] item 042 (C9 (b), "every proposal")
Kind: L
Fidelity: exact -/
theorem proposals_of_allLeg (P : Problem S A) (a : A) (h : ∀ s, P.leg s a = true)
    (Wg K V : MenuVec S A) (lam κ κ' : ℚ) :
    P.PL a = 1 ∧ P.P3 Wg lam V a = P.P1 V a ∧ P.P4b Wg κ κ' V a = κ + (1 - κ) * P.P1 V a
    ∧ P.P5 K V a = some (P.P1 V a) := by
  have hPL : P.PL a = 1 := by
    unfold Problem.PL Problem.mass
    simp only [h, ind_true, mul_one]; exact P.prior_sum
  refine ⟨hPL, ?_, ?_, ?_⟩
  · unfold Problem.P3 Problem.P1
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [h s]
  · unfold Problem.P4b Problem.P1
    have : ∑ s, P.prior s * (ind (P.leg s a) * (κ + (1 - κ) * V s a a)
        + ind (!P.leg s a) * κ' * Wg s a a) = ∑ s, (κ * P.prior s + (1 - κ) * (P.prior s * ind (P.leg s a) * V s a a)) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [h s]; ring
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, P.prior_sum, mul_one]
  · unfold Problem.P5
    rw [if_neg (by rw [hPL]; exact one_ne_zero), if_pos hPL]

/-- **C9 (a), state `b` known** (`toyC v p x`, T2 at `b`): cdot keeps iff `v > 0`; `P2 a₁` and
`P5 a₁` are `none` (exclusion convention); `P3` steers iff `x > v`; `P4a` keeps; `P4b` keeps
for `0 ≤ x ≤ 1`, `0 ≤ κ' < κ ≤ 1`, `0 ≤ v`; and the hybrid penalty `p'` at `(g, a₁)` is never
read (`P1` under `hybridV` equals `P1` under `S1`).
Source: [[corr-legit-neg-inventory]] item 042 (C9 (a)); `c09_late_decision.py` `state_b`
Kind: P
Fidelity: exact -/
theorem C9_state_b (v p x c κ κ' : ℚ) :
    let P := toyC v p x
    let Pb := P.restrict {1} (restrict_singleton_mass_pos P 1 (by norm_num [P, toyC]))
    (argmax (Pb.P1 (S1 P.u)) = {0} ↔ 0 < v)
    ∧ Pb.P2 (S1 P.u) 1 = none
    ∧ Pb.P5 (toyC_K c) (S1 P.u) 1 = none
    ∧ (argmax (Pb.P3 (toyC_W x) 1 (S1 P.u)) = {1} ↔ v < x)
    ∧ argmaxLex (Pb.P4a (toyC_W x) (S1 P.u)) = {0}
    ∧ (0 ≤ x → x ≤ 1 → 0 ≤ κ' → κ' < κ → κ ≤ 1 → 0 ≤ v →
        argmax (Pb.P4b (toyC_W x) κ κ' (S1 P.u)) = {0})
    ∧ (∀ p' a, Pb.P1 (hybridV P p') a = Pb.P1 (S1 P.u) a) := by
  intro P Pb
  have hs : 0 < P.prior 1 := by norm_num [P, toyC]
  have hP1 : ∀ a, Pb.P1 (S1 P.u) a = ![v, 0] a := by
    intro a; simp only [Pb]; rw [restrict_singleton_P1 P 1 hs]; fin_cases a <;> simp [P, toyC]
  have hPL : ∀ a, Pb.PL a = ![1, 0] a := by
    intro a; simp only [Pb]; rw [restrict_singleton_PL P 1 hs]; fin_cases a <;> simp [P, toyC]
  have hP3 : ∀ a, Pb.P3 (toyC_W x) 1 (S1 P.u) a = ![v, x] a := by
    intro a; simp only [Pb]; rw [restrict_singleton_P3 P 1 hs]; fin_cases a <;> simp [P, toyC, toyC_W]
  have hP4b : ∀ a, Pb.P4b (toyC_W x) κ κ' (S1 P.u) a = ![κ + (1 - κ) * v, κ' * x] a := by
    intro a; simp only [Pb]; rw [restrict_singleton_P4b P 1 hs]; fin_cases a <;> simp [P, toyC, toyC_W]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff, hP1, hP1]; simp
  · apply P2_of_eq; rw [hPL]; rfl
  · unfold Problem.P5; rw [hPL]; simp
  · rw [argmax_fin2_eq_one_iff, hP3, hP3]; simp
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two, Problem.P4a,
        Prod.Lex.toLex_le_toLex, hPL, hP3] <;> norm_num
  · intro hx0 hx1 hk0 hk hk1 hv
    rw [argmax_fin2_eq_zero_iff, hP4b, hP4b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1 - κ) hv, mul_le_mul_of_nonneg_left hx1 hk0]
  · intro p' a
    simp only [Pb]; rw [restrict_singleton_P1 P 1 hs, restrict_singleton_P1 P 1 hs]
    fin_cases a <;> simp [P, toyC, hybridV, Problem.penalise]

/-- **C9 (b), state `g` known** (`u(g, a₀) = 1/2`, `u(g, a₁) = 3/4`, both legitimate; the
fixture's `state_g`): with the hybrid penalty `p` kept at T2, cdot refuses the harmless `1/4`
gain iff `p > 1/4`, ties at `1/4`, takes it iff `p < 1/4`; `P2` agrees (both `P(L) = 1`), and by
`proposals_of_allLeg` so do `P3`, `P4b`, `P5`. Exclusion convention (nothing excluded).
Source: [[corr-legit-neg-inventory]] item 042 (C9 (b)); `c09_late_decision.py` `state_g`
Kind: P
Fidelity: exact (parametric in `p`; the fixture's `p ∈ {1/2, 1/4, 0}`)
Hyps: (a) none -/
theorem C9_state_g (p : ℚ) :
    let P := toyB 0 0 (1/2) (3/4) (1/2) (by norm_num) (by norm_num)
    let Pg := P.restrict {0} (restrict_singleton_mass_pos P 0 (by norm_num [P]))
    (argmax (Pg.P1 (hybridV P p)) = {0} ↔ 1/4 < p)
    ∧ (argmax (Pg.P1 (hybridV P p)) = univ ↔ p = 1/4)
    ∧ (argmax (Pg.P1 (hybridV P p)) = {1} ↔ p < 1/4)
    ∧ argmaxOpt (Pg.P2 (hybridV P p)) = argmax (Pg.P1 (hybridV P p))
    ∧ (∀ a, Pg.leg 0 a = true) := by
  intro P Pg
  have hs : 0 < P.prior 0 := by norm_num [P]
  have hP1 : ∀ a, Pg.P1 (hybridV P p) a = ![1/2, 3/4 - p] a := by
    intro a; simp only [Pg]; rw [restrict_singleton_P1 P 0 hs]
    fin_cases a <;> simp [P, hybridV, Problem.penalise]
  have hPL : ∀ a, Pg.PL a = 1 := by
    intro a; simp only [Pg]; rw [restrict_singleton_PL P 0 hs]; fin_cases a <;> simp [P]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff, hP1, hP1]; simp; constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_univ_iff, hP1, hP1]; simp; constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_one_iff, hP1, hP1]; simp; constructor <;> intro h <;> linarith
  · rw [argmaxOpt_P2_eq_argmax_div _ _ (fun a => by rw [hPL]; exact one_ne_zero)]
    exact argmax_congr fun a => by rw [hPL, div_one]
  · intro a; fin_cases a <;> rfl

end Cleanroom.Corrigibility.LegitNegPricing
