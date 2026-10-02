import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# cdot against `H`: B6/B7 conservativity, B8/B8b indifference, B9 over-protection

Package `legit-neg-pricing`, targets 5, 6 and 11. Sources: `clusters/B/NEGATIVES.md` B6–B9,
`clusters/B/VERIFY.md` (B6 narrowed by V6, B8 survives, B9 narrowed by V9 and the cross-cutting
finding), `clusters/B/fixtures/fx_cdot.py`, `verify_B.py` (V6, V9), pinned by
[[corr-legit-neg-inventory]] items 019–021 and [[corr-legit-neg-2-inventory]] item 2-014.

Register: `H` is unconstrained expected utility with correctly learned values (`Problem.W`'s
docstring). Every statement here is a distortion *relative to `H`*; none is named as a failure
by Abram's concerns, and B9 in particular is Abram's own steering worry seen from `H`'s side
(ATTRIBUTION-UNVETTED, as the source's verifier records).
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-! ### B6: `H`-conservativity against a fully legitimate alternative -/

/-- **B6 (general).** Against a *fully legitimate* alternative `b`, if the humans value every
void terminal of `a` at or above the floor, then `H a − H b ≥ P1 a − P1 b`, so cdot strictly
prefers `a` only if `H` does, and by a larger margin. V6 shows the full legitimacy of `b` cannot
be dropped (`V6_witness`).
Source: [[corr-legit-neg-inventory]] item 019 (B6); VERIFY B "B6 — narrowed" (V6)
Kind: P
Fidelity: exact (the narrowed form: keep-vs-void, `b` fully legitimate)
Hyps: (a) `0 ≤ u` on `a`'s void terminals is the source's floor assumption -/
theorem H_conservative_of_allLeg (P : Problem S A) (a b : A) (hb : ∀ s, P.leg s b = true)
    (ha : ∀ s, P.leg s a = false → 0 ≤ P.u s a) :
    P.P1 (S1 P.u) a - P.P1 (S1 P.u) b ≤ P.H a - P.H b
    ∧ (P.P1 (S1 P.u) b < P.P1 (S1 P.u) a → P.H b < P.H a) := by
  have h1 := P1_S1_eq_H_sub_voidPart P a
  have h2 := P.P1_S1_eq_H_of_allLeg b hb
  have h3 := voidPart_nonneg P a ha
  constructor
  · linarith
  · intro h; linarith

/-- **B6 on the toy** (`u(g, ·) = ug` on both options): cdot's protection of `b` is `π_b v`,
the humans' stake is `π_b (v − w)`, and `ΔH − ΔP1 = π_b w` (differences `a₁ − a₀`).
Source: [[corr-legit-neg-inventory]] item 019 (B6, toy); `fx_cdot.py` B6 (`dH − d1 = π_b w`)
Kind: L
Fidelity: exact -/
theorem B6_toy (v w ug πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1) :
    (toyB v w ug ug πb h0 h1).P1 (S1 (toyB v w ug ug πb h0 h1).u) 0
        - (toyB v w ug ug πb h0 h1).P1 (S1 (toyB v w ug ug πb h0 h1).u) 1 = πb * v
    ∧ (toyB v w ug ug πb h0 h1).H 0 - (toyB v w ug ug πb h0 h1).H 1 = πb * (v - w)
    ∧ ((toyB v w ug ug πb h0 h1).H 1 - (toyB v w ug ug πb h0 h1).H 0)
        - ((toyB v w ug ug πb h0 h1).P1 (S1 (toyB v w ug ug πb h0 h1).u) 1
            - (toyB v w ug ug πb h0 h1).P1 (S1 (toyB v w ug ug πb h0 h1).u) 0) = πb * w := by
  rw [toyB_P1_S1_zero, toyB_P1_S1_one, toyB_H_zero, toyB_H_one]
  refine ⟨by ring, by ring, by ring⟩

/-- **B6's boundary, the tie at the floor**: at `v = 0`, `w = −1` cdot is indifferent while `H`
strictly keeps — the under-protection of size `π_b |w|` against a below-floor standard.
Source: [[corr-legit-neg-inventory]] item 019 (B6); `fx_cdot.py` B6 ("tie at v=0 while H strictly keeps")
Kind: N+
Fidelity: exact -/
theorem B6_floor_tie :
    argmax ((toyB 0 (-1) 1 1 (1/2) (by norm_num) (by norm_num)).P1
      (S1 (toyB 0 (-1) 1 1 (1/2) (by norm_num) (by norm_num)).u)) = univ
    ∧ argmax (toyB 0 (-1) 1 1 (1/2) (by norm_num) (by norm_num)).H = {0} := by
  rw [argmax_fin2_eq_univ_iff, argmax_fin2_eq_zero_iff, toyB_P1_S1_zero, toyB_P1_S1_one,
    toyB_H_zero, toyB_H_one]
  norm_num

/-- **B7, the worst case**: `v = 1/1000`, `w = −K`, `δ = 1/100`: cdot voids `b` for every `K`,
at human loss `(v + K − δ)/2`; for every `M` some `K > 0` makes the loss exceed `M` times the
`g`-gain `δ/2`. N−: at `w = 0` (`B7_floor_agrees`) `H` agrees with voiding.
Source: [[corr-legit-neg-inventory]] item 019 (B7); NEGATIVES B7
Kind: P
Fidelity: exact (the unbounded ratio stated as `∀ M ∃ K`)
Hyps: (a) none beyond the toy's parameters -/
theorem B7_worst_case :
    (∀ K : ℚ, argmax ((toyB (1/1000) (-K) (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).P1
        (S1 (toyB (1/1000) (-K) (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).u)) = {1}
      ∧ (toyB (1/1000) (-K) (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).H 0
          - (toyB (1/1000) (-K) (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).H 1
          = (1/1000 + K - 1/100) / 2)
    ∧ ∀ M : ℚ, ∃ K : ℚ, 0 < K ∧
        M * ((1/100 : ℚ) / 2) < (toyB (1/1000) (-K) (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).H 0
          - (toyB (1/1000) (-K) (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).H 1 := by
  refine ⟨fun K => ⟨?_, ?_⟩, fun M => ⟨max M 0 / 100 + 1, ?_, ?_⟩⟩
  · rw [argmax_fin2_eq_one_iff, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · rw [toyB_H_zero, toyB_H_one]; ring
  · have := le_max_right M 0; linarith
  · rw [toyB_H_zero, toyB_H_one]
    have := le_max_left M 0
    nlinarith

/-- **B7's N−**: with `w = 0` the floor is the scale minimum and `H` agrees with voiding.
Source: [[corr-legit-neg-inventory]] item 019 (B7, N−)
Kind: N-
Fidelity: exact -/
theorem B7_floor_agrees :
    argmax ((toyB (1/1000) 0 (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).P1
        (S1 (toyB (1/1000) 0 (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).u)) = {1}
    ∧ argmax (toyB (1/1000) 0 (1 - 1/100) 1 (1/2) (by norm_num) (by norm_num)).H = {1} := by
  rw [argmax_fin2_eq_one_iff, argmax_fin2_eq_one_iff, toyB_P1_S1_zero, toyB_P1_S1_one,
    toyB_H_zero, toyB_H_one]
  norm_num

/-! ### V6: the fully legitimate alternative cannot be dropped -/

/-- V6's problem: three equiprobable states; `a` (`0`) void on `s₁, s₂` (values `0`) and
legitimate on `s₃` (value `1`); `b` (`1`) void on `s₁` (`1/2`), legitimate on `s₂, s₃`
(`1/2`, `1/2 − ε`), `ε = 1/100`.
Source: [[corr-legit-neg-2-inventory]] item 2-014 (V6); `verify_B.py:29-45`
Kind: D
Fidelity: exact -/
def v6 : Problem (Fin 3) (Fin 2) where
  prior := fun _ => 1/3
  prior_nonneg := fun _ => by norm_num
  prior_sum := by simp [Fin.sum_univ_three]
  leg := fun s a => ![![false, false, true], ![false, true, true]] a s
  u := fun s a => ![![0, 0, 1], ![1/2, 1/2, 1/2 - 1/100]] a s

/-- **V6 (N+ for B6's hypothesis)**: every void value is at or above the floor, `a` voids more
than `b`, cdot picks `a` and `H` picks `b` — so B6 needs the alternative fully legitimate.
Source: [[corr-legit-neg-2-inventory]] item 2-014 (V6); VERIFY B "B6 — narrowed"
Kind: N+
Fidelity: exact -/
theorem V6_witness :
    (∀ s a, v6.leg s a = false → 0 ≤ v6.u s a)
    ∧ v6.PL 0 < v6.PL 1
    ∧ argmax (v6.P1 (S1 v6.u)) = {0}
    ∧ argmax v6.H = {1} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s a h; fin_cases s <;> fin_cases a <;> simp [v6] at h <;> norm_num [v6]
  · simp [v6, Problem.PL, Problem.mass, Fin.sum_univ_three] <;> norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp [v6, Problem.P1, Fin.sum_univ_three] <;> norm_num
  · rw [argmax_fin2_eq_one_iff]; simp [v6, Problem.H, Problem.W, EU, Fin.sum_univ_three] <;> norm_num

/-! ### B8/B8b: indifference between mild and catastrophic illegitimacy, up to `D · η` -/

/-- **B8b (general).** If cdot weakly prefers `a` to `b` and `0 ≤ u ≤ D` on the relevant void
terminals, then `H b − H a ≤ D · P(¬L | b) − 𝔼[(1 − ℓ_a) u_a] ≤ D · P(¬L | b)`: the human loss is
bounded by `D` times the void mass of the option forgone.
Source: [[corr-legit-neg-inventory]] item 020 (B8b); NEGATIVES B8b (proof)
Kind: P
Fidelity: exact
Hyps: (a) the range `0 ≤ u ≤ D` on void terminals is the source's modelling assumption -/
theorem B8b_bound (P : Problem S A) (a b : A) {D : ℚ}
    (hab : P.P1 (S1 P.u) b ≤ P.P1 (S1 P.u) a)
    (ha : ∀ s, P.leg s a = false → 0 ≤ P.u s a)
    (hb : ∀ s, P.leg s b = false → P.u s b ≤ D) :
    P.H b - P.H a ≤ D * P.mass (fun s => !P.leg s b) - voidPart P a
    ∧ D * P.mass (fun s => !P.leg s b) - voidPart P a ≤ D * P.mass (fun s => !P.leg s b) := by
  have h1 := P1_S1_eq_H_sub_voidPart P a
  have h2 := P1_S1_eq_H_sub_voidPart P b
  have h3 := voidPart_nonneg P a ha
  have h4 := voidPart_le P b hb
  constructor <;> linarith

/-- B8's problem: a coin `L` (`0`, mass `1 − η`) / `N` (`1`, mass `η`); both options void on `N`;
`mild` (`0`) worth `1/2` on `L` and `D` on `N`; `cat` (`1`) worth `1/2 + ε` on `L` and `0` on `N`.
Source: [[corr-legit-neg-inventory]] item 020 (B8); `fx_cdot.py` B8
Kind: D
Fidelity: exact -/
def b8 (D η ε : ℚ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : Problem (Fin 2) (Fin 2) where
  prior := ![1 - η, η]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s _ => decide (s = 0)
  u := fun s a => ![![1/2, 1/2 + ε], ![D, 0]] s a

/-- **B8 (N+ for B8b, attained at the tie)**: for `0 < η < 1`, both proposals take `cat` iff
`ε > 0` and tie iff `ε = 0`; the human loss `H mild − H cat = D η − (1 − η) ε` attains the B8b
bound `D η` exactly at the tie `ε = 0`; at `η = 1` `P2` is `none` on both (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 020 (B8); VERIFY B "B8 — survives" ("attained only at the tie")
Kind: N+
Fidelity: exact -/
theorem B8_attained (D η ε : ℚ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    (η < 1 →
      (argmax ((b8 D η ε h0 h1).P1 (S1 (b8 D η ε h0 h1).u)) = {1} ↔ 0 < ε)
      ∧ (argmax ((b8 D η ε h0 h1).P1 (S1 (b8 D η ε h0 h1).u)) = univ ↔ ε = 0)
      ∧ argmaxOpt ((b8 D η ε h0 h1).P2 (S1 (b8 D η ε h0 h1).u))
          = argmax ((b8 D η ε h0 h1).P1 (S1 (b8 D η ε h0 h1).u)))
    ∧ (b8 D η ε h0 h1).H 0 - (b8 D η ε h0 h1).H 1 = D * η - (1 - η) * ε
    ∧ (η = 1 → ∀ a, (b8 D η ε h0 h1).P2 (S1 (b8 D η ε h0 h1).u) a = none) := by
  have hP1 : ∀ a, (b8 D η ε h0 h1).P1 (S1 (b8 D η ε h0 h1).u) a = (1 - η) * ![1/2, 1/2 + ε] a := by
    intro a; fin_cases a <;> simp [b8, Problem.P1, Fin.sum_univ_two]
  have hPL : ∀ a, (b8 D η ε h0 h1).PL a = 1 - η := by
    intro a; simp [b8, Problem.PL, Problem.mass, Fin.sum_univ_two]
  refine ⟨fun hη => ⟨?_, ?_, ?_⟩, ?_, fun hη a => ?_⟩
  · rw [argmax_fin2_eq_one_iff, hP1, hP1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [argmax_fin2_eq_univ_iff, hP1, hP1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor
    · intro h
      have h' : (1 - η) * ε = 0 := by linarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' (by linarith)
      · exact h''
    · intro h; subst h; ring
  · rw [argmaxOpt_P2_eq_argmax_div _ _ (fun a => by rw [hPL]; linarith)]
    simp only [hPL]
    exact argmax_div_pos _ (by linarith)
  · simp [b8, Problem.H, Problem.W, EU, Fin.sum_univ_two]; ring
  · apply P2_of_eq; rw [hPL, hη]; norm_num

/-! ### B9: over-protection (a distortion relative to `H`) -/

/-- B9's problem: `risky` (`0`) keeps legitimacy w.p. `1 − η` and is worth `1` on `L`, `w` on the
void world (`1` in B9, `1/2` in V9's graded reading); `safe` (`1`) keeps it surely and is worth
`1 − η + e₂` everywhere.
Source: [[corr-legit-neg-inventory]] item 021 (B9); `fx_cdot.py` B9; `verify_B.py` V9
Kind: D
Fidelity: exact -/
def b9 (η e2 w : ℚ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : Problem (Fin 2) (Fin 2) where
  prior := ![1 - η, η]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s a => decide (a = 1) || decide (s = 0)
  u := fun s a => ![![1, 1 - η + e2], ![w, 1 - η + e2]] s a

/-- **B9 / V9 (parametric).** cdot takes `safe` iff `e₂ > 0`; `H` takes `risky` iff `e₂ < η w`;
the human loss is `η w − e₂` (`η − 1/1000` in B9, `η/2 − 1/1000` in V9); conditioning takes
`risky` iff `e₂ < η` (for `η < 1`). Register: a distortion relative to `H` — by `RUN.md` §2.1
(verbatim, per the verifier) cdot's refusal to steer toward the void here is Abram's own stated
steering worry seen from `H`'s side; not a failure by his concerns (ATTRIBUTION-UNVETTED).
N−: at `w = 0` (`B9_floor`) `H` agrees with cdot.
Source: [[corr-legit-neg-inventory]] item 021 (B9); [[corr-legit-neg-2-inventory]] item 2-014 (V9); VERIFY B cross-cutting finding
Kind: P
Fidelity: exact (parametric in `η, e₂, w`)
Hyps: (a) none -/
theorem B9_over_protection (η e2 w : ℚ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    (argmax ((b9 η e2 w h0 h1).P1 (S1 (b9 η e2 w h0 h1).u)) = {1} ↔ 0 < e2)
    ∧ (argmax (b9 η e2 w h0 h1).H = {0} ↔ e2 < η * w)
    ∧ (b9 η e2 w h0 h1).H 0 - (b9 η e2 w h0 h1).H 1 = η * w - e2
    ∧ (η < 1 → (argmaxOpt ((b9 η e2 w h0 h1).P2 (S1 (b9 η e2 w h0 h1).u)) = {0} ↔ e2 < η)) := by
  have hP1 : ∀ a, (b9 η e2 w h0 h1).P1 (S1 (b9 η e2 w h0 h1).u) a
      = ![(1 - η) * 1, 1 - η + e2] a := by
    intro a; fin_cases a <;> simp [b9, Problem.P1, Fin.sum_univ_two] <;> ring
  have hH : ∀ a, (b9 η e2 w h0 h1).H a = ![(1 - η) + η * w, 1 - η + e2] a := by
    intro a; fin_cases a <;> simp [b9, Problem.H, Problem.W, EU, Fin.sum_univ_two] <;> ring
  have hPL : ∀ a, (b9 η e2 w h0 h1).PL a = ![1 - η, 1] a := by
    intro a; fin_cases a <;> simp [b9, Problem.PL, Problem.mass, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, fun hη => ?_⟩
  · rw [argmax_fin2_eq_one_iff, hP1, hP1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_zero_iff, hH, hH]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor <;> intro h <;> linarith
  · rw [hH, hH]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · rw [argmaxOpt_P2_eq_argmax_div _ _ (fun a => by fin_cases a <;> simp [hPL] <;> linarith),
      argmax_fin2_eq_zero_iff]
    simp only [hP1, hPL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
      mul_one]
    rw [div_self (by linarith : (1 - η) ≠ 0)]
    constructor <;> intro h <;> linarith

/-- **B9's N−**: with `u = 0` on the void world the floor is correct and `H` agrees with cdot.
Source: [[corr-legit-neg-inventory]] item 021 (B9, N−)
Kind: N-
Fidelity: exact -/
theorem B9_floor (η e2 : ℚ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (he : 0 < e2) :
    argmax ((b9 η e2 0 h0 h1).P1 (S1 (b9 η e2 0 h0 h1).u)) = {1}
    ∧ argmax (b9 η e2 0 h0 h1).H = {1} := by
  have h := B9_over_protection η e2 0 h0 h1
  refine ⟨h.1.2 he, ?_⟩
  rw [argmax_fin2_eq_one_iff]
  have hH : ∀ a, (b9 η e2 0 h0 h1).H a = ![(1 - η) + η * 0, 1 - η + e2] a := by
    intro a; fin_cases a <;> simp [b9, Problem.H, Problem.W, EU, Fin.sum_univ_two] <;> ring
  rw [hH, hH]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linarith

end Cleanroom.Corrigibility.LegitNegPricing
