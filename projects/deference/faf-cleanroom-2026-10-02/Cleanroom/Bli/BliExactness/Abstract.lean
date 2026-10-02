import Cleanroom.Bli.BliExactness.Defs

/-!
# `bli-exactness` — the abstract halves of X1 and X2 (FAF-free shapes other packages import)

* **X1 (a)** `exact_reflection_fails_abstract`: over any type with a designated `L`, partition
  events `χ i` with cells `I i`, a conjunction `and` and a valuation `p` that respects
  "`L ↔ (ℙ_m(L) < p₀)`" in conjunction with each **one-sided** cell (slide 40 / bli-slides-041's
  precise statement), exact reflection fails at every one-sided cell of positive mass **in the
  interval sense**: the conditional probability of `L` given the cell lies *outside* the cell
  (`¬ (lo · p(χ) < p(L ⋏ χ) ≤ hi · p(χ))`) — it is `1 > hi` below the threshold and `0 ≤ lo` at
  or above it, which is the slide's "`= 1 ≠ p` … `= 0 ≠ p`". The midpoint form
  `p(L ⋏ χ) ≠ mid · p(χ)` is the corollary `exact_reflection_fails_abstract_mid`
  (`midpoint_of_interval` relates the two; audit r1 B1: the midpoint form alone is the F5
  artifact and holds for `⊤`). The equivalence is a **(c) substitution here** (an abstract
  designated `L`); `Liar.lean` discharges it over FAF's own diagonal (grade (a)). Straddling
  cells are **not** quantified over (Known issue 2) — the slide's caveat; over FAF the completed
  theory decides the liar, which voids the caveat only for the *midpoint* form (`Defs.lean`
  `decided_fails_midpoint`), not for the interval claim.
  N+: `abstractWitness_*` — a probability-shaped valuation with positive mass on a cell of each side.
* **X2 (i)** `no_sharp_fixed_point`: `p = 𝟙(p < p₀)` has no real solution (Soto PDF 07's
  "discontinuity … no fixed point", bli-soto-a-058 (ii), *is* this one-liner), and
  `no_zero_indicator_fixed_point`: `p = 𝟙(p = 0)` has none (PDF 04 footnote 3, bli-soto-a-036 (ii)).
* **bli-soto-b-024's non-locality observation** `selfTrust_not_world_local`: exact self-trust is
  a property of the weights on the betting table, not of its support — two weightings with the
  same (full) support, one satisfying the identity, one not.
-/

namespace Cleanroom.Bli.BliExactness

open Finset

/-! ## X1 (a): the abstract two-case argument -/

/-- **Exact reflection fails on a liar, abstractly — interval form** (slide 40 bullet 2;
bli-slides-041: "`ℙ_n(L | ℙ_m(L) = p) = 1 ≠ p` below `½`, `= 0 ≠ p` at or above"). Over a type `α`
with a designated `L`, events `χ i` indexed by cells `I i = (lo, hi]`, a conjunction `and` and a
valuation `p`: if `p` respects "`L ↔ (ℙ_m(L) < p₀)`" in conjunction with each one-sided cell —
`hlow` (cells entirely below the threshold entail `L`) and `hhigh` (cells entirely at or above it
entail `∼L`) — then at every one-sided cell `i` of positive mass **the conditional probability of
`L` given the cell lies outside the cell**: `¬ (lo · p(χ_i) < p(L ⋏ χ_i) ≤ hi · p(χ_i))`. Below the
threshold the conditional is `1` and `hi < p₀ ≤ 1`; at or above it the conditional is `0` and
`lo ≥ p₀ > 0`. Straddling cells are not constrained (the slide's caveat). The threshold
`p₀ ∈ (0, 1]`; the slide's instance is `p₀ = ½`. No finiteness of `ι` and no sign condition on
`p` is needed. The midpoint form is the corollary `exact_reflection_fails_abstract_mid`.
Source: slide 40 bullet 2 ([[bli-slides-inventory]] 041, precise statement); mandate X1 (a);
audit r1 fidelity B1 (interval conclusion adopted)
Kind: P
Fidelity: exact (one-sided cells; interval form — the slide's conclusion)
Hyps: (c) `hlow`/`hhigh` — the equivalence `L ↔ (ℙ_m(L) < p₀)` for an abstract designated `L`
(discharged at grade (a) over FAF's diagonal by `exact_reflection_fails_liar`) -/
theorem exact_reflection_fails_abstract {α ι : Type*} (L : α) (χ : ι → α) (I : ι → ℚ × ℚ)
    (and : α → α → α) (p : α → ℝ) (p₀ : ℚ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hlow : ∀ i, (I i).2 < p₀ → p (and L (χ i)) = p (χ i))
    (hhigh : ∀ i, p₀ ≤ (I i).1 → p (and L (χ i)) = 0)
    (i : ι) (hside : (I i).2 < p₀ ∨ p₀ ≤ (I i).1) (hpos : 0 < p (χ i)) :
    ¬ (((I i).1 : ℝ) * p (χ i) < p (and L (χ i)) ∧
        p (and L (χ i)) ≤ ((I i).2 : ℝ) * p (χ i)) := by
  rcases hside with hside | hside
  · rw [hlow i hside]
    rintro ⟨-, h⟩
    have hhiR : ((I i).2 : ℝ) < 1 := by
      have : (I i).2 < 1 := lt_of_lt_of_le hside hp₁
      exact_mod_cast this
    nlinarith [mul_pos hpos (sub_pos.2 hhiR)]
  · rw [hhigh i hside]
    rintro ⟨h, -⟩
    have hloR : (0 : ℝ) < ((I i).1 : ℝ) := by
      have : (0 : ℚ) < (I i).1 := lt_of_lt_of_le hp₀ hside
      exact_mod_cast this
    have := mul_pos hloR hpos
    linarith

/-- **The midpoint form** (the F5 reading, "exact at the cell's representative"): under the same
hypotheses, at every one-sided cell `i` with `lo ≤ hi` and positive mass,
`p(L ⋏ χ_i) ≠ mid(I i) · p(χ_i)` (the conditional is `1 ≠ mid < 1` below, `0 ≠ mid > 0` above).
Weaker than the interval form (`midpoint_of_interval`), and — unlike it — true of every
`𝒲`-decided sentence at every interior-midpoint cell (`Defs.lean` `decided_fails_midpoint`);
kept as the shape `ExactReflection`'s refutations instantiate.
Source: slide 40 bullet 2; mandate X1 (a); findings F5
Kind: P
Fidelity: weaker: midpoint representative in place of the interval conclusion
Hyps: (c) `hlow`/`hhigh` as `exact_reflection_fails_abstract` -/
theorem exact_reflection_fails_abstract_mid {α ι : Type*} (L : α) (χ : ι → α) (I : ι → ℚ × ℚ)
    (and : α → α → α) (p : α → ℝ) (p₀ : ℚ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hlow : ∀ i, (I i).2 < p₀ → p (and L (χ i)) = p (χ i))
    (hhigh : ∀ i, p₀ ≤ (I i).1 → p (and L (χ i)) = 0)
    (i : ι) (hI : (I i).1 ≤ (I i).2) (hside : (I i).2 < p₀ ∨ p₀ ≤ (I i).1)
    (hpos : 0 < p (χ i)) :
    p (and L (χ i)) ≠ ((mid (I i) : ℚ) : ℝ) * p (χ i) := by
  rcases hside with hside | hside
  · rw [hlow i hside]
    intro h
    have hmid : mid (I i) < 1 := by unfold mid; linarith
    have hmidR : ((mid (I i) : ℚ) : ℝ) < 1 := by exact_mod_cast hmid
    nlinarith [mul_pos hpos (sub_pos.2 hmidR)]
  · rw [hhigh i hside]
    intro h
    have hmid : 0 < mid (I i) := by unfold mid; linarith
    have hmidR : (0 : ℝ) < ((mid (I i) : ℚ) : ℝ) := by exact_mod_cast hmid
    have := mul_pos hmidR hpos
    linarith

/-- The interval conclusion implies the midpoint conclusion for a **nonempty** cell `lo < hi`
(at `lo = hi` the cell `(lo, hi]` is empty — F5 — and the interval conclusion is vacuous).
Source: audit r1 fidelity B1 (probe `midpoint_of_interval`, adopted)
Kind: L
Fidelity: n/a -/
theorem midpoint_of_interval {lo hi x y : ℝ} (hI : lo < hi) (hpos : 0 < y)
    (h : ¬ (lo * y < x ∧ x ≤ hi * y)) : x ≠ (lo + hi) / 2 * y := by
  intro heq
  apply h
  subst heq
  constructor <;> nlinarith

/-- Corollary shape for importers: under the same hypotheses, no cell family can place the
conditional inside the cell at *all* one-sided cells of positive mass.
Source: mandate X1 (a) (the shape `def-*` packages import)
Kind: L
Fidelity: n/a -/
theorem not_forall_exact_abstract {α ι : Type*} (L : α) (χ : ι → α) (I : ι → ℚ × ℚ)
    (and : α → α → α) (p : α → ℝ) (p₀ : ℚ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hlow : ∀ i, (I i).2 < p₀ → p (and L (χ i)) = p (χ i))
    (hhigh : ∀ i, p₀ ≤ (I i).1 → p (and L (χ i)) = 0)
    (i : ι) (hside : (I i).2 < p₀ ∨ p₀ ≤ (I i).1) (hpos : 0 < p (χ i)) :
    ¬ ∀ j, ((I j).1 : ℝ) * p (χ j) < p (and L (χ j)) ∧ p (and L (χ j)) ≤ ((I j).2 : ℝ) * p (χ j) :=
  fun h => exact_reflection_fails_abstract L χ I and p p₀ hp₀ hp₁ hlow hhigh i hside hpos (h i)

/-! ### N+ witness for X1 (a): positive mass on a cell of each side -/

/-- The abstract carrier: `L := 0`, cells `χ false := 1`, `χ true := 2`, conjunction
`and a b := Nat.pair a b + 3` (so `and L (χ false) = 4`, `and L (χ true) = 7`), cells
`I false := (0, ¼)` (below `½`), `I true := (¾, 1)` (above `½`).
Source: mandate X1 (a) (N+)
Kind: D
Fidelity: n/a -/
def absAnd (a b : ℕ) : ℕ := Nat.pair a b + 3

/-- The two partition events of the abstract witness.
Source: mandate X1 (a) (N+)
Kind: D
Fidelity: n/a -/
def absChi (b : Bool) : ℕ := if b then 2 else 1

/-- The two one-sided cells of the abstract witness.
Source: mandate X1 (a) (N+)
Kind: D
Fidelity: n/a -/
def absI (b : Bool) : ℚ × ℚ := if b then (3 / 4, 1) else (0, 1 / 4)

/-- The abstract valuation: mass `½` on each cell, the below cell entirely inside `L`
(`p(L ⋏ χ_false) = ½ = p(χ_false)`), the above cell entirely outside it (`p(L ⋏ χ_true) = 0`), and
`p(L) = ½ = p(L ⋏ χ_false) + p(L ⋏ χ_true)` (audit r1 adversarial N4: with `p(L) = 0` the former
valuation was not even monotone; now the five values are those of a probability on the four
atoms `L ∧ χ_false`, `∼L ∧ χ_true` (mass `½` each) and `L ∧ χ_true`, `∼L ∧ χ_false` (mass `0`)).
Source: mandate X1 (a) (N+: "`p χ₀ = p χ₁ = ½`, `p (L ⋏ χ₀) = ½`, `p (L ⋏ χ₁) = 0`")
Kind: D
Fidelity: n/a -/
noncomputable def absP (x : ℕ) : ℝ := if x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4 then 1 / 2 else 0

/-- `absAnd 0 1 = 4` and `absAnd 0 2 = 7`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma absAnd_vals : absAnd 0 1 = 4 ∧ absAnd 0 2 = 7 := by
  constructor <;> decide

/-- **N+ for X1 (a)**: the abstract witness inhabits the full hypothesis package of
`exact_reflection_fails_abstract` at `p₀ = ½` — nonnegative, additive on `L` over the two cells,
respects the equivalence on both one-sided cells, both cells one-sided with positive mass — so
the theorem's conclusion is non-vacuous on both sides.
Source: mandate X1 (a) (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem abstractWitness :
    (∀ x, 0 ≤ absP x) ∧
    absP 0 = absP (absAnd 0 (absChi false)) + absP (absAnd 0 (absChi true)) ∧
    (∀ b, (absI b).2 < 1 / 2 → absP (absAnd 0 (absChi b)) = absP (absChi b)) ∧
    (∀ b, 1 / 2 ≤ (absI b).1 → absP (absAnd 0 (absChi b)) = 0) ∧
    (∀ b, (absI b).1 ≤ (absI b).2 ∧ ((absI b).2 < 1 / 2 ∨ 1 / 2 ≤ (absI b).1)) ∧
    (∀ b, 0 < absP (absChi b)) := by
  have h4 := absAnd_vals.1
  have h7 := absAnd_vals.2
  refine ⟨fun x => ?_, ?_, fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_⟩
  · unfold absP; split_ifs <;> norm_num
  · simp [absChi, h4, h7, absP]
  · cases b <;> simp [absI, absChi, h4, h7, absP] <;> norm_num
  · cases b <;> simp [absI, absChi, h4, h7, absP]
  · cases b <;> simp [absI] <;> norm_num
  · cases b <;> simp [absChi, absP]

/-- The abstract witness exhibits the interval failure on both cells (the theorem applied to it):
the conditional is `1 ∉ (0, ¼]` below and `0 ∉ (¾, 1]` above.
Source: mandate X1 (a) (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem abstractWitness_fails (b : Bool) :
    ¬ (((absI b).1 : ℝ) * absP (absChi b) < absP (absAnd 0 (absChi b)) ∧
        absP (absAnd 0 (absChi b)) ≤ ((absI b).2 : ℝ) * absP (absChi b)) := by
  obtain ⟨h0, -, hlow, hhigh, hside, hpos⟩ := abstractWitness
  exact exact_reflection_fails_abstract (0 : ℕ) absChi absI absAnd absP (1 / 2) (by norm_num)
    (by norm_num) hlow hhigh b (hside b).2 (hpos b)

/-- The same witness under the midpoint form (`½ ≠ ⅛` below, `0 ≠ ⅞·½` above).
Source: mandate X1 (a) (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem abstractWitness_fails_mid (b : Bool) :
    absP (absAnd 0 (absChi b)) ≠ ((mid (absI b) : ℚ) : ℝ) * absP (absChi b) := by
  obtain ⟨h0, -, hlow, hhigh, hside, hpos⟩ := abstractWitness
  exact exact_reflection_fails_abstract_mid (0 : ℕ) absChi absI absAnd absP (1 / 2) (by norm_num)
    (by norm_num) hlow hhigh b (hside b).1 (hside b).2 (hpos b)

/-! ## X2 (i): the sharp fixed points that do not exist -/

/-- **No sharp fixed point**: no real `x` satisfies `x = 𝟙(x < p₀)` for a threshold
`p₀ ∈ (0, 1]`. This is Soto's "discontinuity of `fix(V)`, no fixed point" (PDF 07, "Introspection",
`Qₙ(“Qₙ(φ) > 0.5”) = 𝟙(Qₙ(φ) > 0.5)`) reduced to its arithmetic core, and the abstract half of
X2: a market exactly introspective about its own liar atom would price it at `𝟙(price < p₀)`.
Source: Soto PDF 07 p. 4–5 ([[bli-soto-a-inventory]] 058 (ii)); mandate X2 (i)
Kind: P
Fidelity: exact (the fixed-point obstruction; the market-maker continuity story is not modelled)
Hyps: (a) -/
theorem no_sharp_fixed_point (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1) :
    ¬ ∃ x : ℝ, x = if x < p₀ then 1 else 0 := by
  rintro ⟨x, hx⟩
  split_ifs at hx with h
  · linarith
  · linarith

/-- The slide's threshold: `x = 𝟙(x < ½)` has no solution.
Source: slide 40 (`L := ℙ_m(L) < ½`); mandate X2 (i)
Kind: L
Fidelity: exact -/
theorem no_sharp_fixed_point_half : ¬ ∃ x : ℝ, x = if x < 1 / 2 then 1 else 0 :=
  no_sharp_fixed_point (1 / 2) (by norm_num) (by norm_num)

/-- **`p = 𝟙(p = 0)` has no fixed point** (PDF 04 p. 5 footnote 3: "if `P` also updated on
observing itself, `φ := “Pₙ(φ) = 0”` … we won't find a fix-point").
Source: Soto PDF 04 p. 5 fn. 3 ([[bli-soto-a-inventory]] 036 (ii)); mandate X2 (i)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem no_zero_indicator_fixed_point : ¬ ∃ x : ℝ, x = if x = 0 then 1 else 0 := by
  rintro ⟨x, hx⟩
  split_ifs at hx with h
  · rw [h] at hx; norm_num at hx
  · exact h hx

/-! ## bli-soto-b-024: self-trust is not world-local -/

/-- Exact self-trust at one cell over a four-world table `(φ-truth, cell)`: the mass of `φ` inside
cell `c` is the cell's representative `a` times the cell's mass.
Source: Soto PDF 20 p. 1 ([[bli-soto-b-inventory]] 024)
Kind: D
Fidelity: exact (one cell, representative `a`) -/
def selfTrustAt (w : Bool × Bool → ℚ) (a : ℚ) (c : Bool) : Prop :=
  w (true, c) = a * (w (true, c) + w (false, c))

/-- A weighting satisfying exact self-trust with representatives `0.4` (cell `false`) and `0.8`
(cell `true`), full support.
Source: PDF 20 p. 1 (the `0.4`/`0.8` example)
Kind: D
Fidelity: n/a -/
def trustingWeights : Bool × Bool → ℚ
  | (true, false) => 1 / 5
  | (false, false) => 3 / 10
  | (true, true) => 2 / 5
  | (false, true) => 1 / 10

/-- The uniform weighting on the same four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def uniformWeights : Bool × Bool → ℚ := fun _ => 1 / 4

/-- **Self-trust is not world-local** (PDF 20 p. 1: "given `φ` is true, it's perfectly coherent
to have `Q_{k+n}(φ) = 0.4`, and also … `= 0.8` … a global property of `Q_k`, instead of a local
property of single possible worlds that we can remove from the betting table"). Two probability
weightings with the **same full support** on the four worlds `(φ, cell)`: `trustingWeights`
satisfies exact self-trust at both cells (`0.4`, `0.8`); `uniformWeights` violates it at the first.
So no deletion of worlds imposes the identity — it constrains the weights.
Source: Soto PDF 20 p. 1 ([[bli-soto-b-inventory]] 024); mandate § Placed here
Kind: P
Fidelity: exact (finite, two cells)
Hyps: (a) -/
theorem selfTrust_not_world_local :
    (∀ u, 0 < trustingWeights u) ∧ (∀ u, 0 < uniformWeights u) ∧
    (∑ u, trustingWeights u = 1) ∧ (∑ u, uniformWeights u = 1) ∧
    selfTrustAt trustingWeights (2 / 5) false ∧ selfTrustAt trustingWeights (4 / 5) true ∧
    ¬ selfTrustAt uniformWeights (2 / 5) false := by
  refine ⟨fun u => ?_, fun u => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases u with ⟨_ | _, _ | _⟩ <;> simp [trustingWeights]
  · simp [uniformWeights]
  · simp [Fintype.sum_prod_type, trustingWeights]; norm_num
  · simp [uniformWeights]
  · simp [selfTrustAt, trustingWeights]; norm_num
  · simp [selfTrustAt, trustingWeights]; norm_num
  · simp [selfTrustAt, uniformWeights]; norm_num

end Cleanroom.Bli.BliExactness
