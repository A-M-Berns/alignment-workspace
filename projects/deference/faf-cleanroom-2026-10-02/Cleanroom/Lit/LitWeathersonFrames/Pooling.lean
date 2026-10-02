import Cleanroom.Found.LitDdbFrames.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Weatherson §1 — the pooling theorems on finite carriers (T1, T2)

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). Gallow's theorem (no fixed
linear pooling of two totally-deferred-to experts) and Zhang's theorem (no strict-betweenness
pooling when the experts take finitely many values), both over a finite carrier `W` with a
weight vector `C : W → ℝ` (the novice), a target variable `Y : W → ℝ` (Weatherson's `p` is
`Y = ind p`), and two experts `A B : W → ℝ`.

Conventions (mandate): deference is the **unguarded product form**
`∀ a, ∑ w ∈ [A = a], C w · (Y w − a) = 0`. On a `C`-null level set every summand is `0`, so this
is exactly the standard "`C(p | A = a) = a` for all `a` with `C(A = a) > 0`"; the guarded ratio
form is a lemma (`defers_iff_cond`). "`C(A = B) < 1`" is `∃ w, 0 < C w ∧ A w ≠ B w`; the
conclusion of both theorems is its negation `∀ w, 0 < C w → A w = B w`.

Zhang's constraint 4 ("strictly between `a` and `b`") is unsatisfiable at `a = b` as printed;
three readings are formalized (`BetweenOpen`, `Between4`, `BetweenLiteral`), the open one is
refuted on `Fin 8` (`R8`), the closed one is the reading of record and is proved, and only its
*upper* half is used (`BetweenUpper`, `zhang_finite_upper`). Finiteness enters exactly once:
the disagreement set has a world of maximal expert value (`exists_max_image`).
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Level sets and the four constraints -/

/-- The level set `[A = a]` of an expert.
Source: [[Deference and Infinite Frames]] §1 l. 41 (`A(p) = a`)
Kind: D
Fidelity: exact -/
def lev (A : W → ℝ) (a : ℝ) : Finset W := univ.filter (fun w => A w = a)

/-- The joint level set `[A = a] ∩ [B = b]`.
Source: [[Deference and Infinite Frames]] §1 l. 47 (`A(p) = a ∧ B(p) = b`)
Kind: D
Fidelity: exact -/
def lev₂ (A B : W → ℝ) (a b : ℝ) : Finset W := univ.filter (fun w => A w = a ∧ B w = b)

/-- **Total deference** to an expert, product form: `∀ a, ∑ w ∈ [A = a], C w · (Y w − a) = 0`.
Unguarded: on a `C`-null level set every summand is `0`, so this is exactly the standard
"`C(Y | A = a) = a` for every attained `a` with `C(A = a) > 0`" (`defers_iff_cond`). With
`Y = ind p` it is Weatherson's constraint 1 (`C(p | A(p) = a) = a`); the general `Y` is the
"conditionally unbiased estimator" form the proofs actually use.
Source: [[Deference and Infinite Frames]] §1 l. 41 and constraints 1–2 (ll. 47–48, 56–57)
Kind: D
Fidelity: stronger: any target variable `Y`, not only an indicator -/
def Defers (C Y A : W → ℝ) : Prop := ∀ a, ∑ w ∈ lev A a, C w * (Y w - a) = 0

/-- **Gallow's constraint 4**: on every joint level set the posterior is the fixed linear mixture
`λ a + (1 − λ) b`, product form.
Source: [[Deference and Infinite Frames]] §1 l. 50 (constraint 4 of Gallow)
Kind: D
Fidelity: exact (product form) -/
def Pools (C Y A B : W → ℝ) (lam : ℝ) : Prop :=
  ∀ a b, ∑ w ∈ lev₂ A B a b, C w * (Y w - (lam * a + (1 - lam) * b)) = 0

/-- **Zhang's constraint 4, reading R-closed** (the reading of record): on every joint level set
the posterior `c` lies in the closed interval `[min a b, max a b]`, strictly inside when `a ≠ b`.
The posterior is existentially quantified with the product identity, so on a `C`-null cell the
clause is satisfiable (any `c` works) — exactly the guarded-ratio convention.
Source: [[Deference and Infinite Frames]] §1 l. 59 (constraint 4 of Zhang), read with the
agreement clause `C(p | A = a, B = a) = a` that the printed text lacks (finding F-T2)
Kind: D
Fidelity: variant: closed-interval reading; the printed "strictly between" is unsatisfiable at
`a = b` (see `BetweenLiteral`) -/
def Between4 (C Y A B : W → ℝ) : Prop :=
  ∀ a b, ∃ c, ∑ w ∈ lev₂ A B a b, C w * (Y w - c) = 0 ∧
    min a b ≤ c ∧ c ≤ max a b ∧ (a ≠ b → min a b < c ∧ c < max a b)

/-- **Only the upper half of R-closed**: the posterior is at most `max a b`, strictly less when
`a ≠ b`. This is all `zhang_finite_upper` uses; the lower half follows by `Y ↦ −Y`
(`Between4.upper`, `BetweenUpper.neg` route in the report).
Source: none: infrastructure (the strengthening of T2, finding F-T2b)
Kind: D
Fidelity: n/a -/
def BetweenUpper (C Y A B : W → ℝ) : Prop :=
  ∀ a b, ∃ c, ∑ w ∈ lev₂ A B a b, C w * (Y w - c) = 0 ∧
    c ≤ max a b ∧ (a ≠ b → c < max a b)

/-- **Zhang's constraint 4, reading R-open**: strict betweenness only when `a ≠ b`, nothing at
`a = b`. Refuted on `Fin 8` (`R8.refutes_open`).
Source: [[Deference and Infinite Frames]] §1 l. 59 (constraint 4 of Zhang), reading "for `a ≠ b`"
Kind: D
Fidelity: variant: open reading (refuted) -/
def BetweenOpen (C Y A B : W → ℝ) : Prop :=
  ∀ a b, a ≠ b → ∃ c, ∑ w ∈ lev₂ A B a b, C w * (Y w - c) = 0 ∧ min a b < c ∧ c < max a b

/-- **Zhang's constraint 4, reading R-literal**: strict betweenness on every *positive-mass*
joint level set, including `a = b`, where it is unsatisfiable — so it forces `C(A = B) = 0`
(`BetweenLiteral.agree_null`). The degenerate reading.
Source: [[Deference and Infinite Frames]] §1 l. 59 (constraint 4 of Zhang), read literally
Kind: D
Fidelity: variant: literal reading (degenerate) -/
def BetweenLiteral (C Y A B : W → ℝ) : Prop :=
  ∀ a b, 0 < mass C (lev₂ A B a b) →
    ∃ c, ∑ w ∈ lev₂ A B a b, C w * (Y w - c) = 0 ∧ min a b < c ∧ c < max a b

/-- The experts agree on the support of `C`: `∀ w, 0 < C w → A w = B w`, the negation of
Weatherson's constraint 3 "`C(A = B) < 1`" (`not_agreeAE_iff_mass_lt_one`).
Source: [[Deference and Infinite Frames]] §1 l. 49 (constraint 3, negated)
Kind: D
Fidelity: exact -/
def AgreeAE (C A B : W → ℝ) : Prop := ∀ w, 0 < C w → A w = B w

/-! ## Plumbing: level sets, fibers, the guarded ratio form -/

/-- Membership in a level set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_lev {A : W → ℝ} {a : ℝ} {w : W} : w ∈ lev A a ↔ A w = a := by
  simp [lev]

/-- Membership in a joint level set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_lev₂ {A B : W → ℝ} {a b : ℝ} {w : W} : w ∈ lev₂ A B a b ↔ A w = a ∧ B w = b := by
  simp [lev₂]

/-- The `B`-fiber of `[A = a]` is the joint level set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lev_filter_eq_lev₂ (A B : W → ℝ) (a b : ℝ) :
    (lev A a).filter (fun w => B w = b) = lev₂ A B a b := by
  ext w; simp [lev, lev₂]

/-- The `A`-fiber of `[B = b]` is the joint level set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lev_filter_eq_lev₂' (A B : W → ℝ) (a b : ℝ) :
    (lev B b).filter (fun w => A w = a) = lev₂ A B a b := by
  ext w; simp [lev, lev₂, and_comm]

/-- Joint level sets are symmetric in the two experts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lev₂_comm (A B : W → ℝ) (a b : ℝ) : lev₂ B A b a = lev₂ A B a b := by
  ext w; simp [lev₂, and_comm]

/-- Summing over the `B`-fibers of `[A = a]` recovers the sum over `[A = a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_lev₂_eq_sum_lev (A B : W → ℝ) (a : ℝ) (f : W → ℝ) :
    ∑ b ∈ univ.image B, ∑ w ∈ lev₂ A B a b, f w = ∑ w ∈ lev A a, f w := by
  rw [← sum_fiberwise_of_maps_to (s := lev A a) (t := univ.image B) (g := B)
    (fun w _ => mem_image_of_mem B (mem_univ w))]
  exact sum_congr rfl fun b _ => by rw [lev_filter_eq_lev₂]

/-- Summing over the `A`-fibers of `[B = b]` recovers the sum over `[B = b]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_lev₂_eq_sum_lev' (A B : W → ℝ) (b : ℝ) (f : W → ℝ) :
    ∑ a ∈ univ.image A, ∑ w ∈ lev₂ A B a b, f w = ∑ w ∈ lev B b, f w := by
  rw [← sum_fiberwise_of_maps_to (s := lev B b) (t := univ.image A) (g := A)
    (fun w _ => mem_image_of_mem A (mem_univ w))]
  exact sum_congr rfl fun a _ => by rw [lev_filter_eq_lev₂']

/-- Summing over the level sets of `A` recovers the sum over `W`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_lev_eq_sum_univ (A : W → ℝ) (f : W → ℝ) :
    ∑ a ∈ univ.image A, ∑ w ∈ lev A a, f w = ∑ w, f w := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image A) (g := A)
    (fun w _ => mem_image_of_mem A (mem_univ w))]
  rfl

/-- The unguarded product form is the guarded ratio form: `Defers C Y A` iff on every level set
of positive mass the `C`-average of `Y` is `a`.
Source: [[Deference and Infinite Frames]] §1 l. 41; mandate T1 ("say so")
Kind: L
Fidelity: exact -/
theorem defers_iff_cond {C Y A : W → ℝ} (hC : ∀ w, 0 ≤ C w) :
    Defers C Y A ↔ ∀ a, 0 < mass C (lev A a) →
      (∑ w ∈ lev A a, C w * Y w) / mass C (lev A a) = a := by
  have key : ∀ a, ∑ w ∈ lev A a, C w * (Y w - a) =
      (∑ w ∈ lev A a, C w * Y w) - a * mass C (lev A a) := by
    intro a; simp [mul_sub, sum_sub_distrib, mass, mul_sum, mul_comm]
  constructor
  · intro h a hpos
    rw [div_eq_iff hpos.ne']
    have := h a; rw [key] at this; linarith
  · intro h a
    rw [key]
    rcases (mass_nonneg hC (lev A a)).lt_or_eq with hpos | hzero
    · have := h a hpos; rw [div_eq_iff hpos.ne'] at this; linarith
    · have hz : ∀ w ∈ lev A a, C w = 0 := fun w hw => eq_zero_of_mass_eq_zero hC hzero.symm hw
      rw [← hzero, mul_zero, sub_zero]
      exact sum_eq_zero fun w hw => by rw [hz w hw, zero_mul]

/-- "`C(A = B) < 1`" (Weatherson's constraint 3) is the failure of `AgreeAE`, for a distribution.
Source: [[Deference and Infinite Frames]] §1 l. 49
Kind: L
Fidelity: exact -/
theorem not_agreeAE_iff_mass_lt_one {C A B : W → ℝ} (hC : C ∈ stdSimplex ℝ W) :
    ¬ AgreeAE C A B ↔ mass C (univ.filter (fun w => A w = B w)) < 1 := by
  constructor
  · intro h
    simp only [AgreeAE, not_forall] at h
    obtain ⟨w, hw, hne⟩ := h
    have hsub : mass C (univ.filter fun w => A w = B w) + C w ≤ 1 := by
      have := mass_le_one hC (insert w (univ.filter fun w => A w = B w))
      rw [mass, sum_insert (by simp [hne])] at this
      unfold mass; linarith
    linarith
  · intro h hagree
    have : mass C (univ.filter fun w => A w = B w) = 1 := by
      rw [← mass_univ hC]
      unfold mass
      rw [← sum_subset (subset_univ _)]
      intro w _ hw
      simp only [mem_filter, mem_univ, true_and] at hw
      rcases (hC.1 w).lt_or_eq with hpos | hz
      · exact absurd (hagree w hpos) hw
      · exact hz.symm
    linarith

/-! ## T1. Gallow's theorem (direct proof) -/

/-- The one-sided step of Gallow's proof: if `C` defers to `A` and on every level set of `A` the
`C`-average of `Y` is the mixture `λ A + (1 − λ) B` with `λ ≠ 1`, then
`∑ w, C w · A w · (A w − B w) = 0`.
Source: [[Deference and Infinite Frames]] §1 ll. 45–52 (the mandate's proof of record)
Kind: L
Fidelity: n/a -/
theorem gallow_step {C Y A B : W → ℝ} {lam : ℝ} (hA : Defers C Y A)
    (hmix : ∀ a, ∑ w ∈ lev A a, C w * (Y w - (lam * A w + (1 - lam) * B w)) = 0)
    (h1 : lam ≠ 1) : ∑ w, C w * A w * (A w - B w) = 0 := by
  have hlev : ∀ a, ∑ w ∈ lev A a, C w * (B w - A w) = 0 := by
    intro a
    have e1 := hA a
    have e2 := hmix a
    have : ∑ w ∈ lev A a, C w * (Y w - a) - ∑ w ∈ lev A a, C w * (Y w - (lam * A w + (1 - lam) * B w))
        = (1 - lam) * ∑ w ∈ lev A a, C w * (B w - A w) := by
      rw [← sum_sub_distrib, mul_sum]
      refine sum_congr rfl fun w hw => ?_
      rw [mem_lev] at hw
      rw [hw]; ring
    rw [e1, e2, sub_zero] at this
    have h1' : (1 - lam) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    exact (mul_eq_zero.mp this.symm).resolve_left h1'
  rw [← sum_lev_eq_sum_univ A]
  refine sum_eq_zero fun a _ => ?_
  have : ∑ w ∈ lev A a, C w * A w * (A w - B w) = -(a * ∑ w ∈ lev A a, C w * (B w - A w)) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun w hw => ?_
    rw [mem_lev] at hw
    rw [hw]; ring
  rw [this, hlev a, mul_zero, neg_zero]

/-- From `Pools` (constraint 4 on joint level sets), the mixture identity on each level set of
`A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pools.lev_A {C Y A B : W → ℝ} {lam : ℝ} (h4 : Pools C Y A B lam) (a : ℝ) :
    ∑ w ∈ lev A a, C w * (Y w - (lam * A w + (1 - lam) * B w)) = 0 := by
  rw [← sum_lev₂_eq_sum_lev A B a]
  refine sum_eq_zero fun b _ => ?_
  rw [← h4 a b]
  refine sum_congr rfl fun w hw => ?_
  rw [mem_lev₂] at hw
  rw [hw.1, hw.2]

/-- From `Pools`, the mixture identity on each level set of `B`, with the roles swapped.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pools.lev_B {C Y A B : W → ℝ} {lam : ℝ} (h4 : Pools C Y A B lam) (b : ℝ) :
    ∑ w ∈ lev B b, C w * (Y w - ((1 - lam) * B w + (1 - (1 - lam)) * A w)) = 0 := by
  rw [← sum_lev₂_eq_sum_lev' A B b]
  refine sum_eq_zero fun a _ => ?_
  rw [← h4 a b]
  refine sum_congr rfl fun w hw => ?_
  rw [mem_lev₂] at hw
  rw [hw.1, hw.2]; ring_nf

/-- **T1. Gallow's theorem, finite carrier, general target.** If `C ≥ 0` defers to `A` and to
`B` (product form) and on every joint level set the posterior of `Y` is the fixed mixture
`λ a + (1 − λ) b` with `λ ∉ {0, 1}`, then `A = B` on the support of `C`. Proof of record: the
two one-sided identities `∑ C A (A − B) = 0` and `∑ C B (B − A) = 0` add to
`∑ C (A − B)² = 0`. Findings: `λ ∈ (0,1)` is used only as `λ ∉ {0,1}`; `[0,1]`-valuedness of
`A, B` is not used; `Y` need not be an indicator; `C` need not sum to one.
Source: [[Deference and Infinite Frames]] §1 ll. 45–52 (Gallow 2018); inventory 021
Kind: P
Fidelity: stronger: any `λ ∉ {0,1}`, any real target `Y`, any nonnegative weight `C`
Hyps: (a) all — `hC`, the two deference constraints and the pooling constraint are the
theorem's own hypotheses in product form; nothing cited -/
theorem gallow_finite {C Y A B : W → ℝ} {lam : ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : Pools C Y A B lam)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) : AgreeAE C A B := by
  have eA := gallow_step hA h4.lev_A h1
  have eB := gallow_step hB h4.lev_B (by intro h; apply h0; linarith)
  have hsq : ∑ w, C w * (A w - B w) ^ 2 = 0 := by
    have : ∑ w, C w * (A w - B w) ^ 2 =
        ∑ w, C w * A w * (A w - B w) + ∑ w, C w * B w * (B w - A w) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun w _ => by ring
    rw [this, eA, eB, add_zero]
  intro w hw
  have hterm := (sum_eq_zero_iff_of_nonneg (fun v _ => mul_nonneg (hC v) (sq_nonneg _))).1 hsq w
    (mem_univ w)
  have : (A w - B w) ^ 2 = 0 := (mul_eq_zero.mp hterm).resolve_left hw.ne'
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/-- **T1, contrapositive form**: the four constraints of Gallow (deference to `A`, to `B`, fixed
linear pooling, `C(A = B) < 1`) are jointly contradictory.
Source: [[Deference and Infinite Frames]] §1 ll. 45–52
Kind: L
Fidelity: exact -/
theorem gallow_finite_contra {C Y A B : W → ℝ} {lam : ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : Pools C Y A B lam)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) (h3 : ¬ AgreeAE C A B) : False :=
  h3 (gallow_finite hC hA hB h4 h0 h1)

/-- **T1, event form**: Gallow's theorem for `Y = ind p` (the paper's statement).
Source: [[Deference and Infinite Frames]] §1 ll. 47–50
Kind: L
Fidelity: exact -/
theorem gallow_finite_event {C A B : W → ℝ} {p : Finset W} {lam : ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C (ind p) A) (hB : Defers C (ind p) B) (h4 : Pools C (ind p) A B lam)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) : AgreeAE C A B :=
  gallow_finite hC hA hB h4 h0 h1

/-! ## T2. Zhang's theorem (extremal proof, upper half only) -/

/-- R-closed implies its upper half.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Between4.upper {C Y A B : W → ℝ} (h : Between4 C Y A B) : BetweenUpper C Y A B := by
  intro a b
  obtain ⟨c, hc, -, hle, hlt⟩ := h a b
  exact ⟨c, hc, hle, fun hab => (hlt hab).2⟩

/-- The upper half is symmetric in the two experts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem BetweenUpper.symm {C Y A B : W → ℝ} (h : BetweenUpper C Y A B) :
    BetweenUpper C Y B A := by
  intro b a
  obtain ⟨c, hc, hle, hlt⟩ := h a b
  refine ⟨c, ?_, by rwa [max_comm], fun hne => by rw [max_comm]; exact hlt (Ne.symm hne)⟩
  rwa [lev₂_comm]

/-- The contribution of a joint cell to the deference sum at threshold `M` is
`(c − M) · C(cell)` when the cell's posterior is `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cell_sum_shift {C Y A B : W → ℝ} {a b c M : ℝ}
    (hc : ∑ w ∈ lev₂ A B a b, C w * (Y w - c) = 0) :
    ∑ w ∈ lev₂ A B a b, C w * (Y w - M) = (c - M) * mass C (lev₂ A B a b) := by
  have : ∑ w ∈ lev₂ A B a b, C w * (Y w - M) =
      ∑ w ∈ lev₂ A B a b, C w * (Y w - c) + ∑ w ∈ lev₂ A B a b, C w * (c - M) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun w _ => by ring
  rw [this, hc, zero_add, mass, mul_sum]
  exact sum_congr rfl fun w _ => by ring

/-- **The extremal step of Zhang's proof.** If `C ≥ 0` defers to `A`, the upper half of
constraint 4 holds, and `M` bounds `max (A w) (B w)` over every supported disagreeing world,
then no supported world has `A w = M` and `B w ≠ M`. (Proof: split `[A = M]` into `B`-cells;
each contributes `(c − M) · C(cell) ≤ 0`, and a cell with a supported disagreeing world
contributes `< 0`, contradicting the deference identity `∑_{[A = M]} C (Y − M) = 0`.)
Source: [[Deference and Infinite Frames]] §1 l. 88 (the paper's one-sentence gloss, made a proof)
Kind: L
Fidelity: n/a -/
theorem no_top_disagreement {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hA : Defers C Y A)
    (h4 : BetweenUpper C Y A B) (M : ℝ)
    (hM : ∀ w, 0 < C w → A w ≠ B w → max (A w) (B w) ≤ M) :
    ∀ w, 0 < C w → A w = M → A w = B w := by
  intro w₀ hw₀ hA₀
  by_contra hne
  have hdef := hA M
  rw [← sum_lev₂_eq_sum_lev A B M] at hdef
  -- every cell contributes ≤ 0
  have hcell : ∀ b, ∑ w ∈ lev₂ A B M b, C w * (Y w - M) ≤ 0 := by
    intro b
    obtain ⟨c, hc, hle, hlt⟩ := h4 M b
    rw [cell_sum_shift hc]
    rcases (mass_nonneg hC (lev₂ A B M b)).lt_or_eq with hpos | hzero
    · -- a supported world in the cell bounds b
      obtain ⟨w, hw, hCw⟩ : ∃ w ∈ lev₂ A B M b, 0 < C w := by
        by_contra hall
        push Not at hall
        have : mass C (lev₂ A B M b) = 0 :=
          sum_eq_zero fun w hw => le_antisymm (hall w hw) (hC w)
        linarith
      rw [mem_lev₂] at hw
      have hbM : b ≤ M := by
        by_cases hab : A w = B w
        · rw [← hw.2, ← hab, hw.1]
        · have := hM w hCw hab
          rw [hw.1, hw.2] at this
          exact le_trans (le_max_right _ _) this
      have : c ≤ M := by
        have := hle; rwa [max_eq_left hbM] at this
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    · rw [← hzero, mul_zero]
  -- the cell of w₀ contributes < 0
  have hneg : ∑ w ∈ lev₂ A B M (B w₀), C w * (Y w - M) < 0 := by
    obtain ⟨c, hc, hle, hlt⟩ := h4 M (B w₀)
    rw [cell_sum_shift hc]
    have hb : B w₀ < M := by
      have := hM w₀ hw₀ hne
      rw [hA₀] at this
      exact lt_of_le_of_ne (le_trans (le_max_right _ _) this) (fun h => hne (by rw [hA₀, h]))
    have hcM : c < M := by
      have := hlt hb.ne'
      rwa [max_eq_left hb.le] at this
    have hpos : 0 < mass C (lev₂ A B M (B w₀)) :=
      mass_pos_of_mem hC (mem_lev₂.mpr ⟨hA₀, rfl⟩) hw₀
    exact mul_neg_of_neg_of_pos (by linarith) hpos
  have hzero := (sum_eq_zero_iff_of_nonpos (fun b _ => hcell b)).1 hdef (B w₀)
    (mem_image_of_mem B (mem_univ w₀))
  linarith

/-- **T2 (load-bearing 1). Zhang's theorem on a finite carrier, upper half.** If `C ≥ 0`
defers to `A` and to `B` (product form) and on every joint level set the posterior of `Y` is
at most `max a b`, strictly less when `a ≠ b`, then `A = B` on the support of `C`. Proof of
record (replacing the paper's one-sentence gloss): among the supported worlds where the
experts disagree take one maximizing `max (A w) (B w)`; the expert attaining the maximum
`M` there is contradicted by `no_top_disagreement`. **Finiteness enters exactly once**: the
disagreement set has a world of maximal expert value (`Finset.exists_max_image`); on a
countable carrier with values accumulating this fails, and E1 (`PoolingCountable.lean`)
exploits exactly that. Only the *upper* half of constraint 4 is used (finding F-T2b).
Source: [[Deference and Infinite Frames]] §1 ll. 54–61, l. 88 (Zhang, forthcoming); inventory
022
Kind: P
Fidelity: stronger: only the upper half of constraint 4, any real target `Y`, any nonnegative
weight `C`; the finite-range constraint 5 is the finiteness of `W`
Hyps: (a) all — `hC`, the two deference constraints and the betweenness constraint are the
theorem's own hypotheses in product form; nothing cited -/
theorem zhang_finite_upper {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : BetweenUpper C Y A B) : AgreeAE C A B := by
  by_contra hnot
  simp only [AgreeAE, not_forall] at hnot
  obtain ⟨w₁, hw₁, hne₁⟩ := hnot
  set T : Finset W := univ.filter (fun w => 0 < C w ∧ A w ≠ B w) with hT
  have hTne : T.Nonempty := ⟨w₁, by simp [hT, hw₁, hne₁]⟩
  obtain ⟨w₀, hw₀T, hmax⟩ := exists_max_image T (fun w => max (A w) (B w)) hTne
  simp only [hT, mem_filter, mem_univ, true_and] at hw₀T
  set M := max (A w₀) (B w₀) with hMdef
  have hM : ∀ w, 0 < C w → A w ≠ B w → max (A w) (B w) ≤ M :=
    fun w hw hne => hmax w (by simp [hT, hw, hne])
  have hM' : ∀ w, 0 < C w → B w ≠ A w → max (B w) (A w) ≤ M :=
    fun w hw hne => by rw [max_comm]; exact hM w hw (Ne.symm hne)
  rcases le_total (B w₀) (A w₀) with hle | hle
  · have hA₀ : A w₀ = M := by rw [hMdef, max_eq_left hle]
    exact hw₀T.2 (no_top_disagreement hC hA h4 M hM w₀ hw₀T.1 hA₀)
  · have hB₀ : B w₀ = M := by rw [hMdef, max_eq_right hle]
    exact hw₀T.2 (no_top_disagreement hC hB h4.symm M hM' w₀ hw₀T.1 hB₀).symm

/-- **T2. Zhang's theorem, reading R-closed** (the reading of record): deference to `A` and to
`B`, and posteriors in `[min a b, max a b]` (strictly inside when `a ≠ b`), force `A = B` on
the support of `C`. Corollary of the upper-half theorem.
Source: [[Deference and Infinite Frames]] §1 ll. 54–61 (Zhang, forthcoming); inventory 022
Kind: L
Fidelity: variant: closed-interval reading (the printed constraint 4 is unsatisfiable at `a = b`)
Hyps: (a) all, as in `zhang_finite_upper` -/
theorem zhang_finite {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : Between4 C Y A B) : AgreeAE C A B :=
  zhang_finite_upper hC hA hB h4.upper

/-- **T2, contrapositive form**: Zhang's five constraints (with 4 read R-closed and 5 as the
finiteness of `W`) are jointly contradictory.
Source: [[Deference and Infinite Frames]] §1 ll. 54–61
Kind: L
Fidelity: variant: closed-interval reading -/
theorem zhang_finite_contra {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : Between4 C Y A B)
    (h3 : ¬ AgreeAE C A B) : False :=
  h3 (zhang_finite hC hA hB h4)

/-- A fixed linear mixture with `0 < λ < 1` satisfies R-closed: `λ a + (1 − λ) b` lies in
`[min a b, max a b]`, strictly inside when `a ≠ b`, and equals `a` when `a = b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pools.between4 {C Y A B : W → ℝ} {lam : ℝ} (h4 : Pools C Y A B lam)
    (h0 : 0 < lam) (h1 : lam < 1) : Between4 C Y A B := by
  intro a b
  refine ⟨lam * a + (1 - lam) * b, h4 a b, ?_, ?_, ?_⟩
  · rcases le_total a b with hab | hab
    · rw [min_eq_left hab]; nlinarith
    · rw [min_eq_right hab]; nlinarith
  · rcases le_total a b with hab | hab
    · rw [max_eq_right hab]; nlinarith
    · rw [max_eq_left hab]; nlinarith
  · intro hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · rw [min_eq_left hab.le, max_eq_right hab.le]; constructor <;> nlinarith
    · rw [min_eq_right hab.le, max_eq_left hab.le]; constructor <;> nlinarith

/-- **Gallow as a corollary of Zhang** (second proof of T1, for `0 < λ < 1` — the direct proof
`gallow_finite` needs only `λ ∉ {0,1}`). The ledger row of record for T1 is `gallow_finite`.
Source: [[Deference and Infinite Frames]] §1 l. 54 ("considerably generalises Gallow's result")
Kind: C
Fidelity: exact (Gallow's `λ ∈ (0,1)`)
Hyps: (a) all -/
theorem gallow_finite_of_zhang {C Y A B : W → ℝ} {lam : ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : Pools C Y A B lam)
    (h0 : 0 < lam) (h1 : lam < 1) : AgreeAE C A B :=
  zhang_finite hC hA hB (h4.between4 h0 h1)

/-- **R-literal is degenerate**: strict betweenness on every positive-mass cell, including
`a = b`, forces every agreement cell `[A = a] ∩ [B = a]` to be `C`-null.
Source: [[Deference and Infinite Frames]] §1 l. 59, read literally (mandate T2, R-literal)
Kind: L
Fidelity: variant: literal reading -/
theorem BetweenLiteral.agree_null {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w)
    (h4 : BetweenLiteral C Y A B) (a : ℝ) : mass C (lev₂ A B a a) = 0 := by
  rcases (mass_nonneg hC (lev₂ A B a a)).lt_or_eq with hpos | hzero
  · obtain ⟨c, -, hlt, hlt'⟩ := h4 a a hpos
    simp only [min_self, max_self] at hlt hlt'
    exact absurd (lt_trans hlt hlt') (lt_irrefl _)
  · exact hzero.symm

/-- **R-literal with deference is contradictory** for a weight of positive total mass: the
literal reading forces `C(A = B) = 0`, while its upper half (a special case of R-closed's) forces
`A = B` on the support, so the support is empty. Degenerate reading, recorded for completeness.
Source: [[Deference and Infinite Frames]] §1 ll. 54–61, constraint 4 read literally
Kind: L
Fidelity: variant: literal reading (degenerate) -/
theorem zhang_literal_degenerate {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w)
    (hA : Defers C Y A) (hB : Defers C Y B) (h4 : BetweenLiteral C Y A B)
    (hpos : 0 < ∑ w, C w) : False := by
  have hup : BetweenUpper C Y A B := by
    intro a b
    rcases (mass_nonneg hC (lev₂ A B a b)).lt_or_eq with hm | hm
    · obtain ⟨c, hc, -, hlt⟩ := h4 a b hm
      exact ⟨c, hc, hlt.le, fun _ => hlt⟩
    · refine ⟨min a b, ?_, min_le_max, fun hne => min_lt_max.mpr hne⟩
      exact sum_eq_zero fun w hw => by rw [eq_zero_of_mass_eq_zero hC hm.symm hw, zero_mul]
  have hagree := zhang_finite_upper hC hA hB hup
  have hzero : ∀ w, C w = 0 := by
    intro w
    rcases (hC w).lt_or_eq with hw | hw
    · exfalso
      have hmem : w ∈ lev₂ A B (A w) (A w) := mem_lev₂.mpr ⟨rfl, (hagree w hw).symm⟩
      have := mass_pos_of_mem hC hmem hw
      rw [h4.agree_null hC (A w)] at this
      exact lt_irrefl _ this
    · exact hw.symm
  have : ∑ w, C w = 0 := sum_eq_zero fun w _ => hzero w
  linarith

end

end Cleanroom.Lit.LitWeathersonFrames
