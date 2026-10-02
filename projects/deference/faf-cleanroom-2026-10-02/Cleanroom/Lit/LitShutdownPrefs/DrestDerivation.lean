import Cleanroom.Lit.LitShutdownPrefs.Drest
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The DReST meta-return closed form, derived from the enumerated meta-episode (Target 13, first part)

`Drest.F n lam mu p ρ = ∑_{i<n} mu^i ∑_l p l ρ l (1 − (1−lam) p l)^i` was a **(c)** for the expected
return of the enumerated meta-episode (report, Target 13; audit round 1, fidelity B2 / adversarial
B3). This file derives it, converting the (c) to (a):

* `countBefore seq i` — DReST's `N_{e_i}(l)`: the number of earlier mini-episodes `j < i` with the
  same length as mini-episode `i`.
* `seqReturn lam mu ρ i₀ c seq` — the return of a length sequence `seq : Fin n → Fin k`, mini-episode
  `i` contributing `mu^{i₀+i} · ρ (seq i) · lam^{c (seq i) + countBefore seq i}` (initial index `i₀`
  and initial counts `c` make the induction go through; the meta-episode is `i₀ = 0`, `c = 0`).
* `seqProb p seq = ∏_j p (seq j)` — i.i.d. lengths.
* `metaReturn n lam mu p ρ = ∑_{seq} seqProb p seq · seqReturn lam mu ρ 0 0 seq` — **the enumerated
  expected return** (Def D.2 with the mini-episode reward's expectation `ρ l` given its length).
* `R lam mu p ρ n i₀ c` — the backward recursion (expectation over the next length, then recurse
  with the count of that length incremented).
* `metaReturn_eq_R` — enumeration equals recursion (peel the first mini-episode: `Fin.consEquiv`).
* `R_eq_closed` — the recursion has the closed form `∑_{t<n} mu^{i₀+t} ∑_a p a ρ a lam^{c a}
  (1 − (1−lam) p a)^t`; the step is `∑_a p a · lam^{[a = b]} = 1 − (1−lam) p b`
  (`sum_p_lam_ite`), the one-step binomial factor.
* **`F_eq_metaReturn`** — `F = metaReturn` on the simplex: the closed form is what DReST's own
  definition yields under i.i.d. lengths. Both refutation headlines (`lemma_D2_false`,
  `theorem_5_1_neutrality_false`) therefore refute the theorem for the enumerated return itself,
  not only for the closed form.

What remains (c): the `(p, ρ)` model — the length distribution `p` and the coin fraction `ρ l`
given the length treated as the policy's independently controllable data (Def D.3/D.4 as read in
`Drest.lean`).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Drest

open Finset

variable {k : ℕ}

/-- `N_{e_i}(l)`: the number of earlier mini-episodes (`j < i`) with the same length as `i`.
Source: DReST Def D.2 (l. 366): "`N_{e_i}(l)` … the number of previous mini-episodes in the
meta-episode with length `l`"
Kind: D
Fidelity: exact -/
def countBefore {n : ℕ} (seq : Fin n → Fin k) (i : Fin n) : ℕ :=
  ∑ j : Fin n, if j < i ∧ seq j = seq i then 1 else 0

/-- The return of a length sequence: mini-episode `i` contributes `mu^{i₀+i} · ρ (seq i) ·
lam^{c (seq i) + N_{e_i}}`, with initial index `i₀` and initial counts `c` (both `0` for the
meta-episode).
Source: DReST Def D.2 (l. 366), eq. (1) (l. 376), with `mu = lam^{−1/k}` and the mini-episode
reward's expectation given its length written `ρ l`
Kind: D
Fidelity: exact (in the `(p, ρ)` model) -/
noncomputable def seqReturn (lam mu : ℝ) (ρ : Fin k → ℝ) (i₀ : ℕ) (c : Fin k → ℕ) {n : ℕ}
    (seq : Fin n → Fin k) : ℝ :=
  ∑ i : Fin n, mu ^ (i₀ + i.1) * ρ (seq i) * lam ^ (c (seq i) + countBefore seq i)

/-- The probability of a length sequence under i.i.d. lengths drawn from `p`.
Source: DReST App. D (the agent cannot distinguish mini-episodes, so lengths are i.i.d.)
Kind: D
Fidelity: exact -/
def seqProb (p : Fin k → ℝ) {n : ℕ} (seq : Fin n → Fin k) : ℝ := ∏ j, p (seq j)

/-- **The enumerated expected return** of an `n`-mini-episode meta-episode: the sum over all `k^n`
length sequences of probability × return.
Source: DReST Def D.2 (l. 366) / Thm D.1 (l. 354) ("expected return in `E`")
Kind: D
Fidelity: exact (in the `(p, ρ)` model) -/
noncomputable def metaReturn (n : ℕ) (lam mu : ℝ) (p ρ : Fin k → ℝ) : ℝ :=
  ∑ seq : Fin n → Fin k, seqProb p seq * seqReturn lam mu ρ 0 (fun _ => 0) seq

/-- The backward recursion: draw the next length `a`, collect `mu^{i₀} ρ a lam^{c a}`, recurse with
`c a` incremented.
Source: none: infrastructure (the induction scheme of the derivation)
Kind: D -/
noncomputable def R (lam mu : ℝ) (p ρ : Fin k → ℝ) : ℕ → ℕ → (Fin k → ℕ) → ℝ
  | 0, _, _ => 0
  | n + 1, i₀, c => ∑ a, p a * (mu ^ i₀ * ρ a * lam ^ (c a) +
      R lam mu p ρ n (i₀ + 1) (fun b => c b + if a = b then 1 else 0))

/-- The first mini-episode has no predecessors.
Source: none: infrastructure
Kind: L -/
theorem countBefore_cons_zero {n : ℕ} (a : Fin k) (rest : Fin n → Fin k) :
    countBefore (Fin.cons a rest) 0 = 0 := by
  unfold countBefore
  exact Finset.sum_eq_zero fun j _ => by simp

/-- The count for a later mini-episode: whether the first has the same length, plus the count in
the tail.
Source: none: infrastructure
Kind: L -/
theorem countBefore_cons_succ {n : ℕ} (a : Fin k) (rest : Fin n → Fin k) (i : Fin n) :
    countBefore (Fin.cons a rest) i.succ = (if a = rest i then 1 else 0) + countBefore rest i := by
  unfold countBefore
  rw [Fin.sum_univ_succ]
  congr 1
  · simp [Fin.succ_pos]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [Fin.succ_lt_succ_iff]

/-- Peeling the first mini-episode off the return.
Source: none: infrastructure
Kind: L -/
theorem seqReturn_cons (lam mu : ℝ) (ρ : Fin k → ℝ) (i₀ : ℕ) (c : Fin k → ℕ) {n : ℕ} (a : Fin k)
    (rest : Fin n → Fin k) :
    seqReturn lam mu ρ i₀ c (Fin.cons a rest) =
      mu ^ i₀ * ρ a * lam ^ (c a) +
        seqReturn lam mu ρ (i₀ + 1) (fun b => c b + if a = b then 1 else 0) rest := by
  unfold seqReturn
  rw [Fin.sum_univ_succ]
  congr 1
  · simp [countBefore_cons_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.cons_succ, countBefore_cons_succ, Fin.val_succ]
    rw [show i₀ + (i.1 + 1) = i₀ + 1 + i.1 by omega, ← Nat.add_assoc]

/-- Peeling the first length off the probability.
Source: none: infrastructure
Kind: L -/
theorem seqProb_cons (p : Fin k → ℝ) {n : ℕ} (a : Fin k) (rest : Fin n → Fin k) :
    seqProb p (Fin.cons a rest) = p a * seqProb p rest := by
  unfold seqProb
  rw [Fin.prod_univ_succ]
  simp

/-- The probabilities of all length sequences sum to one.
Source: none: infrastructure
Kind: L -/
theorem sum_seqProb (p : Fin k → ℝ) (hp : ∑ a, p a = 1) (n : ℕ) :
    ∑ seq : Fin n → Fin k, seqProb p seq = 1 := by
  unfold seqProb
  rw [← Fintype.prod_sum (fun _ a => p a)]
  simp [hp]

/-- A sum over `(n+1)`-sequences is a sum over the first length and the tail.
Source: none: infrastructure
Kind: L -/
theorem sum_fin_succ_pi {n : ℕ} (g : (Fin (n + 1) → Fin k) → ℝ) :
    ∑ seq : Fin (n + 1) → Fin k, g seq = ∑ a : Fin k, ∑ rest : Fin n → Fin k, g (Fin.cons a rest) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin k)]
  intro x; rfl

/-- **Enumeration equals recursion**: the enumerated expected return with initial data `(i₀, c)`
is the backward recursion `R`.
Source: none: infrastructure (tower property, by induction on the number of mini-episodes)
Kind: P
Fidelity: exact
Hyps: (a) `∑ p = 1` -/
theorem sum_seqProb_seqReturn (lam mu : ℝ) (p ρ : Fin k → ℝ) (hp : ∑ a, p a = 1) :
    ∀ (n i₀ : ℕ) (c : Fin k → ℕ),
      ∑ seq : Fin n → Fin k, seqProb p seq * seqReturn lam mu ρ i₀ c seq = R lam mu p ρ n i₀ c := by
  intro n
  induction n with
  | zero => intro i₀ c; simp [seqReturn, R]
  | succ n ih =>
    intro i₀ c
    rw [sum_fin_succ_pi, R]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [seqProb_cons, seqReturn_cons]
    rw [← ih (i₀ + 1) (fun b => c b + if a = b then 1 else 0)]
    have hone := sum_seqProb p hp n
    have key : p a * (mu ^ i₀ * ρ a * lam ^ c a +
          ∑ seq : Fin n → Fin k, seqProb p seq *
            seqReturn lam mu ρ (i₀ + 1) (fun b => c b + if a = b then 1 else 0) seq) =
        p a * (mu ^ i₀ * ρ a * lam ^ c a * ∑ seq : Fin n → Fin k, seqProb p seq +
          ∑ seq : Fin n → Fin k, seqProb p seq *
            seqReturn lam mu ρ (i₀ + 1) (fun b => c b + if a = b then 1 else 0) seq) := by
      rw [hone, mul_one]
    rw [key]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun rest _ => ?_
    ring

/-- The one-step binomial factor: `∑_a p a · lam^{[a = b]} = 1 − (1 − lam) p b`.
Source: none: infrastructure (`E[lam^{Bernoulli(p b)}]`)
Kind: L -/
theorem sum_p_lam_ite (lam : ℝ) (p : Fin k → ℝ) (hp : ∑ a, p a = 1) (b : Fin k) :
    ∑ a, p a * lam ^ (if a = b then 1 else 0) = 1 - (1 - lam) * p b := by
  have : ∀ a, p a * lam ^ (if a = b then 1 else 0) = p a + (if a = b then p b * (lam - 1) else 0) := by
    intro a
    split_ifs with h
    · subst h; ring
    · ring
  simp only [this, Finset.sum_add_distrib, hp, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **The recursion has the closed form** `∑_{t<n} mu^{i₀+t} ∑_a p a ρ a lam^{c a} (1 − (1−lam) p a)^t`.
Source: none: infrastructure (induction; the step is `sum_p_lam_ite`)
Kind: P
Fidelity: exact
Hyps: (a) `∑ p = 1` -/
theorem R_eq_closed (lam mu : ℝ) (p ρ : Fin k → ℝ) (hp : ∑ a, p a = 1) :
    ∀ (n i₀ : ℕ) (c : Fin k → ℕ),
      R lam mu p ρ n i₀ c =
        ∑ t ∈ range n, mu ^ (i₀ + t) * ∑ a, p a * ρ a * lam ^ (c a) * (1 - (1 - lam) * p a) ^ t := by
  intro n
  induction n with
  | zero => intro i₀ c; simp [R]
  | succ n ih =>
    intro i₀ c
    rw [R, Finset.sum_range_succ', add_comm (∑ t ∈ range n, _) _]
    simp only [ih, mul_add, Finset.sum_add_distrib]
    congr 1
    · -- the `t = 0` term
      rw [Finset.mul_sum]
      simp only [add_zero, pow_zero, mul_one]
      exact Finset.sum_congr rfl fun a _ => by ring
    · -- the recursive part: exchange the sums and absorb `∑_a p a lam^{[a = b]}`
      simp only [Finset.mul_sum]
      refine Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => ?_)
      refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => ?_)
      have h1 : ∀ a, p a * (mu ^ (i₀ + 1 + t) * (p b * ρ b * lam ^ (c b + if a = b then 1 else 0) *
          (1 - (1 - lam) * p b) ^ t)) =
          (mu ^ (i₀ + 1 + t) * (p b * ρ b * lam ^ (c b) * (1 - (1 - lam) * p b) ^ t)) *
            (p a * lam ^ (if a = b then 1 else 0)) := by
        intro a; rw [pow_add]; ring
      simp only [h1, ← Finset.mul_sum, sum_p_lam_ite lam p hp b]
      rw [show i₀ + 1 + t = i₀ + (t + 1) by omega]
      ring

/-- **The closed form is the enumerated expected return**: `F n lam mu p ρ = metaReturn n lam mu p ρ`
whenever `∑ p = 1`. This discharges the (c) on `F` in `lemma_D2_false` and
`theorem_5_1_neutrality_false`: DReST's own Def D.2, enumerated over all length sequences with
i.i.d. lengths, gives exactly `F`.
Source: DReST Def D.2 (l. 366), eq. (1) (l. 376); [[lit-shutdown-prefs-mandate]] Target 13
(first part); audit round 1, fidelity B2 / adversarial B3 (enumeration reproduced numerically
for `n ≤ 8`; here mechanized for every `n`)
Kind: P
Fidelity: exact (in the `(p, ρ)` model)
Hyps: (a) `∑ p = 1`; (c) the `(p, ρ)` model (independently controllable `p` and `ρ`) -/
theorem F_eq_metaReturn (n : ℕ) (lam mu : ℝ) (p ρ : Fin k → ℝ) (hp : ∑ a, p a = 1) :
    F n lam mu p ρ = metaReturn n lam mu p ρ := by
  unfold metaReturn
  rw [sum_seqProb_seqReturn lam mu p ρ hp n 0 (fun _ => 0), R_eq_closed lam mu p ρ hp n 0]
  unfold F
  simp

/-- `F` on the simplex is the enumerated return (the form the refutation headlines use).
Source: as `F_eq_metaReturn`
Kind: L -/
theorem F_eq_metaReturn_of_mem (n : ℕ) (lam mu : ℝ) (p ρ : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) :
    F n lam mu p ρ = metaReturn n lam mu p ρ :=
  F_eq_metaReturn n lam mu p ρ hp.2

/-- **Lemma D.2 refuted for the enumerated return**: at `n = 8`, `lam = 1/4`, `mu = 2`, `ρ ≡ 1`,
the enumerated expected return of `(1/4, 3/4)` exceeds that of `(1/2, 1/2)` by `13191189/4194304`.
The (c) on the closed form is discharged.
Source: DReST Lemma D.2 (l. 386); `lemma_D2_false` with `F_eq_metaReturn`
Kind: C
Fidelity: exact (in the `(p, ρ)` model)
Hyps: (a) all; (c) the `(p, ρ)` model -/
theorem lemma_D2_false_enumerated :
    metaReturn 8 (1/4) 2 ![1/2, 1/2] (fun _ => 1) < metaReturn 8 (1/4) 2 ![1/4, 3/4] (fun _ => 1) := by
  rw [← F_eq_metaReturn _ _ _ _ _ (by norm_num [Fin.sum_univ_two]),
    ← F_eq_metaReturn _ _ _ _ _ (by norm_num [Fin.sum_univ_two])]
  exact lemma_D2_false

/-- **Theorem 5.1's neutrality clause refuted for the enumerated return**: a maximiser of the
enumerated expected return over the simplex exists, and none is uniform.
Source: DReST Thm 5.1 (l. 106) / Thm D.1 (l. 356); `theorem_5_1_neutrality_false` with
`F_eq_metaReturn_of_mem`
Kind: C
Fidelity: exact (of the theorem's neutrality clause, in the `(p, ρ)` model)
Hyps: (a) all; (c) the `(p, ρ)` model -/
theorem theorem_5_1_neutrality_false_enumerated :
    (∃ p ∈ stdSimplex ℝ (Fin 2),
        IsMaxOn (fun q : Fin 2 → ℝ => metaReturn 8 (1/4) 2 q (fun _ => 1)) (stdSimplex ℝ (Fin 2)) p) ∧
      ∀ p ∈ stdSimplex ℝ (Fin 2),
        IsMaxOn (fun q : Fin 2 → ℝ => metaReturn 8 (1/4) 2 q (fun _ => 1)) (stdSimplex ℝ (Fin 2)) p →
          ¬ MaxNeutral p := by
  have hcongr : ∀ p ∈ stdSimplex ℝ (Fin 2),
      (IsMaxOn (fun q : Fin 2 → ℝ => metaReturn 8 (1/4) 2 q (fun _ => 1)) (stdSimplex ℝ (Fin 2)) p ↔
        IsMaxOn (fun q : Fin 2 → ℝ => F 8 (1/4) 2 q (fun _ => 1)) (stdSimplex ℝ (Fin 2)) p) := by
    intro p hp
    rw [isMaxOn_iff, isMaxOn_iff]
    constructor
    · intro h q hq
      rw [F_eq_metaReturn_of_mem _ _ _ _ _ hq, F_eq_metaReturn_of_mem _ _ _ _ _ hp]
      exact h q hq
    · intro h q hq
      rw [← F_eq_metaReturn_of_mem _ _ _ _ _ hq, ← F_eq_metaReturn_of_mem _ _ _ _ _ hp]
      exact h q hq
  obtain ⟨⟨p, hp, hmax⟩, hnone⟩ := theorem_5_1_neutrality_false
  exact ⟨⟨p, hp, (hcongr p hp).mpr hmax⟩, fun p hp h => hnone p hp ((hcongr p hp).mp h)⟩

end Drest

end Cleanroom.Lit.LitShutdownPrefs
