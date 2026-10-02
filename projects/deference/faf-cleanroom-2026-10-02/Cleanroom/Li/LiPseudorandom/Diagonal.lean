import Cleanroom.Li.LiPseudorandom.Defs
import LogicalInduction.Properties.Support.WeightedAverages
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Properties.Pseudorandomness

/-!
# `li-pseudorandom` — T1: the diagonal theorem over countably many causal weight rules

For `p : ℕ → ℝ` with values in `[0,1]` and any countable family of strictly causal bounded weight
rules `R : ℕ → CausalRule`, the diagonal sequence `x := diag R p` (`Defs.lean`) satisfies, for
every rule `k` whose realized weights have divergent sum, `weightedAverage ((R k).w x) (truthR x −
p) ≈ₙ 0` (`diag_pseudorandom`); at constant `p`, `weightedAverage ((R k).w x) (truthR x) ≈ₙ p`
(`diag_pseudorandom_const`).

The proof is a derandomized test-martingale argument. The potential `pot R p x n` is a finite
positive combination of running products `mart`, one per (rule, tilt) pair and sign, each a
supermartingale under a `p`-coin; the one-line identity `pot_update_avg` says that the `p`-average
of the two possible day-`n` continuations equals the old potential plus the newly activated mass,
so choosing the smaller continuation keeps `pot ≤ 2` forever (`pot_diag_le`). Hence every running
product is bounded by `2 / mass i` (`mart_diag_le`); taking logs with FAF's
`sub_two_mul_sq_le_log_one_add` gives, for the rule `k` at tilt `λ = 1/(m+2)`, the window bound
`|∑ w (t − p)| ≤ log(2/mass)/λ + 2λ ∑ w` (`window_bound`); dividing by the divergent `∑ w` and
letting `m → ∞` gives the limit (`weightedAverage_tendsto_of_mart_le`).

Scope (verbatim, per the mandate): **strictly causal rules, weights in `[0,1]` for every stream,
divergent realized sum.** A rule whose realized sum on `diag R p` converges is excluded by the
hypothesis `hdiv`, not by `weightedAverage`'s `0`-at-zero-mass junk value. `p ∈ {0,1}` is allowed
(then the sequence is eventually forced; that is correct, not degenerate).
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology
open scoped BigOperators

/-! ## Elementary facts about the pieces -/
/-- `truthR` takes values in `{0, 1}`.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma truthR_eq (x : ℕ → Bool) (n : ℕ) : truthR x n = 0 ∨ truthR x n = 1 := by
  unfold truthR; split_ifs <;> simp

/-- Supporting lemma `truthR_true` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma truthR_true {x : ℕ → Bool} {n : ℕ} (h : x n = true) : truthR x n = 1 := by
  simp [truthR, h]

/-- Supporting lemma `truthR_false` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma truthR_false {x : ℕ → Bool} {n : ℕ} (h : x n = false) : truthR x n = 0 := by
  simp [truthR, h]

/-- Supporting lemma `truthR_congr` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma truthR_congr {x y : ℕ → Bool} {n : ℕ} (h : x n = y n) : truthR x n = truthR y n := by
  simp [truthR, h]

/-- Supporting lemma `truthR_nonneg` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma truthR_nonneg (x : ℕ → Bool) (n : ℕ) : 0 ≤ truthR x n := by
  rcases truthR_eq x n with h | h <;> simp [h]

/-- Supporting lemma `truthR_le_one` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma truthR_le_one (x : ℕ → Bool) (n : ℕ) : truthR x n ≤ 1 := by
  rcases truthR_eq x n with h | h <;> simp [h]

/-- Supporting lemma `abs_truthR_sub_le` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma abs_truthR_sub_le {x : ℕ → Bool} {n : ℕ} {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    |truthR x n - q| ≤ 1 := by
  rcases truthR_eq x n with h | h <;> rw [h, abs_le] <;> constructor <;> linarith [hq.1, hq.2]

/-- Supporting lemma `clamp_nonneg` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma clamp_nonneg (r : ℝ) : 0 ≤ clamp r := le_max_left _ _

/-- Supporting lemma `clamp_le_one` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma clamp_le_one (r : ℝ) : clamp r ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- `clamp` is the identity on `[0,1]`.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma clamp_of_mem_Icc {r : ℝ} (h : 0 ≤ r ∧ r ≤ 1) : clamp r = r := by
  unfold clamp; rw [min_eq_right h.2, max_eq_right h.1]

/-- Supporting lemma `tilt_pos` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma tilt_pos (i : ℕ) : 0 < tilt i := by unfold tilt; positivity

/-- Supporting lemma `tilt_le_half` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma tilt_le_half (i : ℕ) : tilt i ≤ 1 / 2 := by
  unfold tilt
  have h0 : (0 : ℝ) ≤ ((Nat.unpair i).2 : ℝ) := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Supporting lemma `tilt_pair` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma tilt_pair (k m : ℕ) : tilt (Nat.pair k m) = 1 / ((m : ℝ) + 2) := by
  unfold tilt; rw [Nat.unpair_pair]

/-- Supporting lemma `mass_pos` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mass_pos (i : ℕ) : 0 < mass i := by unfold mass; positivity

/-- Supporting lemma `mass_le_one` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mass_le_one (i : ℕ) : mass i ≤ 1 := by
  unfold mass; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Supporting lemma `sum_mass_eq` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma sum_mass_eq (n : ℕ) : ∑ i ∈ Finset.range n, mass i = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; unfold mass; ring

/-- Supporting lemma `sum_mass_le_one` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma sum_mass_le_one (n : ℕ) : ∑ i ∈ Finset.range n, mass i ≤ 1 := by
  rw [sum_mass_eq]
  have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-! ## The nudge: `factor = 1 + nudge` -/

/-- The signed, tilted, weighted centred truth value that a factor adds to `1`:
`s · tilt i · w_k(x, j) · (truthR x j − p j)`.
Source: none: infrastructure (T1 proof)
Kind: D
Fidelity: n/a -/
noncomputable def nudge (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (s : ℝ) (i j : ℕ) :
    ℝ :=
  s * tilt i * (R (Nat.unpair i).1).w x j * (truthR x j - p j)

/-- Supporting lemma `factor_eq` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma factor_eq (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (s : ℝ) (i j : ℕ) :
    factor R p x s i j = 1 + nudge R p x s i j := rfl

/-- Supporting lemma `abs_nudge_le_tilt_mul` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma abs_nudge_le_tilt_mul {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (hs : |s| ≤ 1) (hp : 0 ≤ p j ∧ p j ≤ 1) :
    |nudge R p x s i j| ≤ tilt i * (R (Nat.unpair i).1).w x j := by
  unfold nudge
  have hw0 := (R (Nat.unpair i).1).nonneg x j
  have ht := abs_truthR_sub_le (x := x) (n := j) hp
  have ht0 := tilt_pos i
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonneg hw0]
  calc |s| * tilt i * (R (Nat.unpair i).1).w x j * |truthR x j - p j|
      ≤ 1 * tilt i * (R (Nat.unpair i).1).w x j * 1 := by gcongr
    _ = tilt i * (R (Nat.unpair i).1).w x j := by ring

/-- Supporting lemma `abs_nudge_le` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma abs_nudge_le {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (hs : |s| ≤ 1) (hp : 0 ≤ p j ∧ p j ≤ 1) :
    |nudge R p x s i j| ≤ tilt i := by
  refine (abs_nudge_le_tilt_mul hs hp).trans ?_
  have := (R (Nat.unpair i).1).le_one x j
  have := tilt_pos i
  nlinarith

/-- Supporting lemma `neg_half_le_nudge` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma neg_half_le_nudge {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (hs : |s| ≤ 1) (hp : 0 ≤ p j ∧ p j ≤ 1) :
    -(1 / 2 : ℝ) ≤ nudge R p x s i j := by
  have h1 := abs_nudge_le (R := R) (p := p) (x := x) (i := i) hs hp
  have h2 := tilt_le_half i
  rw [abs_le] at h1
  linarith [h1.1]

/-- Supporting lemma `sq_nudge_le` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma sq_nudge_le {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (hs : |s| ≤ 1) (hp : 0 ≤ p j ∧ p j ≤ 1) :
    (nudge R p x s i j) ^ 2 ≤ tilt i ^ 2 * (R (Nat.unpair i).1).w x j := by
  have h := abs_nudge_le_tilt_mul (R := R) (p := p) (x := x) (i := i) hs hp
  have hw0 := (R (Nat.unpair i).1).nonneg x j
  have hw1 := (R (Nat.unpair i).1).le_one x j
  have ht := tilt_pos i
  have hsq : (nudge R p x s i j) ^ 2 ≤ (tilt i * (R (Nat.unpair i).1).w x j) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hw2 : (R (Nat.unpair i).1).w x j ^ 2 ≤ (R (Nat.unpair i).1).w x j := by nlinarith
  calc (nudge R p x s i j) ^ 2 ≤ (tilt i * (R (Nat.unpair i).1).w x j) ^ 2 := hsq
    _ = tilt i ^ 2 * (R (Nat.unpair i).1).w x j ^ 2 := by ring
    _ ≤ tilt i ^ 2 * (R (Nat.unpair i).1).w x j := by
        apply mul_le_mul_of_nonneg_left hw2; positivity

/-- Supporting lemma `factor_ge_half` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma factor_ge_half {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (hs : |s| ≤ 1) (hp : 0 ≤ p j ∧ p j ≤ 1) :
    1 / 2 ≤ factor R p x s i j := by
  rw [factor_eq]; linarith [neg_half_le_nudge (R := R) (p := p) (x := x) (i := i) hs hp]

/-- Supporting lemma `factor_pos` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma factor_pos {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (hs : |s| ≤ 1) (hp : 0 ≤ p j ∧ p j ≤ 1) :
    0 < factor R p x s i j := by
  linarith [factor_ge_half (R := R) (p := p) (x := x) (i := i) hs hp]

/-- Supporting lemma `abs_sign_le` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma abs_sign_le {s : ℝ} (hs : s = 1 ∨ s = -1) : |s| ≤ 1 := by
  rcases hs with rfl | rfl <;> norm_num

/-! ## Locality: the potential through day `n − 1` reads days `< n` only -/

/-- A factor at day `j` reads the stream at days `≤ j` only.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma factor_congr {R : ℕ → CausalRule} {p : ℕ → ℝ} {x y : ℕ → Bool} {s : ℝ} {i j : ℕ}
    (h : ∀ j' ≤ j, x j' = y j') : factor R p x s i j = factor R p y s i j := by
  unfold factor
  rw [(R _).causal x y j (fun j' hj' => h j' hj'.le), truthR_congr (h j le_rfl)]

/-- Supporting lemma `mart_congr` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mart_congr {R : ℕ → CausalRule} {p : ℕ → ℝ} {x y : ℕ → Bool} {s : ℝ} {i n : ℕ}
    (h : ∀ j < n, x j = y j) : mart R p x s i n = mart R p y s i n := by
  unfold mart
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact factor_congr (fun j' hj' => h j' (lt_of_le_of_lt hj' hj.2))

/-- The potential through day `n − 1` depends only on the stream at days `< n`.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma pot_congr {R : ℕ → CausalRule} {p : ℕ → ℝ} {x y : ℕ → Bool} {n : ℕ}
    (h : ∀ j < n, x j = y j) : pot R p x n = pot R p y n := by
  unfold pot
  apply Finset.sum_congr rfl
  intro i _
  rw [mart_congr (s := 1) h, mart_congr (s := -1) h]

/-! ## The one-step identity and the bound `pot ≤ 2` along the diagonal -/

/-- Extending the window by one day multiplies by that day's factor.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mart_succ {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i n : ℕ} (hin : i ≤ n) :
    mart R p x s i (n + 1) = mart R p x s i n * factor R p x s i n := by
  unfold mart; exact Finset.prod_Ico_succ_top hin _

/-- Supporting lemma `mart_self` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mart_self (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (s : ℝ) (n : ℕ) :
    mart R p x s n n = 1 := by
  unfold mart; simp

/-- Supporting lemma `mart_pos` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mart_pos {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i n : ℕ}
    (hs : |s| ≤ 1) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) : 0 < mart R p x s i n := by
  unfold mart; exact Finset.prod_pos (fun j _ => factor_pos hs (hp j))

/-- Supporting lemma `pot_succ` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma pot_succ (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (n : ℕ) :
    pot R p x (n + 1) =
      ∑ i ∈ Finset.range n, mass i * (mart R p x 1 i n * factor R p x 1 i n +
        mart R p x (-1) i n * factor R p x (-1) i n) +
      mass n * (factor R p x 1 n n + factor R p x (-1) n n) := by
  unfold pot
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [mart_succ hi.le, mart_succ hi.le]
  · rw [mart_succ le_rfl, mart_succ le_rfl, mart_self, mart_self, one_mul, one_mul]

/-- Supporting lemma `factor_update` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma factor_update (R : ℕ → CausalRule) (p : ℕ → ℝ) (past : ℕ → Bool) (n : ℕ) (b : Bool)
    (s : ℝ) (i : ℕ) :
    factor R p (Function.update past n b) s i n =
      1 + s * tilt i * (R (Nat.unpair i).1).w past n * (truthR (Function.update past n b) n - p n) := by
  unfold factor
  rw [(R _).causal (Function.update past n b) past n
    (fun j hj => Function.update_of_ne hj.ne _ _)]

/-- Supporting lemma `mart_update` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mart_update {R : ℕ → CausalRule} {p : ℕ → ℝ} (past : ℕ → Bool) (n : ℕ) (b : Bool)
    (s : ℝ) (i : ℕ) :
    mart R p (Function.update past n b) s i n = mart R p past s i n :=
  mart_congr (fun _ hj => Function.update_of_ne hj.ne _ _)

/-- The abstract algebra of the one-step identity, separated so that `ring` does the work
termwise.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma avg_step {n : ℕ} (q : ℝ) (c Mp Mm fTp fTm fFp fFm : ℕ → ℝ)
    (hkey : ∀ i, q * (c i * (Mp i * fTp i + Mm i * fTm i)) +
      (1 - q) * (c i * (Mp i * fFp i + Mm i * fFm i)) = c i * (Mp i + Mm i))
    (hn : q * (c n * (fTp n + fTm n)) + (1 - q) * (c n * (fFp n + fFm n)) = 2 * c n) :
    q * (∑ i ∈ Finset.range n, c i * (Mp i * fTp i + Mm i * fTm i) + c n * (fTp n + fTm n)) +
      (1 - q) * (∑ i ∈ Finset.range n, c i * (Mp i * fFp i + Mm i * fFm i) +
        c n * (fFp n + fFm n)) =
    ∑ i ∈ Finset.range n, c i * (Mp i + Mm i) + 2 * c n := by
  rw [← hn, ← Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **The one-step identity.** The `p n`-average of the two day-`n` continuations of a prefix has
potential equal to the old potential plus twice the newly activated mass — because
`p(1−p) + (1−p)(0−p) = 0`. Holds for every real `p n`.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma pot_update_avg (R : ℕ → CausalRule) (p : ℕ → ℝ) (past : ℕ → Bool) (n : ℕ) :
    p n * pot R p (Function.update past n true) (n + 1) +
      (1 - p n) * pot R p (Function.update past n false) (n + 1) =
    pot R p past n + 2 * mass n := by
  rw [pot_succ, pot_succ]
  simp only [mart_update]
  unfold pot
  refine avg_step (p n) mass (fun i => mart R p past 1 i n) (fun i => mart R p past (-1) i n)
    (fun i => factor R p (Function.update past n true) 1 i n)
    (fun i => factor R p (Function.update past n true) (-1) i n)
    (fun i => factor R p (Function.update past n false) 1 i n)
    (fun i => factor R p (Function.update past n false) (-1) i n) ?_ ?_
  · intro i
    simp only [factor_update, truthR_true (Function.update_self n true past),
      truthR_false (Function.update_self n false past)]
    ring
  · simp only [factor_update, truthR_true (Function.update_self n true past),
      truthR_false (Function.update_self n false past)]
    ring

/-- Supporting lemma `diagPrefix_eq_diag` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma diagPrefix_eq_diag (R : ℕ → CausalRule) (p : ℕ → ℝ) :
    ∀ n j, j < n → diagPrefix R p n j = diag R p j := by
  intro n
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro j hj
    simp only [diagPrefix]
    by_cases hjn : j = n
    · subst hjn; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hjn]; exact ih j (by omega)

/-- Supporting lemma `diag_eq_update` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma diag_eq_update (R : ℕ → CausalRule) (p : ℕ → ℝ) (n : ℕ) :
    ∀ j ≤ n, diag R p j = Function.update (diagPrefix R p n) n (diag R p n) j := by
  intro j hj
  by_cases hjn : j = n
  · subst hjn; rw [Function.update_self]
  · rw [Function.update_of_ne hjn, diagPrefix_eq_diag R p n j (by omega)]

/-- Along the diagonal the potential grows by at most the newly activated mass.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma pot_diag_succ_le (R : ℕ → CausalRule) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (n : ℕ) :
    pot R p (diag R p) (n + 1) ≤ pot R p (diag R p) n + 2 * mass n := by
  have h1 : pot R p (diag R p) (n + 1) =
      pot R p (Function.update (diagPrefix R p n) n (diag R p n)) (n + 1) :=
    pot_congr (fun j hj => diag_eq_update R p n j (Nat.lt_succ_iff.1 hj))
  have h2 : pot R p (diag R p) n = pot R p (diagPrefix R p n) n :=
    pot_congr (fun j hj => (diagPrefix_eq_diag R p n j hj).symm)
  have havg := pot_update_avg R p (diagPrefix R p n) n
  rw [h1, h2, ← havg]
  have hd : diag R p n = diagStep R p n (diagPrefix R p n) := rfl
  rw [hd]
  unfold diagStep
  have hp0 := (hp n).1
  have hp1 := (hp n).2
  by_cases hlt : pot R p (Function.update (diagPrefix R p n) n true) (n + 1) <
      pot R p (Function.update (diagPrefix R p n) n false) (n + 1)
  · rw [decide_eq_true hlt]
    nlinarith [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hlt.le)]
  · rw [decide_eq_false hlt]
    have hlt' := not_lt.1 hlt
    nlinarith [mul_nonneg hp0 (sub_nonneg.2 hlt')]

/-- **The potential stays below `2` along the diagonal.**
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma pot_diag_le (R : ℕ → CausalRule) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (n : ℕ) :
    pot R p (diag R p) n ≤ 2 := by
  have h : ∀ n, pot R p (diag R p) n ≤ 2 * ∑ i ∈ Finset.range n, mass i := by
    intro n
    induction n with
    | zero => simp [pot]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [pot_diag_succ_le R p hp n]
  linarith [h n, sum_mass_le_one n]

/-- Supporting lemma `mass_mul_mart_le_pot` for T1.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mass_mul_mart_le_pot {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i n : ℕ}
    (hs : s = 1 ∨ s = -1) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (hin : i < n) :
    mass i * mart R p x s i n ≤ pot R p x n := by
  have hpos1 : 0 < mart R p x 1 i n := mart_pos (by norm_num) hp
  have hpos2 : 0 < mart R p x (-1) i n := mart_pos (by norm_num) hp
  have hterm : mass i * mart R p x s i n ≤ mass i * (mart R p x 1 i n + mart R p x (-1) i n) := by
    apply mul_le_mul_of_nonneg_left _ (mass_pos i).le
    rcases hs with rfl | rfl <;> linarith
  refine hterm.trans ?_
  unfold pot
  refine Finset.single_le_sum (f := fun i => mass i * (mart R p x 1 i n + mart R p x (-1) i n))
    ?_ (Finset.mem_range.2 hin)
  intro j _
  exact mul_nonneg (mass_pos j).le
    (add_nonneg (mart_pos (by norm_num) hp).le (mart_pos (by norm_num) hp).le)

/-- **Every running product along the diagonal is bounded by `2 / mass i`.**
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma mart_diag_le (R : ℕ → CausalRule) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {i n : ℕ} (hin : i ≤ n) :
    mart R p (diag R p) s i n ≤ 2 / mass i := by
  rcases hin.lt_or_eq with hlt | rfl
  · rw [le_div_iff₀ (mass_pos i)]
    linarith [mass_mul_mart_le_pot (R := R) (x := diag R p) hs hp hlt, pot_diag_le R p hp n]
  · rw [mart_self, le_div_iff₀ (mass_pos i), one_mul]
    linarith [mass_le_one i]

/-! ## The logarithmic window bound -/

/-- The logarithmic bound: `∑ (nudge − 2 nudge²) ≤ log (2 / mass i)` from `mart ≤ 2 / mass i`,
through FAF's `sub_two_mul_sq_le_log_one_add` and `Real.log_prod`.
Source: none: infrastructure (T1 proof); FAF `sub_two_mul_sq_le_log_one_add`
Kind: L
Fidelity: n/a -/
lemma sum_log_bound {R : ℕ → CausalRule} {p : ℕ → ℝ} {x : ℕ → Bool} {s : ℝ} {i n : ℕ}
    (hs : s = 1 ∨ s = -1) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (hM : mart R p x s i n ≤ 2 / mass i) :
    ∑ j ∈ Finset.Ico i n, (nudge R p x s i j - 2 * (nudge R p x s i j) ^ 2) ≤
      Real.log (2 / mass i) := by
  have hs' := abs_sign_le hs
  have hpos : ∀ j ∈ Finset.Ico i n, factor R p x s i j ≠ 0 :=
    fun j _ => (factor_pos hs' (hp j)).ne'
  have hlog : Real.log (mart R p x s i n) = ∑ j ∈ Finset.Ico i n, Real.log (factor R p x s i j) := by
    unfold mart; exact Real.log_prod hpos
  calc ∑ j ∈ Finset.Ico i n, (nudge R p x s i j - 2 * (nudge R p x s i j) ^ 2)
      ≤ ∑ j ∈ Finset.Ico i n, Real.log (factor R p x s i j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [factor_eq]
        exact sub_two_mul_sq_le_log_one_add (neg_half_le_nudge hs' (hp j))
    _ = Real.log (mart R p x s i n) := hlog.symm
    _ ≤ Real.log (2 / mass i) := Real.log_le_log (mart_pos hs' hp) hM

/-- **The window bound.** If both signed running products of index `i` are bounded by
`2 / mass i` on `[i, n)`, then on that window `|∑ w (t − p)| ≤ log(2/mass i)/tilt i + 2 tilt i ∑ w`.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma window_bound (R : ℕ → CausalRule) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (x : ℕ → Bool) {i n k : ℕ} (hk : (Nat.unpair i).1 = k)
    (hM : ∀ s, (s = 1 ∨ s = -1) → mart R p x s i n ≤ 2 / mass i) :
    |∑ j ∈ Finset.Ico i n, (R k).w x j * (truthR x j - p j)| ≤
      Real.log (2 / mass i) / tilt i + 2 * tilt i * ∑ j ∈ Finset.Ico i n, (R k).w x j := by
  subst hk
  have ht := tilt_pos i
  have hlin : ∀ s, ∑ j ∈ Finset.Ico i n, nudge R p x s i j =
      s * tilt i * ∑ j ∈ Finset.Ico i n, (R (Nat.unpair i).1).w x j * (truthR x j - p j) := by
    intro s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold nudge; ring
  have hsq : ∀ s, |s| ≤ 1 → ∑ j ∈ Finset.Ico i n, (nudge R p x s i j) ^ 2 ≤
      tilt i ^ 2 * ∑ j ∈ Finset.Ico i n, (R (Nat.unpair i).1).w x j := by
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact sq_nudge_le hs (hp j)
  have h1 := sum_log_bound (Or.inl rfl) hp (hM 1 (Or.inl rfl))
  have h2 := sum_log_bound (Or.inr rfl) hp (hM (-1) (Or.inr rfl))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hlin] at h1 h2
  have hsq1 := hsq 1 (by norm_num)
  have hsq2 := hsq (-1) (by norm_num)
  set D := ∑ j ∈ Finset.Ico i n, (R (Nat.unpair i).1).w x j * (truthR x j - p j) with hD
  set S := ∑ j ∈ Finset.Ico i n, (R (Nat.unpair i).1).w x j with hS
  set L := Real.log (2 / mass i) with hL
  have habs : |tilt i * D| ≤ L + 2 * tilt i ^ 2 * S :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hDeq : |D| = |tilt i * D| / tilt i := by
    rw [abs_mul, abs_of_pos ht, mul_div_cancel_left₀ _ ht.ne']
  rw [hDeq, div_le_iff₀ ht]
  calc |tilt i * D| ≤ L + 2 * tilt i ^ 2 * S := habs
    _ = (L / tilt i + 2 * tilt i * S) * tilt i := by field_simp

/-! ## The limit -/

/-- **The analytic core of T1.** For any stream `x` all of whose running products are bounded by
`2 / mass i`, every rule `k` with divergent realized sum has weighted average of `truthR x − p`
tending to `0`.
Source: mandate T1 (proof); [[anson-inventory]] anson-034
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem weightedAverage_tendsto_of_mart_le (R : ℕ → CausalRule) (p : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (x : ℕ → Bool)
    (hM : ∀ i n, i ≤ n → ∀ s, (s = 1 ∨ s = -1) → mart R p x s i n ≤ 2 / mass i)
    (k : ℕ) (hdiv : Tendsto (prefixSum ((R k).w x)) atTop atTop) :
    weightedAverage ((R k).w x) (fun j => truthR x j - p j) ≈ₙ (fun _ => 0) := by
  have hSpos : ∀ᶠ n in atTop, 0 < prefixSum ((R k).w x) n :=
    hdiv.eventually (eventually_gt_atTop 0)
  have hmain : Tendsto (fun n => prefixSum (fun j => (R k).w x j * (truthR x j - p j)) n /
      prefixSum ((R k).w x) n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
    have hti : tilt (Nat.pair k m) = 1 / ((m : ℝ) + 2) := tilt_pair k m
    have hk : (Nat.unpair (Nat.pair k m)).1 = k := by rw [Nat.unpair_pair]
    have htilt : 2 * tilt (Nat.pair k m) < ε / 2 := by
      rw [hti]
      rw [div_lt_iff₀ hε] at hm
      have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
      rw [mul_one_div, div_lt_iff₀ hm2]
      nlinarith
    set i := Nat.pair k m with hi
    set L := Real.log (2 / mass i) with hL
    set B := ∑ j ∈ Finset.range i, |(R k).w x j * (truthR x j - p j)| + L / tilt i with hB
    have hbound : ∀ n, i ≤ n → 0 < prefixSum ((R k).w x) n →
        |prefixSum (fun j => (R k).w x j * (truthR x j - p j)) n / prefixSum ((R k).w x) n| ≤
          B / prefixSum ((R k).w x) n + 2 * tilt i := by
      intro n hin hSn
      have hwin := window_bound R p hp x hk
        (fun s hs => hM i (n + 1) (by omega) s hs)
      have hsplit : prefixSum (fun j => (R k).w x j * (truthR x j - p j)) n =
          ∑ j ∈ Finset.range i, (R k).w x j * (truthR x j - p j) +
            ∑ j ∈ Finset.Ico i (n + 1), (R k).w x j * (truthR x j - p j) := by
        unfold prefixSum; rw [Finset.sum_range_add_sum_Ico _ (by omega)]
      have hS : ∑ j ∈ Finset.Ico i (n + 1), (R k).w x j ≤ prefixSum ((R k).w x) n := by
        unfold prefixSum
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          rw [Finset.mem_Ico] at hj
          rw [Finset.mem_range]
          exact hj.2
        · intro j _ _
          exact (R k).nonneg x j
      have hnum : |prefixSum (fun j => (R k).w x j * (truthR x j - p j)) n| ≤
          B + 2 * tilt i * prefixSum ((R k).w x) n := by
        rw [hsplit]
        have h2t : 0 ≤ 2 * tilt i := by linarith [tilt_pos i]
        have hS' := mul_le_mul_of_nonneg_left hS h2t
        calc |∑ j ∈ Finset.range i, (R k).w x j * (truthR x j - p j) +
              ∑ j ∈ Finset.Ico i (n + 1), (R k).w x j * (truthR x j - p j)|
            ≤ |∑ j ∈ Finset.range i, (R k).w x j * (truthR x j - p j)| +
              |∑ j ∈ Finset.Ico i (n + 1), (R k).w x j * (truthR x j - p j)| := abs_add_le _ _
          _ ≤ ∑ j ∈ Finset.range i, |(R k).w x j * (truthR x j - p j)| +
              (L / tilt i + 2 * tilt i * ∑ j ∈ Finset.Ico i (n + 1), (R k).w x j) :=
              add_le_add (Finset.abs_sum_le_sum_abs _ _) hwin
          _ ≤ B + 2 * tilt i * prefixSum ((R k).w x) n := by rw [hB]; linarith
      rw [abs_div, abs_of_pos hSn, div_le_iff₀ hSn]
      calc |prefixSum (fun j => (R k).w x j * (truthR x j - p j)) n|
          ≤ B + 2 * tilt i * prefixSum ((R k).w x) n := hnum
        _ = (B / prefixSum ((R k).w x) n + 2 * tilt i) * prefixSum ((R k).w x) n := by
            field_simp
    have hBt : Tendsto (fun n => B / prefixSum ((R k).w x) n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hdiv
    have hB' : ∀ᶠ n in atTop, B / prefixSum ((R k).w x) n < ε / 2 := by
      have := (Metric.tendsto_nhds.1 hBt) (ε / 2) (by positivity)
      filter_upwards [this] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact (le_abs_self _).trans_lt hn
    filter_upwards [hB', hSpos, eventually_ge_atTop i] with n h1 h2 h3
    rw [Real.dist_eq, sub_zero]
    calc |prefixSum (fun j => (R k).w x j * (truthR x j - p j)) n / prefixSum ((R k).w x) n|
        ≤ B / prefixSum ((R k).w x) n + 2 * tilt i := hbound n h3 h2
      _ < ε / 2 + ε / 2 := add_lt_add h1 htilt
      _ = ε := by ring
  unfold AsympEq
  refine hmain.congr' ?_
  filter_upwards [hSpos] with n hn
  rw [weightedAverage_eq_div hn.ne', sub_zero]

/-- **T1, the diagonal theorem (day-varying target).** For `p : ℕ → ℝ` with values in `[0,1]` and
any countable family `R` of strictly causal bounded weight rules, the diagonal sequence
`x := diag R p` defeats every rule at once: for every `k` whose realized weights on `x` have
divergent sum, `weightedAverage ((R k).w x) (truthR x − p) ≈ₙ 0`.
Scope: strictly causal rules, weights in `[0,1]` for every stream, divergent realized sum. A rule
with convergent realized sum is excluded by the hypothesis `hdiv`, not by a junk value. `p ∈ {0,1}`
is allowed. `diag` is a `def` computed from the rules by day recursion, not an existential.
Source: mandate T1; [[anson-inventory]] anson-034 (diagonalization sub-target); LI paper
`main.tex:1281` only remarks the coin-tossed case
Kind: P
Fidelity: stronger: day-varying target `p`; defeats *all* rules with divergent realized sum
(no patience needed)
Hyps: (a) -/
theorem diag_pseudorandom (R : ℕ → CausalRule) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (k : ℕ) (hdiv : Tendsto (prefixSum ((R k).w (diag R p))) atTop atTop) :
    weightedAverage ((R k).w (diag R p)) (fun j => truthR (diag R p) j - p j) ≈ₙ (fun _ => 0) :=
  weightedAverage_tendsto_of_mart_le R p hp (diag R p)
    (fun _ _ hin _ hs => mart_diag_le R p hp hs hin) k hdiv

/-- Centring a weighted average at a constant: `weightedAverage w (t − c) n = weightedAverage w t n − c`
whenever the denominator is nonzero.
Source: none: infrastructure (T1 proof)
Kind: L
Fidelity: n/a -/
lemma weightedAverage_sub_const (w t : ℕ → ℝ) (c : ℝ) {n : ℕ} (hden : prefixSum w n ≠ 0) :
    weightedAverage w (fun j => t j - c) n = weightedAverage w t n - c := by
  rw [weightedAverage_sub w t (fun _ => c) hden, weightedAverage_const w c hden]

/-- **T1 at a constant target.** For `p ∈ [0,1]`, `x := diag R (fun _ => p)` has, for every rule
`k` with divergent realized sum, `weightedAverage ((R k).w x) (truthR x) ≈ₙ p`: the paper's
`def:pseudorandom` limit, over the countable class `R`. A recentring of `diag_pseudorandom`
(`weightedAverage_sub_const` under eventual positivity of the prefix sums).
Source: mandate T1; LI paper `def:pseudorandom` (`main.tex:1273`)
Kind: L
Fidelity: exact (over the class `R`)
Hyps: (a) -/
theorem diag_pseudorandom_const (R : ℕ → CausalRule) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (k : ℕ) (hdiv : Tendsto (prefixSum ((R k).w (diag R (fun _ => p)))) atTop atTop) :
    weightedAverage ((R k).w (diag R (fun _ => p))) (truthR (diag R (fun _ => p))) ≈ₙ
      (fun _ => p) := by
  have h := diag_pseudorandom R (fun _ => p) (fun _ => hp) k hdiv
  have hSpos : ∀ᶠ n in atTop, 0 < prefixSum ((R k).w (diag R (fun _ => p))) n :=
    hdiv.eventually (eventually_gt_atTop 0)
  unfold AsympEq at h ⊢
  refine h.congr' ?_
  filter_upwards [hSpos] with n hn
  rw [sub_zero, weightedAverage_sub_const _ _ _ hn.ne']

/-- The countable-index corollary: any family of rules indexed by a type with a surjection
`ℕ → ι` (so `ι` is nonempty and countable). Stated with the surjection explicit so that a
dependent can choose it.
Source: mandate T1 (corollary)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem diag_pseudorandom_of_surjective {ι : Type*} (R : ι → CausalRule) (e : ℕ → ι)
    (he : Function.Surjective e) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (k : ι)
    (hdiv : Tendsto (prefixSum ((R k).w (diag (R ∘ e) p))) atTop atTop) :
    weightedAverage ((R k).w (diag (R ∘ e) p)) (fun j => truthR (diag (R ∘ e) p) j - p j) ≈ₙ
      (fun _ => 0) := by
  obtain ⟨k', rfl⟩ := he k
  exact diag_pseudorandom (R ∘ e) p hp k' hdiv

end Cleanroom.Li.LiPseudorandom
