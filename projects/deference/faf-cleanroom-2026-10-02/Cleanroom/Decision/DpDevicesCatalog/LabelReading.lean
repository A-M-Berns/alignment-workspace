import Cleanroom.Found.DpCoreTree.Bernstein
import Cleanroom.Found.DpCoreTree.BernsteinBack
import Cleanroom.Found.DpCoreTree.RootEvents
import Cleanroom.Decision.DpDevicesCatalog.Values
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.Polynomial.Bernstein

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T11(d): label-reading environments are not Definition-6 trees

* `exists_polynomial_nu_deviate`: on **any** tree with a two-action point `d`, for every event
  `X`, `q ↦ ν_{C[d ↦ (q, 1−q)]}(X)` is a polynomial in `q` (structural induction; no
  `QueriesExactly` hypothesis, unlike `exists_polynomial_nu_twoPoint`).
* `no_mixing_detector_polynomial`: no polynomial is `1` on `(0,1)` and `0` at `0`;
  `no_mixing_detector`: hence no event of any Definition-6 tree has probability
  `𝟙[0 < q < 1]` — "the seller reads whether the agent mixes" (O&C's Anti-Randomization) is
  unrepresentable (`P02.md` Open 4; dp-sl-2-038).
* The positive side: the `k`-probe detector `1 − q^k − (1−q)^k` **is** realised
  (`probeTree_nu`, a `bernTree` with `b_0 = b_k = 0`, `b_j = 1` otherwise): `N+` at `q = 2/3`,
  `k = 10`, where it exceeds `49/50` (`probe_instance`), and the exact penalty threshold at
  the miniature's tie for `k = 10` is `c ≥ 19683/29012` (`probe_threshold`; dp-sl-065's
  "`c ≳ .68`" is this number, ill-posed until `k` is fixed).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

/-- The two-point weight. Source: none: infrastructure. Kind: L -/
theorem twoPoint_w {α : Type} [Fintype α] [DecidableEq α] (a : α) (hc : Fintype.card α = 2)
    (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : α) :
    (FinDistr.twoPoint a hc q h0 h1).w b = if b = a then q else 1 - q := rfl

/-- **`ν_{C[d ↦ (q, 1−q)]}(X)` is a polynomial in `q` on every tree** (the mandate's "for any
tree `B` querying a two-action point `d` and any event `X`"): by structural induction, a leaf
contributes a constant, a chance node a `β`-combination, a `d`-node the weights `X`/`1 − X`,
another node its constant weights.
Source: [[decision-problems-v2]] Proposition 4 (polynomiality of the law in the label);
mandate T11(d)
Kind: P
Fidelity: stronger (no `QueriesExactly` hypothesis)
Hyps: none -/
theorem exists_polynomial_nu_deviate {Ω ι : Type} [DecidableEq Ω] [DecidableEq ι]
    {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (C : Proc ι acts ℚ) (d : ι) (a : acts d) (hc : Fintype.card (acts d) = 2)
    (B : Tree Ω ι acts ℚ) (X : Finset Ω) :
    ∃ P : Polynomial ℚ, ∀ q (h0 : 0 ≤ q) (h1 : q ≤ 1),
      nu (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B X = P.eval q := by
  induction B with
  | leaf ω r =>
    refine ⟨Polynomial.C (if ω ∈ X then 1 else 0), fun q h0 h1 => ?_⟩
    rw [nu_eq_sum, Tree.sum_leaves_leaf]
    simp only [world_leaf, leafLaw_leaf]
    split_ifs <;> simp
  | chance n β child ih =>
    choose P hP using ih
    refine ⟨∑ i, Polynomial.C (β.w i) * P i, fun q h0 h1 => ?_⟩
    rw [nu_chance, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP i q h0 h1, Polynomial.eval_mul, Polynomial.eval_C]
  | decision d' child ih =>
    choose P hP using ih
    by_cases hd : d' = d
    · subst hd
      refine ⟨∑ b, (if b = a then Polynomial.X else 1 - Polynomial.X) * P b, fun q h0 h1 => ?_⟩
      rw [nu_decision', Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hP b q h0 h1, Polynomial.eval_mul, Proc.deviate_same, twoPoint_w]
      split_ifs <;> simp
    · refine ⟨∑ b, Polynomial.C ((C d').w b) * P b, fun q h0 h1 => ?_⟩
      rw [nu_decision', Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hP b q h0 h1, Polynomial.eval_mul, Polynomial.eval_C, Proc.deviate_ne _ _ hd]

/-- **No polynomial is `1` on `(0, 1)` and `0` at `0`** (`P − 1` would have infinitely many
roots).
Source: `no_threshold_polynomial`'s argument (dp-core-tree); mandate T11(d)
Kind: P
Fidelity: exact -/
theorem no_mixing_detector_polynomial :
    ¬ ∃ P : Polynomial ℚ, (∀ q : ℚ, 0 < q → q < 1 → P.eval q = 1) ∧ P.eval 0 = 0 := by
  rintro ⟨P, h1, h0⟩
  have hz : P - 1 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.Ioo (0 : ℚ) 1)
    · intro q hq
      simp [Polynomial.IsRoot, h1 q hq.1 hq.2]
    · exact Set.Ioo_infinite (by norm_num)
  have := congrArg (Polynomial.eval 0) hz
  simp [h0] at this

/-- **"The seller reads whether the agent mixes" is unrepresentable in Definition 6**: no event
of any tree, under any point-deviation at a two-action point, has probability `𝟙[0 < q < 1]`
as a function of the label `q`.
Source: `sl-workflow/notes/repair/P02.md` Open 4 ("O&C's Anti-Randomization variant (the
seller reads whether the agent mixes) — unrepresentable under Definition 6 (the tree reads
draws, not labels; Proposition 4)"); `P12.md` line 151; dp-sl-2-038
Kind: C
Fidelity: exact
Hyps: none -/
theorem no_mixing_detector {Ω ι : Type} [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (C : Proc ι acts ℚ) (d : ι)
    (a : acts d) (hc : Fintype.card (acts d) = 2) (B : Tree Ω ι acts ℚ) (X : Finset Ω) :
    ¬ ∀ q (h0 : 0 ≤ q) (h1 : q ≤ 1),
      nu (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B X = if 0 < q ∧ q < 1 then 1 else 0 := by
  intro h
  obtain ⟨P, hP⟩ := exists_polynomial_nu_deviate C d a hc B X
  apply no_mixing_detector_polynomial
  refine ⟨P, fun q hq0 hq1 => ?_, ?_⟩
  · rw [← hP q hq0.le hq1.le, h q hq0.le hq1.le, if_pos ⟨hq0, hq1⟩]
  · rw [← hP 0 le_rfl zero_le_one, h 0 le_rfl zero_le_one]
    simp

/-! ## The positive side: the `k`-probe detector -/

/-- The `k`-probe coefficients: `b_j = 1` for `0 < j < k`, `0` at the ends ("not all `k`
draws equal").
Source: dp-sl-065 (the `k`-probe detector `1 − q^k − (1−q)^k`)
Kind: D -/
def probeB (k j : ℕ) : ℚ := if 0 < j ∧ j < k then 1 else 0

/-- The probe coefficients are in `[0, 1]`. Source: none: infrastructure. Kind: L -/
theorem probeB_bounds (k j : ℕ) : 0 ≤ probeB k j ∧ probeB k j ≤ 1 := by
  unfold probeB; split_ifs <;> norm_num

/-- **The `k`-probe tree**: `k` nested `d`-nodes, then a coin that comes up `true` iff the draws
were not all equal (a `bernTree` with `b_0 = b_k = 0`, `b_j = 1` otherwise).
Source: dp-sl-065; mandate T11(d) ("specialise `bernTree` with `b_0 = b_k = 0`, `b_j = 1`
otherwise")
Kind: D -/
def probeTree (k : ℕ) : Tree Bool Unit (fun _ => Bool) ℚ := bernTree (probeB k) (probeB_bounds k) k 0

/-- The endpoint Bernstein values: `B_{k,0}(q) = (1−q)^k`, `B_{k,k}(q) = q^k`.
Source: none: infrastructure. Kind: L -/
theorem bernstein_eval_ends (k : ℕ) (q : ℚ) :
    (bernsteinPolynomial ℚ k 0).eval q = (1 - q) ^ k ∧ (bernsteinPolynomial ℚ k k).eval q = q ^ k := by
  constructor <;> rw [bernstein_eval] <;> simp

/-- **The `k`-probe detector is realised**: `ν_{C_q}(true) = 1 − q^k − (1−q)^k` on `probeTree k`
for `k ≥ 1` (Bernstein's partition of unity minus the two endpoint terms).
Source: dp-sl-065 ("the `k`-probe detector `1 − q^k − (1−q)^k` is realised"); mandate T11(d)
Kind: P
Fidelity: exact
Hyps: (a) `1 ≤ k` -/
theorem probeTree_nu (k : ℕ) (hk : 1 ≤ k) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (procBool q h0 h1) (probeTree k) {true} = 1 - q ^ k - (1 - q) ^ k := by
  have hsum : nu (procBool q h0 h1) (probeTree k) {true} =
      ∑ j ∈ Finset.range (k + 1), probeB k j * (bernsteinPolynomial ℚ k j).eval q := by
    unfold probeTree
    rw [bernTree_nu, bernSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bernstein_eval, zero_add]
    ring
  have htot : ∑ j ∈ Finset.range (k + 1), (bernsteinPolynomial ℚ k j).eval q = 1 := by
    rw [← Polynomial.eval_finsetSum, bernsteinPolynomial.sum]; simp
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hsplit : ∀ f : ℕ → ℚ, ∑ j ∈ Finset.range (m + 1 + 1), probeB (m + 1) j * f j =
      ∑ j ∈ Finset.range (m + 1 + 1), f j - f 0 - f (m + 1) := by
    intro f
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∑ j ∈ Finset.range m, probeB (m + 1) (j + 1) * f (j + 1) =
        ∑ j ∈ Finset.range m, f (j + 1) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have : probeB (m + 1) (j + 1) = 1 := by unfold probeB; rw [if_pos ⟨by omega, by omega⟩]
      rw [this, one_mul]
    have h0' : probeB (m + 1) 0 = 0 := by unfold probeB; simp
    have hk' : probeB (m + 1) (m + 1) = 0 := by unfold probeB; simp
    rw [hmid, h0', hk']; ring
  rw [hsum, hsplit, htot, (bernstein_eval_ends (m + 1) q).1, (bernstein_eval_ends (m + 1) q).2]
  ring

/-- **N+ at `q = 2/3`, `k = 10`**: the detector fires with probability `58024/59049 > 49/50`.
Source: dp-sl-065 ("`> 49/50` exactly"); mandate T11(d)
Kind: N+ -/
theorem probe_instance :
    nu (procBool (2/3) (by norm_num) (by norm_num)) (probeTree 10) {true} = 58024/59049 ∧
    (49/50 : ℚ) < 58024/59049 := by
  rw [probeTree_nu 10 (by norm_num)]
  norm_num

/-- **The exact penalty threshold at the miniature's tie, `k = 10`**: a penalty `c` on
detection cancels the tie's value `2/3` iff `c · (1 − (2/3)^10 − (1/3)^10) ≥ 2/3`, i.e. iff
`c ≥ 19683/29012` (`≈ 0.678`). dp-sl-065's decimal "`c ≳ .68`" is this number at `k = 10`;
without a fixed `k` it is ill-posed.
Source: dp-sl-065; plan §0.4 rule 4 (no decimals transcribed); mandate T11(d)
Kind: T
Fidelity: exact (at `k = 10`) -/
theorem probe_threshold (c : ℚ) :
    c * (1 - (2/3 : ℚ) ^ 10 - (1 - 2/3) ^ 10) ≥ 2/3 ↔ c ≥ 19683/29012 := by
  norm_num
  constructor <;> intro h <;> linarith

end Cleanroom.Decision.DpDevicesCatalog
