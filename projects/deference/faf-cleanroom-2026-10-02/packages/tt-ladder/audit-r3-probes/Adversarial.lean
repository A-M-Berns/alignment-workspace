import Cleanroom.Li.TtLadder

/-!
# tt-ladder audit, round 3, adversarial lens — probes

Not imported by the library. Each probe supports one remark in
`run/wp/tt-ladder/tt-ladder-audit-r3-adversarial.md`.

* S1 `icc_family_not_tFullSeq_unbounded`: `tFullSeq_iff_Icc`'s hypothesis `0 ≤ e` is
  load-bearing — with `a ≡ 0` and `e ≡ −1` every `(t, ε)` with `t ∈ [0,1]` has summable
  weight (the gate is `0` for `t ≥ 0`), yet `T_full` fails at the negative threshold
  `t = −1/2` (gate `1`, ramp `1`, weight identically `1`). So the all-`t` family is strictly
  stronger than the `[0,1]` family off the sources' bounds, as the docstring says in prose.
* S2 `rate_free_flagging`: the library's `rate_free` witness falls silent after day `N`
  (its docstring says so). The same conclusion holds for a quote that exceeds the credence on
  *every* day: `a = 1`, `e = 0` on the first `N` days, then `a = 1/2 + 1/(2(n+1))`, `e = 1/2`.
  Dominated (gap `1/(2(n+1)) → 0`), both `[0,1]`-valued, weight `1` on days `n < N`.
-/

namespace Cleanroom.Li.TtLadder.AuditR3Adversarial

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.TtLadder

/-- S1: the `[0,1]`-threshold family holds while `T_full` (all rational `t`) fails, for a
credence below `0`. -/
theorem icc_family_not_tFullSeq_unbounded :
    (∀ t ε : ℚ, 0 ≤ t → t ≤ 1 → 0 < ε → TSeq (fun _ => 0) (fun _ => -1) t ε (1/10)) ∧
    ¬ TFullSeq (fun _ => 0) (fun _ => -1) (1/10) := by
  constructor
  · intro t ε ht _ _
    unfold TSeq
    refine summable_zero.congr (fun n => ?_)
    rw [viol_eq_gateSeq_mul]
    have htR : (0 : ℝ) ≤ t := by exact_mod_cast ht
    rw [(gateSeq_eq_zero_iff (by norm_num) _ n).2 htR, zero_mul]
  · intro h
    have hs := h (-1/2) (1/10) (by norm_num)
    unfold TSeq at hs
    refine not_summable_const_of_pos (m := 1) one_pos (fun n => ?_) hs
    rw [viol_eq_gateSeq_mul]
    unfold gateSeq
    show ctsInd (1/10) (0 : ℝ) ((-1/2 : ℚ) : ℝ) *
      ctsInd (1/10) (((-1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (-1 : ℝ) = 1
    rw [(ctsInd_eq_one_iff (by norm_num) _ _).2 (by push_cast; norm_num),
      (ctsInd_eq_one_iff (by norm_num) _ _).2 (by push_cast; norm_num), one_mul]

/-- S2: `rate_free` with a persistently flagging quote (`e n < a n` on every day). -/
theorem rate_free_flagging (N : ℕ) :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, e n < a n) ∧ Dominates e a ∧ ∀ n, n < N → viol e a (1/2) (1/4) (1/10) n = 1 := by
  have hhalf : ∀ n : ℕ, (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) ∧ 1 / (2 * ((n : ℝ) + 1)) ≤ 1/2 := by
    intro n
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨fun n => if n < N then 1 else 1/2 + 1 / (2 * ((n : ℝ) + 1)),
    fun n => if n < N then 0 else 1/2, fun n => ?_, fun n => ?_, fun n => ?_, fun c hc => ?_,
    fun n hn => ?_⟩
  · show (if n < N then (1 : ℝ) else 1/2 + 1 / (2 * ((n : ℝ) + 1))) ∈ Set.Icc (0 : ℝ) 1
    split_ifs
    · norm_num
    · exact ⟨by linarith [(hhalf n).1], by linarith [(hhalf n).2]⟩
  · show (if n < N then (0 : ℝ) else 1/2) ∈ Set.Icc (0 : ℝ) 1
    split_ifs <;> norm_num
  · show (if n < N then (0 : ℝ) else 1/2) <
      (if n < N then (1 : ℝ) else 1/2 + 1 / (2 * ((n : ℝ) + 1)))
    split_ifs
    · norm_num
    · linarith [(hhalf n).1]
  · have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (show (0 : ℝ) < 2 * c by linarith))
    filter_upwards [eventually_ge_atTop N, hlim] with n hn hsm
    show (if n < N then (1 : ℝ) else 1/2 + 1 / (2 * ((n : ℝ) + 1))) - c <
      (if n < N then (0 : ℝ) else 1/2)
    rw [if_neg (not_lt.2 hn), if_neg (not_lt.2 hn)]
    have : (1 : ℝ) / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 := by
      rw [div_div, mul_comm]
    linarith
  · rw [viol_eq_gateSeq_mul]
    unfold gateSeq
    show ctsInd (1/10) (if n < N then (1 : ℝ) else 1/2 + 1 / (2 * ((n : ℝ) + 1)))
        ((1/2 : ℚ) : ℝ) *
      ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/4 : ℚ) : ℝ)) (if n < N then (0 : ℝ) else 1/2) = 1
    rw [if_pos hn, if_pos hn, (ctsInd_eq_one_iff (by norm_num) _ _).2 (by push_cast; norm_num),
      (ctsInd_eq_one_iff (by norm_num) _ _).2 (by push_cast; norm_num), one_mul]

end Cleanroom.Li.TtLadder.AuditR3Adversarial
