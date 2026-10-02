import Cleanroom.Li.TtLadder

/-!
# tt-ladder audit, round 3, lens `fidelity` — probes

Not imported by the library. Each probe supports a remark in
`run/wp/tt-ladder/tt-ladder-audit-r3-fidelity.md`.

* **S1** (findings F5, second paragraph, repair round 2): the constant pair `a ≡ 1`, `e ≡ 9/10`
  at `t = 1/2`, `δ = 1/10` has `T_∀ε` (every weight is `0`: `e ≥ 1/2 − ε` for every `ε > 0`) and
  fails the *product* reading of lean-deference-046's Prop A conclusion,
  `G_n (E^H_n − a_n) ≳ₙ 0` (the product is identically `−1/10`). The findings file states this
  in prose only; here it is machine-checked. (The other reading, a `liminf` of `e − a` along gate
  days, is refuted by W2 in prose through `not_lCondSeq_sqQuote_zero`: that reading implies
  `L_cond(1/2)`, which W2 fails.)
-/

namespace Cleanroom.Li.TtLadder.AuditR3Fidelity

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.TtLadder

/-- S1a: the constant pair has `T_∀ε(1/2, 1/10)` — every violation weight is `0`. -/
theorem const_pair_tAllEps : TAllEpsSeq (fun _ => (1 : ℝ)) (fun _ => (9/10 : ℝ)) (1/2) (1/10) := by
  intro ε hε
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  unfold TSeq
  refine summable_zero.congr (fun n => ?_)
  rw [viol_const_quote (by norm_num) (by norm_num),
    (ctsInd_eq_zero_iff (by norm_num) _ _).2 (by push_cast; linarith)]

/-- S1b: the constant pair fails `G_n (e_n − a_n) ≳ₙ 0` — the gate is `1` and the product is
identically `−1/10`. So lean-deference-046's Prop A summary (conclusion with `a_n` in place of
`t`) is false under the product reading; what Prop A proves is `lProdSeq_of_tAllEpsSeq`'s
`G_n (e_n − t) ≳ₙ 0`, which the same pair satisfies (`e ≥ t`). -/
theorem const_pair_not_product :
    ¬ AsympGE (fun n => gateSeq (1/2) (1/10) (fun _ => (1 : ℝ)) n * ((9/10 : ℝ) - 1))
      (fun _ => 0) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/20) (by norm_num))
  have h1 : (0 : ℝ) ≤ gateSeq (1/2) (1/10) (fun _ => (1 : ℝ)) N * ((9/10 : ℝ) - 1) + 1/20 :=
    hN N le_rfl
  rw [gateSeq_const_eq_one (by norm_num) (by norm_num)] at h1
  norm_num at h1

/-- S1c: the same pair *does* satisfy the package's Prop A conclusion `L_prod(1/2, 1/10)`
(`e ≡ 9/10 ≥ t`), so the discrepancy is in 046's summary, not in Prop A. -/
theorem const_pair_lProdSeq : LProdSeq (fun _ => (1 : ℝ)) (fun _ => (9/10 : ℝ)) (1/2) (1/10) :=
  lProdSeq_of_tAllEpsSeq (by norm_num) (fun _ => by norm_num) const_pair_tAllEps

end Cleanroom.Li.TtLadder.AuditR3Fidelity
