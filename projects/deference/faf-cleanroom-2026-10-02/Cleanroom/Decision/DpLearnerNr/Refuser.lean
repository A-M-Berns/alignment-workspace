import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpLearnerNr.Defs

/-!
# `dp-learner-nr` target 11(a): the refuser trap — likelihood ratio 1

Two hypotheses about the iterated mugging: `h₁` (Omega couples: the heads branch transfers `y`
to a payer — `dp-core-tree`'s `mug1`) and `h₀` (the heads branch is inert: no transfer whatever
the agent's disposition — `mugInert`, defined here). The refuser `δ_refuse = procQ 0` sees the
same world law under both (`refuser_nu_eq`): on tails it refuses and gets `0`, on heads it gets
`0` either way. So its episode likelihoods are equal under `h₁` and `h₀`, Bayes' rule is the
identity (`bayesUpdate_eq`), and `π_t = π₀` for all `t` (`refuser_credence_const`). The myopic rule
`𝔼[pay] − 𝔼[refuse] = (πy − x)/2 > 0 ⟺ π > x/y` (`myopic_pay_iff`).

Reading of "inert" (findings F9): the inert heads branch pays *nothing* — the reading under which
the likelihood ratio is `1`. The alternative "pays regardless" (a transfer `y` on heads whatever
the act, `mugPaysRegardless`) is refuted *only* by the likelihood-ratio clause: under it the
refuser's heads episodes are informative (`refuser_informative_paysRegardless`), while the myopic
rule `(πy − x)/2` is the *same* under both readings (`myopic_pay_paysRegardless`), so DY-13's and
GR-15's rule does not decide between them.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Finset

/-- The leaf-world of the inert mugging at chance index `i` and action `act`: tails as in `mug1`,
heads `hZero` whatever the act (no transfer).
Source: `cf-workflow/phase2-notes/repair/dynamic.md` DY-13 ("`h₀` (heads branch inert)");
[[dp-learner-nr-mandate]] target 11(a)
Kind: D -/
def mugWorldInert (i : Fin 2) (act : Act2) : MugW :=
  if i = 0 then (if act = .a then .tPay else .tRefuse) else .hZero

/-- **The inert mugging `h₀`**: fair coin; on tails the point `d` (pay `−x` / refuse `0`); on
heads no transfer whatever the (hypothetical) act.
Source: DY-13; GR-15 ("credence `π` over `{h₁, h₀}`"); [[dp-cf-inventory]] 123;
[[dp-learner-nr-mandate]] target 11(a)
Kind: D
Fidelity: variant: "inert" read as "no transfer on heads" (findings) -/
def mugInert (x y : ℚ) : Tree MugW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun act => .leaf (mugWorldInert i act) (mugPay x y (mugWorldInert i act))

/-- Sums over the leaves of `mugInert`. Source: none: infrastructure. Kind: L -/
theorem mugInert_sum (x y : ℚ) (f : (mugInert x y).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, ⟨act, ()⟩⟩ := by
  unfold mugInert
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `ν` on the inert mugging. Source: none: infrastructure. Kind: L -/
theorem mugInert_nu (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mugInert x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a else 0) +
      (if MugW.tRefuse ∈ X then (1/2 : ℚ) * (C ()).w .b else 0) +
      (if MugW.hZero ∈ X then (1/2 : ℚ) * ((C ()).w .a + (C ()).w .b) else 0) := by
  rw [nu_eq_sum, mugInert_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mugInert, mugWorldInert, FinDistr.fair, FinDistr.coin]
  split_ifs <;> ring

/-- **`V(C)(mugInert) = −C(d)(pay)·x/2`**: paying costs `x` on tails and earns nothing on heads.
Source: DY-13 ("exploring costs expected `x`" per two episodes); [[dp-learner-nr-mandate]] target 11(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem mugInert_value (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (mugInert x y) = -((C ()).w .a * x) / 2 := by
  unfold value
  rw [mugInert_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mugInert, mugWorldInert, mugPay, FinDistr.fair,
    FinDistr.coin]
  ring

/-- **Likelihood ratio 1**: the refuser `δ_refuse` induces the same world law on the coupled
mugging and on the inert one, for every event.
Source: DY-13 ("a refuser's data have likelihood ratio 1"); GR-15; [[dp-cf-inventory]] 123;
[[dp-cf-2-inventory]] 031; [[dp-learner-nr-mandate]] target 11(a), load-bearing 5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem refuser_nu_eq (x y : ℚ) (X : Finset MugW) :
    nu (procQ 0 le_rfl zero_le_one) (mug1 x y) X = nu (procQ 0 le_rfl zero_le_one) (mugInert x y) X := by
  rw [mug1_nu, mugInert_nu]
  simp [procQ]

/-- The refuser's observed worlds have positive mass: `tRefuse` and `hZero` each `½`, under both
hypotheses.
Source: none: infrastructure
Kind: L -/
theorem refuser_observed_pos (x y : ℚ) :
    nu (procQ 0 le_rfl zero_le_one) (mug1 x y) {MugW.tRefuse} = 1 / 2 ∧
    nu (procQ 0 le_rfl zero_le_one) (mug1 x y) {MugW.hZero} = 1 / 2 ∧
    nu (procQ 0 le_rfl zero_le_one) (mugInert x y) {MugW.tRefuse} = 1 / 2 ∧
    nu (procQ 0 le_rfl zero_le_one) (mugInert x y) {MugW.hZero} = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (rw [mug1_nu]; simp [procQ]) | (rw [mugInert_nu]; simp [procQ])

/-- **Bayes' rule** for a two-hypothesis credence `π` on `h₁` with episode likelihoods `L₁`, `L₀`.
Source: DY-13 ("Myopic Bayes"); [[dp-learner-nr-mandate]] target 11(a)
Kind: D -/
def bayesUpdate (π L₁ L₀ : ℚ) : ℚ := π * L₁ / (π * L₁ + (1 - π) * L₀)

/-- **Bayes' rule is the identity when the likelihoods are equal** (and positive).
Source: DY-13 ("a refuser's data have likelihood ratio 1 (`π_t ≡ π_0`)"); [[dp-learner-nr-mandate]] target 11(a)
Kind: P
Hyps: (a) `0 < L` -/
theorem bayesUpdate_eq (π L : ℚ) (hL : 0 < L) : bayesUpdate π L L = π := by
  unfold bayesUpdate
  have : π * L + (1 - π) * L = L := by ring
  rw [this, mul_div_assoc, div_self hL.ne', mul_one]

/-- The credence after `t` episodes with observed worlds `w : ℕ → MugW`, updated by Bayes' rule
on the single-world likelihoods under `h₁` (`mug1`) and `h₀` (`mugInert`) of the refuser's law.
Source: DY-13; [[dp-learner-nr-mandate]] target 11(a)
Kind: D -/
def refuserCredence (x y π₀ : ℚ) (w : ℕ → MugW) : ℕ → ℚ
  | 0 => π₀
  | t + 1 => bayesUpdate (refuserCredence x y π₀ w t)
      (nu (procQ 0 le_rfl zero_le_one) (mug1 x y) {w t})
      (nu (procQ 0 le_rfl zero_le_one) (mugInert x y) {w t})

/-- **The refuser's credence never moves**: `π_t = π₀` for every `t`, along any sequence of
observed worlds the refuser can observe (`tRefuse` or `hZero`).
Source: DY-13 ("`π_t ≡ π_0`"); GR-15 ("A refuser has `γ_test = 0`"); [[dp-cf-inventory]] 123;
[[dp-learner-nr-mandate]] target 11(a), load-bearing 5
Kind: P
Fidelity: exact
Hyps: (a) the observed worlds are the refuser's (`tRefuse` or `hZero`) -/
theorem refuser_credence_const (x y π₀ : ℚ) (w : ℕ → MugW)
    (hw : ∀ t, w t = MugW.tRefuse ∨ w t = MugW.hZero) (t : ℕ) :
    refuserCredence x y π₀ w t = π₀ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [refuserCredence, ih]
    rw [← refuser_nu_eq]
    obtain ⟨h1, h2, _, _⟩ := refuser_observed_pos x y
    rcases hw t with h | h <;> rw [h]
    · rw [h1]; exact bayesUpdate_eq _ _ (by norm_num)
    · rw [h2]; exact bayesUpdate_eq _ _ (by norm_num)

/-- **The myopic rule**: with credence `π` on `h₁`, `𝔼[pay] − 𝔼[refuse] = π·(y−x)/2 + (1−π)·(−x/2)
= (πy − x)/2`, positive iff `π > x/y` (`0 < y`).
Source: DY-13 ("Myopic Bayes pays iff `π > x/y`"); GR-15 ("pay iff `π > x/y`");
[[dp-learner-nr-mandate]] target 11(a)
Kind: L
Hyps: (a) `0 < y` -/
theorem myopic_pay_iff (x y π : ℚ) (hy : 0 < y) :
    π * value (procQ 1 zero_le_one le_rfl) (mug1 x y)
        + (1 - π) * value (procQ 1 zero_le_one le_rfl) (mugInert x y)
      - (π * value (procQ 0 le_rfl zero_le_one) (mug1 x y)
        + (1 - π) * value (procQ 0 le_rfl zero_le_one) (mugInert x y))
      = (π * y - x) / 2 ∧
    (0 < (π * y - x) / 2 ↔ x / y < π) := by
  rw [mug1_value, mug1_value, mugInert_value, mugInert_value]
  simp only [procQ, FinDistr.act2_a]
  constructor
  · ring
  · rw [div_lt_iff₀ hy]; constructor <;> intro h <;> linarith

/-! ## The other reading of "inert": heads pays regardless (findings F9) -/

/-- The leaf-world of the pays-regardless mugging: tails as in `mug1`, heads `hOne` whatever the
act (a transfer `y` on heads regardless of the disposition).
Source: [[dp-learner-nr-mandate]] target 11(a) ("an inert variant where the heads branch pays
regardless"); findings F9
Kind: D -/
def mugWorldPaysRegardless (i : Fin 2) (act : Act2) : MugW :=
  if i = 0 then (if act = .a then .tPay else .tRefuse) else .hOne

/-- **The pays-regardless mugging**: fair coin; on tails the point `d`; on heads a transfer `y`
whatever the act. The reading of "inert" that F9 rejects — kept so the rejection is a theorem.
Source: [[dp-learner-nr-mandate]] target 11(a); findings F9
Kind: D -/
def mugPaysRegardless (x y : ℚ) : Tree MugW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun act =>
      .leaf (mugWorldPaysRegardless i act) (mugPay x y (mugWorldPaysRegardless i act))

/-- Sums over the leaves of `mugPaysRegardless`. Source: none: infrastructure. Kind: L -/
theorem mugPaysRegardless_sum (x y : ℚ) (f : (mugPaysRegardless x y).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, ⟨act, ()⟩⟩ := by
  unfold mugPaysRegardless
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `V(C) = (y − C(d)(pay)·x)/2` on the pays-regardless mugging.
Source: none: infrastructure. Kind: L -/
theorem mugPaysRegardless_value (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (mugPaysRegardless x y) = (y - (C ()).w .a * x) / 2 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  unfold value
  rw [mugPaysRegardless_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mugPaysRegardless, mugWorldPaysRegardless, mugPay,
    FinDistr.fair, FinDistr.coin]
  linear_combination (y / 2) * hs

/-- **The myopic rule does not decide between the two readings of "inert"**: under the
pays-regardless reading `𝔼[pay] − 𝔼[refuse]` is the same `(πy − x)/2` as under the no-transfer
reading (`myopic_pay_iff`) — the heads transfer `y/2` enters both sides and cancels. So findings
F9's choice of reading rests on the likelihood-ratio clause alone
(`refuser_informative_paysRegardless`). Adopted from audit r1's fidelity probe 2.
Source: DY-13; GR-15; [[dp-learner-nr-audit-r1-fidelity]] §2 item 1; findings F9
Kind: L -/
theorem myopic_pay_paysRegardless (x y π : ℚ) :
    π * value (procQ 1 zero_le_one le_rfl) (mug1 x y)
        + (1 - π) * value (procQ 1 zero_le_one le_rfl) (mugPaysRegardless x y)
      - (π * value (procQ 0 le_rfl zero_le_one) (mug1 x y)
        + (1 - π) * value (procQ 0 le_rfl zero_le_one) (mugPaysRegardless x y))
      = (π * y - x) / 2 := by
  rw [mug1_value, mug1_value, mugPaysRegardless_value, mugPaysRegardless_value]
  simp only [procQ, FinDistr.act2_a]
  ring

/-- **Under the pays-regardless reading the refuser's heads episodes are informative**: `hOne`
has mass `0` on `mug1` and `½` on the pays-regardless mugging, so the likelihood ratio is not
`1` — which is why DY-13's "likelihood ratio 1" forces the no-transfer reading (`mugInert`,
`refuser_nu_eq`). Adopted from audit r1's fidelity probe 2.
Source: DY-13 ("a refuser's data have likelihood ratio 1"); [[dp-learner-nr-audit-r1-fidelity]]
§2 item 1; findings F9
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem refuser_informative_paysRegardless (x y : ℚ) :
    nu (procQ 0 le_rfl zero_le_one) (mug1 x y) {MugW.hOne} = 0 ∧
    nu (procQ 0 le_rfl zero_le_one) (mugPaysRegardless x y) {MugW.hOne} = 1 / 2 := by
  constructor
  · rw [mug1_nu]; simp [procQ]
  · rw [nu_eq_sum, mugPaysRegardless_sum]
    simp [Fin.sum_univ_two, Act2.sum_univ, mugPaysRegardless, mugWorldPaysRegardless,
      FinDistr.fair, FinDistr.coin, procQ]
    norm_num

end Cleanroom.Decision.DpLearnerNr
