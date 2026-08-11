/-
  edt-node-value-attack.lean  —  FAITHFULNESS GATE, hypothesis-inertness probes.

  Independent skeptic. Copies the load-bearing definitions from
  run2/lean/edt-node-value.lean and re-runs the MAIN decoupled theorem with each
  hypothesis deleted/weakened in turn. If a stripped variant still compiles, that
  hypothesis was INERT (=> shadow). We also try the conclusion-triviality attack.

  Each ATTACK block is guarded behind `theorem … := by sorry`-free attempts; a block
  that should FAIL is shown commented with the error, or replaced by the proof that
  the negation holds (a counter-instance), so this whole file COMPILES exit 0 and the
  attack conclusions are themselves kernel-checked.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset

namespace Attack

variable {S A : Type*} [Fintype S] [Fintype A]

def policyValue (U : (S → A) → ℝ) (π : S → A) : ℝ := U π
def vNode (U : (S → A) → ℝ) (κ : S → A → (S → A)) (s : S) (a : A) : ℝ := U (κ s a)

section Decoupled
variable [Nonempty A] [DecidableEq S]

def Separable (U : (S → A) → ℝ) (p : S → ℝ) (u : S → A → ℝ) : Prop :=
  ∀ π : S → A, U π = ∑ s, p s * u s (π s)

def Decoupled (κ : S → A → (S → A)) (base : S → S → A) : Prop :=
  ∀ s a, κ s a = Function.update (base s) s a

/- ===========================================================================
   ATTACK A1 — DELETE `hDec` (the Decoupled hypothesis) from the main theorem.
   If this compiles, the decoupling of κ was INERT => κ-laundering shadow.
   We supply NO replacement for hDec and try to close the goal.
   =========================================================================== -/

/-  This is the ORIGINAL theorem with `hDec` removed. We attempt the original proof
    path; it CANNOT work because `vNode_decoupled_eq` needs `hDec`. We instead try the
    strongest generic close and see whether ANY proof exists.  (Left as a `sorry`-free
    counter-instance below: ATTACK A1-COUNTER shows a separable U + a NON-decoupled κ
    where the EDT-argmax policy FAILS to be globally optimal — so hDec is load-bearing.) -/

-- A1-COUNTER: separable U, but κ NOT decoupled (it reports a misleading whole policy),
-- so the EDT-node-value argmax picks the WRONG action and misses the global optimum.
-- This proves: without `Decoupled`, the conclusion is FALSE => hDec is load-bearing.
namespace A1Counter
abbrev S2 := Fin 2
abbrev A2 := Fin 2
def p : S2 → ℝ := fun _ => 1
-- separable u: at s=0 action 1 is best (3 vs 1); at s=1 action 0 is best (4 vs 2).
def u : S2 → A2 → ℝ := fun s a =>
  if s = 0 then (if a = 1 then 3 else 1) else (if a = 0 then 4 else 2)
def U : (S2 → A2) → ℝ := fun π => ∑ s, p s * u s (π s)
theorem hSep : Separable U p u := fun _ => rfl
-- A DECEIVING (non-decoupled) kernel: κbad s a reports the WHOLE policy that plays the
-- FLIPPED local action `flip a` at s (and refuse elsewhere). Maximizing vNode = U∘κbad at
-- s therefore picks the action whose flip is the local u-argmax = the WRONG action.
-- We use an explicit `flip` (0↦1, 1↦0) so no `Fin` subtraction is left for the simplifier.
def flip : A2 → A2 := fun a => if a = 0 then 1 else 0
def κbad : S2 → A2 → (S2 → A2) := fun s a => Function.update (fun _ => (0:A2)) s (flip a)
-- κbad is NOT decoupled: there is no fixed `base` with κbad s a = update (base s) s a, since
-- the value placed AT s is `flip a`, not `a`. So `Decoupled κbad base` fails for every base.
def edtPolicyBad : S2 → A2 := fun s => if s = 0 then 0 else 1   -- the WRONG (flipped) policy
theorem edtBad_is_argmax : ∀ s a, vNode U κbad s a ≤ vNode U κbad s (edtPolicyBad s) := by
  intro s a
  fin_cases s <;> fin_cases a <;>
    simp only [edtPolicyBad, vNode, U, κbad, flip, p, u, Fin.sum_univ_two, Function.update_apply] <;>
    norm_num
-- The global optimum is (1,0) with value 7; edtPolicyBad = (0,1) has value 1+2 = 3.
theorem global_beats_edtbad :
    ∃ π : S2 → A2, policyValue U edtPolicyBad < policyValue U π := by
  refine ⟨fun s => if s = 0 then 1 else 0, ?_⟩
  simp only [policyValue, U, edtPolicyBad, p, u, Fin.sum_univ_two]; norm_num
-- κbad is genuinely NOT decoupled: no fixed base satisfies `Decoupled κbad base`, because
-- κbad places `flip a` (not `a`) at node s. Witness the failure at s=0, a=0: κbad 0 0 puts
-- `flip 0 = 1` at node 0, but `update (base 0) 0 0` puts `0` at node 0.
theorem κbad_not_decoupled : ¬ ∃ base : S2 → S2 → A2, Decoupled κbad base := by
  rintro ⟨base, hDec⟩
  have h := congrArg (fun f => f 0) (hDec 0 0)
  simp only [κbad, flip, Function.update_self] at h
  -- h : (1 : A2) = 0, contradiction
  exact absurd h (by decide)
-- ⇒ DELETING hDec makes the conclusion (∀ π, policyValue U π ≤ policyValue U πstar) FALSE,
--   even though hSep, _hp, and hEDT (edtBad_is_argmax) all hold. hDec is LOAD-BEARING.
theorem A1_hDec_load_bearing :
    Separable U p u ∧ (∀ s, (0:ℝ) ≤ p s) ∧
    (∀ s a, vNode U κbad s a ≤ vNode U κbad s (edtPolicyBad s)) ∧
    (¬ ∃ base : S2 → S2 → A2, Decoupled κbad base) ∧
    ¬ (∀ π : S2 → A2, policyValue U π ≤ policyValue U edtPolicyBad) := by
  refine ⟨hSep, fun _ => by norm_num [p], edtBad_is_argmax, κbad_not_decoupled, ?_⟩
  rintro hAll
  obtain ⟨π, hπ⟩ := global_beats_edtbad
  exact absurd (hAll π) (not_le.mpr hπ)
end A1Counter

/- ===========================================================================
   ATTACK A2 — DELETE `hSep` (Separable). Already implied load-bearing by the
   Mugging instance in the original file; we re-confirm independently that the
   conclusion is FALSE without separability (a non-separable U + decoupled κ +
   genuine EDT-argmax at both nodes, strict miss). This is the mugging structure.
   =========================================================================== -/
namespace A2Counter
abbrev S2 := Fin 2
abbrev A2 := Fin 2
def U : (S2 → A2) → ℝ := fun π =>
  (if π 0 = 1 then (-100:ℝ) else 0) + (if π 0 = 1 ∧ π 1 = 1 then 10000 else 0)
def base : S2 → S2 → A2 := fun _ _ => 0
def κ : S2 → A2 → (S2 → A2) := fun s a => Function.update (base s) s a
def edtPolicy : S2 → A2 := fun _ => 0
-- κ IS decoupled here (base ≡ 0); so hDec HOLDS but hSep FAILS.
theorem hDec : Decoupled κ base := fun _ _ => rfl
theorem edt_argmax : ∀ s a, vNode U κ s a ≤ vNode U κ s (edtPolicy s) := by
  intro s a
  fin_cases s <;> fin_cases a <;>
    simp only [edtPolicy, vNode, U, κ, base, Function.update_apply] <;> norm_num
theorem A2_hSep_load_bearing :
    Decoupled κ base ∧
    (∀ s a, vNode U κ s a ≤ vNode U κ s (edtPolicy s)) ∧
    ¬ (∀ π : S2 → A2, policyValue U π ≤ policyValue U edtPolicy) := by
  refine ⟨hDec, edt_argmax, ?_⟩
  intro hAll
  have h := hAll (fun _ => 1)
  simp only [policyValue, U, edtPolicy] at h
  norm_num at h
end A2Counter

/- ===========================================================================
   ATTACK A3 — DELETE `hEDT` (the spec that π★ is an EDT-argmax). Then π★ is
   arbitrary and the conclusion is trivially FALSE (pick the worst policy). This
   confirms hEDT is load-bearing (not a free pass).
   =========================================================================== -/
namespace A3Counter
abbrev S2 := Fin 2
abbrev A2 := Fin 2
def p : S2 → ℝ := fun _ => 1
def u : S2 → A2 → ℝ := fun s a => if s = 0 then (if a = 1 then 3 else 1) else (if a = 0 then 4 else 2)
def U : (S2 → A2) → ℝ := fun π => ∑ s, p s * u s (π s)
-- a deliberately BAD π★ that is NOT an EDT-argmax: the all-worst policy (0,1) value 3.
def badStar : S2 → A2 := fun s => if s = 0 then 0 else 1
theorem A3_hEDT_load_bearing :
    Separable U p u ∧ (∀ s, (0:ℝ) ≤ p s) ∧
    ¬ (∀ π : S2 → A2, policyValue U π ≤ policyValue U badStar) := by
  refine ⟨fun _ => rfl, fun _ => by norm_num [p], ?_⟩
  intro hAll
  have h := hAll (fun s => if s = 0 then 1 else 0)
  simp only [policyValue, U, badStar, p, u, Fin.sum_univ_two] at h
  norm_num at h
end A3Counter

/- ===========================================================================
   ATTACK C — CONCLUSION-TRIVIALITY. Is the main conclusion provable with no/weak
   hypotheses? I.e. is "∀ π, policyValue U π ≤ policyValue U πstar" trivially true?
   A1/A2/A3 already produce concrete (U, πstar) where it is FALSE, so the conclusion
   is NOT a triviality. We record the meta-fact: the conclusion fails for some inputs.
   =========================================================================== -/
theorem conclusion_not_trivial :
    ∃ (U : (Fin 2 → Fin 2) → ℝ) (πstar : Fin 2 → Fin 2),
      ¬ (∀ π : Fin 2 → Fin 2, policyValue U π ≤ policyValue U πstar) :=
  ⟨A3Counter.U, A3Counter.badStar, (A3Counter.A3_hEDT_load_bearing).2.2⟩

/- ===========================================================================
   ATTACK K — IS κ INERT IN vNode?  (shadow-test (c): vNode definitionally = local
   argmax of U?)  We show the SAME U gives DIFFERENT vNode argmaxes under two κ's,
   which is impossible if vNode were a κ-independent relabel of U's local argmax.
   (Mirrors the original `correlated_kappa_agrees` vs severing κ, re-derived here.)
   =========================================================================== -/
namespace KInert
abbrev S2 := Fin 2
abbrev A2 := Fin 2
def U : (S2 → A2) → ℝ := fun π =>
  (if π 0 = 1 then (-100:ℝ) else 0) + (if π 0 = 1 ∧ π 1 = 1 then 10000 else 0)
def κsev  : S2 → A2 → (S2 → A2) := fun s a => Function.update (fun _ => (0:A2)) s a
def κcorr : S2 → A2 → (S2 → A2) := fun _ a => fun _ => a
-- severing κ: at node 0, refuse (0) beats pay (1): vNode 0 0 = 0 > vNode 0 1 = -100.
theorem sev_node0 : vNode U κsev 0 1 < vNode U κsev 0 0 := by
  simp only [vNode, U, κsev, Function.update_apply]; norm_num
-- correlated κ: at node 0, pay (1) beats refuse (0): vNode 0 1 = 9900 > vNode 0 0 = 0.
theorem corr_node0 : vNode U κcorr 0 0 < vNode U κcorr 0 1 := by
  simp only [vNode, U, κcorr]; norm_num
-- ⇒ for the SAME U, the per-node argmax at node 0 FLIPS with κ. κ is NOT inert; vNode
--   is not a κ-independent relabel of any fixed local argmax of U.
theorem kappa_changes_argmax :
    (vNode U κsev 0 1 < vNode U κsev 0 0) ∧ (vNode U κcorr 0 0 < vNode U κcorr 0 1) :=
  ⟨sev_node0, corr_node0⟩
end KInert

end Decoupled

#print axioms A1Counter.A1_hDec_load_bearing
#print axioms A2Counter.A2_hSep_load_bearing
#print axioms A3Counter.A3_hEDT_load_bearing
#print axioms conclusion_not_trivial
#print axioms KInert.kappa_changes_argmax

end Attack
