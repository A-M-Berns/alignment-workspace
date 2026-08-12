/-
  UNCHECKED — for the Lean-verify agent.

  Candidate file for the "Updatelessness & deference" thread, MODEL doc:
  models/updateless-deference-model.md.

  ----------------------------------------------------------------------
  WHAT THIS IS MEANT TO CAPTURE (plain English)
  ----------------------------------------------------------------------
  We define a relation "A updatelessly-defers to the u-informed self" as a
  DDB-Value inequality evaluated in the GLOBAL (updateless) expectation:

      A defers to u   :⇔   policyValue (πu) = max over policies of policyValue
                            (equivalently  ∀ π, policyValue π ≤ policyValue πu).

  where πu is the "diagonal assembly": the policy that, at each situation s,
  plays the action the u-informed self locally prefers (its local argmax under
  the refined belief, `nodeChoice s`).

  The single load-bearing FORMAL claim of the model is the REDUCTION (clause (i)
  of the task): when the utility is SEPARABLE across situations — i.e. there is
  NO cross-situation coupling, the "updateful / no-acausal" regime — the diagonal
  assembly πu of ANY local-argmax update is automatically a GLOBAL optimum.
  Hence in that regime "A updatelessly-defers to u" coincides with ordinary
  endorsement ("A would adopt u's local choices"): deferring node-by-node is
  globally safe. The counterfactual-mugging / transparent-Newcomb FAILURES of
  deference live entirely in the complementary, COUPLED regime, where this
  theorem's hypothesis fails and πu can be a strict global loser (verified by
  hand / by the Python micro-checker, models/updateless_deference_check.py).

  So this file proves: SEPARABLE ⇒ (local-argmax diagonal assembly IS a global
  optimum) ⇒ the deference relation reduces to ordinary endorsement.

  ----------------------------------------------------------------------
  FIDELITY CHECK (read critically — does the Lean say what the prose says?)
  ----------------------------------------------------------------------
  * `U : S → A → ℝ` (utility of the action AT s, no other-situation argument)
    is the faithful encoding of "separable / no cross-situation dependence".
    A coupled problem would need `U : S → (S → A) → ℝ` or `U : (S → A) → ℝ`;
    we deliberately use the decoupled type, so the hypothesis is STRUCTURAL and
    does NOT smuggle in the conclusion.
  * `policyValue p U π = ∑ s, p s * U s (π s)` is the global/updateless objective
    on a separable U.
  * `nodeChoice : S → A` is the u-informed self's LOCAL pick at each node — an
    ARBITRARY function in `defers_of_local_argmax` BUT constrained by the
    hypothesis `hLoc : ∀ s a, U s a ≤ U s (nodeChoice s)` to be a per-node argmax
    of `U s`. This is the faithful encoding of "the updated self plays the local
    argmax". It is NOT assumed to be a global argmax — that is the CONCLUSION.
  * The theorem `defers_of_local_argmax`: under separability + `nodeChoice` a
    per-node argmax + `p ≥ 0`, the diagonal policy `nodeChoice` DOMINATES every
    policy:  ∀ π, policyValue p U π ≤ policyValue p U nodeChoice.
    This is EXACTLY "A updatelessly-defers to u" in the separable case, with the
    independent (Value-style) definition of "defers". NON-VACUOUS: it would FAIL
    for a coupled U (the mugging witness in the .py file), so the hypothesis is
    doing real work.
  * `endorsement_reduction`: packages the same fact as "πu is a global maximizer",
    the precise sense in which the relation reduces to ordinary endorsement.
  * Quantifiers: ∀ separable U, ∀ p ≥ 0, ∀ per-node-argmax nodeChoice, ∀ π.
    Matches the prose claim "for any benign (separable) update, node-local
    deference is globally optimal".

  What this file does NOT prove (open / by-hand only):
  - The COUPLED direction (mugging/Newcomb non-deference) — that is the content,
    and it is a finite witness, checked in the .py file, not here.
  - The biconditional with an *independent* "defers" predicate beyond the Value
    inequality — see the model doc §"Circularity" for why we take Value-in-the-
    global-expectation AS the definition of defers (DDB Value, expert = updated
    self), making this a genuine reduction rather than a restatement.

  NOTE FOR THE LEAN-VERIFY AGENT (lemma names checked by hand vs prebuilt Mathlib):
  - `Finset.sum_le_sum {s} (h : ∀ i ∈ s, f i ≤ g i) : ∑ i in s, f i ≤ ∑ i in s, g i`
    — `to_additive` of `prod_le_prod'`, in
    `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` (imported).
  - `mul_le_mul_of_nonneg_left {a b c} (h : b ≤ c) (hc : 0 ≤ a) : a*b ≤ a*c`.
  - This file uses NO `sup'`, so it avoids the proof-irrelevance defeq spot that
    `UpdatelessDeference.lean` flagged. Should be a clean, fast check.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

open Finset

namespace UpdatelessDeference2

variable {S A : Type*} [Fintype S]

/-- Global / updateless objective of a policy `π : S → A` under prior `p`,
    for a SEPARABLE utility `U : S → A → ℝ` (no cross-situation coupling). -/
def policyValue (p : S → ℝ) (U : S → A → ℝ) (π : S → A) : ℝ :=
  ∑ s, p s * U s (π s)

/-- "A updatelessly-defers to the u-informed self" (separable-case form):
    the diagonal assembly `nodeChoice` (u's per-node local pick) DOMINATES every
    policy in the global expectation. This is DDB Value with expert = updated
    self, evaluated updatelessly. -/
def defersTo (p : S → ℝ) (U : S → A → ℝ) (nodeChoice : S → A) : Prop :=
  ∀ π : S → A, policyValue p U π ≤ policyValue p U nodeChoice

/-- REDUCTION THEOREM (clause (i)): if the update's local choice `nodeChoice s`
    is a per-node argmax of the SEPARABLE utility `U s`, and the prior is
    nonnegative, then A updatelessly-defers to it. I.e. in the no-coupling
    (updateful / no-acausal) regime, node-local endorsement ⇒ updateless
    deference: the diagonal assembly is globally optimal. -/
theorem defers_of_local_argmax
    (p : S → ℝ) (U : S → A → ℝ) (nodeChoice : S → A)
    (hp : ∀ s, 0 ≤ p s)
    (hLoc : ∀ s a, U s a ≤ U s (nodeChoice s)) :
    defersTo p U nodeChoice := by
  intro π
  unfold policyValue
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (hLoc s (π s)) (hp s)

/-- Repackaged as "πu is a GLOBAL maximizer of policyValue", i.e. the deference
    relation reduces to ordinary endorsement (you'd adopt u's local choices and
    that is globally optimal). Same content as `defers_of_local_argmax`. -/
theorem endorsement_reduction
    (p : S → ℝ) (U : S → A → ℝ) (nodeChoice : S → A)
    (hp : ∀ s, 0 ≤ p s)
    (hLoc : ∀ s a, U s a ≤ U s (nodeChoice s)) :
    ∀ π : S → A, policyValue p U π ≤ policyValue p U nodeChoice :=
  defers_of_local_argmax p U nodeChoice hp hLoc

#print axioms defers_of_local_argmax
#print axioms endorsement_reduction

end UpdatelessDeference2
