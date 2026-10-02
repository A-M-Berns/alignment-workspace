import Cleanroom.Bli.BliExactness.Liar

/-!
# Audit r3 (fidelity) probe — the family-relative **interval** corollary at the liar is a two-liner

Construction-facing (imports `Liar`). Not imported by the library.

The package calls `ExactReflectionInterval` "the refuted object of record" and its `Defs` header
says "X1 and X3 refute the interval forms". X3 does so at the family level
(`x3_not_exactReflectionInterval`); X1 refutes the interval form **per cell**
(`exact_reflection_fails_liar`) and states the family-relative corollary only for the midpoint
predicate (`not_exactReflection_of_liar`, "via the midpoint form"). The interval-form family
corollary is immediate from what is already proved — this file is the evidence that adding it
costs nothing (audit r3 fidelity, non-blocking N2).
-/

namespace Cleanroom.Bli.BliExactness.AuditR3

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliExactness

section

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [𝗥₀ ⪯ T]

/-- No theory-respecting history with positive mass on a one-sided cell of the family satisfies
the **interval** predicate of record on that family — `exact_reflection_fails_liar` read at the
family's cell. -/
theorem not_exactReflectionInterval_of_liar {p : ℚ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) (P : History)
    (cells : ℕ → Finset (ℚ × ℚ)) {n m : ℕ} (hnm : n < m) {lo hi : ℚ} (hcell : (lo, hi) ∈ cells m)
    (hside : hi < p ∨ p ≤ lo)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    ¬ ExactReflectionInterval (quoteAt T) cells P := by
  intro h
  have key := h n m hnm (liar T p m) (lo, hi) hcell hpos
  dsimp only at key
  exact exact_reflection_fails_liar T hp₀ hp₁ P n m hside hresp hpos key

end

end Cleanroom.Bli.BliExactness.AuditR3
