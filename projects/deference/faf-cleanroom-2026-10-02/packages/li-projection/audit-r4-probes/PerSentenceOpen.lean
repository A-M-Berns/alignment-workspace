import Cleanroom.Li.LiProjection.Church

/-!
# Audit r4 (adversarial) probe: the source's *per-sentence* claim, which the package does not address.

anson-029 (chat 11 L4590–4596) argues `𝓡(H) ⊊ 𝓢` in two steps: (1) `𝓡(H) ⊆ {φ : H_∞(φ) is a
computable real}` and (2) "logical inductors over PA have non-computable limit prices on some
sentences". Findings F4 (repair round 3) correctly refutes (1) modulus-free, but its closing
paragraph says a per-sentence form *with a modulus* is "trivially inhabited … empty of content".
It is not: with the approximant computable (as the source's `Ĥ` is), the per-sentence form with a
computable modulus is exactly "`H_∞(φ)` is a computable real", and claim (2) — some limit is NOT a
computable real — is a well-posed, non-trivial statement that T6.2's *uniform* impossibility does
not imply (uniformity fails without any single limit being non-computable). Neither proved nor
refuted by the package. The statement below is the OPEN that F4 should record (it carries `sorry`
on purpose; it is audit evidence, not library). The `example` shows the per-sentence clause is
inhabited on every theorem (`f ≡ 1`), so the question is entirely about the undecidables.
-/

open Cleanroom.Li.LiProjection LogicalInduction LO.FirstOrder LO.FirstOrder.Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- **The source's claim (2), per sentence, with a computable modulus — OPEN, not in the package.**
Some limiting belief of an inductor over `paperDP T` is not a computable real. -/
theorem some_limit_not_computable_real (P : History) [IsLogicalInductor P (paperDP T)] :
    ∃ σ : ArithmeticSentence, ¬ ∃ f : ℕ → ℚ, Computable f ∧
      ∀ k : ℕ, |(f k : ℝ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
  sorry

/-- On every theorem the per-sentence clause is inhabited (the limit is `1`): the content of the
claim above is about the undecidable sentences. -/
example (P : History) [IsLogicalInductor P (paperDP T)] (σ : ArithmeticSentence) (hσ : T ⊢ σ) :
    ∃ f : ℕ → ℚ, Computable f ∧
      ∀ k : ℕ, |(f k : ℝ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
  refine ⟨fun _ => 1, Computable.const 1, fun k => ?_⟩
  rw [limitingBelief_paperPrime_of_provable T P σ hσ]
  simp only [Rat.cast_one, _root_.sub_self, abs_zero]
  positivity
