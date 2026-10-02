import Cleanroom.Li.LiProjection.Church

/-!
# Audit r4 (adversarial) probe: `no_computable_modulus_market` is not true for a trivial reason.

The corollary says `¬ ∃ (A : History) m, ComputableMarket A ∧ Computable m ∧ (modulus clause)`.
If no `ComputableMarket` history could satisfy the modulus clause at all, the `Computable m`
conjunct would be idle. Here `A := P` (the inductor itself — FAF's `marketComputable` field gives
`ComputableMarket P`) with a classical modulus read off `lic_limitingBelief_tendsto` satisfies the
clause for every inductor over `paperDP T`. So the content of the corollary is exactly that the
modulus is not computable — "no inductor can certify its own convergence", as the docstring says.
Sorry-free.
-/

open Cleanroom.Li.LiProjection LogicalInduction LO.FirstOrder LO.FirstOrder.Arithmetic
  Filter Topology

theorem market_modulus_exists_classically (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (P : History) [IsLogicalInductor P (paperDP T)] :
    ∃ (A : History) (m : ℕ → ℕ → ℕ), ComputableMarket A ∧
      ∀ (σ : ArithmeticSentence) (k n : ℕ), m (Encodable.encode σ) k ≤ n →
        |A n (paperPrimeDecompose σ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
  classical
  have hmod : ∀ (σ : ArithmeticSentence) (k : ℕ), ∃ N : ℕ, ∀ n, N ≤ n →
      |P n (paperPrimeDecompose σ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
    intro σ k
    have hconv := lic_limitingBelief_tendsto P (paperDP T) (paperDP_hworld T) (paperPrimeDecompose σ)
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (1 / ((k : ℝ) + 1)) hε
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq] at this
    exact this.le
  choose! N hN using hmod
  refine ⟨P, fun c k => (Encodable.decode (α := ArithmeticSentence) c).elim 0 (fun σ => N σ k),
    (inferInstance : IsLogicalInductor P (paperDP T)).marketComputable, ?_⟩
  intro σ k n hn
  have hn' : N σ k ≤ n := by simpa using hn
  exact hN σ k n hn'

#print axioms market_modulus_exists_classically

/-- At FAF's paper LIA over `paperDP 𝗜𝚺₁`. -/
theorem paper_market_modulus_exists_classically :
    ∃ (A : History) (m : ℕ → ℕ → ℕ), ComputableMarket A ∧
      ∀ (σ : ArithmeticSentence) (k n : ℕ), m (Encodable.encode σ) k ≤ n →
        |A n (paperPrimeDecompose σ) -
          limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (paperPrimeDecompose σ)| ≤ 1 / (k + 1) :=
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  market_modulus_exists_classically 𝗜𝚺₁ (liaHistory (paperDP 𝗜𝚺₁))

#print axioms paper_market_modulus_exists_classically
