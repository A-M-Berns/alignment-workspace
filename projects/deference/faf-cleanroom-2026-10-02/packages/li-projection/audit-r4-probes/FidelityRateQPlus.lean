import Cleanroom.Li.LiProjection.Church

/-! Audit r4 (fidelity) probe: the Fidelity line of `convergence_rate_not_computable` says
"`ε = 1/(k+1)`" in place of the paper's `ε ∈ ℚ⁺`. That is a *restriction* of the rate function's
domain, so the Lean statement is at least as strong as the paper's at that point: a computable
rate function on all positive rationals restricts to a computable one on `{1/(k+1)}`. This probe
derives the paper's `ℚ⁺`-form from the package's theorem (FAF's `ratInv_prim`/`ratAdd_prim`/
`ratNatCast_prim` make `k ↦ 1/(k+1)` primitive recursive on `ℚ`), so the "ε = 1/(k+1)" clause of
the label is machine-checked as not a weakening. What the probe does NOT touch — and the audit
records as the label's real weakening — is the theory class: Foundation's `Halting.lean` binders
(`[T.SoundOnHierarchy 𝚺 1]`) in place of the paper's "represents computable functions". -/

namespace Cleanroom.Li.LiProjection.AuditR4

open LogicalInduction LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

theorem convergence_rate_not_computable_qplus (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (P : History) [IsLogicalInductor P (paperDP T)] :
    ¬ ∃ f : ℕ → ℚ → ℕ, Computable (fun p : ℕ × ℚ => f p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (ε : ℚ) (n : ℕ), 0 < ε → T ⊢ σ →
        f (Encodable.encode σ) ε < n → 1 - (ε : ℝ) < P n (paperPrimeDecompose σ) := by
  rintro ⟨f, hf, hrate⟩
  apply convergence_rate_not_computable T P
  refine ⟨fun c k => f c (((k : ℚ) + 1)⁻¹), ?_, ?_⟩
  · have hinv : Computable fun p : ℕ × ℕ => (((p.2 : ℚ) + 1)⁻¹ : ℚ) :=
      (ratInv_prim.comp (ratAdd_prim.comp (ratNatCast_prim.comp Primrec.snd)
        (Primrec.const (1 : ℚ)))).to_comp
    exact hf.comp (Computable.pair Computable.fst hinv)
  · intro σ k n hprov hn
    have hpos : (0 : ℚ) < ((k : ℚ) + 1)⁻¹ := by positivity
    have h := hrate σ (((k : ℚ) + 1)⁻¹) n hpos hprov hn
    have hcast : ((((k : ℚ) + 1)⁻¹ : ℚ) : ℝ) = 1 / ((k : ℝ) + 1) := by
      push_cast
      rw [one_div]
    rw [hcast] at h
    exact h

#print axioms convergence_rate_not_computable_qplus

end Cleanroom.Li.LiProjection.AuditR4
