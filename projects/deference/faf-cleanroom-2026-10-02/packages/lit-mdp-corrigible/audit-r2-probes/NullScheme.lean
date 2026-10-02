import Cleanroom.Lit.LitMdpCorrigible

/-!
# `lit-mdp-corrigible` · audit r2 (adversarial) probe — the null scheme

Not imported by the library. `SAOSafelyInterruptibleConst`/`WAOSafelyInterruptibleConst` quantify
over *every* scheme, including the null scheme `I ≡ 0` under which `INT sch π = π` and nothing is
ever interrupted. So `¬ (S/W)AOSafelyInterruptibleConst π` follows for any `π` that is not
asymptotically optimal along one of its *own* histories — no interruption is exercised. This probe
derives the fourth and fifth conjuncts of `thm8_not_safely_interruptible` from the null scheme
alone, and states the general reduction: the constant-`θ` safe-interruptibility predicates imply
asymptotic optimality along every own history. The content of Theorem 8's negative half on Fig. 2
is therefore `thm8_int_optimal` (always-`b` *is* int-optimal for `θ > 3/10`) plus "always-`b` is
suboptimal at `s₁`"; the scheme's role is to select the policy, not to defeat it. (This is also how
the paper's Def 6 reads: `I` ranges over all initiation functions, so `I ≡ 0` is admitted there too.)
-/

open Finset FactoredSpaces Filter Topology

namespace Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial

open Interrupt

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The null scheme: `I ≡ 0`, `θ = 0`; the interruption policy is irrelevant. -/
noncomputable def nullScheme (π : Pol S A) : Scheme S A := ⟨fun _ => 0, 0, π⟩

/-- Under the null scheme the interruption operator is the identity on masses. -/
lemma INT_null_mass (π : Pol S A) (s : S) (a : A) : (INT (nullScheme π) π s).mass a = (π s).mass a := by
  rw [INT_mass]; simp [nullScheme]

/-- A history of `π` is a history of `INT (nullScheme π) π`. -/
lemma isHistory_null (M : FinMDP S A) (π : Pol S A) (ρ : ℕ → S) (h : (IsHistory M) π ρ) :
    (IsHistory M) (INT (nullScheme π) π) ρ := by
  intro t
  obtain ⟨a, ha, hs⟩ := h t
  exact ⟨a, by rw [INT_null_mass]; exact ha, hs⟩

/-- **The general reduction:** the constant-`θ` SAO-safe-interruptibility predicate implies that `π`
is an SAO-extension of itself along every own history (asymptotic optimality along own histories). -/
theorem saoConst_implies_own_history (M : FinMDP S A) [Nonempty A] (π : Pol S A)
    (h : (SAOSafelyInterruptibleConst M) π) (ρ : ℕ → S) (hρ : (IsHistory M) π ρ) : (SAOExtAlong M) ρ π :=
  h (nullScheme π) ρ (isHistory_null M π ρ hρ)

/-- Same for WAO. -/
theorem waoConst_implies_own_history (M : FinMDP S A) [Nonempty A] (π : Pol S A)
    (h : (WAOSafelyInterruptibleConst M) π) (ρ : ℕ → S) (hρ : (IsHistory M) π ρ) : (WAOExtAlong M) ρ π :=
  h (nullScheme π) ρ (isHistory_null M π ρ hρ)

/-- The constant history at `s₁` is an own history of always-`b` (no scheme involved). -/
lemma fig2_ownHistory_B : (IsHistory fig2) alwaysB fun _ => .s1 := by
  intro t
  refine ⟨A2.b, ?_, ?_⟩
  · simp [alwaysB, FinMDP.detPol, Distr.delta_mass]
  · show 0 < (Distr.delta (fig2Next .s1 .b)).mass .s1
    simp [Distr.delta_mass, fig2Next]

/-- **The probe's claim:** the fourth and fifth conjuncts of `thm8_not_safely_interruptible` follow
from the null scheme and the uninterrupted suboptimality of always-`b` at `s₁` (`9/5 < 2`), with no
interruption ever fired. -/
theorem alwaysB_fails_by_null_scheme :
    ¬ (SAOSafelyInterruptibleConst fig2) alwaysB ∧ ¬ (WAOSafelyInterruptibleConst fig2) alwaysB := by
  have hS : ¬ (SAOExtAlong fig2) (fun _ => .s1) alwaysB := (thm8_not_safely_interruptible 0).2.1
  have hW : ¬ (WAOExtAlong fig2) (fun _ => .s1) alwaysB := (thm8_not_safely_interruptible 0).2.2.1
  exact ⟨fun h => hS (saoConst_implies_own_history fig2 alwaysB h _ fig2_ownHistory_B),
    fun h => hW (waoConst_implies_own_history fig2 alwaysB h _ fig2_ownHistory_B)⟩

end Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial
