import LogicalInduction.Properties.Pseudorandomness
import LogicalInduction.Properties.SelfTrust

/-!
# `li-pseudorandom` — T8: `succDeferral` recovers the paper's definition

Every divergent weighting is `succDeferral`-patient (the window `[n, n+1]` carries weight `≤ 2`),
so FAF's `PseudorandomFrequency truth p succDeferral P` is exactly the LI paper's
`def:pseudorandom` at frequency `p` over all P-generable divergent weightings
(`pseudorandomFrequency_succDeferral_iff`) — the identification [[faf-map-li]] §5 item 5 records as
unformalized. Consequently, for this `f`, FAF's strengthened `thm:benford` hypothesis is no
weaker than the paper's.

Scope (verbatim, per the mandate): **`succDeferral` only; no monotonicity in `f` claimed.**
`DeferralPatient` compares windows and `DeferralFunction` need not be monotone, so nothing is
stated about other `f`; the two-directional transfer between an arbitrary `f` and the paper's
class is not available from this file (the family of `Family.lean` inhabits all `f` for a
different reason: it defeats every divergent weighting).
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology

/-- **Every divergent weighting is `succDeferral`-patient**: the window `[n, n+1]` has total
weight at most `2`.
Source: mandate T8; FAF `DeferralPatient`, `succDeferral`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem deferralPatient_succDeferral_of_divergent {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P) : DeferralPatient succDeferral W P := by
  refine ⟨2, fun n => ?_⟩
  have hf : (succDeferral : ℕ → ℕ) n = n + 1 := rfl
  rw [hf, Finset.sum_Icc_succ_top (Nat.le_succ n), Finset.Icc_self n, Finset.sum_singleton]
  linarith [(hW.1 n).2, (hW.1 (n + 1)).2]

/-- **T8.** `PseudorandomFrequency truth p succDeferral P` is the paper's `def:pseudorandom`
with frequency `p` over all P-generable divergent weightings.
Scope: `succDeferral` only; no monotonicity in `f` claimed.
Source: mandate T8; [[faf-map-li]] §5 item 5; LI paper `def:pseudorandom` (`main.tex:1273`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem pseudorandomFrequency_succDeferral_iff (truth : ℕ → ℝ) (p : ℝ) (P : History) :
    PseudorandomFrequency truth p succDeferral P ↔
      ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W P →
        weightedAverage (fun i => (W i).denote P) truth ≈ₙ (fun _ => p) := by
  constructor
  · intro h W hWgen hWdiv
    exact h W hWgen hWdiv (deferralPatient_succDeferral_of_divergent hWdiv)
  · intro h W hWgen hWdiv _
    exact h W hWgen hWdiv

/-- The paper's class implies FAF's predicate at **every** `f` (one direction of the general
transfer; the converse at a general `f` is not claimed).
Source: mandate T8
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem pseudorandomFrequency_of_all (truth : ℕ → ℝ) (p : ℝ) (P : History)
    (h : ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W P →
      weightedAverage (fun i => (W i).denote P) truth ≈ₙ (fun _ => p)) :
    ∀ f : DeferralFunction, PseudorandomFrequency truth p f P :=
  fun _ W hWgen hWdiv _ => h W hWgen hWdiv

end Cleanroom.Li.LiPseudorandom
