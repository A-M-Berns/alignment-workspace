import Cleanroom.Deference.DefFrozenSibling.OnG

/-!
# Audit round 3 (adversarial) probe — pointwise object-level deference *holds* on `G` at the
inhabitant

v6 T5's header reads "the object-level ceiling — forced on **every** fragment", and its statement
says pointwise object-level deference `H⁺_n(P^{(n)}) ≈ₙ a_n` is false. The package renders the
negative off `G` (`pointwise_deference_fails_offG`, at the counter-model where the quote is
wrong). This probe shows the positive on `G`: at `onGSystem` (every day timely, e.c. polarity
pattern) the advised reasoner's price of the contract and the predictor's quote both reach the
decided value, so `H⁺_n(P^{(n)}) ≈ₙ a_n` **holds** along the whole sequence
(`pointwise_deference_holds_onG`). So over FAF the ceiling is fragment-relative — confirmed off
`G`, contradicted on an e.c.-patterned timely fragment — and the source's "on every fragment" is
an overclaim the package's F5 does not record. Not imported by the library.
-/

namespace Cleanroom.Deference.DefFrozenSibling.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- The advised reasoner's own provability induction on the e.c. polarity pattern: at the
inhabitant, `Hplus_n(P^{(n)}) → truthAt n` with no quote involved. -/
theorem Hplus_truth_onG :
    ∀ δ > 0, ∀ᶠ n in atTop,
      |onGSystem.Hplus n (onGSystem.contract n) - (truthAt onGSystem n : ℝ)| ≤ δ := by
  haveI := onGSystem.Hplus_inductor
  have h1 := lic_provind_true onGSystem.Hplus onGSystem.processH _ hpat₁_onG (fun n v hv => by
    by_cases hc : (fun _ : ℕ => 0) n = 0 ∧ truthAt onGSystem n = 1
    · rw [if_pos hc]
      exact (truthAt_holds_H (onG_decidedBy n) hv).2 hc.2
    · rw [if_neg hc]
      exact PCWorld.holds_top v) onGSystem.hworldH
  have h0 := lic_provind_false onGSystem.Hplus onGSystem.processH _ hpat₀_onG (fun n v hv => by
    by_cases hc : (fun _ : ℕ => 0) n = 0 ∧ truthAt onGSystem n = 0
    · rw [if_pos hc, PCWorld.holds_neg]
      intro hh
      have := (truthAt_holds_H (onG_decidedBy n) hv).1 hh
      rw [hc.2] at this
      norm_num at this
    · rw [if_neg hc, PCWorld.holds_neg, PCWorld.holds_neg, not_not]
      exact PCWorld.holds_top v) onGSystem.hworldH
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 h1 δ hδ,
    asympEq_iff_eventuallyWithin.1 h0 δ hδ] with n hn1 hn0
  rcases truthAt_eq_zero_or_one onGSystem n with hz | ho
  · rw [if_pos ⟨rfl, hz⟩] at hn0
    rw [hz]
    simpa using hn0
  · rw [if_pos ⟨rfl, ho⟩] at hn1
    rw [ho]
    simpa using hn1

/-- **Pointwise object-level deference holds at the inhabitant**: `H⁺_n(P^{(n)}) ≈ₙ a_n` on the
whole (timely) sequence — the negation of what v6 T5 says is forced on every fragment. -/
theorem pointwise_deference_holds_onG :
    (fun n => onGSystem.Hplus n (onGSystem.contract n)) ≈ₙ (fun n => (onGSystem.a n : ℝ)) := by
  refine asympEq_iff_eventuallyWithin.2 fun δ hδ => ?_
  filter_upwards [Hplus_truth_onG (δ / 2) (half_pos hδ),
    engineA_truth_onG (δ / 2) (half_pos hδ)] with n h1 h2
  have h2' : |(onGSystem.a n : ℝ) - (truthAt onGSystem n : ℝ)| ≤ δ / 2 := h2
  calc |onGSystem.Hplus n (onGSystem.contract n) - (onGSystem.a n : ℝ)|
      = |(onGSystem.Hplus n (onGSystem.contract n) - (truthAt onGSystem n : ℝ)) +
          ((truthAt onGSystem n : ℝ) - (onGSystem.a n : ℝ))| := by ring_nf
    _ ≤ |onGSystem.Hplus n (onGSystem.contract n) - (truthAt onGSystem n : ℝ)| +
          |(truthAt onGSystem n : ℝ) - (onGSystem.a n : ℝ)| := abs_add_le _ _
    _ ≤ δ / 2 + δ / 2 := by
        refine add_le_add h1 ?_
        rw [abs_sub_comm]
        exact h2'
    _ = δ := by ring

end Cleanroom.Deference.DefFrozenSibling.AuditR3
