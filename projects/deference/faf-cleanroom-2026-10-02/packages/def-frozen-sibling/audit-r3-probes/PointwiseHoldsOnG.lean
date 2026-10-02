import Cleanroom.Deference.DefFrozenSibling.OnG

/-!
# Audit round 3 (fidelity) probe — pointwise object-level deference HOLDS on `G` at the inhabitant

Bearing: the ledger row and docstring of `pointwise_deference_fails_offG` (repair round 2) read
v6 T5 as "pointwise object-level deference `H⁺_n(P^{(n)}) ≈ₙ a_n` is false" and say the source's
*claim* is confirmed by a witness off `G`. The source's T5 header says the ceiling is "forced on
every fragment" and its net status lists T5 among the results "forced outright". Here: at
`onGSystem` (every day on `G`), pointwise object-level deference *holds* — the advised reasoner's
own provability induction reaches the decided value on each polarity subfamily (the H-side twin of
`engineA_truth_ofPattern`), and the quote reaches it too (`engineA_truth_onG_noHz`). So over FAF
the ceiling is an off-`G` phenomenon (a non-forcing, not an impossibility): the source's "on every
fragment" is contradicted on `G` by its own T3 at `w ≡ 1`, and `pointwise_deference_fails_offG`
confirms only that pointwise deference is *not forced* off `G`, not that "no quote can match".

(Filed under this name because a parallel round-3 probe with the name `PointwiseOnG.lean` was
written into the same directory by another auditor; that file is not mine and was not read.)

Not imported by the library.
-/

namespace Cleanroom.Deference.DefFrozenSibling.AuditR3Fidelity

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- The advised reasoner's own provability induction along `G'` under the two polarity
certificates: the H-side twin of `engineA_truth_ofPattern` (no `hz`, no quote).
Source: audit probe. Kind: C. Fidelity: n/a -/
theorem hplus_truth_ofPattern (S : FrozenSystem) (ε : ℕ → ℚ) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n)
    (hpat₁ : MachineSentenceCodes
      (fun n => if t n = 0 ∧ truthAt S n = 1 then S.contract n else ⊤))
    (hpat₀ : MachineSentenceCodes
      (fun n => if t n = 0 ∧ truthAt S n = 0 then S.contract n else ∼(⊤ : Sentence))) :
    AgreeAlong t (fun n => S.Hplus n (S.contract n)) (fun n => (truthAt S n : ℝ)) := by
  haveI := S.Hplus_inductor
  have h1 := lic_provind_true S.Hplus S.processH _ hpat₁ (fun n v hv => by
    by_cases hc : t n = 0 ∧ truthAt S n = 1
    · rw [if_pos hc]
      exact (truthAt_holds_H (hG n hc.1).1 hv).2 hc.2
    · rw [if_neg hc]
      exact PCWorld.holds_top v) S.hworldH
  have h0 := lic_provind_false S.Hplus S.processH _ hpat₀ (fun n v hv => by
    by_cases hc : t n = 0 ∧ truthAt S n = 0
    · rw [if_pos hc, PCWorld.holds_neg]
      intro hh
      have := (truthAt_holds_H (hG n hc.1).1 hv).1 hh
      rw [hc.2] at this
      norm_num at this
    · rw [if_neg hc, PCWorld.holds_neg, PCWorld.holds_neg, not_not]
      exact PCWorld.holds_top v) S.hworldH
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 h1 δ hδ,
    asympEq_iff_eventuallyWithin.1 h0 δ hδ] with n hn1 hn0 h0t
  rcases truthAt_eq_zero_or_one S n with hz | ho
  · rw [if_pos ⟨h0t, hz⟩] at hn0
    rw [hz]
    simpa using hn0
  · rw [if_pos ⟨h0t, ho⟩] at hn1
    rw [ho]
    simpa using hn1

/-- **Pointwise object-level deference holds at `onGSystem`**: `H⁺_n(P^{(n)}) ≈ₙ a_n` on every
day — the negation of the shape `pointwise_deference_fails_offG` refutes off `G`.
Source: audit probe. Kind: N+. Fidelity: n/a -/
theorem pointwise_deference_holds_onG :
    (fun n => liaHistory DPH0' n (contract5 n)) ≈ₙ fun n => (a0 n : ℝ) := by
  have hH := hplus_truth_ofPattern onGSystem (fun _ => 0) hG_onG hpat₁_onG hpat₀_onG
  have hA := engineA_truth_onG_noHz
  rw [asympEq_iff_eventuallyWithin]
  intro δ hδ
  filter_upwards [hH (δ / 2) (half_pos hδ), hA (δ / 2) (half_pos hδ)] with n hn1 hn2
  have h1 : |liaHistory DPH0' n (contract5 n) - (truthAt onGSystem n : ℝ)| ≤ δ / 2 := hn1 rfl
  calc |liaHistory DPH0' n (contract5 n) - (a0 n : ℝ)|
      ≤ |liaHistory DPH0' n (contract5 n) - (truthAt onGSystem n : ℝ)| +
          |(a0 n : ℝ) - (truthAt onGSystem n : ℝ)| := by
        rw [abs_sub_comm (a0 n : ℝ)]
        exact abs_sub_le _ _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add h1 hn2
    _ = δ := by ring

end Cleanroom.Deference.DefFrozenSibling.AuditR3Fidelity
