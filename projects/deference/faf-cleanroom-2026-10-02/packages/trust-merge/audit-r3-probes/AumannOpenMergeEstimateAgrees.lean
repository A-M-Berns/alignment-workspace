import Cleanroom.Trust.TrustMerge.Hop2
import LogicalInduction.Properties.Coherence

/-!
# trust-merge · audit r3 (adversarial) probe: the merge-estimate reading of the T9(3) OPEN is refuted

`li_aumann_failure_open` (`Hop2.lean`) tracks the *merge estimate* `B.est n = 𝔼^A_n(α_{0,n})`
(`B.est ≈ₙ B.μ`, `𝔼^H(β) ≈ₙ B.est`) but states the disagreement about `A`'s *own* price
`A n φ`, which no clause mentions. The mandate's T9(3) ("each's expectation of the other's
estimate `≈ₙ` it, yet their estimates do not `≈ₙ` agree") read over the bundle — where `A`'s
estimate of `φ` is the merge estimate — would end in `¬ (H n φ ≈ₙ B.est n)`. This probe shows
that reading is **refuted** by FAF's convergence theorem (`lic_price_convergesTo`, `thm:con`):
for a constant sentence family, `B.est ≈ₙ B.μ = H_{f n}(φ)` and `H n φ − H_{f n}(φ) → 0`, so
`H n φ ≈ₙ B.est n`. Hence the typed `A n φ` is the only non-refuted choice of conclusion over
the bundle, and it is decoupled from every tracking clause (second probe). One claim; not
imported by the library.
-/

namespace Cleanroom.Trust.TrustMerge.AuditR3

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Trust.TrustMerge

/-- Over any merge bundle on a constant sentence family, per-day tracking of `H`'s deferred
price by the merge estimate forces `H`'s same-day price to agree with the merge estimate:
`B.est ≈ₙ B.μ → (H n φ) ≈ₙ (B.est n)`, by LI convergence. -/
theorem mergeEstimate_reading_agrees (B : MergeBundle) (φ : Sentence)
    (hX : B.X = fun _ => literalIndicator φ)
    (htrack : (fun n => B.est n) ≈ₙ (fun n => B.μ n)) :
    (fun n => B.H n φ) ≈ₙ (fun n => B.est n) := by
  haveI := B.H_inductor
  obtain ⟨L, hL⟩ := lic_price_convergesTo B.H B.DPH φ B.H_hworld
  have hμ : (fun n => B.μ n) = fun n => B.H (B.f.f n) φ := by
    funext n
    show (B.X n).expect B.H (B.f.f n) = _
    rw [hX]
    exact literalIndicator_expect _ _ _
  have hf : Tendsto B.f.f atTop atTop :=
    tendsto_atTop_mono (fun n => (B.f.lt n).le) tendsto_id
  have h2 : Tendsto (fun n => B.H (B.f.f n) φ) atTop (𝓝 L) := hL.comp hf
  have h3 : (fun n => B.H n φ) ≈ₙ (fun n => B.μ n) := by
    rw [hμ]
    unfold AsympEq
    simpa using hL.sub h2
  exact h3.trans htrack.symm

end Cleanroom.Trust.TrustMerge.AuditR3
