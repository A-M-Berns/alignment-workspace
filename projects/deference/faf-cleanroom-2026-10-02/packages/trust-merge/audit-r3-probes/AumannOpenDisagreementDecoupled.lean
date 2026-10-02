import Cleanroom.Trust.TrustMerge.Hop2
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.Coherence

/-!
# trust-merge · audit r3 (adversarial) probe: the T9(3) OPEN's disagreement conjunct is decoupled

`li_aumann_failure_open` (`Hop2.lean`) ends in `¬ ((fun n => B.H n φ) ≈ₙ (fun n => B.A n φ))`.
`A n φ` — `A`'s own price of `φ` — occurs in none of the five preceding conjuncts: the tracking
clauses are about the merge estimate `B.est` and `H`'s deferred price `B.μ`, and nothing in the
bundle quotes `A`'s own price of `φ` into `H`'s language. So the disagreement conjunct is
satisfied by any mechanism that moves `A`'s price of `φ` away from `H`'s — for instance `A`'s
process refuting `φ` while `H`'s leaves it undecided: this probe shows that from the OPEN's own
undecidedness clause for `H` (non-dogmatism, `lic_nonDogmatism`) and `A n φ → 0` (FAF's
`lic_disprovable_tendsto_zero` when `A`'s process disproves `φ`), the final conjunct follows. No
knowledge of anybody's estimate is involved — which is the content the source's conjecture
(trust-lab-2-022: "each `≂ₙ`-knows the other's estimate, yet they differ") is about. One claim;
not imported by the library.
-/

namespace Cleanroom.Trust.TrustMerge.AuditR3

open LogicalInduction Filter Topology
open Cleanroom.Trust.TrustMerge

/-- From `φ` undecided (positively) in `H`'s process at every stage — the OPEN's own second
conjunct — and `∼φ` in `A`'s process at some stage (so `A n φ → 0` by `thm:lc`), the OPEN's
disagreement conjunct holds outright. -/
theorem disagreement_of_disproved_elsewhere (B : MergeBundle) (φ : Sentence)
    (hund : ∀ n, ∃ v : PCWorld, v.ConsistentWith (B.DPH.D n) ∧ v.Holds φ)
    (hdis : ∃ k, (∼φ) ∈ (mirrorProcess B.M B.X B.f B.baseA B.σ).D k) :
    ¬ ((fun n => B.H n φ) ≈ₙ (fun n => B.A n φ)) := by
  haveI := B.H_inductor
  haveI := B.A_inductor
  have hA : Tendsto (fun n => B.A n φ) atTop (𝓝 0) :=
    lic_disprovable_tendsto_zero B.A _ φ hdis B.A_hworld
  intro h
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism B.H B.DPH φ hund
  unfold AsympEq at h
  have hH : Tendsto (fun n => B.H n φ) atTop (𝓝 (0 + 0)) :=
    (h.add hA).congr (fun n => by ring)
  rw [zero_add] at hH
  have hclose : ∀ᶠ n in atTop, B.H n φ < ε / 2 :=
    hH.eventually (gt_mem_nhds (by linarith))
  obtain ⟨n, h1, h2⟩ := (hev.and hclose).exists
  linarith

end Cleanroom.Trust.TrustMerge.AuditR3
