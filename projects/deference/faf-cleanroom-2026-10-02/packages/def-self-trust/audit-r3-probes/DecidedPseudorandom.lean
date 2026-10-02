import Cleanroom.Deference.DefSelfTrust.Pseudorandom

/-!
# Audit probe (def-self-trust, round 3, adversarial): the family of record is a *decided* source in the header's own sense

The `Witness.lean` header, `theoremB`'s docstring, the `RobustSelfTrust.lean` header, the report
(§ Target 6, 6e; "Not done") and the ledger (load-bearing row 4) all state: "on *any* decided
source (payout `∈ {0,1}` in every world) Theorem B is `provind`-implied for every forecast, so a
content-exercising inhabitant needs an *undecided* source — the pseudorandom family over T7".

This file checks the two halves of that sentence against each other. The family of record
`atomFamily a` over `atomDP a (truthStar a g p) g` **is** a decided source in exactly the
sense the sentence defines (`truthStar_source_decided`: payout `0` or `1` in every
completed-theory world — FAF's `TheoryTruth` plus `truthR_bool`), and the package's own
`truthStar_uniformAccuracy_false` says the price does **not** track that decided payout
(`decided_but_not_tracked`, under the T7 binder exactly as the package takes it). So "decided"
cannot be the criterion that makes Theorem B `provind`-implied: what the parity source has and
the pseudorandom family lacks is a decision pattern that `thm:provind` can reach (the
theorem-days and the refutable-days are each e.c. families). The grades the sentence justifies
(N− on both parity inhabitants) are right; the reason given is false as a generality and
contradicts the witness it names. Not imported by the library.
-/

namespace Cleanroom.AuditProbe.DefSelfTrust.DecidedPseudorandom

open LogicalInduction Filter Topology
open Cleanroom.Li.LiPseudorandom Cleanroom.Deference.DefSelfTrust

/-- The family of record is decided: in every completed-theory world of its deductive process
the payout of `atomFamily a n` is `0` or `1`. -/
theorem truthStar_source_decided (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : ℝ) :
    ∀ n (v : PCWorld), v.ConsistentWithTheory (atomDP a (truthStar a g p) g) →
      v.payout (atomFamily a n) = 0 ∨ v.payout (atomFamily a n) = 1 := by
  intro n v hv
  rw [truthStar_theoryTruth a g hg p n v hv]
  exact truthR_bool _ n

/-- Decided, yet not tracked: the same source is one on which (under li-pseudorandom's OPEN T7
instance, taken as a binder exactly as the package does) the price does not converge to the
decided payout — the package's own `truthStar_uniformAccuracy_false`. -/
theorem decided_but_not_tracked (a g : ℕ → ℕ) (ha : Function.Injective a)
    (hg : ∀ j, j < g j) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hcodes : MachineSentenceCodes (atomFamily a))
    [IsLogicalInductor (liaHistory (atomDP a (truthStar a g p) g)) (atomDP a (truthStar a g p) g)] :
    (∀ n (v : PCWorld), v.ConsistentWithTheory (atomDP a (truthStar a g p) g) →
        v.payout (atomFamily a n) = 0 ∨ v.payout (atomFamily a n) = 1) ∧
      ¬ (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
        |liaHistory (atomDP a (truthStar a g p) g) n (atomFamily a n) -
          truthR (truthStar a g p) n| < ε) :=
  ⟨truthStar_source_decided a g hg p,
    truthStar_uniformAccuracy_false a g ha hg hp0 hp1 hcodes⟩

end Cleanroom.AuditProbe.DefSelfTrust.DecidedPseudorandom
