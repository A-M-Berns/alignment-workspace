import Cleanroom.Fa.FaTheoremA.Half1
import LogicalInduction.Properties.Pseudorandomness
import LogicalInduction.Properties.ExpectationProperties

/-!
# `fa-theorem-a` · Errata: the LI-paper errata and the mis-cited engine, as FAF facts (T9)

Recorded here with the sources quoted; the findings rows are in [[fa-theorem-a-findings]].

* **PE2** (root-fa-011, vq-wiki-040, lean-deference-040). FAF's
  `LUVCombination.BoundedSequence.recurringunbiasednessexp` takes a bare
  `PGenerableWeighting`/`DivergentWeighting` and **no deferral function** — its docstring: "One
  printed premise is deliberately dropped … a transposition … Recorded as PE2". The clause
  belongs on `thm:wubexp` (`BoundedSequence.wubexp`, which carries `hstrict`, `hsupport`, `emit`,
  `bridge`). The corpus's corrected reading and FAF's agree; `pe2_engine_has_no_deferral` is the
  record: Half 1's engine stated with no `DeferralFunction` in scope at all.
* **PE5** (root-fa-012, root-fa-2-001, vq-wiki-041). FAF's `VariedPseudorandomAbove truth p f P`
  is `PseudorandomAbove (fun n ↦ truth n − p n) f P`: "above" means weighted truth frequency
  `≳ p` — appendix D.7's convention, opposite to the printed Def 4.4.4 numerator.
  `varied_above_unfold` (`Iff.rfl`) names the convention; any one-sided use in the run cites it.
* **Fired-element timing** (root-fa-2-002). FAF's `FeedbackTruthSequence.feedback_price`:
  `(sequence (f (k+1))).price P (f (k+1)) = (As (f k)).price P (f (k+1)) − truth (f k)` — the
  "`Val(B_{f(k)})` available by day `f(k+1)`" reading. Recorded; nothing to prove.
* **The mis-cited engine** (root-fa-010). FA §4 (II) applies `wubexp` (4.8.16) "for any
  𝒞_A-generable divergent weighting `w_n` that is patient", and §8 instantiates it at the gate
  `w_n = Ind_δ(a_n > t)` — a weighting with **no support restriction** (it fires wherever `A`
  quotes above `t`). `wubexp`'s actual premise `hsupport : WeightingSupportedOnDeferralImage
  W P f` confines the support to `image f`. The checked record is the simplest unrestricted
  weighting, `w ≡ 1`: `not_supported_const_one` (day `0` is not `f k` for any `k`, since
  `f k > k ≥ 0`). FA never uses `w ≡ 1` itself ("everywhere-supported" in root-fa-010 means
  *not confined to a deferral image*, not *identically one*); whether FA's own ramp's realized
  support meets the clause depends on `A`'s prices and is not formalized — root-fa-010 calls
  it "a modelling observation, not a theorem" — the ramp fails `hsupport` exactly when it fires
  on a day off `image f`. "Patient" (`DeferralPatient`) is the hypothesis of the *learning*
  family (`PseudorandomAbove`), not of `wubexp`. Severity: blocking for FA §5 as argued
  (already retracted by the corpus; this is the formal record, by a stand-in).
* **Rate-free grounding** (lean-deference-062): literature, outside the materials; recorded in
  the findings only.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **PE2, the record.** Half 1's engine (`engine_no_persistent_bias_general`, root-fa-025's
"M") restated: its statement mentions no `DeferralFunction` — FAF's
`recurringunbiasednessexp` takes a bare generable divergent weighting, the printed
support-in-image clause being a transposition from `thm:wubexp` (FAF's docstring, PE2 in its
`notes/paper-errata.md`). Kind L: the content is `engine_no_persistent_bias_general`'s; this
declaration exists so that the absence of `f` is a checked fact about a named statement.
Source: root-fa-011; vq-wiki-040; lean-deference-040; [[li-paper-erratum]] §1; FAF `thm:recurringunbiasednessexp` docstring
Kind: L
Fidelity: exact
Hyps: (a) as `engine_no_persistent_bias_general` -/
theorem pe2_engine_has_no_deferral {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {As : ℕ → LUVCombination}
    (h : LUVCombination.BoundedSequence As P) (hvalued : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W P) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P) (fun i => (As i).expect P i) truth) 0 :=
  LUVCombination.BoundedSequence.recurringunbiasednessexp h hvalued hdet hW hdiv hworld

/-- **PE5, the record.** FAF's "varied pseudorandom above `p`" is pseudorandomness of the centered
truth `truth − p` against patient generable divergent weightings: weighted truth frequency `≳ p`
(appendix D.7's convention), opposite to the printed Def 4.4.4's numerator. `Iff.rfl`.
Source: root-fa-012; root-fa-2-001; vq-wiki-041; [[li-paper-erratum]] §2; FAF `Properties/Pseudorandomness.lean` (`VariedPseudorandomAbove`, "PE5 in `notes/paper-errata.md`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem varied_above_unfold (truth : ℕ → ℝ) (p : ℕ → ℚ) (f : DeferralFunction) (P : History) :
    VariedPseudorandomAbove truth p f P ↔
      PseudorandomAbove (fun n => truth n - (p n : ℝ)) f P :=
  Iff.rfl

/-- **The mis-cited engine (root-fa-010), the stand-in record.** FA §4 (II)/§8's gate
`Ind_δ(a_n > t)` carries no support restriction; the simplest such weighting, `w ≡ 1`, already
fails `wubexp`'s `hsupport : WeightingSupportedOnDeferralImage W P f` for every deferral
function: day `0` has weight `1 ≠ 0` but is not `f k` for any `k`, since `f k > k ≥ 0`. This is
a *stand-in* for FA's weighting, which is the ramp, not the constant `1`; whether FA's own
gate's realized support lies in `image f` depends on `A`'s prices and is not formalized
(root-fa-010: "a modelling observation, not a theorem"). The engine an unrestricted gate can
use is `recurringunbiasednessexp` (4.8.15, no support clause) — which is what this package does.
Source: root-fa-010 (FA §4 (II)/§8's ingredient (II) mis-citation; the constant-`1` stand-in is this package's); FAF `WeightingSupportedOnDeferralImage`
Kind: L
Fidelity: weaker: constant-`1` stand-in for FA's ramp `Ind_δ(a_n > t)`; the claim about FA's own gate is prose (root-fa-010, [[fa-positive-results-corrected-v2]] §2.4)
Hyps: (a) none -/
theorem not_supported_const_one (P : History) (f : DeferralFunction) :
    ¬ WeightingSupportedOnDeferralImage (fun _ => EF.const 1) P f := by
  intro h
  obtain ⟨k, hk⟩ := h 0 (by simp)
  have := f.lt k
  omega

end Cleanroom.Fa.FaTheoremA
