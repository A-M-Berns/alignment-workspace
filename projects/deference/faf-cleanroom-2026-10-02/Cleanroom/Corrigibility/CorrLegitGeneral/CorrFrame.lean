import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Trust.TtFiniteFrames.Partition
import Cleanroom.Found.CorrThreeStep.Identities

/-!
# corr-legit-general — T13: the corrigibility frame under the common-prior reading

ddb-mm-authors T1 asks to build the corrigibility frame (worlds = value hypothesis × the
programmers' credence state × the first action) and conjectures that Theorem 4.1's conditions
hold **iff** the base-rate inequality `α/β ≤ (ε/(1−ε))·(h/c)` holds. Under the common-prior
reading — the programmers' credence at `(ω, o)` is the agent's prior conditioned on the
observation `o` — the frame is `Frame.ofPartition` of the agent's prior along the observation
map, and `tt-finite-frames`' `totalTrust_ofPartition` gives Total Trust for **every** prior with
full support and every observation map, hence for every `(ε, α, β)`: the conjectured "iff" is
refuted (N−: the reading makes the frame a Bayesian refinement, for which trust is automatic).
The surviving neighbour: the base-rate inequality is *which action the trusted expert
recommends* — `corr-three-step`'s `shPolicy_beats_constants_iff_delta_nonneg` (cited). The
reading is one choice among several: ATTRIBUTION-UNVETTED. Under the two-prior reading (the
programmers' credences a free coordinate derived from their own prior) the exact condition is
cross-prior cell agreement, `corrFrame_twoPrior_totalTrust_iff` — again not the base-rate
inequality. The manipulative-`a₁⁻` half and the Bentham embedding (T4) are recorded in the
findings only.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Trust.TtFiniteFrames

noncomputable section

set_option linter.unusedSectionVars false

/-- **The common-prior corrigibility frame is totally trusted unconditionally**: for any prior
`π` with full support on a finite joint space and any observation map `f`, the frame whose row
at `w` is `π(· | f = f w)` is totally trusted by `π` — no base-rate condition is necessary, so
ddb-mm-authors T1's conjectured "iff" fails under this reading.
Source: [[ddb-mm-authors]] T1 l. 138 (conjecture, refuted under the common-prior reading;
ATTRIBUTION-UNVETTED); `totalTrust_ofPartition` (`tt-finite-frames`); corr-wf13-2-063
Kind: N-
Fidelity: variant: common-prior reading of the frame (disclosed)
Hyps: (a) `∀ w, 0 < π w` -/
theorem corrFrame_totalTrust {W ι : Type} [Fintype W] [DecidableEq W] [DecidableEq ι]
    {π : W → ℝ} (hpos : ∀ w, 0 < π w) (f : W → ι) :
    TotalTrust π (Frame.ofPartition π hpos f) :=
  totalTrust_ofPartition hpos f

/-- **The two-prior reading** (T1's own wording, "the programmers' credences as a function of the
world"): with the programmers' credence state at `(ω, o)` the *programmers'* prior `πA`
conditioned on the observation, the agent's prior `πH` totally trusts the frame iff the two
priors' conditional probabilities agree within every observation cell (product form) —
`tt-finite-frames`' `totalTrust_ofPartition_cross_iff`, restated (letters: the dependency reads
`πH` as the deferrer and `πA` as the partition expert's prior with no agent/human assignment;
here `πH` is the agent's prior and `πA` the programmers', the opposite of the dependency's
mnemonic — the condition is symmetric, so nothing turns on it; audit r2 fidelity N7). Under this reading too the
condition is not the base-rate inequality, which is about which action the trusted expert
recommends; so findings F7's conclusion holds under both readings (audit r1 adversarial N5).
Source: [[ddb-mm-authors]] T1 l. 138 (two-prior reading; ATTRIBUTION-UNVETTED);
`totalTrust_ofPartition_cross_iff` (`tt-finite-frames`, trust-lab-064)
Kind: C
Fidelity: variant: two-prior reading of the frame (disclosed)
Hyps: (a) `∀ w, 0 < πH w`, `∀ w, 0 < πA w` (full support, the dependency's standing assumption) -/
theorem corrFrame_twoPrior_totalTrust_iff {W ι : Type} [Fintype W] [DecidableEq W]
    [DecidableEq ι] {πH πA : W → ℝ} (hposH : ∀ w, 0 < πH w) (hposA : ∀ w, 0 < πA w)
    (f : W → ι) :
    TotalTrust πH (Frame.ofPartition πA hposA f) ↔
      ∀ v, πA v * mass πH (Corr.ofMap f v) = πH v * mass πA (Corr.ofMap f v) :=
  totalTrust_ofPartition_cross_iff hposH hposA f

end

end Cleanroom.Corrigibility.CorrLegitGeneral
