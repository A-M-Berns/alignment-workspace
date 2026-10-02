import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Found.LitDdbFrames.Value
import Cleanroom.Lit.LitDdbFacts.Collected
import Cleanroom.Lit.LitDdbAccuracyMm.Accuracy
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Value
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Theorem34
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Refute
import Cleanroom.Lit.LitWeathersonFrames.Composite
import Cleanroom.Corrigibility.CorrGeneralObject.Faking

/-!
# corr-legit-general — T12: the imported theorems, grade (a)

Restatements in this namespace, by one-line proofs, of the theorems the corrigibility workflows
cite as [reported]: DDB 2.2, 4.1, 5.1, 3.2; MM 3.2, 3.4 (with the refutation of its forward
direction without type-measurability); Weatherson's Coin/Bentham status and the countable-frame
status of Theorem 2.2; probe-blindness (`no_separation_of_same_law`). The brain-reader separation
(`corr-channel-voi`'s `brainReader_separation`) is cited in the ledger and not restated: its
statement is a conjunction over the dictionary's four buttons with eight explicit parameters,
and restating it adds nothing a `cited (a)` row does not say. Each row of the ledger reads
`cited (a)`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbFacts Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- DDB Theorem 2.2: Value ⟺ Total Trust.
Source: [[Deference Done Better]] §2 Theorem 2.2 l. 186; `lit-ddb-frames` (`value_iff_totalTrust`)
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem ddb_thm22 {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    Value π F ↔ TotalTrust π F :=
  value_iff_totalTrust hπ F

/-- DDB Theorem 4.1: Total Trust ⟺ hull and modest informedness.
Source: [[Deference Done Better]] §4 Theorem 4.1 l. 327; `lit-ddb-frames`
(`totalTrust_iff_hullAndModestlyInformed`)
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem ddb_thm41 {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    TotalTrust π F ↔ HullAndModestlyInformed π F :=
  totalTrust_iff_hullAndModestlyInformed hπ F

/-- DDB Theorem 5.1: the six-way characterization of Value.
Source: [[Deference Done Better]] §5 Theorem 5.1 l. 375; `lit-ddb-facts` (`tfae_thm51`)
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem ddb_thm51 {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    List.TFAE [Value π F,
      ¬ ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
        FixedOptionBook π F 𝒪₁ 𝒪₂ O S SureLoss,
      TotalTrust π F, TotalTrustBiconvex π F, HullAndModestlyInformed π F, LambdaForm π F] :=
  tfae_thm51 hπ F

/-- DDB Theorem 3.2: Total Trust on `X` ⟺ epistemic value on `X` (local in `X`).
Source: [[Deference Done Better]] §3 Theorem 3.2 l. 271; `lit-ddb-accuracy-mm`
(`totalTrustOn_iff_epistemicValueOn`)
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem ddb_thm32 {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    TotalTrustOn X π F ↔ EpistemicValueOn X π F :=
  totalTrustOn_iff_epistemicValueOn hπ F

/-- MM Theorem 3.2 (cellwise): Value ⟺ Total Trust, restating DDB 2.2.
Source: [[mm]] I5.1 l. 146 (MM Thm 3.2); `lit-ddb-accuracy-mm` (`MM.mm_theorem32_cell`)
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W` -/
theorem mm_thm32 {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    Value π F ↔ TotalTrust π F :=
  MM.mm_theorem32_cell hπ F

/-- MM Theorem 3.4: under clarity and richness, Value of every type-measurable behaviour ⟺
strict agreement.
Source: [[mm]] I9.3 l. 188 ("MM 3.4's half"); `lit-ddb-accuracy-mm`
(`MM.typeMeasurable_valuesB_iff_strictAgree`)
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W`, `Clarity G`, `Richness G` -/
theorem mm_thm34 {C : Type} [Fintype C] [DecidableEq C] [Nonempty C] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) {G : MM.GFrame W C} (hcl : MM.Clarity G) (hri : MM.Richness G) :
    (∀ B, MM.TypeMeasurable G B → MM.IsBehaviour G B → MM.ValuesB π G B) ↔ MM.StrictAgree π G :=
  MM.typeMeasurable_valuesB_iff_strictAgree hπ hcl hri

/-- MM Theorem 3.4's forward direction without type-measurability is refuted.
Source: `lit-ddb-accuracy-mm` (`MM.mm34_forward_refuted`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem mm_thm34_forward_refuted :
    MM.IsBehaviour MM.G2 MM.B2 ∧ MM.ValuesB MM.π2 MM.G2 MM.B2 ∧
      MM.StochasticChoiceU MM.G2 MM.π2 MM.B2 ∧ MM.StochasticChoiceV MM.G2 MM.π2 MM.B2 ∧
      MM.Clarity MM.G2 ∧ MM.Richness MM.G2 ∧ MM.ConstantActs MM.G2 ∧
      ¬ MM.StrictAgree MM.π2 MM.G2 :=
  MM.mm34_forward_refuted

/-- Weatherson's Coin frame: Total Trust holds and Value fails for an infinite menu of
non-uniformly-bounded integrable options, while finite-menu and bounded Value hold.
Source: [[legitimacy]] R1 l. 44 ("fails both ways for countable W (Weatherson)");
`lit-weatherson-frames` (`Coin.status`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem weatherson_coin :
    Cleanroom.Lit.LitWeathersonFrames.TotalTrustInt Cleanroom.Lit.LitWeathersonFrames.Coin.π
        Cleanroom.Lit.LitWeathersonFrames.Coin.frame ∧
      ¬ Cleanroom.Lit.LitWeathersonFrames.ValueInt Cleanroom.Lit.LitWeathersonFrames.Coin.π
        Cleanroom.Lit.LitWeathersonFrames.Coin.frame ∧
      Cleanroom.Lit.LitWeathersonFrames.ValueFinInt Cleanroom.Lit.LitWeathersonFrames.Coin.π
        Cleanroom.Lit.LitWeathersonFrames.Coin.frame ∧
      Cleanroom.Lit.LitWeathersonFrames.ValueBdd Cleanroom.Lit.LitWeathersonFrames.Coin.π
        Cleanroom.Lit.LitWeathersonFrames.Coin.frame :=
  ⟨Cleanroom.Lit.LitWeathersonFrames.Coin.status.1, Cleanroom.Lit.LitWeathersonFrames.Coin.status.2.1,
    Cleanroom.Lit.LitWeathersonFrames.Coin.status.2.2.1,
    Cleanroom.Lit.LitWeathersonFrames.Coin.status.2.2.2.1⟩

/-- Weatherson's Bentham frame is valued and totally trusted (positive-mass convention): the
premise of ddb-mm-authors T4 ("Value holds, Total Trust fails") is the null-event artifact.
Source: [[ddb-mm-authors]] T4 l. 143; mandate Known issues 9; `lit-weatherson-frames`
(`Bentham.status`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem weatherson_bentham :
    Cleanroom.Lit.LitWeathersonFrames.ValueFinInt Cleanroom.Lit.LitWeathersonFrames.Bentham.π
        Cleanroom.Lit.LitWeathersonFrames.Bentham.frame ∧
      Cleanroom.Lit.LitWeathersonFrames.ValueBdd Cleanroom.Lit.LitWeathersonFrames.Bentham.π
        Cleanroom.Lit.LitWeathersonFrames.Bentham.frame ∧
      Cleanroom.Lit.LitWeathersonFrames.TotalTrustC Cleanroom.Lit.LitWeathersonFrames.Bentham.π
        Cleanroom.Lit.LitWeathersonFrames.Bentham.frame ∧
      Cleanroom.Lit.LitWeathersonFrames.TotalTrustInt Cleanroom.Lit.LitWeathersonFrames.Bentham.π
        Cleanroom.Lit.LitWeathersonFrames.Bentham.frame :=
  ⟨Cleanroom.Lit.LitWeathersonFrames.Bentham.status.1,
    Cleanroom.Lit.LitWeathersonFrames.Bentham.status.2.1,
    Cleanroom.Lit.LitWeathersonFrames.Bentham.status.2.2.1,
    Cleanroom.Lit.LitWeathersonFrames.Bentham.status.2.2.2.1⟩

/-- Value ⟹ Total Trust on every countable frame (the direction that never fails).
Source: `lit-weatherson-frames` (`thm22_countable_status`, fourth clause)
Kind: C
Fidelity: exact
Hyps: (a) `IsDist π`, `ValueBdd π F` -/
theorem weatherson_value_imp_totalTrust (V : Type) (π : V → ℝ)
    (F : Cleanroom.Lit.LitWeathersonFrames.CFrame V)
    (hπ : Cleanroom.Lit.LitWeathersonFrames.IsDist π)
    (hV : Cleanroom.Lit.LitWeathersonFrames.ValueBdd π F) :
    Cleanroom.Lit.LitWeathersonFrames.TotalTrustC π F :=
  Cleanroom.Lit.LitWeathersonFrames.thm22_countable_status.2.2.2 V π F hπ hV

/-- Probe-blindness: if the probe feature law equals the live one, no feature separates them.
Source: corr-wf14b-2-008; `corr-general-object` (`no_separation_of_same_law`)
Kind: C
Fidelity: exact
Hyps: (a) `hsame` -/
theorem probe_blind {F : Type} [Fintype F] (J : FactoredSpaces.Distr (F × Bool))
    (hsame : ∀ f, J.mass (f, true) * (∑ f', J.mass (f', false)) =
      J.mass (f, false) * (∑ f', J.mass (f', true))) :
    ¬ ∃ f₀, Cleanroom.Corrigibility.CorrGeneralObject.Separates J f₀ :=
  Cleanroom.Corrigibility.CorrGeneralObject.no_separation_of_same_law J hsame

end

end Cleanroom.Corrigibility.CorrLegitGeneral
