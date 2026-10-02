import Cleanroom.Info.InfoVoiLatents.Bridge

/-!
# info-voi-latents — Turner's policy-modification corrigibility (Target 12)

Finite human policies `PolH`, AI policies `PolAI`, and a *bridging kernel* `κ : Experiment PolH PolAI` (the
law of the later AI policy given the human policy, at a fixed current state and AI policy — the
conditioning is a parameter, not a variable). **`corrPM κ := sSup {I[fst : snd ; joint p κ] | p ∈
stdSimplex}`**, the channel capacity of the bridging kernel over PFR's `mutualInfo` on the joint
measure of `Bridge.lean`. The set is nonempty (`miSet_nonempty`, the uniform prior) and bounded by
`log |PolAI|` (`mutualInfo_le_log_card`), so the `sSup` is not junk; `corrPM_nonneg`,
**`corrPM_le_log_card`** (property (c)), and **`corrPM_eq_zero_of_const`** (property (a): a kernel
constant in the human policy — the human killed or disabled — has capacity `0`, through the
bridge: every posterior equals the prior). Property (b) (garbling ⇒ ≤) is not done.

The coordinate projections are named `polH`/`polAI` (`fun q => q.1`, `fun q => q.2`): with the bare
`Prod.fst`/`Prod.snd` the `FiniteRange` instance search is stuck on this toolchain (findings F11);
`I[polH : polAI ; μ] = I[Prod.fst : Prod.snd ; μ]` definitionally (`mutualInfo_pol`).

Mandate: Target 12.
-/

namespace Cleanroom.Info.InfoVoiLatents.Turner

open MeasureTheory ProbabilityTheory Finset Real
open Cleanroom.Found.LitDdbFrames.Blackwell Cleanroom.Info.InfoVoiLatents.Voi
open Cleanroom.Info.InfoVoiLatents.Bridge

noncomputable section

set_option linter.unusedSectionVars false

variable {PolH PolAI : Type} [Fintype PolH] [Fintype PolAI] [MeasurableSpace PolH] [MeasurableSpace PolAI]
  [MeasurableSingletonClass PolH] [MeasurableSingletonClass PolAI]

/-- The human-policy coordinate of the joint.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def polH : PolH × PolAI → PolH := fun q => q.1

/-- The AI-policy coordinate of the joint.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def polAI : PolH × PolAI → PolAI := fun q => q.2

/-- `I[polH : polAI ; μ] = I[Prod.fst : Prod.snd ; μ]`, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mutualInfo_pol (μ : Measure (PolH × PolAI)) :
    I[(polH : PolH × PolAI → PolH) : (polAI : PolH × PolAI → PolAI) ; μ] = I[Prod.fst : Prod.snd ; μ] := rfl

/-- The set of mutual informations achievable by a distribution over human policies.
Source: [[turner-2021-formalizing-policy-modification-corrigibility]] l. 62 (the `max` over
`p(Π^human)`)
Kind: D
Fidelity: exact (finite, conditioning fixed) -/
def miSet (κ : Experiment PolH PolAI) : Set ℝ :=
  {x | ∃ (p : PolH → ℝ) (hp : p ∈ stdSimplex ℝ PolH),
    x = I[(polH : PolH × PolAI → PolH) : (polAI : PolH × PolAI → PolAI) ; joint p κ hp]}

/-- **Policy-modification corrigibility** of a bridging kernel: the maximum mutual information
between the human policy and the later AI policy over distributions of human policies — a channel
capacity, over PFR's `mutualInfo`.
Source: [[turner-2021-formalizing-policy-modification-corrigibility]] ll. 60–64 (Definition,
formal); item 057
Kind: D
Fidelity: variant: finite policy sets, the conditioning `(s_t, π^AI_t)` fixed as a parameter -/
def corrPM (κ : Experiment PolH PolAI) : ℝ := sSup (miSet κ)

/-- The uniform distribution over human policies (`PolH` nonempty).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uniform_mem [Nonempty PolH] :
    (fun _ : PolH => (1 : ℝ) / Fintype.card PolH) ∈ stdSimplex ℝ PolH := by
  refine ⟨fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card PolH : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := PolH)
    exact_mod_cast this.ne'
  field_simp

/-- The achievable set is nonempty.
Source: none: infrastructure (Target 12: "say the set is nonempty")
Kind: L
Fidelity: n/a -/
theorem miSet_nonempty [Nonempty PolH] (κ : Experiment PolH PolAI) : (miSet κ).Nonempty :=
  ⟨_, _, uniform_mem, rfl⟩

/-- Every achievable mutual information is at most `log |PolAI|`.
Source: none: infrastructure (Target 12: "prove the bound so `sSup` is not junk")
Kind: P
Fidelity: exact -/
theorem mutualInfo_le_log_card {p : PolH → ℝ} (κ : Experiment PolH PolAI) (hp : p ∈ stdSimplex ℝ PolH) :
    I[(polH : PolH × PolAI → PolH) : (polAI : PolH × PolAI → PolAI) ; joint p κ hp]
      ≤ Real.log (Fintype.card PolAI) := by
  have hH : Measurable (polH : PolH × PolAI → PolH) := measurable_fst
  have hA : Measurable (polAI : PolH × PolAI → PolAI) := measurable_snd
  rw [ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy' hH hA]
  have h1 := condEntropy_nonneg (polAI : PolH × PolAI → PolAI) (polH : PolH × PolAI → PolH) (joint p κ hp)
  have h2 := entropy_le_log_card (polAI : PolH × PolAI → PolAI) (joint p κ hp)
  linarith

/-- Every achievable mutual information is also at most `log |PolH|` — the twin of
`mutualInfo_le_log_card`, from `I ≤ H[polH]`; this is the bound Turner's l. 68 states ("if the
human's action space is impoverished, this decreases the channel capacity").
Source: [[turner-2021-formalizing-policy-modification-corrigibility]] l. 68; audit r1 (fidelity
item 9)
Kind: P
Fidelity: exact -/
theorem mutualInfo_le_log_card_polH {p : PolH → ℝ} (κ : Experiment PolH PolAI)
    (hp : p ∈ stdSimplex ℝ PolH) :
    I[(polH : PolH × PolAI → PolH) : (polAI : PolH × PolAI → PolAI) ; joint p κ hp]
      ≤ Real.log (Fintype.card PolH) := by
  have hH : Measurable (polH : PolH × PolAI → PolH) := measurable_fst
  have hA : Measurable (polAI : PolH × PolAI → PolAI) := measurable_snd
  rw [ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy hH hA]
  have h1 := condEntropy_nonneg (polH : PolH × PolAI → PolH) (polAI : PolH × PolAI → PolAI)
    (joint p κ hp)
  have h2 := entropy_le_log_card (polH : PolH × PolAI → PolH) (joint p κ hp)
  linarith

/-- The achievable set is bounded above.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem miSet_bddAbove (κ : Experiment PolH PolAI) : BddAbove (miSet κ) := by
  refine ⟨Real.log (Fintype.card PolAI), ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact mutualInfo_le_log_card κ hp

/-- Every achievable mutual information is nonnegative (through the bridge: it is an expected
`klFin`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mutualInfo_nonneg' {p : PolH → ℝ} (κ : Experiment PolH PolAI) (hp : p ∈ stdSimplex ℝ PolH) :
    0 ≤ I[(polH : PolH × PolAI → PolH) : (polAI : PolH × PolAI → PolAI) ; joint p κ hp] := by
  rw [mutualInfo_pol, ← sum_klFin_eq_mutualInfo κ hp]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (sigMass_nonneg hp κ s) (klFin_post_nonneg κ hp s)

/-- **(c) `corrPM κ ≤ log |PolAI|`**: the capacity is at most the log of the number of AI policies
— the generic capacity bound (`I ≤ H[polAI] ≤ log |PolAI|`), which the mandate's Target 12(c) asks
for. Turner's l. 68 is about `|Π_H|`; that twin is `corrPM_le_log_card_polH`.
Source: mandate Target 12(c); [[turner-2021-formalizing-policy-modification-corrigibility]]
ll. 60–64 (the capacity definition)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem corrPM_le_log_card [Nonempty PolH] (κ : Experiment PolH PolAI) :
    corrPM κ ≤ Real.log (Fintype.card PolAI) := by
  unfold corrPM
  refine csSup_le (miSet_nonempty κ) ?_
  rintro x ⟨p, hp, rfl⟩
  exact mutualInfo_le_log_card κ hp

/-- **(c′) `corrPM κ ≤ log |PolH|`**: an impoverished human action space caps the capacity —
Turner's l. 68 rendered.
Source: [[turner-2021-formalizing-policy-modification-corrigibility]] l. 68 ("if the human's action
space is impoverished, this decreases the channel capacity"); audit r1 (fidelity item 9)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem corrPM_le_log_card_polH [Nonempty PolH] (κ : Experiment PolH PolAI) :
    corrPM κ ≤ Real.log (Fintype.card PolH) := by
  unfold corrPM
  refine csSup_le (miSet_nonempty κ) ?_
  rintro x ⟨p, hp, rfl⟩
  exact mutualInfo_le_log_card_polH κ hp

/-- `0 ≤ corrPM κ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem corrPM_nonneg [Nonempty PolH] (κ : Experiment PolH PolAI) : 0 ≤ corrPM κ := by
  unfold corrPM
  exact le_csSup_of_le (miSet_bddAbove κ) ⟨_, uniform_mem, rfl⟩ (mutualInfo_nonneg' κ uniform_mem)

/-- **(a) Kill ⇒ 0**: a bridging kernel constant in the human policy (the human cannot affect the
later AI policy) has capacity `0` — every distribution over human policies yields mutual
information `0`, because every positive-mass posterior equals the prior (through the bridge).
Source: [[turner-2021-formalizing-policy-modification-corrigibility]] l. 66 ("if the AI kills or
disables the human before the policy is modified, the agent is totally incorrigible")
Kind: P
Fidelity: exact
Hyps: (a) all — `hconst` is the claim's own antecedent -/
theorem corrPM_eq_zero_of_const [Nonempty PolH] (κ : Experiment PolH PolAI)
    (hconst : ∀ h h' a, κ.k h a = κ.k h' a) : corrPM κ = 0 := by
  have hzero : ∀ (p : PolH → ℝ) (hp : p ∈ stdSimplex ℝ PolH),
      I[(polH : PolH × PolAI → PolH) : (polAI : PolH × PolAI → PolAI) ; joint p κ hp] = 0 := by
    intro p hp
    rw [mutualInfo_pol, ← sum_klFin_eq_mutualInfo κ hp]
    refine Finset.sum_eq_zero fun s _ => ?_
    obtain ⟨h₀⟩ := (inferInstance : Nonempty PolH)
    have hsig : sigMass p κ s = κ.k h₀ s := by
      unfold sigMass
      rw [Finset.sum_congr rfl fun h _ => by rw [hconst h h₀ s], ← Finset.sum_mul, hp.2, one_mul]
    rcases (sigMass_nonneg hp κ s).lt_or_eq with hs | hs
    · have hpost : post p κ s = p := by
        funext w
        unfold post
        rw [hconst w h₀ s, ← hsig]
        exact mul_div_cancel_right₀ _ hs.ne'
      rw [hpost, (klFin_eq_zero_iff hp hp fun _ h => h).2 rfl, mul_zero]
    · rw [← hs, zero_mul]
  have hset : miSet κ = {0} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hzero p hp
    · rintro rfl
      exact ⟨_, uniform_mem, (hzero _ uniform_mem).symm⟩
  unfold corrPM
  rw [hset, csSup_singleton]

end

end Cleanroom.Info.InfoVoiLatents.Turner
