import Cleanroom.Udt.UdtCondenseDd.Bridge
import Cleanroom.Udt.UdtCommTrust.Count
import Condensation.Comparison

/-!
# `Cleanroom.Udt.UdtCondenseDd.Correspond`: the "correspondence theorem for agency" (T8)

Work package `udt-condense-dd`, target T8 (udt-rep-040, 2-029, 2-030). The note's sentence, quoted
per plan §0.4 rule 3 ([[condensation-connection-attempt]] lines 100–105): "Under the right
conditions: 1. Both models have determination: H(A_i | Π_k, O_i) = 0; 2. Observations have
sufficient coverage; 3. Both policies are recoverable. **Then Π₁ = Π₂ — they must agree on the
policy.**"

* `CorpusAgencyAttribution`: the note's two formal conditions — determination (each action is a.e.
  a function of the attributed policy and the observation) and recoverability (the policy is a.e. a
  function of the behaviour tuple). "Coverage" has no formal content in the note (recorded in the
  findings).
* `agency_correspondence_fails` (T8(a), load-bearing 4): the conclusion is **false** without a
  minimality premise — two attributions of the same behaviour satisfy both conditions and the second
  is not a function of the first (`Pol₂ = (Pol₁, one extra bit)` on a four-point uniform space).
* `agency_correspondence_of_perfectlyCondenses` (T8(b)): the nearest true statement, FAF's Theorem
  4.15 (`aeFunctionOf_jointAbove_of_perfectlyCondenses`) for two latent models of the behaviour
  random variable model `X i = (O i, B i)` that both *perfectly condense* it, on any amalgamation.
  Eisenstat's hypothesis is perfect condensation, which the corpus's two conditions do not imply
  (`Latent.lean`, `Markov.lean`: even DD does not).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust MeasureTheory ProbabilityTheory Finset
open Condensation

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The corpus's hypothesis package -/

section Corpus

variable {I Ω ObsT ActT PolT : Type} [MeasurableSpace Ω] [MeasurableSpace ObsT]
  [MeasurableSpace ActT] [MeasurableSpace PolT]

/-- The behaviour tuple `ω ↦ (i ↦ (O i ω, B i ω))`.
Source: [[condensation-connection-attempt]] lines 101–103 ("behavior")
Kind: D
Fidelity: exact
Hyps: n/a -/
def behaviourTuple (O : I → Ω → ObsT) (B : I → Ω → ActT) (ω : Ω) : I → ObsT × ActT :=
  fun i => (O i ω, B i ω)

/-- **The corpus's "good agency attribution"**: determination `H(A_i | Π, O_i) = 0` (each action a.e.
a function of policy and observation) and recoverability `H(Π | behaviour) ≈ 0`, read as `= 0` (the
policy a.e. a function of the behaviour tuple). The note's "coverage" condition has no formal
content and is not modelled.
Source: [[condensation-connection-attempt]] lines 100–105, 144–146; [[agency-as-condensation]] lines 230–231 (udt-rep-040)
Kind: D
Fidelity: exact for the two formal conditions; "coverage" omitted (no content); "≈ 0" read as "= 0" (ATTRIBUTION-UNVETTED)
Hyps: n/a -/
def CorpusAgencyAttribution (μ : Measure Ω) (Pol : Ω → PolT) (O : I → Ω → ObsT)
    (B : I → Ω → ActT) : Prop :=
  (∀ i, AEFunctionOf (fun ω => (Pol ω, O i ω)) (B i) μ) ∧ AEFunctionOf (behaviourTuple O B) Pol μ

end Corpus

/-! ### T8(a): the refutation -/

namespace AgencyFail

/-- Four worlds `(k, j)`, uniform.
Source: mandate T8(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Bool × Bool

/-- Uniform weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The uniform measure on the four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def μ : Measure Ω := distMeasure weights.dist

instance μ_isProbabilityMeasure : IsProbabilityMeasure μ := by
  unfold μ
  infer_instance

/-- One situation; the observation is the second bit, the behaviour is the whole world.
Source: mandate T8(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def O : Unit → Ω → Bool := fun _ ω => ω.2

/-- The behaviour: the whole world.
Source: mandate T8(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def B : Unit → Ω → Ω := fun _ ω => ω

/-- The first attribution: the policy is the first bit.
Source: mandate T8(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Pol₁ : Ω → Bool := Prod.fst

/-- The second attribution: the policy is the whole world — `Pol₁` plus one extra bit of behaviour.
Source: mandate T8(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Pol₂ : Ω → Ω := id

/-- Supporting lemma: on `μ`, a.e. is everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ae_iff (P : Ω → Prop) : (∀ᵐ ω ∂μ, P ω) ↔ ∀ ω, P ω :=
  distMeasure_ae_iff_forall_of_pos weights.dist weights.w_pos P

/-- **The first attribution satisfies both conditions.**
Source: mandate T8(a) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem attribution₁ : CorpusAgencyAttribution μ Pol₁ O B := by
  refine ⟨fun _ => ⟨fun p => (p.1, p.2), measurable_of_countable _, ?_⟩,
    ⟨fun b => (b ()).2.1, measurable_of_countable _, ?_⟩⟩
  · rw [ae_iff]; intro ω; rfl
  · rw [ae_iff]; intro ω; rfl

/-- **The second attribution satisfies both conditions.**
Source: mandate T8(a) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem attribution₂ : CorpusAgencyAttribution μ Pol₂ O B := by
  refine ⟨fun _ => ⟨fun p => p.1, measurable_of_countable _, ?_⟩,
    ⟨fun b => (b ()).2, measurable_of_countable _, ?_⟩⟩
  · rw [ae_iff]; intro ω; rfl
  · rw [ae_iff]; intro ω; rfl

/-- **`Pol₂` is not a function of `Pol₁`**: two worlds share `Pol₁` and differ in `Pol₂`.
Source: mandate T8(a) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_aeFunctionOf : ¬ AEFunctionOf Pol₁ Pol₂ μ := by
  rintro ⟨f, -, hf⟩
  rw [ae_iff] at hf
  have h1 := hf (true, true)
  have h2 := hf (true, false)
  simp only [Pol₁, Pol₂, id] at h1 h2
  rw [← h2] at h1
  exact absurd h1 (by decide)

/-- **Non-degeneracy**: `Pol₁` is non-constant and the extra bit is non-constant given `Pol₁`.
Source: mandate T8(a) (witness, N+)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem nondegenerate : (∃ ω ω', Pol₁ ω ≠ Pol₁ ω') ∧ (∃ ω ω', Pol₁ ω = Pol₁ ω' ∧ Pol₂ ω ≠ Pol₂ ω') :=
  ⟨⟨(true, true), (false, true), by decide⟩, ⟨(true, true), (true, false), by decide, by decide⟩⟩

end AgencyFail

/-- **The "correspondence theorem for agency" is false (T8(a), load-bearing 4)**: there is a
probability space with two attributions of the same behaviour, both satisfying determination and
recoverability, whose policies are not a.e. functions of each other. The note's conclusion
("Then Π₁ = Π₂ — they must agree on the policy") needs a minimality premise it never states; the
surviving neighbour is Eisenstat's Theorem 4.15 under *perfect condensation*
(`agency_correspondence_of_perfectlyCondenses`).
Source: [[condensation-connection-attempt]] line 105 (udt-rep-040; findings §6.6)
Kind: P
Fidelity: exact (refutation of the quoted sentence under the two formal conditions)
Hyps: none -/
theorem agency_correspondence_fails :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (Pol₁ : Ω → Bool) (Pol₂ : Ω → Bool × Bool) (O : Unit → Ω → Bool) (B : Unit → Ω → Bool × Bool),
      CorpusAgencyAttribution μ Pol₁ O B ∧ CorpusAgencyAttribution μ Pol₂ O B ∧
        ¬ AEFunctionOf Pol₁ Pol₂ μ :=
  ⟨AgencyFail.Ω, inferInstance, AgencyFail.μ, inferInstance, AgencyFail.Pol₁, AgencyFail.Pol₂,
    AgencyFail.O, AgencyFail.B, AgencyFail.attribution₁, AgencyFail.attribution₂,
    AgencyFail.not_aeFunctionOf⟩

/-! ### T8(b): the nearest true statement, FAF's Theorem 4.15 -/

section Behaviour

variable {I : Type} [Finite I] {Ω : Type} [MeasurableSpace Ω] [Countable Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  [ShannonInformation.FiniteEntropyMeasure μ]
  {ObsT ActT : Type} [MeasurableSpace ObsT] [Countable ObsT] [MeasurableSingletonClass ObsT]
  [MeasurableSpace ActT] [Countable ActT] [MeasurableSingletonClass ActT]

/-- **The behaviour random variable model** `X i = (O i, B i)`: one variable per situation, the
observation–action pair.
Source: [[condensation-connection-attempt]] lines 140–142 ("Let M be a behavior model"); mandate T8(b)
Kind: D
Fidelity: exact
Hyps: n/a -/
def behaviourModel (O : I → Ω → ObsT) (B : I → Ω → ActT) : RVModel I where
  Ω := Ω
  P := μ
  R := fun _ => ObsT × ActT
  X := fun i ω => (O i ω, B i ω)
  measurable_X := fun _ => measurable_of_countable _
  finiteEntropy_X := fun _ => ShannonInformation.finiteEntropyMeasure_map μ (measurable_of_countable _)

/-- **The correspondence theorem under Eisenstat's hypothesis (T8(b))**: if two latent variable
models of the behaviour model both perfectly condense it, then in any amalgamation each latent
`Y_A` is a.e. a function of the other model's `Z_{⊇A}`, and conversely. This is FAF's Theorem 4.15
instantiated; its hypothesis is *perfect condensation* of both models, which the corpus's
determination + recoverability package does not imply (T8(a)) — nor does decision-determination
(`Markov.lean`: DD is the ordered-Markov clause; the function clause is what fails).
Source: [[condensation-connection-attempt]] lines 92–107 (udt-rep-040, 2-030 "Lemma"); FAF Theorem 4.15
Kind: L
Fidelity: exact (FAF's theorem at the behaviour model; the amalgamation is any, e.g. `LatentAmalgamation.canonical`)
Hyps: (a) `h₁`, `h₂` (perfect condensation, Eisenstat's hypothesis, not the corpus's) -/
theorem agency_correspondence_of_perfectlyCondenses (O : I → Ω → ObsT) (B : I → Ω → ActT)
    (L₁ L₂ : LatentModel (behaviourModel μ O B)) (h₁ : L₁.PerfectlyCondenses)
    (h₂ : L₂.PerfectlyCondenses) (Am : LatentAmalgamation L₁ L₂) (A : PPlus I) :
    AEFunctionOf (Am.lat₂.jointAbove A.toFinset) (Am.lat₁.Y A) Am.P₀ ∧
      AEFunctionOf (Am.lat₁.jointAbove A.toFinset) (Am.lat₂.Y A) Am.P₀ :=
  aeFunctionOf_jointAbove_of_perfectlyCondenses h₁ h₂ Am A

/-- **The same at the top index set** (`A = I`, the "policy-level" latent of the agent reading):
the two models' top latents are a.e. functions of each other (since `Y_{⊇I} = Y_I`).
Source: [[topics/optimal-prediction]] lines 30–32 ("Corollary … perfect condensations of the same RVM are rigid"; "Agent interpretation") (udt-rep-040)
Kind: L
Fidelity: exact (stated through `jointAbove univ`, which is the one-element family `{I}`)
Hyps: (a) `h₁`, `h₂` -/
theorem agency_correspondence_top [Fintype I] [Nonempty I] (O : I → Ω → ObsT) (B : I → Ω → ActT)
    (L₁ L₂ : LatentModel (behaviourModel μ O B)) (h₁ : L₁.PerfectlyCondenses)
    (h₂ : L₂.PerfectlyCondenses) (Am : LatentAmalgamation L₁ L₂) :
    AEFunctionOf (Am.lat₂.jointAbove Finset.univ) (Am.lat₁.Y ⟨Finset.univ, Finset.univ_nonempty⟩)
        Am.P₀ ∧
      AEFunctionOf (Am.lat₁.jointAbove Finset.univ) (Am.lat₂.Y ⟨Finset.univ, Finset.univ_nonempty⟩)
        Am.P₀ :=
  aeFunctionOf_jointAbove_of_perfectlyCondenses h₁ h₂ Am ⟨Finset.univ, Finset.univ_nonempty⟩

end Behaviour

end

end Cleanroom.Udt.UdtCondenseDd
