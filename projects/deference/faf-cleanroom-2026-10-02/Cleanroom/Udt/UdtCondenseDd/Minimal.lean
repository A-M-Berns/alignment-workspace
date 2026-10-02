import Cleanroom.Udt.UdtCondenseDd.Correspond

/-!
# `Cleanroom.Udt.UdtCondenseDd.Minimal`: the minimality premise (T6)

Work package `udt-condense-dd`, target T6 (udt-rep-037, 2-028). The "minimality gap" of
[[fair-environment-theorem]] lines 130–132: the sufficient-statistic argument for Gap 1 needs the
policy to be *minimal* among sufficient statistics, which recoverability does not supply.

* **T6(a)** `refine_keeps_determination_recoverability`: determination and recoverability are
  preserved by refining the policy with any function `J` of the behaviour, `Pol' := (Pol, J)`; on the
  T8(a) witness `Pol' = (Pol₁, extra bit)` is not a function of `Pol` (`Correspond.lean`,
  `AgencyFail.not_aeFunctionOf`). Recoverability gives `Pol = f(B)`, never `B = g(Pol)`; FAF's
  Corollary 4.6 (`aeFunctionOf_of_perfectlyCondenses`) is the form of that asymmetry under perfect
  condensation (udt-rep-2-028).
* **T6(b)** `Sufficient`, `MinimalSufficient`, `gap1_of_minimalSufficient`: "exact Gap 1 under
  minimality" — a minimal-sufficient *predictor* statistic is a function of every sufficient one, in
  particular of the policy — is **definitional** (`L`): the minimality reading turns Gap 1 into a
  definition-unfolding, and it is the *predictor* `E` that must be minimal, the direction the corpus
  never states. Sufficiency is a.e., so off-support values are unconstrained and the T2(b)
  counterexample survives (findings). A non-definitional version is not stated (mandate: at most a
  session-quarter; none found).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust MeasureTheory ProbabilityTheory Finset
open Condensation

noncomputable section

set_option linter.unusedSectionVars false

section Minimal

variable {I Ω ObsT ActT PolT J : Type} [MeasurableSpace Ω] [MeasurableSpace ObsT]
  [MeasurableSpace ActT] [MeasurableSpace PolT] [MeasurableSpace J]

/-- **Refining the policy keeps determination and recoverability (T6(a))**: if `Pol` determines each
action together with the observation and is recoverable from the behaviour, so is `(Pol, J)` for
every `J` recoverable from the behaviour. Hence the two conditions do not pin the policy down: they
are preserved under refinement, and only a *minimality* premise could select `Pol`.
Source: [[fair-environment-theorem]] lines 130–132 (the minimality gap; udt-rep-037)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem refine_keeps_determination_recoverability (μ : Measure Ω) (Pol : Ω → PolT)
    (O : I → Ω → ObsT) (B : I → Ω → ActT) (Jv : Ω → J) (h : CorpusAgencyAttribution μ Pol O B)
    (hJ : AEFunctionOf (behaviourTuple O B) Jv μ) :
    CorpusAgencyAttribution μ (fun ω => (Pol ω, Jv ω)) O B := by
  obtain ⟨hdet, hrec⟩ := h
  refine ⟨fun i => ?_, hrec.prodMk hJ⟩
  obtain ⟨f, hf, hae⟩ := hdet i
  refine ⟨fun p => f (p.1.1, p.2), hf.comp (measurable_fst.fst.prodMk measurable_snd), ?_⟩
  exact hae

/-- **`T` is a sufficient statistic for the behaviour**: together with each observation it
determines each action, `H(A_i | T, O_i) = 0`.
Source: [[fair-environment-theorem]] lines 119–121, 126–128 (udt-rep-037)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Sufficient (μ : Measure Ω) {T : Type} [MeasurableSpace T] (Tv : Ω → T) (O : I → Ω → ObsT)
    (B : I → Ω → ActT) : Prop :=
  ∀ i, AEFunctionOf (fun ω => (Tv ω, O i ω)) (B i) μ

/-- **`Pol` is a minimal sufficient statistic**: sufficient, and a.e. a function of every sufficient
statistic. (The "minimal sufficient statistic" of [[fair-environment-theorem]] line 126.)
Source: [[fair-environment-theorem]] lines 126–132 (udt-rep-037)
Kind: D
Fidelity: exact
Hyps: n/a -/
def MinimalSufficient (μ : Measure Ω) (Pol : Ω → PolT) (O : I → Ω → ObsT) (B : I → Ω → ActT) :
    Prop :=
  Sufficient μ Pol O B ∧
    ∀ (T : Type) (_ : MeasurableSpace T) (Tv : Ω → T), Sufficient μ Tv O B → AEFunctionOf Tv Pol μ

/-- **"Exact Gap 1 under minimality" is definitional (T6(b))**: if the *predictor's* statistic `E`
is a minimal sufficient statistic of the behaviour and the policy is sufficient, then `E` is a.e.
a function of the policy. This is `MinimalSufficient` unfolded (`L`/`S`): the minimality reading
makes Gap 1 a definition-unfolding, and the minimality is required of the predictor `E`, not of
the policy — the direction the corpus never states. Sufficiency is a.e., so off-support values are
unconstrained and the T2(b) counterexample survives.
Source: [[fair-environment-theorem]] lines 123–132 (udt-rep-037; findings)
Kind: S
Fidelity: exact (definitional)
Hyps: (a); `hE` is the conclusion's content -/
theorem gap1_of_minimalSufficient (μ : Measure Ω) {ET : Type} [MeasurableSpace ET] (E : Ω → ET)
    (Pol : Ω → PolT) (O : I → Ω → ObsT) (B : I → Ω → ActT) (hE : MinimalSufficient μ E O B)
    (hPol : Sufficient μ Pol O B) : AEFunctionOf Pol E μ :=
  hE.2 PolT inferInstance Pol hPol

/-- **Recoverability is the wrong direction**: `Pol = f(B)` (recoverability) never gives
`B = g(Pol)`; on the T8(a) witness the first attribution is recoverable while the behaviour is not
a function of it.
Source: udt-rep-2-028 (Cor 4.6 as the FAF form of the asymmetry); mandate T6(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem recoverable_not_determining :
    AEFunctionOf (behaviourTuple AgencyFail.O AgencyFail.B) AgencyFail.Pol₁ AgencyFail.μ ∧
      ¬ AEFunctionOf AgencyFail.Pol₁ (behaviourTuple AgencyFail.O AgencyFail.B) AgencyFail.μ := by
  refine ⟨AgencyFail.attribution₁.2, ?_⟩
  rintro ⟨f, -, hf⟩
  rw [AgencyFail.ae_iff] at hf
  have h1 := hf (true, true)
  have h2 := hf (true, false)
  simp only [AgencyFail.Pol₁] at h1 h2
  rw [← h2] at h1
  have := congrArg (fun g => (g ()).2.2) h1
  simp [behaviourTuple, AgencyFail.O, AgencyFail.B] at this

end Minimal

end

end Cleanroom.Udt.UdtCondenseDd
