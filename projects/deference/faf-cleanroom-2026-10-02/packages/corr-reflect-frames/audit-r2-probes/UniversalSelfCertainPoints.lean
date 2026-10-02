import Cleanroom.Corrigibility.CorrReflectFrames.SelfRef

/-!
Audit r2 (adversarial) probe — the repaired OPEN statement of T13(c) has content.

Round 0's `selfRefSpace_exists_open` was provable with `Ω := Empty` (audit r1). The repaired
statement asks for a `SelfRefSpace W` that `IsUniversal`. This probe checks that `IsUniversal`
is not an empty clause: applied to the one-point test coalgebra `PUnit → W × Δ(PUnit)` with
state `w` and the Dirac credence, it forces a **unique self-certain total world for every
external state** — an `ω₀` with `state ω₀ = w` and `cred ω₀ = δ_{ω₀}`. So any witness of
`universalSelfRefSpace_exists_open` must contain the "certainty hierarchies" of Mertens–Zamir
(one per state), which a bare fixed point of `X ↦ W × Δ(X)` need not; and the uniqueness half of
`∃!` is exercised (two self-certain worlds with the same state would give two morphisms).
Nothing here is imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.AuditR2

open MeasureTheory

/-- The one-point space is opens-measurable for its `⊤` σ-algebra. -/
instance : OpensMeasurableSpace PUnit := ⟨le_top⟩

/-- The Dirac probability measure at a point. -/
noncomputable def diracPM {Ω : Type} [MeasurableSpace Ω] (ω : Ω) : ProbabilityMeasure Ω :=
  ⟨Measure.dirac ω, inferInstance⟩

theorem diracPM_map {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (ω : Ω)
    {f : Ω → Ω'} (hf : Measurable f) :
    (diracPM ω).map hf.aemeasurable = diracPM (f ω) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  show (Measure.dirac ω).map f = Measure.dirac (f ω)
  exact Measure.map_dirac' hf ω

/-- **Universality forces a unique self-certain world per state.** -/
theorem universal_selfCertain {W : Type} [TopologicalSpace W] (X : SelfRefSpace W)
    (hU : X.IsUniversal) (w : W) :
    ∃! ω₀ : X.Ω, X.state ω₀ = w ∧ X.cred ω₀ = diracPM ω₀ := by
  have hcont : Continuous (fun _ : PUnit => (w, diracPM PUnit.unit)) := continuous_const
  obtain ⟨h, hh, huniq⟩ := hU PUnit (fun _ => w) (fun _ => diracPM PUnit.unit) hcont
  refine ⟨h.1 PUnit.unit, ⟨(hh PUnit.unit).1, ?_⟩, ?_⟩
  · rw [(hh PUnit.unit).2, diracPM_map PUnit.unit h.2.measurable]
  · rintro ω₁ ⟨hs, hc⟩
    have hmem : ∀ u : PUnit, X.state ((⟨fun _ => ω₁, continuous_const⟩ :
        {h : PUnit → X.Ω // Continuous h}).1 u) = w ∧
        X.cred ((⟨fun _ => ω₁, continuous_const⟩ : {h : PUnit → X.Ω // Continuous h}).1 u) =
          (diracPM PUnit.unit).map
            (⟨fun _ => ω₁, continuous_const⟩ :
              {h : PUnit → X.Ω // Continuous h}).2.measurable.aemeasurable := by
      intro u
      refine ⟨hs, ?_⟩
      have hmeas : Measurable (fun _ : PUnit => ω₁) := measurable_const
      show X.cred ω₁ = (diracPM PUnit.unit).map hmeas.aemeasurable
      rw [diracPM_map PUnit.unit hmeas]
      exact hc
    have := huniq ⟨fun _ => ω₁, continuous_const⟩ hmem
    exact (congrArg (fun k : {h : PUnit → X.Ω // Continuous h} => k.1 PUnit.unit) this)

end Cleanroom.Corrigibility.CorrReflectFrames.AuditR2
