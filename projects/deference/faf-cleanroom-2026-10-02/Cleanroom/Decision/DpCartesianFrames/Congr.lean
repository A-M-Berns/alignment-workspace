import Cleanroom.Decision.DpCartesianFrames.Observe

/-!
# `&` and `⊗` respect biextensional equivalence

Package `dp-cartesian-frames`, file 13 (repair round 1; mandate T10(a)'s "`sum`/`tensor`
respect `≃ᵇ`"). Through FAF's `biextEquiv_iff_homotopyEquiv`: a homotopy equivalence of each
factor induces one of the sum (`Hom.sumMap`) and of the tensor (`Hom.tensorMap`, whose
environment map pre-composes with the forward morphism and post-composes with the dual of the
other factor's forward morphism).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame

universe u

variable {W : Type u}

/-- The sum of two Chu morphisms, `φ & χ : C & D ⟶ C' & D'`.
Source: post 11 §3 (line 123); none otherwise: infrastructure
Kind: D -/
def Hom.sumMap {C C' D D' : CartesianFrames.Frame W} (φ : C ⟶ C') (χ : D ⟶ D') :
    Frame.sum C D ⟶ Frame.sum C' D' where
  agent a := (φ.agent a.1, χ.agent a.2)
  env e := match e with
    | .inl e => .inl (φ.env e)
    | .inr f => .inr (χ.env f)
  adjoint a e := by
    cases e with
    | inl e => exact φ.adjoint a.1 e
    | inr f => exact χ.adjoint a.2 f

/-- **`&` respects biextensional equivalence**: `C ≃ᵇ C' → D ≃ᵇ D' → C & D ≃ᵇ C' & D'`.
Source: mandate T10(a) ("`sum`/`tensor` respect `≃ᵇ`")
Kind: C
Fidelity: exact
Hyps: none -/
theorem sum_biextEquiv {C C' D D' : CartesianFrames.Frame W} (hC : C ≃ᵇ C') (hD : D ≃ᵇ D') :
    Frame.sum C D ≃ᵇ Frame.sum C' D' := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp hC
  obtain ⟨φ', ψ', hφψ', hψφ'⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp hD
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨Hom.sumMap φ φ', Hom.sumMap ψ ψ', ?_, ?_⟩
  · rintro ⟨a, b⟩ (e | f)
    · exact hφψ a e
    · exact hφψ' b f
  · rintro ⟨a, b⟩ (e | f)
    · exact hψφ a e
    · exact hψφ' b f

/-- The tensor of two Chu morphisms, `φ ⊗ χ : C ⊗ D ⟶ C' ⊗ D'`: on environments a morphism
`θ : C' ⟶ D'*` goes to `φ ≫ θ ≫ χ* : C ⟶ D*`.
Source: post 11 §4.1 (line 177); none otherwise: infrastructure
Kind: D -/
def Hom.tensorMap {C C' D D' : CartesianFrames.Frame W} (φ : C ⟶ C') (χ : D ⟶ D') :
    Frame.tensor C D ⟶ Frame.tensor C' D' where
  agent a := (φ.agent a.1, χ.agent a.2)
  env θ := φ ≫ θ ≫ χ.dual
  adjoint a θ := φ.adjoint a.1 (θ.env (χ.agent a.2))

/-- **`⊗` respects biextensional equivalence**: `C ≃ᵇ C' → D ≃ᵇ D' → C ⊗ D ≃ᵇ C' ⊗ D'`.
Source: mandate T10(a) ("`sum`/`tensor` respect `≃ᵇ`")
Kind: C
Fidelity: exact
Hyps: none -/
theorem tensor_biextEquiv {C C' D D' : CartesianFrames.Frame W} (hC : C ≃ᵇ C')
    (hD : D ≃ᵇ D') : Frame.tensor C D ≃ᵇ Frame.tensor C' D' := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp hC
  obtain ⟨φ', ψ', hφψ', hψφ'⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp hD
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr
    ⟨Hom.tensorMap φ φ', Hom.tensorMap ψ ψ', ?_, ?_⟩
  · rintro ⟨a, b⟩ θ
    show C.outcome a (θ.env b) =
      C.outcome (ψ.agent (φ.agent a)) (θ.env (ψ'.agent (φ'.agent b)))
    have h1 : C.outcome a (θ.env b) = D.outcome b (θ.agent a) := θ.adjoint a b
    have h2 : D.outcome b (θ.agent a) = D.outcome (ψ'.agent (φ'.agent b)) (θ.agent a) :=
      hφψ' b (θ.agent a)
    have h3 : D.outcome (ψ'.agent (φ'.agent b)) (θ.agent a) =
        C.outcome a (θ.env (ψ'.agent (φ'.agent b))) := (θ.adjoint a _).symm
    have h4 : C.outcome a (θ.env (ψ'.agent (φ'.agent b))) =
        C.outcome (ψ.agent (φ.agent a)) (θ.env (ψ'.agent (φ'.agent b))) := hφψ a _
    exact h1.trans (h2.trans (h3.trans h4))
  · rintro ⟨a, b⟩ θ
    show C'.outcome a (θ.env b) =
      C'.outcome (φ.agent (ψ.agent a)) (θ.env (φ'.agent (ψ'.agent b)))
    have h1 : C'.outcome a (θ.env b) = D'.outcome b (θ.agent a) := θ.adjoint a b
    have h2 : D'.outcome b (θ.agent a) = D'.outcome (φ'.agent (ψ'.agent b)) (θ.agent a) :=
      hψφ' b (θ.agent a)
    have h3 : D'.outcome (φ'.agent (ψ'.agent b)) (θ.agent a) =
        C'.outcome a (θ.env (φ'.agent (ψ'.agent b))) := (θ.adjoint a _).symm
    have h4 : C'.outcome a (θ.env (φ'.agent (ψ'.agent b))) =
        C'.outcome (φ.agent (ψ.agent a)) (θ.env (φ'.agent (ψ'.agent b))) := hψφ a _
    exact h1.trans (h2.trans (h3.trans h4))

end Cleanroom.Decision.DpCartesianFrames
