import Cleanroom.Udt.UdtPaperTiling.Rules

/-!
# `udt-paper-tiling` · Theorem1: Policy Fairness and the UDT 1.1 tiling theorem (T3)

The paper's Policy Fairness (`main.tex` 145–147: `eff(π₁) = eff(π₂) → E_p(u|π* = ⌜π₁⌝) =
E_p(u|π* = ⌜π₂⌝)`) **is** `udt-bli-core`'s `PolicyFair` on the paper layer's procedure layer
(`paperPolicyFair_iff`, `Iff.rfl`), so the run has one fairness predicate. Theorem 1 ("under
Policy Fairness, UDT 1.1 does not strictly prefer any self-modifying policy") is one application
of that hypothesis to the pair `(π, eff π)`, using `eff(eff π) = eff π` — Kind **L**, as the
ledger says. It is **weak tiling**: no self-modifying policy is *strictly* better than every
non-modifying one; ties are allowed and the argmax may still be self-modifying (bli-slides-026's
own remark). Never state it on the trivial layer (`Proc = Policy`, `eff = id`), where it is `rfl`
(`policyFair_trivialLayer`, Kind T); the witnesses in `Theorem1Witness.lean` have `eff`
non-injective.

The properties of `eff` the proofs use (`eff ∘ eff = eff`, `eff π ∈ Π^{-m}`, type preservation)
are explicit hypotheses: grade (a) through `EffData.ofCausal`/`effCausal_*`, grade (c) through a
bare `EffData` (`main.tex` 97's assumption). `PaperLayer.ofEffData` and the `_ofEffData` forms
discharge them.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act}

/-- **The paper's Policy Fairness is the run's `PolicyFair`** on the paper layer: for policies
`π₁, π₂` of positive mass, `eff π₁ = eff π₂ → 𝔼[U | π* = π₁] = 𝔼[U | π* = π₂]`. Definitional.
Source: `main.tex` 145–147 (bli-paper-004); bli-slides-026
Kind: L
Fidelity: exact (positivity of both policies, so the predicate never speaks of junk) -/
theorem paperPolicyFair_iff (Λ : PaperLayer P) :
    P.PolicyFair Λ.toProcLayer ↔
      ∀ π₁ π₂, Λ.eff π₁ = Λ.eff π₂ → 0 < Λ.procMass π₁ → 0 < Λ.procMass π₂ →
        Λ.procEU π₁ = Λ.procEU π₂ :=
  Iff.rfl

/-- **Theorem 1 (UDT 1.1 weak tiling), the identity form.** Under Policy Fairness, a policy `π`
of positive mass whose effective policy has positive mass is exactly as good as its effective
policy: `𝔼[U | π* = π] = 𝔼[U | π* = eff π]`. The proof is the paper's: `eff(eff π) = eff π`, so
fairness applies to the pair. One application of the hypothesis.
Source: `main.tex` 149–161, Theorem 1 (bli-paper-005); bli-slides-026
Kind: L
Fidelity: exact given positivity of both policies
Hyps: (a) `PolicyFair`; `hidem` is (a) from `effCausal_idem`, (c) from a bare `EffData` -/
theorem thm1_udt11_tiling (Λ : PaperLayer P) (hF : P.PolicyFair Λ.toProcLayer)
    (π : Policy 𝒟 Act) (hidem : Λ.eff (Λ.eff π) = Λ.eff π) (hπ : 0 < Λ.procMass π)
    (hE : 0 < Λ.procMass (Λ.eff π)) : Λ.procEU π = Λ.procEU (Λ.eff π) :=
  hF π (Λ.eff π) hidem.symm hπ hE

/-- **Theorem 1 in the paper's words**: under Policy Fairness (and every well-typed policy of
positive mass), no self-modifying well-typed policy is *strictly* better than every well-typed
non-modifying one. Weak tiling: ties are allowed, and a self-modifying policy may still be *an*
argmax. The hypothesis `¬ S.NonMod π` is **not used** by the proof (audit r1): no well-typed
policy at all, self-modifying or not, strictly beats every well-typed non-modifying one; it is
kept so that the statement reads as the paper's sentence. `hpos` is stronger than the proof
needs (only `π` and `eff π` must be positive) — the paper's implicit "every policy is a possible
choice". The N+ witness of record is `Thm1Wit4.thm1_on_prior4` (`Theorem2Witness.lean`), a
`PaperLayer` with non-injective `eff`.
Source: `main.tex` 149–161, Theorem 1 (bli-paper-005)
Kind: L
Fidelity: exact (with the positivity `hpos`, the paper's implicit "every policy is a possible
choice"); the self-modification restriction is inert
Hyps: (a) `PolicyFair`, `hpos`; `hidem`, `hnm`, `hwt` are (a) from the causal construction or
(c) from a bare `EffData` -/
theorem thm1_no_strict_selfMod (S : PaperStructure 𝒟 Act) (Λ : PaperLayer P)
    (hF : P.PolicyFair Λ.toProcLayer) (hidem : ∀ π, Λ.eff (Λ.eff π) = Λ.eff π)
    (hnm : ∀ π, S.NonMod (Λ.eff π)) (hwt : ∀ π, S.WellTyped π → S.WellTyped (Λ.eff π))
    (hpos : ∀ π, S.WellTyped π → 0 < Λ.procMass π) :
    ¬ ∃ π, S.WellTyped π ∧ ¬ S.NonMod π ∧
      ∀ π', S.WellTyped π' → S.NonMod π' → Λ.procEU π' < Λ.procEU π := by
  rintro ⟨π, hπ, _, hstrict⟩
  have h := hstrict (Λ.eff π) (hwt π hπ) (hnm π)
  rw [thm1_udt11_tiling Λ hF π (hidem π) (hpos π hπ) (hpos _ (hwt π hπ))] at h
  exact lt_irrefl _ h

/-- **The effective policy of a UDT 1.1 optimum is a UDT 1.1 optimum** (and non-modifying when
`eff` is): under Policy Fairness, `eff πstar` is as good as `πstar`, hence prior-optimal too.
Source: `main.tex` 149–161 (bli-paper-005), read through the UDT 1.1 rule (bli-paper-003)
Kind: L
Fidelity: exact
Hyps: (a) `PolicyFair`, `IsUDT11`; `hidem` as above -/
theorem isUDT11_eff (S : PaperStructure 𝒟 Act) (Λ : PaperLayer P) (hF : P.PolicyFair Λ.toProcLayer)
    {πstar : Policy 𝒟 Act} (hU : IsUDT11 S Λ πstar) (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar)
    (hπ : 0 < Λ.procMass πstar) (hE : 0 < Λ.procMass (Λ.eff πstar)) :
    IsUDT11 S Λ (Λ.eff πstar) ∧ Λ.procEU (Λ.eff πstar) = Λ.procEU πstar := by
  have heq := thm1_udt11_tiling Λ hF πstar hidem hπ hE
  refine ⟨fun π hπ' hpos => ?_, heq.symm⟩
  rw [← heq]
  exact hU π hπ' hpos

/-! ## Layers built from an `EffData` -/

namespace PaperLayer

/-- A paper layer from the paper's `eff` (an `EffData`) and a chosen coordinate.
Source: mandate §3
Kind: D
Fidelity: exact -/
def ofEffData {S : PaperStructure 𝒟 Act} (E : S.EffData) (chosen : P.Ω → Policy 𝒟 Act)
    (h : ∀ ω, P.pp ω = E.eff (chosen ω)) : PaperLayer P where
  chosen := chosen
  eff := E.eff
  pp_eff := h

end PaperLayer

/-- **Theorem 1 over an `EffData`**: the three `eff` hypotheses discharged from the data (grade
(c) for a bare `EffData`, grade (a) for `CausalStructure.toEffData`).
Source: `main.tex` 149–161, Theorem 1 (bli-paper-005)
Kind: L
Fidelity: exact
Hyps: (a) `PolicyFair`, `hpos`; (c) `E`'s fields unless `E = C.toEffData` -/
theorem thm1_no_strict_selfMod_ofEffData {S : PaperStructure 𝒟 Act} (E : S.EffData)
    (chosen : P.Ω → Policy 𝒟 Act) (h : ∀ ω, P.pp ω = E.eff (chosen ω))
    (hF : P.PolicyFair (PaperLayer.ofEffData E chosen h).toProcLayer)
    (hpos : ∀ π, S.WellTyped π → 0 < (PaperLayer.ofEffData E chosen h).procMass π) :
    ¬ ∃ π, S.WellTyped π ∧ ¬ S.NonMod π ∧
      ∀ π', S.WellTyped π' → S.NonMod π' →
        (PaperLayer.ofEffData E chosen h).procEU π' < (PaperLayer.ofEffData E chosen h).procEU π :=
  thm1_no_strict_selfMod S _ hF E.eff_idem E.eff_nonMod E.eff_wellTyped hpos

end Cleanroom.Udt.UdtPaperTiling
