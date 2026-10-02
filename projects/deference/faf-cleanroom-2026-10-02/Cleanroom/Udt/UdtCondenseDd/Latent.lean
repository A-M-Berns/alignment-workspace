import Cleanroom.Udt.UdtCondenseDd.Bridge
import Condensation.Perfect

/-!
# `Cleanroom.Udt.UdtCondenseDd.Latent`: the policy latent model over FAF, and what perfect condensation forces (T9(a))

Work package `udt-condense-dd`, target T9 (udt-rep-045). The note says (quoted per plan §0.4 rule 3):
"**`Π̈` is a perfect condensation variable for the agent's influence on the environment**"
([[topics/decision-determination]] line 99). Reading of record (ATTRIBUTION-UNVETTED — the note may
mean only the Markov clause, which is T9(b), `Markov.lean`): Eisenstat's `PerfectlyCondenses` of the
two-variable random variable model `(D_{I,B}, E)` by the latent variable model whose pair latent is
`Π̈` and whose singleton latents are the variables themselves.

## Encoding (settled first, mandate §3)

* `Idx := Fin 2`, `0 ↦ D_{I,B}`, `1 ↦ E`; `P0 = {0}`, `P1 = {1}`, `P01 = {0,1}` exhaust `PPlus Idx`
  (`pplus_cases`, by `decide`).
* **All ranges are coded into one type** `LatVal := (DI × DB) ⊕ ((AE × DE) ⊕ (OE → AE))` by the
  three injections, so that the latent family `Y : PPlus Idx → Ω → LatVal` and the given family
  `X : Idx → Ω → LatVal` are plain (non-dependent) functions: `X 0 = inl ∘ D_{I,B}`,
  `X 1 = inr ∘ inl ∘ E`, `Y P0 = X 0`, `Y P1 = X 1`, `Y P01 = inr ∘ inr ∘ Π̈`. The coding is
  injective and entropy-invariant; every headline below is *stated for the uncoded variables*
  (`S.E`, `S.DIB`, `S.polE`), transported along the injections and their left inverses. Nothing here
  is a `(c)`: `Λ = Ω`, `π = id`, and the latent model's measure is `dsMeasure S`.
* `contributes`: `X 0` is recovered from `Y P0` and `X 1` from `Y P1` — projections.

## Result (T9(a), load-bearing 3, first half)

`aeFunctionOf_polE_of_perfectlyCondenses`: if `polLatent S` perfectly condenses `rvModel S`, then
`Π̈` is a.e. a function of `E` (FAF Corollary 4.6 at `i = 1`, `A = P01`), hence
`isSubvariable_polE_of_perfectlyCondenses` (everywhere, by T7(a)) and
`condEntropy_polE_E_eq_zero`. The refutation (a decision-determined structure with `Π̈` not a
function of `E`) is `WitnessLatent.lean`; the mandate's "environment ignores the agent" witness
cannot exist (`polE_const_of_indep_E_DIB`, a finding).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust MeasureTheory ProbabilityTheory Finset
open Condensation

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Sum types have measurable singletons (Mathlib lacks the instance) -/

/-- Measurable singletons on a sum type.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
instance sum_measurableSingletonClass {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a => rw [← Set.image_singleton]; exact (measurableSet_singleton a).inl_image
    | inr b => rw [← Set.image_singleton]; exact (measurableSet_singleton b).inr_image

/-! ### The index set and its nonempty power set -/

/-- The index set of the three-variable model: `0 ↦ D_{I,B}`, `1 ↦ E`.
Source: mandate §3 (T9)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Idx : Type := Fin 2

/-- `{0} ∈ P⁺ Idx` (the `D_{I,B}` singleton).
Source: mandate §3 (T9)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def P0 : PPlus Idx := ⟨{0}, Finset.singleton_nonempty _⟩

/-- `{1} ∈ P⁺ Idx` (the `E` singleton).
Source: mandate §3 (T9)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def P1 : PPlus Idx := ⟨{1}, Finset.singleton_nonempty _⟩

/-- `{0, 1} ∈ P⁺ Idx` (the pair, carrying `Π̈`).
Source: mandate §3 (T9)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def P01 : PPlus Idx := ⟨{0, 1}, ⟨0, by decide⟩⟩

/-- `P⁺ (Fin 2)` has exactly the three elements `P0`, `P1`, `P01`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pplus_cases (A : PPlus Idx) : A = P0 ∨ A = P1 ∨ A = P01 := by
  revert A
  decide

/-- Supporting lemma: the three elements are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pplus_ne : P0 ≠ P1 ∧ P0 ≠ P01 ∧ P1 ≠ P01 := by decide

/-! ### The models -/

section Models

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE] [Fintype DE] [DecidableEq DE]
  [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable [MeasurableSpace OE] [MeasurableSingletonClass OE] [MeasurableSpace AE]
  [MeasurableSingletonClass AE] [MeasurableSpace DE] [MeasurableSingletonClass DE]
  [MeasurableSpace DI] [MeasurableSingletonClass DI] [MeasurableSpace DB]
  [MeasurableSingletonClass DB]

/-- **The common coded range** of the three variables: `D_{I,B}`, `E` and `Π̈` injected into one sum
type, so that the given and latent families are non-dependent functions.
Source: mandate §3 (T9), encoding
Kind: D
Fidelity: exact (an injective coding of the three ranges; headlines are stated uncoded)
Hyps: n/a -/
abbrev LatVal (OE AE DE DI DB : Type) : Type := (DI × DB) ⊕ ((AE × DE) ⊕ (OE → AE))

variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- The coded `D_{I,B}`.
Source: mandate §3 (T9)
Kind: D
Fidelity: exact (coded)
Hyps: n/a -/
def cDIB (ω : Ω) : LatVal OE AE DE DI DB := Sum.inl (S.DIB ω)

/-- The coded `E`.
Source: mandate §3 (T9)
Kind: D
Fidelity: exact (coded)
Hyps: n/a -/
def cE (ω : Ω) : LatVal OE AE DE DI DB := Sum.inr (Sum.inl (S.E ω))

/-- The coded `Π̈`.
Source: mandate §3 (T9)
Kind: D
Fidelity: exact (coded)
Hyps: n/a -/
def cPolE (ω : Ω) : LatVal OE AE DE DI DB := Sum.inr (Sum.inr (S.polE ω))

/-- The decoding of `Π̈` (left inverse of `cPolE`; junk `Π̈(w₀)` off the summand).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dPolE : LatVal OE AE DE DI DB → OE → AE :=
  Sum.elim (fun _ => S.polE S.w₀) (Sum.elim (fun _ => S.polE S.w₀) id)

/-- The decoding of `E` (left inverse of `cE`; junk `E(w₀)` off the summand).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dE : LatVal OE AE DE DI DB → AE × DE :=
  Sum.elim (fun _ => S.E S.w₀) (Sum.elim id (fun _ => S.E S.w₀))

/-- The decoding of `D_{I,B}` (left inverse of `cDIB`; junk `D_{I,B}(w₀)` off the summand).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dDIB : LatVal OE AE DE DI DB → DI × DB :=
  Sum.elim id (fun _ => S.DIB S.w₀)

/-- Supporting lemma: the decodings invert the codings.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem decode_code (ω : Ω) :
    dPolE S (cPolE S ω) = S.polE ω ∧ dE S (cE S ω) = S.E ω ∧ dDIB S (cDIB S ω) = S.DIB ω :=
  ⟨rfl, rfl, rfl⟩

/-- **The given family** `X 0 = D_{I,B}`, `X 1 = E` (coded).
Source: mandate §3 (T9)
Kind: D
Fidelity: exact (coded)
Hyps: n/a -/
def rvX (i : Idx) (ω : Ω) : LatVal OE AE DE DI DB := if i = 0 then cDIB S ω else cE S ω

/-- **The latent family**: `Y P0 = D_{I,B}`, `Y P1 = E`, `Y P01 = Π̈` (coded).
Source: [[topics/decision-determination]] line 99, reading of record (udt-rep-045)
Kind: D
Fidelity: exact (coded; the pair latent is `Π̈`)
Hyps: n/a -/
def latY (A : PPlus Idx) (ω : Ω) : LatVal OE AE DE DI DB :=
  if A = P0 then cDIB S ω else if A = P1 then cE S ω else cPolE S ω

/-- Supporting lemma: `rvX` at the two indices.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rvX_zero : rvX S 0 = cDIB S := by
  funext ω; simp [rvX]

/-- Supporting lemma: `rvX` at the two indices.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rvX_one : rvX S 1 = cE S := by
  funext ω; simp [rvX]

/-- Supporting lemma: `latY` at the three latents.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem latY_P0 : latY S P0 = cDIB S := by
  funext ω; simp [latY]

/-- Supporting lemma: `latY` at the three latents.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem latY_P1 : latY S P1 = cE S := by
  funext ω; simp [latY, pplus_ne.1.symm]

/-- Supporting lemma: `latY` at the three latents.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem latY_P01 : latY S P01 = cPolE S := by
  funext ω; simp [latY, pplus_ne.2.1.symm, pplus_ne.2.2.symm]

/-- **The random variable model `(D_{I,B}, E)`** of a decision structure, over `dsMeasure S`.
Source: mandate §3 (T9), `AbstractDS.rvModel`
Kind: D
Fidelity: exact (ranges coded into `LatVal`)
Hyps: n/a -/
def rvModel : RVModel Idx where
  Ω := Ω
  P := dsMeasure S
  R := fun _ => LatVal OE AE DE DI DB
  X := rvX S
  measurable_X := fun _ => measurable_of_countable _
  finiteEntropy_X := fun _ => inferInstance

/-- **The latent random variable model** with latents `Y P0 = D_{I,B}`, `Y P1 = E`, `Y P01 = Π̈`,
on the same space and measure.
Source: mandate §3 (T9)
Kind: D
Fidelity: exact (ranges coded into `LatVal`)
Hyps: n/a -/
def latRV : RVModel (PPlus Idx) where
  Ω := Ω
  P := dsMeasure S
  R := fun _ => LatVal OE AE DE DI DB
  X := latY S
  measurable_X := fun _ => measurable_of_countable _
  finiteEntropy_X := fun _ => inferInstance

/-- **The policy latent model** `polLatent S : LatentModel (rvModel S)`: `Λ = Ω`, `π = id`, the
latents above; `contributes` holds because `X 0 = Y P0` and `X 1 = Y P1` are coordinates of
`Y_∋0`, `Y_∋1`. This is the object the note's sentence is read as being about.
Source: [[topics/decision-determination]] line 99 (udt-rep-045), reading of record (ATTRIBUTION-UNVETTED)
Kind: D
Fidelity: exact (coded ranges; the pair latent is `Π̈`)
Hyps: n/a -/
def polLatent : LatentModel (rvModel S) where
  L := latRV S
  π := id
  π_pres := MeasurePreserving.id _
  contributes := Fin.forall_fin_two.2 ⟨
    ⟨fun g => g ⟨P0, mem_contribIdx.2 (PPlus.mem_iff.2 (Finset.mem_singleton_self _))⟩,
      measurable_of_countable _,
      Filter.Eventually.of_forall fun ω => by
        show rvX S 0 ω = latY S P0 ω
        rw [rvX_zero, latY_P0]⟩,
    ⟨fun g => g ⟨P1, mem_contribIdx.2 (PPlus.mem_iff.2 (Finset.mem_singleton_self _))⟩,
      measurable_of_countable _,
      Filter.Eventually.of_forall fun ω => by
        show rvX S 1 ω = latY S P1 ω
        rw [rvX_one, latY_P1]⟩⟩

/-- Supporting lemma: the latent model's pieces, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polLatent_Y (A : PPlus Idx) : (polLatent S).Y A = latY S A := rfl

/-- Supporting lemma: the latent model's measure is `dsMeasure S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polLatent_P : (polLatent S).P = dsMeasure S := rfl

/-! ### T9(a): perfect condensation forces `Π̈` to be a function of `E` -/

/-- **Perfect condensation by the policy latent forces `Π̈ ⊑ E` (T9(a), load-bearing 3)**: FAF's
Corollary 4.6 (`aeFunctionOf_of_perfectlyCondenses`) at `i = 1 ∈ P01` says the pair latent `Π̈` is
a.e. a function of `X 1 = E`; decoding gives the uncoded statement. This is what Eisenstat's notion
demands and what the corpus's DD does not supply: the corpus's DD is the ordered-Markov clause of
Theorem 4.9(B) without its function clause (`Markov.lean`).
Source: [[topics/decision-determination]] line 99 (udt-rep-045); FAF Corollary 4.6
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem aeFunctionOf_polE_of_perfectlyCondenses (h : (polLatent S).PerfectlyCondenses) :
    AEFunctionOf S.E S.polE (dsMeasure S) := by
  have h1 := (polLatent S).aeFunctionOf_of_perfectlyCondenses h 1 P01
    (PPlus.mem_iff.2 (by decide))
  obtain ⟨f, -, hae⟩ := h1
  have hae' : ∀ᵐ ω ∂dsMeasure S, latY S P01 ω = f (rvX S 1 ω) := hae
  refine ⟨fun e => dPolE S (f (Sum.inr (Sum.inl e))), measurable_of_countable _, ?_⟩
  filter_upwards [hae'] with ω hω
  rw [latY_P01, rvX_one] at hω
  show S.polE ω = dPolE S (f (cE S ω))
  rw [← hω]
  rfl

/-- **The same, everywhere**: `Π̈` is a subvariable of `E` on the support (by T7(a)).
Source: [[topics/decision-determination]] line 99 (udt-rep-045)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem isSubvariable_polE_of_perfectlyCondenses (h : (polLatent S).PerfectlyCondenses) :
    IsSubvariable S.E S.polE :=
  (isSubvariable_iff_aeFunctionOf S S.E S.polE).2 (aeFunctionOf_polE_of_perfectlyCondenses S h)

/-- **`H[Π̈ | E] = 0` under perfect condensation** (FAF Proposition 2.5's easy direction).
Source: [[topics/decision-determination]] line 99 (udt-rep-045)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem condEntropy_polE_E_eq_zero (h : (polLatent S).PerfectlyCondenses) :
    H[S.polE | S.E ; dsMeasure S] = 0 :=
  condEntropy_eq_zero_of_aeFunctionOf (measurable_of_countable _) (measurable_of_countable _)
    (aeFunctionOf_polE_of_perfectlyCondenses S h)

/-- **Criterion for the refutation**: a structure in which `Π̈` is not a function of `E` is not
perfectly condensed by the policy latent. `WitnessLatent.lean` supplies a decision-determined one.
Source: [[topics/decision-determination]] line 99 (udt-rep-045)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem not_perfectlyCondenses_of_not_isSubvariable (h : ¬ IsSubvariable S.E S.polE) :
    ¬ (polLatent S).PerfectlyCondenses :=
  fun hp => h (isSubvariable_polE_of_perfectlyCondenses S hp)

/-! ### A finding about the mandate's witness -/

/-- **The mandate's "environment ignores the agent" witness cannot exist**: in any abstract decision
structure in which `E` is independent of `D_{I,B}` (division-free, on the support), `Π̈` is
constant. Reason: `Ä = Π̈(Ö)` and `Ö` are both functions of `E`, so `(Ö, Π̈(Ö)) ⊥ D_{I,B}` forces
every value of `D_{I,B}` to realize every realized observation with the same action. So T9's
refutation witness must let `E` depend on `Π̈` while `Π̈` is not a function of `E`
(`WitnessLatent.lean`); the mandate's description ("E independent of `D_{I,B}`, so DD holds
trivially, and `Π̈` non-constant") is contradictory. Recorded in the findings.
Source: mandate T9(a), witness description (a finding about the mandate)
Kind: P
Fidelity: n/a (finding)
Hyps: (a); `udt-comm-trust` §3 (c) by reference -/
theorem polE_const_of_indep_E_DIB
    (hind : ∀ (e : AE × DE) (d : DI × DB),
      mass S.μ.w (event fun ω => S.E ω = e ∧ S.DIB ω = d) =
        mass S.μ.w (S.evE e) * mass S.μ.w (S.evDIB d)) (ω ω' : Ω) : S.polE ω = S.polE ω' := by
  -- every realized `(E, D_{I,B})` pair is realized jointly with every other realized value of the
  -- other coordinate
  have hjoint : ∀ ω₁ ω₂, ∃ ω₃, S.E ω₃ = S.E ω₁ ∧ S.DIB ω₃ = S.DIB ω₂ := by
    intro ω₁ ω₂
    have h := hind (S.E ω₁) (S.DIB ω₂)
    have h1 : 0 < mass S.μ.w (S.evE (S.E ω₁)) := mass_pos_of_nonempty S.pos ⟨ω₁, by simp⟩
    have h2 : 0 < mass S.μ.w (S.evDIB (S.DIB ω₂)) := mass_pos_of_nonempty S.pos ⟨ω₂, by simp⟩
    have h3 : 0 < mass S.μ.w (event fun ω => S.E ω = S.E ω₁ ∧ S.DIB ω = S.DIB ω₂) := by
      rw [h]; exact mul_pos h1 h2
    by_contra hne
    have h0 : (event fun ω => S.E ω = S.E ω₁ ∧ S.DIB ω = S.DIB ω₂) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω₃ hω₃
      rw [mem_event] at hω₃
      exact hne ⟨ω₃, hω₃⟩
    rw [h0] at h3
    simp [mass] at h3
  funext e
  -- `Π̈(ω)(e)` is read off a world with `D_{I,B} = D_{I,B}(ω)` and `Ö = e`, if there is one
  by_cases hreal : ∃ ω₁, S.DIB ω₁ = S.DIB ω ∧ S.oE ω₁ = e
  · obtain ⟨ω₁, h₁, h₂⟩ := hreal
    obtain ⟨ω₃, h₃, h₄⟩ := hjoint ω₁ ω'
    have hoE : S.oE ω₃ = e := by rw [← h₂]; exact S.oE_E ω₃ ω₁ h₃
    have haE : S.aE ω₃ = S.aE ω₁ := (Prod.mk.inj h₃).1
    calc S.polE ω e = S.polE ω (S.oE ω₁) := by rw [h₂]
      _ = S.aE ω₁ := S.polE_apply_of_DIB_eq h₁.symm
      _ = S.aE ω₃ := haE.symm
      _ = S.polE ω' (S.oE ω₃) := (S.polE_apply_of_DIB_eq h₄.symm).symm
      _ = S.polE ω' e := by rw [hoE]
  · -- `(e, D_{I,B}(ω))` unrealized ⟹ `(e, D_{I,B}(ω'))` unrealized too, and both read the junk
    have hreal' : ¬ ∃ ω₂, S.DIB ω₂ = S.DIB ω' ∧ S.oE ω₂ = e := by
      rintro ⟨ω₂, h₁, h₂⟩
      obtain ⟨ω₃, h₃, h₄⟩ := hjoint ω₂ ω
      exact hreal ⟨ω₃, h₄, by rw [← h₂]; exact S.oE_E ω₃ ω₂ h₃⟩
    have hj : ∀ ω₀, (¬ ∃ ω₂, S.DIB ω₂ = S.DIB ω₀ ∧ S.oE ω₂ = e) →
        S.polE ω₀ e = S.projAE (S.IB S.w₀).2 := by
      intro ω₀ h₀
      show S.projAE (S.rho (S.DIB ω₀) e).2 = _
      unfold AbstractDS.rho projOf
      have hex : ¬ ∃ ω₂, (S.oE ω₂, S.DIB ω₂) = (e, S.DIB ω₀) := by
        rintro ⟨ω₂, hω₂⟩
        exact h₀ ⟨ω₂, (Prod.mk.inj hω₂).2, (Prod.mk.inj hω₂).1⟩
      rw [dif_neg hex]
    rw [hj ω hreal, hj ω' hreal']

end Models

end

end Cleanroom.Udt.UdtCondenseDd
