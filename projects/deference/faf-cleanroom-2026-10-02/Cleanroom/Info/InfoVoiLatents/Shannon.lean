import ShannonInformation.API

/-!
# info-voi-latents — generic Shannon lemmas FAF lacks (FAF API requests)

All at `ShannonInformation.FiniteEntropyOf` on countable discrete ranges, derived from FAF's
`condMutualInfo_eq'`, `chain_rule''`, `condEntropy_comp_ge`, `condEntropy_of_injective'`,
`IndepFun.condEntropy_eq_entropy` and PFR's `entropy_comp_of_injective`, `entropy_congr`.

* `condMutualInfo_le_condEntropy`: `I[X : Y | Z] ≤ H[X | Z]` (Target 9(c), "`I ≤ H`").
* `condMutualInfo_comp_le_right`/`_left`/`condMutualInfo_comp_comp_le`: conditional data
  processing at `FiniteEntropyOf` (PFR has it only at `FiniteRange`).
* `condMutualInfo_pair_right`: the chain rule `I[X : ⟨Y, W⟩ | Z] = I[X : Y | Z] + I[X : W | ⟨Y, Z⟩]`.
* `condMutualInfo_eq_zero_of_indepFun`: independent noise adds nothing, `I[X : ξ | Z] = 0` when
  `ξ ⊥ ⟨X, Z⟩` (Target 9(a); FAF has no such lemma).
* `mutualInfo_congr_left`, `condMutualInfo_congr_left`, `condMutualInfo_congr_right`: a.e.
  congruence (Target 10).
* `condMutualInfo_self`: `I[Y : Y | Z] = H[Y | Z]` (Target 10).
* `mutualInfo_pair_left`: the chain rule for mutual information
  `I[⟨X, Y⟩ : Z] = I[X : Z] + I[Y : Z | X]` (Target 4(iii)).

Mandate: Targets 4(iii), 9(a)(c), 10 (supporting lemmas).
-/

namespace Cleanroom.Info.InfoVoiLatents.Shannon

open MeasureTheory ProbabilityTheory ShannonInformation

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω S T U V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  [Countable S] [Countable T] [Countable U] [Countable V]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {W : Ω → V}

/-- **`I[X : Y | Z] ≤ H[X | Z]`**: conditional mutual information is at most the conditional
entropy of either argument.
Source: [[d1-special-case-final]] S2(c) l. 48, P2(c) l. 80 ("`I ≤ H`"); none: infrastructure
Kind: P
Fidelity: exact -/
theorem condMutualInfo_le_condEntropy (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    I[X : Y | Z ; μ] ≤ H[X | Z ; μ] := by
  rw [ShannonInformation.condMutualInfo_eq' hX hY hZ μ]
  linarith [condEntropy_nonneg X (⟨Y, Z⟩ : Ω → T × U) μ]

/-- **Conditional data processing, second argument**: `I[X : f ∘ Y | Z] ≤ I[X : Y | Z]` at
`FiniteEntropyOf` (PFR's `condMutual_comp_comp_le` needs `FiniteRange`). FAF API request.
Source: none: infrastructure (Targets 9(a), 10)
Kind: P
Fidelity: exact -/
theorem condMutualInfo_comp_le_right (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : T → V) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    I[X : f ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hf : Measurable f := measurable_of_countable f
  haveI : FiniteEntropyOf (f ∘ Y) μ := finiteEntropyOf_comp hY hf
  haveI : FiniteEntropyOf (⟨Y, Z⟩ : Ω → T × U) μ := finiteEntropyOf_pair hY hZ
  rw [ShannonInformation.condMutualInfo_eq' hX (hf.comp hY) hZ μ,
    ShannonInformation.condMutualInfo_eq' hX hY hZ μ]
  have h := ShannonInformation.condEntropy_comp_ge μ (hY.prodMk hZ) hX (Prod.map f id)
  have e : (Prod.map f id) ∘ (⟨Y, Z⟩ : Ω → T × U) = (⟨f ∘ Y, Z⟩ : Ω → V × U) := funext fun ω => rfl
  rw [e] at h
  linarith

/-- **Conditional data processing, first argument**: `I[f ∘ X : Y | Z] ≤ I[X : Y | Z]`.
Source: none: infrastructure
Kind: P
Fidelity: exact -/
theorem condMutualInfo_comp_le_left (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : S → V) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    I[f ∘ X : Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hf : Measurable f := measurable_of_countable f
  rw [condMutualInfo_comm (hf.comp hX) hY, condMutualInfo_comm hX hY]
  exact condMutualInfo_comp_le_right hY hX hZ f

/-- **Conditional data processing, both arguments**: `I[f ∘ X : g ∘ Y | Z] ≤ I[X : Y | Z]`.
Source: none: infrastructure (Target 10's "conditionally independent variables have
conditionally independent images")
Kind: C
Fidelity: exact -/
theorem condMutualInfo_comp_comp_le {V' : Type*} [MeasurableSpace V'] [Countable V']
    [MeasurableSingletonClass V'] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : S → V) (g : T → V') [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hf : Measurable f := measurable_of_countable f
  haveI : FiniteEntropyOf (f ∘ X) μ := finiteEntropyOf_comp hX hf
  calc I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[f ∘ X : Y | Z ; μ] :=
        condMutualInfo_comp_le_right (hf.comp hX) hY hZ g
    _ ≤ I[X : Y | Z ; μ] := condMutualInfo_comp_le_left hX hY hZ f

/-- **Chain rule for conditional mutual information**:
`I[X : ⟨Y, W⟩ | Z] = I[X : Y | Z] + I[X : W | ⟨Y, Z⟩]`.
Source: none: infrastructure (Targets 4(iii), 9(a))
Kind: P
Fidelity: exact -/
theorem condMutualInfo_pair_right (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hW : Measurable W) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ]
    [FiniteEntropyOf W μ] :
    I[X : (⟨Y, W⟩ : Ω → T × V) | Z ; μ] = I[X : Y | Z ; μ] + I[X : W | (⟨Y, Z⟩ : Ω → T × U) ; μ] := by
  haveI : FiniteEntropyOf (⟨Y, W⟩ : Ω → T × V) μ := finiteEntropyOf_pair hY hW
  haveI : FiniteEntropyOf (⟨Y, Z⟩ : Ω → T × U) μ := finiteEntropyOf_pair hY hZ
  haveI : FiniteEntropyOf (⟨(⟨Y, W⟩ : Ω → T × V), Z⟩ : Ω → (T × V) × U) μ :=
    finiteEntropyOf_pair (hY.prodMk hW) hZ
  rw [ShannonInformation.condMutualInfo_eq' hX (hY.prodMk hW) hZ μ,
    ShannonInformation.condMutualInfo_eq' hX hY hZ μ,
    ShannonInformation.condMutualInfo_eq' hX hW (hY.prodMk hZ) μ]
  have e : H[X | (⟨(⟨Y, W⟩ : Ω → T × V), Z⟩ : Ω → (T × V) × U) ; μ]
      = H[X | (⟨W, (⟨Y, Z⟩ : Ω → T × U)⟩ : Ω → V × (T × U)) ; μ] := by
    have hf : Function.Injective (fun p : (T × V) × U => (p.1.2, (p.1.1, p.2))) := by
      rintro ⟨⟨y, w⟩, z⟩ ⟨⟨y', w'⟩, z'⟩ h
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    have := ShannonInformation.condEntropy_of_injective' μ hX ((hY.prodMk hW).prodMk hZ)
      (fun p : (T × V) × U => (p.1.2, (p.1.1, p.2))) hf
      ((measurable_of_countable _).comp ((hY.prodMk hW).prodMk hZ))
    exact this.symm
  rw [e]
  ring

/-- **Independent noise adds nothing**: if `ξ` is independent of `⟨X, Z⟩` then `I[X : ξ | Z] = 0`.
FAF has no ready lemma for this; proved here from `IndepFun.condEntropy_eq_entropy`.
Source: [[d1-special-case-final]] P2(a) l. 80 ("`Pr = g(F_H, ξ)` with `ξ` independent");
none: infrastructure (FAF API request)
Kind: P
Fidelity: exact -/
theorem condMutualInfo_eq_zero_of_indepFun {ξ : Ω → V} (hX : Measurable X) (hZ : Measurable Z)
    (hξ : Measurable ξ) [FiniteEntropyOf X μ] [FiniteEntropyOf Z μ] [FiniteEntropyOf ξ μ]
    (hind : IndepFun ξ (⟨X, Z⟩ : Ω → S × U) μ) : I[X : ξ | Z ; μ] = 0 := by
  haveI : FiniteEntropyOf (⟨X, Z⟩ : Ω → S × U) μ := finiteEntropyOf_pair hX hZ
  rw [condMutualInfo_comm hX hξ, ShannonInformation.condMutualInfo_eq' hξ hX hZ μ]
  have h1 : H[ξ | (⟨X, Z⟩ : Ω → S × U) ; μ] = H[ξ ; μ] :=
    ShannonInformation.IndepFun.condEntropy_eq_entropy hind hξ (hX.prodMk hZ)
  have hZind : IndepFun ξ Z μ := by
    have := hind.comp measurable_id (measurable_snd : Measurable (Prod.snd : S × U → U))
    exact this
  have h2 : H[ξ | Z ; μ] = H[ξ ; μ] :=
    ShannonInformation.IndepFun.condEntropy_eq_entropy hZind hξ hZ
  rw [h1, h2, sub_self]

/-- Mutual information respects a.e. equality in the first argument.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mutualInfo_congr_left {ν : Measure Ω} {X' : Ω → S} (h : X =ᵐ[ν] X') :
    I[X : Y ; ν] = I[X' : Y ; ν] := by
  simp only [mutualInfo_def]
  rw [entropy_congr h, entropy_congr (Filter.EventuallyEq.prodMk h (Filter.EventuallyEq.refl _ Y))]

/-- **Conditional mutual information respects a.e. equality** in the first argument: the
integrand agrees on every fibre because `μ[|Z ⁻¹' {z}] ≪ μ`.
Source: none: infrastructure (Target 10)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_congr_left {X' : Ω → S} (h : X =ᵐ[μ] X') :
    I[X : Y | Z ; μ] = I[X' : Y | Z ; μ] := by
  rw [condMutualInfo_eq_integral_mutualInfo, condMutualInfo_eq_integral_mutualInfo]
  congr 1
  funext z
  exact mutualInfo_congr_left (cond_absolutelyContinuous.ae_eq h)

/-- Conditional mutual information respects a.e. equality in the second argument.
Source: none: infrastructure (Target 10)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_congr_right {Y' : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    (hY' : Measurable Y') (h : Y =ᵐ[μ] Y') : I[X : Y | Z ; μ] = I[X : Y' | Z ; μ] := by
  rw [condMutualInfo_comm hX hY, condMutualInfo_comm hX hY']
  exact condMutualInfo_congr_left h

/-- **`I[Y : Y | Z] = H[Y | Z]`**: a variable's conditional information about itself is its
conditional entropy.
Source: none: infrastructure (Target 10)
Kind: P
Fidelity: exact -/
theorem condMutualInfo_self (hY : Measurable Y) (hZ : Measurable Z) [FiniteEntropyOf Y μ]
    [FiniteEntropyOf Z μ] : I[Y : Y | Z ; μ] = H[Y | Z ; μ] := by
  haveI : FiniteEntropyOf (⟨Y, Y⟩ : Ω → T × T) μ := finiteEntropyOf_pair hY hY
  rw [ShannonInformation.condMutualInfo_eq hY hY hZ μ]
  have e : H[(⟨Y, Y⟩ : Ω → T × T) | Z ; μ] = H[Y | Z ; μ] := by
    rw [ShannonInformation.chain_rule'' μ (hY.prodMk hY) hZ, ShannonInformation.chain_rule'' μ hY hZ]
    have hf : Function.Injective (fun p : T × U => ((p.1, p.1), p.2)) := by
      rintro ⟨y, z⟩ ⟨y', z'⟩ h
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨⟨rfl, -⟩, rfl⟩
      rfl
    have := entropy_comp_of_injective μ (hY.prodMk hZ) (fun p : T × U => ((p.1, p.1), p.2)) hf
    have e2 : (fun p : T × U => ((p.1, p.1), p.2)) ∘ (⟨Y, Z⟩ : Ω → T × U)
        = (⟨(⟨Y, Y⟩ : Ω → T × T), Z⟩ : Ω → (T × T) × U) := funext fun ω => rfl
    rw [e2] at this
    rw [this]
  rw [e]
  ring

/-- `H[X | X] = 0`: a variable is determined by itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condEntropy_self (hX : Measurable X) [FiniteEntropyOf X μ] : H[X | X ; μ] = 0 := by
  rw [ShannonInformation.chain_rule'' μ hX hX]
  have hf : Function.Injective (fun x : S => (x, x)) := fun a b h => (Prod.mk.inj h).1
  have := entropy_comp_of_injective μ hX (fun x : S => (x, x)) hf
  have e : (fun x : S => (x, x)) ∘ X = (⟨X, X⟩ : Ω → S × S) := funext fun ω => rfl
  rw [e] at this
  rw [this, sub_self]

/-- `I[X : X | X] = 0`: the degenerate natural latent (`Λ = X₁ = X₂`) has all three errors `0`.
Source: none: infrastructure (Target 1 witness)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_self_self (hX : Measurable X) [FiniteEntropyOf X μ] :
    I[X : X | X ; μ] = 0 := by
  rw [condMutualInfo_self hX hX, condEntropy_self hX]

/-- `I[X : Y | X] = 0`: given itself, a variable carries no further information about anything.
Source: none: infrastructure (Target 10 witness: `Λ = X₁` mediates trivially)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_self_left (hX : Measurable X) (hY : Measurable Y) [FiniteEntropyOf X μ]
    [FiniteEntropyOf Y μ] : I[X : Y | X ; μ] = 0 := by
  haveI : FiniteEntropyOf (⟨Y, X⟩ : Ω → T × S) μ := finiteEntropyOf_pair hY hX
  rw [ShannonInformation.condMutualInfo_eq' hX hY hX μ, condEntropy_self hX,
    ShannonInformation.chain_rule'' μ hX (hY.prodMk hX)]
  have hf : Function.Injective (fun p : T × S => (p.2, p)) := fun a b h => (Prod.mk.inj h).2
  have := entropy_comp_of_injective μ (hY.prodMk hX) (fun p : T × S => (p.2, p)) hf
  have e : (fun p : T × S => (p.2, p)) ∘ (⟨Y, X⟩ : Ω → T × S)
      = (⟨X, (⟨Y, X⟩ : Ω → T × S)⟩ : Ω → S × (T × S)) := funext fun ω => rfl
  rw [e] at this
  rw [this]
  ring

/-- **Chain rule for mutual information**: `I[⟨X, Y⟩ : Z] = I[X : Z] + I[Y : Z | X]`.
Source: [[generalization-final]] D11 l. 47, P3(a) l. 113 ("`I(ω_A; E) = I(Λ_A; E) + I(θ_A; E | Λ_A)`
by the chain rule"); none: infrastructure
Kind: P
Fidelity: exact -/
theorem mutualInfo_pair_left (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    I[(⟨X, Y⟩ : Ω → S × T) : Z ; μ] = I[X : Z ; μ] + I[Y : Z | X ; μ] := by
  haveI : FiniteEntropyOf (⟨X, Y⟩ : Ω → S × T) μ := finiteEntropyOf_pair hX hY
  haveI : FiniteEntropyOf (⟨Y, X⟩ : Ω → T × S) μ := finiteEntropyOf_pair hY hX
  rw [ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy' (hX.prodMk hY) hZ μ,
    ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy' hX hZ μ,
    condMutualInfo_comm hY hZ, ShannonInformation.condMutualInfo_eq' hZ hY hX μ]
  have e : H[Z | (⟨X, Y⟩ : Ω → S × T) ; μ] = H[Z | (⟨Y, X⟩ : Ω → T × S) ; μ] := by
    have := ShannonInformation.condEntropy_of_injective' μ hZ (hY.prodMk hX) Prod.swap
      Prod.swap_injective (measurable_swap.comp (hY.prodMk hX))
    have e2 : Prod.swap ∘ (⟨Y, X⟩ : Ω → T × S) = (⟨X, Y⟩ : Ω → S × T) := funext fun ω => rfl
    rw [e2] at this
    exact this
  rw [e]
  ring

/-! ### Conditioning-pair bookkeeping (audit r2 probe `ApproxBound.lean`, promoted) -/

/-- **Swapping the conditioning pair**: `I[X : Y | ⟨Z, W⟩] = I[X : Y | ⟨W, Z⟩]` (through
`condMutualInfo_eq'` and `condEntropy_of_injective'` with `Prod.swap`).
Source: none: infrastructure (audit r2, adversarial item 2)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_cond_swap (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hW : Measurable W) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ]
    [FiniteEntropyOf W μ] :
    I[X : Y | (⟨Z, W⟩ : Ω → U × V) ; μ] = I[X : Y | (⟨W, Z⟩ : Ω → V × U) ; μ] := by
  haveI : FiniteEntropyOf (⟨Z, W⟩ : Ω → U × V) μ := finiteEntropyOf_pair hZ hW
  haveI : FiniteEntropyOf (⟨W, Z⟩ : Ω → V × U) μ := finiteEntropyOf_pair hW hZ
  haveI : FiniteEntropyOf (⟨Y, (⟨Z, W⟩ : Ω → U × V)⟩ : Ω → T × (U × V)) μ :=
    finiteEntropyOf_pair hY (hZ.prodMk hW)
  haveI : FiniteEntropyOf (⟨Y, (⟨W, Z⟩ : Ω → V × U)⟩ : Ω → T × (V × U)) μ :=
    finiteEntropyOf_pair hY (hW.prodMk hZ)
  rw [ShannonInformation.condMutualInfo_eq' hX hY (hZ.prodMk hW) μ,
    ShannonInformation.condMutualInfo_eq' hX hY (hW.prodMk hZ) μ]
  have e1 : H[X | (⟨Z, W⟩ : Ω → U × V) ; μ] = H[X | (⟨W, Z⟩ : Ω → V × U) ; μ] := by
    have := ShannonInformation.condEntropy_of_injective' μ hX (hW.prodMk hZ) Prod.swap
      Prod.swap_injective (measurable_swap.comp (hW.prodMk hZ))
    have e : Prod.swap ∘ (⟨W, Z⟩ : Ω → V × U) = (⟨Z, W⟩ : Ω → U × V) := funext fun ω => rfl
    rw [e] at this
    exact this
  have e2 : H[X | (⟨Y, (⟨Z, W⟩ : Ω → U × V)⟩ : Ω → T × (U × V)) ; μ]
      = H[X | (⟨Y, (⟨W, Z⟩ : Ω → V × U)⟩ : Ω → T × (V × U)) ; μ] := by
    have hf : Function.Injective (fun p : T × (V × U) => (p.1, Prod.swap p.2)) := by
      rintro ⟨y, w, z⟩ ⟨y', w', z'⟩ h
      simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    have := ShannonInformation.condEntropy_of_injective' μ hX (hY.prodMk (hW.prodMk hZ))
      (fun p : T × (V × U) => (p.1, Prod.swap p.2)) hf
      ((measurable_of_countable _).comp (hY.prodMk (hW.prodMk hZ)))
    have e : (fun p : T × (V × U) => (p.1, Prod.swap p.2))
        ∘ (⟨Y, (⟨W, Z⟩ : Ω → V × U)⟩ : Ω → T × (V × U))
        = (⟨Y, (⟨Z, W⟩ : Ω → U × V)⟩ : Ω → T × (U × V)) := funext fun ω => rfl
    rw [e] at this
    exact this
  rw [e1, e2]

/-- Dropping the first component of a pair in the first argument: `I[Y : Z | W] ≤ I[⟨X, Y⟩ : Z | W]`
(data processing along `Prod.snd`).
Source: none: infrastructure (audit r2, adversarial item 2)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_snd_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hW : Measurable W) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ]
    [FiniteEntropyOf W μ] :
    I[Y : Z | W ; μ] ≤ I[(⟨X, Y⟩ : Ω → S × T) : Z | W ; μ] := by
  haveI : FiniteEntropyOf (⟨X, Y⟩ : Ω → S × T) μ := finiteEntropyOf_pair hX hY
  have := condMutualInfo_comp_le_left (μ := μ) (hX.prodMk hY) hZ hW (Prod.snd : S × T → T)
  exact this

/-- Swapping the pair in the second argument: `I[X : ⟨Y, Z⟩ | W] ≤ I[X : ⟨Z, Y⟩ | W]` (data
processing along `Prod.swap`; with the symmetric instance, an equality).
Source: none: infrastructure (audit r2, adversarial item 2)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_swap_right_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hW : Measurable W) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ]
    [FiniteEntropyOf W μ] :
    I[X : (⟨Y, Z⟩ : Ω → T × U) | W ; μ] ≤ I[X : (⟨Z, Y⟩ : Ω → U × T) | W ; μ] := by
  haveI : FiniteEntropyOf (⟨Z, Y⟩ : Ω → U × T) μ := finiteEntropyOf_pair hZ hY
  have := condMutualInfo_comp_le_right (μ := μ) hX (hZ.prodMk hY) hW (Prod.swap : U × T → T × U)
  exact this

/-- **Conditioning on more, or including it in the second argument**:
`I[X : Z | ⟨Y, W⟩] ≤ I[X : ⟨Y, Z⟩ | W]` (the chain rule `condMutualInfo_pair_right` and
nonnegativity).
Source: none: infrastructure (audit r2, adversarial item 2)
Kind: L
Fidelity: n/a -/
theorem condMutualInfo_le_pair_of_cond (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hW : Measurable W) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ]
    [FiniteEntropyOf W μ] :
    I[X : Z | (⟨Y, W⟩ : Ω → T × V) ; μ] ≤ I[X : (⟨Y, Z⟩ : Ω → T × U) | W ; μ] := by
  rw [condMutualInfo_pair_right hX hY hW hZ]
  have h0 : 0 ≤ I[X : Y | W ; μ] := ShannonInformation.condMutualInfo_nonneg hX hY
  linarith

end

end Cleanroom.Info.InfoVoiLatents.Shannon
