import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Blackwell definitions of record (finite experiments)

Package `lit-ddb-frames`, Target 5. Definitions only: Blackwell's theorem, garbling monotonicity
and refinement facts are `tt-finite-frames`'s. Consumers: fixpoint-lit-025 (partitional
Blackwell, Geanakoplos), corr-wf13-010 (garbling monotonicity), trust-lab-2-030 (calibrated
garbling of a signal map), corr-wf14-015/019/038 (binary sensors), trust-lab-004/039
(refinement).

An experiment is a finite stochastic kernel `k : W → S → ℝ` with every row in `stdSimplex ℝ S`.
Mathlib's `Matrix.rowStochastic` is a submonoid of *square* matrices and is not this object.
-/

namespace Cleanroom.Found.LitDdbFrames.Blackwell

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W S T : Type} [Fintype W] [Fintype S] [Fintype T]

/-- A finite *experiment* (signal structure, information structure): a stochastic kernel from
states `W` to signals `S`, each row a distribution.
Source: none: infrastructure (Blackwell 1953; consumers listed in the module docstring)
Kind: D
Fidelity: exact -/
structure Experiment (W S : Type) [Fintype S] where
  /-- the likelihood of each signal at each state -/
  k : W → S → ℝ
  /-- each row is a probability distribution over signals -/
  k_mem : ∀ w, k w ∈ stdSimplex ℝ S

/-- A map `g : S → T → ℝ` is *stochastic* when every row is a distribution.
Source: none: infrastructure (Blackwell 1953)
Kind: D
Fidelity: exact -/
def Stochastic (g : S → T → ℝ) : Prop := ∀ s, g s ∈ stdSimplex ℝ T

/-- `k₂` is the garbling of `k₁` through `g`: `k₂ w t = ∑ s, k₁ w s · g s t` (post-processing the
signal of `k₁` by the channel `g` yields `k₂`).
Source: none: infrastructure (Blackwell 1953)
Kind: D
Fidelity: exact -/
def IsGarbling (k₁ : Experiment W S) (k₂ : Experiment W T) (g : S → T → ℝ) : Prop :=
  ∀ w t, k₂.k w t = ∑ s, k₁.k w s * g s t

/-- The **Blackwell order** `BlackwellLE k₂ k₁`: `k₁` is at least as informative as `k₂`, i.e.
`k₂` is a garbling of `k₁` through some stochastic `g`. The *first* argument is the less
informative experiment.
Source: none: infrastructure (Blackwell 1953; consumers fixpoint-lit-025, corr-wf13-010)
Kind: D
Fidelity: exact -/
def BlackwellLE (k₂ : Experiment W T) (k₁ : Experiment W S) : Prop :=
  ∃ g : S → T → ℝ, Stochastic g ∧ IsGarbling k₁ k₂ g

/-- The strict Blackwell order: `k₁` strictly more informative than `k₂`.
Source: none: infrastructure (Blackwell 1953)
Kind: D
Fidelity: exact -/
def BlackwellLT (k₂ : Experiment W T) (k₁ : Experiment W S) : Prop :=
  BlackwellLE k₂ k₁ ∧ ¬ BlackwellLE k₁ k₂

/-- The deterministic experiment of a signal map `f : W → S` (a partition is the map to its
cells): the kernel `k w s = 𝟙[f w = s]`.
Source: none: infrastructure (partitional information; consumers fixpoint-lit-025,
trust-lab-004/039)
Kind: D
Fidelity: exact -/
def ofMap [DecidableEq S] (f : W → S) : Experiment W S where
  k := fun w s => if f w = s then 1 else 0
  k_mem := fun w => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by simp⟩

/-- `f₁` *refines* `f₂` (the partition of `f₁` is finer): `f₂` factors through `f₁`.
Source: none: infrastructure (consumers trust-lab-004/039)
Kind: D
Fidelity: exact -/
def Refines (f₁ : W → S) (f₂ : W → T) : Prop := ∃ h : S → T, f₂ = h ∘ f₁

/-- A refinement is a garbling: if `f₂ = h ∘ f₁` then `ofMap f₂` is Blackwell-below `ofMap f₁`,
through the deterministic channel `g s t = 𝟙[h s = t]`.
Source: none: infrastructure (Target 5)
Kind: L
Fidelity: n/a -/
theorem Refines.blackwellLE [DecidableEq S] [DecidableEq T] {f₁ : W → S} {f₂ : W → T}
    (hf : Refines f₁ f₂) : BlackwellLE (ofMap f₂) (ofMap f₁) := by
  obtain ⟨h, rfl⟩ := hf
  refine ⟨fun s t => if h s = t then 1 else 0,
    fun s => ⟨fun t => by dsimp only; split_ifs <;> norm_num, by simp⟩, ?_⟩
  intro w t
  simp only [ofMap, Function.comp, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (f₁ w)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (mem_univ _) h

/-- **Decision value** (Bayes value) of an experiment for a prior `μ` and a menu of `n + 1`
options `u`: the best expected utility over all decision rules `δ : S → Fin (n + 1)`,
`max_δ ∑ w, μ w · ∑ s, k w s · u (δ s) w`. Menus indexed by `Fin (n + 1)` for all `n` are all
nonempty finite menus without quantifying over `Type`.
Source: none: infrastructure (Blackwell 1953)
Kind: D
Fidelity: exact -/
def bayesValue [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) : ℝ :=
  (univ : Finset (S → Fin (n + 1))).sup' univ_nonempty
    (fun δ => ∑ w, μ w * ∑ s, k.k w s * u (δ s) w)

/-- `k₁` is *more valuable* than `k₂`: for every prior in the simplex and every nonempty finite
menu, the Bayes value of `k₁` is at least that of `k₂`. Blackwell's theorem (`tt-finite-frames`)
identifies this with `BlackwellLE k₂ k₁`.
Source: none: infrastructure (Blackwell 1953)
Kind: D
Fidelity: exact -/
def MoreValuable [DecidableEq S] [DecidableEq T] (k₁ : Experiment W S) (k₂ : Experiment W T) :
    Prop :=
  ∀ μ ∈ stdSimplex ℝ W, ∀ (n : ℕ) (u : Fin (n + 1) → W → ℝ), bayesValue μ k₂ u ≤ bayesValue μ k₁ u

/-- The mass `μ(f = f w)` of the fibre of a signal map through `w`.
Source: none: infrastructure (consumer trust-lab-2-030)
Kind: D
Fidelity: exact -/
def fibreMass [DecidableEq S] (μ : W → ℝ) (f : W → S) (w : W) : ℝ :=
  ∑ v ∈ univ.filter (fun v => f v = f w), μ v

/-- The **conditional-mean report** (calibrated garbling) of a quantity `θ` through a signal map
`f`: `w ↦ E_μ[θ | f = f w]`, as the ratio `∑_{f v = f w} μ v θ v / μ(f = f w)`. On a `μ`-null
fibre Lean's `x / 0 = 0` gives the junk value `0`; `calibratedGarbling_mul_fibreMass` is the
product-guarded characterisation consumers should use.
Source: none: infrastructure (consumer trust-lab-2-030)
Kind: D
Fidelity: exact (under `0 < fibreMass μ f w`; see docstring) -/
def calibratedGarbling [DecidableEq S] (μ θ : W → ℝ) (f : W → S) : W → ℝ :=
  fun w => (∑ v ∈ univ.filter (fun v => f v = f w), μ v * θ v) / fibreMass μ f w

/-- Product-guarded characterisation of the conditional-mean report: on a positive-mass fibre,
`E_μ[θ | f = f w] · μ(f = f w) = ∑_{f v = f w} μ v θ v`.
Source: none: infrastructure (Target 5)
Kind: L
Fidelity: n/a -/
theorem calibratedGarbling_mul_fibreMass [DecidableEq S] (μ θ : W → ℝ) (f : W → S) (w : W)
    (h : 0 < fibreMass μ f w) :
    calibratedGarbling μ θ f w * fibreMass μ f w =
      ∑ v ∈ univ.filter (fun v => f v = f w), μ v * θ v := by
  unfold calibratedGarbling
  exact div_mul_cancel₀ _ h.ne'

end

end Cleanroom.Found.LitDdbFrames.Blackwell
