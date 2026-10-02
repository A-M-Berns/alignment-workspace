import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Cleanroom.Corrigibility.CorrScimCid.ThreeNode

/-!
# A witness for the CPD form of ancestor invariance (LB1, audit r1 N2/N3)

Two CPD families on the all-`Bool` chain `D → X → U` (the graph of `ThreeNode`) that agree on the
ancestrally closed set `S = {D, X}` (`D` uniform, `X` copies `D`) and differ at `U` (`U = true`
versus `U = false`). `marg_tau_tauInv_eq_of_agree` gives equal `S`-marginals of the two laws FAF
builds through `tau ∘ tauInv`; the full laws differ (mass `1/2` versus `0` at the all-`true`
point). So the theorem's content — the marginal on `S` ignores the mechanisms outside `S` — is
exercised on an instance where the laws are genuinely different and the `S`-marginal is not a
point mass. Grade N+.

Source: holtman-2021 §8 (l. 915–926); mandate T2(a).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces

/-- The mass of `tau (tauInv ψ)` at a joint value is the product of the CPD masses (FAF's
`tau_tauInv` argument, extracted as a lemma).
Source: none: infrastructure (FAF `BayesNet.lean` `tau_tauInv`)
Kind: L -/
lemma tau_tauInv_mass {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    {Val : V → Type} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] (hG : G.IsAcyclic)
    (ψ : CPD (G := G) (Val := Val)) (x : Pt Val) :
    (tau hG (tauInv ψ)).mass x = ∏ v, (ψ v (parentConfig G Val x v)).mass (x v) := by
  rw [tau_mass, prob_jointVar_fiber hG (factorizes_tauInv ψ) x]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [show (tauInv ψ).margAt ⟨v, parentConfig G Val x v⟩ = ψ v (parentConfig G Val x v) from
    Distr.margAt_prod _ _]

namespace CpdWitness

open ThreeNode (Node G rank)
open ThreeNode.Node

/-- All-`Bool` values on the chain.
Source: none: infrastructure
Kind: D -/
def ValB : Node → Type := fun _ => Bool

instance instFintypeValB : ∀ v, Fintype (ValB v) := fun _ => inferInstanceAs (Fintype Bool)
instance instDecidableEqValB : ∀ v, DecidableEq (ValB v) := fun _ => inferInstanceAs (DecidableEq Bool)
instance instInhabitedValB : ∀ v, Inhabited (ValB v) := fun _ => inferInstanceAs (Inhabited Bool)

lemma G_acyclic : G.IsAcyclic := Digraph.isAcyclic_of_rank rank (by decide)

/-- `φ`: `D` uniform, `X` copies `D`, `U = true`.
Source: none: infrastructure
Kind: D -/
noncomputable def φ : CPD (G := G) (Val := ValB) := fun v => match v with
  | D => fun _ => (Distr.uniform : Distr Bool)
  | X => fun pa => Distr.delta (pa ⟨D, by decide⟩)
  | U => fun _ => Distr.delta true

/-- `φ'`: as `φ` on `D`, `X`; `U = false`.
Source: none: infrastructure
Kind: D -/
noncomputable def φ' : CPD (G := G) (Val := ValB) := fun v => match v with
  | D => fun _ => (Distr.uniform : Distr Bool)
  | X => fun pa => Distr.delta (pa ⟨D, by decide⟩)
  | U => fun _ => Distr.delta false

/-- The ancestrally closed set `{D, X}`.
Source: none: infrastructure
Kind: D -/
def S : Finset Node := {D, X}

lemma S_ancClosed : G.AncClosed S := by
  show ∀ v ∈ S, G.parents v ⊆ S
  decide

lemma agree : ∀ v ∈ S, φ v = φ' v := by
  intro v hv
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> rfl

lemma differ_U : φ U ≠ φ' U := by
  intro h
  have h1 := congrArg (fun d => Distr.mass d true) (congrFun h fun _ => true)
  simp [φ, φ', Distr.delta_mass] at h1

/-- The all-`true` joint value.
Source: none: infrastructure
Kind: D -/
def x₀ : Pt ValB := fun _ => true

lemma mass_φ : (tau G_acyclic (tauInv φ)).mass x₀ = 1 / 2 := by
  rw [tau_tauInv_mass, Finset.prod_eq_single D]
  · show (Distr.uniform : Distr Bool).mass true = _
    simp [Distr.uniform]
  · intro v _ hv
    cases v
    · exact absurd rfl hv
    · show (Distr.delta (x₀ D)).mass (x₀ X) = 1
      simp [x₀, Distr.delta_mass]
    · show (Distr.delta true).mass (x₀ U) = 1
      simp [x₀, Distr.delta_mass]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma mass_φ' : (tau G_acyclic (tauInv φ')).mass x₀ = 0 := by
  rw [tau_tauInv_mass]
  refine Finset.prod_eq_zero (Finset.mem_univ U) ?_
  show (Distr.delta false).mass (x₀ U) = 0
  simp [x₀, Distr.delta_mass]

/-- The two laws differ.
Source: none: infrastructure
Kind: L -/
theorem laws_ne : tau G_acyclic (tauInv φ) ≠ tau G_acyclic (tauInv φ') := by
  intro h
  have this : (tau G_acyclic (tauInv φ)).mass x₀ = (tau G_acyclic (tauInv φ')).mass x₀ := by
    rw [h]
  rw [mass_φ, mass_φ'] at this
  norm_num at this

/-- Their `{D, X}`-marginals agree, by LB1.
Source: holtman-2021 §8
Kind: L -/
theorem marg_eq : (tau G_acyclic (tauInv φ)).marg S = (tau G_acyclic (tauInv φ')).marg S :=
  marg_tau_tauInv_eq_of_agree G_acyclic S_ancClosed φ φ' agree

/-- **LB1's witness**: an ancestrally closed `S`, two CPD families agreeing on `S` and differing off
it, whose FAF laws differ but have the same `S`-marginal.
Source: holtman-2021 §8 (l. 915–926); mandate T2(a)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem cpd_witness :
    G.AncClosed S ∧ (∀ v ∈ S, φ v = φ' v) ∧ φ U ≠ φ' U ∧
      (tau G_acyclic (tauInv φ)).marg S = (tau G_acyclic (tauInv φ')).marg S ∧
      tau G_acyclic (tauInv φ) ≠ tau G_acyclic (tauInv φ') :=
  ⟨S_ancClosed, agree, differ_U, marg_eq, laws_ne⟩

end CpdWitness

end Cleanroom.Corrigibility.CorrScimCid
