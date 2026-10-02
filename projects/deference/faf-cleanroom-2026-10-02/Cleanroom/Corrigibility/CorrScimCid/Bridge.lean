import Cleanroom.Corrigibility.CorrScimCid.Scim
import FactoredSpaces.BayesNet
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The FAF bridge: the law of a SCIM factorizes over its DAG (T1, STANDARDS §1 check)

With finite value types, the law `law M := (M.eval hG)_* (⨂_v P v)` of a closed model is a
distribution on `Pt Val` that **factorizes over `G`** in FAF's sense (`FactorizesOverDAG`, §5.2
eq. (2)), with the CPD `φ v pa := (f v pa)_* (P v)` — decision rows under a policy being the point
masses `δ_{π(pa)}`. This is the check that the package's models are FAF's Bayesian networks: every
statement of the package about a law is a statement about an element of FAF's `dagFactorizing G Val`.

Proof: the law's mass at `x` is the total noise mass of `{ε | eval ε = x}`, and `eval ε = x` iff
every node's mechanism, fed the parent configuration of `x` and its own noise, returns `x`'s value
(`Scm.eval_eq_iff`, a well-founded induction); the product of the per-node pushforward masses expands
(`Fintype.prod_sum`) to the sum over noise points of the product of the per-node indicators, which is
the same set.

**Scope** (audit r1 B1): the bridge needs `[∀ v, Fintype (Val v)]`, which FAF's `Distr (Pt Val)`
requires. Every real-valued model of record in the package (`Fig1.Mdl`, `Dict.Mdl`,
`ThreeNode.Mdl`, `RocksDiamonds.Mdl`, `Fig1Link.Mdl`, `TwoLatent.Mdl` — all with a utility node in
`ℝ`, design decision 2) is therefore outside it: they are FAF Bayesian networks in graph and noise,
and their laws factorize in the same way, but FAF's `Distr` type cannot carry them. The bridge is
instantiated on the finite-valued twin of Fig. 1 (`Fig1Fin.law_factorizesOverDAG`).

Source: mandate T1 ("FAF bridge"); FAF `BayesNet.lean` §5.2 eq. (2).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)]

namespace Scm

variable (M : Scm G Val E) (hG : G.IsAcyclic)

/-- `eval ε = x` iff every mechanism, at `x`'s parent configuration and `ε`'s noise, returns `x`'s
value. (⇐ is the well-founded induction; ⇒ is the unfolding.)
Source: none: infrastructure
Kind: P -/
lemma eval_eq_iff (ε : Pt E) (x : Pt Val) :
    M.eval hG ε = x ↔ ∀ v, M.f v (parentConfig G Val x v) (ε v) = x v := by
  constructor
  · rintro rfl v
    exact (M.eval_apply hG ε v).symm
  · intro h
    funext v
    refine hG.wf.induction (C := fun v => M.eval hG ε v = x v) v ?_
    intro v ih
    rw [eval_apply]
    have hpc : parentConfig G Val (M.eval hG ε) v = parentConfig G Val x v :=
      funext fun u => ih u.1 ((Digraph.mem_parents G).mp u.2)
    rw [hpc]
    exact h v

variable [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- **The law** of a closed model on `Pt Val`: the pushforward of the product noise along evaluation.
Source: everitt-2021 Def. 1 ("`Pr(W = w) = ∑_{ε : W(ε) = w} P(ε)`")
Kind: D -/
noncomputable def law : Distr (Pt Val) := Distr.map (M.eval hG) M.μ

/-- **The CPD of a closed model**: the pushforward of each node's noise along its mechanism at a
parent configuration.
Source: FAF `BayesNet.lean` §5.2 eq. (2)
Kind: D -/
noncomputable def cpd : CPD (G := G) (Val := Val) := fun v pa => Distr.map (M.f v pa) (M.P v)

/-- **The FAF bridge**: the law of a closed model factorizes over its DAG, with `cpd M` as the CPD
family.
Source: mandate T1 (FAF bridge); FAF `FactorizesOverDAG` (§5.2 eq. (2))
Kind: P
Fidelity: exact
Hyps: — -/
theorem law_factorizesOverDAG : FactorizesOverDAG G Val (M.law hG) := by
  classical
  refine ⟨M.cpd, fun x => ?_⟩
  have hL : (M.law hG).mass x = ∑ ε, if M.eval hG ε = x then ∏ v, (M.P v).mass (ε v) else 0 := by
    unfold law
    rw [Distr.map_mass, Distr.prob]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, μ, Distr.prod_mass]
  have hcpd : ∀ v, (M.cpd v (parentConfig G Val x v)).mass (x v) =
      ∑ e, if M.f v (parentConfig G Val x v) e = x v then (M.P v).mass e else 0 := by
    intro v
    unfold cpd
    rw [Distr.map_mass, Distr.prob]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hR : ∏ v, (M.cpd v (parentConfig G Val x v)).mass (x v) =
      ∑ ε : Pt E, ∏ v, if M.f v (parentConfig G Val x v) (ε v) = x v then (M.P v).mass (ε v)
        else 0 := by
    simp only [hcpd]
    exact Fintype.prod_sum fun v e =>
      if M.f v (parentConfig G Val x v) e = x v then (M.P v).mass e else 0
  rw [hL, hR]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_implies, M.eval_eq_iff hG ε x]

end Scm

/-- The law of a SCIM under a policy factorizes over the CID, with decision rows `δ_{π(pa)}`.
Source: mandate T1 (FAF bridge)
Kind: C -/
theorem Scim.law_factorizesOverDAG [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]
    {C : Cid G Val} (M : Scim C E) (π : Policy C) :
    FactorizesOverDAG G Val ((M.withPolicy π).law C.acyclic) :=
  (M.withPolicy π).law_factorizesOverDAG C.acyclic

end Cleanroom.Corrigibility.CorrScimCid
