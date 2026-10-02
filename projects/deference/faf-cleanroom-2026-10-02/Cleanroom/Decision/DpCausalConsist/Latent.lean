import Cleanroom.Decision.DpCausalConsist.Dags
import Cleanroom.Decision.DpCausalConsist.Defs

/-!
# `dp-causal-consist`: Corollary 3.1(d), latent cancellation (T4(d))

Coordinates `0 = U` (the latent), `1 = m`, `2 = k`; the DAG `U → m`, `U → k`, `m → k` is `gLMK`
with `U` in the `ℓ` slot. The law `latentP`: `P(U = 1) = 1/2`, `P(m = 1 | U) = (4/5, 1/5)` at
`U = (1, 0)`, and `P(k = 1 | m, U)`: `7/10` at `(m, U) = (1, 0)`, `3/10` at `(1, 1)`, `1/4` at
`(0, 0)`, `9/10` at `(0, 1)` — the four numbers recomputed from the wiki's targets (finding §6.6:
the inventory's tuple `(3/10, 7/10, 9/10, 1/4)` is this table read in the order
`(1,1), (1,0), (0,1), (0,0)`). Then:

* `latentP` factorizes over the DAG (`sLatent_isFor`);
* the observable marginal has `m ⊥ k` — FAF's `CondIndepVar` with trivial conditioning
  (`latentP_m_indep_k`), and `P(k | m = 1) = P(k | m = 0) = 19/50` (`latentP_k_given`): the
  faithfulness violation, so the `(m, k)`-marginal is Markov to the empty graph;
* `P(k | do m = 1) = 1/2`, `P(k | do m = 0) = 23/40` (`sLatent_truncate_k`): an effect of `−3/40`
  that no observational record removes (`latent_effect`);
* **the empty structure** (repair round 1): the edgeless DAG `gEmpty` on `(U, m, k)` with the
  product law `latentQ` of `latentP`'s marginals — compatible (`sEmpty_isFor`), with the same
  `(m, k)`-marginal as `latentP` (`latentP_marg_eq_latentQ`), and effect-free by Pearl's
  invariance (`sEmpty_truncate_k`, `sEmpty_effect`);
* a prior `(w, 1 − w)` over the two structures gives Definition 25's mixed supposition
  (`mixState` of the two `cfG`s) the effect `−3w/40` on `{k = 1}` (`latent_mixture_effect`).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree FactoredSpaces Finset

/-- `P(k = 1 | m, U)`. Source: mandate T4(d) (recomputed, finding §6.6). Kind: D -/
noncomputable def latK (m U : Bool) : ℝ :=
  match m, U with
  | true, false => 7/10
  | true, true => 3/10
  | false, false => 1/4
  | false, true => 9/10

/-- `P(m = 1 | U)`. Source: mandate T4(d) (`P(m=1|U) = (4/5, 1/5)`). Kind: D -/
noncomputable def latM (U : Bool) : ℝ := if U then 4/5 else 1/5

/-- The mass table of the latent law. Source: mandate T4(d). Kind: D -/
noncomputable def latMass (U m k : Bool) : ℝ :=
  (1/2) * (if m then latM U else 1 - latM U) * (if k then latK m U else 1 - latK m U)

/-- **The latent-cancellation law** on `(U, m, k)`.
Source: [[learning-cdt-renderings]] "Checks" ("Latent cancellation: `U → m`, `U → k`, `m → k`
with `P(k | m=1) = P(k | m=0) = 0.38` and `P(k | do m) = (0.500, 0.575)`"); mandate T4(d)
Kind: D -/
noncomputable def latentP : Distr W3 :=
  distr3 latMass (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num [latMass, latM, latK])
    (by norm_num [latMass, latM, latK])

/-- The rate table of the latent structure. Source: mandate T4(d). Kind: D -/
noncomputable def rLatent : Rate3 where
  r v U m _ := match v with
    | 0 => 1/2
    | 1 => latM U
    | 2 => latK m U
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [latM, latK]
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [latM, latK]

/-- **The latent-bearing structure** `U → m`, `U → k`, `m → k`. Source: mandate T4(d). Kind: D -/
noncomputable def sLatent : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gLMK, isAcyclic_of_rank _ _ gLMK_rank, cpdOfRate gLMK rLatent⟩

/-- `latentP` factorizes over the latent DAG. Source: mandate T4(d). Kind: N+ -/
theorem sLatent_isFor : sLatent.IsFor latentP := by
  unfold sLatent
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gLMK_parents.1, gLMK_parents.2.1, gLMK_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [latentP, latMass, latM, latK, rLatent]

/-- `P(m = b) = 1/2`. Source: mandate T4(d). Kind: L -/
theorem latentP_m (b : Bool) : latentP.prob {x | x 1 = b} = 1/2 := by
  rw [prob3_eq]; cases b <;> norm_num [latentP, latMass, latM, latK]

/-- `P(k = 1) = 19/50`. Source: mandate T4(d) (`0.38`). Kind: N+ -/
theorem latentP_k : latentP.prob {x | x 2 = true} = 19/50 := by
  rw [prob3_eq]; norm_num [latentP, latMass, latM, latK]

/-- **The faithfulness violation**: `P(k = 1 | m = 1) = P(k = 1 | m = 0) = 19/50`.
Source: [[learning-cdt-renderings]] "Checks" (`P(k | m=1) = P(k | m=0) = 0.38`); mandate T4(d)
Kind: N+ -/
theorem latentP_k_given (b : Bool) : latentP.condProb {x | x 2 = true} {x | x 1 = b} = 19/50 := by
  unfold Distr.condProb
  have : ({x : W3 | x 2 = true} ∩ {x | x 1 = b}) = {x | x 2 = true ∧ x 1 = b} := by ext x; simp
  rw [this, latentP_m, prob3_eq]
  cases b <;> norm_num [latentP, latMass, latM, latK]

/-- **`m ⊥ k` under the latent law**, as FAF's `CondIndepVar` with trivial conditioning: the
observable `(m, k)`-marginal is Markov to the empty graph.
Source: [[learning-cdt-renderings]] "Checks" ("observationally consistent with `m ⊥ k`");
mandate T4(d) ("`Distr.marg P {m, k}` satisfies `CondIndep` of `{m=1}` and `{k=1}`")
Kind: N+
Fidelity: variant: independence stated on the full law as a variable-level `CondIndepVar`
(equivalent to the marginal's `CondIndep`; FAF's `Distr.marg` lands in `PtOn`, not used) -/
theorem latentP_m_indep_k :
    CondIndepVar latentP (fun x : W3 => x 1) (fun x => x 2) (fun _ => ()) := by
  intro a b z
  unfold CondIndep
  have hz : ({x : W3 | (fun _ => ()) x = z}) = Set.univ := by
    ext x; simp
  rw [hz, Set.inter_univ, Set.inter_univ, Set.inter_univ, Distr.prob_univ, mul_one]
  have : ({x : W3 | x 1 = a} ∩ {x | x 2 = b}) = {x | x 1 = a ∧ x 2 = b} := by ext x; simp
  rw [this, prob3_eq, prob3_eq, prob3_eq]
  cases a <;> cases b <;> norm_num [latentP, latMass, latM, latK]

/-- **The interventional `k`-rates**: `P(k = 1 | do m = 1) = 1/2`, `P(k = 1 | do m = 0) = 23/40`.
Source: [[learning-cdt-renderings]] "Checks" (`P(k | do m) = (0.500, 0.575)`); mandate T4(d)
Kind: N+ -/
theorem sLatent_truncate_k (b : Bool) :
    (sLatent.truncate 1 b).prob {x | x 2 = true} = if b then 1/2 else 23/40 := by
  rw [prob3_eq]
  unfold sLatent
  simp only [truncate_cpdOfRate_mass, cpdFactor_cpdOfRate, gLMK_parents.1, gLMK_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases b <;> norm_num [rLatent, latM, latK]

/-- **Corollary 3.1(d), the two effects**: under the latent structure the act has the effect
`P(k | do m = 1) − P(k | do m = 0) = −3/40` although the observable conditionals coincide.
Source: [[learning-cdt-renderings]] Corollary 3.1(d), "Checks" (latent cancellation); mandate T4(d)
Kind: N+ -/
theorem latent_effect :
    (sLatent.truncate 1 true).prob {x | x 2 = true}
      - (sLatent.truncate 1 false).prob {x | x 2 = true} = -3/40 ∧
    latentP.condProb {x | x 2 = true} {x | x 1 = true}
      - latentP.condProb {x | x 2 = true} {x | x 1 = false} = 0 := by
  rw [sLatent_truncate_k, sLatent_truncate_k, latentP_k_given, latentP_k_given]
  exact ⟨by norm_num, by norm_num⟩

/-! ## The empty structure (repair round 1, audit r1 B2)

The "effect-free empty structure" of Corollary 3.1(d) is built: the edgeless DAG on `(U, m, k)`
with the product law `latentQ` of the three marginals of `latentP`. Its `(m, k)`-marginal is
`latentP`'s (`latentP_marg_eq_latentQ`, the faithfulness violation `m ⊥ k` read as "the marginal
factorizes over the empty graph"), it is Markov-compatible (`sEmpty_isFor`), and its zero effect is
**derived** from Pearl's invariance (`k` is a non-descendant of `m` in the empty graph), not
written as `x − x`. -/

/-- The edgeless DAG on `Fin 3`. Source: mandate T4(d) ("the empty graph on `{m, k}`"). Kind: D -/
def gEmpty : Digraph (Fin 3) := dag3 fun _ _ => false

instance : DecidableRel gEmpty.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)

/-- The empty graph is acyclic under any rank (vacuously). Source: none: infrastructure. Kind: L -/
theorem gEmpty_rank : ∀ u v, gEmpty.Adj u v → rankKML u < rankKML v := by decide

/-- No node has parents in the empty graph. Source: none: infrastructure. Kind: L -/
theorem gEmpty_parents : gEmpty.parents 0 = ∅ ∧ gEmpty.parents 1 = ∅ ∧ gEmpty.parents 2 = ∅ := by
  decide

/-- `k ∈ nondesc(m)` in the empty graph. Source: none: infrastructure. Kind: L -/
theorem gEmpty_k_nondesc : (2 : Fin 3) ∈ nondesc gEmpty 1 :=
  mem_nondesc_of_rank gEmpty rankKML gEmpty_rank (by decide) (by decide)

/-- The rate table of the empty structure: the three marginals of `latentP` (`P(U=1) = 1/2`,
`P(m=1) = 1/2`, `P(k=1) = 19/50`).
Source: mandate T4(d) ("`Distr.prod` of the marginals")
Kind: D -/
noncomputable def rEmpty : Rate3 where
  r v _ _ _ := match v with
    | 0 => 1/2
    | 1 => 1/2
    | 2 => 19/50
  nonneg v a b c := by fin_cases v <;> norm_num
  le_one v a b c := by fin_cases v <;> norm_num

/-- **The product law** `P(U) ⊗ P(m) ⊗ P(k)` of `latentP`'s marginals on `(U, m, k)`.
Source: mandate T4(d) ("it is `Distr.prod` of the marginals")
Kind: D -/
noncomputable def latentQ : Distr W3 :=
  distr3 (fun _ _ k => (1/2) * (1/2) * (if k then 19/50 else 31/50))
    (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num) (by norm_num)

/-- **The empty structure**: the edgeless DAG with the marginal CPDs.
Source: [[learning-cdt-renderings]] Corollary 3.1(d) ("the empty structure"); mandate T4(d)
Kind: D -/
noncomputable def sEmpty : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gEmpty, isAcyclic_of_rank _ _ gEmpty_rank, cpdOfRate gEmpty rEmpty⟩

/-- The product law factorizes over the empty graph (Markov compatibility of the empty structure).
Source: mandate T4(d) ("factorizes over the empty graph on `{m,k}` — prove that too")
Kind: N+ -/
theorem sEmpty_isFor : sEmpty.IsFor latentQ := by
  unfold sEmpty
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gEmpty_parents.1, gEmpty_parents.2.1, gEmpty_parents.2.2,
    Finset.notMem_empty]
  cases a <;> cases b <;> cases c <;> norm_num [latentQ, rEmpty]

/-- **The `(m, k)`-marginals of the latent law and the product law coincide**: the faithfulness
violation `m ⊥ k` under `latentP` is exactly "its observable marginal is Markov to the empty graph".
Source: [[learning-cdt-renderings]] "Checks" ("observationally consistent with `m ⊥ k`"); mandate
T4(d) ("`Distr.marg P {m, k}` … factorizes over the empty graph")
Kind: N+
Fidelity: variant: the marginal is compared cellwise on the full space (FAF's `Distr.marg` lands in
`PtOn`, not used) -/
theorem latentP_marg_eq_latentQ (b c : Bool) :
    latentP.prob {x | x 1 = b ∧ x 2 = c} = latentQ.prob {x | x 1 = b ∧ x 2 = c} := by
  rw [prob3_eq, prob3_eq]
  cases b <;> cases c <;> norm_num [latentP, latentQ, latMass, latM, latK]

/-- `P(k = 1) = 19/50` under the product law. Source: none: infrastructure. Kind: L -/
theorem latentQ_k : latentQ.prob {x | x 2 = true} = 19/50 := by
  rw [prob3_eq]; norm_num [latentQ]

/-- **The empty structure is effect-free, by Pearl's invariance**: `k` is a non-descendant of `m`
in the empty graph, so `P^{do m = b}(k) = P(k) = 19/50` for both acts.
Source: [[learning-cdt-renderings]] Corollary 3.1(d) ("the (effect-free) empty structure");
mandate T4(d)
Kind: C
Hyps: (a) `sEmpty_isFor`; (a) `k ∈ nondesc gEmpty m` -/
theorem sEmpty_truncate_k (b : Bool) : (sEmpty.truncate 1 b).prob {x | x 2 = true} = 19/50 := by
  have hset : ({x : W3 | x 2 = true}) = ↑(Finset.univ.filter fun x : W3 => x 2 = true) := by
    ext x; simp
  rw [hset, CausalStructure.truncate,
    truncate_prob_eq_of_inFixedAlgebra sEmpty.acyclic sEmpty.φ sEmpty_isFor 1 b _
      (k_inFixedAlgebra gEmpty gEmpty_k_nondesc), ← hset, latentQ_k]

/-- The empty structure's effect is `0`. Source: mandate T4(d). Kind: C -/
theorem sEmpty_effect :
    (sEmpty.truncate 1 true).prob {x | x 2 = true}
      - (sEmpty.truncate 1 false).prob {x | x 2 = true} = 0 := by
  rw [sEmpty_truncate_k, sEmpty_truncate_k]; norm_num

/-- The two-point prior `(w, 1 − w)` on `Fin 2`. Source: mandate T4(d) ("a prior giving this
structure weight `w` and the empty structure `1−w`"). Kind: D -/
def mixTwo (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : FinDistr ℝ (Fin 2) where
  w := ![w, 1 - w]
  nonneg := by
    intro i; fin_cases i
    · simpa using hw0
    · simp; linarith
  sum_one := by simp [Fin.sum_univ_two]

/-- The two structures of Corollary 3.1(d): the latent one and the empty one.
Source: mandate T4(d)
Kind: D -/
noncomputable def latentPair : Fin 2 → CausalStructure (fun _ : Fin 3 => Bool) := ![sLatent, sEmpty]

/-- The event `{k = 1}` as a finset. Source: none: infrastructure. Kind: D -/
def kEv : Finset W3 := Finset.univ.filter fun x => x 2 = true

/-- The coerced `kEv`. Source: none: infrastructure. Kind: L -/
theorem coe_kEv : (↑kEv : Set W3) = {x | x 2 = true} := by ext x; simp [kEv]

/-- **Corollary 3.1(d), the mixed supposition**: a prior `π = (w, 1−w)` over the latent structure
and the empty structure gives the mixed supposition `∫ cf^G(a) dπ` (Definition 25's `mixState`,
the supposition of each act being `cfG`) the effect `P^π(k | do m = 1) − P^π(k | do m = 0) =
−3w/40`, for every supervenient payoff `u`. Repair round 1: the empty structure is `sEmpty`, its
zero effect derived (`sEmpty_truncate_k`), and the mixture is the package's `mixState` of the two
`cfG` suppositions, not a hand-assembled sum.
Source: [[learning-cdt-renderings]] Corollary 3.1(d) ("a prior giving such structures weight `w`
assigns the act an effect `−0.075 w` that no observational record removes"); mandate T4(d)
Kind: C
Fidelity: variant: the note's empty structure is a DAG on the observable coordinates `{m, k}` whose
law is the `(m, k)`-marginal; here `U` stays a coordinate, `sEmpty` is a structure on `(U, m, k)` for
the product law `latentQ`, whose `(m, k)`-marginal is `latentP`'s cellwise — the two mixed structures
are for different full laws, and "π over structures for `s_d`" is rendered as "two structures whose
`(m, k)`-marginals agree" (audit r2 fid N3); the effect is read on the mixed supposition's law of
`{k = 1}`
Hyps: (a) `0 ≤ w ≤ 1` -/
theorem latent_mixture_effect (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (u : W3 → ℝ) :
    (mixState (mixTwo w hw0 hw1) (fun i => cfG (latentPair i) 1 u true)).pr kEv
      - (mixState (mixTwo w hw0 hw1) (fun i => cfG (latentPair i) 1 u false)).pr kEv
      = -3 * w / 40 := by
  rw [mixState_pr, mixState_pr, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [latentPair, Matrix.cons_val_zero, Matrix.cons_val_one, mixTwo,
    cfG, expState_pr, coe_kEv]
  rw [sLatent_truncate_k, sLatent_truncate_k, sEmpty_truncate_k, sEmpty_truncate_k]
  simp only [Bool.false_eq_true, if_true, if_false]
  ring

end Cleanroom.Decision.DpCausalConsist
