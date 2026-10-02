import FactoredSpaces.BayesNet
import Cleanroom.Corrigibility.CorrScimCid.Scim
import Cleanroom.Corrigibility.CorrScimCid.Expect

/-!
# Ancestor invariance and the path-to-value property (T2)

* **(a) CPD form over FAF** (`marg_tau_tauInv_eq_of_agree`, P): two CPD families that agree on an
  ancestrally closed set `S` of nodes induce the same law on `S` — FAF's `tau hG (tauInv φ)`
  marginalised (`Distr.marg`) to `S`. Proof: the node variables of `S` read only table entries
  indexed by nodes of `S` (`nodeVar_congr_of_agree`, by well-founded induction along the DAG using
  `AncClosed`), so the law on `S` is the pushforward of the marginal of the product `tauInv φ` on
  those entries, and that marginal is a product of the agreed factors (`Factorizes.marg_mass`,
  `Distr.margAt_prod`). This is Holtman's "∀D. U_p = U_q" made precise.
* **(b) per-`ε` form** is `Scm.eval_softAt_of_not_ancSelf` (Scim.lean), restated here as
  `ancestor_invariance_per_eps`; **Thm 18 soundness** (`nested_eq_of_no_path`,
  `not_hasICI_of_no_path`): with no directed path `D ⇢ X ⇢ U` (paths of length ≥ 0, Everitt's
  convention), the nested counterfactual `U_{X_d}(ε)` equals `U(ε)` for every `ε`, `d`, and no
  policy — a fortiori no optimal policy — has an instrumental control incentive on `X`.
* **(c) Holtman's property** (`indifferent_of_downstream_of_notOnPathToValue`, C): a node
  downstream of some decision and on no decision-to-utility path is one every policy's value is
  indifferent to, under every soft intervention (reading (i)); hence every optimal policy stays
  optimal with the same value (reading (ii)). The two readings diverge only off downstream nodes.
* **(d)** the converse fails: a witness lives in `ThreeNode.lean` (a node on a path whose child
  ignores it).

Sources: holtman-2021 Defs 9–11 and the displayed property (l. 915–930); everitt-2021 Def. 17 and
Thm 18 soundness (l. 236–246); everitt-2019 §2.2 (l. 193–205).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-! ### (a) Ancestor invariance, CPD form, over FAF's Bayesian-network construction -/

section CPD

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- The table indices `(v, pa_v)` of FAF's `bnIndex` whose node lies in `S`.
Source: none: infrastructure
Kind: D -/
def idxOf (S : Finset V) : Finset (bnIndex G Val) := Finset.univ.filter fun i => i.1 ∈ S

/-- **The node variables of an ancestrally closed set read only their own table rows**: two table
points agreeing on every index `(v, ·)` with `v ∈ S` give every `v ∈ S` the same node value.
Source: none: infrastructure (the content of Holtman's property)
Kind: P -/
lemma nodeVar_congr_of_agree (hG : G.IsAcyclic) {S : Finset V} (hS : G.AncClosed S)
    {ω ω' : Pt (bnFactor G Val)} (h : ∀ i : bnIndex G Val, i.1 ∈ S → ω i = ω' i) :
    ∀ v ∈ S, nodeVar hG v ω = nodeVar hG v ω' := by
  intro v
  refine hG.wf.induction (C := fun v => v ∈ S → nodeVar hG v ω = nodeVar hG v ω') v ?_
  intro v ih hv
  rw [nodeVar_apply, nodeVar_apply]
  have hpa : (fun u : G.parents v => nodeVar hG u.1 ω) = fun u : G.parents v => nodeVar hG u.1 ω' := by
    funext u
    exact ih u.1 ((Digraph.mem_parents G).mp u.2) (hS v hv u.2)
  rw [hpa]
  exact h ⟨v, _⟩ hv

variable [∀ v, Inhabited (Val v)]

/-- Extend a partial table (rows of `S`) by defaults.
Source: none: infrastructure
Kind: D -/
noncomputable def extendIdx (S : Finset V) (α : PtOn (bnFactor G Val) (idxOf (G := G) (Val := Val) S)) :
    Pt (bnFactor G Val) :=
  fun i => if h : i ∈ idxOf (G := G) (Val := Val) S then α ⟨i, h⟩ else default

/-- The joint value on `S` factors through the rows of `S`.
Source: none: infrastructure
Kind: L -/
lemma proj_jointVar_eq_extend (hG : G.IsAcyclic) {S : Finset V} (hS : G.AncClosed S)
    (ω : Pt (bnFactor G Val)) :
    proj S (jointVar hG ω) = proj S (jointVar hG (extendIdx S (proj (idxOf S) ω))) := by
  funext v
  show nodeVar hG v.1 ω = nodeVar hG v.1 (extendIdx S (proj (idxOf S) ω))
  refine nodeVar_congr_of_agree hG hS ?_ v.1 v.2
  intro i hi
  have hmem : i ∈ idxOf (G := G) (Val := Val) S := by simp [idxOf, hi]
  simp [extendIdx, hmem, proj]

/-- **T2(a): ancestor invariance, CPD form.** If two CPD families agree at every node of an
ancestrally closed set `S` (FAF's `Digraph.AncClosed`), the laws they induce through FAF's
`tau ∘ tauInv` have the same marginal on `S`. Every "the agent lacks an instrumental goal on `X`"
claim of this package reduces to it (with `S` = the ancestors-or-self of the utility nodes, which
excludes `X`).
Source: holtman-2021 §8 Def. 9 and the displayed property (l. 915–926); everitt-2019 §2.2 (l. 193)
Kind: P
Fidelity: exact
Hyps: — -/
theorem marg_tau_tauInv_eq_of_agree (hG : G.IsAcyclic) {S : Finset V} (hS : G.AncClosed S)
    (φ φ' : CPD (G := G) (Val := Val)) (h : ∀ v ∈ S, φ v = φ' v) :
    (tau hG (tauInv φ)).marg S = (tau hG (tauInv φ')).marg S := by
  have hF : ∀ ψ : CPD (G := G) (Val := Val), (tau hG (tauInv ψ)).marg S =
      ((tauInv ψ).marg (idxOf S)).map fun α => proj S (jointVar hG (extendIdx S α)) := by
    intro ψ
    unfold tau Distr.marg
    rw [Distr.map_map, Distr.map_map]
    congr 1
    funext ω
    exact proj_jointVar_eq_extend hG hS ω
  rw [hF, hF]
  congr 1
  ext α
  rw [Factorizes.marg_mass (factorizes_tauInv φ), Factorizes.marg_mass (factorizes_tauInv φ')]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [tauInv, Distr.margAt_prod]
  have hi : i.1.1 ∈ S :=
    (Finset.mem_filter.mp (show i.1 ∈ Finset.univ.filter (fun j : bnIndex G Val => j.1 ∈ S) from i.2)).2
  rw [h _ hi]

end CPD

/-! ### (b) Per-`ε` form, nested counterfactuals and Thm 18 soundness -/

section PerEps

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)]

/-- **T2(b): ancestor invariance, per-`ε` form** (restating `Scm.eval_softAt_of_not_ancSelf`): a
soft intervention at `X` changes the value of `v` at `ε` only if `v = X` or `X ⇢ v`.
Source: holtman-2021 §8 property (l. 926); everitt-2019 §2.2 (l. 193)
Kind: P
Fidelity: exact
Hyps: — -/
theorem ancestor_invariance_per_eps (M : Scm G Val E) (hG : G.IsAcyclic) (ε : Pt E) {X : V}
    (g : ParentVals G Val X → E X → Val X) {v : V} (hv : v ≠ X) (hanc : ¬ G.IsAncestor X v) :
    (M.softAt X g).eval hG ε v = M.eval hG ε v :=
  M.eval_softAt_of_not_ancSelf hG ε g fun h => h.elim (fun e => hv e.symm) hanc

/-- **The nested counterfactual `W_{X_d}(ε)`** (Everitt 2021 after Def. 2): intervene `D := d`,
read `x := X_{D=d}(ε)`, then intervene `X := x` in the original model and read `W`.
Source: everitt-2021 (l. 108–112: "`U_{O_d}(ε) := U_o(ε)` where `o = O_d(ε)`"), Def. 17
Kind: D
Fidelity: exact -/
noncomputable def Scm.nested (M : Scm G Val E) (hG : G.IsAcyclic) (D : V) (d : Val D) (X W : V)
    (ε : Pt E) : Val W :=
  (M.doAt X ((M.doAt D d).eval hG ε X)).eval hG ε W

/-- **Thm 18 soundness, per `ε`.** If there is no directed path `D ⇢ X ⇢ W` (paths of length
`≥ 0`), then `W_{X_d}(ε) = W(ε)` for every `ε` and `d`: either `D ⇢̸ X`, so `X_d(ε) = X(ε)` and
consistency applies, or `X ⇢̸ W`, so intervening at `X` does not reach `W`.
Source: everitt-2021 Thm 18 soundness proof (l. 242–246)
Kind: P
Fidelity: exact
Hyps: — -/
theorem Scm.nested_eq_of_no_path (M : Scm G Val E) (hG : G.IsAcyclic) {D X W : V}
    (h : ¬ (Scm.AncSelf G X D ∧ Scm.AncSelf G W X)) (d : Val D) (ε : Pt E) :
    M.nested hG D d X W ε = M.eval hG ε W := by
  unfold Scm.nested
  by_cases hDX : Scm.AncSelf G X D
  · have hXW : ¬ Scm.AncSelf G W X := fun h' => h ⟨hDX, h'⟩
    exact M.eval_doAt_of_not_ancSelf hG ε _ hXW
  · rw [M.eval_doAt_of_not_ancSelf hG ε d hDX]
    exact M.eval_doAt_of_eq hG ε rfl W

end PerEps

/-! ### Instrumental control incentives and Holtman's property -/

section Incentives

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)] {C : Cid G Val}

/-- `U_{X_d}(ε)` summed over the utility nodes, under the closed model `M^π`.
Source: everitt-2021 Def. 17
Kind: D -/
noncomputable def Scim.nestedUtil (M : Scim C E) (π : Policy C) (D : V) (d : Val D) (X : V)
    (ε : Pt E) : ℝ :=
  ∑ u, if h : C.kind u = .utility then
    C.utilVal u h ((M.withPolicy π).nested C.acyclic D d X u ε) else 0

/-- **Instrumental control incentive** (Everitt 2021 Def. 17) on `X` in decision context `pa_D`:
for every optimal policy, some `d` has `E[U_{X_d} | pa_D] ≠ E[U | pa_D]`. (The paper leaves the
quantifier on `d` implicit; the existential reading is the weakest, so its negation is the
strongest absence claim. Vacuously true when no optimal policy exists — so `¬ HasICI` unfolds to
"*some* optimal policy has `E[U_{X_d} | pa_D] = E[U | pa_D]` for every `d`", which is why the
absence theorems carry `hopt`; the universal-in-`π`, universal-in-`d` fact is
`nestedUtil_eq_of_noPath`.)
Source: everitt-2021 Def. 17 (l. 236)
Kind: D
Fidelity: variant: existential reading of the implicit quantifier on `d` -/
def Scim.HasICI (M : Scim C E) (D X : V) (paD : ParentVals G Val D) : Prop :=
  ∀ π, M.IsOptimal π → ∃ d : Val D,
    condExpect M.μ {ε | parentConfig G Val (M.ev π ε) D = paD} (M.nestedUtil π D d X) ≠
      condExpect M.μ {ε | parentConfig G Val (M.ev π ε) D = paD} fun ε => C.utilSum (M.ev π ε)

/-- **A policy responds to `X`** (Everitt 2021 Def. 10): some intervention `do(X = x)` and some
setting `ε` have `D_x(ε) ≠ D(ε)`. `X` has a *response incentive* when every optimal policy responds
to it; Claim 2.3a of the critique ("there is an optimal policy for which pressing changes nothing")
is the negation of a response incentive on `H` (`Fig1Link.lean`).
Source: everitt-2021 Def. 10 (l. 170)
Kind: D
Fidelity: exact -/
def Scim.RespondsTo (M : Scim C E) (π : Policy C) (D X : V) : Prop :=
  ∃ (x : Val X) (ε : Pt E), ((M.withPolicy π).doAt X x).eval C.acyclic ε D ≠ M.ev π ε D

/-- The graph has no directed path `D ⇢ X ⇢ U` through `X` to any utility node.
Source: everitt-2021 Thm 18
Kind: D -/
def Cid.NoPathThrough (C : Cid G Val) (D X : V) : Prop :=
  ∀ u, C.kind u = .utility → ¬ (Scm.AncSelf G X D ∧ Scm.AncSelf G u X)

/-- **Thm 18 soundness (value form).** With no path `D ⇢ X ⇢ U`, the nested utility equals the
utility at every `ε`, for every policy and every `d`.
Source: everitt-2021 Thm 18 soundness (l. 242–246)
Kind: C
Fidelity: exact
Hyps: — -/
theorem Scim.nestedUtil_eq_of_noPath (M : Scim C E) {D X : V} (h : C.NoPathThrough D X)
    (π : Policy C) (d : Val D) (ε : Pt E) :
    M.nestedUtil π D d X ε = C.utilSum (M.ev π ε) := by
  unfold Scim.nestedUtil Cid.utilSum
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : C.kind u = .utility
  · simp only [hu, dif_pos]
    rw [Scm.nested_eq_of_no_path _ C.acyclic (h u hu)]
    rfl
  · simp [hu]

/-- **No instrumental control incentive without a path** (Thm 18 soundness): if some optimal
policy exists and the graph has no `D ⇢ X ⇢ U`, the CID admits no ICI on `X` at any context.
Source: everitt-2021 Thm 18 soundness (l. 242–246)
Kind: C
Fidelity: exact
Hyps: — -/
theorem Scim.not_hasICI_of_noPath (M : Scim C E) {D X : V} (h : C.NoPathThrough D X)
    (hopt : ∃ π, M.IsOptimal π) (paD : ParentVals G Val D) : ¬ M.HasICI D X paD := by
  intro hici
  obtain ⟨π, hπ⟩ := hopt
  obtain ⟨d, hd⟩ := hici π hπ
  exact hd (condExpect_congr M.μ fun ε _ _ => M.nestedUtil_eq_of_noPath h π d ε)

/-- **Downstream of the policy** (Holtman Def. 10): some decision node is an ancestor of `X`
(nonempty path).
Source: holtman-2021 Def. 10 (l. 921)
Kind: D
Fidelity: exact -/
def Cid.Downstream (C : Cid G Val) (X : V) : Prop := ∃ d, C.kind d = .decision ∧ G.IsAncestor d X

/-- **Not on a path to value** (Holtman Def. 11): no directed path from a decision node via `X` to
a utility node (paths of length `≥ 0` on either side, Everitt's convention).
Source: holtman-2021 Def. 11 (l. 923)
Kind: D
Fidelity: exact -/
def Cid.NotOnPathToValue (C : Cid G Val) (X : V) : Prop :=
  ∀ d u, C.kind d = .decision → C.kind u = .utility → ¬ (Scm.AncSelf G X d ∧ Scm.AncSelf G u X)

/-- **Indifference, reading (i), per policy** (Holtman Def. 9, "∀D. U_p = U_q"): every policy's
value is unchanged by every soft intervention at `X`.
Source: holtman-2021 Def. 9 (l. 917); corr-refs-2-002 reading (i)
Kind: D
Fidelity: exact -/
def Scim.IndifferentTo (M : Scim C E) (X : V) (hX : C.kind X ≠ .decision) : Prop :=
  ∀ (π : Policy C) (g : ParentVals G Val X → E X → Val X), (M.softAt X hX g).value π = M.value π

/-- **Indifference, reading (ii), optimal value**: every optimal policy of `M` is optimal in the
intervened model with the same value.
Source: corr-refs-2-002 reading (ii)
Kind: D
Fidelity: variant: optimal-value reading -/
def Scim.IndifferentToOpt (M : Scim C E) (X : V) (hX : C.kind X ≠ .decision) : Prop :=
  ∀ (π : Policy C) (g : ParentVals G Val X → E X → Val X),
    M.IsOptimal π → (M.softAt X hX g).IsOptimal π ∧ (M.softAt X hX g).value π = M.value π

/-- **Graph lemma**: a downstream node on no path to value is an ancestor-or-self of no utility
node.
Source: holtman-2021 §8 (l. 926)
Kind: L -/
lemma Cid.not_ancSelf_utility_of_downstream (C : Cid G Val) {X : V} (hd : C.Downstream X)
    (hn : C.NotOnPathToValue X) (u : V) (hu : C.kind u = .utility) : ¬ Scm.AncSelf G u X := by
  obtain ⟨d, hdk, hdX⟩ := hd
  exact fun h => hn d u hdk hu ⟨Or.inr hdX, h⟩

/-- The utility sum at `ε` is unchanged by a soft intervention at a node that is an ancestor-or-self
of no utility node.
Source: holtman-2021 §8 property
Kind: L -/
lemma Cid.utilSum_softAt_eq (M : Scim C E) (π : Policy C) {X : V} (hX : C.kind X ≠ .decision)
    (h : ∀ u, C.kind u = .utility → ¬ Scm.AncSelf G u X)
    (g : ParentVals G Val X → E X → Val X) (ε : Pt E) :
    C.utilSum ((M.softAt X hX g).ev π ε) = C.utilSum (M.ev π ε) := by
  unfold Cid.utilSum
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : C.kind u = .utility
  · simp only [hu, dif_pos]
    unfold Scim.ev
    rw [Scim.withPolicy_softAt, Scm.eval_softAt_of_not_ancSelf _ C.acyclic ε g (h u hu)]
  · simp [hu]

/-- **Holtman's property (T2 c), reading (i)**: a node downstream of the policy and not on a path to
value is one the planner is indifferent to — every policy's value is invariant under every soft
intervention at it. Content: the per-`ε` ancestor invariance and the graph lemma.
Source: holtman-2021 §8 displayed property (l. 926)
Kind: C
Fidelity: exact
Hyps: — -/
theorem Scim.indifferent_of_downstream_of_notOnPathToValue (M : Scim C E) {X : V}
    (hX : C.kind X ≠ .decision) (hd : C.Downstream X) (hn : C.NotOnPathToValue X) :
    M.IndifferentTo X hX := by
  intro π g
  unfold Scim.value
  rw [show (M.softAt X hX g).μ = M.μ from rfl]
  simp only [expect]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [C.utilSum_softAt_eq M π hX (C.not_ancSelf_utility_of_downstream hd hn) g ε]

/-- Reading (i) implies reading (ii).
Source: corr-refs-2-002
Kind: L -/
theorem Scim.indifferentToOpt_of_indifferentTo (M : Scim C E) {X : V} (hX : C.kind X ≠ .decision)
    (h : M.IndifferentTo X hX) : M.IndifferentToOpt X hX := by
  intro π g hπ
  refine ⟨fun π' => ?_, h π g⟩
  rw [h π g, h π' g]
  exact hπ π'

/-- **Holtman's property, reading (ii).**
Source: holtman-2021 §8; corr-refs-2-002 reading (ii)
Kind: C
Fidelity: exact
Hyps: — -/
theorem Scim.indifferentToOpt_of_downstream_of_notOnPathToValue (M : Scim C E) {X : V}
    (hX : C.kind X ≠ .decision) (hd : C.Downstream X) (hn : C.NotOnPathToValue X) :
    M.IndifferentToOpt X hX :=
  M.indifferentToOpt_of_indifferentTo hX (M.indifferent_of_downstream_of_notOnPathToValue hX hd hn)

/-- Not being an ancestor-or-self of any utility node gives `NoPathThrough` for every decision.
Source: none: infrastructure
Kind: L -/
lemma Cid.noPathThrough_of_not_ancSelf (C : Cid G Val) {X : V}
    (h : ∀ u, C.kind u = .utility → ¬ Scm.AncSelf G u X) (D : V) : C.NoPathThrough D X :=
  fun u hu hp => h u hu hp.2

end Incentives

/-! ### A rank certificate for acyclicity (for the finite witnesses) -/

section Rank

variable {V : Type} {G : Digraph V}

/-- A graph whose edges strictly increase a rank is acyclic.
Source: none: infrastructure
Kind: L -/
lemma Digraph.isAcyclic_of_rank (r : V → ℕ) (h : ∀ u v, G.Adj u v → r u < r v) : G.IsAcyclic := by
  intro v hv
  have : ∀ a b, Relation.TransGen G.Adj a b → r a < r b := by
    intro a b hab
    induction hab with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact ih.trans (h _ _ h')
  exact lt_irrefl _ (this v v hv)

end Rank

end Cleanroom.Corrigibility.CorrScimCid
