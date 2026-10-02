import FactoredSpaces.BayesNet
import Cleanroom.Found.CorrThreeStep.Setting

/-!
# The SCIM layer: CIDs, structural causal influence models, policies, evaluation (T1)

Package `corr-scim-cid` (area `corrigibility`). FAF has the graph layer (`Digraph`, `parents`,
`ParentVals`, `parentConfig`, `IsAcyclic`, `depth`) and the probability layer (`Distr`,
`Distr.prod`), but no carrier for decision nodes, interventions or counterfactuals. This file adds
them, *structurally* (exogenous noise + functions, Pearl/Everitt 2021 Def. 1, Carey–Everitt 2023
Def. 1 "with independent errors"), so that per-`ε` statements (vigilance preservation, nested
counterfactuals) are expressible.

Design decisions of record (see the report §T1):
* **Graph and parents are FAF's.** `G : Digraph V`, `G.parents v`, `ParentVals G Val v`,
  `parentConfig`. Nothing is hand-rolled.
* **Value types `Val v` are arbitrary types, not required finite**; the exogenous types `E v`
  are finite and carry all the probability. Every law is stated on the finite exogenous space
  `Pt E` through FAF's `Distr.prod`, exactly as the papers define `P(W = w) := ∑_{ε : W(ε) = w} P(ε)`.
  Reason: Lemma 22/23 of Carey–Everitt intervene on the utility node with values (`−α`) outside its
  original finite domain; with real-valued utility nodes those interventions stay inside one model.
  The FAF bridge to `FactorizesOverDAG` (module `Bridge`) adds `[∀ v, Fintype (Val v)]`.
* **A closed model `Scm` is the primitive**: every node has a mechanism `f v : ParentVals → E v → Val v`.
  A SCIM (`Scim`) is an `Scm` minus the mechanisms at decision nodes; a deterministic policy
  (Carey–Everitt §3 "which we assume to be deterministic") closes it (`Scim.withPolicy`).
  Interventions (`doAt`, `softAt`) act on `Scm` by `Function.update` of the mechanism family.
* **Evaluation** is well-founded recursion along the DAG (`IsAcyclic.wf`), as FAF's `nodeVar`;
  the unfolding is `Scm.eval_apply`. Evaluation is *not* routed through FAF's table encoding
  `Pt (bnFactor G Val)`, which is one particular exogenous encoding (mandate T1).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Finset

set_option linter.unusedSectionVars false

/-- The three node kinds of a causal influence diagram (Everitt 2021 Def. 3; Carey–Everitt Def. 1
"structure, decision, utility").
Source: everitt-2021 Def. 3 (l. 130); carey-everitt-2023 Def. 1 (l. 87)
Kind: D
Fidelity: exact -/
inductive NodeKind
  | struct
  | decision
  | utility
  deriving DecidableEq, Repr

section Cid

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type}

/-- **Causal influence diagram** over FAF's `Digraph`: an acyclic graph, a kind per node, a real
reading of every utility node's values (Everitt: "utility variable domains are a subset of ℝ" —
here a map `Val v → ℝ`, so `Val v` may itself be `ℝ`), and the CID axiom that utility nodes have
no children (Everitt 2021 Def. 3; Lemma 21 of Carey–Everitt needs it).
Parents are FAF's `G.parents v`; the information links of a decision `d` are the edges into `d`.
Source: everitt-2021 Def. 3 (l. 130–140); carey-everitt-2023 Def. 1 (l. 87–91)
Kind: D
Fidelity: exact (the real reading `utilVal` replaces "`X_U ⊆ ℝ`") -/
structure Cid (G : Digraph V) (Val : V → Type) where
  /-- The CID is acyclic. -/
  acyclic : G.IsAcyclic
  /-- The kind of every node. -/
  kind : V → NodeKind
  /-- The real reading of a utility node's value. -/
  utilVal : ∀ v, kind v = .utility → Val v → ℝ
  /-- Utility nodes have no children. -/
  utility_sink : ∀ v, kind v = .utility → ∀ w, ¬ G.Adj v w

variable (C : Cid G Val)

/-- The decision nodes of a CID, as a subtype (so that policies are a `Fintype` when the value
types are).
Source: none: infrastructure
Kind: D -/
abbrev Cid.Decisions : Type := {d : V // C.kind d = .decision}

/-- A **deterministic policy**: one decision rule per decision node, a function of that node's
parent configuration (Carey–Everitt §3: "`π_i : X_{Pa_{D_i}} → X_{D_i}`, which we assume to be
deterministic"; Everitt 2021 likewise). Holtman's stochastic decision kernels are covered by soft
interventions on structure nodes, not by this type.
Source: carey-everitt-2023 §3 (l. 91); everitt-2021 Def. 4
Kind: D
Fidelity: exact -/
abbrev Policy : Type := ∀ d : C.Decisions, ParentVals G Val d.1 → Val d.1

/-- The sum of the utility nodes' readings at a joint value (`∑_{U ∈ 𝒰} U`, the objective of
Carey–Everitt §3 and Everitt 2021).
Source: carey-everitt-2023 §3 (l. 91); everitt-2021 Def. 4
Kind: D -/
noncomputable def Cid.utilSum (x : Pt Val) : ℝ :=
  ∑ v, if h : C.kind v = .utility then C.utilVal v h (x v) else 0

/-- A utility node is nobody's ancestor (it has no children, so no path leaves it).
Source: none: infrastructure
Kind: L -/
lemma Cid.not_isAncestor_of_utility {v : V} (hv : C.kind v = .utility) (w : V) :
    ¬ G.IsAncestor v w := by
  intro h
  induction h with
  | single h => exact C.utility_sink v hv _ h
  | tail _ _ ih => exact ih

end Cid

section Scm

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Structural causal model (closed).** Independent exogenous noise `P v : Distr (E v)` (FAF's
`Distr`; independence is the product `Distr.prod P`) and one mechanism per node reading its FAF
parent configuration and its own noise (Pearl; Everitt 2021 Def. 1).
Source: everitt-2021 Def. 1 (l. 84–90)
Kind: D
Fidelity: exact -/
@[ext]
structure Scm (G : Digraph V) [DecidableRel G.Adj] (Val E : V → Type) [∀ v, Fintype (E v)] where
  /-- The exogenous noise, one FAF distribution per node. -/
  P : ∀ v, Distr (E v)
  /-- The structural functions. -/
  f : ∀ v, ParentVals G Val v → E v → Val v

variable {G : Digraph V} [DecidableRel G.Adj] {Val E : V → Type} [∀ v, Fintype (E v)]

namespace Scm

variable (M : Scm G Val E)

/-- The joint law of the exogenous noise, FAF's product `⨂_v P v` on the finite space `Pt E`.
Source: everitt-2021 Def. 1 ("mutually independent")
Kind: D -/
noncomputable def μ : Distr (Pt E) := Distr.prod M.P

/-- **Evaluation at one node**, by well-founded recursion along the DAG: `X_v(ε) = f_v(X_{pa(v)}(ε), ε_v)`
(Everitt 2021 "recursive application of the structural functions"). Same construction as FAF's
`nodeVar`, over the exogenous space instead of the table space.
Source: everitt-2021 Def. 1 ("`W(ε)`"); carey-everitt-2023 §3 ("the assignment `W(ε)`")
Kind: D -/
noncomputable def evalAt (hG : G.IsAcyclic) : ∀ v : V, Pt E → Val v :=
  hG.wf.fix (C := fun v => Pt E → Val v) fun v ih ε =>
    M.f v (fun u : G.parents v => ih u.1 ((Digraph.mem_parents G).mp u.2) ε) (ε v)

/-- **Evaluation**: the joint value `V(ε) : Pt Val` of the model at the exogenous setting `ε`.
Source: everitt-2021 Def. 1; carey-everitt-2023 §3
Kind: D -/
noncomputable def eval (hG : G.IsAcyclic) (ε : Pt E) : Pt Val := fun v => M.evalAt hG v ε

/-- The unfolding of evaluation: `X_v(ε) = f_v(X_{pa(v)}(ε), ε_v)`.
Source: everitt-2021 Def. 1
Kind: L -/
lemma eval_apply (hG : G.IsAcyclic) (ε : Pt E) (v : V) :
    M.eval hG ε v = M.f v (parentConfig G Val (M.eval hG ε) v) (ε v) := by
  show hG.wf.fix (C := fun v => Pt E → Val v)
      (fun v ih ε => M.f v (fun u : G.parents v => ih u.1 ((Digraph.mem_parents G).mp u.2) ε) (ε v))
      v ε = _
  rw [WellFounded.fix_eq]
  rfl

/-- **Hard intervention** `do(X = x)`: the mechanism at `X` becomes the constant `x`
(Everitt 2021 Def. 2, the submodel `M_x`).
Source: everitt-2021 Def. 2 (l. 100–104); carey-everitt-2023 §3 ("`M_{V=v}`")
Kind: D
Fidelity: exact -/
noncomputable def doAt (X : V) (x : Val X) : Scm G Val E :=
  { M with f := Function.update M.f X (fun _ _ => x) }

/-- **Soft intervention** at `X`: the mechanism at `X` is replaced by `g : Pa_X × E_X → Val X`,
respecting the graph (Everitt 2021 after Def. 2; Carey–Everitt's `M_{g^V}`).
Source: everitt-2021 (l. 104–106); carey-everitt-2023 §3 ("`P(W | do(V = g^V(V')))`")
Kind: D
Fidelity: exact -/
noncomputable def softAt (X : V) (g : ParentVals G Val X → E X → Val X) : Scm G Val E :=
  { M with f := Function.update M.f X g }

@[simp] lemma doAt_P (X : V) (x : Val X) : (M.doAt X x).P = M.P := rfl
@[simp] lemma softAt_P (X : V) (g : ParentVals G Val X → E X → Val X) : (M.softAt X g).P = M.P := rfl
@[simp] lemma doAt_μ (X : V) (x : Val X) : (M.doAt X x).μ = M.μ := rfl
@[simp] lemma softAt_μ (X : V) (g : ParentVals G Val X → E X → Val X) : (M.softAt X g).μ = M.μ := rfl

lemma doAt_f_self (X : V) (x : Val X) (pa : ParentVals G Val X) (e : E X) :
    (M.doAt X x).f X pa e = x := by
  simp [doAt, Function.update_self]

lemma doAt_f_of_ne {X w : V} (h : w ≠ X) (x : Val X) : (M.doAt X x).f w = M.f w := by
  simp [doAt, Function.update_of_ne h]

lemma softAt_f_self (X : V) (g : ParentVals G Val X → E X → Val X) : (M.softAt X g).f X = g := by
  simp [softAt, Function.update_self]

lemma softAt_f_of_ne {X w : V} (h : w ≠ X) (g : ParentVals G Val X → E X → Val X) :
    (M.softAt X g).f w = M.f w := by
  simp [softAt, Function.update_of_ne h]

/-- Intervening on `X` by its own mechanism changes nothing.
Source: none: infrastructure
Kind: L -/
lemma softAt_self (X : V) : M.softAt X (M.f X) = M := by
  simp [softAt, Function.update_eq_self]

/-- Two soft interventions at the same node: the second wins.
Source: none: infrastructure
Kind: L -/
lemma softAt_softAt (X : V) (g g' : ParentVals G Val X → E X → Val X) :
    (M.softAt X g).softAt X g' = M.softAt X g' := by
  simp [softAt, Function.update_idem]

/-- A hard intervention after a soft one at the same node is the hard one (`do(H = 0)` overrides
`g^H`, the step of Carey–Everitt's proof of Thm 14 ⇒).
Source: carey-everitt-2023 Thm 14 proof ("do(H = 0) overrides g^H")
Kind: L -/
lemma doAt_softAt (X : V) (g : ParentVals G Val X → E X → Val X) (x : Val X) :
    (M.softAt X g).doAt X x = M.doAt X x := by
  simp [softAt, doAt, Function.update_idem]

/-- Interventions at distinct nodes commute.
Source: none: infrastructure
Kind: L -/
lemma softAt_comm {X Y : V} (h : X ≠ Y) (g : ParentVals G Val X → E X → Val X)
    (g' : ParentVals G Val Y → E Y → Val Y) :
    (M.softAt X g).softAt Y g' = (M.softAt Y g').softAt X g := by
  simp [softAt, Function.update_comm h]

/-! ### The master congruence lemma and its three corollaries (T1's infrastructure lemmas) -/

/-- The set of ancestors-or-self of `v`, as a predicate.
Source: none: infrastructure
Kind: D -/
def AncSelf (G : Digraph V) (v w : V) : Prop := w = v ∨ G.IsAncestor w v

lemma ancSelf_of_adj_of_ancSelf {u w v : V} (hu : G.Adj u w) (hw : AncSelf G v w) :
    AncSelf G v u := by
  rcases hw with rfl | hw
  · exact Or.inr (Relation.TransGen.single hu)
  · exact Or.inr (Relation.TransGen.head hu hw)

lemma ancSelf_of_ancSelf_of_adj {X u v : V} (h : AncSelf G u X) (hu : G.Adj u v) :
    AncSelf G v X := by
  rcases h with rfl | h
  · exact Or.inr (Relation.TransGen.single hu)
  · exact Or.inr (Relation.TransGen.tail h hu)

/-- **Master congruence.** If the mechanisms of `M'` agree with those of `M` at every
ancestor-or-self of `v`, *evaluated at the inputs `M` realises at `ε`*, then `M` and `M'` give `v`
the same value at `ε`. Consistency (`eval_doAt_of_eq`) and invariance under interventions off the
ancestors (`eval_softAt_of_not_ancSelf`) are the two instances.
Source: none: infrastructure (Everitt 2021 Lemma 20's mechanism)
Kind: P -/
lemma eval_congr {M M' : Scm G Val E} (hG : G.IsAcyclic) (ε : Pt E) (v : V)
    (h : ∀ w, AncSelf G v w →
      M'.f w (parentConfig G Val (M.eval hG ε) w) (ε w) =
        M.f w (parentConfig G Val (M.eval hG ε) w) (ε w)) :
    M'.eval hG ε v = M.eval hG ε v := by
  revert h
  refine hG.wf.induction (C := fun v => (∀ w, AncSelf G v w →
      M'.f w (parentConfig G Val (M.eval hG ε) w) (ε w) =
        M.f w (parentConfig G Val (M.eval hG ε) w) (ε w)) →
      M'.eval hG ε v = M.eval hG ε v) v ?_
  intro v ih h
  rw [eval_apply, eval_apply]
  have hpc : parentConfig G Val (M'.eval hG ε) v = parentConfig G Val (M.eval hG ε) v := by
    funext u
    exact ih u.1 ((Digraph.mem_parents G).mp u.2)
      (fun w hw => h w (ancSelf_of_ancSelf_of_adj hw ((Digraph.mem_parents G).mp u.2)))
  rw [hpc]
  exact h v (Or.inl rfl)

/-- **Consistency (T1 i).** Intervening a node to the value it already takes at `ε` changes
nothing at `ε` (Pearl's consistency; Carey–Everitt's Prop. 6 and Lemma 22 use it as "from
consistency").
Source: carey-everitt-2023 Lemma 22 proof ("it follows from consistency")
Kind: P -/
lemma eval_doAt_of_eq (hG : G.IsAcyclic) (ε : Pt E) {X : V} {x : Val X}
    (hx : M.eval hG ε X = x) (W : V) : (M.doAt X x).eval hG ε W = M.eval hG ε W := by
  refine eval_congr hG ε W fun w _ => ?_
  by_cases hw : w = X
  · subst hw
    rw [doAt_f_self, ← hx, eval_apply]
  · rw [doAt_f_of_ne M hw]

/-- **Ancestor invariance, per-`ε` form (T2 b).** A soft intervention at `X` changes the value of
`v` only if `v = X` or `X` is an ancestor of `v`.
Source: holtman-2021 §8 property (l. 926); everitt-2019 §2.2 (l. 193)
Kind: P -/
lemma eval_softAt_of_not_ancSelf (hG : G.IsAcyclic) (ε : Pt E) {X : V}
    (g : ParentVals G Val X → E X → Val X) {v : V} (hv : ¬ AncSelf G v X) :
    (M.softAt X g).eval hG ε v = M.eval hG ε v := by
  refine eval_congr hG ε v fun w hw => ?_
  have hwX : w ≠ X := fun e => hv (e ▸ hw)
  rw [softAt_f_of_ne M hwX]

/-- The same for a hard intervention.
Source: everitt-2021 Lemma 20 (soundness of Thm 18: "`X_d(ε) = X(ε)`" when `D ⇢̸ X`)
Kind: P -/
lemma eval_doAt_of_not_ancSelf (hG : G.IsAcyclic) (ε : Pt E) {X : V} (x : Val X) {v : V}
    (hv : ¬ AncSelf G v X) : (M.doAt X x).eval hG ε v = M.eval hG ε v :=
  eval_softAt_of_not_ancSelf M hG ε (fun _ _ => x) hv

/-- The parents of `X` are not ancestors-or-self of `X`'s descendants through `X` — in particular
a soft intervention at `X` leaves `X`'s own parent configuration unchanged.
Source: none: infrastructure
Kind: L -/
lemma parentConfig_softAt (hG : G.IsAcyclic) (ε : Pt E) (X : V)
    (g : ParentVals G Val X → E X → Val X) :
    parentConfig G Val ((M.softAt X g).eval hG ε) X = parentConfig G Val (M.eval hG ε) X := by
  funext u
  have hadj : G.Adj u.1 X := (Digraph.mem_parents G).mp u.2
  refine eval_softAt_of_not_ancSelf M hG ε g ?_
  rintro (h | h)
  · rw [← h] at hadj
    exact hG X (Relation.TransGen.single hadj)
  · exact hG X (Relation.TransGen.tail h hadj)

/-- The value at the intervened node itself: `g` applied to the (unchanged) parent configuration.
Source: none: infrastructure
Kind: L -/
lemma eval_softAt_self (hG : G.IsAcyclic) (ε : Pt E) (X : V)
    (g : ParentVals G Val X → E X → Val X) :
    (M.softAt X g).eval hG ε X = g (parentConfig G Val (M.eval hG ε) X) (ε X) := by
  rw [eval_apply, softAt_f_self, parentConfig_softAt]

/-- The value at a hard-intervened node is the constant.
Source: none: infrastructure
Kind: L -/
lemma eval_doAt_self (hG : G.IsAcyclic) (ε : Pt E) (X : V) (x : Val X) :
    (M.doAt X x).eval hG ε X = x := by
  rw [eval_apply, doAt_f_self]

/-- A node whose value at `ε` is unchanged by an intervention has its whole parent configuration
unchanged too, as soon as the intervention target is not an ancestor-or-self of any of its parents.
Source: none: infrastructure
Kind: L -/
lemma parentConfig_softAt_of_not_ancSelf (hG : G.IsAcyclic) (ε : Pt E) {X : V}
    (g : ParentVals G Val X → E X → Val X) {v : V} (hv : ¬ AncSelf G v X) :
    parentConfig G Val ((M.softAt X g).eval hG ε) v = parentConfig G Val (M.eval hG ε) v := by
  funext u
  refine eval_softAt_of_not_ancSelf M hG ε g fun h =>
    hv (ancSelf_of_ancSelf_of_adj h ((Digraph.mem_parents G).mp u.2))

/-- The expectation of a function of the joint value, `E[X(V(ε))]`, over FAF's product noise.
Source: everitt-2021 Def. 1 ("`Pr(W = w) = ∑_{ε : W(ε) = w} P(ε)`")
Kind: D -/
noncomputable def expectOf (hG : G.IsAcyclic) (X : Pt Val → ℝ) : ℝ :=
  Cleanroom.Found.CorrThreeStep.expect M.μ fun ε => X (M.eval hG ε)

end Scm

end Scm

section Scim

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)]

/-- **Structural causal influence model** (Carey–Everitt Def. 1, Everitt 2021 Def. 4): a CID,
independent finite exogenous noise, and a mechanism at every non-decision node. Decision nodes
carry no function.
Source: carey-everitt-2023 Def. 1 (l. 87–91); everitt-2021 Def. 4 (l. 146–156)
Kind: D
Fidelity: exact -/
structure Scim (C : Cid G Val) (E : V → Type) [∀ v, Fintype (E v)] where
  /-- The exogenous noise. -/
  P : ∀ v, Distr (E v)
  /-- The mechanisms of the non-decision nodes. -/
  f : ∀ v, C.kind v ≠ .decision → ParentVals G Val v → E v → Val v

namespace Scim

variable {C : Cid G Val} (M : Scim C E)

/-- **Closing a SCIM with a policy** (`M^π`): the decision nodes get the policy's rules.
Source: carey-everitt-2023 §3 ("the policy and SCIM jointly form a SCM `M^π`")
Kind: D
Fidelity: exact -/
noncomputable def withPolicy (π : Policy C) : Scm G Val E where
  P := M.P
  f v := if h : C.kind v = .decision then fun pa _ => π ⟨v, h⟩ pa else M.f v h

lemma withPolicy_f_decision (π : Policy C) {d : V} (hd : C.kind d = .decision)
    (pa : ParentVals G Val d) (e : E d) : (M.withPolicy π).f d pa e = π ⟨d, hd⟩ pa := by
  simp [withPolicy, hd]

lemma withPolicy_f_of_ne (π : Policy C) {v : V} (hv : C.kind v ≠ .decision)
    (pa : ParentVals G Val v) (e : E v) : (M.withPolicy π).f v pa e = M.f v hv pa e := by
  simp [withPolicy, hv]

@[simp] lemma withPolicy_P (π : Policy C) : (M.withPolicy π).P = M.P := rfl

/-- The joint law of the noise, independent of the policy.
Source: none: infrastructure
Kind: D -/
noncomputable def μ : Distr (Pt E) := Distr.prod M.P

@[simp] lemma withPolicy_μ (π : Policy C) : (M.withPolicy π).μ = M.μ := rfl

/-- Evaluation of the closed model at the policy `π`, using the CID's acyclicity.
Source: carey-everitt-2023 §3
Kind: D -/
noncomputable def ev (π : Policy C) (ε : Pt E) : Pt Val := (M.withPolicy π).eval C.acyclic ε

/-- The value of a decision node under the closed model is the policy's rule at the realised
parent configuration.
Source: none: infrastructure
Kind: L -/
lemma ev_decision (π : Policy C) (ε : Pt E) {d : V} (hd : C.kind d = .decision) :
    M.ev π ε d = π ⟨d, hd⟩ (parentConfig G Val (M.ev π ε) d) := by
  show (M.withPolicy π).eval C.acyclic ε d = _
  rw [Scm.eval_apply, withPolicy_f_decision M π hd]
  rfl

lemma ev_of_ne (π : Policy C) (ε : Pt E) {v : V} (hv : C.kind v ≠ .decision) :
    M.ev π ε v = M.f v hv (parentConfig G Val (M.ev π ε) v) (ε v) := by
  show (M.withPolicy π).eval C.acyclic ε v = _
  rw [Scm.eval_apply, withPolicy_f_of_ne M π hv]
  rfl

/-- **Soft intervention on a structure node of a SCIM** (Everitt 2021 Def. 15's `M_{g^X}`), the
open-model form; it commutes with closing by a policy (`withPolicy_softAt`).
Source: everitt-2021 Def. 15 (l. 218)
Kind: D -/
noncomputable def softAt (X : V) (_hX : C.kind X ≠ .decision)
    (g : ParentVals G Val X → E X → Val X) : Scim C E where
  P := M.P
  f := Function.update M.f X (fun _ => g)

/-- Closing a soft-intervened SCIM is soft-intervening the closed model (Everitt's "the resulting
SCMs are identical", Thm 16 proof).
Source: everitt-2021 Thm 16 proof ("by SCM equivalence")
Kind: L -/
lemma withPolicy_softAt (X : V) (hX : C.kind X ≠ .decision)
    (g : ParentVals G Val X → E X → Val X) (π : Policy C) :
    (M.softAt X hX g).withPolicy π = (M.withPolicy π).softAt X g := by
  refine Scm.ext rfl ?_
  funext v
  by_cases hv : v = X
  · subst hv
    simp [withPolicy, softAt, Scm.softAt, Function.update_self, hX]
  · simp [withPolicy, softAt, Scm.softAt, Function.update_of_ne hv]

/-- **The value of a policy**: the expected sum of the utility nodes, `E^π[∑ U]`.
Source: carey-everitt-2023 §3 ("optimal if it maximises expected utility"); everitt-2021 Def. 4
Kind: D -/
noncomputable def value (π : Policy C) : ℝ :=
  Cleanroom.Found.CorrThreeStep.expect M.μ fun ε => C.utilSum (M.ev π ε)

/-- **Optimality** as a predicate, never a chosen argmax (Holtman Def. 7's "argmax always
deterministically returns the same function" is a choice function — corr-refs-2-001).
Source: carey-everitt-2023 §3; everitt-2021 Def. 4; holtman-2021 Def. 7 (l. 335)
Kind: D
Fidelity: exact ("`π ∈ argmax`") -/
def IsOptimal (π : Policy C) : Prop := ∀ π' : Policy C, M.value π' ≤ M.value π

/-- **The policy space is finite as soon as the decision nodes and their parents have finite value
types** — nothing is asked of the other nodes, so a real-valued utility node (design decision 2)
is fine. (Audit r1 B1(iii): the earlier hypothesis `[∀ v, Fintype (Val v)]` excluded every model
of record.)
Source: none: infrastructure
Kind: D -/
@[reducible] noncomputable def policyFintype (hd : ∀ d : C.Decisions, Fintype (Val d.1))
    (hp : ∀ d : C.Decisions, ∀ p : G.parents d.1, Fintype (Val p.1)) : Fintype (Policy C) := by
  classical
  haveI : ∀ d : C.Decisions, Fintype (Val d.1) := hd
  haveI : ∀ d : C.Decisions, Fintype (ParentVals G Val d.1) := fun d => by
    haveI : ∀ p : G.parents d.1, Fintype (Val p.1) := hp d
    exact Pi.instFintype
  exact Pi.instFintype

/-- An optimal policy exists when the policy space is a nonempty `Fintype` (`policyFintype`:
finiteness at the decision nodes and their parents suffices). Without finiteness the supremum need
not be attained, so `IsOptimal` may be empty.
Source: none: infrastructure
Kind: P -/
lemma exists_isOptimal [Fintype (Policy C)] [Nonempty (Policy C)] :
    ∃ π : Policy C, M.IsOptimal π := by
  classical
  obtain ⟨π, -, hπ⟩ := Finset.exists_max_image (Finset.univ : Finset (Policy C)) M.value
    Finset.univ_nonempty
  exact ⟨π, fun π' => hπ π' (Finset.mem_univ _)⟩

/-- The earlier, over-hypothesised form: every value type finite and inhabited.
Source: none: infrastructure
Kind: P -/
lemma exists_isOptimal_of_fintypeVal [∀ v, Fintype (Val v)] [∀ v, Inhabited (Val v)] :
    ∃ π : Policy C, M.IsOptimal π :=
  haveI : Fintype (Policy C) := policyFintype (fun d => inferInstance) (fun _ p => inferInstance)
  haveI : Nonempty (Policy C) := ⟨fun d _ => default⟩
  M.exists_isOptimal

end Scim

end Scim

end Cleanroom.Corrigibility.CorrScimCid
