import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Mathlib.Tactic.DeriveFintype

/-!
# Claims 3 and 9, Holtman's ITC: one theorem over the TI-ignoring diagram class (T3)

The **TI-ignoring class** (Everitt 2019 Fig. 7 / Fig. 12 shape) is the set of acyclic digraphs on
the eight nodes `S₁ A₁ Θ₁ Θ₂ S₂ S₃ R₁ R₂` defined by the *absence* of edges out of the future
objective `Θ₂`: none into a state (Assumption 1, private), none into a reward (Assumption 3,
state-based: rewards read `Θ₁`), none into the decision `A₁` (no information link), and none into
the earlier objective `Θ₁` (time order). `A₁ → Θ₂` is allowed: the agent may influence the
implemented objective. Under these, `Θ₂` has no children, so it is an ancestor-or-self of no
reward (`tiIgnoring_not_ancSelf_reward`), and T2 gives, for every SCIM compatible with the class:

* **value invariance** under every soft intervention at `Θ₂`, for every policy
  (`tiIgnoring_indifferent`, Holtman's Def. 9 indifference "to all of `I₁, I₂, …`");
* **no instrumental control incentive** on `Θ₂` at any context (`tiIgnoring_not_hasICI`, Thm 18
  soundness).

The same theorem is Claim 3 (`Θ = Θ^R`, the implemented reward parameters), Claim 9 (`Θ = Θ^PM`,
the predictive model, with belief nodes as structure nodes) and Holtman's ITC (after rerouting every
reward reads `I₀`, so `I_{t ≥ 1}` is off every path to value) — three ledger rows, one proof.
**Not oversold:** the content is "the graph admits no incentive", a fact about paths whose
substance is T2; the "may tamper" halves of Claims 1/8 are witness claims and are not theorems
here. The rocks-and-diamonds witness of T3(c) (`RocksDiamonds.lean`) exhibits the contrast on the
same node type: the standard agent, whose `R₂` reads `Θ₂`, tampers at every optimal policy, and the
TI-ignoring agent, whose `R₂` reads `Θ₁`, does not.

**The class collapses to sink-ness** (audit r1, probe `TISink`): on this eight-node type the four
absences are jointly equivalent to "`Θ₂` has no children" (plus acyclicity) — the edgeless graph
is a member — so every SCIM compatible with the class has *nothing* reading `Θ₂`, and
`tiIgnoring_indifferent` is the sink instance of `Scim.indifferent_of_not_ancSelf_utility`. This is
the two-step truncation of Everitt's three-step Fig. 7 (`Θ₂ → Θ₃` present there); a three-step
class ("no `Θ_{t ≥ 2} ⇢ R`") would make the graph lemma more than one case split and let a
witness carry an edge out of `Θ₂`. The theorem still ranges over every compatible SCIM and every
policy, which is what Claims 3/9 assert; its "may tamper" contrast is `RocksDiamonds`.

Sources: everitt-2019 Assumptions 1–3 (l. 305), Claim 3 (l. 347), Claims 8–9 (l. 559);
holtman-2021 §7.2–7.4 (l. 835–913), Def. 9 (l. 917); corr-refs-2-020, 2-022, 2-023;
corr-wf13-2-040 I1.3.
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-! ### General: a node that is nobody's utility ancestor is one every policy is indifferent to -/

section General

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)] {C : Cid G Val}

/-- **Value invariance without a path to any utility node**: if `X` is an ancestor-or-self of no
utility node, every policy's value is unchanged by every soft intervention at `X`. (Holtman's
property without the `Downstream` hypothesis, which only matters for reading (ii)'s divergence.)
Source: holtman-2021 Def. 9 (l. 917); everitt-2019 §2.2 (l. 193)
Kind: C
Fidelity: exact
Hyps: — -/
theorem Scim.indifferent_of_not_ancSelf_utility (M : Scim C E) {X : V}
    (hX : C.kind X ≠ .decision) (h : ∀ u, C.kind u = .utility → ¬ Scm.AncSelf G u X) :
    M.IndifferentTo X hX := by
  intro π g
  unfold Scim.value
  rw [show (M.softAt X hX g).μ = M.μ from rfl]
  simp only [expect]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [C.utilSum_softAt_eq M π hX h g ε]

end General

/-! ### The TI-ignoring class -/

namespace TI

/-- The eight nodes of the two-step reward/objective diagram (Everitt 2019 Fig. 7 / Fig. 12 shape).
Source: everitt-2019 Fig. 7 (l. 305–347)
Kind: D -/
inductive Node
  | S₁ | A₁ | Θ₁ | Θ₂ | S₂ | S₃ | R₁ | R₂
  deriving DecidableEq, Fintype, Repr

open Node

/-- The node kinds of the class: one decision `A₁`, two rewards `R₁ R₂`.
Source: everitt-2019 Fig. 7
Kind: D -/
def kind : Node → NodeKind
  | A₁ => .decision
  | R₁ => .utility
  | R₂ => .utility
  | _ => .struct

/-- **The TI-ignoring class**, by absence of edges out of `Θ₂` (Everitt 2019 Assumptions 1, 3, the
missing information link `Θ₂ → A₁`, and time order `Θ₂ ↛ Θ₁`); `A₁ → Θ₂` is allowed.
Source: everitt-2019 Assumptions 1–3 (l. 305–311), Fig. 7 (l. 347), Fig. 12 (l. 559)
Kind: D
Fidelity: exact (the absences are the paper's; time order added) -/
structure IsTIIgnoring (G : Digraph Node) : Prop where
  /-- Assumption 1 (private): no `Θ₂ → S_t`. -/
  no_state : ∀ t, t = S₁ ∨ t = S₂ ∨ t = S₃ → ¬ G.Adj Θ₂ t
  /-- Current-RF objective (Fig. 7): every reward reads `Θ₁`, so no `Θ₂ → R_t`. (Assumption 3 alone
  forbids only `Θ_k → R_t` for `k ≠ t`; `Θ₂ → R₂` is excluded here because Claim 3's agent is
  current-RF.) -/
  no_reward : ∀ t, t = R₁ ∨ t = R₂ → ¬ G.Adj Θ₂ t
  /-- No information link `Θ₂ → A₁` (the TI-ignoring agent does not observe the future objective). -/
  no_info : ¬ G.Adj Θ₂ A₁
  /-- Time order: the future objective does not feed the earlier one. -/
  no_back : ¬ G.Adj Θ₂ Θ₁
  /-- Acyclicity (a CID). -/
  acyclic : G.IsAcyclic

/-- In the class, `Θ₂` has no children at all.
Source: everitt-2019 Fig. 7 ("lacks paths from `Θ₂` to `R_k`")
Kind: L -/
lemma IsTIIgnoring.no_child {G : Digraph Node} (h : IsTIIgnoring G) (w : Node) :
    ¬ G.Adj Θ₂ w := by
  cases w with
  | S₁ => exact h.no_state _ (Or.inl rfl)
  | S₂ => exact h.no_state _ (Or.inr (Or.inl rfl))
  | S₃ => exact h.no_state _ (Or.inr (Or.inr rfl))
  | R₁ => exact h.no_reward _ (Or.inl rfl)
  | R₂ => exact h.no_reward _ (Or.inr rfl)
  | A₁ => exact h.no_info
  | Θ₁ => exact h.no_back
  | Θ₂ => exact fun e => h.acyclic Θ₂ (Relation.TransGen.single e)

/-- In the class, `Θ₂` reaches nothing.
Source: everitt-2019 Fig. 7
Kind: L -/
lemma IsTIIgnoring.no_desc {G : Digraph Node} (h : IsTIIgnoring G) (w : Node) :
    ¬ G.IsAncestor Θ₂ w := by
  intro e
  induction e with
  | single e => exact h.no_child _ e
  | tail _ _ ih => exact ih

/-- **Graph lemma**: in the class, `Θ₂` is an ancestor-or-self of no reward.
Source: everitt-2019 Fig. 7 (l. 347: "lacks paths from `Θ₂` to `R_k`")
Kind: L -/
lemma IsTIIgnoring.not_ancSelf_reward {G : Digraph Node} (h : IsTIIgnoring G) {u : Node}
    (hu : kind u = .utility) : ¬ Scm.AncSelf G u Θ₂ := by
  rintro (e | e)
  · cases u <;> cases hu <;> cases e
  · exact h.no_desc u e

variable {G : Digraph Node} [DecidableRel G.Adj] {Val E : Node → Type} [∀ v, Fintype (E v)]

/-- A CID on the class's node set with the class's kinds.
Source: everitt-2019 Fig. 7
Kind: D -/
structure ClassCid (G : Digraph Node) (Val : Node → Type) extends Cid G Val where
  kind_eq : toCid.kind = TI.kind
  ti : IsTIIgnoring G

/-- **Claim 3 / Claim 9 / Holtman's ITC, the theorem.** In every SCIM compatible with the
TI-ignoring class, every policy's value is invariant under every soft intervention at `Θ₂`: the
agent lacks an instrumental goal to influence the implemented objective. Content: T2's ancestor
invariance plus the graph lemma. On this eight-node type the class is exactly "`Θ₂` is a sink"
(module docstring), so this is the sink instance of `indifferent_of_not_ancSelf_utility`; the
contrast with the standard agent, whose reward reads `Θ₂` and who tampers, is
`RocksDiamonds.rocks_and_diamonds`.
Source: everitt-2019 Claim 3 (l. 347); Claim 9 (l. 559); holtman-2021 §7.4 Def. 9 ("indifferent to all of `I₁, I₂, …`")
Kind: C
Fidelity: exact (Claim 3 with "lack an instrumental goal" read as Def. 9 indifference / no ICI; the
two-step class is Everitt's three-step Fig. 7 truncated)
Hyps: — -/
theorem tiIgnoring_indifferent (C : ClassCid G Val) (M : Scim C.toCid E)
    (hΘ : C.toCid.kind Θ₂ ≠ .decision) : M.IndifferentTo Θ₂ hΘ :=
  M.indifferent_of_not_ancSelf_utility hΘ fun u hu =>
    C.ti.not_ancSelf_reward (by rw [← C.kind_eq]; exact hu)

/-- The same, reading (ii): every optimal policy stays optimal with the same value.
Source: everitt-2019 Claim 3; corr-refs-2-002 reading (ii)
Kind: C -/
theorem tiIgnoring_indifferentToOpt (C : ClassCid G Val) (M : Scim C.toCid E)
    (hΘ : C.toCid.kind Θ₂ ≠ .decision) : M.IndifferentToOpt Θ₂ hΘ :=
  M.indifferentToOpt_of_indifferentTo hΘ (tiIgnoring_indifferent C M hΘ)

/-- **No instrumental control incentive on `Θ₂`** (Thm 18 soundness on the class), at any context of
`A₁`, provided an optimal policy exists.
Source: everitt-2019 Claim 3 (l. 347), Claim 9 (l. 559); everitt-2021 Thm 18
Kind: C
Fidelity: exact
Hyps: — -/
theorem tiIgnoring_not_hasICI (C : ClassCid G Val) (M : Scim C.toCid E)
    (hopt : ∃ π, M.IsOptimal π) (paD : ParentVals G Val A₁) : ¬ M.HasICI A₁ Θ₂ paD :=
  M.not_hasICI_of_noPath
    (C.toCid.noPathThrough_of_not_ancSelf
      (fun u hu => C.ti.not_ancSelf_reward (by rw [← C.kind_eq]; exact hu)) A₁)
    hopt paD

/-- **Claim 3** (implemented reward function `Θ = Θ^R`): TI-ignoring current-RF agents lack an
instrumental goal to influence the implemented RF when it is private and state-based.
Source: everitt-2019 Claim 3 (l. 347)
Kind: C
Fidelity: exact -/
theorem claim3 (C : ClassCid G Val) (M : Scim C.toCid E) (hΘ : C.toCid.kind Θ₂ ≠ .decision) :
    M.IndifferentTo Θ₂ hΘ :=
  tiIgnoring_indifferent C M hΘ

/-- **Claim 9** (predictive model `Θ = Θ^PM`, belief nodes as structure nodes): a TI-ignoring
belief-based agent lacks an instrumental goal to influence the predictive model when the
implemented reward function is fixed and the predictive model is private.
Source: everitt-2019 Claim 9 (l. 559), Fig. 12
Kind: C
Fidelity: exact (same graph class; belief nodes `B_t` are the `S_t` slots) -/
theorem claim9 (C : ClassCid G Val) (M : Scim C.toCid E) (hΘ : C.toCid.kind Θ₂ ≠ .decision) :
    M.IndifferentTo Θ₂ hΘ :=
  tiIgnoring_indifferent C M hΘ

/-- **Holtman's ITC**: in the rerouted planning world every reward reads `I₀`, so the later input
terminal signals `I_{t ≥ 1}` are off every path to value and the planner is indifferent to them
(Def. 9), for every policy and every replacement of their mechanism.
Source: holtman-2021 §7.4 (l. 835–913), Def. 9 (l. 917)
Kind: C
Fidelity: exact (Def. 9's "∀D. U_p = U_q" as `IndifferentTo`) -/
theorem holtman_itc (C : ClassCid G Val) (M : Scim C.toCid E) (hΘ : C.toCid.kind Θ₂ ≠ .decision) :
    M.IndifferentTo Θ₂ hΘ :=
  tiIgnoring_indifferent C M hΘ

/-- Fig. 7's edges
`S₁ → A₁, S₁ → S₂, A₁ → S₂, S₂ → S₃, Θ₁ → R₁, Θ₁ → R₂, S₁ → R₁, S₂ → R₂, A₁ → Θ₂, Θ₁ → Θ₂` — the
agent influences `Θ₂`, which then influences nothing.
Source: everitt-2019 Fig. 7
Kind: D -/
def fig7Adj : Node → Node → Bool
  | S₁, A₁ => true
  | S₁, S₂ => true
  | A₁, S₂ => true
  | S₂, S₃ => true
  | Θ₁, R₁ => true
  | Θ₁, R₂ => true
  | S₁, R₁ => true
  | S₂, R₂ => true
  | A₁, Θ₂ => true
  | Θ₁, Θ₂ => true
  | _, _ => false

/-- Fig. 7 as a digraph.
Source: everitt-2019 Fig. 7
Kind: D -/
def fig7 : Digraph Node := ⟨fun u v => fig7Adj u v = true⟩

instance : DecidableRel fig7.Adj := fun u v => inferInstanceAs (Decidable (fig7Adj u v = true))

/-- A rank for Fig. 7.
Source: none: infrastructure
Kind: D -/
def fig7Rank : Node → ℕ
  | S₁ => 0 | Θ₁ => 0 | A₁ => 1 | S₂ => 2 | Θ₂ => 2 | S₃ => 3 | R₁ => 1 | R₂ => 3

/-- Fig. 7 is in the class, and `A₁ → Θ₂` is present (the agent can influence the objective).
**Inhabitation only** (audit r1 B2): the class forces `Θ₂` to be a sink, so no member can exhibit a
model in which anything depends on `Θ₂`; the contrast the mandate's T3(c) asks for is
`RocksDiamonds.rocks_and_diamonds`.
Source: everitt-2019 Fig. 7
Kind: N− (inhabits the class; exercises no contrast) -/
theorem fig7_isTIIgnoring : IsTIIgnoring fig7 ∧ fig7.Adj A₁ Θ₂ :=
  ⟨{ no_state := by decide
     no_reward := by decide
     no_info := by decide
     no_back := by decide
     acyclic := Digraph.isAcyclic_of_rank fig7Rank (by decide) }, by decide⟩

end TI

end Cleanroom.Corrigibility.CorrScimCid
