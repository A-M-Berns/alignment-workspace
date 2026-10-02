import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Cleanroom.Corrigibility.CorrScimCid.FinModel
import Mathlib.Tactic.DeriveFintype

/-!
# The converse of Holtman's property fails (T2 d)

A three-node SCIM `D → X → U` in which the mechanism of `U` ignores `X`: `X` lies on the path from
the decision to the utility (so it is downstream *and* on a path to value), yet every policy's value
is invariant under every soft intervention at `X` — the planner is indifferent to `X` although the
graph admits an incentive. This is Everitt 2019's "a diagram can only be used to assert the absence
of instrumental goals, and never their presence" (l. 203), and the vacuity check for every "may have
an incentive" sentence in the sources.

Source: everitt-2019 §2.2 (l. 203); holtman-2021 §8.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.ThreeNode

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid

set_option linter.unusedSectionVars false

/-- The three nodes.
Source: everitt-2019 §2.2
Kind: D -/
inductive Node
  | D | X | U
  deriving DecidableEq, Fintype, Repr

open Node

/-- Edges `D → X → U`.
Source: everitt-2019 §2.2
Kind: D -/
def adjB : Node → Node → Bool
  | D, X => true
  | X, U => true
  | _, _ => false

/-- The chain digraph.
Source: everitt-2019 §2.2
Kind: D -/
def G : Digraph Node := ⟨fun u v => adjB u v = true⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

/-- Rank.
Source: none: infrastructure
Kind: D -/
def rank : Node → ℕ
  | D => 0 | X => 1 | U => 2

/-- Values: `Bool` at `D`, `X`; `ℝ` at `U`.
Source: everitt-2019 §2.2
Kind: D -/
def Val : Node → Type
  | U => ℝ
  | _ => Bool

/-- Trivial noise.
Source: none: infrastructure
Kind: D -/
def E : Node → Type := fun _ => Unit

instance instFintypeE : ∀ v, Fintype (E v) := fun _ => inferInstanceAs (Fintype Unit)

/-- Kinds.
Source: everitt-2019 §2.2
Kind: D -/
def kind : Node → NodeKind
  | D => .decision
  | X => .struct
  | U => .utility

/-- The CID `D → X → U`.
Source: everitt-2019 §2.2
Kind: D -/
def C : Cid G Val where
  acyclic := Digraph.isAcyclic_of_rank rank (by decide)
  kind := kind
  utilVal := fun v _ => match v with
    | U => fun x => x
    | D => fun _ => 0
    | X => fun _ => 0
  utility_sink := by decide

/-- The SCIM: `X` copies `D`; `U` is the constant `1` — it ignores its parent `X`.
Source: everitt-2019 §2.2 (l. 203: "a conditional probability distribution `P(Y | X)` may completely
ignore the value of `X`")
Kind: D -/
noncomputable def Mdl : Scim C E where
  P := fun _ => unitD
  f := fun v h => match v, h with
    | X, _ => fun pa _ => pa ⟨D, by decide⟩
    | U, _ => fun _ _ => (1 : ℝ)
    | D, h => absurd rfl h

/-- `X` is downstream of the decision and on the path `D → X → U` to value: the graph admits an
incentive on `X` (Thm 18's criterion holds).
Source: everitt-2019 §2.2; everitt-2021 Thm 18
Kind: N+ -/
theorem X_on_path : C.Downstream X ∧ ¬ C.NotOnPathToValue X := by
  refine ⟨⟨D, rfl, Relation.TransGen.single (by decide)⟩, fun h => ?_⟩
  exact h D U rfl rfl ⟨Or.inr (Relation.TransGen.single (by decide)),
    Or.inr (Relation.TransGen.single (by decide))⟩

/-- Yet every policy is indifferent to `X`: the value is `1` under every policy and every soft
intervention at `X`.
Source: everitt-2019 §2.2 (l. 203)
Kind: N+ -/
theorem indifferent_X : Mdl.IndifferentTo X (by decide) := by
  intro π g
  have hval : ∀ (N : Scim C E), (N.f U (by decide) = fun _ _ => (1 : ℝ)) → N.value π = 1 := by
    intro N hN
    unfold Scim.value Cid.utilSum
    have hU : ∀ ε, (∑ v, if h : C.kind v = .utility then C.utilVal v h (N.ev π ε v) else 0) = 1 := by
      intro ε
      have hev : N.ev π ε U = (1 : ℝ) := by
        rw [Scim.ev_of_ne N π ε (by decide), hN]
      rw [Fintype.sum_eq_single U (fun v hv => by
        cases v with
        | U => exact absurd rfl hv
        | D => exact dif_neg (by decide)
        | X => exact dif_neg (by decide))]
      change C.utilVal U rfl (N.ev π ε U) = 1
      rw [hev]
      rfl
    simp only [hU]
    exact expect_const N.μ 1
  rw [hval _ (by
      show Function.update Mdl.f X (fun _ => g) U (by decide) = fun _ _ => (1 : ℝ)
      rw [Function.update_of_ne (show U ≠ X by decide)]
      rfl),
    hval Mdl rfl]

/-- **The converse of Holtman's property fails**: a node on a decision-to-utility path to which the
planner is nonetheless indifferent.
Source: everitt-2019 §2.2 (l. 203); holtman-2021 §8
Kind: N+
Fidelity: exact
Hyps: — -/
theorem converse_fails :
    ¬ C.NotOnPathToValue X ∧ C.Downstream X ∧ Mdl.IndifferentTo X (by decide) :=
  ⟨X_on_path.2, X_on_path.1, indifferent_X⟩

end Cleanroom.Corrigibility.CorrScimCid.ThreeNode
