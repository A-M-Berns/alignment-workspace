import Cleanroom.Found.DpCoreTree.Recording
import Cleanroom.Found.DpCoreTree.Occurrence
import Cleanroom.Found.DpCoreTree.Basic
import Cleanroom.Found.DpCoreTree.Catalogue

/-!
# The predictor-labelled instantiation `B_θ`: GR-D2's node classes, GR-2, GR-4 — T14(a)(b) of
[[dp-firstperson-sc-mandate]]

* **Node classes (GR-D2, repaired)** at a decision node carrying `d`: **live** if subtree-veridical
  (every leaf below has its world in `O_d`); **routing** if not live and some `O_d`-leaf below it
  passes no further `d`-node on the way down (the node's own draw is the act an `O_d`-world
  records); **predictor** otherwise (not live, and every `O_d`-leaf below passes another `d`-node —
  Omega's simulation of the agent at `d`). `LiveAt`/`RoutingAt`/`PredictorAt` are the classes of
  the subtree rooted at a decision node (the form the structural recursion uses); `Live`/`Routing`/
  `Predictor` are the same classes at a `DecNode` address, and `live_iff_subtreeVeridical` says
  `Live` is `dp-core-tree`'s `SubtreeVeridical`. `RoutingFree B d`: no routing `d`-node.
* **`replacePred obs θ B` (`B_θ`)**: every predictor node carrying `d` is replaced by a chance node
  with law `θ d` over the same children (recursively, so nested predictors are replaced too); live
  and routing nodes are untouched. The leaf set is carried along by `fromRepl` (a bijection,
  `replEquiv`), and `world`/`payoff` are preserved. The construction is *meaningful* under the
  GR-D2 domain hypothesis (routing-free and covered at `d`: at a routing node it would delete the
  agent's only consultation); the identities below hold for every tree, and the domain hypothesis
  is for meaning, not for the identities (mandate T14(a)).
* **GR-2, exactness** (`leafLaw_replacePred_self`, `value_replacePred_self`,
  `nu_replacePred_self`): under Definition 6 (independent redraws) `μ_{B_C, C} = μ_{B, C}` for
  *every* tree — a chance node with law `C(d)` samples the same law as a `d`-node under `C`. The
  shared-seed failure for mixed `C` on nested fibers (`value' C B_C ≠ value' C B` on TN-V2) is in
  `WitnessesPredictor.lean`.
* **GR-4, verdict substitution** (`value_replacePred_sub_le`): for `θ, θ'` differing only at `d`
  and payoffs in `[m, M]`, `|V_{B_θ}(C) − V_{B_θ'}(C)| ≤ (M − m) · TV(θ_d, θ'_d) · usePred`, with
  `usePred θ C d B` the expected number of predictor `d`-nodes on a run of `B_θ` (defined by the
  same recursion, `usePred_eq_expectation` reads it as an expectation). Proved by structural
  induction with a per-node total-variation bound (`abs_sum_sub_mul_le_tv`), no coupling.

Vocabulary: "predictor" is GR-D2's node class, not SC's anything; `θ` is a *label* (a verdict in
`∏_d Δ(A_d)`), `C` the procedure actually run.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- A distribution re-indexed along a bijection: `(reindex θ e).w b = θ.w (e.symm b)`.
Source: none: infrastructure (the law `θ d` placed on a `Fin n`-indexed chance node)
Kind: D -/
def FinDistr.reindex {α β : Type} [Fintype α] [Fintype β] (θ : FinDistr K α) (e : α ≃ β) :
    FinDistr K β where
  w := fun b => θ.w (e.symm b)
  nonneg := fun b => θ.nonneg _
  sum_one := (Equiv.sum_comp e.symm θ.w).trans θ.sum_one

/-- Weights of `reindex`. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.reindex_w {α β : Type} [Fintype α] [Fintype β] (θ : FinDistr K α)
    (e : α ≃ β) (b : β) : (FinDistr.reindex θ e).w b = θ.w (e.symm b) := rfl

/-! ## GR-D2's node classes -/

section classes

variable (obs : ι → Finset Ω)

/-- **Live** (GR-D2) at the decision node `decision d child`: every leaf below has its world in
`O_d` — subtree-veridicality (Definition 7) read on the subtree.
Source: `grounding.md` GR-D2 ("live if it is subtree-veridical")
Kind: D
Fidelity: exact -/
def LiveAt (d : ι) (child : acts d → Tree Ω ι acts K) : Prop :=
  ∀ a (ℓ : (child a).Leaves), world (child a) ℓ ∈ obs d

/-- **Routing** (GR-D2) at `decision d child`: not live, and some `O_d`-leaf below it passes no
further `d`-node on the way down (`count d = 0` in the child) — the node's own draw is the act an
`O_d`-world records (Remark 3.4's routing root).
Source: `grounding.md` GR-D2 ("routing if it is not subtree-veridical and some `O_d`-leaf below `q`
has no `d`-node strictly between `q` and it")
Kind: D
Fidelity: exact -/
def RoutingAt (d : ι) (child : acts d → Tree Ω ι acts K) : Prop :=
  ¬ LiveAt obs d child ∧
    ∃ (a : acts d) (ℓ : (child a).Leaves), world (child a) ℓ ∈ obs d ∧ count d (child a) ℓ = 0

/-- **Predictor** (GR-D2) at `decision d child`: not live, and every `O_d`-leaf below it passes
another `d`-node on the way down — Omega's simulation of the agent at `d`. Extent of the class
(GR-D2's "(if any)"): a `d`-node with **no** `O_d`-leaf below it is a predictor node vacuously
(the second clause is empty, the first holds), not a routing node; it is replaced by `θ d` in
`replacePred` and counted by `usePred`. Faithful to the source's text (audit r2 adversarial N3,
probe `audit-r2-probes/PredictorVacuous.lean`; findings F21).
Source: `grounding.md` GR-D2 ("predictor otherwise — not subtree-veridical, and every `O_d`-leaf
below it (if any) passes another `d`-node on the way down")
Kind: D
Fidelity: exact -/
def PredictorAt (d : ι) (child : acts d → Tree Ω ι acts K) : Prop :=
  ¬ LiveAt obs d child ∧
    ∀ a (ℓ : (child a).Leaves), world (child a) ℓ ∈ obs d → 0 < count d (child a) ℓ

/-- The three classes are exhaustive and exclusive: a non-live node is routing or predictor, never
both. Source: `grounding.md` GR-D2 (the trichotomy). Kind: L -/
theorem routingAt_or_predictorAt (d : ι) (child : acts d → Tree Ω ι acts K)
    (h : ¬ LiveAt obs d child) : RoutingAt obs d child ∨ PredictorAt obs d child := by
  by_cases hp : ∀ a (ℓ : (child a).Leaves), world (child a) ℓ ∈ obs d → 0 < count d (child a) ℓ
  · exact Or.inr ⟨h, hp⟩
  · left
    refine ⟨h, ?_⟩
    simp only [not_forall, not_lt, Nat.le_zero] at hp
    obtain ⟨a, ℓ, hw, hc⟩ := hp
    exact ⟨a, ℓ, hw, hc⟩

/-- Routing and predictor exclude each other. Source: `grounding.md` GR-D2. Kind: L -/
theorem not_routingAt_of_predictorAt (d : ι) (child : acts d → Tree Ω ι acts K)
    (h : PredictorAt obs d child) : ¬ RoutingAt obs d child := by
  rintro ⟨_, a, ℓ, hw, hc⟩
  have := h.2 a ℓ hw
  omega

/-- A live node is neither routing nor predictor. Source: `grounding.md` GR-D2. Kind: L -/
theorem not_predictorAt_of_liveAt (d : ι) (child : acts d → Tree Ω ι acts K)
    (h : LiveAt obs d child) : ¬ PredictorAt obs d child := fun hp => hp.1 h

/-- **Live at a `DecNode` address**, by recursion along the address.
Source: `grounding.md` GR-D2
Kind: D -/
def Live : (B : Tree Ω ι acts K) → B.DecNode → Prop
  | leaf _ _, q => q.elim
  | chance _ _ child, ⟨i, q⟩ => Live (child i) q
  | decision d child, none => LiveAt obs d child
  | decision _ child, some ⟨a, q⟩ => Live (child a) q

/-- **Routing at a `DecNode` address.** Source: `grounding.md` GR-D2. Kind: D -/
def Routing : (B : Tree Ω ι acts K) → B.DecNode → Prop
  | leaf _ _, q => q.elim
  | chance _ _ child, ⟨i, q⟩ => Routing (child i) q
  | decision d child, none => RoutingAt obs d child
  | decision _ child, some ⟨a, q⟩ => Routing (child a) q

/-- **Predictor at a `DecNode` address.** Source: `grounding.md` GR-D2. Kind: D -/
def Predictor : (B : Tree Ω ι acts K) → B.DecNode → Prop
  | leaf _ _, q => q.elim
  | chance _ _ child, ⟨i, q⟩ => Predictor (child i) q
  | decision d child, none => PredictorAt obs d child
  | decision _ child, some ⟨a, q⟩ => Predictor (child a) q

/-- **`Live` is `dp-core-tree`'s `SubtreeVeridical`** (Definition 7), so GR-D2's "live" is the
mandate's `Live := SubtreeVeridical B q`.
Source: `grounding.md` GR-D2 ("live if it is subtree-veridical (Def 7)")
Kind: L
Fidelity: exact -/
theorem live_iff_subtreeVeridical :
    (B : Tree Ω ι acts K) → (q : B.DecNode) → (Live obs B q ↔ SubtreeVeridical obs B q)
  | leaf _ _, q => q.elim
  | chance n β child, ⟨i, q⟩ => by
      rw [show Live obs (chance n β child) ⟨i, q⟩ = Live obs (child i) q from rfl,
        live_iff_subtreeVeridical (child i) q]
      constructor
      · intro h ℓ hℓ
        obtain ⟨j, ℓ⟩ := ℓ
        rw [mem_leavesBelow, edgeOf_chance] at hℓ
        by_cases hji : j = i
        · subst hji
          rw [dif_pos rfl] at hℓ
          exact h ℓ ((mem_leavesBelow _ _ _).mpr hℓ)
        · rw [dif_neg hji] at hℓ; exact absurd hℓ (by simp)
      · intro h ℓ hℓ
        have hmem := (mem_leavesBelow (chance n β child) ⟨i, q⟩ ⟨i, ℓ⟩).mpr (by
          rw [edgeOf_chance, dif_pos rfl]
          exact (mem_leavesBelow _ _ _).mp hℓ)
        exact h ⟨i, ℓ⟩ hmem
  | decision d child, none => by
      constructor
      · intro h ℓ _
        obtain ⟨a, ℓ⟩ := ℓ
        exact h a ℓ
      · intro h a ℓ
        exact h ⟨a, ℓ⟩ (by rw [mem_leavesBelow, edgeOf_decision_none]; rfl)
  | decision d child, some ⟨a, q⟩ => by
      rw [show Live obs (decision d child) (some ⟨a, q⟩) = Live obs (child a) q from rfl,
        live_iff_subtreeVeridical (child a) q]
      constructor
      · intro h ℓ hℓ
        obtain ⟨b, ℓ⟩ := ℓ
        rw [mem_leavesBelow, edgeOf_decision_some] at hℓ
        by_cases hba : b = a
        · subst hba
          rw [dif_pos rfl] at hℓ
          exact h ℓ ((mem_leavesBelow _ _ _).mpr hℓ)
        · rw [dif_neg hba] at hℓ; exact absurd hℓ (by simp)
      · intro h ℓ hℓ
        have hmem := (mem_leavesBelow (decision d child) (some ⟨a, q⟩) ⟨a, ℓ⟩).mpr (by
          rw [edgeOf_decision_some, dif_pos rfl]
          exact (mem_leavesBelow _ _ _).mp hℓ)
        exact h ⟨a, ℓ⟩ hmem

/-- **Routing-free at `d`** (GR-D2's domain hypothesis, first half): no routing node carries `d`.
Source: `grounding.md` GR-D2 ("`B` is routing-free at `d` (no routing node in `F_d`)")
Kind: D -/
def RoutingFree (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∀ q : B.DecNode, pt B q = d → ¬ Routing obs B q

end classes

/-! ## The replacement `B_θ` -/

/-- The replaced tree together with the bijection from the original leaves onto its leaves (the
leaf type changes shape at each replaced node: a `Σ a : acts d` becomes a `Σ i : Fin |A_d|`).
Source: none: infrastructure
Kind: D -/
structure Repl (B : Tree Ω ι acts K) where
  /-- The replaced tree. -/
  tree : Tree Ω ι acts K
  /-- The leaf bijection, original leaves to replaced leaves. -/
  equiv : B.Leaves ≃ tree.Leaves

section replace

variable (obs : ι → Finset Ω) (θ : Proc ι acts K)

open Classical in
/-- The replacement with its leaf bijection, by structural recursion: a predictor node
`decision d child` becomes `chance |A_d| (θ d ∘ e⁻¹) (child ∘ e⁻¹)` with `e := Fintype.equivFin`;
every other node keeps its shape and recurses.
Source: `grounding.md` GR-D2 ("`B_θ` is `B` with every predictor node of `d` replaced by a chance
node with law `θ_d` over the same children")
Kind: D -/
noncomputable def replacePredAux : (B : Tree Ω ι acts K) → Repl B
  | leaf ω r => ⟨leaf ω r, Equiv.refl _⟩
  | chance n β child =>
      ⟨chance n β fun i => (replacePredAux (child i)).tree,
        Equiv.sigmaCongrRight fun i => (replacePredAux (child i)).equiv⟩
  | decision d child =>
      if PredictorAt obs d child then
        ⟨chance (Fintype.card (acts d)) (FinDistr.reindex (θ d) (Fintype.equivFin (acts d)))
            fun i => (replacePredAux (child ((Fintype.equivFin (acts d)).symm i))).tree,
          (Equiv.sigmaCongrRight fun a => (replacePredAux (child a)).equiv).trans
            (Equiv.sigmaCongrLeft (β := fun a => (replacePredAux (child a)).tree.Leaves)
              (Fintype.equivFin (acts d)).symm).symm⟩
      else
        ⟨decision d fun a => (replacePredAux (child a)).tree,
          Equiv.sigmaCongrRight fun a => (replacePredAux (child a)).equiv⟩

/-- **`B_θ := replacePred obs θ B`**: the predictor-labelled instantiation — every predictor node
carrying `d` replaced by a chance node with law `θ d` over the same children. Meaningful under
GR-D2's domain hypothesis (`RoutingFree ∧ Covers`); defined, and the identities below proved, for
every tree.
Source: `grounding.md` GR-D2 ("Predictor-labelled instantiation `B_θ`"); mandate T14(a)
Kind: D
Fidelity: exact (the domain hypothesis is for meaning, not for the construction) -/
noncomputable def replacePred (B : Tree Ω ι acts K) : Tree Ω ι acts K :=
  (replacePredAux obs θ B).tree

/-- The leaf bijection of the replacement, original leaves to replaced leaves.
Source: none: infrastructure. Kind: D -/
noncomputable def replEquiv (B : Tree Ω ι acts K) : B.Leaves ≃ (replacePred obs θ B).Leaves :=
  (replacePredAux obs θ B).equiv

/-- A replaced leaf read back as an original leaf (the inverse bijection; this is the direction
whose computation rules are cast-free).
Source: none: infrastructure. Kind: D -/
noncomputable def fromRepl (B : Tree Ω ι acts K) : (replacePred obs θ B).Leaves → B.Leaves :=
  (replacePredAux obs θ B).equiv.symm

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem replacePred_leaf (ω : Ω) (r : K) :
    replacePred obs θ (leaf ω r) = leaf ω r := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem replacePred_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    replacePred obs θ (chance n β child) = chance n β fun i => replacePred obs θ (child i) := rfl

/-- Equation lemma, predictor case. Source: none: infrastructure. Kind: L -/
theorem replacePred_decision_pos {d : ι} {child : acts d → Tree Ω ι acts K}
    (h : PredictorAt obs d child) :
    replacePred obs θ (decision d child) =
      chance (Fintype.card (acts d)) (FinDistr.reindex (θ d) (Fintype.equivFin (acts d)))
        fun i => replacePred obs θ (child ((Fintype.equivFin (acts d)).symm i)) := by
  unfold replacePred; rw [replacePredAux, if_pos h]

/-- Equation lemma, non-predictor case. Source: none: infrastructure. Kind: L -/
theorem replacePred_decision_neg {d : ι} {child : acts d → Tree Ω ι acts K}
    (h : ¬ PredictorAt obs d child) :
    replacePred obs θ (decision d child) = decision d fun a => replacePred obs θ (child a) := by
  unfold replacePred; rw [replacePredAux, if_neg h]

open Classical in
/-- The weight the replaced tree assigns at an original leaf's nodes: `θ` at predictor nodes, `C`
elsewhere (the leaf law of `B_θ` read on `B`'s leaves).
Source: `grounding.md` GR-D2, GR-2 (`μ_{B_θ, C}`)
Kind: D -/
noncomputable def leafLawRepl (C : Proc ι acts K) : (B : Tree Ω ι acts K) → B.Leaves → K
  | leaf _ _, _ => 1
  | chance _ β child, ⟨i, ℓ⟩ => β.w i * leafLawRepl C (child i) ℓ
  | decision d child, ⟨a, ℓ⟩ =>
      (if PredictorAt obs d child then (θ d).w a else (C d).w a) * leafLawRepl C (child a) ℓ

/-- `world` is preserved by the replacement. Source: none: infrastructure. Kind: L -/
theorem world_replacePred :
    (B : Tree Ω ι acts K) → ∀ ℓ' : (replacePred obs θ B).Leaves,
      world (replacePred obs θ B) ℓ' = world B (fromRepl obs θ B ℓ')
  | leaf _ _, _ => rfl
  | chance n β child, ⟨i, ℓ'⟩ => by
      show world (replacePred obs θ (child i)) ℓ' = world (child i) (fromRepl obs θ (child i) ℓ')
      exact world_replacePred (child i) ℓ'
  | decision d child, ℓ' => by
      revert ℓ'
      show ∀ ℓ' : (replacePredAux obs θ (decision d child)).tree.Leaves,
        world (replacePredAux obs θ (decision d child)).tree ℓ' =
          world (decision d child) ((replacePredAux obs θ (decision d child)).equiv.symm ℓ')
      rw [replacePredAux]
      by_cases h : PredictorAt obs d child
      · rw [if_pos h]
        rintro ⟨i, ℓ'⟩
        show world (replacePred obs θ (child _)) ℓ' = world (child _) (fromRepl obs θ (child _) ℓ')
        exact world_replacePred (child _) ℓ'
      · rw [if_neg h]
        rintro ⟨a, ℓ'⟩
        show world (replacePred obs θ (child a)) ℓ' = world (child a) (fromRepl obs θ (child a) ℓ')
        exact world_replacePred (child a) ℓ'

/-- `payoff` is preserved by the replacement. Source: none: infrastructure. Kind: L -/
theorem payoff_replacePred :
    (B : Tree Ω ι acts K) → ∀ ℓ' : (replacePred obs θ B).Leaves,
      payoff (replacePred obs θ B) ℓ' = payoff B (fromRepl obs θ B ℓ')
  | leaf _ _, _ => rfl
  | chance n β child, ⟨i, ℓ'⟩ => by
      show payoff (replacePred obs θ (child i)) ℓ' = payoff (child i) (fromRepl obs θ (child i) ℓ')
      exact payoff_replacePred (child i) ℓ'
  | decision d child, ℓ' => by
      revert ℓ'
      show ∀ ℓ' : (replacePredAux obs θ (decision d child)).tree.Leaves,
        payoff (replacePredAux obs θ (decision d child)).tree ℓ' =
          payoff (decision d child) ((replacePredAux obs θ (decision d child)).equiv.symm ℓ')
      rw [replacePredAux]
      by_cases h : PredictorAt obs d child
      · rw [if_pos h]
        rintro ⟨i, ℓ'⟩
        show payoff (replacePred obs θ (child _)) ℓ' = payoff (child _) (fromRepl obs θ (child _) ℓ')
        exact payoff_replacePred (child _) ℓ'
      · rw [if_neg h]
        rintro ⟨a, ℓ'⟩
        show payoff (replacePred obs θ (child a)) ℓ' = payoff (child a) (fromRepl obs θ (child a) ℓ')
        exact payoff_replacePred (child a) ℓ'

open Classical in
/-- **The leaf law of `B_θ` under `C`, read on `B`'s leaves**: `θ` at predictor nodes, `C`
elsewhere.
Source: `grounding.md` GR-2 (`μ_{B_θ, C}`)
Kind: L -/
theorem leafLaw_replacePred (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ' : (replacePred obs θ B).Leaves,
      leafLaw C (replacePred obs θ B) ℓ' = leafLawRepl obs θ C B (fromRepl obs θ B ℓ')
  | leaf _ _, _ => rfl
  | chance n β child, ⟨i, ℓ'⟩ => by
      show β.w i * leafLaw C (replacePred obs θ (child i)) ℓ' =
        β.w i * leafLawRepl obs θ C (child i) (fromRepl obs θ (child i) ℓ')
      rw [leafLaw_replacePred C (child i) ℓ']
  | decision d child, ℓ' => by
      revert ℓ'
      show ∀ ℓ' : (replacePredAux obs θ (decision d child)).tree.Leaves,
        leafLaw C (replacePredAux obs θ (decision d child)).tree ℓ' =
          leafLawRepl obs θ C (decision d child)
            ((replacePredAux obs θ (decision d child)).equiv.symm ℓ')
      rw [replacePredAux]
      by_cases h : PredictorAt obs d child
      · rw [if_pos h]
        rintro ⟨i, ℓ'⟩
        show (θ d).w ((Fintype.equivFin (acts d)).symm i) *
            leafLaw C (replacePred obs θ (child _)) ℓ' =
          (if PredictorAt obs d child then (θ d).w ((Fintype.equivFin (acts d)).symm i)
            else (C d).w ((Fintype.equivFin (acts d)).symm i)) *
            leafLawRepl obs θ C (child _) (fromRepl obs θ (child _) ℓ')
        rw [if_pos h, leafLaw_replacePred C (child _) ℓ']
      · rw [if_neg h]
        rintro ⟨a, ℓ'⟩
        show (C d).w a * leafLaw C (replacePred obs θ (child a)) ℓ' =
          (if PredictorAt obs d child then (θ d).w a else (C d).w a) *
            leafLawRepl obs θ C (child a) (fromRepl obs θ (child a) ℓ')
        rw [if_neg h, leafLaw_replacePred C (child a) ℓ']

/-- Sums over the replaced leaves are sums over the original leaves. Source: none: infrastructure.
Kind: L -/
theorem sum_replacePred {M : Type} [AddCommMonoid M] (B : Tree Ω ι acts K)
    (f : B.Leaves → M) : ∑ ℓ' : (replacePred obs θ B).Leaves, f (fromRepl obs θ B ℓ') = ∑ ℓ, f ℓ :=
  Equiv.sum_comp (replacePredAux obs θ B).equiv.symm f

/-- **`value C B_θ` on `B`'s leaves.** Source: none: infrastructure. Kind: L -/
theorem value_replacePred (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    value C (replacePred obs θ B) = ∑ ℓ, leafLawRepl obs θ C B ℓ * payoff B ℓ := by
  unfold value
  rw [← sum_replacePred obs θ B (fun ℓ => leafLawRepl obs θ C B ℓ * payoff B ℓ)]
  exact Finset.sum_congr rfl fun ℓ' _ => by
    rw [leafLaw_replacePred, payoff_replacePred]

/-- **`ν_{B_θ, C}` on `B`'s leaves.** Source: none: infrastructure. Kind: L -/
theorem nu_replacePred (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nu C (replacePred obs θ B) X = ∑ ℓ, if world B ℓ ∈ X then leafLawRepl obs θ C B ℓ else 0 := by
  unfold nu Tree.mass worldEv
  rw [Finset.sum_filter,
    ← sum_replacePred obs θ B (fun ℓ => if world B ℓ ∈ X then leafLawRepl obs θ C B ℓ else 0)]
  exact Finset.sum_congr rfl fun ℓ' _ => by
    rw [leafLaw_replacePred, world_replacePred]

open Classical in
/-- The replaced leaf law sums to one on every tree. Source: none: infrastructure. Kind: L -/
theorem leafLawRepl_sum_one (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∑ ℓ, leafLawRepl obs θ C B ℓ = 1
  | leaf ω r => by
      show ∑ _ : Unit, (1 : K) = 1
      simp
  | chance n β child => by
      rw [sum_leaves_chance]
      show ∑ i, ∑ ℓ, β.w i * leafLawRepl obs θ C (child i) ℓ = 1
      simp_rw [← Finset.mul_sum, leafLawRepl_sum_one C, mul_one]
      exact β.sum_one
  | decision d child => by
      rw [sum_leaves_decision]
      show ∑ a, ∑ ℓ, (if PredictorAt obs d child then (θ d).w a else (C d).w a) *
        leafLawRepl obs θ C (child a) ℓ = 1
      simp_rw [← Finset.mul_sum, leafLawRepl_sum_one C, mul_one]
      by_cases h : PredictorAt obs d child
      · simp only [if_pos h]; exact (θ d).sum_one
      · simp only [if_neg h]; exact (C d).sum_one

/-! ## GR-2: exactness under independent redraws -/

open Classical in
/-- With `θ = C`, the replaced leaf law is the original one (every node samples `C`).
Source: `grounding.md` GR-2
Kind: L -/
theorem leafLawRepl_self (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLawRepl obs C C B ℓ = leafLaw C B ℓ
  | leaf _ _, _ => rfl
  | chance n β child, ⟨i, ℓ⟩ => by
      show β.w i * leafLawRepl obs C C (child i) ℓ = β.w i * leafLaw C (child i) ℓ
      rw [leafLawRepl_self C (child i) ℓ]
  | decision d child, ⟨a, ℓ⟩ => by
      show (if PredictorAt obs d child then (C d).w a else (C d).w a) *
          leafLawRepl obs C C (child a) ℓ = (C d).w a * leafLaw C (child a) ℓ
      rw [ite_self, leafLawRepl_self C (child a) ℓ]

/-- **GR-2, exactness (leaf form)**: under Definition 6 (independent redraws),
`μ_{B_C, C}(ℓ') = μ_{B, C}(ℓ)` along the leaf bijection, for *every* tree — a chance node with law
`C(d)` samples the same law as a `d`-node under `C`. GR-2's domain hypothesis (routing-free and
covered at every queried point, `θ_d = C(d)`) is for the *meaning* of `B_θ`, not for this identity.
Source: `grounding.md` GR-2 ("Under independent redraws `μ_{B_θ,C} = μ_{B,C}`"); mandate T14(a)
("state it without the domain hypothesis and note the hypothesis is for meaning")
Kind: P
Fidelity: stronger: no domain hypothesis (the identity is unconditional under Definition 6)
Hyps: none -/
theorem leafLaw_replacePred_self (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (ℓ' : (replacePred obs C B).Leaves) :
    leafLaw C (replacePred obs C B) ℓ' = leafLaw C B (fromRepl obs C B ℓ') := by
  rw [leafLaw_replacePred, leafLawRepl_self]

/-- **GR-2, value form**: `V_{B_C}(C) = V_B(C)` for every tree.
Source: `grounding.md` GR-2 (the values `9427/4900` on V2 and `1669/700` on V1 are instances)
Kind: P
Fidelity: stronger: no domain hypothesis
Hyps: none -/
theorem value_replacePred_self (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    value C (replacePred obs C B) = value C B := by
  rw [value_replacePred]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLawRepl_self]

/-- **GR-2, statistics form**: `ν_{B_C, C} = ν_{B, C}` for every tree.
Source: `grounding.md` GR-2; GR-D2′(iii) (`g_d = ν(O_d)` at both TN points)
Kind: P
Fidelity: stronger: no domain hypothesis
Hyps: none -/
theorem nu_replacePred_self (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nu C (replacePred obs C B) X = nu C B X := by
  rw [nu_replacePred]
  unfold nu Tree.mass worldEv
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLawRepl_self]

open Classical in
/-- The number of *non-predictor* `d`-nodes on the path to a leaf of `B` — the `d`-nodes that
survive the replacement (`count_replacePred`).
Source: none: infrastructure
Kind: D -/
noncomputable def countNonPred (d : ι) : (B : Tree Ω ι acts K) → B.Leaves → ℕ
  | leaf _ _, _ => 0
  | chance _ _ child, ⟨i, ℓ⟩ => countNonPred d (child i) ℓ
  | decision d' child, ⟨a, ℓ⟩ =>
      (if PredictorAt obs d' child then 0 else if d' = d then 1 else 0) + countNonPred d (child a) ℓ

open Classical in
/-- `#_d` on the replaced tree counts the non-predictor `d`-nodes of the original path.
Source: none: infrastructure
Kind: L -/
theorem count_replacePred (d : ι) :
    (B : Tree Ω ι acts K) → ∀ ℓ' : (replacePred obs θ B).Leaves,
      count d (replacePred obs θ B) ℓ' = countNonPred obs d B (fromRepl obs θ B ℓ')
  | leaf _ _, _ => rfl
  | chance n β child, ⟨i, ℓ'⟩ => by
      show count d (replacePred obs θ (child i)) ℓ' =
        countNonPred obs d (child i) (fromRepl obs θ (child i) ℓ')
      exact count_replacePred d (child i) ℓ'
  | decision d' child, ℓ' => by
      revert ℓ'
      show ∀ ℓ' : (replacePredAux obs θ (decision d' child)).tree.Leaves,
        count d (replacePredAux obs θ (decision d' child)).tree ℓ' =
          countNonPred obs d (decision d' child)
            ((replacePredAux obs θ (decision d' child)).equiv.symm ℓ')
      rw [replacePredAux]
      by_cases h : PredictorAt obs d' child
      · rw [if_pos h]
        rintro ⟨i, ℓ'⟩
        show count d (replacePred obs θ (child _)) ℓ' =
          (if PredictorAt obs d' child then 0 else if d' = d then 1 else 0) +
            countNonPred obs d (child _) (fromRepl obs θ (child _) ℓ')
        rw [if_pos h, Nat.zero_add, count_replacePred d (child _) ℓ']
      · rw [if_neg h]
        rintro ⟨a, ℓ'⟩
        show (if d' = d then 1 else 0) + count d (replacePred obs θ (child a)) ℓ' =
          (if PredictorAt obs d' child then 0 else if d' = d then 1 else 0) +
            countNonPred obs d (child a) (fromRepl obs θ (child a) ℓ')
        rw [if_neg h, count_replacePred d (child a) ℓ']

end replace

/-! ## GR-4: verdict substitution -/

section gr4

variable (obs : ι → Finset Ω)

/-- Total-variation distance of two distributions on a finite type, `½ ∑_a |p(a) − q(a)|`.
Source: `grounding.md` GR-4 (`TV(θ_d, θ'_d)`)
Kind: D -/
def tv {α : Type} [Fintype α] (p q : FinDistr K α) : K := (∑ a, |p.w a - q.w a|) / 2

/-- `tv ≥ 0`. Source: none: infrastructure. Kind: L -/
theorem tv_nonneg {α : Type} [Fintype α] (p q : FinDistr K α) : 0 ≤ tv p q :=
  div_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg _) (by norm_num)

/-- **The per-node total-variation bound**: for values `v` in `[m, M]`,
`|∑_a (p(a) − q(a)) v(a)| ≤ (M − m) · TV(p, q)` (centre `v` at `(m + M)/2`; the weights sum to
zero).
Source: `grounding.md` GR-4 proof ("payoff gap `≤ R` on divergence"; the maximal-coupling step in
algebraic form)
Kind: L -/
theorem abs_sum_sub_mul_le_tv {α : Type} [Fintype α] (p q : FinDistr K α) (v : α → K) (m M : K)
    (hlo : ∀ a, m ≤ v a) (hhi : ∀ a, v a ≤ M) :
    |∑ a, (p.w a - q.w a) * v a| ≤ (M - m) * tv p q := by
  have hc : ∑ a, (p.w a - q.w a) * v a = ∑ a, (p.w a - q.w a) * (v a - (m + M) / 2) := by
    have h0 : ∑ a, (p.w a - q.w a) * ((m + M) / 2) = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, p.sum_one, q.sum_one, sub_self, zero_mul]
    rw [← sub_zero (∑ a, (p.w a - q.w a) * v a), ← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hc]
  calc |∑ a, (p.w a - q.w a) * (v a - (m + M) / 2)|
      ≤ ∑ a, |(p.w a - q.w a) * (v a - (m + M) / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |p.w a - q.w a| * |v a - (m + M) / 2| := by simp_rw [abs_mul]
    _ ≤ ∑ a, |p.w a - q.w a| * ((M - m) / 2) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]; constructor <;> linarith [hlo a, hhi a]
    _ = (M - m) * tv p q := by rw [← Finset.sum_mul]; unfold tv; ring

/-- A weighted sum with non-negative weights is bounded termwise in absolute value.
Source: none: infrastructure. Kind: L -/
theorem abs_weighted_sum_le {α : Type} [Fintype α] (w : α → K) (hw : ∀ a, 0 ≤ w a) (x c : α → K)
    (hx : ∀ a, |x a| ≤ c a) : |∑ a, w a * x a| ≤ ∑ a, w a * c a :=
  calc |∑ a, w a * x a| ≤ ∑ a, |w a * x a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w a * |x a| := Finset.sum_congr rfl fun a _ => by rw [abs_mul, abs_of_nonneg (hw a)]
    _ ≤ ∑ a, w a * c a := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hx a) (hw a)

/-- A convex combination of values in `[m, M]` lies in `[m, M]`. Source: none: infrastructure.
Kind: L -/
theorem convex_bounds {α : Type} [Fintype α] (w : FinDistr K α) (x : α → K) (m M : K)
    (hlo : ∀ a, m ≤ x a) (hhi : ∀ a, x a ≤ M) :
    m ≤ ∑ a, w.w a * x a ∧ ∑ a, w.w a * x a ≤ M := by
  constructor
  · calc m = ∑ a, w.w a * m := by rw [← Finset.sum_mul, w.sum_one, one_mul]
      _ ≤ ∑ a, w.w a * x a :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hlo a) (w.nonneg a)
  · calc ∑ a, w.w a * x a ≤ ∑ a, w.w a * M :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hhi a) (w.nonneg a)
      _ = M := by rw [← Finset.sum_mul, w.sum_one, one_mul]

open Classical in
/-- **`usePred θ C d B`, the use rate**: the expected number of predictor `d`-nodes on a run of
`B_θ` under `C` (`𝔼_{μ_{B_θ, C}}[#pred_d]`), by the recursion of the run law — `θ` at predictor
nodes, `C` elsewhere, `+1` at each predictor `d`-node. `usePred_eq_expectation` is the expectation
form.
Source: `grounding.md` GR-4 (`𝔼_{μ_{B_θ,C}}[#pred_d]`); GR-D3 ("use rate `m_d(θ)`", the
one-instantiation case)
Kind: D
Fidelity: exact -/
noncomputable def usePred (θ C : Proc ι acts K) (d : ι) : Tree Ω ι acts K → K
  | leaf _ _ => 0
  | chance _ β child => ∑ i, β.w i * usePred θ C d (child i)
  | decision d' child =>
      if PredictorAt obs d' child then
        (if d' = d then 1 else 0) + ∑ a, (θ d').w a * usePred θ C d (child a)
      else ∑ a, (C d').w a * usePred θ C d (child a)

open Classical in
/-- `V_{B_θ}(C)` by the recursion of the run law (`θ` at predictor nodes, `C` elsewhere);
`value_replacePred_eq_valueRepl` identifies it with `value C (replacePred obs θ B)`.
Source: `grounding.md` GR-4 (`V_{B_θ}(C)`)
Kind: D -/
noncomputable def valueRepl (θ C : Proc ι acts K) : Tree Ω ι acts K → K
  | leaf _ r => r
  | chance _ β child => ∑ i, β.w i * valueRepl θ C (child i)
  | decision d child =>
      ∑ a, (if PredictorAt obs d child then (θ d).w a else (C d).w a) * valueRepl θ C (child a)

open Classical in
/-- The number of predictor `d`-nodes on the path to a leaf of `B`.
Source: `grounding.md` GR-4 (`#pred_d`)
Kind: D -/
noncomputable def predCount (d : ι) : (B : Tree Ω ι acts K) → B.Leaves → ℕ
  | leaf _ _, _ => 0
  | chance _ _ child, ⟨i, ℓ⟩ => predCount d (child i) ℓ
  | decision d' child, ⟨a, ℓ⟩ =>
      (if PredictorAt obs d' child then (if d' = d then 1 else 0) else 0) + predCount d (child a) ℓ

open Classical in
/-- **`value C B_θ` is `valueRepl`** (the recursion computes the value of the replaced tree).
Source: none: infrastructure
Kind: L -/
theorem value_replacePred_eq_valueRepl (θ C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → value C (replacePred obs θ B) = valueRepl obs θ C B
  | leaf ω r => by
      rw [value_replacePred]
      show ∑ _ : Unit, 1 * r = r
      simp
  | chance n β child => by
      rw [value_replacePred, sum_leaves_chance]
      show ∑ i, ∑ ℓ, β.w i * leafLawRepl obs θ C (child i) ℓ * payoff (child i) ℓ =
        ∑ i, β.w i * valueRepl obs θ C (child i)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← value_replacePred_eq_valueRepl θ C (child i), value_replacePred, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  | decision d child => by
      rw [value_replacePred, sum_leaves_decision]
      show ∑ a, ∑ ℓ, (if PredictorAt obs d child then (θ d).w a else (C d).w a) *
          leafLawRepl obs θ C (child a) ℓ * payoff (child a) ℓ =
        ∑ a, (if PredictorAt obs d child then (θ d).w a else (C d).w a) *
          valueRepl obs θ C (child a)
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← value_replacePred_eq_valueRepl θ C (child a), value_replacePred, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring

open Classical in
/-- **`usePred` is the expected number of predictor `d`-nodes on a run of `B_θ`**:
`∑_ℓ μ_{B_θ,C}(ℓ) · #pred_d(ℓ)`.
Source: `grounding.md` GR-4 (`𝔼_{μ_{B_θ,C}}[#pred_d]`)
Kind: L -/
theorem usePred_eq_expectation (θ C : Proc ι acts K) (d : ι) :
    (B : Tree Ω ι acts K) →
      usePred obs θ C d B = ∑ ℓ, leafLawRepl obs θ C B ℓ * (predCount obs d B ℓ : K)
  | leaf ω r => by
      show (0 : K) = ∑ _ : Unit, 1 * ((0 : ℕ) : K)
      simp
  | chance n β child => by
      rw [sum_leaves_chance]
      show ∑ i, β.w i * usePred obs θ C d (child i) =
        ∑ i, ∑ ℓ, β.w i * leafLawRepl obs θ C (child i) ℓ * (predCount obs d (child i) ℓ : K)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [usePred_eq_expectation θ C d (child i), Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  | decision d' child => by
      rw [sum_leaves_decision]
      show (if PredictorAt obs d' child then
          (if d' = d then 1 else 0) + ∑ a, (θ d').w a * usePred obs θ C d (child a)
        else ∑ a, (C d').w a * usePred obs θ C d (child a)) =
        ∑ a, ∑ ℓ, (if PredictorAt obs d' child then (θ d').w a else (C d').w a) *
          leafLawRepl obs θ C (child a) ℓ *
          (((if PredictorAt obs d' child then (if d' = d then 1 else 0) else 0) +
            predCount obs d (child a) ℓ : ℕ) : K)
      by_cases h : PredictorAt obs d' child
      · simp only [if_pos h]
        have hsum : ∀ a, ∑ ℓ, (θ d').w a * leafLawRepl obs θ C (child a) ℓ *
            (((if d' = d then 1 else 0) + predCount obs d (child a) ℓ : ℕ) : K) =
            (θ d').w a * (if d' = d then 1 else 0) + (θ d').w a * usePred obs θ C d (child a) := by
          intro a
          have e : ∀ ℓ, (θ d').w a * leafLawRepl obs θ C (child a) ℓ *
              (((if d' = d then 1 else 0) + predCount obs d (child a) ℓ : ℕ) : K) =
              (θ d').w a * (if d' = d then 1 else 0) * leafLawRepl obs θ C (child a) ℓ +
              (θ d').w a * (leafLawRepl obs θ C (child a) ℓ * (predCount obs d (child a) ℓ : K)) := by
            intro ℓ; push_cast; split_ifs <;> ring
          simp_rw [e]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, leafLawRepl_sum_one,
            mul_one, usePred_eq_expectation θ C d (child a)]
        simp_rw [hsum]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, (θ d').sum_one, one_mul]
      · simp only [if_neg h, Nat.zero_add]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [usePred_eq_expectation θ C d (child a), Finset.mul_sum]
        exact Finset.sum_congr rfl fun ℓ _ => by ring

open Classical in
/-- `valueRepl` lies between the payoff bounds (a convex combination of payoffs).
Source: none: infrastructure
Kind: L -/
theorem valueRepl_bounds (θ C : Proc ι acts K) (m M : K) :
    (B : Tree Ω ι acts K) → (∀ ℓ, m ≤ payoff B ℓ) → (∀ ℓ, payoff B ℓ ≤ M) →
      m ≤ valueRepl obs θ C B ∧ valueRepl obs θ C B ≤ M
  | leaf ω r, hlo, hhi => ⟨hlo (), hhi ()⟩
  | chance n β child, hlo, hhi => by
      show m ≤ ∑ i, β.w i * valueRepl obs θ C (child i) ∧
        ∑ i, β.w i * valueRepl obs θ C (child i) ≤ M
      exact convex_bounds β _ m M
        (fun i => (valueRepl_bounds θ C m M (child i) (fun ℓ => hlo ⟨i, ℓ⟩) (fun ℓ => hhi ⟨i, ℓ⟩)).1)
        (fun i => (valueRepl_bounds θ C m M (child i) (fun ℓ => hlo ⟨i, ℓ⟩) (fun ℓ => hhi ⟨i, ℓ⟩)).2)
  | decision d child, hlo, hhi => by
      show m ≤ ∑ a, (if PredictorAt obs d child then (θ d).w a else (C d).w a) *
          valueRepl obs θ C (child a) ∧
        ∑ a, (if PredictorAt obs d child then (θ d).w a else (C d).w a) *
          valueRepl obs θ C (child a) ≤ M
      have h1 := fun a => (valueRepl_bounds θ C m M (child a) (fun ℓ => hlo ⟨a, ℓ⟩)
        (fun ℓ => hhi ⟨a, ℓ⟩)).1
      have h2 := fun a => (valueRepl_bounds θ C m M (child a) (fun ℓ => hlo ⟨a, ℓ⟩)
        (fun ℓ => hhi ⟨a, ℓ⟩)).2
      by_cases h : PredictorAt obs d child
      · simp only [if_pos h]; exact convex_bounds (θ d) _ m M h1 h2
      · simp only [if_neg h]; exact convex_bounds (C d) _ m M h1 h2

open Classical in
/-- **GR-4, verdict substitution (recursion form)**: for labels `θ, θ'` differing only at `d` and
payoffs in `[m, M]`, `|V_{B_θ}(C) − V_{B_θ'}(C)| ≤ (M − m) · TV(θ_d, θ'_d) · usePred θ C d B`, by
structural induction with the per-node bound `abs_sum_sub_mul_le_tv` at predictor `d`-nodes.
Source: `grounding.md` GR-4
Kind: P -/
theorem valueRepl_sub_le (θ θ' C : Proc ι acts K) (d : ι) (hdiff : ∀ d', d' ≠ d → θ d' = θ' d')
    (m M : K) :
    (B : Tree Ω ι acts K) → (∀ ℓ, m ≤ payoff B ℓ) → (∀ ℓ, payoff B ℓ ≤ M) →
      |valueRepl obs θ C B - valueRepl obs θ' C B| ≤ (M - m) * tv (θ d) (θ' d) * usePred obs θ C d B
  | leaf ω r, _, _ => by
      show |r - r| ≤ (M - m) * tv (θ d) (θ' d) * 0
      simp
  | chance n β child, hlo, hhi => by
      show |∑ i, β.w i * valueRepl obs θ C (child i) - ∑ i, β.w i * valueRepl obs θ' C (child i)| ≤
        (M - m) * tv (θ d) (θ' d) * ∑ i, β.w i * usePred obs θ C d (child i)
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      simp_rw [← mul_sub]
      refine (abs_weighted_sum_le β.w β.nonneg _ (fun i => (M - m) * tv (θ d) (θ' d) *
        usePred obs θ C d (child i)) fun i => valueRepl_sub_le θ θ' C d hdiff m M (child i)
        (fun ℓ => hlo ⟨i, ℓ⟩) (fun ℓ => hhi ⟨i, ℓ⟩)).trans ?_
      exact le_of_eq (Finset.sum_congr rfl fun i _ => by ring)
  | decision d' child, hlo, hhi => by
      have ih := fun a => valueRepl_sub_le θ θ' C d hdiff m M (child a) (fun ℓ => hlo ⟨a, ℓ⟩)
        (fun ℓ => hhi ⟨a, ℓ⟩)
      show |∑ a, (if PredictorAt obs d' child then (θ d').w a else (C d').w a) *
            valueRepl obs θ C (child a) -
          ∑ a, (if PredictorAt obs d' child then (θ' d').w a else (C d').w a) *
            valueRepl obs θ' C (child a)| ≤
        (M - m) * tv (θ d) (θ' d) *
          (if PredictorAt obs d' child then
            (if d' = d then 1 else 0) + ∑ a, (θ d').w a * usePred obs θ C d (child a)
          else ∑ a, (C d').w a * usePred obs θ C d (child a))
      by_cases h : PredictorAt obs d' child
      · simp only [if_pos h]
        by_cases hd : d' = d
        · subst hd
          simp only [if_true]
          -- split the difference into the recursive part and the label part
          have hsplit : ∑ a, (θ d').w a * valueRepl obs θ C (child a) -
              ∑ a, (θ' d').w a * valueRepl obs θ' C (child a) =
              ∑ a, (θ d').w a * (valueRepl obs θ C (child a) - valueRepl obs θ' C (child a)) +
              ∑ a, ((θ d').w a - (θ' d').w a) * valueRepl obs θ' C (child a) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun a _ => by ring
          rw [hsplit]
          have hb := fun a => valueRepl_bounds obs θ' C m M (child a) (fun ℓ => hlo ⟨a, ℓ⟩)
            (fun ℓ => hhi ⟨a, ℓ⟩)
          have hA : |∑ a, (θ d').w a * (valueRepl obs θ C (child a) - valueRepl obs θ' C (child a))|
              ≤ (M - m) * tv (θ d') (θ' d') * ∑ a, (θ d').w a * usePred obs θ C d' (child a) := by
            refine (abs_weighted_sum_le (θ d').w (θ d').nonneg _
              (fun a => (M - m) * tv (θ d') (θ' d') * usePred obs θ C d' (child a)) ih).trans ?_
            rw [Finset.mul_sum]
            exact le_of_eq (Finset.sum_congr rfl fun a _ => by ring)
          have hB : |∑ a, ((θ d').w a - (θ' d').w a) * valueRepl obs θ' C (child a)| ≤
              (M - m) * tv (θ d') (θ' d') :=
            abs_sum_sub_mul_le_tv (θ d') (θ' d') _ m M (fun a => (hb a).1) (fun a => (hb a).2)
          calc |∑ a, (θ d').w a * (valueRepl obs θ C (child a) - valueRepl obs θ' C (child a)) +
                ∑ a, ((θ d').w a - (θ' d').w a) * valueRepl obs θ' C (child a)|
              ≤ |∑ a, (θ d').w a * (valueRepl obs θ C (child a) - valueRepl obs θ' C (child a))| +
                |∑ a, ((θ d').w a - (θ' d').w a) * valueRepl obs θ' C (child a)| := abs_add_le _ _
            _ ≤ (M - m) * tv (θ d') (θ' d') * ∑ a, (θ d').w a * usePred obs θ C d' (child a) +
                (M - m) * tv (θ d') (θ' d') := add_le_add hA hB
            _ = (M - m) * tv (θ d') (θ' d') *
                (1 + ∑ a, (θ d').w a * usePred obs θ C d' (child a)) := by ring
        · simp only [if_neg hd, zero_add]
          rw [hdiff d' hd]
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          simp_rw [← mul_sub]
          refine (abs_weighted_sum_le (θ' d').w (θ' d').nonneg _ (fun a => (M - m) * tv (θ d) (θ' d) *
            usePred obs θ C d (child a)) ih).trans ?_
          exact le_of_eq (Finset.sum_congr rfl fun a _ => by ring)
      · simp only [if_neg h]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        simp_rw [← mul_sub]
        refine (abs_weighted_sum_le (C d').w (C d').nonneg _ (fun a => (M - m) * tv (θ d) (θ' d) *
          usePred obs θ C d (child a)) ih).trans ?_
        exact le_of_eq (Finset.sum_congr rfl fun a _ => by ring)

/-- **GR-4, verdict substitution**: for labels `θ, θ'` that differ only at `d`, with every payoff
of `B` in `[m, M]` (so `R := M − m` bounds the payoff range; with `m, M` the actual minimum and
maximum it is GR-4's `R = max r − min r`),
`|V_{B_θ}(C) − V_{B_θ'}(C)| ≤ R · TV(θ_d, θ'_d) · 𝔼_{μ_{B_θ,C}}[#pred_d]`.
One verdict error at `d` costs at most the payoff range times the error times the use rate. Holds
on every tree (GR-D2's routing-freeness is for the meaning of `B_θ`, not for the bound), under
independent redraws (Definition 6).
Source: `grounding.md` GR-4 ("verdict substitution"); mandate T14(b)
Kind: P
Fidelity: exact (payoff range given by bounds; the exact range is the instance `m = min r`,
`M = max r`)
Hyps: (a) `θ, θ'` agree off `d`; (a) payoff bounds -/
theorem value_replacePred_sub_le (θ θ' C : Proc ι acts K) (d : ι)
    (hdiff : ∀ d', d' ≠ d → θ d' = θ' d') (m M : K) (B : Tree Ω ι acts K)
    (hlo : ∀ ℓ, m ≤ payoff B ℓ) (hhi : ∀ ℓ, payoff B ℓ ≤ M) :
    |value C (replacePred obs θ B) - value C (replacePred obs θ' B)| ≤
      (M - m) * tv (θ d) (θ' d) * usePred obs θ C d B := by
  rw [value_replacePred_eq_valueRepl, value_replacePred_eq_valueRepl]
  exact valueRepl_sub_le obs θ θ' C d hdiff m M B hlo hhi

end gr4

end Cleanroom.Decision.DpFirstpersonSc
