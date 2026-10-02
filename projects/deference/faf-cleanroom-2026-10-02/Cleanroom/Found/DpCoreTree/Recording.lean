import Cleanroom.Found.DpCoreTree.Nodes

/-!
# Definition 7: veridicality, coverage, recording — and its quantifier forms

Definitions of record for [[decision-problems-v2]] §3.1 Definition 7, stated per leaf: every
"`μ_{B,C}`-a.s." clause is *for every leaf `ℓ` with `0 < μ_{B,C}(ℓ)`*, never "not identically
zero on symbolic weights" (the cf toolkit's reading, flagged in dp-cf-012; see the package
findings). Also the three quantifier forms of recording that come apart (for `C`; for every
point-deviation of `C`; for every procedure — `sl-synthesis.md` line 20), F3′ veridical
act-recording (`faithful.md`), `H*` (Proposition 3's hypothesis), `DecidedAt`, pre-query events
(Lemma 3′) and root events (`clean-source-and-policy-responsiveness.md` §3).

The observation `O_d` and the action events `a ∈ A_d ⊆ 𝓔` of Definition 3 are supplied as
functions `obs : ι → Finset Ω` and `actEv : (d : ι) → acts d → Finset Ω`; the disjointness /
non-emptiness constraints of Definition 3 are hypotheses of the theorems that need them.
-/

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

namespace Tree

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- The instance `(q, ℓ)` is *observation-veridical*: the leaf-world satisfies `O_{d_q}`.
Source: [[decision-problems-v2]] §3.1 Definition 7
Kind: D -/
def ObsVeridicalAt (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves) : Prop :=
  world B ℓ ∈ obs (pt B q)

/-- The instance `(q, ℓ)` is *action-veridical*: the leaf-world satisfies the action drawn at
`q` on the path to `ℓ`.
Source: [[decision-problems-v2]] §3.1 Definition 7
Kind: D -/
def ActVeridicalAt (B : Tree Ω ι acts K) (q : B.DecNode) (ℓ : B.Leaves) : Prop :=
  ∀ a, edgeOf B q ℓ = some a → world B ℓ ∈ actEv (pt B q) a

/-- The node `q` is *subtree-veridical*: every leaf below `q` has its world in `O_{d_q}`.
Source: [[decision-problems-v2]] §3.1 Definition 7
Kind: D -/
def SubtreeVeridical (B : Tree Ω ι acts K) (q : B.DecNode) : Prop :=
  ∀ ℓ ∈ leavesBelow B q, world B ℓ ∈ obs (pt B q)

/-- The node `q` is *node-action-veridical* (F3′): for every `a`, every leaf below `q`'s
`a`-edge has its world in the action event `a`.
Source: `cf-workflow/phase2-notes/repair/faithful.md` F3′ (via dp-cf-2-001)
Kind: D -/
def NodeActionVeridical (B : Tree Ω ι acts K) (q : B.DecNode) : Prop :=
  ∀ ℓ a, edgeOf B q ℓ = some a → world B ℓ ∈ actEv (pt B q) a

variable [DecidableEq ι]

/-- **Coverage**: `B` covers `d` for `C` if every positive-mass run whose leaf-world satisfies
`O_d` passes through a `d`-node.
Source: [[decision-problems-v2]] §3.1 Definition 7 ("covers")
Kind: D
Fidelity: exact ("a.s." rendered as "every leaf of positive mass") -/
def Covers (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → 0 < count d B ℓ

/-- **Recording (Definition 7)**: `B` records at `d` for `C` if for every positive-mass run
whose leaf-world satisfies `O_d`: (1) the path passes exactly one `d`-node; (2) that node is
subtree-veridical; (3) its instance is action-veridical; (4) the leaf-world satisfies an action
event of `d` only for the action drawn there.
Source: [[decision-problems-v2]] §3.1 Definition 7 ("records at `d`")
Kind: D
Fidelity: exact ("a.s." rendered as "every leaf of positive mass"; "that node" rendered as
"every `d`-node on the path", which under clause (1) is the unique one) -/
def RecordsFor (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d →
    count d B ℓ = 1 ∧
    ∀ q : B.DecNode, pt B q = d → ∀ a, edgeOf B q ℓ = some a →
      SubtreeVeridical obs B q ∧ world B ℓ ∈ actEv (pt B q) a ∧
      ∀ a', world B ℓ ∈ actEv (pt B q) a' → a' = a

/-- Recording for `C` and every point-deviation `C[d ↦ m]` of it.
Source: `sl-workflow/notes/final/sl-synthesis.md` line 20 ("for every point-deviation
`C[d ↦ m]`"); line 121 (C2-B′)
Kind: D -/
def RecordsForDeviations (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∀ m, RecordsFor obs actEv (C.deviate d m) B d

/-- Recording for every procedure.
Source: `sl-synthesis.md` line 20 ("for every procedure")
Kind: D -/
def RecordsForAll (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∀ C : Proc ι acts K, RecordsFor obs actEv C B d

/-- **F3′, veridical act-recording**: every node-action-veridical `d`-node is subtree-veridical,
and every positive-mass `O_d`-run passes exactly one node-action-veridical `d`-node (other
`d`-nodes — upstream simulations — are allowed).
Source: `faithful.md` F3′ as restated in dp-cf-2-001
Kind: D -/
def ActRecording (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  (∀ q, pt B q = d → NodeActionVeridical actEv B q → SubtreeVeridical obs B q) ∧
  ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d →
    ∃! q, q ∈ dNodesOn B d ℓ ∧ NodeActionVeridical actEv B q

/-- **`H*`**: Definition 7 recording for `C`, and every positive-mass run through a `d`-node
has its leaf-world in `O_d` (so `occ(d)` and the `O_d`-runs coincide a.s.).
Source: `sl-synthesis.md` line 20 (`H*`); [[decision-problems-v2]] Remark 3.4 (the two
inclusions)
Kind: D -/
def HStar (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  RecordsFor obs actEv C B d ∧
  ∀ ℓ, 0 < leafLaw C B ℓ → 0 < count d B ℓ → world B ℓ ∈ obs d

/-- The event `X` is *decided at* `q`: all leaves below `q` agree on whether their world is in
`X`.
Source: `sl-defensible-claims.md` S4 ("pre-query event"); mandate T6
Kind: D -/
def DecidedAt (B : Tree Ω ι acts K) (q : B.DecNode) (X : Finset Ω) : Prop :=
  (∀ ℓ ∈ leavesBelow B q, world B ℓ ∈ X) ∨ (∀ ℓ ∈ leavesBelow B q, world B ℓ ∉ X)

/-- `X` is *pre-query* for `d` (under `C`): every `d`-node met on a positive-mass `O_d`-run
decides `X`.
Source: `sl-defensible-claims.md` S4; mandate T6 (`PreQuery`)
Kind: D -/
def PreQuery (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) : Prop :=
  ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d →
    ∀ q, pt B q = d → (edgeOf B q ℓ).isSome → DecidedAt B q X

/-- `X` is a *root event*: it is decided at every topmost decision node (leaves reached by
chance alone are unconstrained).
Source: `directions/clean-source-and-policy-responsiveness.md` §3 (root events; "no `d`-node
is upstream of it")
Kind: D -/
def RootEvent (B : Tree Ω ι acts K) (X : Finset Ω) : Prop :=
  ∀ q, IsTopmost B q → DecidedAt B q X

end Tree

end Cleanroom.Found.DpCoreTree
