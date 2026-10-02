import Cleanroom.Decision.DpCartesianFrames.Reloc

/-!
# The kernel of the diagonal: what `FrIdent`'s columns are (T7(c), repair round 3)

Package `dp-cartesian-frames`, file 20 (repair round 3; audit r3 fidelity 1 / adversarial N1).

ZO-5(b)/CFF-2(b) say the identified relocated frame and `Fr B` are "equal as matrices under
the row bijection and the column identity iff every chance node of `B` lies on a root-path
that answers each relocated point consistently" (`E' = E_B`), and ZO-5(c) that this is
automatic when no `U`-fiber is nested. The adversarial auditor of round 3 proposed to render
the `core` "if" half as `(∀ d ∈ U, ¬ Nested B d) → Function.Injective (diag U B)`. This file
settles what the package's `diag` actually identifies, and shows that proposal is **false**:

* **`diag_eq_iff`**: `diag U B ε = diag U B ε' ↔ ∀ π, runLeaf π B ε = runLeaf π B ε'` — two
  original profiles have the same diagonal column exactly when they give the same leaf under
  every pure policy. (⟹) is `diagProfile_spec` read along `liftFun`; (⟸) is that
  `diagProfile` is `Classical.choose` of a proposition that mentions `ε` only through its
  runs, so equal runs give the same chosen profile (`choose_congr`). **For every `U`**, nested
  or not: the kernel of `diag` does not see `U` at all.
* **`not_injective_diag_twoCoins`**: on the chance-only tree "coin; tails → coin; heads →
  leaf" with `U = ∅` (so no point is nested, or even present), `diag` is not injective — the
  inner coin's coordinate is dead on the heads column. So the kernel of `diag` is the kernel
  of `Fr B`'s own column map `ε ↦ (π ↦ runLeaf π B ε)`, and the source's `E' ≠ E_B` (a chance
  node reachable only through inconsistent `U`-answers — a *dead* coordinate for `Fr B` as
  well) is invisible to `FrIdent`: the package's `FrIdent U B` has columns
  `ChanceProfile B / ~` for every `U`.

Consequence for ZO-5(b)/(c): the nested/non-nested distinction is a statement about the
*structural* diagonal (one coordinate per surviving original chance node, copies read
unconditionally — CFF-A's `Fr_κ`), which this package does not define; `FrIdent` is a
variant that quotients the dead coordinates away. The ledger carries ZO-5(b)/(c) as
`flagged` with this reason, and `Diag.lean` is the evidence. Findings F20.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

/-- `Classical.choose` of two existence proofs over equal predicates is the same value.
Source: none: infrastructure
Kind: L -/
theorem choose_congr {α : Sort*} {p q : α → Prop} (hp : ∃ x, p x) (hq : ∃ x, q x)
    (h : p = q) : Classical.choose hp = Classical.choose hq := by
  subst h; rfl

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

section kernel

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (U : Finset ι)

omit [∀ d, DecidableEq (acts d)] in
/-- **The kernel of the diagonal**: two profiles of `B` have the same diagonal column of the
relocated tree iff they give the same leaf under every pure policy of `B` — for every `U`,
nested fibers or not. (⟹): read `diagProfile_spec` along `liftFun U π`, whose `toPolicy` is
`π`. (⟸): `diagProfile U σ B ε` is `Classical.choose` of a proposition in which `ε` occurs
only as `runLeaf (toPolicy U σ ρ) B ε`, so equal runs give the same chosen profile.
Source: zoo ZO-5(b) (line 70: "the column index sets differ"); cf-frontier CFF-2(b) (line
62); audit r3 (fidelity 1, adversarial N1); mandate T7(c)
Kind: P
Fidelity: variant: the statement is about the package's choice-based `diag`, whose kernel is
`U`-independent — see the file header
Hyps: none -/
theorem diag_eq_iff (B : Tree Ω ι acts K) (ε ε' : ChanceProfile B) :
    diag U B ε = diag U B ε' ↔ ∀ π : (d : ι) → acts d, runLeaf π B ε = runLeaf π B ε' := by
  constructor
  · intro h π
    have hσ : diagProfile U (liftFun U π (.inr ())) B ε =
        diagProfile U (liftFun U π (.inr ())) B ε' :=
      congrFun h (liftFun U π (.inr ()))
    have h1 := diagProfile_spec U (liftFun U π (.inr ())) B ε (liftFun U π)
    have h2 := diagProfile_spec U (liftFun U π (.inr ())) B ε' (liftFun U π)
    rw [toPolicy_liftFun] at h1 h2
    rw [← h1, ← h2, hσ]
  · intro h
    funext σ
    unfold diag diagProfile
    apply choose_congr
    funext ε''
    simp only [h]

end kernel

/-! ### The refutation: `diag` is not injective on a chance-only tree with `U = ∅` -/

/-- The inner coin of the two-coin tree.
Source: audit r3 (adversarial N1), refutation witness
Kind: D -/
def twoCoinsInner : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair ![.leaf true 0, .leaf false 0]

/-- **The two-coin tree**: a fair coin; tails → a second fair coin over two leaves; heads → a
leaf. No decision node at all, so `∀ d ∈ U, ¬ Nested B d` holds for every `U` — and for
`U = ∅` the relocation is the identity up to the trivial root.
Source: audit r3 (adversarial N1), refutation witness
Kind: D -/
def twoCoins : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair ![twoCoinsInner, .leaf true 0]

/-- A heads column of the two-coin tree whose (unread) inner coin is `j`.
Source: none: infrastructure
Kind: D -/
noncomputable def twoCoinsε (j : Fin 2) : ChanceProfile twoCoins :=
  (1, Fin.cons (α := fun i : Fin 2 =>
      ChanceProfile (![twoCoinsInner, (Tree.leaf true 0 : Tree Bool Unit (fun _ => Act2) ℚ)] i))
    ((j, fun _ => Classical.arbitrary _) : ChanceProfile twoCoinsInner)
    (fun _ => Classical.arbitrary _))

/-- Every run of the two-coin tree on a heads column lands on the heads leaf, whatever the
inner coin.
Source: none: infrastructure
Kind: L -/
theorem runLeaf_twoCoinsε (π : Unit → Act2) (j : Fin 2) :
    runLeaf π twoCoins (twoCoinsε j) = ⟨1, ()⟩ := rfl

/-- The two heads columns differ as profiles (their inner coins differ).
Source: none: infrastructure
Kind: L -/
theorem twoCoinsε_ne : twoCoinsε 0 ≠ twoCoinsε 1 := by
  intro h
  have h' := congrArg (fun ε : ChanceProfile twoCoins => (ε.2 0).1) h
  exact absurd h' (by decide)

/-- **The auditor's proposed statement is false**: `(∀ d ∈ U, ¬ Nested B d) →
Function.Injective (diag U B)` fails on the two-coin tree with `U = ∅` (its hypothesis holds
vacuously — the tree has no decision node). The two heads columns `twoCoinsε 0`,
`twoCoinsε 1` give the same leaf under every policy, hence the same diagonal column
(`diag_eq_iff`), while they differ as profiles. The coordinate `diag` loses here is the
inner coin on the heads branch — dead for `Fr twoCoins` too — not a coordinate under an
inconsistently answered relocated point.
Source: audit r3 (adversarial N1); zoo ZO-5(c) (line 71)
Kind: N+
Fidelity: exact (refutation of the proposed rendering; the source's claim is about the
structural diagonal, which this does not touch) -/
theorem not_injective_diag_twoCoins :
    (∀ d ∈ (∅ : Finset Unit), ¬ Nested twoCoins d) ∧
    ¬ Function.Injective (diag (∅ : Finset Unit) twoCoins) := by
  refine ⟨fun d hd => absurd hd (Finset.notMem_empty d), fun hinj => ?_⟩
  have h : diag (∅ : Finset Unit) twoCoins (twoCoinsε 0) = diag ∅ twoCoins (twoCoinsε 1) :=
    (diag_eq_iff _ _ _ _).2 fun π => by rw [runLeaf_twoCoinsε, runLeaf_twoCoinsε]
  exact twoCoinsε_ne (hinj h)

end Cleanroom.Decision.DpCartesianFrames
