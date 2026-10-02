import Cleanroom.Decision.DpDevicesCatalog.TableMugging
import Cleanroom.Decision.DpCalibration.Witnesses

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T11(b)–(c): experimental identifiability and the assumption table

* (b) **Q14 experimental identifiability** (dp-sl-077): `ExpIdentifiable obs actEv C B d` — at
  every act event realizable within `O_d`, the tremble-limit conditional act value (D4's
  evaluator) equals Theorem 1's forcing value (D3⁰'s evaluator, unnormalised; the two
  normalisations agree when `𝔼[#_d] = 1`, as on both witnesses). Inhabited on `coinQuery`
  (`N−`: every payoff is `0`), refuted on the mugging (`−x ≠ (y − x)/2`: the tremble-limit
  conditional refuses, the forcing evaluator pays — T8's D4 vs D3⁰ cells).
* (c) **A1–A10** (`sequence-map.md:292–307`), one pointer per row (the catalogue is the
  value): A1 exploration = the two devices named apart (`FixedEpsTie` vs `FloorRatifiable`,
  `Miniature.lean`; procedure-side D3 vs problem-side D2); A2 ratifiability of mixed
  strategies = `StrictOCAt` on labels (Remark 5.1); A3 implementability = a *type* in v2:
  `mass_edge` / `node_mass_edge` (dp-core-tree `NodeSums`/`Screening`: the draw at a node is
  `C(d)` whatever the path); A4 Bayes-net compatibility = one chassis, two evaluators
  (Remark 1.1; no theorem); A5 nonzero action probabilities = `APlusNonempty` below
  (Definition 12 / `A_d^+`); A6 knowledge of own policy = `SelfTransparent` (App. B item 2);
  A7 fairness / same problem = `IsCalibrated κ` (F2), `MakesInconsistent` (Definition 16);
  A8 the Law of Logical Causality = Remark 3.11 / Q6, declined (no theorem); A9 decision as
  state formation = Remark 5.3, recorded; A10 grafted bets = a stipulation (no theorem).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

section vocabulary

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)]

/-- **A5, nonzero action probabilities**: some act is subjectively possible at `d` — the domain
condition of Definition 17/18 and D2/D4's escape clauses.
Source: `sequence-map.md` A5 ("Nonzero action probabilities … Definition 12 / `A_d^+`")
Kind: D -/
abbrev APlusNonempty (s : ι → State Ω ℚ) (actEv : (d : ι) → acts d → Finset Ω) (d : ι) : Prop :=
  (APlus s actEv d).Nonempty

/-- **Q14, experimental identifiability at `d`**: for every act `a` whose event within `O_d` is
tremble-realizable, the tremble-limit conditional act value (D4's evaluator, `limitVal`) equals
Theorem 1's forcing value (`siaSum`, unnormalised — equal to the normalised value when
`𝔼[#_d] = 1`, which holds on both witnesses below).
Source: `sl-workflow` Q14 (dp-sl-077: "experimental identifiability"); mandate T11(b)
Kind: D
Fidelity: variant: forcing value unnormalised (`siaSum`), limit value algebraic (`limitVal`) -/
def ExpIdentifiable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) : Prop :=
  ∀ a, nuPoly C B (actEv d a ∩ obs d) ≠ 0 →
    limitVal C B (actEv d a ∩ obs d) = siaSum C B d a

end vocabulary

/-- Theorem 1's functional on `coinQuery` is `0` (every payoff is `0`).
Source: none: infrastructure. Kind: L -/
theorem coinQuery_siaSum (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    siaSum C coinQuery () a = 0 := by
  simp [coinQuery, siaSum_decision, value_leaf]

/-- **`coinQuery` is experimentally identifiable** for every procedure: both evaluators are `0`
(every payoff is `0`) — a degenerate witness.
Source: mandate T11(b) ("inhabit on `coinQuery`")
Kind: N−
Fidelity: exact -/
theorem coinQuery_expIdentifiable (C : Proc Unit (fun _ => Act2) ℚ) :
    ExpIdentifiable cqObs cqActEv C coinQuery () := by
  intro a hne
  rw [coinQuery_siaSum]
  apply limitVal_of_const _ _ _ 0 _ hne
  intro ℓ _
  unfold coinQuery at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp

/-- **The mugging is not experimentally identifiable** (`0 < x < y`, any label): at `pay` the
tremble-limit conditional is `−x` (refuse) while the forcing value is `(y − x)/2` (pay).
Source: mandate T11(b) ("refute on `mug1`: the tremble-limit conditional refuses, the forcing
evaluator pays: T8's D4 vs D3⁰ cells")
Kind: N+
Fidelity: exact -/
theorem mug1_not_expIdentifiable (x y : ℚ) (hx : 0 < x) (hxy : x < y)
    (C : Proc Unit (fun _ => Act2) ℚ) : ¬ ExpIdentifiable mugObs mugActEv C (mug1 x y) () := by
  intro h
  have := h .a (mug1_nuPoly_actObs_ne_zero x y C .a)
  rw [(mug1_limitVal x y C).1, (mug1_siaSum x y C).1] at this
  linarith

end Cleanroom.Decision.DpDevicesCatalog
