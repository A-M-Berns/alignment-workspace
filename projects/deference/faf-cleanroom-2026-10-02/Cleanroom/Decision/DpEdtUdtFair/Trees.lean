import Cleanroom.Decision.DpLocalOpt.Trees

/-!
# New catalogue trees for `dp-edt-udt-fair` (mandate representation decision 7)

Over `ℚ`, worlds record the drawn act wherever recording is claimed:

* `dupPay ra rb` — a fair coin over two literally equal copies of `decision d [a ↦ ra, b ↦ rb]`,
  worlds `Act2` blind to the coin: the two-member-fiber inhabitant of `𝔉`
  (`dp-fairness-reloc`'s `dup` has payoffs `0`).
* `cornerTree` — GR-9's example (2) with act-recording worlds `Bool × Act2`: one point on two
  evented branches, left `a → ½/½ → 1, 3`, right `a → 2`; `b → 0` both. Value-fair, not
  strongly fair: GR-11's corner witness.
* `mislabelled` (ZO-4 (d1)) and `doppel` (ZO-4 (d2)) — strongly fair, veridical, not recording
  (action-veridicality; coverage / only-via-the-draw).
* `tieTree3` — CA-4′'s tie tree `T₃` on `Pt3` with worlds `(act₁, act₂)`.
* `revTree D t` — GR-10's reviewer tree: a fair coin; a live `d`-node `a → 0, b → −t` with
  `O_d`-worlds; a predictor `d`-node `a → −D, b → D` with worlds outside `O_d`.
* `stagObs`/`stagActEv` — observations `⊤` and act-recording events for `dp-local-opt`'s
  `twoStag` (worlds `MiniW = Act2 × Act2`).

Each tree ships its leaf enumeration (`*_sum`) and its value closed form (`*_value`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpLocalOpt

/-! ### `dupPay`: a two-member fiber in `𝔉` -/

/-- One copy: `decision d [a ↦ ra, b ↦ rb]`, world = the drawn act.
Source: mandate representation decision 7 (`dupPay`)
Kind: D -/
def dupNode (ra rb : ℚ) : Tree Act2 Unit (fun _ => Act2) ℚ :=
  .decision () fun x => .leaf x (if x = .a then ra else rb)

/-- **`dupPay ra rb`**: a fair coin over two literally equal copies of `dupNode ra rb`; the
worlds (`Act2`, the drawn act) cannot see the coin. Strongly fair with a two-member fiber; in
`𝔉` with `O_d = ⊤` and act events `{v}` (`dupPay_fairClass`, `FairWitnesses.lean`).
Source: mandate representation decision 7; `adversary-repair.md` Claim B ("multi-instance
… fibers exist only where the algebra is blind to which instance is which")
Kind: D -/
def dupPay (ra rb : ℚ) : Tree Act2 Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun _ => dupNode ra rb

/-- `O_d = ⊤` on `dupPay`. Source: mandate representation decision 7. Kind: D -/
def dupPayObs : Unit → Finset Act2 := fun _ => Finset.univ

/-- Act events `{v}` on `dupPay` (the world is the act). Source: mandate representation
decision 7. Kind: D -/
def dupPayActEv : Unit → Act2 → Finset Act2 := fun _ v => {v}

/-- A sum over the four leaves of `dupPay`. Source: none: infrastructure. Kind: L -/
theorem dupPay_sum {M : Type} [AddCommMonoid M] (ra rb : ℚ) (f : (dupPay ra rb).Leaves → M) :
    ∑ ℓ, f ℓ = (f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩) + (f ⟨1, .a, ()⟩ + f ⟨1, .b, ()⟩) := by
  unfold dupPay dupNode at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `V_{dupPay ra rb}(q) = q ra + (1 − q) rb`.
Source: mandate representation decision 7
Kind: P -/
theorem dupPay_value (ra rb q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (dupPay ra rb) = q * ra + (1 - q) * rb := by
  simp only [dupPay, dupNode, value_chance, value_decision, value_leaf, Fin.sum_univ_two,
    Act2.sum_univ, procQ, FinDistr.act2_a, FinDistr.act2_b, FinDistr.fair, FinDistr.coin]
  simp; ring

/-! ### `cornerTree`: GR-9 (2) with act-recording worlds -/

/-- Corner-tree worlds: `(branch, act)`.
Source: `grounding.md` GR-9 example (2); mandate representation decision 7
Kind: D -/
abbrev CornerW : Type := Bool × Act2

/-- GR-9 (2), left member: `a → ½/½ → 1, 3`; `b → 0`; worlds `(true, act)`.
Source: `grounding.md` GR-9 example (2)
Kind: D -/
def cornerL : Tree CornerW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .chance 2 FinDistr.fair fun i => .leaf (true, .a) (if i = 0 then 1 else 3)
    | .b => .leaf (true, .b) 0

/-- GR-9 (2), right member: `a → 2`; `b → 0`; worlds `(false, act)`.
Source: `grounding.md` GR-9 example (2)
Kind: D -/
def cornerR : Tree CornerW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf (false, .a) 2
    | .b => .leaf (false, .b) 0

/-- **`cornerTree`**: the two members on the two branches of a fair coin, evented (the worlds
carry the branch) and act-recording.
Source: `grounding.md` GR-9 example (2), GR-11 ("example (2) lies in the corner and outside
phase 1's class"); mandate representation decision 7
Kind: D -/
def cornerTree : Tree CornerW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases cornerL (fun _ => cornerR) i

/-- `O_d = ⊤` on `cornerTree`. Source: `grounding.md` GR-9 (2) ("`O_d = ⊤`"). Kind: D -/
def cornerObs : Unit → Finset CornerW := fun _ => Finset.univ

/-- Act events `{act = v}` on `cornerTree`. Source: mandate representation decision 7. Kind: D -/
def cornerActEv : Unit → Act2 → Finset CornerW := fun _ v => Finset.univ.filter fun w => w.2 = v

/-- A sum over the five leaves of `cornerTree`. Source: none: infrastructure. Kind: L -/
theorem cornerTree_sum {M : Type} [AddCommMonoid M] (f : cornerTree.Leaves → M) :
    ∑ ℓ, f ℓ = (f ⟨0, .a, 0, ()⟩ + f ⟨0, .a, 1, ()⟩ + f ⟨0, .b, ()⟩) +
      (f ⟨1, .a, ()⟩ + f ⟨1, .b, ()⟩) := by
  unfold cornerTree at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : cornerL.Leaves, f ⟨0, ℓ⟩) + (∑ ℓ : cornerR.Leaves, f ⟨1, ℓ⟩) = _
  unfold cornerL cornerR
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_chance, Fin.sum_univ_two,
    sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `V_{cornerTree}(q) = 2q`. Source: `grounding.md` GR-11 ("the optimum `V = 2`"). Kind: P -/
theorem cornerTree_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) cornerTree = 2 * q := by
  have hL : value (procQ q h0 h1) cornerL = 2 * q := by
    simp only [cornerL, value_decision, value_chance, value_leaf, Fin.sum_univ_two, Act2.sum_univ,
      procQ, FinDistr.act2_a, FinDistr.act2_b, FinDistr.fair, FinDistr.coin]
    simp; norm_num; ring
  have hR : value (procQ q h0 h1) cornerR = 2 * q := by
    simp only [cornerR, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
      FinDistr.act2_b]
    ring
  simp only [cornerTree, value_chance, Fin.sum_univ_two]
  show FinDistr.fair.w 0 * value (procQ q h0 h1) cornerL +
    FinDistr.fair.w 1 * value (procQ q h0 h1) cornerR = 2 * q
  rw [hL, hR]
  simp [FinDistr.fair, FinDistr.coin]; ring

/-! ### `mislabelled` and `doppel` (ZO-4) -/

/-- **`mislabelled`** (ZO-4 (d1)): one node, `O = ⊤`; the `a`-edge lands in the world `act = b`
(`r = 0`), the `b`-edge in `act = a` (`r = 1`). Recording fails by action-veridicality.
Source: `zoo.md` ZO-4 (d1)
Kind: D -/
def mislabelled : Tree Act2 Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .b 0
    | .b => .leaf .a 1

/-- `O = ⊤` for the one-point act-world trees (`mislabelled`, `doppel`). Source: `zoo.md` ZO-4.
Kind: D -/
def actObs : Unit → Finset Act2 := fun _ => Finset.univ

/-- Act events `{v}` for the one-point act-world trees. Source: `zoo.md` ZO-4. Kind: D -/
def actActEv : Unit → Act2 → Finset Act2 := fun _ v => {v}

/-- A sum over the two leaves of `mislabelled`. Source: none: infrastructure. Kind: L -/
theorem mislabelled_sum {M : Type} [AddCommMonoid M] (f : mislabelled.Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, ()⟩ := by
  unfold mislabelled at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `V_{mislabelled}(q) = 1 − q`. Source: `zoo.md` ZO-4 (d1). Kind: P -/
theorem mislabelled_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) mislabelled = 1 - q := by
  simp only [mislabelled, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  ring

/-- The doppelgänger's consulted branch: `d` with `a → (act = a) 0`, `b → (act = b) 1`. The
whole tree (`doppel`) fails recording by coverage and only-via-the-draw.
Source: `zoo.md` ZO-4 (d2)
Kind: D -/
def doppelL : Tree Act2 Unit (fun _ => Act2) ℚ :=
  .decision () fun | .a => .leaf .a 0 | .b => .leaf .b 1

/-- The doppelgänger's unconsulted branch: the leaf `(act = a)`, payoff `10`.
Source: `zoo.md` ZO-4 (d2)
Kind: D -/
def doppelR : Tree Act2 Unit (fun _ => Act2) ℚ := .leaf .a 10

/-- **`doppel`** (ZO-4 (d2)): a fair coin over `doppelL` and `doppelR`.
Source: `zoo.md` ZO-4 (d2)
Kind: D -/
def doppel : Tree Act2 Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases doppelL (fun _ => doppelR) i

/-- A sum over the three leaves of `doppel`. Source: none: infrastructure. Kind: L -/
theorem doppel_sum {M : Type} [AddCommMonoid M] (f : doppel.Leaves → M) :
    ∑ ℓ, f ℓ = (f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩) + f ⟨1, ()⟩ := by
  unfold doppel at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : doppelL.Leaves, f ⟨0, ℓ⟩) + (∑ ℓ : doppelR.Leaves, f ⟨1, ℓ⟩) = _
  unfold doppelL doppelR
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `V_{doppel}(q) = (1 − q)/2 + 5`. Source: `zoo.md` ZO-4 (d2) (`V(δ_a) = 5 < 11/2 = V(δ_b)`).
Kind: P -/
theorem doppel_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) doppel = (1 - q) / 2 + 5 := by
  have hL : value (procQ q h0 h1) doppelL = 1 - q := by
    simp only [doppelL, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
      FinDistr.act2_b]
    ring
  have hR : value (procQ q h0 h1) doppelR = 10 := by simp [doppelR, value_leaf]
  simp only [doppel, value_chance, Fin.sum_univ_two]
  show FinDistr.fair.w 0 * value (procQ q h0 h1) doppelL +
    FinDistr.fair.w 1 * value (procQ q h0 h1) doppelR = _
  rw [hL, hR]
  simp [FinDistr.fair, FinDistr.coin]; ring

/-! ### `tieTree3` (CA-4′) -/

/-- Tie-tree worlds `(act₁, act₂)`. Source: `calibration.md` CA-4′. Kind: D -/
abbrev TieW : Type := Act2 × Act2

/-- **CA-4′'s tie tree `T₃`**: `d₁ = (⊤, {a, b})`; `a → d₂` with `x → 1`, `y → 0`; `b → d₃` with
`x' → 1`, `y' → −5` (`x = x' = a`, `y = y' = b`); worlds record `(act₁, act₂)`.
Source: `calibration.md` CA-4′ ("the tie tree `T₃`")
Kind: D -/
def tieTree3 : Tree TieW Pt3 (fun _ => Act2) ℚ :=
  .decision .d1 fun
    | .a => .decision .d2 fun
      | .a => .leaf (.a, .a) 1
      | .b => .leaf (.a, .b) 0
    | .b => .decision .d3 fun
      | .a => .leaf (.b, .a) 1
      | .b => .leaf (.b, .b) (-5)

/-- `O_{d₁} = ⊤`, `O_{d₂} = {act₁ = a}`, `O_{d₃} = {act₁ = b}`.
Source: `calibration.md` CA-4′
Kind: D -/
def tieObs : Pt3 → Finset TieW
  | .d1 => Finset.univ
  | .d2 => Finset.univ.filter fun w => w.1 = .a
  | .d3 => Finset.univ.filter fun w => w.1 = .b

/-- Act events on `tieTree3`: `d₁` reads `act₁`, `d₂`/`d₃` read `act₂`.
Source: `calibration.md` CA-4′
Kind: D -/
def tieActEv : Pt3 → Act2 → Finset TieW
  | .d1, v => Finset.univ.filter fun w => w.1 = v
  | .d2, v => Finset.univ.filter fun w => w.2 = v
  | .d3, v => Finset.univ.filter fun w => w.2 = v

/-- A sum over the four leaves of `tieTree3`. Source: none: infrastructure. Kind: L -/
theorem tieTree3_sum {M : Type} [AddCommMonoid M] (f : tieTree3.Leaves → M) :
    ∑ ℓ, f ℓ = (f ⟨.a, .a, ()⟩ + f ⟨.a, .b, ()⟩) + (f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩) := by
  unfold tieTree3 at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- The value of `tieTree3` under any procedure, in the weights at the three points.
Source: `calibration.md` CA-4′
Kind: P -/
theorem tieTree3_value (C : Proc Pt3 (fun _ => Act2) ℚ) :
    value C tieTree3 =
      (C .d1).w .a * ((C .d2).w .a * 1 + (C .d2).w .b * 0) +
        (C .d1).w .b * ((C .d3).w .a * 1 + (C .d3).w .b * (-5)) := by
  simp only [tieTree3, value_decision, value_leaf, Act2.sum_univ]

/-! ### `revTree D t` (GR-10's reviewer tree) -/

/-- Reviewer-tree worlds `(live?, act)`. Source: `grounding.md` GR-10 (single-fiber sharpening).
Kind: D -/
abbrev RevW : Type := Bool × Act2

/-- The reviewer tree's live `d`-node: `a → 0`, `b → −t`, worlds `(true, act)` in `O_d`.
Source: `grounding.md` GR-10; mandate T9(c), representation decision 7
Kind: D -/
def revLive (t : ℚ) : Tree RevW Unit (fun _ => Act2) ℚ :=
  .decision () fun | .a => .leaf (true, .a) 0 | .b => .leaf (true, .b) (-t)

/-- The reviewer tree's predictor `d`-node: `a → −D`, `b → D`, worlds `(false, act)` outside `O_d`.
Source: `grounding.md` GR-10
Kind: D -/
def revPred (D : ℚ) : Tree RevW Unit (fun _ => Act2) ℚ :=
  .decision () fun | .a => .leaf (false, .a) (-D) | .b => .leaf (false, .b) D

/-- **`revTree D t`**: a fair coin over `revLive t` and `revPred D`.
Source: `grounding.md` GR-10 ("the reviewer's tree: ratio `→ 2`"); mandate T9(c)
Kind: D -/
def revTree (D t : ℚ) : Tree RevW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases (revLive t) (fun _ => revPred D) i

/-- `O_d = {live}` on `revTree`. Source: `grounding.md` GR-10. Kind: D -/
def revObs : Unit → Finset RevW := fun _ => Finset.univ.filter fun w => w.1 = true

/-- Act events `{act = v}` on `revTree`. Source: `grounding.md` GR-10. Kind: D -/
def revActEv : Unit → Act2 → Finset RevW := fun _ v => Finset.univ.filter fun w => w.2 = v

/-- A sum over the four leaves of `revTree`. Source: none: infrastructure. Kind: L -/
theorem revTree_sum {M : Type} [AddCommMonoid M] (D t : ℚ) (f : (revTree D t).Leaves → M) :
    ∑ ℓ, f ℓ = (f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩) + (f ⟨1, .a, ()⟩ + f ⟨1, .b, ()⟩) := by
  unfold revTree at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (revLive t).Leaves, f ⟨0, ℓ⟩) + (∑ ℓ : (revPred D).Leaves, f ⟨1, ℓ⟩) = _
  unfold revLive revPred
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `V_{revTree D t}(q) = ½ (1 − q)(−t) + ½ (q(−D) + (1 − q) D)`.
Source: `grounding.md` GR-10 (single-fiber sharpening); mandate T9(c)
Kind: P -/
theorem revTree_value (D t q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (revTree D t) =
      (1 / 2) * ((1 - q) * (-t)) + (1 / 2) * (q * (-D) + (1 - q) * D) := by
  have hL : value (procQ q h0 h1) (revLive t) = (1 - q) * (-t) := by
    simp only [revLive, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
      FinDistr.act2_b]
    ring
  have hR : value (procQ q h0 h1) (revPred D) = q * (-D) + (1 - q) * D := by
    simp only [revPred, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
      FinDistr.act2_b]
  simp only [revTree, value_chance, Fin.sum_univ_two]
  show FinDistr.fair.w 0 * value (procQ q h0 h1) (revLive t) +
    FinDistr.fair.w 1 * value (procQ q h0 h1) (revPred D) = _
  rw [hL, hR]
  simp [FinDistr.fair, FinDistr.coin]; norm_num

/-! ### The Stag Hunt's observations and act events -/

/-- `O = ⊤` at both points of `twoStag`.
Source: `repair/P10.md` P10-3′(ii) ("`O = ⊤` at both"); `identity.md` ID-21
Kind: D -/
def stagObs : Pt2 → Finset MiniW := fun _ => Finset.univ

/-- Act events on `twoStag` (worlds `(a₁, a₂)`): `p1` reads the first coordinate, `p2` the second.
Source: `zoo.md` ZO-7 ("worlds record `(a₁, a₂)`"); `identity.md` ID-21
Kind: D -/
def stagActEv : Pt2 → Act2 → Finset MiniW
  | .p1, v => Finset.univ.filter fun w => w.1 = v
  | .p2, v => Finset.univ.filter fun w => w.2 = v

/-- A sum over the four leaves of `twoStag`. Source: none: infrastructure. Kind: L -/
theorem twoStag_sum {M : Type} [AddCommMonoid M] (f : twoStag.Leaves → M) :
    ∑ ℓ, f ℓ = (f ⟨.a, .a, ()⟩ + f ⟨.a, .b, ()⟩) + (f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩) := by
  unfold twoStag at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

end Cleanroom.Decision.DpEdtUdtFair
