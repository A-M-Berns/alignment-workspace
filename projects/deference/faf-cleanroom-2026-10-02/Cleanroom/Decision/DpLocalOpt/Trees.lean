import Cleanroom.Decision.DpLocalOpt.Sia

/-!
# `dp-local-opt`: the new catalogue trees and their `value` closed forms

Every tree of the package's witnesses, over `ℚ`, with its value as a polynomial in the mixing
weights, proved from the tree (as `dp-core-tree`'s `amd_value` is). Worlds carry the draw
sequence where the sources name one, and are `Unit` where only payoffs matter (the `k`-fold
mugging and Death in Damascus: no theorem here reads an event on them).

* `amdShape r₀ r₁ r₂` — the absent-minded-driver shape (v2 Proposition 5(c)) with free payoffs;
  `amdShape 0 4 1 = amd`; Wei Dai's variant `amdShape 1 0 2`; ZO-6's `amdShape 2 1 5`.
* `mergedStag` — one point at two nested nodes, both branches continue (P10-3′(i)).
* `twoStag` — the two-point sequential Stag Hunt (P10-3′(ii), ID-21).
* `threeCoal` — three chance-free points with HA-9′'s payoffs.
* `kfold k x y b` — the `k`-fold counterfactual mugging with coupling `b` (SE-13, SP-23).
* `deathDamascus p L c` — draw-keyed Death in Damascus (P03-7).
* `fairDepth2` — the depth-2 fair tree `(1; 4, 1/2)` (dp-cf-2-026(b)).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-! ### Sums over the leaves of a leaf tree, over `ℚ` -/

/-- The absent-minded-driver **shape** with free payoffs: one point `d` at two nested nodes; first
node `a → r₀`, `b →` second node; second node `a → r₁`, `b → r₂`. `amdShape 0 4 1` is v2's `amd`.
Source: [[decision-problems-v2]] Proposition 5(c) (line 203); `sl-workflow/notes/repair/P10.md`
I1 (Wei Dai's variant, `(1, 0, 2)` with EXIT = `a`, CONT = `b`); A31 (`(2, 1, 5)`)
Kind: D -/
def amdShape (r₀ r₁ r₂ : ℚ) : Tree AmdW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .sa r₀
    | .b => .decision () fun
      | .a => .leaf .sba r₁
      | .b => .leaf .sbb r₂

/-- `amdShape 0 4 1` is the catalogue's `amd`.
Source: none: infrastructure
Kind: L -/
theorem amdShape_eq_amd : amdShape 0 4 1 = amd := rfl

/-- **Wei Dai's AMD** `(1; 0, 2)`: EXIT (`a`) at the first node pays `1`, EXIT at the second `0`,
CONT (`b`) twice `2`.
Source: `sl-workflow/notes/repair/P10.md` I1 ("leaf payoffs `1` (exit at the first node), `0`
(exit at the second), `2` (continue twice)"); `notes/lean/P10-weidai-amd.lean`
Kind: D -/
abbrev weiDai : Tree AmdW Unit (fun _ => Act2) ℚ := amdShape 1 0 2

/-- **ZO-6's AMD** `(2; 1, 5)`: the nested shape on which `δ_a` is Theorem-1-ratified but not
coherent.
Source: A31 ("payoffs `2` at the first exit and `1, 5` at the second")
Kind: D -/
abbrev zo6Amd : Tree AmdW Unit (fun _ => Act2) ℚ := amdShape 2 1 5

/-- `V_{amdShape}(C) = q r₀ + (1 − q)(q r₁ + (1 − q) r₂)`, `q := C(d)(a)`.
Source: [[decision-problems-v2]] Proposition 5(c) proof (`(1−x)(3x+1)` at `(0,4,1)`)
Kind: P -/
theorem amdShape_value (r₀ r₁ r₂ q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (amdShape r₀ r₁ r₂) = q * r₀ + (1 - q) * (q * r₁ + (1 - q) * r₂) := by
  simp only [amdShape, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]

/-- Wei Dai's AMD: `V = 2q² − 3q + 2` in `q := C(d)(EXIT)`; with `x := C(d)(CONT) = 1 − q` this
is P10's `2x² − x + 1`.
Source: `repair/P10.md` I1 (`V(x) = 2x² − x + 1`); `notes/lean/P10-weidai-amd.lean` `V_closed`
Kind: P -/
theorem weiDai_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) weiDai = 2 * (1 - q) ^ 2 - (1 - q) + 1 := by
  rw [weiDai, amdShape_value]; ring

/-- ZO-6's AMD: `V = 5 − 7q + 4q²` (convex in `q := C(d)(a)`).
Source: mandate T5(d) (`V = 5 − 7q + 4q²`)
Kind: P -/
theorem zo6Amd_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) zo6Amd = 5 - 7 * q + 4 * q ^ 2 := by
  rw [zo6Amd, amdShape_value]; ring

/-! ### The merged Stag Hunt -/

/-- **The merged Stag Hunt**: one point at two nested nodes, both branches continue; `S = a`,
`H = b`; `(S,S) → 2`, `(H,H) → 1`, else `0`. Worlds record the two draws.
Source: `sl-workflow/notes/repair/P10.md` P10-3′(i) ("one point at two nested nodes, both
always reached; `2` at `(S,S)`, `1` at `(H,H)`, else `0`")
Kind: D -/
def mergedStag : Tree MiniW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .decision () fun
      | .a => .leaf (.a, .a) 2
      | .b => .leaf (.a, .b) 0
    | .b => .decision () fun
      | .a => .leaf (.b, .a) 0
      | .b => .leaf (.b, .b) 1

/-- `V_{mergedStag} = 3q² − 2q + 1`, `q := C(d)(S)`.
Source: `repair/P10.md` P10-3′(i) (`V(q) = 3q² − 2q + 1`)
Kind: P -/
theorem mergedStag_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) mergedStag = 3 * q ^ 2 - 2 * q + 1 := by
  simp only [mergedStag, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  ring

/-! ### Two-point trees: the sequential Stag Hunt and the depth-2 fair tree -/

/-- The two-point procedure `C(p1) = (p, 1 − p)`, `C(p2) = (q, 1 − q)` on `Pt2`.
Source: none: infrastructure
Kind: D -/
def proc2 (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Proc Pt2 (fun _ => Act2) ℚ
  | .p1 => FinDistr.act2 p hp0 hp1
  | .p2 => FinDistr.act2 q hq0 hq1

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem proc2_p1 (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    proc2 p q hp0 hp1 hq0 hq1 .p1 = FinDistr.act2 p hp0 hp1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem proc2_p2 (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    proc2 p q hp0 hp1 hq0 hq1 .p2 = FinDistr.act2 q hq0 hq1 := rfl

/-- **The two-point sequential Stag Hunt**: `d₁` then `d₂`, no chance; `S = a`, `H = b`;
`(S,S) → 2`, `(H,H) → 1`, else `0`. Almost fair (one node per point).
Source: `repair/P10.md` P10-3′(ii) ("Two-point Stag Hunt (`d₁` then `d₂`, `O = ⊤` at both, no
chance; ID-21's tree)"); A32 ("a sequential Stag Hunt")
Kind: D -/
def twoStag : Tree MiniW Pt2 (fun _ => Act2) ℚ :=
  .decision .p1 fun
    | .a => .decision .p2 fun
      | .a => .leaf (.a, .a) 2
      | .b => .leaf (.a, .b) 0
    | .b => .decision .p2 fun
      | .a => .leaf (.b, .a) 0
      | .b => .leaf (.b, .b) 1

/-- `V_{twoStag}(p, q) = 2pq + (1 − p)(1 − q)`, `p := C(d₁)(S)`, `q := C(d₂)(S)`.
Source: mandate T11(b) (`V = 2pq + (1−p)(1−q)`)
Kind: P -/
theorem twoStag_value (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    value (proc2 p q hp0 hp1 hq0 hq1) twoStag = 2 * p * q + (1 - p) * (1 - q) := by
  simp only [twoStag, value_decision, value_leaf, Act2.sum_univ, proc2_p1, proc2_p2,
    FinDistr.act2_a, FinDistr.act2_b]
  ring

/-- **The depth-2 fair tree** `(1; 4, 1/2)`: `out → 1`; `in → [x → 4, y → 1/2]`, two points.
Source: `cf-workflow/phase2-notes/repair/dynamic.md` Open 8 ("the face `p_in = 0`, `p_x < 1/7` of
the depth-2 fair tree, value `1 < 4`"); dp-cf-2-026(b)
Kind: D -/
abbrev fairDepth2 : Tree TwoW Pt2 (fun _ => Act2) ℚ := twoPoint 1 4 (1 / 2)

/-- `V_{fairDepth2}(p, q) = 1 + (1 − p)(7q/2 − 1/2)` with `p := C(p1)(out)`, `q := C(p2)(x)`.
Source: mandate T11(a) (`V = 1 + p_in (7 p_x / 2 − 1/2)`)
Kind: P -/
theorem fairDepth2_value (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    value (proc2 p q hp0 hp1 hq0 hq1) fairDepth2 = 1 + (1 - p) * (7 * q / 2 - 1 / 2) := by
  simp only [fairDepth2, twoPoint, value_decision, value_leaf, Act2.sum_univ, proc2_p1, proc2_p2,
    FinDistr.act2_a, FinDistr.act2_b]
  ring

/-! ### Three chance-free points -/

/-- Three decision points.
Source: `repair/harmony.md` HA-9′ ("three chance-free points")
Kind: D -/
inductive Pt3 : Type
  | d1
  | d2
  | d3
  deriving DecidableEq, Fintype

/-- HA-9′'s payoffs (`S = a`, `H = b`): `HHH → 4`; `SSH, SHH, HSS, HSH, HHS → 3`; `SSS, SHS → 2`.
Source: `repair/harmony.md` HA-9′ ("payoffs `SSS:2, SSH:3, SHS:2, SHH:3, HSS:3, HSH:3, HHS:3,
HHH:4`")
Kind: D -/
def coalPay : Act2 → Act2 → Act2 → ℚ
  | .a, .a, .a => 2
  | .a, .a, .b => 3
  | .a, .b, .a => 2
  | .a, .b, .b => 3
  | .b, .a, .a => 3
  | .b, .a, .b => 3
  | .b, .b, .a => 3
  | .b, .b, .b => 4

/-- **The three-coalition tree**: `d₁`, `d₂`, `d₃` in sequence, no chance, HA-9′'s payoffs.
Source: `repair/harmony.md` HA-9′
Kind: D -/
def threeCoal : Tree (Act2 × Act2 × Act2) Pt3 (fun _ => Act2) ℚ :=
  .decision .d1 fun a₁ => .decision .d2 fun a₂ => .decision .d3 fun a₃ =>
    .leaf (a₁, a₂, a₃) (coalPay a₁ a₂ a₃)

/-- The deterministic three-point profile.
Source: none: infrastructure
Kind: D -/
def prof3 (a₁ a₂ a₃ : Act2) : Proc Pt3 (fun _ => Act2) ℚ :=
  Proc.ofFun fun | .d1 => a₁ | .d2 => a₂ | .d3 => a₃

/-- The value of a deterministic profile on `threeCoal` is its payoff.
Source: none: infrastructure
Kind: L -/
theorem threeCoal_value_prof (a₁ a₂ a₃ : Act2) :
    value (prof3 a₁ a₂ a₃) threeCoal = coalPay a₁ a₂ a₃ := by
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    simp [threeCoal, value_decision, prof3, Proc.ofFun, coalPay]

/-! ### The `k`-fold counterfactual mugging -/

/-- The simulated branch of the `k`-fold mugging: `k` nested `d`-nodes, then a chance node paying
`y` with probability `b j`, `j` = number of paying draws so far (`pay = a`, `refuse = b`). Built
by recursion on the remaining depth carrying `j`.
Source: `repair/seeds.md` SE-13 ("`H`: `k` nested simulated `d`-nodes, transfer `y` with
probability `b_j`, `j` = number of paying draws")
Kind: D -/
def kfoldH (y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    ℕ → ℕ → Tree Unit Unit (fun _ => Act2) ℚ
  | 0, j => .chance 2 (FinDistr.coin (b j) (hb j).1 (hb j).2) ![.leaf () y, .leaf () 0]
  | k + 1, j => .decision () fun
      | .a => kfoldH y b hb k (j + 1)
      | .b => kfoldH y b hb k j

/-- **The `k`-fold counterfactual mugging**: fair coin; `T` (index `0`): one real `d`-node, pay
(`a`) `→ −x`, refuse (`b`) `→ 0`; `H` (index `1`): `k` nested simulated `d`-nodes then a chance
node paying `y` with probability `b j`, `j` = number of paying draws. Couplings `b`: `linearB`,
`concaveB`, `convexB` below.
Source: `repair/seeds.md` SE-13; `repair/spectrum.md` SP-23; [[fable-slop-notes]] "Dilution"
Kind: D -/
def kfold (k : ℕ) (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair
    ![.decision () fun | .a => .leaf () (-x) | .b => .leaf () 0, kfoldH y b hb k 0]

/-- Linear coupling `b_j = j/k` (clamped at `1`; only `j ≤ k` is reached).
Source: `repair/seeds.md` SE-13 ("`1` linear"); [[fable-slop-notes]] "Dilution" (`b_j = j/k`)
Kind: D -/
def linearB (k : ℕ) (j : ℕ) : ℚ := min ((j : ℚ) / k) 1

/-- Concave coupling `b_j = 1[j ≥ 1]` ("any one payer suffices").
Source: [[fable-slop-notes]] "Dilution" (`b_j = 1[j ≥ 1]`)
Kind: D -/
def concaveB (j : ℕ) : ℚ := if 1 ≤ j then 1 else 0

/-- Convex coupling `b_j = 1[j = k]` ("unanimity").
Source: [[fable-slop-notes]] "Dilution" (`b_j = 1[j = k]`)
Kind: D -/
def convexB (k : ℕ) (j : ℕ) : ℚ := if j = k then 1 else 0

/-- The linear coupling is a probability.
Source: none: infrastructure
Kind: L -/
theorem linearB_bounds (k j : ℕ) : 0 ≤ linearB k j ∧ linearB k j ≤ 1 := by
  unfold linearB
  refine ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩

/-- The concave coupling is a probability.
Source: none: infrastructure
Kind: L -/
theorem concaveB_bounds (j : ℕ) : 0 ≤ concaveB j ∧ concaveB j ≤ 1 := by
  unfold concaveB; split_ifs <;> norm_num

/-- The convex coupling is a probability.
Source: none: infrastructure
Kind: L -/
theorem convexB_bounds (k j : ℕ) : 0 ≤ convexB k j ∧ convexB k j ≤ 1 := by
  unfold convexB; split_ifs <;> norm_num

/-- Below `k` the linear coupling is `j/k`.
Source: none: infrastructure
Kind: L -/
theorem linearB_of_le {k j : ℕ} (hk : 0 < k) (h : j ≤ k) : linearB k j = (j : ℚ) / k := by
  unfold linearB
  apply min_eq_left
  rw [div_le_one (by exact_mod_cast hk)]
  exact_mod_cast h

/-- The value of the simulated branch at the bottom: `y · b j`.
Source: none: infrastructure
Kind: L -/
theorem kfoldH_zero_value (y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (j : ℕ)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (kfoldH y b hb 0 j) = y * b j := by
  simp only [kfoldH, value_chance, value_leaf, Fin.sum_univ_two, FinDistr.coin]
  simp; ring

/-- The value of the simulated branch one level up: the `C(d)`-average of the two continuations.
Source: none: infrastructure
Kind: L -/
theorem kfoldH_succ_value (y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (k j : ℕ)
    (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (kfoldH y b hb (k + 1) j) =
      q * value (procQ q h0 h1) (kfoldH y b hb k (j + 1)) +
        (1 - q) * value (procQ q h0 h1) (kfoldH y b hb k j) := by
  simp only [kfoldH, value_decision, Act2.sum_univ, procQ, FinDistr.act2_a, FinDistr.act2_b]

/-- `V_{kfold}(C) = ½(−x q) + ½ V_H(C)` where `V_H` is the simulated branch's value.
Source: none: infrastructure
Kind: L -/
theorem kfold_value (k : ℕ) (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (kfold k x y b hb) =
      (1 / 2) * (-x * q) + (1 / 2) * value (procQ q h0 h1) (kfoldH y b hb k 0) := by
  simp [kfold, value_chance, value_decision, Fin.sum_univ_two, FinDistr.fair, FinDistr.coin,
    Act2.sum_univ, procQ]
  ring

/-- **Linear coupling**: the simulated branch of remaining depth `k'` starting at `j` payers is
worth `y (j + k' q) / k` (for `j + k' ≤ k`, `k > 0`).
Source: [[fable-slop-notes]] "Dilution" ("with linear `b_j = j/k`, `V` is affine in the pay-rate
`q`")
Kind: P -/
theorem kfoldH_linear_value (k : ℕ) (hk : 0 < k) (y : ℚ) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∀ k' j, j + k' ≤ k →
      value (procQ q h0 h1) (kfoldH y (linearB k) (linearB_bounds k) k' j) =
        y * ((j : ℚ) + k' * q) / k
  | 0, j, hj => by
      rw [kfoldH_zero_value, linearB_of_le hk (by simpa using hj)]
      simp; ring
  | k' + 1, j, hj => by
      rw [kfoldH_succ_value, kfoldH_linear_value k hk y q h0 h1 k' (j + 1) (by omega),
        kfoldH_linear_value k hk y q h0 h1 k' j (by omega)]
      push_cast; ring

/-- **Convex coupling at `q = 1`**: every draw pays, so the branch is worth `y` iff `j + k' = k`.
Source: [[fable-slop-notes]] "Dilution" (convex `b_j = 1[j = k]`, all-pay)
Kind: P -/
theorem kfoldH_convex_value_one (k : ℕ) (y : ℚ) :
    ∀ k' j, value (procQ 1 zero_le_one le_rfl) (kfoldH y (convexB k) (convexB_bounds k) k' j) =
      if j + k' = k then y else 0
  | 0, j => by
      rw [kfoldH_zero_value]; unfold convexB
      simp only [add_zero]; split_ifs <;> simp
  | k' + 1, j => by
      rw [kfoldH_succ_value, kfoldH_convex_value_one k y k' (j + 1),
        kfoldH_convex_value_one k y k' j]
      have : j + 1 + k' = j + (k' + 1) := by omega
      rw [this]; ring

/-- **Convex `3`-fold**: `V(q) = ½(−x q + y q³)`.
Source: mandate T8(c) (`V(q) = ½(−xq + yq³)`); dp-cf-122
Kind: P -/
theorem kfold3_convex_value (x y : ℚ) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (kfold 3 x y (convexB 3) (convexB_bounds 3)) =
      (1 / 2) * (-x * q + y * q ^ 3) := by
  rw [kfold_value]
  simp only [kfoldH_succ_value, kfoldH_zero_value, convexB]
  norm_num; ring

/-- **Concave `4`-fold at `x = 1`, `y = 3`**: `V(q) = ½(−q + 3(1 − (1−q)⁴))`.
Source: mandate T5(c) (`V(q) = ½(−q + 3(1 − (1 − q)⁴))`)
Kind: P -/
theorem kfold4_concave_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (kfold 4 1 3 concaveB concaveB_bounds) =
      (1 / 2) * (-q + 3 * (1 - (1 - q) ^ 4)) := by
  rw [kfold_value]
  simp only [kfoldH_succ_value, kfoldH_zero_value, concaveB]
  norm_num; ring

/-! ### Death in Damascus, draw-keyed -/

/-- **Draw-keyed Death in Damascus** `(p, L, c)`: stay = `a`, flee = `b`. With probability `p`
Death is at the drawn city (one `d`-node: stay `→ 0`, flee `→ −c`); with probability `1 − p` a
second `d`-node is Death's independent sample of `C(d)`: same draw `→` death (`0` / `−c`),
different `→` life (`L` / `L − c`). The outer node is Death's sample, the inner the agent's draw.
Source: `sl-workflow/notes/repair/P03.md` P03-7 (Death's city as "the realized draw — a
draw-keyed Definition 6 chance node"; the skill-`p` family, `p = 0` numbers)
Kind: D -/
def deathDamascus (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L c : ℚ) :
    Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin p hp0 hp1)
    ![.decision () fun | .a => .leaf () 0 | .b => .leaf () (-c),
      .decision () fun
        | .a => .decision () fun | .a => .leaf () 0 | .b => .leaf () (L - c)
        | .b => .decision () fun | .a => .leaf () L | .b => .leaf () (-c)]

/-- `V_{DD}(q) = p(−c(1−q)) + (1−p)(q(1−q)(L−c) + (1−q)(qL − (1−q)c))`, `q := C(d)(stay)`.
Source: `repair/P03.md` P03-7 (the `p = 0` instance `−2000q² + 2001q − 1` at `L = 1000`, `c = 1`)
Kind: P -/
theorem deathDamascus_value (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L c q : ℚ) (h0 : 0 ≤ q)
    (h1 : q ≤ 1) :
    value (procQ q h0 h1) (deathDamascus p hp0 hp1 L c) =
      p * (-(c * (1 - q))) + (1 - p) * (q * ((1 - q) * (L - c)) + (1 - q) * (q * L - (1 - q) * c)) := by
  simp [deathDamascus, value_chance, value_decision, Fin.sum_univ_two, FinDistr.coin,
    Act2.sum_univ, procQ]
  ring

/-- The `p = 0`, `L = 1000`, `c = 1` instance: `V = −2000q² + 2001q − 1`.
Source: `repair/P03.md` P03-7 ("its `p = 0` numbers: `V_B(q) = −2000q² + 2001q − 1`")
Kind: N+ -/
theorem deathDamascus_value_instance (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (deathDamascus 0 le_rfl zero_le_one 1000 1) =
      -2000 * q ^ 2 + 2001 * q - 1 := by
  rw [deathDamascus_value]; ring

end Cleanroom.Decision.DpLocalOpt
