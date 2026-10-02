import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Tickle
import Cleanroom.Decision.DpLocalOpt.Sia
import Cleanroom.Decision.DpLocalOpt.Trees
import Cleanroom.Decision.DpLocalOpt.TwoPointWitness
import Cleanroom.Decision.DpLocalOpt.AmdWitness
import Cleanroom.Decision.DpCalibration.Witnesses
import Cleanroom.Decision.DpCalibration.Examples

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T1: the value-polynomial library

`V_B(C)` as an explicit polynomial in the procedure's parameters, for every catalogue tree of
`dp-core-tree` without a shipped closed form, derived from the tree (`value_decision` /
`value_chance` / `value_leaf`, then `ring`) and never asserted. Already shipped elsewhere and
cited, not restated: `amd_value` (`(1−q)(3q+1)`), `amd_value'` (`1−q`), `miniature_value`
(`3q(1−q)`), `mug1_value` (`q(y−x)/2`), `mug2_value` (`(y − q(x+y))/2`), `twoPoint_value`
(`p r_out + (1−p)(q r_x + (1−q) r_y)`), `amdShape_value`, `mergedStag_value`, `twoStag_value`,
`kfold_*_value`, `deathDamascus_value`, `threeCoal_value_prof`.

**Disclosed once for the whole package** (`Fidelity: variant: payoffs in a linearly ordered
field`): every catalogue statement is over `ℚ`, as `dp-core-tree`'s catalogue is.

Procedures on multi-point trees are parametrised by one number per point (`tnProc x y` on
`TnPt`/`Box`, `tysProc u v` on `Five10`, `proc2 p q` on `Pt2`), and the lemmas
`Proc.tnPt_eq_tnProc` / `Proc.five10_eq_tysProc` / `Proc.unit_eq_procQ` show every procedure is
one of these, so a closed form at the parametrised procedure is a closed form for *every*
procedure (the mandate's "for every procedure" trap).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## Parametrised procedures on the catalogue's action types -/

/-- The mixed action `(t, 1 − t)` on `Box` (`t` = mass on `large`).
Source: none: infrastructure
Kind: D -/
def FinDistr.box (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : FinDistr ℚ Box where
  w := fun | .large => t | .both => 1 - t
  nonneg := by intro x; cases x <;> simp <;> linarith
  sum_one := by rw [Box.sum_univ]; simp

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.box_large (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (FinDistr.box t h0 h1).w .large = t := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.box_both (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (FinDistr.box t h0 h1).w .both = 1 - t := rfl

/-- Every mixed action on `Box` is `box (m(large))`. Source: none: infrastructure. Kind: L -/
theorem FinDistr.eq_box (m : FinDistr ℚ Box) :
    m = FinDistr.box (m.w .large) (m.nonneg .large) (m.w_le_one .large) := by
  apply FinDistr.ext'
  intro x
  have h := m.sum_one
  rw [Box.sum_univ] at h
  cases x
  · rfl
  · simp only [FinDistr.box_both]; linarith

/-- **The two-point Newcomb procedure** `tnProc x y`: `large` with probability `x` at `d_F` and
`y` at `d_E` (the mandate's `(x, y)`; pure labels `1 = large`, `0 = both`).
Source: [[decision-problems-v2]] §7.2 ("Policies `(x, y)`"); mandate T1
Kind: D -/
def tnProc (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Proc TnPt (fun _ => Box) ℚ
  | .F => FinDistr.box x hx0 hx1
  | .E => FinDistr.box y hy0 hy1

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tnProc_F (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    tnProc x y hx0 hx1 hy0 hy1 .F = FinDistr.box x hx0 hx1 := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tnProc_E (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    tnProc x y hx0 hx1 hy0 hy1 .E = FinDistr.box y hy0 hy1 := rfl

/-- Every procedure on the Newcomb points is a `tnProc`. Source: none: infrastructure. Kind: L -/
theorem Proc.tnPt_eq_tnProc (C : Proc TnPt (fun _ => Box) ℚ) :
    C = tnProc ((C .F).w .large) ((C .E).w .large) ((C .F).nonneg _) ((C .F).w_le_one _)
      ((C .E).nonneg _) ((C .E).w_le_one _) := by
  funext d; cases d
  · exact FinDistr.eq_box (C .F)
  · exact FinDistr.eq_box (C .E)

/-- The two-boxer is `tnProc 0 0`. Source: none: infrastructure. Kind: L -/
theorem procBoth_eq : procBoth = tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one := by
  funext d; apply FinDistr.ext'; intro a; cases d <;> cases a <;> simp [procBoth]

/-- The one-boxer is `tnProc 1 1`. Source: none: infrastructure. Kind: L -/
theorem procLarge_eq : procLarge = tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl := by
  funext d; apply FinDistr.ext'; intro a; cases d <;> cases a <;> simp [procLarge]

/-- Deviating `tnProc x y` at `d_E` to `box y'` is `tnProc x y'`. Source: none: infrastructure.
Kind: L -/
theorem tnProc_deviate_E (x y y' : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hy0' : 0 ≤ y') (hy1' : y' ≤ 1) :
    (tnProc x y hx0 hx1 hy0 hy1).deviate .E (FinDistr.box y' hy0' hy1') =
      tnProc x y' hx0 hx1 hy0' hy1' := by
  funext d; cases d <;> simp [Proc.deviate, tnProc]

/-- Deviating `tnProc x y` at `d_F` to `box x'` is `tnProc x' y`. Source: none: infrastructure.
Kind: L -/
theorem tnProc_deviate_F (x y x' : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1) :
    (tnProc x y hx0 hx1 hy0 hy1).deviate .F (FinDistr.box x' hx0' hx1') =
      tnProc x' y hx0' hx1' hy0 hy1 := by
  funext d; cases d <;> simp [Proc.deviate, tnProc]

/-- The mixed action `(1 − t, t)` on `Five10` (`t` = mass on `ten`).
Source: none: infrastructure
Kind: D -/
def FinDistr.five10 (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : FinDistr ℚ Five10 where
  w := fun | .five => 1 - t | .ten => t
  nonneg := by intro x; cases x <;> simp <;> linarith
  sum_one := by rw [Five10.sum_univ]; simp

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.five10_five (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (FinDistr.five10 t h0 h1).w .five = 1 - t := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.five10_ten (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (FinDistr.five10 t h0 h1).w .ten = t := rfl

/-- Every mixed action on `Five10` is `five10 (m(ten))`. Source: none: infrastructure. Kind: L -/
theorem FinDistr.eq_five10 (m : FinDistr ℚ Five10) :
    m = FinDistr.five10 (m.w .ten) (m.nonneg .ten) (m.w_le_one .ten) := by
  apply FinDistr.ext'
  intro x
  have h := m.sum_one
  rw [Five10.sum_univ] at h
  cases x
  · simp only [FinDistr.five10_five]; linarith
  · rfl

/-- **The Told-You-So procedure** `tysProc u v`: mass `u` on `ten` at `d₅`, `v` at `d₁₀`.
Source: mandate T1 ("`u` = mass on `ten` at `d₅`, `v` at `d₁₀`")
Kind: D -/
def tysProc (u v : ℚ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Proc Five10 (fun _ => Five10) ℚ
  | .five => FinDistr.five10 u hu0 hu1
  | .ten => FinDistr.five10 v hv0 hv1

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tysProc_five (u v : ℚ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    tysProc u v hu0 hu1 hv0 hv1 .five = FinDistr.five10 u hu0 hu1 := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tysProc_ten (u v : ℚ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    tysProc u v hu0 hu1 hv0 hv1 .ten = FinDistr.five10 v hv0 hv1 := rfl

/-- Every procedure on the Told-You-So points is a `tysProc`. Source: none: infrastructure.
Kind: L -/
theorem Proc.five10_eq_tysProc (C : Proc Five10 (fun _ => Five10) ℚ) :
    C = tysProc ((C .five).w .ten) ((C .ten).w .ten) ((C .five).nonneg _) ((C .five).w_le_one _)
      ((C .ten).nonneg _) ((C .ten).w_le_one _) := by
  funext d; cases d
  · exact FinDistr.eq_five10 (C .five)
  · exact FinDistr.eq_five10 (C .ten)

/-! ## Transparent Newcomb -/

section newcomb

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y) (hy1 : y ≤ 1)

/-- **`V_{V1(p)}(x, y)`**: with `x` the probability of `large` at `d_F` and `y` at `d_E`,
`V = x·[p(L + (1−x)S) + (1−p)(1−y)S] + (1−x)·[(1−p)(L + (1−x)S) + p(1−y)S]` — the hypothetical
answer `x` routes the coin, the real answers pay.
Source: [[decision-problems-v2]] §7.2 (the V1 column of the table, extended to mixed policies);
mandate T1
Kind: P
Fidelity: stronger (mixed policies; the table's four rows are the vertices)
Hyps: none -/
theorem tnV1_value :
    value (tnProc x y hx0 hx1 hy0 hy1) (tnV1 p h0 h1 L S) =
      x * (p * (L + (1 - x) * S) + (1 - p) * ((1 - y) * S)) +
        (1 - x) * ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S)) := by
  simp only [tnV1, value_decision, value_chance, Box.sum_univ, Fin.sum_univ_two, tnProc_F,
    FinDistr.box_large, FinDistr.box_both]
  simp [tnReal, value_decision, value_leaf, Box.sum_univ, tnPay, FinDistr.coin]
  ring

/-- **`V_{V2(p)}(x, y)`**: `V = xy·[p(L + (1−x)S) + (1−p)(1−y)S] + (1−xy)·[(1−p)(L + (1−x)S) +
p(1−y)S]` — the coin is `p` only when both hypothetical answers are `large`.
Source: [[decision-problems-v2]] §7.2 (the V2 column of the table, extended to mixed policies);
mandate T1
Kind: P
Fidelity: stronger (mixed policies; the table's four rows are the vertices)
Hyps: none -/
theorem tnV2_value :
    value (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) =
      x * y * (p * (L + (1 - x) * S) + (1 - p) * ((1 - y) * S)) +
        (1 - x * y) * ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S)) := by
  simp only [tnV2, value_decision, value_chance, Box.sum_univ, Fin.sum_univ_two, tnProc_F,
    tnProc_E, FinDistr.box_large, FinDistr.box_both]
  simp [tnReal, value_decision, value_leaf, Box.sum_univ, tnPay, FinDistr.coin]
  ring

end newcomb

/-! ## Told-You-So -/

/-- **`V_{B_P}(u, v) = 5(1 − u) + u(10v + 5(1 − v))`**, `u` the mass on `ten` at `d₅`, `v` at
`d₁₀`.
Source: [[decision-problems-v2]] §7.1 (Proposition 8's values `5`, `10` are the vertices);
mandate T1 (`V = 5(1−u) + u(10v + 5(1−v))`)
Kind: P
Fidelity: stronger (every mixed procedure)
Hyps: none -/
theorem toldYouSo_value (u v : ℚ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    value (tysProc u v hu0 hu1 hv0 hv1) toldYouSo = 5 * (1 - u) + u * (10 * v + 5 * (1 - v)) := by
  simp only [toldYouSo, value_decision, value_leaf, Five10.sum_univ, tysProc_five, tysProc_ten,
    FinDistr.five10_five, FinDistr.five10_ten]
  ring

/-- The same for every procedure, in its own weights.
Source: mandate T1 ("do not state a closed form only at `procQ q` when the source says 'for
every procedure'")
Kind: L -/
theorem toldYouSo_value_all (C : Proc Five10 (fun _ => Five10) ℚ) :
    value C toldYouSo =
      5 * (1 - (C .five).w .ten) + (C .five).w .ten * (10 * (C .ten).w .ten + 5 * (1 - (C .ten).w .ten)) := by
  conv_lhs => rw [Proc.five10_eq_tysProc C]
  exact toldYouSo_value _ _ _ _ _ _

/-! ## One-point trees: selection forcing, Tree J, the routing root, opaque Newcomb, the gate,
coin-then-query -/

section onePoint

variable (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- **`V_{S_sel}(q) = ⅓(q u_a + (1−q) u_b) + ⅓ r_a + ⅓ r_b`**.
Source: `calibration.md` line 23 (the tree); mandate T1
Kind: P
Fidelity: exact
Hyps: none -/
theorem selectionForcing_value (ua ub ra rb : ℚ) :
    value (procQ q h0 h1) (selectionForcing ua ub ra rb) =
      (1 / 3) * (q * ua + (1 - q) * ub) + (1 / 3) * ra + (1 / 3) * rb := by
  simp only [selectionForcing, value_chance, Fin.sum_univ_three, FinDistr.third]
  simp [value_decision, value_leaf, Act2.sum_univ, procQ]

/-- **`V_J(q) = q + 4q(1 − q)`** on Tree J (`a → 1`; `b →` second node: `a → 4`, `b → 0`).
Source: `sl-synthesis.md` line 121 (the tree); mandate T1
Kind: P
Fidelity: exact
Hyps: none -/
theorem treeJ_value : value (procQ q h0 h1) treeJ = q + 4 * q * (1 - q) := by
  simp only [treeJ, value_decision, value_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  ring

/-- **`V_{routingRoot} = 0`** for every procedure (both leaves pay `0`).
Source: [[decision-problems-v2]] Remark 3.4 (the tree); mandate T1
Kind: T
Fidelity: exact -/
theorem routingRoot_value (C : Proc Unit (fun _ => Act2) ℚ) : value C routingRoot = 0 := by
  simp [routingRoot, value_decision, Act2.sum_univ]

/-- **`V_{gate} = 0`** for every procedure (every leaf pays `0`: the gate tree is a recording
witness, not a payoff witness).
Source: mandate T1 (dp-core-tree's `gate`)
Kind: T
Fidelity: exact -/
theorem gate_value (C : Proc GatePt (fun _ => Act2) ℚ) : value C gate = 0 := by
  simp [gate, value_decision, Act2.sum_univ]

/-- **`V_{coinQuery} = 0`** for every procedure (every leaf pays `0`).
Source: mandate T1 (dp-core-tree's `coinQuery`)
Kind: T
Fidelity: exact -/
theorem coinQuery_value (C : Proc Unit (fun _ => Act2) ℚ) : value C coinQuery = 0 := by
  simp [coinQuery, value_chance, value_decision, value_leaf]

/-- **Opaque Newcomb: `V(q) = L·(qp + (1−q)(1−p)) + (1−q)S`**, `q` the one-boxing probability
(the predictor samples `C(d)` and is right with probability `p`; the live draw takes `S` iff it
two-boxes).
Source: `sl-synthesis.md` line 120 (the tree); mandate T1
Kind: P
Fidelity: exact
Hyps: none -/
theorem opaqueNewcomb_value (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L S : ℚ) :
    value (procQ q h0 h1) (opaqueNewcomb p hp0 hp1 L S) =
      L * (q * p + (1 - q) * (1 - p)) + (1 - q) * S := by
  simp only [opaqueNewcomb, value_decision, value_chance, Act2.sum_univ, Fin.sum_univ_two,
    procQ, FinDistr.act2_a, FinDistr.act2_b]
  simp [value_leaf, opaqueFill, opaquePay, FinDistr.coin]
  ring

end onePoint

/-- Every one-point `Act2` closed form transfers to every procedure (`Proc.unit_eq_procQ`); the
selection-forcing tree as the instance the device table needs.
Source: mandate T1
Kind: L -/
theorem selectionForcing_value_all (ua ub ra rb : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (selectionForcing ua ub ra rb) =
      (1 / 3) * ((C ()).w .a * ua + (1 - (C ()).w .a) * ub) + (1 / 3) * ra + (1 / 3) * rb := by
  conv_lhs => rw [Proc.unit_eq_procQ C]
  exact selectionForcing_value _ _ _ ua ub ra rb

/-! ## The tickle tree -/

/-- **`V_{tickle}(q₁, q₀) = ρ(q₁ α − γ₁ β) + (1−ρ)(q₀ α − γ₀ β)`** under `procTickle q₁ q₀`
(smoke with probability `q_ℓ` at lesion `ℓ`): cancer is drawn from the lesion, not from the act,
so the act's only effect is `α` per smoke.
Source: [[decision-problems-v2]] §7.3 Proposition 12 (the tree); mandate T1
Kind: P
Fidelity: exact
Hyps: none -/
theorem tickle_value (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ₁ : ℚ) (g10 : 0 ≤ γ₁) (g11 : γ₁ ≤ 1)
    (γ₀ : ℚ) (g00 : 0 ≤ γ₀) (g01 : γ₀ ≤ 1) (α β : ℚ)
    (q₁ : ℚ) (a0 : 0 ≤ q₁) (a1 : q₁ ≤ 1) (q₀ : ℚ) (b0 : 0 ≤ q₀) (b1 : q₀ ≤ 1) :
    value (procTickle q₁ a0 a1 q₀ b0 b1) (tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β) =
      ρ * (q₁ * α - γ₁ * β) + (1 - ρ) * (q₀ * α - γ₀ * β) := by
  simp only [tickle, value_chance, value_decision, value_leaf, Fin.sum_univ_two,
    Fintype.sum_bool]
  simp [procTickle, tickleGamma, ticklePay, FinDistr.coin]
  ring

/-! ## The two-point out/in family as instances of `twoPoint_value` -/

section twoPointFamily

variable (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- Fantasy `(2;4,1)`: `V = 2p + (1−p)(4q + (1−q))`, `p := C(p1)(out)`, `q := C(p2)(x)`.
Source: `adversary/calibration.md` line 35; mandate T1
Kind: N+ -/
theorem fantasy241_value :
    value (proc2 p q hp0 hp1 hq0 hq1) fantasy241 = 2 * p + (1 - p) * (4 * q + (1 - q)) := by
  unfold fantasy241; rw [twoPoint_value]; ring

/-- Fantasy `(5;4,1)`: `V = 5p + (1−p)(4q + (1−q))`.
Source: `adversary/calibration.md` line 36; mandate T1
Kind: N+ -/
theorem fantasy541_value :
    value (proc2 p q hp0 hp1 hq0 hq1) fantasy541 = 5 * p + (1 - p) * (4 * q + (1 - q)) := by
  unfold fantasy541; rw [twoPoint_value]; ring

/-- FR-12 `(0;0,−1)`: `V = −(1−p)(1−q)`.
Source: `fair-repair.md` line 114; mandate T1
Kind: N+ -/
theorem fr12_value :
    value (proc2 p q hp0 hp1 hq0 hq1) fr12 = -((1 - p) * (1 - q)) := by
  unfold fr12; rw [twoPoint_value]; ring

/-- The threat tree `(1;2,0)`: `V = p + 2(1−p)q`.
Source: `repair/identity.md` line 38; mandate T1
Kind: N+ -/
theorem threat_value :
    value (proc2 p q hp0 hp1 hq0 hq1) threat = p + 2 * (1 - p) * q := by
  unfold threat; rw [twoPoint_value]; ring

end twoPointFamily

end Cleanroom.Decision.DpDevicesCatalog
