import Cleanroom.Decision.DpReferentsCdt.Learning

/-!
# The label-probe Omega: the learning-Newcomb tree whose predictor is a simulation

Mandate §3.5 and T9 (label-probe Omega): the `Ω` chance nodes of `learnTree` are replaced by a
**simulation** — a second `d`-node running the agent's whole exploration mechanism (its own
exploration flag `E'`, deliberate draw `D' ∼ C(d)` and coin `K'`), whose realized act fills the box.
Under Definition 6 this is the only way a tree reads the label (Proposition 4): the predictor's
fill is an independent draw from the same mechanism, so `P(Ω) = q_ε := (1−ε) p + ε/2 = P(A = one)`.

**Closed forms** (every procedure `C`, `p := C(d)(one)`): `V = 9 q_ε` (`probe_value`); the full
deviation `V(δ_one) − V(δ_two) = 9(1−ε)` (`probe_deviation`), so `dV/dp = 9(1−ε)`; ITT on the
real agent's deliberate draw `D` is `−(1−ε)` (`probe_itt`: the fill is independent of `D`, only the
realized act moves); LICDT `= −1` (`probe_licdt`) and LIEDT `= −1` (`probe_liedt`): every evaluator
that conditions on the realized act sees no effect on the fill. ITT ≠ deviation here (dp-core-090's
wedge: the simulation makes the label causally live while the draw is not), and single-instance
forcing at the real `E = 0` node has gap exactly `−1` (`probe_gNode_real0`), the note's "forcing
`−1` always" — on this rendering, where the fill is upstream of the real draw (findings F5); forcing
the *simulation's* draw instead has gap `+10` (`probe_gNode_sim0`), the term Theorem 1's SIA weighting
adds.

**Draw vs run-level `drew`.** The tree passes two `d`-nodes on every run (the simulation's and the
real agent's), so `dp-core-tree`'s run event `drew d a` ("some `d`-node took the `a`-edge") conflates
the simulation's draw with the agent's; ITT conditions on the world coordinate `D` (the real agent's
deliberate draw, Definition 7′'s draw coordinate), stated as the world event `probeD a`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-- Probe worlds `(Ω, E, D, K)`: fill, the real agent's exploration flag, deliberate draw, coin.
Source: mandate §3.5 (label-probe Omega); handoff item 2
Kind: D -/
abbrev ProbeW : Type := Bool × Bool × Act2 × Act2

/-- The real agent's realized act `A := K` on exploration rounds, `D` otherwise.
Source: `newcomb-correction.md` line 15. Kind: D -/
def probeA (w : ProbeW) : Act2 := if w.2.1 then w.2.2.2 else w.2.2.1

/-- The payoff `10·[Ω] − [A = one]`. Source: `newcomb-correction.md` line 15. Kind: D -/
def probePay (w : ProbeW) : ℚ := (if w.1 then 10 else 0) - (if probeA w = .a then 1 else 0)

/-- A leaf of the probe tree. Source: mandate §3.5. Kind: D -/
def probeLeaf (Ω e : Bool) (D K : Act2) : Tree ProbeW Unit (fun _ => Act2) ℚ :=
  .leaf (Ω, e, D, K) (probePay (Ω, e, D, K))

section probe

variable (ε : ℚ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)

/-- The real agent's subtree once the box is filled (`Ω`): `E ∼ Bern ε`, the decision `d` on both
branches, the coin `K` on the exploration branch.
Source: mandate §3.5; `learnTree`'s real side
Kind: D -/
def probeReal (Ω : Bool) : Tree ProbeW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (1 - ε) (by linarith) (by linarith))
    ![.decision () fun D => probeLeaf Ω false D D,
      .decision () fun D => .chance 2 FinDistr.fair fun k => probeLeaf Ω true D (coinAct k)]

/-- **The label-probe tree**: the simulation (`E' ∼ Bern ε`, a `d`-node drawing `D'`, the coin `K'`
on its exploration branch) fills the box with its realized act, then the real agent plays
`probeReal`. Every run passes two `d`-nodes.
Source: mandate §3.5 ("replace the `Ω` chance nodes by a second `d`-node (a simulation) whose draw
fills the box"); dp-core-090; dp-core-2-012
Kind: D
Fidelity: variant: the simulation runs the full exploration mechanism (flag, draw, coin), so that
`P(Ω) = P(A = one)`; the mandate's "trembled procedure at both nodes" is the tremble encoding of the
same device, not built -/
def probeTree : Tree ProbeW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (1 - ε) (by linarith) (by linarith))
    ![.decision () fun D' => probeReal ε hε0 hε1 (decide (D' = .a)),
      .decision () fun D' =>
        .chance 2 FinDistr.fair fun k' => probeReal ε hε0 hε1 (decide (coinAct k' = .a))]

/-- Sums over the leaves of the real agent's subtree. Source: none: infrastructure. Kind: L -/
theorem probeReal_sum (Ω : Bool) (f : (probeReal ε hε0 hε1 Ω).Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ D, f ⟨0, D, ()⟩) + ∑ D, ∑ k, f ⟨1, D, k, ()⟩ := by
  unfold probeReal at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have h0 : (∑ ℓ : (Tree.decision () fun D => probeLeaf Ω false D D).Leaves, f ⟨0, ℓ⟩) =
      ∑ D, f ⟨0, D, ()⟩ :=
    (sum_leaves_decision (M := ℚ) _).trans
      (Finset.sum_congr rfl fun D _ => Tree.sum_leaves_leaf _ _ _)
  have h1 : (∑ ℓ : (Tree.decision () fun D => Tree.chance 2 FinDistr.fair fun k =>
      probeLeaf Ω true D (coinAct k)).Leaves, f ⟨1, ℓ⟩) = ∑ D, ∑ k, f ⟨1, D, k, ()⟩ :=
    (sum_leaves_decision (M := ℚ) _).trans
      (Finset.sum_congr rfl fun D _ => (sum_leaves_chance (M := ℚ) _).trans
        (Finset.sum_congr rfl fun k _ => Tree.sum_leaves_leaf _ _ _))
  show (∑ ℓ : (Tree.decision () fun D => probeLeaf Ω false D D).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.decision () fun D => Tree.chance 2 FinDistr.fair fun k =>
      probeLeaf Ω true D (coinAct k)).Leaves, f ⟨1, ℓ⟩) = _
  rw [h0, h1]

/-- Sums over the leaves of the probe tree, simulation paths outermost.
Source: none: infrastructure. Kind: L -/
theorem probe_sum (f : (probeTree ε hε0 hε1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ D', ∑ ℓ, f ⟨0, D', ℓ⟩) + ∑ D', ∑ k', ∑ ℓ, f ⟨1, D', k', ℓ⟩ := by
  unfold probeTree at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have h0 : (∑ ℓ : (Tree.decision () fun D' => probeReal ε hε0 hε1 (decide (D' = .a))).Leaves,
      f ⟨0, ℓ⟩) = ∑ D', ∑ ℓ, f ⟨0, D', ℓ⟩ :=
    sum_leaves_decision (M := ℚ) _
  have h1 : (∑ ℓ : (Tree.decision () fun D' => Tree.chance 2 FinDistr.fair fun k' =>
      probeReal ε hε0 hε1 (decide (coinAct k' = .a))).Leaves, f ⟨1, ℓ⟩) =
      ∑ D', ∑ k', ∑ ℓ, f ⟨1, D', k', ℓ⟩ :=
    (sum_leaves_decision (M := ℚ) _).trans
      (Finset.sum_congr rfl fun D' _ => sum_leaves_chance (M := ℚ) _)
  show (∑ ℓ : (Tree.decision () fun D' => probeReal ε hε0 hε1 (decide (D' = .a))).Leaves,
      f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.decision () fun D' => Tree.chance 2 FinDistr.fair fun k' =>
      probeReal ε hε0 hε1 (decide (coinAct k' = .a))).Leaves, f ⟨1, ℓ⟩) = _
  rw [h0, h1]

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- **`V(C) = 9 q_ε`**, `q_ε := (1−ε) p + ε/2`, `p := C(d)(one)`: the box is filled with probability
`q_ε` (the simulation's realized act) and the agent one-boxes with the same probability.
Source: mandate T9 (label-probe Omega: "`value = 9 q_ε`"); dp-core-090
Kind: P
Fidelity: exact -/
theorem probe_value :
    value C (probeTree ε hε0 hε1) = 9 * ((1 - ε) * (C ()).w .a + ε / 2) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  unfold value
  rw [probe_sum]
  simp only [probeReal_sum]
  simp [probeTree, probeReal, leafLaw, payoff, probeLeaf, probePay, probeA, coinAct, FinDistr.coin,
    FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb]
  ring

/-- **Deviation: `V(δ_one) − V(δ_two) = 9(1−ε)`** — the coefficient of the affine value in the label
(`dV/dp = 9(1−ε)`): deviating all instances moves the simulation too.
Source: mandate T9 ("deviation `9(1−ε)`"); dp-core-090
Kind: P
Fidelity: exact -/
theorem probe_deviation :
    refR1Prior C (probeTree ε hε0 hε1) () .a - refR1Prior C (probeTree ε hε0 hε1) () .b =
      9 * (1 - ε) := by
  unfold refR1Prior
  rw [probe_value, probe_value]
  simp [Proc.deviatePure, Proc.deviate_same]
  ring

/-- The world event "the real agent's deliberate draw is `a`" (Definition 7′'s draw coordinate).
Source: dp-core-097 (Definition 7′); mandate §3.5, §7 trap 8
Kind: D -/
def probeD (a : Act2) : Finset ProbeW := Finset.univ.filter fun w => w.2.2.1 = a

/-- The exploration event `{E = 1}` of the real agent. Source: `newcomb-correction.md`. Kind: D -/
def probeE : Finset ProbeW := Finset.univ.filter fun w => w.2.1 = true

/-- The realized-act event `{A = a}`. Source: `newcomb-correction.md`. Kind: D -/
def probeAct (a : Act2) : Finset ProbeW := Finset.univ.filter fun w => probeA w = a

/-- `ν(D = a) = C(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem probe_nu_D (a : Act2) : nu C (probeTree ε hε0 hε1) (probeD a) = (C ()).w a := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [nu_eq_sum, probe_sum]
  simp only [probeReal_sum]
  cases a <;> simp [probeTree, probeReal, leafLaw, world, probeLeaf, probeD, coinAct,
    FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- `∑_{D = a} μ r = C(d)(a) · (10 q_ε − ((1−ε)[a = one] + ε/2))`: the fill is independent of the
draw. Source: none: infrastructure. Kind: L -/
theorem probe_paySum_D (a : Act2) :
    paySum C (probeTree ε hε0 hε1) (probeD a) =
      (C ()).w a * (10 * ((1 - ε) * (C ()).w .a + ε / 2) -
        ((1 - ε) * (if a = .a then 1 else 0) + ε / 2)) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [paySum_eq_sum_ite, probe_sum]
  simp only [probeReal_sum]
  cases a <;> simp [probeTree, probeReal, leafLaw, world, payoff, probeLeaf, probePay, probeA,
    probeD, coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- **ITT on the deliberate draw: `𝔼[U ∣ D = one] − 𝔼[U ∣ D = two] = −(1−ε)`** for `0 < p < 1` — not
the deviation's `9(1−ε)`: the fill is an independent draw from the label, so conditioning on the
agent's draw moves only the realized act (dp-core-090's wedge between ITT and deviation).
Source: mandate T9 (label-probe Omega: "ITT `−(1−ε)`"); dp-core-090
Kind: P
Fidelity: exact (ITT conditions on the world coordinate `D`, see the module docstring)
Hyps: (a) `0 < p < 1` -/
theorem probe_itt (hp0 : 0 < (C ()).w .a) (hp1 : (C ()).w .a < 1) :
    condExp C (probeTree ε hε0 hε1) (probeD .a) - condExp C (probeTree ε hε0 hε1) (probeD .b) =
      -(1 - ε) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  have ha' : (C ()).w .a ≠ 0 := hp0.ne'
  have hb' : (C ()).w .b ≠ 0 := by rw [hb]; linarith
  unfold condExp
  rw [probe_paySum_D, probe_paySum_D, probe_nu_D, probe_nu_D, mul_div_cancel_left₀ _ ha',
    mul_div_cancel_left₀ _ hb']
  simp

/-- `ν(E ∧ A = a) = ε/2`. Source: none: infrastructure. Kind: L -/
theorem probe_nu_E_act (a : Act2) :
    nu C (probeTree ε hε0 hε1) (probeE ∩ probeAct a) = ε / 2 := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [nu_eq_sum, probe_sum]
  simp only [probeReal_sum]
  cases a <;> simp [probeTree, probeReal, leafLaw, world, probeLeaf, probeE, probeAct, probeA,
    coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- `∑_{E ∧ A = a} μ r = (ε/2)(10 q_ε − [a = one])`. Source: none: infrastructure. Kind: L -/
theorem probe_paySum_E_act (a : Act2) :
    paySum C (probeTree ε hε0 hε1) (probeE ∩ probeAct a) =
      ε / 2 * (10 * ((1 - ε) * (C ()).w .a + ε / 2) - if a = .a then 1 else 0) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [paySum_eq_sum_ite, probe_sum]
  simp only [probeReal_sum]
  cases a <;> simp [probeTree, probeReal, leafLaw, world, payoff, probeLeaf, probePay, probeE,
    probeAct, probeA, coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ,
    hb] <;> ring

/-- **LICDT `= −1`** for `ε > 0`, at every label: on exploration rounds the fill is independent of the
coin, so the exploration learner sees exactly the dollar.
Source: mandate T9 (label-probe Omega: "LICDT `= LIEDT = −1`"); dp-core-090
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε` -/
theorem probe_licdt (hε : 0 < ε) :
    condExp C (probeTree ε hε0 hε1) (probeE ∩ probeAct .a) -
      condExp C (probeTree ε hε0 hε1) (probeE ∩ probeAct .b) = -1 := by
  unfold condExp
  rw [probe_paySum_E_act, probe_paySum_E_act, probe_nu_E_act, probe_nu_E_act]
  have : ε / 2 ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ this, mul_div_cancel_left₀ _ this]
  simp

/-- `ν(A = a) = (1−ε) C(d)(a) + ε/2`. Source: none: infrastructure. Kind: L -/
theorem probe_nu_act (a : Act2) :
    nu C (probeTree ε hε0 hε1) (probeAct a) = (1 - ε) * (C ()).w a + ε / 2 := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [nu_eq_sum, probe_sum]
  simp only [probeReal_sum]
  cases a <;> simp [probeTree, probeReal, leafLaw, world, probeLeaf, probeAct, probeA, coinAct,
    FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- `∑_{A = a} μ r = ν(A = a) · (10 q_ε − [a = one])`: the fill is independent of the realized act.
Source: none: infrastructure. Kind: L -/
theorem probe_paySum_act (a : Act2) :
    paySum C (probeTree ε hε0 hε1) (probeAct a) =
      ((1 - ε) * (C ()).w a + ε / 2) *
        (10 * ((1 - ε) * (C ()).w .a + ε / 2) - if a = .a then 1 else 0) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [paySum_eq_sum_ite, probe_sum]
  simp only [probeReal_sum]
  cases a <;> simp [probeTree, probeReal, leafLaw, world, payoff, probeLeaf, probePay, probeAct,
    probeA, coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- **LIEDT `= −1`** for `ε > 0`, at every label: the evidential learner conditioning on the realized
act sees the fill as independent of it (the simulation's draw is a separate draw from the label).
Source: mandate T9 (label-probe Omega: "LICDT `= LIEDT = −1`"); dp-core-2-011
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε` -/
theorem probe_liedt (hε : 0 < ε) :
    condExp C (probeTree ε hε0 hε1) (probeAct .a) - condExp C (probeTree ε hε0 hε1) (probeAct .b) =
      -1 := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  have ha : (1 - ε) * (C ()).w .a + ε / 2 ≠ 0 := by
    have := (C ()).nonneg .a
    have : 0 ≤ (1 - ε) * (C ()).w .a := mul_nonneg (by linarith) this
    positivity
  have hb' : (1 - ε) * (C ()).w .b + ε / 2 ≠ 0 := by
    have := (C ()).nonneg .b
    have : 0 ≤ (1 - ε) * (C ()).w .b := mul_nonneg (by linarith) this
    positivity
  unfold condExp
  rw [probe_paySum_act, probe_paySum_act, probe_nu_act, probe_nu_act, mul_div_cancel_left₀ _ ha,
    mul_div_cancel_left₀ _ hb']
  simp

/-! ## Single-instance forcing: the real `E = 0` node and the simulation node -/

/-- The real agent's `E = 0` node on the simulation path `E' = 0, D' = x`.
Source: mandate T9 ("forcing at the `E = 0` node"); handoff item 2
Kind: D -/
def probeRealNode0 (x : Act2) : (probeTree ε hε0 hε1).DecNode := ⟨0, some ⟨x, ⟨0, none⟩⟩⟩

/-- The simulation's `E' = 0` node. Source: mandate T9. Kind: D -/
def probeSimNode0 : (probeTree ε hε0 hε1).DecNode := ⟨0, none⟩

/-- **Forcing at the real `E = 0` node is `G(a) = 10·[x = one] − [a = one]`** (for `ε < 1` and
`C(d)(x) > 0`, `x` the simulation's draw on that path): the fill is upstream and fixed, so the gap is
exactly `−1` — the note's "forcing `−1` always", realized on the label-probe rendering (contrast
`learn_gNode0` on the `(r_D, r_K)` rendering, where the fill is downstream and the gap is
`20 r_D − 11`; findings F5).
Source: `newcomb-correction.md` ("forcing at the live node, `−1` always"); mandate T9; handoff item 2
Kind: P
Fidelity: exact for the tree
Hyps: (a) `ε < 1`, (a) `0 < C(d)(x)` -/
theorem probe_gNode_real0 (hε : ε < 1) (x : Act2) (hx : 0 < (C ()).w x) (a : Act2) :
    gNode (probeTree ε hε0 hε1) (NodePolicy.ofProc C (probeTree ε hε0 hε1))
        (probeRealNode0 ε hε0 hε1 x) a =
      (if x = .a then 10 else 0) - (if a = .a then 1 else 0) := by
  unfold gNode probeRealNode0 probeTree
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance, reachNode_chance,
    NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_some, reachNode_decision_some, NodePolicy.ofProc_none,
    NodePolicy.ofProc_restrictDecision]
  unfold probeReal
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance, reachNode_chance,
    NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_none, reachNode_decision_none, NodePolicy.ofProc_restrictDecision]
  unfold valueNode probeLeaf
  rw [Tree.sum_leaves_leaf]
  have h1 : (1 - ε) ≠ 0 := by linarith
  have hx' : (C ()).w x ≠ 0 := hx.ne'
  simp [leafLawNode, probePay, probeA, FinDistr.coin]
  cases x <;> cases a <;> simp <;> field_simp <;> ring

/-- **Forcing the simulation's `E' = 0` draw** gives `G(a') = 10·[a' = one] − q_ε` (for `ε < 1`): gap
`+10`, the term that Theorem 1's reach-weighted sum over *all* `d`-nodes adds to the real node's `−1`
(`(1−ε)·10 + (1−ε)·(−1) = 9(1−ε)`, the deviation).
Source: mandate T9; [[decision-problems-v2]] §8 Theorem 1 (the simulation's forcing in the SIA sum)
Kind: P
Fidelity: exact for the tree
Hyps: (a) `ε < 1` -/
theorem probe_gNode_sim0 (hε : ε < 1) (a' : Act2) :
    gNode (probeTree ε hε0 hε1) (NodePolicy.ofProc C (probeTree ε hε0 hε1))
        (probeSimNode0 ε hε0 hε1) a' =
      (if a' = .a then 10 else 0) - ((1 - ε) * (C ()).w .a + ε / 2) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  unfold gNode probeSimNode0 probeTree
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance, reachNode_chance,
    NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_none, reachNode_decision_none, NodePolicy.ofProc_restrictDecision,
    valueNode_ofProc]
  have h1 : (1 - ε) ≠ 0 := by linarith
  have hv : ∀ Ω : Bool, value C (probeReal ε hε0 hε1 Ω) =
      (if Ω then 10 else 0) - ((1 - ε) * (C ()).w .a + ε / 2) := by
    intro Ω
    unfold value
    rw [probeReal_sum]
    cases Ω <;> simp [probeReal, leafLaw, payoff, probeLeaf, probePay, probeA, coinAct,
      FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring
  rw [hv]
  cases a' <;> simp [FinDistr.coin] <;> field_simp

end probe

/-! ## The `(1/2, 1/10)` row -/

/-- **The label-probe row at `p = 1/2`, `ε = 1/10`**: `V = 9 q_ε = 9/2`, deviation `81/10`, ITT
`−9/10`, LICDT `−1`, LIEDT `−1`, forcing gap at the real `E = 0` node `−1`.
Source: `clean-source-and-policy-responsiveness.md` §A table (label-probe row); mandate T9
Kind: N+ -/
theorem probe_table_row :
    let B := probeTree (1/10) (by norm_num) (by norm_num)
    value procHalf B = 9/2 ∧
    refR1Prior procHalf B () .a - refR1Prior procHalf B () .b = 81/10 ∧
    condExp procHalf B (probeD .a) - condExp procHalf B (probeD .b) = -9/10 ∧
    condExp procHalf B (probeE ∩ probeAct .a) - condExp procHalf B (probeE ∩ probeAct .b) = -1 ∧
    condExp procHalf B (probeAct .a) - condExp procHalf B (probeAct .b) = -1 ∧
    gNode B (NodePolicy.ofProc procHalf B) (probeRealNode0 _ _ _ .a) .a -
      gNode B (NodePolicy.ofProc procHalf B) (probeRealNode0 _ _ _ .a) .b = -1 := by
  intro B
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [probe_value]; simp [procHalf, procQ]; norm_num
  · rw [probe_deviation]; norm_num
  · rw [probe_itt _ _ _ _ (by simp [procHalf, procQ]) (by simp [procHalf, procQ]; norm_num)]
    norm_num
  · rw [probe_licdt _ _ _ _ (by norm_num)]
  · rw [probe_liedt _ _ _ _ (by norm_num)]
  · rw [probe_gNode_real0 _ _ _ _ (by norm_num) .a (by simp [procHalf, procQ]),
      probe_gNode_real0 _ _ _ _ (by norm_num) .a (by simp [procHalf, procQ])]
    simp

end Cleanroom.Decision.DpReferentsCdt
