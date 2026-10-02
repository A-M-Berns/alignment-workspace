import Cleanroom.Decision.DpReferentsCdt.Rows
import Cleanroom.Decision.DpReferentsCdt.OpaqueBasic
import Cleanroom.Decision.DpLocalOpt.Coherence

/-!
# The learning-Newcomb tree and Proposition A (T9)

`wiki/newcomb-correction.md`'s model, rendered as a `dp-core-tree` tree (mandate §3.5): one point `d`
with acts `one` (`Act2.a`) and `two` (`Act2.b`); worlds `(E, D, K, Ω)` (exploration flag, deliberate
draw, coin, fill); a chance node draws `E ∼ Bern ε` (index `1` = exploration), then the decision
node draws `D` on both branches; on `E = 0` a chance node fills the box "matching `D`" with
probability `r_D`; on `E = 1` a fair coin `K` is drawn, ignored by nothing but the payoff, and the box
is filled matching `K` with probability `r_K`. Payoff `10·[Ω] − [A = one]` with `A := K` on
exploration rounds and `D` otherwise.

The five evaluators of "one-box minus two-box", in closed form for every label `p`, `ε`, `r_D`, `r_K`:
**deviation** `V(δ_one) − V(δ_two) = (1−ε)(20 r_D − 11)`; **ITT** (condition on the draw event
`drew d ·`) `= (1−ε)(20 r_D − 11)` — identically the deviation (dp-core-090); **LICDT** (condition on
`E ∧ A = ·`) `= 20 r_K − 11`; **LIEDT** (condition on `A = ·`) through the two act-conditional fill
probabilities; **single-instance forcing at the `E = 0` node** (`gNode`) `= 20 r_D − 11` — *not* the
`−1` of the note's "forcing" column: on this tree the fill node is downstream of the draw, so
forcing the draw moves the fill (findings F5). **Proposition A**: `V` is affine in `p` with
coefficient `(1−ε)(20 r_D − 11)` (`learn_value`), so the exploration learner one-boxes iff
`r_K > 11/20` and the policy optimum is one-box iff `r_D ≥ 11/20`; the rider on the LICDT
best-response fixed point (`learn_fixed_point_optimal`). The table rows at `p = 1/2`, `ε = 1/10`
(`learn_table_deliberate_sharing`, `learn_table_coin_only`).

The tree is draw-recorded, not act-recorded: ITT conditions on `drew d a`, LICDT/LIEDT on the
realized-act world event, and `learn_not_actRecording` shows F3′ fails for the realized act.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-- Learning-Newcomb worlds `(E, D, K, Ω)`: exploration flag, deliberate draw, coin, fill.
Source: `wiki/newcomb-correction.md` line 15 (the model); mandate §3.5
Kind: D -/
abbrev LearnW : Type := Bool × Act2 × Act2 × Bool

/-- The realized act `A := K` on exploration rounds, `D` otherwise. Source: `newcomb-correction.md`
line 15. Kind: D -/
def learnA (w : LearnW) : Act2 := if w.1 then w.2.2.1 else w.2.1

/-- The payoff `10·[Ω] − [A = one]`. Source: `newcomb-correction.md` line 15 ("post 04's
normalization"). Kind: D -/
def learnPay (w : LearnW) : ℚ := (if w.2.2.2 then 10 else 0) - (if learnA w = .a then 1 else 0)

/-- The fill produced by a "match `x` with probability `r`" chance node: index `0` = match (fill
iff `x = one`), index `1` = mismatch (fill iff `x = two`).
Source: `newcomb-correction.md` line 15 ("matches `D` w.p. `r_D`"); mandate §3.5
Kind: D -/
def learnFill (x : Act2) (i : Fin 2) : Bool := if i = 0 then decide (x = .a) else decide (x = .b)

/-- The coin's act: index `0` = one-box. Source: `newcomb-correction.md` line 15. Kind: D -/
def coinAct (k : Fin 2) : Act2 := if k = 0 then .a else .b

/-- A leaf of the learning tree. Source: mandate §3.5. Kind: D -/
def learnLeaf (e : Bool) (D K : Act2) (fill : Bool) : Tree LearnW Unit (fun _ => Act2) ℚ :=
  .leaf (e, D, K, fill) (learnPay (e, D, K, fill))

section learnTree

variable (ε rD rK : ℚ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hD0 : 0 ≤ rD) (hD1 : rD ≤ 1)
  (hK0 : 0 ≤ rK) (hK1 : rK ≤ 1)

/-- **The learning-Newcomb tree** with an `(r_D, r_K)`-Omega: `E ∼ Bern ε` (chance index `1` =
exploration), then the decision `d` on both branches, then on `E = 0` a chance fill matching `D` with
probability `r_D`, on `E = 1` a fair coin `K` and a chance fill matching `K` with probability `r_K`.
On exploration runs the draw `D` and the realized act `K` differ: the tree is draw-recorded, not
act-recorded (`dp-core-tree`'s `Overwrite` pattern).
Source: `wiki/newcomb-correction.md` line 15 (the model); dp-core-089; dp-core-097; mandate §3.5
Kind: D
Fidelity: variant: the `(r_D, r_K)`-Omega rendered as chance fill nodes downstream of the draw (the
only Definition-6 rendering of "matches `D` with probability `r_D`") -/
def learnTree : Tree LearnW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (1 - ε) (by linarith) (by linarith))
    ![.decision () fun D =>
        .chance 2 (FinDistr.coin rD hD0 hD1) fun i => learnLeaf false D D (learnFill D i),
      .decision () fun D =>
        .chance 2 FinDistr.fair fun k =>
          .chance 2 (FinDistr.coin rK hK0 hK1) fun i =>
            learnLeaf true D (coinAct k) (learnFill (coinAct k) i)]

/-- Sums over the leaves of the learning tree. Source: none: infrastructure. Kind: L -/
theorem learn_sum (f : (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ D, ∑ i, f ⟨0, D, i, ()⟩) + ∑ D, ∑ k, ∑ i, f ⟨1, D, k, i, ()⟩ := by
  unfold learnTree at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (Tree.decision () fun D =>
      Tree.chance 2 (FinDistr.coin rD hD0 hD1) fun i => learnLeaf false D D (learnFill D i)).Leaves,
        f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.decision () fun D => Tree.chance 2 FinDistr.fair fun k =>
      Tree.chance 2 (FinDistr.coin rK hK0 hK1) fun i =>
        learnLeaf true D (coinAct k) (learnFill (coinAct k) i)).Leaves, f ⟨1, ℓ⟩) = _
  congr 1
  · rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  · rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Tree.sum_leaves_leaf _ _ _

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- **`V(C) = (1−ε)[10(1−r_D) + p(20 r_D − 11)] + 9ε/2`**, `p := C(d)(one)`, for every procedure:
the value is affine in the label with coefficient `(1−ε)(20 r_D − 11)`.
Source: `wiki/newcomb-correction.md` Proposition A (`dV/dp = (1−ε)(10(2r_D − 1) − 1)`); dp-core-089;
mandate T9
Kind: P
Fidelity: exact (`dV/dp` read as the coefficient of the affine function) -/
theorem learn_value :
    value C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) =
      (1 - ε) * (10 * (1 - rD) + (C ()).w .a * (20 * rD - 11)) + 9 * ε / 2 := by
  unfold value
  rw [learn_sum]
  simp [learnTree, leafLaw, payoff, learnLeaf, learnPay, learnA, learnFill, coinAct, FinDistr.coin,
    FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, Act2.w_b_eq]
  ring

/-- **Deviation: `V(δ_one) − V(δ_two) = (1−ε)(20 r_D − 11)`**.
Source: `newcomb-correction.md` Proposition A; mandate T9
Kind: P
Fidelity: exact -/
theorem learn_deviation :
    refR1Prior C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) () .a -
      refR1Prior C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) () .b = (1 - ε) * (20 * rD - 11) := by
  unfold refR1Prior
  rw [learn_value, learn_value]
  simp [Proc.deviatePure, Proc.deviate_same]
  ring

/-- The run-space conditional expectation of the payoff on a leaf event (junk `0` at a null event).
Source: `newcomb-correction.md` ("ITT, `E[U ∣ D = 1] − E[U ∣ D = 2]`"); mandate T9
Kind: D -/
def runCondExp {Ω : Type} (B : Tree Ω Unit (fun _ => Act2) ℚ) (S : Finset B.Leaves) : ℚ :=
  (∑ ℓ ∈ S, leafLaw C B ℓ * payoff B ℓ) / mass C B S

/-- The mass of the draw event `drew d a` is `C(d)(a)` (the draw is independent of everything
else). Source: none: infrastructure. Kind: L -/
theorem learn_mass_drew (a : Act2) :
    mass C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (drew () a _) = (C ()).w a := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  unfold mass drew
  rw [Finset.sum_filter, learn_sum]
  cases a <;> simp [learnTree, leafLaw, draws, learnLeaf, FinDistr.coin, FinDistr.fair,
    Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- The payoff mass of the draw event. Source: none: infrastructure. Kind: L -/
theorem learn_paySum_drew (a : Act2) :
    (∑ ℓ ∈ drew () a (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1),
      leafLaw C _ ℓ * payoff _ ℓ) =
      (C ()).w a * ((1 - ε) * (if a = .a then 10 * rD - 1 else 10 * (1 - rD)) + 9 * ε / 2) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  unfold drew
  rw [Finset.sum_filter, learn_sum]
  cases a <;> simp [learnTree, leafLaw, payoff, draws, learnLeaf, learnPay, learnA, learnFill,
    coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- **ITT: `𝔼[U ∣ drew d one] − 𝔼[U ∣ drew d two] = (1−ε)(20 r_D − 11)`** for `0 < p < 1` — identically
the deviation (the exploration branch is independent of the draw).
Source: `newcomb-correction.md` (ITT, "condition on the intention"); dp-core-090 ("ITT = deviation");
mandate T9
Kind: P
Fidelity: exact -/
theorem learn_itt (hp0 : 0 < (C ()).w .a) (hp1 : (C ()).w .a < 1) :
    runCondExp C _ (drew () .a (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1)) -
      runCondExp C _ (drew () .b (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1)) =
      (1 - ε) * (20 * rD - 11) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  have ha' : (C ()).w .a ≠ 0 := hp0.ne'
  have hb' : (C ()).w .b ≠ 0 := by rw [hb]; linarith
  unfold runCondExp
  rw [learn_paySum_drew, learn_paySum_drew, learn_mass_drew, learn_mass_drew,
    mul_div_cancel_left₀ _ ha', mul_div_cancel_left₀ _ hb']
  simp
  ring

/-- The exploration event `{E = 1}`. Source: `newcomb-correction.md` (LICDT). Kind: D -/
def learnE : Finset LearnW := Finset.univ.filter fun w => w.1 = true

/-- The realized-act event `{A = a}`. Source: `newcomb-correction.md` (LICDT, LIEDT). Kind: D -/
def learnAct (a : Act2) : Finset LearnW := Finset.univ.filter fun w => learnA w = a

/-- The fill event `{Ω = 1}`. Source: `newcomb-correction.md`. Kind: D -/
def learnFillEv : Finset LearnW := Finset.univ.filter fun w => w.2.2.2 = true

/-- `ν(E ∧ A = a) = ε/2`. Source: none: infrastructure. Kind: L -/
theorem learn_nu_E_act (a : Act2) :
    nu C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnE ∩ learnAct a) = ε / 2 := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [nu_eq_sum, learn_sum]
  cases a <;> simp [learnTree, leafLaw, world, learnLeaf, learnE, learnAct, learnA, learnFill,
    coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- `∑_{E ∧ A = a} μ r = (ε/2)·(10 r_K − 1)` for `a = one`, `(ε/2)·10(1 − r_K)` for `a = two`.
Source: none: infrastructure. Kind: L -/
theorem learn_paySum_E_act (a : Act2) :
    paySum C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnE ∩ learnAct a) =
      ε / 2 * (if a = .a then 10 * rK - 1 else 10 * (1 - rK)) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [paySum_eq_sum_ite, learn_sum]
  cases a <;> simp [learnTree, leafLaw, world, payoff, learnLeaf, learnPay, learnE, learnAct,
    learnA, learnFill, coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ,
    hb] <;> ring

/-- **LICDT: `𝔼[U ∣ E ∧ A = one] − 𝔼[U ∣ E ∧ A = two] = 20 r_K − 11`** for `ε > 0`, at every label —
the exploration-episode learner tracks the predictor's accuracy on the coin.
Source: `newcomb-correction.md` Proposition A ("LICDT gap `= 10(2r_K − 1) − 1`"); dp-core-089;
mandate T9
Kind: P
Fidelity: exact -/
theorem learn_licdt (hε : 0 < ε) :
    condExp C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnE ∩ learnAct .a) -
      condExp C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnE ∩ learnAct .b) =
      20 * rK - 11 := by
  unfold condExp
  rw [learn_paySum_E_act, learn_paySum_E_act, learn_nu_E_act, learn_nu_E_act]
  have : ε / 2 ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ this, mul_div_cancel_left₀ _ this]
  simp
  ring

/-- `ν(A = a) = (1−ε) C(d)(a) + ε/2`. Source: dp-core-2-011. Kind: L -/
theorem learn_nu_act (a : Act2) :
    nu C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnAct a) = (1 - ε) * (C ()).w a + ε / 2 := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [nu_eq_sum, learn_sum]
  cases a <;> simp [learnTree, leafLaw, world, learnLeaf, learnAct, learnA, learnFill, coinAct,
    FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- **The two act-conditional fill masses of LIEDT** (dp-core-2-011): `ν(Ω ∧ A = one) = (1−ε) p r_D +
(ε/2) r_K`, `ν(Ω ∧ A = two) = (1−ε)(1−p)(1−r_D) + (ε/2)(1−r_K)`.
Source: dp-core-2-011 (the two conditionals); `newcomb-correction.md` (LIEDT); mandate T9
Kind: P
Fidelity: exact -/
theorem learn_nu_fill_act (a : Act2) :
    nu C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnFillEv ∩ learnAct a) =
      (1 - ε) * (C ()).w a * (if a = .a then rD else 1 - rD) +
        ε / 2 * (if a = .a then rK else 1 - rK) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [nu_eq_sum, learn_sum]
  cases a <;> simp [learnTree, leafLaw, world, learnLeaf, learnFillEv, learnAct, learnA,
    learnFill, coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- **LIEDT's act values are `10·P(Ω ∣ A = a) − [a = one]`**, cross-multiplied: `paySum(A = a) =
10·ν(Ω ∧ A = a) − [a = one]·ν(A = a)`.
Source: `newcomb-correction.md` (LIEDT, "`10[P(Ω ∣ A = one) − P(Ω ∣ A = two)] − 1`"); mandate T9
Kind: P
Fidelity: exact (cross-multiplied) -/
theorem learn_paySum_act (a : Act2) :
    paySum C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnAct a) =
      10 * nu C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnFillEv ∩ learnAct a) -
        (if a = .a then 1 else 0) * nu C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) (learnAct a) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [learn_nu_fill_act, learn_nu_act, paySum_eq_sum_ite, learn_sum]
  cases a <;> simp [learnTree, leafLaw, world, payoff, learnLeaf, learnPay, learnAct, learnA,
    learnFill, coinAct, FinDistr.coin, FinDistr.fair, Fin.sum_univ_two, Act2.sum_univ, hb] <;> ring

/-- The `E = 0` decision node. Source: mandate T9 ("forcing at the `E = 0` node"). Kind: D -/
def learnNode0 : (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1).DecNode := ⟨0, none⟩

/-- **Single-instance forcing at the `E = 0` node is `G(one) = 10 r_D − 1`, `G(two) = 10(1 − r_D)`**
(for `ε < 1`): the gap is `20 r_D − 11` — the deviation's coefficient, *not* the `−1` of the note's
"forcing" column, because on this tree the fill node is downstream of the draw (findings F5).
Source: `newcomb-correction.md` ("forcing at the live node, `−1` always") — refuted for this
rendering; dp-core-2-011; mandate T9
Kind: P
Fidelity: exact for the tree; `variant` against the note's forcing column (findings F5) -/
theorem learn_gNode0 (hε : ε < 1) (a : Act2) :
    gNode (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1)
        (NodePolicy.ofProc C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1)) (learnNode0 ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) a =
      if a = .a then 10 * rD - 1 else 10 * (1 - rD) := by
  unfold gNode learnNode0 learnTree
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance, reachNode_chance,
    NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_none, reachNode_decision_none, NodePolicy.ofProc_restrictDecision]
  unfold valueNode
  rw [sum_leaves_chance]
  have h1 : (1 - ε) ≠ 0 := by linarith
  simp [leafLawNode, learnLeaf, learnPay, learnA, learnFill, FinDistr.coin, Fin.sum_univ_two]
  cases a <;> simp <;> field_simp <;> ring

/-- **Proposition A, the optimum**: one-boxing is optimal iff `r_D ≥ 11/20` (for `ε < 1`).
Source: `newcomb-correction.md` Proposition A ("the policy-optimal act is one-box iff
`r_D > 0.55`"); mandate T9
Kind: P
Fidelity: exact (with the tie `r_D = 11/20` included, where both pure labels are optimal) -/
theorem learn_isOptimal_one_iff (hε : ε < 1) :
    IsOptimal (procQ 1 (by norm_num) (by norm_num)) (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) ↔
      11 / 20 ≤ rD := by
  unfold IsOptimal
  constructor
  · intro h
    have := h (procQ 0 (by norm_num) (by norm_num))
    rw [learn_value, learn_value] at this
    simp [procQ] at this
    nlinarith
  · intro hr C'
    rw [learn_value, learn_value]
    simp only [procQ, FinDistr.act2_a]
    have h0 := (C' ()).nonneg .a
    have h1 := FinDistr.w_le_one (C' ()) .a
    have key : 0 ≤ (1 - ε) * (1 - (C' ()).w .a) * (20 * rD - 11) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [key]

/-- **Proposition A, the optimum**: two-boxing is optimal iff `r_D ≤ 11/20` (for `ε < 1`).
Source: `newcomb-correction.md` Proposition A; mandate T9
Kind: P
Fidelity: exact -/
theorem learn_isOptimal_zero_iff (hε : ε < 1) :
    IsOptimal (procQ 0 (by norm_num) (by norm_num)) (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) ↔
      rD ≤ 11 / 20 := by
  unfold IsOptimal
  constructor
  · intro h
    have := h (procQ 1 (by norm_num) (by norm_num))
    rw [learn_value, learn_value] at this
    simp [procQ] at this
    nlinarith
  · intro hr C'
    rw [learn_value, learn_value]
    simp only [procQ, FinDistr.act2_a]
    have h0 := (C' ()).nonneg .a
    have h1 := FinDistr.w_le_one (C' ()) .a
    have key : 0 ≤ (1 - ε) * (C' ()).w .a * (11 - 20 * rD) :=
      mul_nonneg (mul_nonneg (by linarith) h0) (by linarith)
    nlinarith [key]

/-- **The rider (dp-core-2-012)**: the LICDT best-response fixed point — `δ_one` if the LICDT gap is
positive, `δ_two` if negative — is optimal iff the thresholds agree: for `r_K > 11/20`, `δ_one` is
optimal iff `r_D ≥ 11/20`; for `r_K < 11/20`, `δ_two` is optimal iff `r_D ≤ 11/20` (`ε < 1`).
Source: `newcomb-correction.md` Proposition A ("the learner's best-response fixed point is optimal
iff the two thresholds agree"); dp-core-2-012; mandate T9
Kind: C
Fidelity: exact (stated on the two strict sides of the LICDT threshold; at `r_K = 11/20` the
learner is indifferent and no fixed point is singled out) -/
theorem learn_fixed_point_optimal (hε : ε < 1) :
    (11 / 20 < rK → (IsOptimal (procQ 1 (by norm_num) (by norm_num))
        (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) ↔ 11 / 20 ≤ rD)) ∧
    (rK < 11 / 20 → (IsOptimal (procQ 0 (by norm_num) (by norm_num))
        (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) ↔ rD ≤ 11 / 20)) :=
  ⟨fun _ => learn_isOptimal_one_iff ε rD rK hε0 hε1 hD0 hD1 hK0 hK1 hε,
    fun _ => learn_isOptimal_zero_iff ε rD rK hε0 hε1 hD0 hD1 hK0 hK1 hε⟩

/-- The realized-act events as an `actEv` parameter. Source: mandate §3.5. Kind: D -/
def learnActEv : (d : Unit) → Act2 → Finset LearnW := fun _ a => learnAct a

/-- `O_d = ⊤`: the agent sees nothing before acting. Source: `newcomb-correction.md`. Kind: D -/
def learnObs : Unit → Finset LearnW := fun _ => Finset.univ

/-- **The learning tree is not act-recording for the realized act** (for `ε > 0`, `r_K > 0` and a
label with `C(d)(one) > 0`): the exploration branch's `d`-node is not node-action-veridical (below its
`one`-edge lies a leaf whose realized act is the coin's `two`), so the positive exploration run
`(E = 1, D = one, K = two)` passes no node-action-veridical `d`-node. ITT must condition on the draw
event `drew d ·` (Definition 7′), LICDT/LIEDT on the realized-act world event.
Source: dp-core-097 (Definition 7′, draw-recorded); mandate §3.5, §7 trap 8
Kind: N+ -/
theorem learn_not_actRecording (hε : 0 < ε) (hK : 0 < rK) (hp : 0 < (C ()).w .a) :
    ¬ ActRecording learnObs learnActEv C (learnTree ε rD rK hε0 hε1 hD0 hD1 hK0 hK1) () := by
  intro h
  obtain ⟨q, ⟨hq, hnav⟩, -⟩ := h.2 ⟨1, .a, 1, 0, ()⟩ (by
    simp [learnTree, leafLaw, learnLeaf, FinDistr.coin, FinDistr.fair]
    positivity) (by simp [learnObs])
  rw [mem_dNodesOn] at hq
  rcases q with ⟨i, q⟩
  fin_cases i
  · simp [learnTree, edgeOf_chance] at hq
  · rcases q with _ | ⟨D, k, e⟩
    · have := hnav ⟨1, .a, 1, 0, ()⟩ .a (by simp [learnTree, edgeOf_chance, edgeOf_decision_none])
      simp [learnActEv, learnAct, learnA, learnTree, learnLeaf, world, coinAct] at this
    · rcases e with ⟨i', e⟩
      exact e.elim

end learnTree

/-! ## The table rows at `p = 1/2`, `ε = 1/10` -/

section table

/-- The label `p = 1/2`. Source: `clean-source-and-policy-responsiveness.md` §A. Kind: D -/
def procHalf : Proc Unit (fun _ => Act2) ℚ := procQ (1/2) (by norm_num) (by norm_num)

/-- **The deliberate-sharing row `(r_D, r_K) = (1, 1/2)`**: LICDT `−1` (two-box), ITT `81/10`, LIEDT
`8`, deviation `81/10` — the exploration learner two-boxes where one-boxing is worth `8.1` more.
Source: `clean-source-and-policy-responsiveness.md` §A table (deliberate-sharing row); mandate T9
Kind: N+ -/
theorem learn_table_deliberate_sharing :
    let B := learnTree (1/10) 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    condExp procHalf B (learnE ∩ learnAct .a) - condExp procHalf B (learnE ∩ learnAct .b) = -1 ∧
    runCondExp procHalf B (drew () .a B) - runCondExp procHalf B (drew () .b B) = 81/10 ∧
    condExp procHalf B (learnAct .a) - condExp procHalf B (learnAct .b) = 8 ∧
    refR1Prior procHalf B () .a - refR1Prior procHalf B () .b = 81/10 := by
  intro B
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [learn_licdt _ _ _ _ _ _ _ _ _ _ (by norm_num)]; norm_num
  · rw [learn_itt _ _ _ _ _ _ _ _ _ _ (by simp [procHalf, procQ]) (by simp [procHalf, procQ]; norm_num)]
    norm_num
  · unfold condExp
    rw [learn_paySum_act, learn_paySum_act, learn_nu_fill_act, learn_nu_fill_act, learn_nu_act,
      learn_nu_act]
    simp [procHalf, procQ]
    norm_num
  · rw [learn_deviation]; norm_num

/-- **The coin-only row `(r_D, r_K) = (1/2, 1)`**: LICDT `9` (one-box), ITT `−9/10`, deviation
`−9/10`, and `V(δ_one) = 81/20 < 99/20 = V(δ_two)` — the learner one-boxes where two-boxing is
optimal.
Source: `clean-source-and-policy-responsiveness.md` §A table (coin-only row); mandate T9
Kind: N+ -/
theorem learn_table_coin_only :
    let B := learnTree (1/10) (1/2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    condExp procHalf B (learnE ∩ learnAct .a) - condExp procHalf B (learnE ∩ learnAct .b) = 9 ∧
    runCondExp procHalf B (drew () .a B) - runCondExp procHalf B (drew () .b B) = -9/10 ∧
    refR1Prior procHalf B () .a - refR1Prior procHalf B () .b = -9/10 ∧
    value (procQ 1 (by norm_num) (by norm_num)) B = 81/20 ∧
    value (procQ 0 (by norm_num) (by norm_num)) B = 99/20 := by
  intro B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [learn_licdt _ _ _ _ _ _ _ _ _ _ (by norm_num)]; norm_num
  · rw [learn_itt _ _ _ _ _ _ _ _ _ _ (by simp [procHalf, procQ]) (by simp [procHalf, procQ]; norm_num)]
    norm_num
  · rw [learn_deviation]; norm_num
  · rw [learn_value]; simp [procQ]; norm_num
  · rw [learn_value]; simp [procQ]; norm_num

end table

end Cleanroom.Decision.DpReferentsCdt
