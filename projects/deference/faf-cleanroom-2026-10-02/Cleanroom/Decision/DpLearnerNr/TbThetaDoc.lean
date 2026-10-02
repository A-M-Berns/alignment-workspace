import Cleanroom.Decision.DpCausalConsist.TbTheta
import Cleanroom.Decision.DpCausalConsist.PR
import Cleanroom.Decision.DpLearnerNr.Defs

/-!
# `dp-learner-nr` D3, targets 3(a)–(c) and 4(a): the doc-faithful tree `tbThetaDoc`

**`tbThetaDoc θ`**: the same worlds `TbW := Bool × Act2` and payoff table `tbPay` as
`dp-causal-consist`'s bypass `tbTheta`, the only change being that the `bot` branch (chance index
`0`, weight `θ`) *consults the point `d`* instead of forcing `cross`: payoff `−10` on
`cross ∧ bot`, `+10` on `cross ∧ ¬bot`, `0` on `stay`.

* `tbThetaDoc_value`: `V(q) = 10·q·(1 − 2θ)`; `tbThetaDoc_deviation_cross`: `V(C[d ↦ cross]) = 10 − 20θ`,
  `tbThetaDoc_deviation_stay = 0`; the deviation gap `10(1 − 2θ)` is positive iff `θ < ½` —
  **Proposition 10's rule** "cross iff `10 − 20·P₀(□⊥) > 0`" with `P₀ = θ`
  (`tbThetaDoc_gap_pos_iff`).
* Both trees classify `bot` as non-responsive (`tbThetaDoc_bot_nonResponsive`, with
  `dp-causal-consist`'s `tb_bot_nonResponsive`), and differ only in whether the label controls the
  inconsistent world's act: `ν{bot ∧ cross} = θq` here vs `θ` there (`tbThetaDoc_bot_cross_nu`).
* **The five evaluations at a mixed label** (`tbThetaDoc_five`): act-conditional, NR-cf
  (`kPart` with `exo := bot`), draw-conditional, R2-SIA (`siaSum`) and deviation all equal
  `10 − 20θ`; single-node forcing `gNode` is `−10` at the `bot` node and `10` at the `¬bot` node
  — every evaluator except per-node forcing coincides.
* **Target 4(a)**: the marginal formula with the K-partition state's cells and conditional
  expectations *is* the K-partition value `10 − 20θ` on the bypass tree (`cfMarginal_eq_kPart_tb`),
  hence equals Theorem 2's deviation and differs from Theorem 1's forcing.

Trap (i): `tbThetaDoc` has two `d`-nodes carrying `()`; `count () ≤ 1` on every leaf
(`tbThetaDoc_count_le`), so `AlmostFair` holds, but `gNode` ranges over two nodes and the forcing
row names its node. Trap (ii): this is not a third `TB(θ)` — it imports `dp-causal-consist`'s.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpLocalOpt Cleanroom.Decision.DpCausalConsist
  Finset

/-- **D3 — the doc-faithful tree `tbThetaDoc θ`**: a chance root with weight `θ` on index `0`
(`bot`); on *both* branches the point `d` is consulted and the leaf world is `(bot, a)` with
payoff `tbPay (bot, a)`: `−10` on `(bot, cross)`, `+10` on `(¬bot, cross)`, `0` on `stay`. The
chance children are one lambda in the index (`bot := decide (i = 0)`), as `mug1` is written.
Source: [[tb-theta-shadow]] "Bypass-shaped versus doc-faithful" ("A doc-faithful tree consults
`d` in both worlds: payoff `−10` on cross ∧ `bot`, `+10` on cross ∧ ¬`bot`, `0` on stay");
[[clean-source-and-policy-responsiveness]] §9 C; [[dp-learner-nr-mandate]] D3
Kind: D
Fidelity: exact (of the wiki's description; that the doc's bridge *is* this tree is
ATTRIBUTION-UNVETTED — the doc has no tree) -/
def tbThetaDoc (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : Tree TbW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin θ h0 h1) fun i =>
    .decision () fun a => .leaf (decide (i = 0), a) (tbPay (decide (i = 0), a))

section formulas

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- Sums over the leaves of `tbThetaDoc`: chance index, then action.
Source: none: infrastructure
Kind: L -/
theorem tbThetaDoc_sum (f : (tbThetaDoc θ h0 h1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ a : Act2, f ⟨i, ⟨a, ()⟩⟩ := by
  unfold tbThetaDoc
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `ν` on `tbThetaDoc`. Source: none: infrastructure. Kind: L -/
theorem tbThetaDoc_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset TbW) :
    nu C (tbThetaDoc θ h0 h1) X =
      θ * ((if (true, Act2.a) ∈ X then (C ()).w .a else 0)
            + (if (true, Act2.b) ∈ X then (C ()).w .b else 0))
      + (1 - θ) * ((if (false, Act2.a) ∈ X then (C ()).w .a else 0)
            + (if (false, Act2.b) ∈ X then (C ()).w .b else 0)) := by
  rw [nu_eq_sum, tbThetaDoc_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, tbThetaDoc, FinDistr.coin]
  split_ifs <;> ring

/-- `paySum` on `tbThetaDoc`. Source: none: infrastructure. Kind: L -/
theorem tbThetaDoc_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset TbW) :
    paySum C (tbThetaDoc θ h0 h1) X =
      θ * (if (true, Act2.a) ∈ X then (C ()).w .a * (-10) else 0)
      + (1 - θ) * (if (false, Act2.a) ∈ X then (C ()).w .a * 10 else 0) := by
  rw [paySum_eq_sum_ite, tbThetaDoc_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, tbThetaDoc, FinDistr.coin, tbPay]
  split_ifs <;> ring

/-- **`V(C) = C(d)(cross) · 10(1 − 2θ)` on the doc-faithful tree**, for every procedure.
Source: [[tb-theta-shadow]] "Bypass-shaped versus doc-faithful"; [[dp-learner-nr-mandate]] target 3(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tbThetaDoc_value (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (tbThetaDoc θ h0 h1) = (C ()).w .a * (10 * (1 - 2 * θ)) := by
  have := tbThetaDoc_paySum θ h0 h1 C Finset.univ
  rw [paySum_eq_sum_ite] at this
  unfold value
  simp only [Finset.mem_univ, if_true] at this
  rw [this]; ring

/-- Every run meets `d` at most once (two `d`-nodes, one per path). Source: none: infrastructure. Kind: L -/
theorem tbThetaDoc_count_le (ℓ : (tbThetaDoc θ h0 h1).Leaves) :
    count () (tbThetaDoc θ h0 h1) ℓ ≤ 1 := by
  unfold tbThetaDoc at ℓ ⊢
  rcases ℓ with ⟨i, b, _⟩
  show count () (Tree.decision () fun a => Tree.leaf (decide (i = 0), a)
    (tbPay (decide (i = 0), a)) : Tree TbW Unit (fun _ => Act2) ℚ) ⟨b, ()⟩ ≤ 1
  simp

/-- `tbThetaDoc` is almost fair. Source: none: infrastructure. Kind: L -/
theorem tbThetaDoc_almostFair : AlmostFair (tbThetaDoc θ h0 h1) :=
  fun _ ℓ => tbThetaDoc_count_le θ h0 h1 ℓ

end formulas

/-! ## Target 3(a): the value, the deviation, Proposition 10's rule -/

section deviation

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- `V(q) = 10·q·(1 − 2θ)` at the label `q`. Source: [[dp-learner-nr-mandate]] target 3(a). Kind: L -/
theorem tbThetaDoc_value_procQ :
    value (procQ q q0 q1) (tbThetaDoc θ h0 h1) = 10 * q * (1 - 2 * θ) := by
  rw [tbThetaDoc_value]; simp [procQ]; ring

/-- **The deviation `V(C[d ↦ cross]) = 10 − 20θ`** on the doc-faithful tree, for every label.
Source: [[tb-theta-shadow]] ("Its deviation gap is `10(1−θ) − 10θ = 10(1 − 2θ)`");
[[dp-learner-nr-mandate]] target 3(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tbThetaDoc_deviation_cross (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.a) (tbThetaDoc θ h0 h1) = 10 - 20 * θ := by
  rw [tbThetaDoc_value]; simp [Proc.deviatePure, Proc.deviate]; ring

/-- The deviation `V(C[d ↦ stay]) = 0`. Source: [[dp-learner-nr-mandate]] target 3(a). Kind: L -/
theorem tbThetaDoc_deviation_stay (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.b) (tbThetaDoc θ h0 h1) = 0 := by
  rw [tbThetaDoc_value]; simp [Proc.deviatePure, Proc.deviate]

/-- **The deviation gap is `10(1 − 2θ)`, positive iff `θ < ½` — Proposition 10's rule
"cross iff `10 − 20·P₀(□⊥) > 0`" with `P₀ = θ`** (load-bearing 2).
Source: [[tb-theta-shadow]] ("positive iff `θ < ½` — *verbatim* Proposition 10's rule");
[[two-lesions-doc-2026-09-18]] §7 Proposition 10; [[dp-core-inventory]] 106;
[[dp-learner-nr-mandate]] target 3(a), load-bearing 2
Kind: P
Fidelity: exact (of the wiki's identity; that this tree is the doc's bridge is
ATTRIBUTION-UNVETTED — the doc has no tree)
Hyps: (a) none -/
theorem tbThetaDoc_gap_pos_iff (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.a) (tbThetaDoc θ h0 h1)
        - value (C.deviatePure () Act2.b) (tbThetaDoc θ h0 h1) = 10 * (1 - 2 * θ) ∧
    (0 < value (C.deviatePure () Act2.a) (tbThetaDoc θ h0 h1)
        - value (C.deviatePure () Act2.b) (tbThetaDoc θ h0 h1) ↔ θ < 1 / 2) := by
  rw [tbThetaDoc_deviation_cross, tbThetaDoc_deviation_stay]
  constructor
  · ring
  · constructor <;> intro h <;> linarith

/-- The two gaps side by side: `10(1 − 2θ)` on the doc-faithful tree, `10(1 − θ)` on the bypass
tree (`dp-causal-consist`'s `tb_dev_gap`).
Source: [[tb-theta-shadow]] ("The run's tree is bypass-shaped, with gap `10(1−θ)`; a tree
faithful to the doc's troll gives `10(1 − 2θ)`"); [[dp-learner-nr-mandate]] target 3(a)
Kind: L -/
theorem gaps_doc_vs_bypass (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.a) (tbThetaDoc θ h0 h1)
        - value (C.deviatePure () Act2.b) (tbThetaDoc θ h0 h1) = 10 * (1 - 2 * θ) ∧
    value (C.deviatePure () Act2.a) (tbTheta θ h0 h1)
        - value (C.deviatePure () Act2.b) (tbTheta θ h0 h1) = 10 * (1 - θ) :=
  ⟨(tbThetaDoc_gap_pos_iff θ h0 h1 C).1, tb_dev_gap θ h0 h1 C⟩

end deviation

/-! ## Target 3(b): both trees classify `bot` as non-responsive -/

section responsive

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- `ν_{C[d↦a]}(bot) = θ` on the doc-faithful tree. Source: none: infrastructure. Kind: L -/
theorem tbThetaDoc_bot_dev (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nu (C.deviatePure () a) (tbThetaDoc θ h0 h1) (cell exoBot true) = θ := by
  rw [tbThetaDoc_nu]
  cases a <;> simp [cell, exoBot, Proc.deviatePure, Proc.deviate]

/-- **`bot` is not policy-responsive on the doc-faithful tree** (as on the bypass tree,
`tb_bot_nonResponsive`).
Source: [[tb-theta-shadow]] ("Both trees classify `bot` as non-responsive");
[[dp-learner-nr-mandate]] target 3(b)
Kind: P (a universal statement over every procedure `C`, not a witness; relabelled from N+ at
audit r1)
Fidelity: exact
Hyps: (a) none -/
theorem tbThetaDoc_bot_nonResponsive (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ Responsive C (tbThetaDoc θ h0 h1) () (cell exoBot true) := by
  rw [not_responsive_iff]
  intro a b
  rw [tbThetaDoc_bot_dev, tbThetaDoc_bot_dev]

/-- **The two trees differ in whether the label controls the inconsistent world's act**:
`ν{bot ∧ cross} = θ·q` on the doc-faithful tree and `θ` on the bypass tree. (The wiki's "differ
*only* in" is its sentence, not this theorem's: `ν{bot ∧ stay}` is `θ(1−q)` here and `0` there.)
Source: [[tb-theta-shadow]] ("they differ only in whether the label controls the inconsistent
world's act"); [[dp-learner-nr-mandate]] target 3(b)
Kind: L (two closed-form values; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_bot_cross_nu (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1) :
    nu (procQ q q0 q1) (tbThetaDoc θ h0 h1) {(true, Act2.a)} = θ * q ∧
    nu (procQ q q0 q1) (tbTheta θ h0 h1) {(true, Act2.a)} = θ := by
  constructor
  · rw [tbThetaDoc_nu]; simp [procQ]
  · rw [tbTheta_nu]; simp [Act2.sum_univ]

end responsive

/-! ## Target 3(c): the five evaluations at a mixed label -/

section five

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- The strictly calibrated state of `tbThetaDoc` at label `q`, `O = ⊤`.
Source: [[dp-learner-nr-mandate]] target 3(c)
Kind: D -/
def docState : State TbW ℚ :=
  calibratedState (procQ q q0 q1) (tbThetaDoc θ h0 h1) Finset.univ (nu_univ_pos _ _)

/-- `P_s(X) = ν(X)` at `O = ⊤`. Source: none: infrastructure. Kind: L -/
theorem docState_pr (X : Finset TbW) :
    (docState θ h0 h1 q q0 q1).pr X =
      θ * ((if (true, Act2.a) ∈ X then q else 0) + (if (true, Act2.b) ∈ X then 1 - q else 0))
      + (1 - θ) * ((if (false, Act2.a) ∈ X then q else 0) + (if (false, Act2.b) ∈ X then 1 - q else 0)) := by
  rw [docState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, tbThetaDoc_nu]
  simp [procQ]

/-- `V_s(X) = paySum(X)/ν(X)` at `O = ⊤`. Source: none: infrastructure. Kind: L -/
theorem docState_V (X : Finset TbW) :
    (docState θ h0 h1 q q0 q1).V X =
      (θ * (if (true, Act2.a) ∈ X then q * (-10) else 0)
        + (1 - θ) * (if (false, Act2.a) ∈ X then q * 10 else 0))
      / (θ * ((if (true, Act2.a) ∈ X then q else 0) + (if (true, Act2.b) ∈ X then 1 - q else 0))
        + (1 - θ) * ((if (false, Act2.a) ∈ X then q else 0) + (if (false, Act2.b) ∈ X then 1 - q else 0))) := by
  rw [docState, calibratedState_V, Finset.inter_univ, tbThetaDoc_paySum, tbThetaDoc_nu]
  simp [procQ]

/-- **1. The act-conditional expectation of `cross` is `10 − 20θ`** at every label `q > 0`:
the crossings are `θq` bad and `(1−θ)q` good. At the stay label `q = 0` the crossing event is
null and `condExp` returns the junk `0` (`tbThetaDoc_stay_condExp_junk`), so `0 < q` is
load-bearing.
Source: [[dp-learner-nr-mandate]] target 3(c)
Kind: P (one of the computations behind `tbThetaDoc_five`; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_condExp_cross (hq : 0 < q) :
    condExp (procQ q q0 q1) (tbThetaDoc θ h0 h1) (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * θ := by
  unfold condExp
  rw [tbThetaDoc_paySum, tbThetaDoc_nu]
  simp [DpCausalConsist.tbActEv, procQ]
  have hden : θ * q + (1 - θ) * q = q := by ring
  rw [hden, div_eq_iff hq.ne']
  ring

/-- **2. The K-partition state's value of `cross` is `10 − 20θ`** at every mixed label
(`exo := bot`), on the doc-faithful tree.
Source: [[dp-learner-nr-mandate]] target 3(c) ("NR-cf with `exo := bot` `10 − 20θ`")
Kind: P (one of the computations behind `tbThetaDoc_five`; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_nrcf_cross (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    (kPart (docState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot).V (DpCausalConsist.tbActEv () Act2.a)
      = 10 - 20 * θ := by
  have hθ' : θ ≠ 0 := hθ0.ne'
  have hq' : q ≠ 0 := hq.ne'
  have h1' : (1 - θ) ≠ 0 := by linarith
  rw [kPart_V_of_suppRegular (docState θ h0 h1 q q0 q1)
    (by unfold docState; exact suppRegular_calibratedState _ _ _ _), Fintype.sum_bool,
    Fintype.sum_bool]
  have hcellT : (docState θ h0 h1 q q0 q1).pr (cell exoBot true) = θ := by
    rw [docState_pr]; simp [cell, exoBot]
  have hcellF : (docState θ h0 h1 q q0 q1).pr (cell exoBot false) = 1 - θ := by
    rw [docState_pr]; simp [cell, exoBot]
  have hposT : 0 < (docState θ h0 h1 q q0 q1).pr (DpCausalConsist.tbActEv () Act2.a ∩ cell exoBot true) := by
    rw [docState_pr]; simp [cell, exoBot, DpCausalConsist.tbActEv]; exact mul_pos hθ0 hq
  have hposF : 0 < (docState θ h0 h1 q q0 q1).pr (DpCausalConsist.tbActEv () Act2.a ∩ cell exoBot false) := by
    rw [docState_pr]; simp [cell, exoBot, DpCausalConsist.tbActEv]; exact mul_pos (by linarith) hq
  have hT : (kPartComp (docState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot true).pr (DpCausalConsist.tbActEv () Act2.a) = 1 ∧
      (kPartComp (docState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot true).V (DpCausalConsist.tbActEv () Act2.a) = -10 := by
    unfold kPartComp
    rw [dif_pos hposT, jeffreyCond_pr, jeffreyCond_V, docState_pr, docState_pr, docState_V]
    simp [cell, exoBot, DpCausalConsist.tbActEv]
    constructor <;> (first | exact ⟨hθ', hq'⟩ | exact ⟨h1', hq'⟩ | exact ⟨fun h => hθ1.ne (by linarith), hq'⟩ | (field_simp; ring) | field_simp | ring)
  have hF : (kPartComp (docState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot false).pr (DpCausalConsist.tbActEv () Act2.a) = 1 ∧
      (kPartComp (docState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot false).V (DpCausalConsist.tbActEv () Act2.a) = 10 := by
    unfold kPartComp
    rw [dif_pos hposF, jeffreyCond_pr, jeffreyCond_V, docState_pr, docState_pr, docState_V]
    simp [cell, exoBot, DpCausalConsist.tbActEv]
    constructor <;> (first | exact ⟨hθ', hq'⟩ | exact ⟨h1', hq'⟩ | exact ⟨fun h => hθ1.ne (by linarith), hq'⟩ | (field_simp; ring) | field_simp | ring)
  rw [hcellT, hcellF, hT.1, hT.2, hF.1, hF.2]
  ring

/-- The payoff mass of the runs that drew `cross` on the doc-faithful tree: `q·(10 − 20θ)`.
Source: none: infrastructure
Kind: L -/
theorem tbThetaDoc_drew_paySum :
    ∑ ℓ ∈ drew () Act2.a (tbThetaDoc θ h0 h1), leafLaw (procQ q q0 q1) (tbThetaDoc θ h0 h1) ℓ
        * payoff (tbThetaDoc θ h0 h1) ℓ = q * (10 - 20 * θ) := by
  unfold drew
  rw [Finset.sum_filter, tbThetaDoc_sum]
  simp [Fin.sum_univ_two, tbThetaDoc, FinDistr.coin, procQ, tbPay]
  ring

/-- The mass of the runs that drew `cross` on the doc-faithful tree: `q`.
Source: none: infrastructure
Kind: L -/
theorem tbThetaDoc_drew_mass :
    mass (procQ q q0 q1) (tbThetaDoc θ h0 h1) (drew () Act2.a (tbThetaDoc θ h0 h1)) = q := by
  unfold drew mass
  rw [Finset.sum_filter, tbThetaDoc_sum]
  simp [Fin.sum_univ_two, tbThetaDoc, FinDistr.coin, procQ]
  ring

/-- **3. The draw-conditional expectation of `cross` is `10 − 20θ`** on the doc-faithful tree
(every crossing is a draw; contrast `tb_drawCondExp_cross = 10` on the bypass tree).
Source: [[tb-theta-shadow]] "Five evaluations" (`E[U | draw = cross] = 8` at `θ = 1/10`);
[[dp-causal-consist]] finding F5 ("the note's `10 − 20θ` belongs to the doc-faithful tree");
[[dp-learner-nr-mandate]] target 3(c)
Kind: P (one of the computations behind `tbThetaDoc_five`; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_drawCondExp_cross (hq : 0 < q) :
    drawCondExp (procQ q q0 q1) (tbThetaDoc θ h0 h1) () Act2.a = 10 - 20 * θ := by
  unfold drawCondExp
  rw [tbThetaDoc_drew_paySum, tbThetaDoc_drew_mass, div_eq_iff hq.ne']; ring

/-- **4. R2-SIA (`siaSum`) of `cross` is `10 − 20θ`**: the two `d`-nodes contribute `θ·(−10)` and
`(1 − θ)·10`.
Source: [[dp-learner-nr-mandate]] target 3(c) ("R2-SIA (`siaSum`) `10 − 20θ` (the two `d`-nodes
contribute `(1−θ)·10` and `θ·(−10)`)")
Kind: P (one of the computations behind `tbThetaDoc_five`; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_siaSum (C : Proc Unit (fun _ => Act2) ℚ) :
    siaSum C (tbThetaDoc θ h0 h1) () Act2.a = 10 - 20 * θ := by
  unfold tbThetaDoc
  rw [siaSum_chance, Fin.sum_univ_two]
  simp only [siaSum_decision_self, siaSum_leaf, mul_zero, Finset.sum_const_zero, zero_add,
    value_leaf, FinDistr.coin]
  simp [tbPay]
  ring

/-- **Single-node forcing at the `bot` node `⟨0, none⟩` is `−10`** (`θ > 0`).
Source: [[dp-learner-nr-mandate]] target 3(c) ("single-node forcing `gNode` is … `−10` at the
`bot` node"); trap (i) (two `d`-nodes — the row names its node)
Kind: P (one of the computations behind `tbThetaDoc_five`; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_gNode_bot (hθ : 0 < θ) (C : Proc Unit (fun _ => Act2) ℚ) :
    gNode (tbThetaDoc θ h0 h1) (NodePolicy.ofProc C _) ⟨0, none⟩ Act2.a = -10 := by
  unfold gNode tbThetaDoc
  rw [forcedBelow_chance, reachNode_chance]
  show (FinDistr.coin θ h0 h1).w 0 * forcedBelow (Tree.decision () fun a => Tree.leaf (decide ((0 : Fin 2) = 0), a)
      (tbPay (decide ((0 : Fin 2) = 0), a)) : Tree TbW Unit (fun _ => Act2) ℚ) _ none Act2.a
    / ((FinDistr.coin θ h0 h1).w 0 * reachNode (Tree.decision () fun a => Tree.leaf (decide ((0 : Fin 2) = 0), a)
      (tbPay (decide ((0 : Fin 2) = 0), a)) : Tree TbW Unit (fun _ => Act2) ℚ) _ none) = -10
  rw [forcedBelow_decision_none, reachNode_decision_none]
  show (FinDistr.coin θ h0 h1).w 0 * (∑ ℓ : Unit, 1 * tbPay (decide ((0 : Fin 2) = 0), Act2.a))
    / ((FinDistr.coin θ h0 h1).w 0 * 1) = -10
  have : (FinDistr.coin θ h0 h1).w 0 = θ := by simp [FinDistr.coin]
  rw [this]
  simp [tbPay]
  field_simp

/-- **Single-node forcing at the `¬bot` node `⟨1, none⟩` is `10`** (`θ < 1`).
Source: [[dp-learner-nr-mandate]] target 3(c) ("`10` at the `¬bot` node")
Kind: P (one of the computations behind `tbThetaDoc_five`; relabelled from N+ at audit r1) -/
theorem tbThetaDoc_gNode_nobot (hθ : θ < 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    gNode (tbThetaDoc θ h0 h1) (NodePolicy.ofProc C _) ⟨1, none⟩ Act2.a = 10 := by
  unfold gNode tbThetaDoc
  rw [forcedBelow_chance, reachNode_chance]
  show (FinDistr.coin θ h0 h1).w 1 * forcedBelow (Tree.decision () fun a => Tree.leaf (decide ((1 : Fin 2) = 0), a)
      (tbPay (decide ((1 : Fin 2) = 0), a)) : Tree TbW Unit (fun _ => Act2) ℚ) _ none Act2.a
    / ((FinDistr.coin θ h0 h1).w 1 * reachNode (Tree.decision () fun a => Tree.leaf (decide ((1 : Fin 2) = 0), a)
      (tbPay (decide ((1 : Fin 2) = 0), a)) : Tree TbW Unit (fun _ => Act2) ℚ) _ none) = 10
  rw [forcedBelow_decision_none, reachNode_decision_none]
  show (FinDistr.coin θ h0 h1).w 1 * (∑ ℓ : Unit, 1 * tbPay (decide ((1 : Fin 2) = 0), Act2.a))
    / ((FinDistr.coin θ h0 h1).w 1 * 1) = 10
  have : (FinDistr.coin θ h0 h1).w 1 = 1 - θ := by simp [FinDistr.coin]
  rw [this]
  have hne : (1 - θ) ≠ 0 := by linarith
  simp [tbPay]
  field_simp

/-- **The five evaluations of `cross` on the doc-faithful tree at a mixed label** (load-bearing 2,
target 3(c)): act-conditional, NR-cf (K-partition with `exo := bot`), draw-conditional, R2-SIA
and deviation all equal `10 − 20θ`; single-node forcing is `−10` at the `bot` node and `10` at
the `¬bot` node. Every evaluator except per-node forcing coincides — the companion of
`dp-causal-consist`'s `tb_five`, where on the bypass tree they split.
Source: [[tb-theta-shadow]] "Five evaluations of 'cross'" (the table, whose middle three rows
are the doc-faithful values); [[non-responsiveness-learnability]] §8 D; [[dp-core-inventory]]
106; [[dp-learner-nr-mandate]] target 3(c)
Kind: P
Fidelity: exact (at a mixed label where every conditional is defined; the NR-cf row is the
K-partition *state's* value, as in `tb_five`)
Hyps: (a) `0 < θ < 1`, `0 < q` -/
theorem tbThetaDoc_five (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    condExp (procQ q q0 q1) (tbThetaDoc θ h0 h1) (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * θ ∧
    (kPart (docState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot).V (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * θ ∧
    drawCondExp (procQ q q0 q1) (tbThetaDoc θ h0 h1) () Act2.a = 10 - 20 * θ ∧
    siaSum (procQ q q0 q1) (tbThetaDoc θ h0 h1) () Act2.a = 10 - 20 * θ ∧
    value ((procQ q q0 q1).deviatePure () Act2.a) (tbThetaDoc θ h0 h1) = 10 - 20 * θ ∧
    gNode (tbThetaDoc θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨0, none⟩ Act2.a = -10 ∧
    gNode (tbThetaDoc θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨1, none⟩ Act2.a = 10 :=
  ⟨tbThetaDoc_condExp_cross θ h0 h1 q q0 q1 hq, tbThetaDoc_nrcf_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq,
    tbThetaDoc_drawCondExp_cross θ h0 h1 q q0 q1 hq, tbThetaDoc_siaSum θ h0 h1 _,
    tbThetaDoc_deviation_cross θ h0 h1 _, tbThetaDoc_gNode_bot θ h0 h1 hθ0 _,
    tbThetaDoc_gNode_nobot θ h0 h1 hθ1 _⟩

end five

section junk

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- **The `0 < q` guards are load-bearing**: at the untrembled stay label the crossing event of
`tbThetaDoc` is null, and `condExp`/`nuCond` return the junk `0` — not `10 − 20θ` and not `θ`.
No headline of this package claims a value at a null event; this lemma records the fact so the
hypotheses `0 < q` (`tbThetaDoc_condExp_cross`, `tbThetaDoc_five`) and `0 < ε`
(`tbThetaDoc_tremble`) are seen to exclude exactly this. Adopted from audit r1's `DocJunk` probe.
Source: [[dp-learner-nr-audit-r1-adversarial]] §3 item 14; [[STANDARDS]] §3 (junk values)
Kind: L -/
theorem tbThetaDoc_stay_condExp_junk :
    nu (procQ 0 le_rfl zero_le_one) (tbThetaDoc θ h0 h1) (DpCausalConsist.tbActEv () Act2.a) = 0 ∧
    condExp (procQ 0 le_rfl zero_le_one) (tbThetaDoc θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      = 0 ∧
    nuCond (procQ 0 le_rfl zero_le_one) (tbThetaDoc θ h0 h1) (cell exoBot true)
      (DpCausalConsist.tbActEv () Act2.a) = 0 := by
  have hnu : nu (procQ 0 le_rfl zero_le_one) (tbThetaDoc θ h0 h1)
      (DpCausalConsist.tbActEv () Act2.a) = 0 := by
    rw [tbThetaDoc_nu]; simp [DpCausalConsist.tbActEv, procQ]
  refine ⟨hnu, ?_, ?_⟩
  · unfold condExp
    rw [hnu, div_zero]
  · unfold nuCond
    rw [tbThetaDoc_nu, tbThetaDoc_nu]
    simp [cell, exoBot, DpCausalConsist.tbActEv, procQ]

end junk

/-! ## Target 4(a): the marginal formula is the K-partition value -/

section marginalKGeneral

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {E : Type} [Fintype E] [DecidableEq E]

/-- The response table read off a state on an arbitrary event `A` and partition `exo`:
`E(e) := V_s(A ∧ cell e)`, the state's conditional expectation of the payoff on `A ∧ cell e`.
Source: [[dp-learner-nr-mandate]] target 4(a) ("`E a e` is the state's conditional expectation
on the cell")
Kind: D -/
def stateEOn (s : State Ω ℚ) (A : Finset Ω) (exo : Ω → E) (e : E) : ℚ := s.V (A ∩ cell exo e)

omit [Fintype Ω] in
/-- `A ∩ (A ∩ C) = A ∩ C`. Source: none: infrastructure. Kind: L -/
theorem inter_inter_self_left (A C : Finset Ω) : A ∩ (A ∩ C) = A ∩ C := by
  ext ω; simp

/-- **The marginal formula is the K-partition value, in general** (target 4(a), the structural
identity): on every support-regular state `s` whose every positive cell of `exo` meets `A`
positively, D2 fed the state's cell marginal `P_s(cell e)` and cell conditionals
`V_s(A ∧ cell e)` *is* the K-partition state's value of `A`:
`∑_e P_s(e) · V_s(A ∧ e) = (kPart s A exo).V A`. Through `dp-causal-consist`'s `kPart` unchanged
(`kPart_V_of_suppRegular`, `jeffreyCond_pr` = `1` on `A`, `jeffreyCond_V`). The `tbTheta` instance
`cfMarginal_eq_kPart_tb` is derived from this lemma; adopted from audit r1's `KPartGeneral` probe.
Source: [[non-responsiveness]] "Axiom NR" ("the dependency-hypothesis / K-partition form");
[[marginal-formula-learner]] ("on the tree it is CDT with the logical state in the fixed
algebra"); [[dp-core-inventory]] 088(a); [[dp-learner-nr-mandate]] target 4(a)
Kind: L (`kPart_V_of_suppRegular` then, per cell, `jeffreyCond_pr`/`jeffreyCond_V` and
`cellDistr.sum_one` — one unfolding per cell rather than a multi-step composition; relabelled from
C at audit r2)
Fidelity: exact (through `kPart` unchanged; the hypothesis `hpos` is what makes every cell's
Jeffrey conditional on `A` defined — at a null `A ∧ cell e` the K-partition component is the junk
default and the identity is not claimed; it *fails* there: `cfMarginal_ne_kPart_stay`,
`KPartStay.lean`)
Hyps: (a) `SuppRegular s`; (a) every positive cell meets `A` positively -/
theorem cfMarginal_eq_kPart_general (s : State Ω ℚ) (hs : SuppRegular s) (A : Finset Ω)
    (exo : Ω → E) (hpos : ∀ e, 0 < s.pr (cell exo e) → 0 < s.pr (A ∩ cell exo e)) :
    ∑ e, (cellDistr s exo).w e * stateEOn s A exo e = (kPart s A exo).V A := by
  rw [kPart_V_of_suppRegular s hs]
  have hcomp : ∀ e, s.pr (cell exo e) * (kPartComp s A exo e).pr A = s.pr (cell exo e) ∧
      s.pr (cell exo e) * (kPartComp s A exo e).pr A * (kPartComp s A exo e).V A
        = s.pr (cell exo e) * s.V (A ∩ cell exo e) := by
    intro e
    rcases lt_or_eq_of_le (probOf_nonneg s.P (cell exo e) : (0 : ℚ) ≤ s.pr (cell exo e))
      with he | he
    · have h1 := hpos e he
      unfold kPartComp
      rw [dif_pos h1, jeffreyCond_pr, jeffreyCond_V, inter_inter_self_left, div_self h1.ne']
      constructor <;> ring
    · have he' : s.pr (cell exo e) = 0 := he.symm
      rw [he']
      constructor <;> ring
  have hnum : ∑ e, s.pr (cell exo e) * (kPartComp s A exo e).pr A * (kPartComp s A exo e).V A
      = ∑ e, s.pr (cell exo e) * s.V (A ∩ cell exo e) :=
    Finset.sum_congr rfl fun e _ => (hcomp e).2
  have hden : ∑ e, s.pr (cell exo e) * (kPartComp s A exo e).pr A = 1 := by
    rw [Finset.sum_congr rfl fun e _ => (hcomp e).1]
    exact (cellDistr s exo).sum_one
  rw [hnum, hden, div_one]
  rfl

end marginalKGeneral

section marginalK

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- The response table read off a state: `E(a, e) := V_s(act a ∧ cell e)`, the state's
conditional expectation of the payoff on the cell.
Source: [[dp-learner-nr-mandate]] target 4(a) ("`E a e` is the state's conditional expectation
on the cell")
Kind: D -/
def stateE (s : State TbW ℚ) (a : Act2) (e : Bool) : ℚ := s.V (DpCausalConsist.tbActEv () a ∩ cell exoBot e)

/-- `P_s(bot) = θ`, `P_s(¬bot) = 1 − θ` for the bypass tree's state. Source: none: infrastructure. Kind: L -/
theorem tbState_cells :
    (tbState θ h0 h1 q q0 q1).pr (cell exoBot true) = θ ∧
    (tbState θ h0 h1 q q0 q1).pr (cell exoBot false) = 1 - θ := by
  constructor
  · rw [tbState_pr]; simp [cell, exoBot]
  · rw [tbState_pr]; simp [cell, exoBot]

/-- The state's conditional expectations on the two cells: `−10` on `cross ∧ bot`, `10` on
`cross ∧ ¬bot` (bypass tree, mixed label). Source: none: infrastructure. Kind: L -/
theorem tbState_stateE (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    stateE (tbState θ h0 h1 q q0 q1) Act2.a true = -10 ∧
    stateE (tbState θ h0 h1 q q0 q1) Act2.a false = 10 := by
  have hθ' : θ ≠ 0 := hθ0.ne'
  have hq' : q ≠ 0 := hq.ne'
  have h1' : (1 - θ) ≠ 0 := by linarith
  constructor
  · unfold stateE; rw [tbState_V]; simp [cell, exoBot, DpCausalConsist.tbActEv]
    first | (field_simp; ring) | field_simp | ring
  · unfold stateE; rw [tbState_V]; simp [cell, exoBot, DpCausalConsist.tbActEv]
    first | (field_simp; ring) | field_simp | ring

/-- Both cells of the bypass tree's state meet the crossing event positively at a mixed label
(`θ` on `bot`, `(1−θ)q` on `¬bot`). Source: none: infrastructure. Kind: L -/
theorem tbState_cross_cells_pos (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    ∀ e, 0 < (tbState θ h0 h1 q q0 q1).pr (cell exoBot e) →
      0 < (tbState θ h0 h1 q q0 q1).pr (DpCausalConsist.tbActEv () Act2.a ∩ cell exoBot e) := by
  intro e _
  cases e <;> (rw [tbState_pr]; simp [cell, exoBot, DpCausalConsist.tbActEv])
  · exact mul_pos (by linarith) hq
  · exact hθ0

/-- **The marginal formula is Axiom NR's K-partition value** (target 4(a)): on the bypass tree at
a mixed label with `exo := bot`, `cfMarginal (cellDistr s exo) (stateE s) cross = (kPart s cross
exo).V cross = 10 − 20θ`. D2 fed the state's cell marginal and cell conditionals *is* the
K-partition value — "the marginal formula selects the deviation referent". The first conjunct is
the instance of the structural identity `cfMarginal_eq_kPart_general` (since audit r1; before,
both sides were computed to `10 − 20θ` and equated); the second is the numeral, via
`tbState_cells`/`tbState_stateE`.
Source: [[non-responsiveness]] "Axiom NR" ("the dependency-hypothesis / K-partition form");
[[marginal-formula-learner]] ("on the tree it is CDT with the logical state in the fixed
algebra"); [[dp-core-inventory]] 088(a), 106; [[dp-learner-nr-mandate]] target 4(a)
Kind: C
Fidelity: exact (through `dp-causal-consist`'s `kPart` unchanged; the identity is
`cfMarginal_eq_kPart_general`, the numeral `tb_nrcf_cross`'s). At the stay label `q = 0` the
identity fails — D2 fed the state's cells is `−10θ` and the K-partition value is `−10`
(`cfMarginal_ne_kPart_stay`, `KPartStay.lean`) — so `0 < q` is load-bearing; `dp-causal-consist`'s
`cfNR_ne_kPart` (findings F4) is about `NRAt`'s `cf`, a different object, and is not the stay-label
fact here
Hyps: (a) `0 < θ < 1`, `0 < q` -/
theorem cfMarginal_eq_kPart_tb (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    cfMarginal (cellDistr (tbState θ h0 h1 q q0 q1) exoBot) (stateE (tbState θ h0 h1 q q0 q1)) Act2.a
      = (kPart (tbState θ h0 h1 q q0 q1) (DpCausalConsist.tbActEv () Act2.a) exoBot).V (DpCausalConsist.tbActEv () Act2.a) ∧
    cfMarginal (cellDistr (tbState θ h0 h1 q q0 q1) exoBot) (stateE (tbState θ h0 h1 q q0 q1)) Act2.a
      = 10 - 20 * θ := by
  obtain ⟨hcT, hcF⟩ := tbState_cells θ h0 h1 q q0 q1
  obtain ⟨hET, hEF⟩ := tbState_stateE θ h0 h1 q q0 q1 hθ0 hθ1 hq
  have hcf : cfMarginal (cellDistr (tbState θ h0 h1 q q0 q1) exoBot)
      (stateE (tbState θ h0 h1 q q0 q1)) Act2.a = 10 - 20 * θ := by
    unfold cfMarginal
    rw [Fintype.sum_bool]
    show (tbState θ h0 h1 q q0 q1).pr (cell exoBot true) * stateE _ Act2.a true
      + (tbState θ h0 h1 q q0 q1).pr (cell exoBot false) * stateE _ Act2.a false = _
    rw [hcT, hcF, hET, hEF]; ring
  refine ⟨?_, hcf⟩
  have hs : SuppRegular (tbState θ h0 h1 q q0 q1) := by
    unfold tbState; exact suppRegular_calibratedState _ _ _ _
  exact cfMarginal_eq_kPart_general (tbState θ h0 h1 q q0 q1) hs
    (DpCausalConsist.tbActEv () Act2.a) exoBot (tbState_cross_cells_pos θ h0 h1 q q0 q1 hθ0 hθ1 hq)

/-- The marginal formula equals Theorem 2's deviation and differs from Theorem 1's forcing on
the bypass tree (through `kpart_cross_eq_deviation`, `kpart_cross_ne_forcing`).
Source: [[non-responsiveness]] ("NR-cf `= V_B(C[d ↦ cross])`, Theorem 2's deviation, `≠`
Theorem 1's forcing `G_q = 10`"); [[dp-learner-nr-mandate]] target 4(a)
Kind: C
Hyps: (a) `0 < θ < 1`, `0 < q` -/
theorem cfMarginal_deviation_ne_forcing_tb (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    cfMarginal (cellDistr (tbState θ h0 h1 q q0 q1) exoBot) (stateE (tbState θ h0 h1 q q0 q1)) Act2.a
      = value ((procQ q q0 q1).deviatePure () Act2.a) (tbTheta θ h0 h1) ∧
    cfMarginal (cellDistr (tbState θ h0 h1 q q0 q1) exoBot) (stateE (tbState θ h0 h1 q q0 q1)) Act2.a
      ≠ gNode (tbTheta θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨1, none⟩ Act2.a := by
  rw [(cfMarginal_eq_kPart_tb θ h0 h1 q q0 q1 hθ0 hθ1 hq).1]
  exact ⟨kpart_cross_eq_deviation θ h0 h1 q q0 q1 hθ0 hθ1 hq,
    kpart_cross_ne_forcing θ h0 h1 q q0 q1 hθ0 hθ1 hq⟩

end marginalK

end Cleanroom.Decision.DpLearnerNr
