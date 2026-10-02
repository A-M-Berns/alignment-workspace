import Cleanroom.Decision.DpDutchBook.WhoBuys
import Cleanroom.Decision.DpCalibration.Mugging

/-!
# T4(b) and T2's witness: the mugging hybrid on `B₁` at the tails node

P12-7's example, made a theorem over the tree: Counterfactual Mugging `B₁` (`mug1 x y`, the
fair coin, the real query on tails, the hypothetical query on heads) at the **tails node**
`mugTails = ⟨0, none⟩`, observation `O_T = {tPay, tRefuse}`. Every `O_T`-run passes that one
node (`mug1_tails_covered`, P12's standing assumption `Covered`), the node is node-action-veridical
(`mug1_tails_nav`), the action events are disjoint, and in fact the point is Definition-7-recorded
for **every** procedure (`mug1_recordsFor_all`; `dp-core-tree` proves it at `C(d) = ½` only).

* **The strictly calibrated tails conditionals** `(e(pay), e(refuse)) = (−x, 0)` (`mugE_a`,
  `mugE_b`) — `condExp` on `mug1`, equal by `rfl` to the calibrated state's `V`.
* **The hybrid cf** `mugHybrid x y a := V_{B₁}(δ_a)`, the R1-prior values `((y − x)/2, 0)` —
  `c`-data in P12's sense ("legal in v2 because supposed desirabilities are primitive data"),
  here *computed* from the tree, and counterfactually calibrated to no `O_T`-conditioned referent.
* **T4(b), the "⇒" of the reviewer's biconditional fails** (`mug1_hybrid_approved_and_bookable`):
  at `(x, y) = (1, 3)` the deterministic payer `δ_pay` is `ApprovedBy` the hybrid (`1 > 0`), yet
  its book gap at its **taken** act is `Δ(pay) = 1·|1 − (−1)| = 2 > 0` — `Δ` read off
  `bookGapExt`, which `bookGapExt_eq` ties to `calibratedState`'s `pr`/`V`.
* **The bettors on this witness** (T2's N+): the myopic bettor prices `V(buy) − V(decline) =
  2 − 2δ` and buys for `δ < 1` (`mug1_myopic_buy_sub_decline`, `mug1_myopic_buys`); the
  sophisticated bettor under the true continuation values `(−1 − δ, −1)` and declines
  (`mug1_sophisticated_values`, `mug1_sophisticated_declines`); with the reverse bet offered
  regardless it buys iff `2δ < 2` (`mug1_regardless_buys_iff`); the book loses `δ` on every
  tails leaf (`mug1_tails_leaf_book`; `−11/10` vs `−1` at `δ = 1/10`) and `δ/2` in value
  (`mug1_book_value`: the reach factor of the tails node is `½`, findings F-C).

Semantics: Definition 6 throughout (`leafLaw`/`nu`/`value`; on `mug1` the two agree,
`dp-core-tree`'s `mug1_agreement`). The counterfactual slot is reduced to act values
(`SupposedVal`, mandate §3.2).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

section muggingTree

variable (x y : ℚ)

/-- **The tails node of `B₁`**: chance index `0` (= `T`), the real query.
Source: [[decision-problems-v2]] Proposition 6; `repair/P12.md` P12-7 ("tails point")
Kind: D -/
def mugTails : (mug1 x y).DecNode := ⟨0, none⟩

/-- The point carried by the tails node. Source: none: infrastructure. Kind: L -/
@[simp] theorem mugTails_pt : pt (mug1 x y) (mugTails x y) = () := rfl

/-- **`Covered` at the tails node, for every procedure**: every positive `O_T`-run passes the
tails node (the heads leaves are off `O_T`). This is P12's standing assumption ("the `d`-node met
on `O_d`-runs"), which fails on nested trees (findings F-D) and holds here.
Source: `repair/P12.md` line 7; P12-7 ("tails point (Definition-7-recorded, FA-18)")
Kind: L -/
theorem mug1_tails_covered (C : Proc Unit (fun _ => Act2) ℚ) :
    Covered C (mug1 x y) (mugTails x y) (mugObs ()) := by
  intro ℓ _ hO
  unfold mug1 at ℓ hO ⊢
  unfold mugTails
  rcases ℓ with ⟨j, act, _⟩
  by_cases hj : j = 0
  · subst hj; simp
  · exfalso
    simp only [world_chance, world_decision, world_leaf] at hO
    cases act <;> simp [mugWorld1, hj, mugObs] at hO

/-- **The tails node is node-action-veridical** (F3′ at the real node): a leaf below its
`a`-edge has its world in `{choice = a}`.
Source: `faithful.md` F3′; P12-7
Kind: L -/
theorem mug1_tails_nav : NodeActionVeridical mugActEv (mug1 x y) (mugTails x y) := by
  intro ℓ act he
  unfold mug1 at ℓ he ⊢
  unfold mugTails at he ⊢
  rcases ℓ with ⟨j, act', _⟩
  by_cases hj : j = 0
  · subst hj
    simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at he
    subst he
    cases act' <;> simp [mugActEv, mugWorld1]
  · simp [edgeOf_chance, hj] at he

/-- The mugging's action events are disjoint (re-proved locally; `dp-core-tree`'s
`mugActEv_disjoint` lives in a heavier module). Source: [[decision-problems-v2]] Definition 3.
Kind: L -/
theorem mug1_disjointActEv : DisjointActEv mugActEv () := by
  intro aa bb hab
  cases aa <;> cases bb <;> simp_all [mugActEv]

/-- **The tails point is Definition-7-recorded for every procedure** (`dp-core-tree`'s
`mug1_recordsFor` states it at `C(d) = ½` only): every positive `O_T`-run passes exactly one
`d`-node, the tails node, which is subtree-veridical and action-veridical with a unique action
event.
Source: [[decision-problems-v2]] Definition 7; `faithful.md` ("`B₁` — F3′ and Def 7"); P12-7
("Definition-7-recorded, FA-18"); mandate T4(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem mug1_recordsFor_all (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsFor mugObs mugActEv C (mug1 x y) () := by
  intro ℓ _ hobs
  unfold mug1 at ℓ hobs ⊢
  rcases ℓ with ⟨i, act, _⟩
  refine ⟨rfl, ?_⟩
  rintro ⟨i', (_ | ⟨bb, q⟩)⟩ hq aa ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      fin_cases i
      · refine ⟨?_, ?_, ?_⟩
        · rintro ⟨j, bb, _⟩ hj
          rw [mem_leavesBelow] at hj
          by_cases hj0 : j = 0
          · subst hj0; cases bb <;> simp [mugObs, mugWorld1]
          · simp [edgeOf_chance, hj0] at hj
        · cases act <;> simp [mugActEv, mugWorld1]
        · intro aa' ha'; cases act <;> cases aa' <;> simp_all [mugActEv, mugWorld1, mugObs]
      · exfalso
        cases act <;> simp [mugObs, mugWorld1] at hobs
    · simp [edgeOf_chance, hi] at ha
  · exact q.elim

/-! ### Masses and payoff masses on `B₁` -/

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- `𝔼_C[r · 1_X]` on `B₁` as an explicit expression (the refuse leaves pay `0`).
Source: none: infrastructure. Kind: L -/
theorem mug1_paySum (X : Finset MugW) :
    paySum C (mug1 x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a * (-x) else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * (C ()).w .a * y else 0) := by
  rw [paySum_eq_sum_ite, mug1_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
  split_ifs <;> ring

/-- `M = ν(O_T) = ½` at the tails node. Source: none: infrastructure. Kind: L -/
theorem mug1_belowMass : belowMass C (mug1 x y) (mugTails x y) (mugObs ()) = 1 / 2 := by
  rw [belowMass_eq_nu _ _ _ _ (mug1_tails_covered x y C), mug1_nu_obs]

/-- `P = 𝔼[r · 1_{O_T}] = −x·q/2` at the tails node. Source: none: infrastructure. Kind: L -/
theorem mug1_belowPay :
    belowPay C (mug1 x y) (mugTails x y) (mugObs ()) = -(x * (C ()).w .a / 2) := by
  rw [belowPay_eq_paySum _ _ _ _ (mug1_tails_covered x y C), mug1_paySum]
  simp [mugObs]; ring

/-- `M_pay = ν(pay ∧ O_T) = q/2` at the tails node. Source: none: infrastructure. Kind: L -/
theorem mug1_belowMassA_a :
    belowMassA C (mug1 x y) (mugTails x y) (mugObs ()) .a = (C ()).w .a / 2 := by
  rw [belowMassA_eq_nu _ _ _ _ mugActEv (mug1_tails_covered x y C) (mug1_tails_nav x y)
    mug1_disjointActEv, mug1_nu]
  simp [mugActEv, mugObs]; ring

/-- `P_pay = 𝔼[r · 1_{pay ∧ O_T}] = −x·q/2` at the tails node. Source: none: infrastructure.
Kind: L -/
theorem mug1_belowPayA_a :
    belowPayA C (mug1 x y) (mugTails x y) (mugObs ()) .a = -(x * (C ()).w .a / 2) := by
  rw [belowPayA_eq_paySum _ _ _ _ mugActEv (mug1_tails_covered x y C) (mug1_tails_nav x y)
    mug1_disjointActEv, mug1_paySum]
  simp [mugActEv, mugObs]; ring

/-! ### The strictly calibrated tails conditionals -/

/-- The strictly calibrated act value at the tails point: `e(a) := 𝔼_μ[r ∣ a ∧ O_T]`.
Source: `repair/P12.md` P12-7 ("strictly calibrated tails conditionals"); Setting (`e := V_{s_d}(a)`)
Kind: D -/
noncomputable def mugE (act : Act2) : ℚ := condExp C (mug1 x y) (mugActEv () act ∩ mugObs ())

/-- `mugE` is the calibrated state's `V` at the tails point, by definition.
Source: none: infrastructure. Kind: L -/
theorem mugE_eq_calibratedState_V (h : 0 < nu C (mug1 x y) (mugObs ())) (act : Act2) :
    (calibratedState C (mug1 x y) (mugObs ()) h).V (mugActEv () act) = mugE x y C act := rfl

/-- **`e(pay) = −x`** at a positive pay weight.
Source: P12-7 ("`(pay, refuse) = (−1, 0)`" at `x = 1`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q` (the guard of the conditional) -/
theorem mugE_a (hq : 0 < (C ()).w .a) : mugE x y C .a = -x := by
  unfold mugE condExp
  rw [mug1_paySum, mug1_nu]
  simp [mugActEv, mugObs]
  field_simp

/-- **`e(refuse) = 0`** (the refuse leaf pays `0`; at `q = 1` the conditional is the junk `0/0 = 0`,
which happens to coincide — the headline uses it only at `0 < 1 − q`).
Source: P12-7
Kind: P
Fidelity: exact at `0 < 1 − q`; the junk value coincides at `q = 1` -/
theorem mugE_b : mugE x y C .b = 0 := by
  unfold mugE condExp
  rw [mug1_paySum]
  simp [mugActEv, mugObs]

/-! ### The hybrid cf and its approval of the payer -/

/-- **The hybrid cf**: the R1-prior values `c(a) := V_{B₁}(δ_a)` — the supposed desirabilities of
a hybrid updateful/updateless agent, `c`-data in P12's sense ("legal in v2 because supposed
desirabilities are primitive data (Remark 1.2(i))"), here computed from the tree.
Source: `repair/P12.md` P12-7 ("hybrid cf calibrated to R1-prior `(V_B(δ_pay), V_B(δ_refuse)) = (1, 0)`")
Kind: D
Fidelity: variant: cf reduced to its act values (`SupposedVal`) -/
def mugHybrid (act : Act2) : ℚ := value (Proc.ofFun fun _ => act) (mug1 x y)

/-- `c(pay) = (y − x)/2`. Source: P12-7; `dp-calibration`'s `mug1_value`. Kind: L -/
theorem mugHybrid_a : mugHybrid x y .a = (y - x) / 2 := by
  unfold mugHybrid; rw [mug1_value]; simp [Proc.ofFun]

/-- `c(refuse) = 0`. Source: P12-7. Kind: L -/
theorem mugHybrid_b : mugHybrid x y .b = 0 := by
  unfold mugHybrid; rw [mug1_value]; simp [Proc.ofFun]

/-- **The hybrid cf approves the deterministic payer** when `x ≤ y` (`c(pay) = (y − x)/2 ≥ 0 = c(refuse)`).
Source: P12-7 ("`δ_pay` *is* `T_CDT`-approved under this cf")
Kind: P
Fidelity: exact
Hyps: (a) `x ≤ y` -/
theorem mug1_payer_approved (hxy : x ≤ y) : ApprovedBy (FinDistr.pure Act2.a) (mugHybrid x y) := by
  intro z hz w
  cases z with
  | a =>
      cases w with
      | a => exact le_rfl
      | b => rw [mugHybrid_a, mugHybrid_b]; linarith
  | b => simp at hz

/-- The hybrid cf disapproves the deterministic refuser when `x < y`.
Source: P12-7. Kind: P. Hyps: (a) `x < y` -/
theorem mug1_refuser_not_approved (hxy : x < y) :
    ¬ ApprovedBy (FinDistr.pure Act2.b) (mugHybrid x y) := by
  intro h
  have := h .b (by simp) .a
  rw [mugHybrid_a, mugHybrid_b] at this
  linarith

/-! ### The book gap at the tails node -/

/-- **`Δ(pay) = q · |c − (−x)|`** at the tails node, for every supposed value `c` and every label
with `0 < q` — `bookGapExt` computed on `mug1`.
Source: P12-7 (`Δ(pay) = 1·|1 − (−1)| = 2`); Setting (`Δ := P_{s_d}(a)|c − e|`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q` -/
theorem mug1_bookGapExt_a (ca : ℚ) (hq : 0 < (C ()).w .a) :
    bookGapExt C (mug1 x y) (mugTails x y) (mugObs ()) .a ca = (C ()).w .a * |ca + x| := by
  unfold bookGapExt
  rw [mug1_belowMass, mug1_belowMassA_a, mug1_belowPayA_a]
  have h1 : -(x * (C ()).w .a / 2) / ((C ()).w .a / 2) = -x := by field_simp
  rw [h1, sub_neg_eq_add]
  ring

/-- **`Δ` at the tails node is `P_{s_T}(pay) · |c − V_{s_T}(pay)|`** at the strictly calibrated
tails state — the mandate's trap ("`Δ` must come out of `calibratedState_V`") met on the witness:
an instance of `bookGapExt_eq`.
Source: mandate T2 (trap), T4(b)
Kind: L
Hyps: (a) `0 < ν(O_T)` (holds: `½`) -/
theorem mug1_bookGapExt_eq_calibrated (h : 0 < nu C (mug1 x y) (mugObs ())) (ca : ℚ) :
    bookGapExt C (mug1 x y) (mugTails x y) (mugObs ()) .a ca =
      (calibratedState C (mug1 x y) (mugObs ()) h).pr (mugActEv () .a) *
        |ca - (calibratedState C (mug1 x y) (mugObs ()) h).V (mugActEv () .a)| :=
  bookGapExt_eq C (mug1 x y) (mugTails x y) (mugObs ()) mugActEv (mug1_tails_covered x y C)
    (mug1_tails_nav x y) mug1_disjointActEv h .a ca

end muggingTree

/-! ### The instance `(x, y) = (1, 3)`, the deterministic payer -/

/-- The deterministic payer `δ_pay`. Source: P12-7 (`q = 1`). Kind: D -/
def mugPayer : Proc Unit (fun _ => Act2) ℚ := Proc.ofFun fun _ => Act2.a

/-- Weights of the payer. Source: none: infrastructure. Kind: L -/
@[simp] theorem mugPayer_w_a : (mugPayer ()).w .a = 1 := by simp [mugPayer, Proc.ofFun]

/-- Weights of the payer. Source: none: infrastructure. Kind: L -/
@[simp] theorem mugPayer_w_b : (mugPayer ()).w .b = 0 := by simp [mugPayer, Proc.ofFun]

/-- **T4(b): "bookable ⇒ not approved" fails** (the "⇒" of the reviewer's "a label is bookable at a
positive act iff it is not `T_CDT`-approved"): on `B₁` at `(x, y) = (1, 3)`, the deterministic
payer is approved by the hybrid cf (`c = (1, 0)`, `1 > 0`), the strictly calibrated tails value
of its taken act is `e(pay) = −1 ≠ 1 = c(pay)`, and its book gap at the **taken** act is
`Δ(pay) = 1·|1 − (−1)| = 2 > 0`. A self-knowing deterministic agent is booked at its own fixed
point with no mixed label and no advice reading.
Source: `repair/P12.md` line 15 (the reviewer's biconditional, "and in general (the mugging
hybrid, P12-7: approved and booked)"); P12-7 (line 46); mandate T4(b)
Kind: N+
Fidelity: exact
Hyps: (c) the hybrid cf's values are `c`-data (P12's "supposed desirabilities are primitive
data"), here computed as the R1-prior values from the tree -/
theorem mug1_hybrid_approved_and_bookable :
    ApprovedBy (mugPayer ()) (mugHybrid 1 3) ∧
    mugHybrid 1 3 .a = 1 ∧ mugE 1 3 mugPayer .a = -1 ∧
    bookGapExt mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) .a (mugHybrid 1 3 .a) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ApprovedBy (FinDistr.pure Act2.a) (mugHybrid 1 3)
    exact mug1_payer_approved 1 3 (by norm_num)
  · rw [mugHybrid_a]; norm_num
  · exact mugE_a 1 3 mugPayer (by rw [mugPayer_w_a]; norm_num)
  · rw [mug1_bookGapExt_a 1 3 mugPayer _ (by rw [mugPayer_w_a]; norm_num), mugHybrid_a,
      mugPayer_w_a]
    norm_num

section bettors

variable (δ : ℚ) (bet : FinDistr ℚ Bool)

/-- The booked act: pay at the one point. Source: P12-7. Kind: D -/
def mugBooked : (e : Unit) → Act2 := fun _ => Act2.a

/-- The sign hypothesis of the T2 theorems at the witness: `s = 1`, `c − e = 1 − (−1) = 2 > 0`.
Source: none: infrastructure. Kind: L -/
theorem mug1_sign :
    (1 : ℚ) * (mugHybrid 1 3 .a -
        belowPayA mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) .a /
          belowMassA mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) .a) =
      |mugHybrid 1 3 .a -
        belowPayA mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) .a /
          belowMassA mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) .a| := by
  rw [mug1_belowPayA_a, mug1_belowMassA_a, mugHybrid_a, mugPayer_w_a]
  norm_num

/-- `0 < M` at the witness. Source: none: infrastructure. Kind: L -/
theorem mug1_hM : 0 < belowMass mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) := by
  rw [mug1_belowMass]; norm_num

/-- `0 < M_pay` at the witness. Source: none: infrastructure. Kind: L -/
theorem mug1_hMa : 0 < belowMassA mugPayer (mug1 1 3) (mugTails 1 3) (mugObs ()) .a := by
  rw [mug1_belowMassA_a, mugPayer_w_a]; norm_num

/-- **The myopic bettor prices `V(buy) − V(decline) = 2 − 2δ`** on the witness (P12-7: "the myopic
bettor buys for `2δ < 2`"): `myopic_buy_sub_decline` with `Δ = 2`.
Source: P12-7; P12-4(i); mandate T2(c), T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) both bets positive; (c) the hybrid's `c` as in `mug1_hybrid_approved_and_bookable` -/
theorem mug1_myopic_buy_sub_decline (hb : 0 < bet.w true) (hd : 0 < bet.w false) :
    condExp (liftProc mugPayer .keep bet)
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (buyEv ∩ betObs (mugObs ())) -
      condExp (liftProc mugPayer .keep bet)
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (declineEv ∩ betObs (mugObs ())) = 2 - 2 * δ := by
  have h := myopic_buy_sub_decline δ (mugHybrid 1 3 .a) 1 mugBooked mugPayer (mug1 1 3)
    (mugTails 1 3) (mugObs ()) bet (mug1_tails_covered 1 3 mugPayer) mug1_hM mug1_hMa hb hd
    mug1_sign
  simp only [mugBooked] at h
  rw [h, mug1_bookGapExt_a 1 3 mugPayer _ (by rw [mugPayer_w_a]; norm_num), mugHybrid_a,
    mugPayer_w_a]
  norm_num

/-- **The myopic bettor buys for `δ < 1`**. Source: P12-7 ("buys for `2δ < 2`"). Kind: N+ -/
theorem mug1_myopic_buys (hb : 0 < bet.w true) (hd : 0 < bet.w false) (hδ : δ < 1) :
    condExp (liftProc mugPayer .keep bet)
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (declineEv ∩ betObs (mugObs ())) <
      condExp (liftProc mugPayer .keep bet)
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (buyEv ∩ betObs (mugObs ())) := by
  have := mug1_myopic_buy_sub_decline δ bet hb hd
  linarith

/-- **The sophisticated bettor's values on the witness**: under the true continuation (sell)
`V(buy) = −1 − δ`, `V(decline) = −1` — so it declines for `δ > 0` (`mug1_sophisticated_declines`).
Source: P12-7 ("the sophisticated bettor needs the 'regardless' clause, as always"); P12-3;
mandate T2(a), T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) both bets positive -/
theorem mug1_sophisticated_values (hb : 0 < bet.w true) (hd : 0 < bet.w false) :
    condExp (liftProc mugPayer .sell bet)
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (buyEv ∩ betObs (mugObs ())) = -1 - δ ∧
      condExp (liftProc mugPayer .sell bet)
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (declineEv ∩ betObs (mugObs ())) = -1 := by
  obtain ⟨h1, h2⟩ := sophisticated_values δ (mugHybrid 1 3 .a) 1 mugBooked mugPayer (mug1 1 3)
    (mugTails 1 3) (mugObs ()) bet (mug1_tails_covered 1 3 mugPayer) mug1_hM hb hd
  rw [mug1_belowPay, mug1_belowMass, mugPayer_w_a] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [h1]; norm_num
  · rw [h2]; norm_num

/-- **The sophisticated bettor declines** on the witness for `δ > 0`: no self-model with weight
on buying is approved at `d_B` under the true continuation.
Source: P12-7; P12-3; mandate T2(a)
Kind: N+
Hyps: (a) both bets positive, `0 < δ` -/
theorem mug1_sophisticated_declines (hb : 0 < bet.w true) (hd : 0 < bet.w false) (hδ : 0 < δ) :
    ¬ ApprovedBy bet (fun bt => condExp (liftProc mugPayer .sell bet)
      (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
      (betEv bt ∩ betObs (mugObs ()))) :=
  sophisticated_not_approved δ (mugHybrid 1 3 .a) 1 mugBooked mugPayer (mug1 1 3) (mugTails 1 3)
    (mugObs ()) bet (mug1_tails_covered 1 3 mugPayer) mug1_hM hb hd hδ

/-- **With the reverse bet offered regardless, the sophisticated bettor buys iff `2δ < 2`** on the
witness (`Δ = 2`).
Source: P12-7 ("needs the 'regardless' clause … (§D, `Δ = 2`)"); mandate T2(b), T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) both bets positive -/
theorem mug1_regardless_buys_iff (hb : 0 < bet.w true) (hd : 0 < bet.w false) :
    condExp (liftProc mugPayer .sell bet)
        (attachBetRegardless δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (declineEv ∩ betObs (mugObs ())) <
      condExp (liftProc mugPayer .sell bet)
        (attachBetRegardless δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3))
        (buyEv ∩ betObs (mugObs ())) ↔ 2 * δ < 2 := by
  rw [regardless_buys_iff δ (mugHybrid 1 3 .a) 1 mugBooked mugPayer (mug1 1 3) (mugTails 1 3)
    (mugObs ()) bet (mug1_tails_covered 1 3 mugPayer) mug1_hM mug1_hMa hb hd mug1_sign]
  simp only [mugBooked]
  rw [mug1_bookGapExt_a 1 3 mugPayer _ (by rw [mugPayer_w_a]; norm_num), mugHybrid_a, mugPayer_w_a]
  norm_num

/-- **The book's value loss is `δ/2`** on the witness: the reach of the tails node is `½`
(findings F-C: the loss is `δ` per run *through the bet point*, `δ·R_{q₀}` in value), against
`V_{B₁}(δ_pay) = 1` for declining.
Source: P12-1 (`−δ`), P12-7 ("leaf-wise loss `δ`"); mandate T1(e)
Kind: N+
Fidelity: stronger: the reach factor explicit -/
theorem mug1_book_value :
    value (liftProc mugPayer .sell (FinDistr.pure true))
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3)) = 1 - δ / 2 ∧
      value (liftProc mugPayer .keep (FinDistr.pure false))
        (attachBet δ (mugHybrid 1 3 .a) 1 mugBooked (mug1 1 3) (mugTails 1 3)) = 1 := by
  have hreach : reach mugPayer (mug1 1 3) (mugTails 1 3) = 1 / 2 := by
    simp [mug1, mugTails, FinDistr.fair, FinDistr.coin]
  have hval : value mugPayer (mug1 1 3) = 1 := by rw [mug1_value]; norm_num
  refine ⟨?_, ?_⟩
  · rw [value_attachBet_book, hreach, hval]; ring
  · rw [value_attachBet_dec, hval]

/-- **The leaf-wise loss on the tails-pay leaf**: buying and selling pays `−1 − δ`, declining and
keeping pays `−1` (P12-7's check: `−11/10` vs `−1` at `δ = 1/10`).
Source: P12-7 ("leaf-wise loss `δ` (checked at `δ = 1/10`: `−11/10` vs `−1`)")
Kind: L -/
theorem mug1_tails_leaf_book :
    betPay δ (mugHybrid 1 3 .a) 1 true true .sell (-1) = -1 - δ ∧
      betPay δ (mugHybrid 1 3 .a) 1 false true .keep (-1) = -1 := by
  rw [mugHybrid_a]; simp [betPay]; ring

/-- **The cf's own sell decision** (P12-7: "CDT at `d′` values pay-keep at `1 − 2δ` and pay-sell at
`1 − δ` and sells"): evaluated at the supposed payoff `r = c`, keeping nets `c − 2δ` and selling
`c − δ`. Arithmetic on `betPay` — `c`-data, not a tree fact (the side is a coordinate of the
extended action, chosen with the act; the true continuation of `C_book` is sell by stipulation).
Source: P12-7
Kind: T
Fidelity: variant: the post-act point `d′` is the side coordinate, not a node -/
theorem supposed_keep_vs_sell (c : ℚ) :
    betPay δ c 1 true true .keep c = c - 2 * δ ∧ betPay δ c 1 true true .sell c = c - δ := by
  simp [betPay]; ring

end bettors

end Cleanroom.Decision.DpDutchBook
