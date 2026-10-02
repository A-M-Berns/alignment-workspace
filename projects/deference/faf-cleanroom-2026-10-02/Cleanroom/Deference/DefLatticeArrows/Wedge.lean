import Cleanroom.Deference.DefLatticeArrows.Partition
import Cleanroom.Found.DefLattice.TwoOptionFinite

/-!
# T9 — Soft threshold-0 Total Trust is strictly weaker than the hard threshold-0 cut: the wedge

Package `def-lattice-arrows`, file 11. lean-deference-2-015 (the 07-23 arc): "the ramp is `0`
at the boundary", so a bet whose expert-estimate is `≥ 0` but possibly `= 0` gets nothing from
the soft threshold-0 cut, while DDB's hard cut with `≥` covers it; the *wedge*
`0 < E*(D) ≤ δ` is where the hard indicator is `1` and the ramp still climbs.

Finite-exact separation over two worlds, with novice weights `π ≥ 0`, expert estimates `e` and
a bet `X`:
* soft cut at width `δ`: `0 ≤ ∑_w π_w X_w ctsInd δ (e_w) 0`; hard cut:
  `0 ≤ ∑_w π_w X_w 1[0 ≤ e_w]`;
* **(a) the boundary witness** `e = (0, 1)`, `X = (−1, 1)`, `π = (9/10, 1/10)`: every soft cut
  at every `δ > 0` holds, the hard cut fails (`−8/10`);
* **(b) the wedge at fixed `δ ≤ 1`** `e = (δ/2, 1)`, `π = (3/5, 2/5)`: the soft cut at width `δ`
  holds (`1/10`), the hard cut fails (`−1/5`), and the soft cut at width `δ/2` **fails** too — the
  separation is per width; only the boundary case separates at all widths.
* The one-sidedness clauses: on a frame with `e ≥ 0` the hard threshold-0 cut is
  `E_π(X) ≥ 0`; the soft cut's summand vanishes wherever `e = 0`.
* The boundary novice endorses the hedged strategy (`E_π(X · ctsInd δ e 0) ≥ 0`) yet fails hard
  two-option Value at `0` (def-lattice's `twoOption_identity_above` at `s = 0`).

`π` need not be a probability (the identities need no normalization).

**Finding (imprecision):** the chat names the amplifier as the intended witness; the amplifier
passes every hard cut including threshold `0` (li-asymp-calc `amp_upper_cut` at `t = 0`,
`∫_0^1 amp c = ½ ≥ 0`), so it is not a soft-but-not-hard threshold-0 witness. (a) is.
-/

namespace Cleanroom.Deference.DefLatticeArrows.Wedge

open LogicalInduction Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.DefLattice.TwoOptionFinite Cleanroom.Deference.DefLatticeArrows

noncomputable section

/-- The soft threshold-0 cut at width `δ` on a finite frame.
Source: lean-deference-2-015; [[deference-notions]] §Total Trust (finite form)
Kind: D
Fidelity: exact -/
def softCut {W : Type*} [Fintype W] (π e X : W → ℝ) (δ : ℚ) : ℝ :=
  ∑ w, π w * (X w * ctsInd δ (e w) 0)

/-- The hard threshold-0 cut (DDB's `≥` form) on a finite frame.
Source: [[Deference Done Better]] l. 175 at `t = 0`; lean-deference-2-015
Kind: D
Fidelity: exact -/
def hardCut {W : Type*} [Fintype W] (π e X : W → ℝ) : ℝ :=
  ∑ w, π w * (X w * if 0 ≤ e w then 1 else 0)

/-- **One-sidedness, hard**: where every estimate is `≥ 0`, the hard threshold-0 cut is the
unconditional expectation `E_π(X)` (provable-bound respect at `0`).
Source: lean-deference-2-015 (msg 16: "the conditioning event is everything")
Kind: L
Fidelity: exact -/
theorem hardCut_of_nonneg {W : Type*} [Fintype W] (π e X : W → ℝ) (he : ∀ w, 0 ≤ e w) :
    hardCut π e X = ∑ w, π w * X w := by
  unfold hardCut
  exact Finset.sum_congr rfl (fun w _ => by simp [he w])

/-- **One-sidedness, soft**: the soft summand vanishes wherever the estimate is exactly `0`
(`ctsInd δ 0 0 = 0`) — the ramp gives no guarantee at the boundary.
Source: lean-deference-2-015 (msg 24: "`Ind_δ(x > t) = 0` at `x = t` exactly")
Kind: L
Fidelity: exact -/
theorem softCut_summand_zero {W : Type*} [Fintype W] (π e X : W → ℝ) (δ : ℚ) (w : W)
    (hw : e w = 0) : π w * (X w * ctsInd δ (e w) 0) = 0 := by
  rw [hw, ctsInd_self]; ring

/-! ### (a) The boundary witness -/

/-- Boundary estimates `(0, 1)`.
Source: mandate T9 (a)
Kind: D
Fidelity: n/a -/
def eB : Fin 2 → ℝ := ![0, 1]

/-- The bet `(−1, 1)`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def XB : Fin 2 → ℝ := ![-1, 1]

/-- Boundary novice weights `(9/10, 1/10)`.
Source: mandate T9 (a)
Kind: D
Fidelity: n/a -/
def πB : Fin 2 → ℝ := ![9 / 10, 1 / 10]

/-- **(a) The boundary novice passes every soft threshold-0 cut at every width, on this bet**
(`X = (−1, 1)`; the frame is one bet, not soft threshold-0 Total Trust as a predicate over
all bets): the world with estimate `0` contributes nothing (`ctsInd_self`) and the other has
`X = 1`.
Source: lean-deference-2-015; mandate T9 (a)
Kind: N+
Fidelity: exact
Hyps: (a) none (`0 < δ` not even needed) -/
theorem boundary_soft (δ : ℚ) : 0 ≤ softCut πB eB XB δ := by
  simp only [softCut, Fin.sum_univ_two, πB, eB, XB]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ctsInd_self]
  have := ctsInd_nonneg δ 1 0
  nlinarith

/-- **(a) The boundary novice fails the hard threshold-0 cut**: `−9/10 + 1/10 = −8/10`.
Source: lean-deference-2-015; mandate T9 (a)
Kind: N+
Fidelity: exact -/
theorem boundary_hard_fails : hardCut πB eB XB = -8 / 10 := by
  simp [hardCut, Fin.sum_univ_two, πB, eB, XB]
  norm_num

/-- **(a) The boundary novice endorses the hedged strategy at `0`** — the hedged two-option
strategy `X · ctsInd δ (e) 0 + 0 · (1 − ctsInd …)` has nonnegative expectation (this is
`boundary_soft` read through the two-option identity, T7).
Source: lean-deference-2-015 ("endorses the hedged strategy"); [[two-option-value-iff-total-trust]]
Kind: L
Fidelity: exact -/
theorem boundary_hedged_endorsed (δ : ℚ) :
    0 ≤ ∑ w, πB w * (XB w * ctsInd δ (eB w) 0 + 0 * (1 - ctsInd δ (eB w) 0)) := by
  have := boundary_soft δ
  unfold softCut at this
  simpa using this

/-- **(a) … yet fails hard two-option Value at `0`**: the hard-argmax strategy on `{X, const 0}`
(def-lattice's `twoOptionStrategy`) has negative expectation, by the two-option identity at
`s = 0`.
Source: lean-deference-2-015 ("fails hard Value"); def-lattice `twoOption_identity_above`
Kind: N+
Fidelity: exact -/
theorem boundary_hard_value_fails :
    ∑ w, πB w * twoOptionStrategy eB XB 0 w < 0 * ∑ w, πB w := by
  have h := twoOption_identity_above πB eB XB 0
  have h' : ∑ w, πB w * (XB w - 0) * (if (0 : ℝ) ≤ eB w then 1 else 0) = hardCut πB eB XB := by
    unfold hardCut
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [h', boundary_hard_fails] at h
  linarith

/-! ### (b) The wedge at a fixed width -/

/-- Wedge estimates `(δ/2, 1)`.
Source: mandate T9 (b)
Kind: D
Fidelity: n/a -/
def eW (δ : ℚ) : Fin 2 → ℝ := ![(δ : ℝ) / 2, 1]

/-- Wedge novice weights `(3/5, 2/5)`.
Source: mandate T9 (b)
Kind: D
Fidelity: n/a -/
def πW : Fin 2 → ℝ := ![3 / 5, 2 / 5]

/-- **(b) The wedge novice passes the soft cut at width `δ`** (`0 < δ ≤ 1`):
`−3/5 · ½ + 2/5 · 1 = 1/10`.
Source: mandate T9 (b)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < δ ≤ 1` -/
theorem wedge_soft {δ : ℚ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : softCut πW (eW δ) XB δ = 1 / 10 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have h1 : ctsInd δ ((δ : ℝ) / 2) 0 = 1 / 2 := by
    rw [ctsInd_eq_div hδ (by linarith) (by linarith), sub_zero, div_div, mul_comm, ← div_div,
      div_self hδR.ne']
  have h2 : ctsInd δ 1 0 = 1 := by
    rw [ctsInd_eq_one_iff hδ]
    have : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
    linarith
  simp only [softCut, Fin.sum_univ_two, πW, eW, XB, Matrix.cons_val_zero, Matrix.cons_val_one,
    h1, h2]
  norm_num

/-- **(b) The wedge novice fails the hard cut**: `−3/5 + 2/5 = −1/5`.
Source: mandate T9 (b)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < δ` -/
theorem wedge_hard_fails {δ : ℚ} (hδ : 0 < δ) : hardCut πW (eW δ) XB = -1 / 5 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have h0 : (0 : ℝ) ≤ (δ : ℝ) / 2 := by linarith
  simp [hardCut, Fin.sum_univ_two, πW, eW, XB, h0]
  norm_num

/-- **(b) The wedge novice fails the soft cut at width `δ/2`**: the ramp of width `δ/2` is
already `1` at `δ/2`, so the soft cut coincides with the hard one, `−1/5`. The separation is
per width.
Source: mandate T9 (b) ("the soft cut at width `δ/2` fails too")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < δ ≤ 1` -/
theorem wedge_soft_half_fails {δ : ℚ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    softCut πW (eW δ) XB (δ / 2) = -1 / 5 := by
  have hδ2 : (0 : ℚ) < δ / 2 := by positivity
  have h1 : ctsInd (δ / 2) ((δ : ℝ) / 2) 0 = 1 := by
    rw [ctsInd_eq_one_iff hδ2]; push_cast; linarith
  have h2 : ctsInd (δ / 2) 1 0 = 1 := by
    rw [ctsInd_eq_one_iff hδ2]
    have : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
    push_cast; linarith
  simp only [softCut, Fin.sum_univ_two, πW, eW, XB, Matrix.cons_val_zero, Matrix.cons_val_one,
    h1, h2]
  norm_num

/-- **The separation, assembled, on the bet `X = (−1, 1)`**: (a) separates at every width;
(b) separates at width `δ` but not at `δ/2`. Per bet: the frame fixes one bet, so this is the
soft-versus-hard threshold-0 *cut* separating, not the predicates over all bets.
Source: lean-deference-2-015; mandate T9
Kind: N+
Fidelity: exact -/
theorem separation :
    (∀ δ : ℚ, 0 ≤ softCut πB eB XB δ) ∧ hardCut πB eB XB < 0 ∧
      (∀ δ : ℚ, 0 < δ → δ ≤ 1 → 0 ≤ softCut πW (eW δ) XB δ ∧ hardCut πW (eW δ) XB < 0 ∧
        softCut πW (eW δ) XB (δ / 2) < 0) := by
  refine ⟨boundary_soft, by rw [boundary_hard_fails]; norm_num, fun δ hδ hδ1 => ?_⟩
  refine ⟨by rw [wedge_soft hδ hδ1]; norm_num, by rw [wedge_hard_fails hδ]; norm_num,
    by rw [wedge_soft_half_fails hδ hδ1]; norm_num⟩

end

end Cleanroom.Deference.DefLatticeArrows.Wedge
