import Cleanroom.Corrigibility.CorrLegitModif.Y1Model
import Cleanroom.Corrigibility.CorrLegitModif.Plumbing
import Cleanroom.Corrigibility.CorrLegitGeneral.Locality
import Cleanroom.Corrigibility.CorrLegitGeneral.LocalValue

/-!
# corr-legit-modif — T1(b): the legitimacy label of the Y1 successor frame, at grade (a)

The successor frame `F_ow` of the honest policy: at a `modify`-world the row is the overwriting
install `P^hon(· | modify, L)` (ignoring `σ_A` and `ℓ`), at a `keep`-world the agent's own
continuation `P^hon(· | keep, σ_A)`. Both are `condRow`s of the honest joint
(`corr-reflect-frames`): the keep rows along the three-cell map `f3`, the modify row along
`(ℓ, v)` through a fixed `L`-modify world.

**At `P(L) = 1`** the `¬L`-worlds are null and `F_ow` *is* the Bayesian refinement
`refineFrame (y1 1) f3` (`y1Frame_one_P`), so Reflection and Total Trust of the coarse `P_{t₁}`
toward it come from `refineFrame_reflects` / `refineFrame_totalTrust`, and the
legitimacy-conditioned criterion holds for every question — adversary A5.2's "globally legitimate
by Theorem 4.1 from `P_{t₁}`", proved rather than reported. The mandate's `ofPartition` route is
also given, on the eight `L`-worlds where the joint has full support (`F8`).

**At `P(L) = 9/10` there are two successor frames in the sources** (findings F2, repair round 1).
(i) The scripts' own-continuation frame `y1Frame` (`hudson-respondent` `checks.py` `own_cont`,
`legitimacy-general-final-scratch/repair_checks.py` l. 49): its keep rows `P^hon(· | keep, σ_A)`
are *not* certain of `L` (`P(L | keep, σ_A = w) = λ`, `y1Frame_keepw_massL`), so the *global*
`L`-conditioned criterion fails at every `λ < 1` (`y1Frame_not_legitimizingTT`, via
`legitimizingTT_certain_of_legit`), while the *local* criterion on the decision question `{W, R}`
holds at `9/10` and `7/10` and fails at `1/2` (`y1Frame_legitTotalTrustWrt_sQ`,
`y1Frame_legitTotalTrustWrt_sQ_seven`, `y1Frame_not_legitTotalTrustWrt_sQ_half`) — the source's
"honest holds at `P(L) ≥ 7/10`". (ii) The `L`-conditioned frame `y1FrameL` of lgf l. 170 (A5.2:
"a conditional of `π_L` on a partition") and of the mandate's cone route: the Bayesian refinement
of `restrict π L` along the three cells, whose every row is certain of `L` (`y1FrameL_certain`);
for it the global label holds at every `λ` in two lines (`y1FrameL_legitimizingTT`). The two frames
share the install row (`y1FrameL_P_modify`) and coincide at `λ = 1` (`y1FrameL_one_P`), which is
the only `λ` the refutation row uses. At `λ = 1` the `L`-conditioning is vacuous for every frame
(`legitimizingTT_one_iff_totalTrust`).
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrLegitGeneral Cleanroom.Trust.TtFiniteFrames
  Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

/-! ## Events, questions, partition maps -/

/-- The legitimacy event `L = {ℓ = true}`.
Source: [[legitimacy-general-final]] Proofs l. 118
Kind: D
Fidelity: exact -/
def Lset : Finset Y1W := univ.filter (fun w => w.1 = true)

/-- The verdict event `modify = {v = true}`.
Source: [[legitimacy-general-final]] Proofs l. 118
Kind: D
Fidelity: exact -/
def modSet : Finset Y1W := univ.filter (fun w => w.2.2.2 = true)

/-- The world event `W = {s = true}` (the decision-relevant proposition).
Source: [[legitimacy-general-final]] Proofs l. 134 ("Total Trust on `{R, W}`")
Kind: D
Fidelity: exact -/
def sW : Finset Y1W := univ.filter (fun w => w.2.1 = true)

/-- The own-signal cell `{σ_A = a}`.
Source: [[hudson-respondent]] B2(b) l. 51 (the agent's "full state … holds `σ_A`")
Kind: D
Fidelity: exact -/
def aCell (a : Bool) : Finset Y1W := univ.filter (fun w => w.2.2.1 = a)

/-- The decision question `{W, R}` as the two-cell question of `W`.
Source: [[legitimacy-general-final]] Proofs l. 134
Kind: D
Fidelity: exact -/
abbrev sQ : Y1W → Bool := questionOf sW

/-- The three successor cells, as `(v, v ∨ σ_A)`: `modify ↦ (true, true)`,
`keep ∧ σ_A = w ↦ (false, true)`, `keep ∧ σ_A = r ↦ (false, false)` (the mandate's `Fin 3` with a
codomain `simp` decides).
Source: mandate T1(b)
Kind: D
Fidelity: exact -/
def f3 : Y1W → Bool × Bool := fun w => (w.2.2.2, w.2.2.2 || w.2.2.1)

/-- The map `(ℓ, v)`: its fibre through an `L`-modify world is `L ∩ modify`, the overwriting
install's conditioning event.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def gLV : Y1W → Bool × Bool := fun w => (w.1, w.2.2.2)

/-- A fixed `L`-modify world (base point of the install's conditioning event).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wL : Y1W := (true, true, true, true)

/-- Nonnegativity of the policy joint for `λ ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem y1Pol_nonneg {lam : ℝ} (hl : 0 ≤ lam ∧ lam ≤ 1) (fake : Bool) : ∀ w, 0 ≤ y1Pol lam fake w := by
  intro w
  unfold y1Pol
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · unfold pL; split_ifs <;> linarith [hl.1, hl.2]
  · unfold pS eps; split_ifs <;> norm_num
  · unfold pSig; split_ifs <;> norm_num
  · unfold modRate pMod; split_ifs <;> norm_num

/-- At `P(L) = 1` the `¬L`-worlds are null.
Source: none: infrastructure (mandate Known issues 13)
Kind: L
Fidelity: n/a -/
theorem y1_one_null_offL (w : Y1W) (hw : w.1 = false) : y1 1 w = 0 := by
  simp [y1Pol, pL, hw]

/-- At `P(L) = 1` restriction to `L` is the identity on the joint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_y1_one_L : restrict (y1 1) Lset = y1 1 := by
  funext w
  rw [restrict_apply]
  split_ifs with hw
  · rfl
  · have : w.1 = false := by simpa [Lset] using hw
    exact (y1_one_null_offL w this).symm

/-! ## The successor frame -/

/-- **The overwriting successor frame `F_ow` at `P(L) = λ`**: at a modify-world the row is the
overwriting install `P^hon(· | modify, L)` (the conditional of the honest joint on `L ∩ modify`,
regardless of `ℓ` and `σ_A`); at a keep-world the own continuation `P^hon(· | keep, σ_A)`.
Scope: the Y1 scope clause (`ε = 1/10`, honest kernel `(9/10, 1/10)` inverted under `¬L`, own
signal `(1/10, 9/10)`, stakes `(1, 4)`, overwriting install `P^hon(· | modify, L)` ignoring
`σ_A`). Rows are `condRow`s, so on a `π`-null fibre (only at `λ = 0`) a row is a point mass;
every headline carries `0 < λ`.
Source: [[legitimacy-general-final]] Proofs l. 118 ("installed state at modify … own
continuation at keep"); [[hudson-respondent]] `checks.py` (1)
Kind: D
Fidelity: exact -/
def y1Frame (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) : Frame Y1W where
  P := fun w => if w.2.2.2 then condRow (y1 lam) gLV wL else condRow (y1 lam) f3 w
  P_mem := fun w => by
    show (if w.2.2.2 then condRow (y1 lam) gLV wL else condRow (y1 lam) f3 w) ∈ stdSimplex ℝ Y1W
    split_ifs <;> exact condRow_mem (y1Pol_nonneg hl false) _ _

/-- `f3 v = (true, true)` iff `v` is a modify-world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem f3_eq_modify_iff (v : Y1W) : f3 v = (true, true) ↔ v.2.2.2 = true := by
  unfold f3
  cases h : v.2.2.2 <;> simp

/-- The `f3`-fibre of a modify-world is `modify`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_f3_modify {w : Y1W} (hw : w.2.2.2 = true) : fibre f3 w = modSet := by
  ext v
  have hw0 : f3 w = (true, true) := (f3_eq_modify_iff w).2 hw
  simp only [mem_fibre, modSet, mem_filter, mem_univ, true_and, hw0, f3_eq_modify_iff]

/-- The `(ℓ, v)`-fibre of the base point is `L ∩ modify`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_gLV_wL : fibre gLV wL = Lset ∩ modSet := by
  ext v
  simp [mem_fibre, gLV, wL, Lset, modSet]

/-- **At `P(L) = 1` the successor frame is the Bayesian refinement along `f3`**: the modify row
`P(· | modify, L)` equals `P(· | modify)` because the `¬L`-modify worlds are null.
Source: none: infrastructure (T1(b), the `λ = 1` identification)
Kind: L
Fidelity: n/a -/
theorem y1Frame_one_P (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) :
    (y1Frame 1 h).P = (refineFrame (y1 1) (y1Pol_nonneg h false) f3).P := by
  funext w
  simp only [y1Frame, refineFrame_P]
  split_ifs with hv
  · apply condRow_eq_of_subset_null
    · rw [fibre_gLV_wL, fibre_f3_modify hv]; exact inter_subset_right
    · intro v hv' hnv
      rw [fibre_gLV_wL] at hnv
      rw [fibre_f3_modify hv] at hv'
      have : v ∉ Lset := fun hL => hnv (mem_inter.2 ⟨hL, hv'⟩)
      exact y1_one_null_offL v (by simpa [Lset] using this)
    · rw [fibre_gLV_wL]
      apply mass_pos_of_mem (y1Pol_nonneg h false) (q := Lset ∩ modSet) (w := wL)
      · simp [Lset, modSet, wL]
      · norm_num [y1Pol, wL, pL, pS, pSig, pMod, modRate, eps]
  · rfl

/-- **T1(b) at `P(L) = 1`, Reflection**: the coarse `P_{t₁}` reflects the overwriting successor
frame (every candidate is the conditional on its own cell).
Scope: the Y1 scope clause; `P(L) = 1`.
Source: [[legitimacy-general-final]] Proofs l. 134 (A5.2: "globally legitimate by Thm 4.1 from
`P_{t₁}`"); [[hudson-respondent]] B2(b) l. 51 ("judged from the *coarse* state … holds")
Kind: C (`refineFrame_reflects` through the row identification)
Fidelity: exact
Hyps: (a) none -/
theorem y1Frame_one_reflects (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) : Reflects (y1 1) (y1Frame 1 h) :=
  reflects_of_P_eq (y1Frame_one_P h).symm (refineFrame_reflects _ f3)

/-- **T1(b) at `P(L) = 1`, Total Trust**: the coarse `P_{t₁}` totally trusts the overwriting
successor frame.
Scope: the Y1 scope clause; `P(L) = 1`.
Source: as `y1Frame_one_reflects`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem y1Frame_one_totalTrust (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) :
    TotalTrust (y1 1) (y1Frame 1 h) :=
  totalTrust_of_P_eq (y1Frame_one_P h).symm (refineFrame_totalTrust _ f3)

/-- **The legitimacy label at grade (a)** (`P(L) = 1`): the overwriting successor frame is
`L`-conditioned totally trusted by the coarse `P_{t₁}` — `LegitimizingTT π F_ow L` — and hence
`L`-conditioned locally trusted on every question. This is the frame the agent dodges
(`y1_dodge`): the modification is legitimate in the verdict-process sense and dodged.
Scope: the Y1 scope clause; `P(L) = 1` (so `restrict π L = π`).
Source: [[legitimacy-general-final]] Proofs l. 134 (A5.2); [[truth]] 1.1 l. 24 ("the installed
state is globally legitimate by DDB Thm 4.1 from `P_{t₁}`"); corr-wf14b-056
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem y1Frame_one_legitimizingTT (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) :
    LegitimizingTT (y1 1) (y1Frame 1 h) Lset := by
  unfold LegitimizingTT
  rw [restrict_y1_one_L]
  exact y1Frame_one_totalTrust h

/-- The local criterion for every question, at `P(L) = 1`.
Source: as `y1Frame_one_legitimizingTT`
Kind: L
Fidelity: exact -/
theorem y1Frame_one_legitTotalTrustWrt (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) {C : Type} [Fintype C]
    [DecidableEq C] (Q : Y1W → C) : LegitTotalTrustWrt Q (y1 1) (y1Frame 1 h) Lset :=
  (y1Frame_one_legitimizingTT h).wrt Q

/-! ## The `ofPartition` route on the eight `L`-worlds -/

/-- The eight `L`-worlds `(s, σ_A, v)`.
Source: mandate T1(b) ("let `π` be the joint on the 8 `L`-worlds")
Kind: D
Fidelity: exact -/
abbrev Y1L := Bool × Bool × Bool

/-- The honest joint under `L` on the eight worlds: `P(s) · P(σ_A | s) · P(v | s, L)`.
Source: [[legitimacy-general-final]] Proofs l. 118
Kind: D
Fidelity: exact -/
def y1L : Y1L → ℝ := fun w =>
  pS w.1 * pSig w.1 w.2.1 * (if w.2.2 then pMod true w.1 else 1 - pMod true w.1)

/-- The three cells on the eight worlds, as `(v, v ∨ σ_A)`.
Source: mandate T1(b)
Kind: D
Fidelity: exact -/
def f3L : Y1L → Bool × Bool := fun w => (w.2.2, w.2.2 || w.2.1)

/-- Full support of the joint under `L`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem y1L_pos : ∀ w, 0 < y1L w := by
  rintro ⟨s, a, v⟩
  cases s <;> cases a <;> cases v <;> norm_num [y1L, pS, pSig, pMod, eps]

/-- **The successor frame on the `L`-worlds as a partition expert**: `Frame.ofPartition y1L f3L`.
Source: mandate T1(b) ("This is `Frame.ofPartition π hpos f`")
Kind: D
Fidelity: exact -/
def F8 : Frame Y1L := Frame.ofPartition y1L y1L_pos f3L

/-- **A5.2 by `totalTrust_ofPartition`**: the coarse `P_{t₁}` on the `L`-worlds totally trusts and
reflects the successor frame; the criterion holds with `L = univ` and locally for every question.
Scope: the Y1 scope clause; `P(L) = 1` (the eight `L`-worlds carry all the mass).
Source: [[legitimacy-general-final]] Proofs l. 134 (A5.2); `tt-finite-frames` T1
Kind: C (cited `totalTrust_ofPartition`; Reflection by `reflects_ofPartition`)
Fidelity: exact
Hyps: (a) none -/
theorem F8_legit :
    TotalTrust y1L F8 ∧ Reflects y1L F8 ∧ LegitimizingTT y1L F8 univ ∧
    ∀ {C : Type} [Fintype C] [DecidableEq C] (Q : Y1L → C), LegitTotalTrustWrt Q y1L F8 univ := by
  have hT : TotalTrust y1L F8 := totalTrust_ofPartition y1L_pos f3L
  have hL : LegitimizingTT y1L F8 univ := by unfold LegitimizingTT; rw [restrict_univ]; exact hT
  exact ⟨hT, reflects_ofPartition y1L_pos f3L, hL, fun Q => hL.wrt Q⟩

/-- The `W`-event on the eight worlds.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def sWL : Finset Y1L := univ.filter (fun w => w.1 = true)

/-- **The rows of `F8` are the record's states**: `P(W | modify, L) = 1/2` (the overwriting
install `Q_ow`), `P(W | keep, w) = 1/10`, `P(W | keep, r) = 1/730` (the own continuations).
Source: [[yudkowsky-respondent]] `y1_reflection_check.out` (`Q(W | modify, L) = 1/2`); mandate,
Representation of record (`P(W | keep, σ_A = r) = 1/730`)
Kind: L
Fidelity: exact -/
theorem F8_rows (w : Y1L) :
    mass (F8.P w) sWL = if w.2.2 then 1 / 2 else if w.2.1 then 1 / 10 else 1 / 730 := by
  obtain ⟨s, a, v⟩ := w
  unfold F8
  simp only [mass, sWL, sum_filter, Frame.ofPartition_P_apply, Corr.ofMap, Fintype.sum_prod_type,
    Fintype.sum_bool]
  cases s <;> cases a <;> cases v <;> norm_num [f3L, y1L, pS, pSig, pMod, eps]

/-! ## Row masses on the sixteen worlds -/

/-- Positivity of the install's conditioning event `L ∩ modify` for `λ > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_gLV_pos {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) :
    0 < mass (y1 lam) (fibre gLV wL) := by
  rw [fibre_gLV_wL]
  apply mass_pos_of_mem (y1Pol_nonneg hl false) (q := Lset ∩ modSet) (w := wL)
  · simp [Lset, modSet, wL]
  · norm_num [y1Pol, wL, pL, pS, pSig, pMod, modRate, eps]; exact hl0

/-- Positivity of a keep-fibre for `λ > 0` (the `L`-part alone is positive).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_f3_keep_pos {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) {w : Y1W}
    (hw : w.2.2.2 = false) : 0 < mass (y1 lam) (fibre f3 w) := by
  apply mass_pos_of_mem (y1Pol_nonneg hl false) (q := fibre f3 w) (w := (true, true, w.2.2.1, false))
  · simp [mem_fibre, f3, hw]
  · cases h : w.2.2.1 <;> norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps] <;> exact hl0

/-- **The rows' credences in `W`** on the sixteen worlds, for `0 < λ ≤ 1`: the install has
`P(W | modify, L) = 1/2`; the own continuations `P(W | keep, w) = (9 − 8λ)/10` and
`P(W | keep, r) = (9 − 8λ)/(90 + 640λ)` (`1/10`, `1/730` at `λ = 1`; `9/50`, `1/370` at `9/10`).
Source: [[yudkowsky-respondent]] `y1_reflection_check.out`; mandate, Representation of record
Kind: L
Fidelity: exact -/
theorem y1Frame_rows_sW {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) (w : Y1W) :
    mass ((y1Frame lam hl).P w) sW =
      if w.2.2.2 then 1 / 2 else if w.2.2.1 then (9 - 8 * lam) / 10
        else (9 - 8 * lam) / (90 + 640 * lam) := by
  obtain ⟨ℓ, s, a, v⟩ := w
  simp only [y1Frame]
  cases v
  · have hpos := mass_fibre_f3_keep_pos hl0 hl (w := (ℓ, s, a, false)) rfl
    rw [condRow_of_pos hpos]
    cases a
    · have hm : mass (y1 lam) (fibre f3 (ℓ, s, false, false)) = (90 + 640 * lam) / 1000 := by
        simp only [mass, fibre, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, f3]
        norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]; ring
      have hne : (90 : ℝ) + 640 * lam ≠ 0 := ne_of_gt (by linarith [hl.1])
      rw [hm]
      simp only [mass, sW, sum_filter, fibre, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [f3, ind, mem_filter, mem_univ, true_and]
      norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
      rw [eq_div_iff hne]
      field_simp
      ring
    · have hm : mass (y1 lam) (fibre f3 (ℓ, s, true, false)) = 9 / 100 := by
        simp only [mass, fibre, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, f3]
        norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]; ring
      rw [hm]
      simp only [mass, sW, sum_filter, fibre, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [f3, ind, mem_filter, mem_univ, true_and]
      norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
      ring
  · have hpos := mass_fibre_gLV_pos hl0 hl
    rw [condRow_of_pos hpos]
    have hm : mass (y1 lam) (fibre gLV wL) = 9 * lam / 50 := by
      simp only [mass, fibre, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, gLV, wL]
      norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]; ring
    rw [hm]
    simp only [mass, sW, sum_filter, fibre, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [gLV, wL, ind, mem_filter, mem_univ, true_and]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
    field_simp
    ring

/-- **The own continuation is not certain of `L`**: `P(L | keep, σ_A = w) = λ` for `0 < λ ≤ 1`.
Source: none: infrastructure (the fact behind `y1Frame_not_legitimizingTT`)
Kind: L
Fidelity: exact -/
theorem y1Frame_keepw_massL {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) (ℓ s : Bool) :
    mass ((y1Frame lam hl).P (ℓ, s, true, false)) Lset = lam := by
  simp only [y1Frame]
  have hpos := mass_fibre_f3_keep_pos hl0 hl (w := (ℓ, s, true, false)) rfl
  rw [condRow_of_pos hpos]
  have hm : mass (y1 lam) (fibre f3 (ℓ, s, true, false)) = 9 / 100 := by
    simp only [mass, fibre, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, f3]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]; ring
  rw [hm]
  simp only [mass, Lset, sum_filter, fibre, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [f3, ind, mem_filter, mem_univ, true_and]
  norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
  ring

/-! ## At `P(L) = 9/10`: the global criterion fails, the local one holds -/

/-- **The global `L`-conditioned criterion fails at `P(L) = 9/10` for the scripts' successor
frame** (and at every `λ < 1`): the own continuation at `keep` is a positive-mass legitimate
candidate with `P(L) = λ < 1`, which `legitimizingTT_certain_of_legit` forbids. This is the frame
of the Y1 scripts (`own_cont`, keep rows `P^hon(· | keep, σ_A)`). It is *not* the frame of lgf
l. 170's hull argument, whose rows are conditionals of `π_L` and which passes the label at every
`λ` (`y1FrameL`, `y1FrameL_legitimizingTT`); the two coincide at `λ = 1` (`y1FrameL_one_P`).
What is refuted is therefore [[truth]] 1.1 item 2's transfer of A5.2's global label to Y1 at
`9/10` *under the scripts' own successor convention* (findings F2).
Scope: the Y1 scope clause; `0 < λ < 1`.
Source: [[corr-legit-general]] `legitimizingTT_certain_of_legit`; [[truth]] 1.1 item 2 (l. 26)
and [[legitimacy-general-final]] l. 170 (refuted at `9/10` for the scripts' frame); mandate T1(b)
Kind: N+ (refutation, for the scripts' successor frame)
Fidelity: exact
Hyps: (a) `0 < λ < 1` -/
theorem y1Frame_not_legitimizingTT {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hl : 0 ≤ lam ∧ lam ≤ 1) : ¬ LegitimizingTT (y1 lam) (y1Frame lam hl) Lset := by
  intro h
  have hw : (true, true, true, false) ∈ Lset := by simp [Lset]
  have hpos : 0 < y1 lam (true, true, true, false) := by
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]; exact hl0
  have := legitimizingTT_certain_of_legit (y1Pol_nonneg hl false) h hw hpos
  rw [y1Frame_keepw_massL hl0 hl] at this
  linarith

/-- `answer (questionOf q) {true} = q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem answer_sQ_true : answer sQ {true} = sW := by
  ext w; simp [answer, questionOf]

/-- **The local criterion on the decision question at `P(L) = 9/10`**: `L`-conditioned Total
Trust with respect to `{W, R}` toward the overwriting successor frame holds (the source: "honest
holds at `P(L) ≥ 7/10`"). Through `totalTrustWrt_questionOf_iff` this is the pair of Simple-Trust
cuts at every threshold against the three row credences `1/2`, `9/50`, `1/370`.
Scope: the Y1 scope clause; `P(L) = 9/10`.
Source: [[legitimacy-general-final]] Proofs l. 134 ("Local legitimacy-conditioned Total Trust on
`{R,W}` toward the successor frame: honest holds at `P(L) ≥ 7/10`")
Kind: C (T4(b) of `corr-legit-general` plus the finite cut check)
Fidelity: exact
Hyps: (a) none -/
theorem y1Frame_legitTotalTrustWrt_sQ (h : (0 : ℝ) ≤ 9 / 10 ∧ (9 / 10 : ℝ) ≤ 1) :
    LegitTotalTrustWrt sQ (y1 (9 / 10)) (y1Frame (9 / 10) h) Lset := by
  unfold LegitTotalTrustWrt
  rw [totalTrustWrt_questionOf_iff (restrict_nonneg (y1Pol_nonneg h false) Lset)]
  have hrow := y1Frame_rows_sW (lam := 9 / 10) (by norm_num) h
  constructor
  · intro t
    simp only [Frame.probEvent, hrow]
    simp only [sW, ← filter_and, mass, sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [restrict_apply, Lset, mem_filter, mem_univ, true_and]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
    split_ifs <;> linarith
  · intro t
    simp only [probEventLE, hrow]
    simp only [sW, ← filter_and, mass, sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [restrict_apply, Lset, mem_filter, mem_univ, true_and]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
    split_ifs <;> linarith

/-- **The local criterion at the source's boundary `P(L) = 7/10`** (the instance the source names:
"honest holds at `P(L) ≥ 7/10`"), by the same route. Added at audit round 1 (adversarial N5; the
auditor's probe `LocalTTAt7Over10.lean`).
Scope: the Y1 scope clause; `P(L) = 7/10`.
Source: [[legitimacy-general-final]] Proofs l. 134
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem y1Frame_legitTotalTrustWrt_sQ_seven (h : (0 : ℝ) ≤ 7 / 10 ∧ (7 / 10 : ℝ) ≤ 1) :
    LegitTotalTrustWrt sQ (y1 (7 / 10)) (y1Frame (7 / 10) h) Lset := by
  unfold LegitTotalTrustWrt
  rw [totalTrustWrt_questionOf_iff (restrict_nonneg (y1Pol_nonneg h false) Lset)]
  have hrow := y1Frame_rows_sW (lam := 7 / 10) (by norm_num) h
  constructor
  · intro t
    simp only [Frame.probEvent, hrow]
    simp only [sW, ← filter_and, mass, sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [restrict_apply, Lset, mem_filter, mem_univ, true_and]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
    split_ifs <;> linarith
  · intro t
    simp only [probEventLE, hrow]
    simp only [sW, ← filter_and, mass, sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [restrict_apply, Lset, mem_filter, mem_univ, true_and]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
    split_ifs <;> linarith

/-- **The local criterion fails at `P(L) = 1/2`** (the source's table: "fails at `1/2`"): at the
threshold `t = 1/2` the keep-`w` row claims `P(W) = (9 − 8λ)/10 = 1/2` while under `L` its cell
has `P(W | keep, w, L) = 1/10`, so the above-threshold cut at `1/2` loses
(`(1/2)(270/2000) > 99/2000`). One `X`, one `s`.
Scope: the Y1 scope clause; `P(L) = 1/2`.
Source: [[legitimacy-general-final]] Proofs l. 134 (the `1/2` row of the table)
Kind: N+ (refutation instance)
Fidelity: exact
Hyps: (a) none -/
theorem y1Frame_not_legitTotalTrustWrt_sQ_half (h : (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1) :
    ¬ LegitTotalTrustWrt sQ (y1 (1 / 2)) (y1Frame (1 / 2) h) Lset := by
  unfold LegitTotalTrustWrt
  rw [totalTrustWrt_questionOf_iff (restrict_nonneg (y1Pol_nonneg h false) Lset)]
  intro hST
  have hrow := y1Frame_rows_sW (lam := 1 / 2) (by norm_num) h
  have hcut := hST.1 (1 / 2)
  simp only [Frame.probEvent, hrow] at hcut
  simp only [sW, ← filter_and, mass, sum_filter] at hcut
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hcut
  simp only [restrict_apply, Lset, mem_filter, mem_univ, true_and] at hcut
  norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps] at hcut

/-! ## At `P(L) = 1` the `L`-conditioning is vacuous -/

/-- **At `λ = 1` the event `L` carries no content in the label**: `restrict (y1 1) L = y1 1`, so
for *every* frame the `L`-conditioned criterion is plain Total Trust of the coarse prior. Not a
defect of the Lean — it is the source's setup at `P(L) = 1` — but it is why "legitimate and dodged"
there means exactly "the coarse `P_{t₁}` totally trusts its own Bayesian refinement". Added at
audit round 1 (adversarial N6; the auditor's probe `LambdaOneVacuousL.lean`).
Source: none: infrastructure (disclosure of the `λ = 1` headline's content)
Kind: L
Fidelity: n/a -/
theorem legitimizingTT_one_iff_totalTrust (F : Frame Y1W) :
    LegitimizingTT (y1 1) F Lset ↔ TotalTrust (y1 1) F := by
  unfold LegitimizingTT; rw [restrict_y1_one_L]

/-- Every Bayesian refinement of the coarse prior along any map earns the `λ = 1` label: the label
does not see what the install forgets.
Source: none: infrastructure (as `legitimizingTT_one_iff_totalTrust`)
Kind: L
Fidelity: n/a -/
theorem any_refinement_is_legit {S : Type} [DecidableEq S] (f : Y1W → S)
    (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) :
    LegitimizingTT (y1 1) (refineFrame (y1 1) (y1Pol_nonneg h false) f) Lset :=
  (legitimizingTT_one_iff_totalTrust _).2 (refineFrame_totalTrust _ f)

/-! ## The `L`-conditioned successor frame (lgf l. 170; the mandate's cone route) -/

/-- **The `L`-conditioned successor frame `F_L`** of [[legitimacy-general-final]] l. 170 (A5.2:
"the installed state `P_{t₁}(· | σ, L)` is a conditional of `π_L` on a partition") and of mandate
T1(b)'s cone route at `9/10`: the Bayesian refinement of `restrict π L` along the three cells, so
the modify row is the install `π(· | L ∩ modify)` and the keep rows are `π(· | L ∩ keep ∧ σ_A)`.
Every row is certain of `L` (`y1FrameL_certain`). It differs from the scripts' frame `y1Frame`
(keep rows `π(· | keep, σ_A)`, not `L`-certain) only on the keep rows (`y1FrameL_P_modify`) and
coincides with it at `λ = 1` (`y1FrameL_one_P`).
Scope: the Y1 scope clause. Rows are `condRow`s of `restrict π L`, so on a `π_L`-null fibre
(only at `λ = 0`) a row is a point mass.
Source: [[legitimacy-general-final]] l. 170 (A5.2); mandate T1(b) ("keep-worlds
`π(· | keep, σ_A)`" on the `L`-worlds; the cone route)
Kind: D
Fidelity: exact -/
def y1FrameL (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) : Frame Y1W :=
  refineFrame (restrict (y1 lam) Lset) (restrict_nonneg (y1Pol_nonneg hl false) Lset) f3

/-- **The global `L`-conditioned label holds for the `L`-conditioned frame at every `λ`**:
`LegitimizingTT π F_L L` unfolds to `TotalTrust (restrict π L) F_L`, and `F_L` is the Bayesian
refinement of `restrict π L`, so `refineFrame_totalTrust` closes it — lgf l. 170's hull argument,
with no cone route needed. Read against `y1Frame_not_legitimizingTT`: the scripts' successor
fails the same label at every `λ < 1`; the two frames coincide at `λ = 1`.
Scope: the Y1 scope clause; `0 ≤ λ ≤ 1` (at `λ = 0` the restricted deferrer is `0` and the
statement is empty; `0 < λ` is where it has content).
Source: [[legitimacy-general-final]] l. 170 (A5.2); [[truth]] 1.1 item 2 (l. 26); mandate T1(b)
at `9/10`
Kind: C (`refineFrame_totalTrust`)
Fidelity: exact for the `L`-conditioned frame (which frame the sources mean is findings F2)
Hyps: (a) none -/
theorem y1FrameL_legitimizingTT (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) :
    LegitimizingTT (y1 lam) (y1FrameL lam hl) Lset := by
  unfold LegitimizingTT y1FrameL
  exact refineFrame_totalTrust _ f3

/-- The restricted deferrer reflects the `L`-conditioned frame (the equality form of the label).
Source: as `y1FrameL_legitimizingTT`
Kind: C (`refineFrame_reflects`)
Fidelity: exact
Hyps: (a) none -/
theorem y1FrameL_reflects (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) :
    Reflects (restrict (y1 lam) Lset) (y1FrameL lam hl) :=
  refineFrame_reflects _ f3

/-- The local form of the label for every question, for the `L`-conditioned frame.
Source: as `y1FrameL_legitimizingTT`
Kind: L
Fidelity: exact -/
theorem y1FrameL_legitTotalTrustWrt (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) {C : Type} [Fintype C]
    [DecidableEq C] (Q : Y1W → C) : LegitTotalTrustWrt Q (y1 lam) (y1FrameL lam hl) Lset :=
  (y1FrameL_legitimizingTT lam hl).wrt Q

/-- **Every row of the `L`-conditioned frame is certain of `L`** (for `0 < λ`): it is an
`L`-certain successor, which is why `legitimizingTT_certain_of_legit` does not bite it.
Source: none: infrastructure (the contrast with `y1Frame_keepw_massL`)
Kind: L
Fidelity: exact
Hyps: (a) `0 < λ` -/
theorem y1FrameL_certain {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) (w : Y1W) :
    mass ((y1FrameL lam hl).P w) Lset = 1 := by
  show mass (condRow (restrict (y1 lam) Lset) f3 w) Lset = 1
  apply condRow_restrict_certain (y1Pol_nonneg hl false)
  rw [mass_restrict]
  obtain ⟨ℓ, s, a, v⟩ := w
  cases v
  · apply mass_pos_of_mem (y1Pol_nonneg hl false) (q := fibre f3 (ℓ, s, a, false) ∩ Lset)
      (w := (true, true, a, false))
    · simp [mem_fibre, f3, Lset]
    · cases a <;> norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps] <;> exact hl0
  · apply mass_pos_of_mem (y1Pol_nonneg hl false) (q := fibre f3 (ℓ, s, a, true) ∩ Lset) (w := wL)
    · simp [mem_fibre, f3, Lset, wL]
    · norm_num [y1Pol, wL, pL, pS, pSig, pMod, modRate, eps]; exact hl0

/-- **The two successor frames share the install row**: at a modify-world the `L`-conditioned
frame's row is `π(· | L ∩ modify)`, the same overwriting install as `y1Frame`'s. The frames differ
only on the keep rows.
Source: none: infrastructure (findings F2: where the two conventions differ)
Kind: L
Fidelity: exact
Hyps: (a) `0 < λ` -/
theorem y1FrameL_P_modify {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) {w : Y1W}
    (hw : w.2.2.2 = true) : (y1FrameL lam hl).P w = (y1Frame lam hl).P w := by
  simp only [y1FrameL, y1Frame, refineFrame_P]
  rw [if_pos hw]
  have hfib : fibre f3 w ∩ Lset = fibre gLV wL := by
    rw [fibre_gLV_wL, fibre_f3_modify hw, inter_comm]
  have hpos : 0 < mass (y1 lam) (fibre gLV wL) := mass_fibre_gLV_pos hl0 hl
  rw [condRow_restrict_eq _ _ _ _ (by rw [hfib]; exact hpos), hfib, condRow_of_pos hpos]

/-- **At `λ = 1` the two successor frames coincide**: both are `refineFrame (y1 1) f3`, since
`restrict (y1 1) L = y1 1`. This is the only `λ` the refutation row (T1(c)) uses.
Source: none: infrastructure (findings F2)
Kind: L
Fidelity: exact -/
theorem y1FrameL_one_P (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) : (y1FrameL 1 h).P = (y1Frame 1 h).P := by
  rw [y1Frame_one_P h]
  funext w
  simp only [y1FrameL, refineFrame_P, restrict_y1_one_L]

end

end Cleanroom.Corrigibility.CorrLegitModif
