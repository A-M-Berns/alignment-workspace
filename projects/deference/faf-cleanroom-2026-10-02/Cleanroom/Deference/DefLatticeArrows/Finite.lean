import Cleanroom.Found.LitDdbFrames.Examples
import Cleanroom.Found.DefLattice.TwoOptionFinite
import LogicalInduction.Framework.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# T1 — The finite backbone and check.py's numbers

Package `def-lattice-arrows`, file 10. The finite-frame algebra the corpus's earlier Lean
proved over real sequences (lean-deference-001/002/004/006, root-deference-014), re-proved
here over `Finset` sums with no hypotheses beyond the stated finite conditions, and the exact
numbers of `deference-in-logical-induction-check.py` part C (root-deference-2-015) as `N` rows
over `lit-ddb-frames`'s Figure 2 / Figure 3 frames (imported, not redefined).

* `decomposition` — the keystone identity `gap_i = D_CM + D_UM,i + soft_i`, pure linearity over
  a commutative ring, *without* a normalization of the weights `α` (the identity needs none).
* `value_of_defects`, `soft_nonneg`, `value_of_CM` — finite tower ⟹ Value.
* `softmax_lower_bound` — `∑ softmax_δ(m)_j m_j ≥ m_i − |J|·δ` for `δ > 0`: the crude constant;
  the note's `δ log |J|` is **not** claimed.
* `value_of_argmax`, `payoff_gap_le_l1`, `value_argmax_via_softmax` — the argmax backbone, the
  `L¹` bound and the `AsympLE` squeeze.
* `fig2_*`, `fig3_*` — check.py's exact values (gaps, stationarity, the decomposition for
  `O_a`) by `norm_num`.

Nothing here is an LI theorem; `value_of_CM` is the exact finite statement.
-/

namespace Cleanroom.Deference.DefLatticeArrows.Finite

open Finset LogicalInduction Filter Topology

noncomputable section

/-! ### The keystone decomposition -/

/-- The value gap `E_π(Ŝ) − E_π(O^i)` for the weighted strategy `Ŝ_w = ∑_j α_j(w) O_j(w)`.
Source: v6 §1.1; check.py part A
Kind: D
Fidelity: exact -/
def valueGap {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (O : J → W → K) (α : J → W → K) (i : J) : K :=
  (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * O i w)

/-- The conditional-martingale defect `D_CM = ∑_w π_w ∑_j α_j(w) (O_j(w) − ∑_v P_wv O_j(v))`.
Source: check.py part A; lean-deference-001
Kind: D
Fidelity: exact -/
def defectCM {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) : K :=
  ∑ w, π w * (∑ j, α j w * (O j w - ∑ v, P w v * O j v))

/-- The unconditional-martingale defect `D_UM,i = ∑_w π_w ∑_v P_wv O_i(v) − ∑_w π_w O_i(w)`.
Source: check.py part A; lean-deference-001
Kind: D
Fidelity: exact -/
def defectUM {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (i : J) : K :=
  (∑ w, π w * (∑ v, P w v * O i v)) - (∑ w, π w * O i w)

/-- The soft term `soft_i = ∑_w π_w (∑_j α_j(w) m_j(w) − m_i(w))`, `m_j(w) = ∑_v P_wv O_j(v)`.
Source: check.py part A; lean-deference-001
Kind: D
Fidelity: exact -/
def softTerm {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J) : K :=
  ∑ w, π w * ((∑ j, α j w * (∑ v, P w v * O j v)) - (∑ v, P w v * O i v))

/-- **The keystone decomposition** (lean-deference-001, root-deference-014 A): for every finite
frame, menu, weight family and option, `gap_i = D_CM + D_UM,i + soft_i`. Pure linearity over a
commutative ring; no normalization of `α`, no hypothesis on the frame.
Source: `LeanDeference.lean:24` (`Deference.decomposition`, shape only); v6 §1.1; check.py A
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem decomposition {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J) :
    valueGap π O α i = defectCM π P O α + defectUM π P O i + softTerm π P O α i := by
  unfold valueGap defectCM defectUM softTerm
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Value from vanishing defects** (exact finite version, lean-deference-002): `D_CM = 0`,
`D_UM,i = 0` and `soft_i ≥ 0` give `E_π(O^i) ≤ E_π(Ŝ)`.
Source: `LeanDeference.lean:38–77`; v6 §1.1
Kind: L
Fidelity: exact
Hyps: (a) the three finite conditions -/
theorem value_of_defects {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J)
    (hCM : defectCM π P O α = 0) (hUM : defectUM π P O i = 0) (hsoft : 0 ≤ softTerm π P O α i) :
    0 ≤ valueGap π O α i := by
  rw [decomposition π P O α i, hCM, hUM]
  simpa using hsoft

/-- The soft term is nonnegative for argmax weights (`∑_j α_j m_j ≥ m_i` at every world) and
nonnegative `π`.
Source: `LeanDeference.lean` (`soft_nonneg`); v6 §1.1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem soft_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J)
    (hπ : ∀ w, 0 ≤ π w)
    (hmax : ∀ w, (∑ v, P w v * O i v) ≤ ∑ j, α j w * (∑ v, P w v * O j v)) :
    0 ≤ softTerm π P O α i := by
  unfold softTerm
  exact Finset.sum_nonneg (fun w _ => mul_nonneg (hπ w) (by linarith [hmax w]))

/-- **Finite tower ⟹ Value** (exact, lean-deference-002): the conditional-martingale and
unconditional-martingale defects vanish and the weights are argmax weights, so
`E_π(O^i) ≤ E_π(Ŝ)`. A finite-frame statement, not an LI theorem.
Source: `LeanDeference.lean` (`value_of_CM`); check.py part D; v6 §1.1
Kind: L
Fidelity: exact
Hyps: (a) the finite conditions -/
theorem value_of_CM {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J)
    (hπ : ∀ w, 0 ≤ π w) (hCM : defectCM π P O α = 0) (hUM : defectUM π P O i = 0)
    (hmax : ∀ w, (∑ v, P w v * O i v) ≤ ∑ j, α j w * (∑ v, P w v * O j v)) :
    0 ≤ valueGap π O α i :=
  value_of_defects π P O α i hCM hUM (soft_nonneg π P O α i hπ hmax)

/-! ### The softmax lower bound -/

/-- `u ≤ exp u` for `u ≥ 0` (from `u + 1 ≤ exp u`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem le_exp_self (u : ℝ) : u ≤ Real.exp u := by
  linarith [Real.add_one_le_exp u]

/-- **The softmax lower bound** (lean-deference-004): for `δ > 0`,
`∑_j softmax_δ(m)_j · m_j ≥ m_i − |J|·δ`. The crude constant `|J|·δ` (each term
`softmax_j (M − m_j) ≤ exp((m_j − M)/δ)(M − m_j) ≤ δ`); the note's tight `δ log |J|` is not
claimed.
Source: `LeanDeference.lean:187` (`softmax_lower_bound`, shape only); check.py part B (Gibbs);
lean-deference-004
Kind: P
Fidelity: weaker: constant `|J|·δ` in place of `δ log |J|` (disclosed)
Hyps: (a) `0 < δ` -/
theorem softmax_lower_bound {J : Type*} [Fintype J] [Nonempty J]
    (m : J → ℝ) (δ : ℝ) (hδ : 0 < δ) (i : J) :
    m i - (Fintype.card J : ℝ) * δ ≤
      ∑ j, (Real.exp (m j / δ) / ∑ k, Real.exp (m k / δ)) * m j := by
  obtain ⟨j0, hj0⟩ := Finite.exists_max m
  set M : ℝ := m j0 with hM
  set Z : ℝ := ∑ k, Real.exp (m k / δ) with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun k _ => Real.exp_pos _) univ_nonempty
  have hZge : Real.exp (M / δ) ≤ Z :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos (m k / δ)).le) (mem_univ j0)
  -- the weights sum to one
  have hsum1 : ∑ j, Real.exp (m j / δ) / Z = 1 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hZpos.ne'
  -- each defect term is at most δ
  have hterm : ∀ j, (Real.exp (m j / δ) / Z) * (M - m j) ≤ δ := by
    intro j
    have hmj : m j ≤ M := hj0 j
    have h1 : Real.exp (m j / δ) / Z ≤ Real.exp (m j / δ) / Real.exp (M / δ) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hZge
    have h2 : Real.exp (m j / δ) / Real.exp (M / δ) = Real.exp (-((M - m j) / δ)) := by
      rw [← Real.exp_sub]; congr 1; ring
    set u : ℝ := (M - m j) / δ with hu
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hδ.le
    have hMm : M - m j = δ * u := by rw [hu]; field_simp
    calc (Real.exp (m j / δ) / Z) * (M - m j)
        ≤ (Real.exp (m j / δ) / Real.exp (M / δ)) * (M - m j) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = Real.exp (-u) * (δ * u) := by rw [h2, hMm]
      _ ≤ δ := by
          have hexp : Real.exp (-u) * u ≤ 1 := by
            rw [Real.exp_neg]
            rw [inv_mul_le_iff₀ (Real.exp_pos u)]
            simpa using le_exp_self u
          nlinarith [hexp, hδ]
  -- assemble: ∑ w_j m_j = M − ∑ w_j (M − m_j) ≥ M − |J| δ ≥ m_i − |J| δ
  have hsplit : ∑ j, (Real.exp (m j / δ) / Z) * m j =
      M - ∑ j, (Real.exp (m j / δ) / Z) * (M - m j) := by
    have : ∑ j, (Real.exp (m j / δ) / Z) * (M - m j) =
        M * ∑ j, Real.exp (m j / δ) / Z - ∑ j, (Real.exp (m j / δ) / Z) * m j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hsum1]; ring
  have hbound : ∑ j, (Real.exp (m j / δ) / Z) * (M - m j) ≤ (Fintype.card J : ℝ) * δ := by
    calc ∑ j, (Real.exp (m j / δ) / Z) * (M - m j) ≤ ∑ _j : J, δ :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = (Fintype.card J : ℝ) * δ := by simp
  rw [hsplit]
  linarith [hj0 i]

/-! ### The argmax backbone and the `L¹` bound -/

/-- **Argmax Value from the two unconditional-martingale identities** (lean-deference-006 (a)):
with `jstar w` the expert's pick at `w`, `hstar` its optimality by the expert's lights, and the
identities `E_π(Ŝ) = E_π(m_{jstar})`, `E_π(m_i) = E_π(O^i)`: `E_π(O^i) ≤ E_π(Ŝ)`. Tie-break free.
Source: `LeanDeference.lean:302` (`value_of_argmax`, shape only); lean-deference-006
Kind: L
Fidelity: exact
Hyps: (a) the finite conditions -/
theorem value_of_argmax {W J : Type*} [Fintype W] [Fintype J]
    (π : W → ℝ) (P : W → W → ℝ) (O : J → W → ℝ) (i : J) (jstar : W → J)
    (hπ : ∀ w, 0 ≤ π w)
    (hstar : ∀ w j, (∑ v, P w v * O j v) ≤ ∑ v, P w v * O (jstar w) v)
    (hUM_S : (∑ w, π w * O (jstar w) w) = ∑ w, π w * (∑ v, P w v * O (jstar w) v))
    (hUM_i : (∑ w, π w * (∑ v, P w v * O i v)) = ∑ w, π w * O i w) :
    (∑ w, π w * O i w) ≤ ∑ w, π w * O (jstar w) w := by
  rw [hUM_S, ← hUM_i]
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hstar w i) (hπ w))

/-- **The payoff gap is bounded by the `L¹` weight distance** (lean-deference-006 (b)): for
options in `[0,1]` and nonnegative `π`, `|E_π(∑ α O) − E_π(∑ β O)| ≤ E_π ‖α − β‖₁`.
Source: `LeanDeference.lean:323` (`payoff_gap_le_l1`, shape only); lean-deference-006
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem payoff_gap_le_l1 {W J : Type*} [Fintype W] [Fintype J]
    (π : W → ℝ) (O : J → W → ℝ) (α β : J → W → ℝ)
    (hπ : ∀ w, 0 ≤ π w) (hO : ∀ j w, 0 ≤ O j w ∧ O j w ≤ 1) :
    |(∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * (∑ j, β j w * O j w))|
      ≤ ∑ w, π w * (∑ j, |α j w - β j w|) := by
  have hrw : (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * (∑ j, β j w * O j w))
      = ∑ w, π w * (∑ j, (α j w - β j w) * O j w) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hrw]
  calc |∑ w, π w * (∑ j, (α j w - β j w) * O j w)|
      ≤ ∑ w, |π w * (∑ j, (α j w - β j w) * O j w)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w, π w * |∑ j, (α j w - β j w) * O j w| := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [abs_mul, abs_of_nonneg (hπ w)]
    _ ≤ ∑ w, π w * (∑ j, |α j w - β j w|) := by
        refine Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left ?_ (hπ w))
        calc |∑ j, (α j w - β j w) * O j w|
            ≤ ∑ j, |(α j w - β j w) * O j w| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, |α j w - β j w| := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              rw [abs_mul]
              have hO1 : |O j w| ≤ 1 := by
                rw [abs_of_nonneg (hO j w).1]; exact (hO j w).2
              calc |α j w - β j w| * |O j w|
                  ≤ |α j w - β j w| * 1 := mul_le_mul_of_nonneg_left hO1 (abs_nonneg _)
                _ = |α j w - β j w| := mul_one _

/-- **Argmax Value via the softmax limit** (lean-deference-006, the `AsympLE` squeeze): softmax
Value `E(O^i) ≲ₙ E(Ŝ_soft)` and `|E(Ŝ_soft) − E(Ŝ)| ≤ Δ_n → 0` give argmax Value
`E(O^i) ≲ₙ E(Ŝ)`.
Source: `LeanDeference.lean:355` (`value_argmax_via_softmax`, shape only); lean-deference-006
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem value_argmax_via_softmax {Eoi ESa ESb Δ : ℕ → ℝ}
    (hSoft : Eoi ≲ₙ ESa) (hb : ∀ n, |ESa n - ESb n| ≤ Δ n) (hΔ : Tendsto Δ atTop (𝓝 0)) :
    Eoi ≲ₙ ESb := by
  intro ε hε
  filter_upwards [hSoft (ε / 2) (half_pos hε), hΔ.eventually (gt_mem_nhds (half_pos hε))]
    with n h1 h2
  have := abs_le.mp (hb n)
  linarith [this.2]

/-! ### check.py part C: DDB Figure 2 and Figure 3 as `N` rows -/

open Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

/-- The DDB bet menu: `O_a = (1, −1)`, `O_b = (−1, 1)` (check.py part C).
Source: check.py part C (`O_a, O_b = half(1,-1), half(-1,1)`)
Kind: D
Fidelity: exact -/
def ddbMenu : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![-1, 1]]

/-- Hard selection on Figure 2: option `b` at world `0`, option `a` at world `1`
(`α j w = 1[j = sel w]`).
Source: check.py part C (`hard_select(P2, menu)`)
Kind: D
Fidelity: exact -/
def fig2Sel : Fin 2 → Fin 2 → ℝ := ![![0, 1], ![1, 0]]

/-- The Figure 2 selection is the expert's argmax at each world: at world `0`
(`P_a = (1/5, 4/5)`) option `b` is strictly better, at world `1` option `a`.
Source: check.py part C
Kind: N+
Fidelity: exact -/
theorem fig2_selection_argmax :
    (∑ v, fig2.P 0 v * ddbMenu 0 v) < (∑ v, fig2.P 0 v * ddbMenu 1 v) ∧
      (∑ v, fig2.P 1 v * ddbMenu 1 v) < (∑ v, fig2.P 1 v * ddbMenu 0 v) := by
  simp [Fin.sum_univ_two, fig2_P0, fig2_P1, ddbMenu]
  norm_num

/-- **Figure 2 (the anti-expert): Value fails** — both gaps are `−1`.
Source: check.py part C ("Value FAILS (some gap < 0)", gaps `(−1, −1)`); root-deference-2-015
Kind: N+
Fidelity: exact -/
theorem fig2_gaps :
    valueGap half ddbMenu fig2Sel 0 = -1 ∧ valueGap half ddbMenu fig2Sel 1 = -1 := by
  simp [valueGap, Fin.sum_univ_two, half, ddbMenu, fig2Sel]
  norm_num

/-- **Figure 2 is stationary**: `π P = π` (the unconditional martingale on these bets).
Source: check.py part C ("stationary: pi@P == pi")
Kind: N+
Fidelity: exact -/
theorem fig2_stationary : ∀ v, (∑ w, half w * fig2.P w v) = half v := by
  intro v
  fin_cases v <;> simp [Fin.sum_univ_two, half, fig2_P0, fig2_P1] <;> norm_num

/-- **Figure 2, the §4 trap quantified** for option `O_a`: `gap = −1`, `D_CM = −8/5`,
`D_UM = 0`, `soft = 3/5` — the gap is all conditional-martingale defect.
Source: check.py part C ("sec.4 trap: gap = D_CM + D_UM + soft with D_UM==0 and D_CM<0");
root-deference-2-015
Kind: N+
Fidelity: exact -/
theorem fig2_decomposition_Oa :
    defectCM half fig2.P ddbMenu fig2Sel = -8 / 5 ∧ defectUM half fig2.P ddbMenu 0 = 0 ∧
      softTerm half fig2.P ddbMenu fig2Sel 0 = 3 / 5 := by
  simp [defectCM, defectUM, softTerm, Fin.sum_univ_two, half, ddbMenu, fig2Sel, fig2_P0, fig2_P1]
  norm_num

/-- Hard selection on Figure 3: option `a` at world `0`, option `b` at world `1`.
Source: check.py part C
Kind: D
Fidelity: exact -/
def fig3Sel : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- The Figure 3 selection is the expert's argmax at each world.
Source: check.py part C
Kind: N+
Fidelity: exact -/
theorem fig3_selection_argmax :
    (∑ v, fig3.P 0 v * ddbMenu 1 v) < (∑ v, fig3.P 0 v * ddbMenu 0 v) ∧
      (∑ v, fig3.P 1 v * ddbMenu 0 v) < (∑ v, fig3.P 1 v * ddbMenu 1 v) := by
  simp [Fin.sum_univ_two, fig3_P0, fig3_P1, ddbMenu]
  norm_num

/-- **Figure 3 (valued modest): Value holds** — both gaps are `1`.
Source: check.py part C ("Value HOLDS (all gaps >= 0)", gaps `(1, 1)`)
Kind: N+
Fidelity: exact -/
theorem fig3_gaps :
    valueGap half ddbMenu fig3Sel 0 = 1 ∧ valueGap half ddbMenu fig3Sel 1 = 1 := by
  simp [valueGap, Fin.sum_univ_two, half, ddbMenu, fig3Sel]
  norm_num

/-- **Figure 3 is not stationary**: `π P = (11/20, 9/20) ≠ π`.
Source: check.py part C ("yet NOT stationary")
Kind: N+
Fidelity: exact -/
theorem fig3_not_stationary :
    (∑ w, half w * fig3.P w 0) = 11 / 20 ∧ (∑ w, half w * fig3.P w 1) = 9 / 20 ∧
      (∑ w, half w * fig3.P w 0) ≠ half 0 := by
  simp [Fin.sum_univ_two, half, fig3_P0, fig3_P1]
  norm_num

end

end Cleanroom.Deference.DefLatticeArrows.Finite
