import Cleanroom.Found.LitDdbFrames.Examples
import Cleanroom.Trust.TtFiniteFrames.Collapse

/-!
# The anti-expert frame's finite facts, and the diagonal lemma

Package `tt-finite-frames`, Targets F1 and F2.

* **F1**: on the dependency's `fig2` (rows `(1/5, 4/5)`, `(4/5, 1/5)`) with the uniform `half`:
  the unconditional martingale (stationarity `∑ w, π w P_w(v) = π v`) holds, the product-form
  mass at `(𝟙_{0}, 1/2)` is `−1/4` (so Total Trust fails directly, complementing the dependency's
  `fig2_not_value`), and on the bet menu `{(1,−1), (−1,1)}` the expert at `a` values the diagonal
  of the recommended strategy at `−1` while its row-wise maximum is `3/5`. No second copy of the
  frame is made.
* **F2**: the diagonal lemma. `S w = E_{P_w}(S)` for every `S` iff `P_w = δ_w`; and the
  world-dependent-selection form `D_CM = 0` for all menus and selections iff `P_w = δ_w` on the
  support. **Finding**: root-deference-2-010 (i) says "iff the expert is immodest on `supp π`";
  the condition characterises the *omniscient* expert, strictly stronger than DDB immodesty —
  witnessed by the flat frame `P ≡ (1/2, 1/2)`, immodest, with `D_CM = 1/2` at the selection
  "bet at world 0 only" on the bet `(1, −1)`.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## F1: the anti-expert frame -/

namespace AntiExpert

/-- **Stationarity**: the uniform deferrer is an invariant distribution of the anti-expert frame,
`∑ w, π w · P_w(v) = π v` — the unconditional martingale.
Source: lean-deference-008 `AntiExpert.stationary`; [[deference-in-logical-induction-v6]] §2.1
Kind: N+
Fidelity: exact -/
theorem stationary : ∀ v, ∑ w, half w * fig2.P w v = half v := by
  intro v
  fin_cases v <;> simp [Fin.sum_univ_two, half, fig2_P0, fig2_P1] <;> norm_num

/-- The anti-expert's estimates of `𝟙_{0}`: `1/5` at `a`, `4/5` at `b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_ind0 : E (fig2.P 0) (ind {0}) = 1 / 5 ∧ E (fig2.P 1) (ind {0}) = 4 / 5 := by
  constructor <;> simp [E, fig2_P0, fig2_P1, ind]

/-- **The product-form mass at `(𝟙_{0}, 1/2)` is `−1/4`**: only world `b` (estimate `4/5`) is in
the event, contributing `(1/2)(0 − 1/2)`.
Source: lean-deference-008 `AntiExpert.TT_negative`; root-deference-010 (ii); vq-wiki-027 (a)
Kind: N+
Fidelity: exact -/
theorem mass_neg :
    ∑ w, half w * (ind {0} w - 1 / 2) * (if (1 / 2 : ℝ) ≤ E (fig2.P w) (ind {0}) then 1 else 0) =
      -1 / 4 := by
  obtain ⟨h0, h1⟩ := E_ind0
  rw [Fin.sum_univ_two, h0, h1]
  simp [half, ind]
  norm_num

/-- **Total Trust fails on the anti-expert frame**, directly (the dependency proves `¬ Value`).
Source: lean-deference-008; root-deference-010 (ii)
Kind: N+
Fidelity: exact -/
theorem not_totalTrust : ¬ TotalTrust half fig2 := by
  intro h
  have := h (ind {0}) (1 / 2)
  rw [mass_neg] at this
  norm_num at this

/-- The recommended strategy on the bet menu `{(1,−1), (−1,1)}`: `(−1, 1)` at `a`, `(1, −1)` at `b`
(the dependency's `fig2_not_value` strategy).
Source: [[Deference Done Better]] Figure 2; lean-deference-008
Kind: D
Fidelity: exact -/
def betStrategy : Fin 2 → Fin 2 → ℝ := ![![-1, 1], ![1, -1]]

/-- The bet strategy is recommended.
Source: [[Deference Done Better]] Figure 2 (the dependency's `fig2_not_value` proof)
Kind: L
Fidelity: n/a -/
theorem betStrategy_recommended : fig2.Recommended {![1, -1], ![-1, 1]} betStrategy := by
  refine ⟨⟨fun w => ?_, fun w v e => ?_⟩, fun w o ho => ?_⟩
  · fin_cases w <;> simp [betStrategy]
  · fin_cases w <;> fin_cases v <;> first | rfl | (exact absurd e fig2_ne) |
      (exact absurd e.symm fig2_ne)
  · simp only [mem_insert, mem_singleton] at ho
    fin_cases w <;> rcases ho with rfl | rfl <;>
      norm_num [E, Fin.sum_univ_two, fig2_P0, fig2_P1, betStrategy]

/-- **The diagonal-vs-row-wise gap.** The expert at `a` values the *diagonal* `Ŝ(w) = S_w(w)` of
the recommended strategy at `−1`, while its row-wise maximum `E_{P_a}(S_a)` is `3/5`: a frame's
recommendation is world-dependent, so the realised return is not the maximum.
Source: [[deference-in-logical-induction-v6]] §2.1 ("in the anti-expert frame `E_a(Ŝ) = −1` while
`M(a) = .6`"); vq-wiki-027 (a)
Kind: N+
Fidelity: exact -/
theorem diagonal_gap : E (fig2.P 0) (fun w => betStrategy w w) = -1 ∧
    E (fig2.P 0) (betStrategy 0) = 3 / 5 := by
  constructor <;> simp [E, Fin.sum_univ_two, fig2_P0, betStrategy] <;> norm_num

end AntiExpert

/-! ## F2: the diagonal lemma -/

/-- **The diagonal lemma.** `S w = E_{P_w}(S)` for every random variable `S` iff `P_w = δ_w` (the
expert at `w` is certain of `w`). (⇒) test `S = δ_v`.
Source: root-deference-2-010 (i)
Kind: P (small)
Fidelity: exact -/
theorem diagonal_iff (F : Frame W) (w : W) :
    (∀ S : W → ℝ, S w = E (F.P w) S) ↔ F.P w = Pi.single w 1 := by
  constructor
  · intro h
    funext v
    have := h (Pi.single v 1)
    simp only [E, Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      if_true] at this
    rw [Pi.single_apply]
    by_cases hv : v = w
    · subst hv; simpa using this.symm
    · rw [if_neg hv]
      have : (if w = v then (1 : ℝ) else 0) = F.P w v := this
      rw [if_neg (Ne.symm hv)] at this
      exact this.symm
  · intro h S
    rw [h]
    simp [E, Pi.single_apply]

/-- **`D_CM` — the world-dependent-selection defect** of a frame against a deferrer: for a menu
`O` and a selection weight `α j w` (how much of option `j` is taken at world `w`),
`∑ w, π w · ∑ j, α j w · (O j w − E_{P_w}(O j))`. Reading: the selections `α^j_w` are
arbitrary world-indexed weights — the inventory's family, with no cell-measurability, and the
normalisation `∑_j α^j_w = 1` dropped (immaterial: pad the menu with a zero option). Under
DDB's strategy reading (`α` cell-measurable) the property characterised by `D_CM = 0` would be
the conditional martingale on the support rather than omniscience; finding F-F2's conclusion
holds under either reading (see the findings file).
Source: root-deference-2-010 (i)
Kind: D
Fidelity: variant: selections unconstrained (audit r1 adversarial N4) -/
def dCM (π : W → ℝ) (F : Frame W) {n : ℕ} (O α : Fin (n + 1) → W → ℝ) : ℝ :=
  ∑ w, π w * ∑ j, α j w * (O j w - E (F.P w) (O j))

/-- **The `D_CM` form of the diagonal lemma.** `D_CM = 0` for every menu and every selection iff
`P_w = δ_w` at every world of positive prior probability — the *omniscient* expert on the
support, not merely an immodest one (see `flat_immodest_dCM_ne`).
Source: root-deference-2-010 (i) (corrected: "immodest" there means omniscient)
Kind: P (small)
Fidelity: variant: the source says "immodest on `supp π`"; the proved characterisation is
`P_w = δ_w` on `supp π`
Hyps: (a) `hπ` nonneg (for ⇐: null worlds contribute nothing) -/
theorem dCM_eq_zero_iff {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (F : Frame W) :
    (∀ (n : ℕ) (O α : Fin (n + 1) → W → ℝ), dCM π F O α = 0) ↔
      ∀ w, 0 < π w → F.P w = Pi.single w 1 := by
  constructor
  · intro h w hw
    rw [← diagonal_iff]
    intro S
    have := h 0 (fun _ => S) (fun _ v => if v = w then 1 else 0)
    unfold dCM at this
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at this
    rw [Finset.sum_eq_single w] at this
    · simp only [if_true, one_mul] at this
      rcases mul_eq_zero.1 this with h3 | h3
      · linarith
      · linarith
    · intro b _ hb; simp [hb]
    · intro hnot; exact absurd (mem_univ w) hnot
  · intro h n O α
    unfold dCM
    apply sum_eq_zero
    intro w _
    rcases lt_or_ge 0 (π w) with hw | hw
    · rw [h w hw]
      simp [E, Pi.single_apply]
    · have h0 : π w = 0 := le_antisymm hw (hπ w)
      rw [h0, zero_mul]

/-- **The finding's witness.** The flat frame `P ≡ (1/2, 1/2)` is immodest (its one cell is
everything), yet `D_CM = 1/2` on the bet `(1, −1)` at the selection "bet at world 0 only". So
"`D_CM = 0` for all selections" is omniscience, strictly stronger than immodesty.
Source: root-deference-2-010 (i) (finding F2); the dependency's `flat`
Kind: N+
Fidelity: exact -/
theorem flat_immodest_dCM_ne : flat.Immodest ∧
    dCM half flat (n := 0) (fun _ => ![1, -1]) (fun _ w => if w = 0 then 1 else 0) = 1 / 2 := by
  constructor
  · intro w
    have hcell : flat.cell (flat.P w) = univ := by
      ext v; simp [Frame.cell]
      fin_cases w <;> fin_cases v <;> simp [flat_P.1, flat_P.2]
    rw [Frame.selfMass, hcell]
    fin_cases w <;> simp [mass, Fin.sum_univ_two, flat_P.1, flat_P.2, half] <;> norm_num
  · unfold dCM
    simp [Fin.sum_univ_two, E, half, flat_P.1]

/-- **I1 is not a squeeze.** The flat frame (both rows `(1/2, 1/2)`) is immodest but does not
satisfy the conditional-martingale identity for the deferrer `(1/4, 3/4)` (test `X = 𝟙_{0}`:
`1/2 ≠ 1/4`). So `CondMartingaleAt` is strictly stronger than immodesty: I1 is an implication,
not an equivalence, and its proof is one instantiation — the content of the collapse is I2.
Source: none: audit r1 adversarial N8 (probe P5)
Kind: N+
Fidelity: n/a -/
theorem flat_immodest_not_cm :
    flat.Immodest ∧ ¬ CondMartingaleAt (![1 / 4, 3 / 4] : Fin 2 → ℝ) flat 0 := by
  refine ⟨flat_immodest_dCM_ne.1, ?_⟩
  intro h
  have hcell : flat.cell (flat.P 0) = univ := by
    ext v; simp only [Frame.mem_cell, mem_univ, iff_true]
    fin_cases v <;> simp [flat_P.1, flat_P.2]
  have := h (ind {0})
  rw [hcell] at this
  simp [E, mass, Fin.sum_univ_two, flat_P.1, half, ind] at this
  norm_num at this

end

end Cleanroom.Trust.TtFiniteFrames
