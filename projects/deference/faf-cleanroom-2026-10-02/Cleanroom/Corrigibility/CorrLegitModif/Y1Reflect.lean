import Cleanroom.Corrigibility.CorrLegitModif.Y1Legit

/-!
# corr-legit-modif — T1(d): Reflection toward the installed state, from which judge

[[hudson-respondent]] B2(b) and [[yudkowsky-respondent]] B4: Reflection toward the overwriting
install `Q_ow = P^hon(· | modify, L)` (`Q_ow(W) = 1/2`) **holds from the coarse `P_{t₁}`** and
**fails from the `σ_A`-informed deferrer on both cells** (`P(W | σ_A = r, modify, L) = 1/10`,
`P(W | σ_A = w, modify, L) = 9/10`); toward the additive install `Q_add(σ_A)` it holds from the
informed deferrer by construction (Y1c). The decision differs between the informed state and the
install exactly at `σ_A = r` (`E[X | L, modify, r] = +1/2` against `E_Q X = −3/2`; at `w`,
`−7/2` against `−3/2`) — the dodged cell is the decision-flip cell. The general half of
corr-wf14b-2-002's conjecture is `coarse_install_reflects_iff`: an install equal to the coarse
conditional `π(· | C)` is reflected from a refinement `A ⊆ C` of its cell iff
`π(· | A) = π(· | C)`.

All statements are at `P(L) = 1` with the deferrers `restrict (y1 1) (L ∩ {σ_A = a})`
(informed) and `restrict (y1 1) L` (coarse), in `ReflectsWrt` on the decision question or in
`Reflects`; Y1 scope clause throughout.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrLegitGeneral

noncomputable section

/-! ## The general lemma (2-002's general half) -/

/-- **Coarse install, refined judge.** Let `ρ = π(· | C)` (product form `ρ w · π(C) = π w · 𝟙_C w`,
`0 < π(C)`) be a row whose cell contains `C`, and `A ⊆ C` a refinement of the install's
conditioning event. The candidate-`ρ` clause of Reflection from the refined deferrer
`restrict π A` holds iff `π(· | A) = π(· | C)` in product form
(`π w · 𝟙_A w · π(C) = π(A) · π w · 𝟙_C w`): the install is reflected from the finer state iff
refining does not move the conditional.
Source: corr-wf14b-2-002 (general half); [[hudson-respondent]] B2(b) l. 51
Kind: L
Fidelity: exact
Hyps: (a) `A ⊆ C ⊆ F.cell ρ`, `0 < π(C)`, `ρ` the conditional on `C` -/
theorem coarse_install_reflects_iff {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    {F : Frame W} {ρ : W → ℝ} {A C : Finset W} (hAC : A ⊆ C) (hC : C ⊆ F.cell ρ)
    (hCpos : 0 < mass π C) (hρ : ∀ w, ρ w * mass π C = π w * ind C w) :
    (∀ w, restrict π A w * ind (F.cell ρ) w = mass (restrict π A) (F.cell ρ) * ρ w) ↔
      ∀ w, π w * ind A w * mass π C = mass π A * (π w * ind C w) := by
  rw [reflect_clause_iff_cond (hAC.trans hC)]
  apply forall_congr'
  intro w
  rw [← hρ w]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have := mul_right_cancel₀ hCpos.ne' (h.trans (by ring : mass π A * (ρ w * mass π C) =
      (mass π A * ρ w) * mass π C))
    exact this

/-! ## The cell of the installed row -/

/-- The cell of the overwriting install is `modify` (for `0 < λ`): every modify-world carries the
install and no keep-world does (the install is positive at the base point, where every keep row
vanishes).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem y1Frame_cell_mod {lam : ℝ} (hl0 : 0 < lam) (hl : 0 ≤ lam ∧ lam ≤ 1) {w : Y1W}
    (hw : w.2.2.2 = true) : (y1Frame lam hl).cell ((y1Frame lam hl).P w) = modSet := by
  have hpos := mass_fibre_gLV_pos hl0 hl
  ext v
  rw [Frame.mem_cell]
  simp only [y1Frame, hw, if_true, modSet, mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    by_contra hnv
    rw [if_neg hnv] at hv
    have h1 : condRow (y1 lam) gLV wL wL = y1 lam wL / mass (y1 lam) (fibre gLV wL) := by
      rw [condRow_apply_of_pos hpos]; simp [ind]
    have h2 : condRow (y1 lam) f3 v wL = 0 := by
      have hvpos := mass_fibre_f3_keep_pos hl0 hl (w := v) (by simpa using hnv)
      rw [condRow_apply_of_pos hvpos]
      have : wL ∉ fibre f3 v := by
        rw [mem_fibre]; simp only [f3, wL]; simp [hnv]
      simp [ind, this]
    rw [hv] at h2
    rw [h2] at h1
    have : 0 < y1 lam wL / mass (y1 lam) (fibre gLV wL) := by
      apply div_pos _ hpos
      norm_num [y1Pol, wL, pL, pS, pSig, pMod, modRate, eps]; exact hl0
    linarith
  · intro hv; rw [if_pos hv]

/-- Restriction to `L ∩ A` is restriction to `A` at `P(L) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_y1_one_inter (A : Finset Y1W) : restrict (y1 1) (Lset ∩ A) = restrict (y1 1) A := by
  rw [← restrict_restrict, restrict_y1_one_L]

/-! ## Reflection toward the overwriting install -/

/-- **From the `σ_A`-informed deferrer, Reflection toward the overwriting install fails on both
cells**: at `σ_A = r`, `P(W ∧ modify | L, r) = 9/1000` against `P(modify | L, r) · Q_ow(W) =
(9/100)(1/2)`; at `σ_A = w`, `81/1000` against the same `45/1000` — the local Reflection clause
on the decision question fails at the installed row and the partial answer `W`.
Scope: the Y1 scope clause; `P(L) = 1`; judge `restrict π (L ∩ {σ_A = a})`.
Source: [[hudson-respondent]] B2(b) l. 51 ("fails in both cells"); [[yudkowsky-respondent]] B4
l. 75 (`P_{t₁}(· | σ_A, P_{t₂} = Q) ≠ Q` in both cells); [[legitimacy-general-final]]
Statement 8(d) l. 62 ("true `9/10` against installed `1/2`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem y1_informed_not_reflectsWrt (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) (a : Bool) :
    ¬ ReflectsWrt sQ (restrict (y1 1) (Lset ∩ aCell a)) (y1Frame 1 h) := by
  intro hR
  have hpos : 0 < restrict (y1 1) (Lset ∩ aCell a) (true, true, a, true) := by
    rw [restrict_apply, if_pos (by simp [Lset, aCell])]
    cases a <;> norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
  have hρ : (y1Frame 1 h).P (true, true, a, true) ∈
      (y1Frame 1 h).cands (restrict (y1 1) (Lset ∩ aCell a)) :=
    Frame.P_mem_cands _ hpos
  have hcell := y1Frame_cell_mod (lam := 1) (by norm_num) h (w := (true, true, a, true)) rfl
  have hrow := y1Frame_rows_sW (lam := 1) (by norm_num) h (true, true, a, true)
  simp only [if_true] at hrow
  have := hR _ hρ {true}
  rw [answer_sQ_true, hcell, hrow] at this
  rw [mass_restrict, mass_restrict] at this
  simp only [mass, modSet, sW, Lset, aCell, ← filter_and, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, true_and] at this
  cases a <;> norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps] at this

/-- **From the coarse deferrer, Reflection toward the overwriting install holds** (on the decision
question, and in fact candidate-wise: `y1Frame_one_reflects`): `P(W | modify, L) = 1/2 = Q_ow(W)`.
Scope: the Y1 scope clause; `P(L) = 1`; judge `restrict π L`.
(One rewrite and `reflectsWrt_of_reflects`; regraded L at audit round 1.)
Source: [[hudson-respondent]] B2(b) l. 51 ("judged from the *coarse* state … holds");
[[yudkowsky-respondent]] B4 l. 75 ("reflection holds only with `σ_A` integrated out")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem y1_coarse_reflectsWrt (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) :
    ReflectsWrt sQ (restrict (y1 1) Lset) (y1Frame 1 h) := by
  rw [restrict_y1_one_L]
  exact reflectsWrt_of_reflects (y1Frame_one_reflects h) sQ

/-! ## The additive install -/

/-- The map `(ℓ, σ_A, v)`: its fibre through `(L, ·, a, modify)` is the additive install's
conditioning event `L ∩ {σ_A = a} ∩ modify`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def gLAV : Y1W → Bool × Bool × Bool := fun w => (w.1, w.2.2.1, w.2.2.2)

/-- The map `(σ_A, v)`: the four cells of the additive successor at `P(L) = 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def f4 : Y1W → Bool × Bool := fun w => (w.2.2.1, w.2.2.2)

/-- **The additive successor frame `F_add`**: at a modify-world with signal `a` the row is the
additive install `P^hon(· | modify, L, σ_A = a)`; at a keep-world the own continuation.
Scope: the Y1 scope clause with the additive install.
Source: [[legitimacy-general-final]] Proofs l. 134 (Y1c)
Kind: D
Fidelity: exact -/
def y1FrameAdd (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) : Frame Y1W where
  P := fun w => if w.2.2.2 then condRow (y1 lam) gLAV (true, true, w.2.2.1, true)
    else condRow (y1 lam) f3 w
  P_mem := fun w => by
    show (if w.2.2.2 then condRow (y1 lam) gLAV (true, true, w.2.2.1, true)
      else condRow (y1 lam) f3 w) ∈ stdSimplex ℝ Y1W
    split_ifs <;> exact condRow_mem (y1Pol_nonneg hl false) _ _

/-- The `(ℓ, σ_A, v)`-fibre of `(L, ·, a, modify)` is `L ∩ {σ_A = a} ∩ modify`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_gLAV (a : Bool) : fibre gLAV (true, true, a, true) = Lset ∩ aCell a ∩ modSet := by
  ext v; simp [mem_fibre, gLAV, Lset, aCell, modSet, Prod.ext_iff]

/-- The `(σ_A, v)`-fibre of a world is `{σ_A = a} ∩ modify` or `{σ_A = a} ∩ keep`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_f4 (w : Y1W) :
    fibre f4 w = univ.filter (fun v => v.2.2.1 = w.2.2.1 ∧ v.2.2.2 = w.2.2.2) := by
  ext v; simp [mem_fibre, f4, Prod.ext_iff]

/-- At `P(L) = 1` the additive successor frame is the Bayesian refinement along `(σ_A, v)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem y1FrameAdd_one_P (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) :
    (y1FrameAdd 1 h).P = (refineFrame (y1 1) (y1Pol_nonneg h false) f4).P := by
  funext w
  simp only [y1FrameAdd, refineFrame_P]
  split_ifs with hv
  · apply condRow_eq_of_subset_null
    · intro v hv'
      rw [fibre_gLAV] at hv'
      rw [fibre_f4]
      simp only [mem_inter, Lset, aCell, modSet, mem_filter, mem_univ, true_and] at hv'
      simp [hv'.1.2, hv'.2, hv]
    · intro v hv' hnv
      rw [fibre_gLAV] at hnv
      rw [fibre_f4] at hv'
      simp only [mem_filter, mem_univ, true_and] at hv'
      simp only [mem_inter, Lset, aCell, modSet, mem_filter, mem_univ, true_and] at hnv
      apply y1_one_null_offL
      by_contra hL
      have hL' : v.1 = true := by simpa using hL
      exact hnv ⟨⟨hL', hv'.1⟩, hv'.2.trans hv⟩
    · rw [fibre_gLAV]
      apply mass_pos_of_mem (y1Pol_nonneg h false) (q := Lset ∩ aCell w.2.2.1 ∩ modSet)
        (w := (true, true, w.2.2.1, true))
      · simp [Lset, aCell, modSet]
      · cases w.2.2.1 <;> norm_num [y1Pol, pL, pS, pSig, pMod, modRate, eps]
  · apply condRow_eq_of_fibre_eq
    rw [fibre_f4]
    ext v
    simp only [mem_fibre, f3, mem_filter, mem_univ, true_and, Prod.mk.injEq]
    have hv : w.2.2.2 = false := by simpa using hv
    rw [hv]
    cases v.2.2.2 <;> simp

/-- **From the `σ_A`-informed deferrer, Reflection toward the additive install holds** — on every
question, since the additive successor is the Bayesian refinement along `(σ_A, v)` and the
informed deferrer is a union of its fibres (Y1c: "the additive state … equals the agent's informed
state by construction").
Scope: the Y1 scope clause with the additive install; `P(L) = 1`; judge
`restrict π (L ∩ {σ_A = a})`.
Source: [[legitimacy-general-final]] Proofs l. 134 (Y1c); [[yudkowsky-respondent]] B4 l. 75
("the additive state … is")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem y1_additive_informed_reflects (h : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) (a : Bool) :
    Reflects (restrict (y1 1) (Lset ∩ aCell a)) (y1FrameAdd 1 h) ∧
    ReflectsWrt sQ (restrict (y1 1) (Lset ∩ aCell a)) (y1FrameAdd 1 h) := by
  have hR : Reflects (restrict (y1 1) (Lset ∩ aCell a)) (y1FrameAdd 1 h) := by
    rw [restrict_y1_one_inter]
    refine reflects_of_P_eq (y1FrameAdd_one_P h).symm
      (reflects_restrict_refineFrame _ f4 (aCell a) ?_)
    intro w hw v hv
    simp only [aCell, mem_filter, mem_univ, true_and] at hw ⊢
    simp only [f4, Prod.mk.injEq] at hv
    rw [hv.1, hw]
  exact ⟨hR, reflectsWrt_of_reflects hR sQ⟩

/-! ## The dodged cell is the decision-flip cell -/

/-- **`y1_dodge_cell_iff`**: the informed decision (the additive install's, `P(· | L, modify,
σ_A)`) and the overwriting install's decision differ exactly at `σ_A = r`: there the informed
state continues (`E[X] = 1/2`) and the install stops (`E_Q X = −3/2`); at `σ_A = w` both stop
(`−7/2`, `−3/2`). The cell the dodge is chosen in is the cell where the decision flips.
Scope: the Y1 scope clause.
Source: [[hudson-respondent]] B2(b) l. 51 ("the *decision* differs only at `σ_A = r` … which is
exactly the cell the dodge is chosen in"); [[yudkowsky-respondent]] `y1_reflection_check.out`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem y1_dodge_cell_iff :
    (∀ a, (contOf (qaddW a) (qaddR a) ↔ ¬ contOf qowW qowR) ↔ a = false) ∧
    (qaddR false - 4 * qaddW false) / (qaddW false + qaddR false) = 1 / 2 ∧
    (qaddR true - 4 * qaddW true) / (qaddW true + qaddR true) = -7 / 2 ∧
    (qowR - 4 * qowW) / (qowW + qowR) = -3 / 2 := by
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · cases a <;> norm_num [contOf, qowW, qowR, qaddW, qaddR, eps, pMod, pSig]
  all_goals norm_num [qowW, qowR, qaddW, qaddR, eps, pMod, pSig]

end

end Cleanroom.Corrigibility.CorrLegitModif
