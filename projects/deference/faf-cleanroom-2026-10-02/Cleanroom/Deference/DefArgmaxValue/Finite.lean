import Cleanroom.Deference.DefLatticeArrows.Wedge

/-!
# `def-argmax-value` · Finite: the keep-or-switch telescope and the one-shot hedge, finite-exact (target 10)

The two threshold-0 routes of the 07-20/07-23 arc — the **keep-or-switch telescope**
([[keep-or-switch-telescope]], lean-deference-063, vq-wiki-024) and the **one-shot hedge**
([[one-shot-hedge]], lean-deference-2-013, vq-wiki-025) — **retracted as LI theorems** in the
07-23 arc (lean-deference-064: exact F1 is false for inductor-experts; the "linear-extension
surrogate" smuggled expert-side content into notation) and surviving as **finite-exact**
statements: pure arithmetic on decided quotes, and `Finset` identities on a finite frame. Nothing
here is an LI theorem; the true-setting replacement is target 9 (`Hedged.lean`) and the scoped
theorem (`Theorem.lean`).

Two levels:

* **Quote level** (the expert side, "Claim A"): quotes are real numbers, the ramp `ctsInd` is
  FAF's. The one-shot hedge `m_i + d·Ind_δ(d > 0)` with `d := M − m_i ≥ 0` lies in
  `[M − δ, M]` (`hedgedOneShot_mem`); the hard one-shot `m_i + d·1[d > 0]` is `M` exactly
  (`hardOneShot_eq_max`). Along a processing order `m : ℕ → ℝ` (position `0` the comparison
  option), the hard chain `V_{k+1} = V_k + (m_{k+1} − V_k)·1[m_{k+1} − V_k > 0]` **is** the running
  max (`hardChain_eq_runMax` — Claim B at quote level, first-max-wins), and the hedged chain
  `V_{k+1} = V_k + (m_{k+1} − V_k)·Ind_δ(m_{k+1} − V_k > 0)` stays in `[M_k − δ, M_k]` — **the
  δ-loss does not accumulate** (`hedgedChain_mem`, the page's "⚠ (write-up) — verified" claim,
  proved).
* **Frame level** (the novice side): worlds `W` finite, novice weights `π` (no normalization),
  the expert's frame estimate `est P X w := ∑_v P_wv X_v` (the kernel of `value_of_argmax`), and
  the one-shot / chain strategies as world functions. The novice-side identities are exact
  linearity: the one-shot hedge's value gap against the incumbent is the **soft threshold-0 cut**
  `softCut` of `Wedge.lean` on the bet `D := S − O^i` (`oneShotHedge_identity`); the hard
  one-shot's is the strict hard cut (`oneShotHard_identity`); each telescope rung is the same
  identity on `D_k := O^{k+1} − Ŝ^{(k)}` (`hardChainFrame_rung`, `hedgedChainFrame_rung`), and the
  telescope sums the `K` rungs (`*_telescope`), so `K` nonnegative cuts give finite-exact Value
  against the comparison option (`*_value`). The expert-side Claim A transfers to the frame under
  the **frame fold** (the indicator or ramp is constant on the support of `P w ·` — the finite
  form of "the expert knows its own estimate", a disclosed hypothesis): `est_hardChainFrame`,
  `est_hedgedChainFrame`.

The wedge — the near-threshold layer `D·(1[E*(D) > 0] − Ind_δ(E*(D) > 0))` that threshold-0
Total Trust leaves unconstrained — is `Wedge.lean`'s `separation` (cited, not redone). Each rung
is the two-option identity of `def-lattice`'s `TwoOptionFinite` in shape, with the tie toward
the *incumbent* (switch only on strict improvement — Claim B's first-max-wins wrinkle) and a
non-constant incumbent; `twoOption_identity_above` is the constant-incumbent, tie-toward-the-bet
case.

Not construction-facing; no FAF construction import (`ctsInd` and the wedge vocabulary only).
-/

namespace Cleanroom.Deference.DefArgmaxValue.Finite

open Finset LogicalInduction
open Cleanroom.Found.DefLattice.TwoOptionFinite Cleanroom.Deference.DefLatticeArrows.Wedge

noncomputable section

/-! ## Ramp arithmetic (FAF's `ctsInd`) -/

/-- The ramp is nonnegative.
Source: none: infrastructure (FAF `ctsInd_mem_Icc`)
Kind: L
Fidelity: n/a -/
theorem ramp_nonneg (δ : ℚ) (x y : ℝ) : 0 ≤ ctsInd δ x y := (ctsInd_mem_Icc δ x y).1

/-- The ramp is at most one.
Source: none: infrastructure (FAF `ctsInd_mem_Icc`)
Kind: L
Fidelity: n/a -/
theorem ramp_le_one (δ : ℚ) (x y : ℝ) : ctsInd δ x y ≤ 1 := (ctsInd_mem_Icc δ x y).2

/-- The ramp vanishes at or below its threshold (lean-deference-2-017 (i): one-sidedness at the
boundary).
Source: lean-deference-2-017 (i); none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ramp_eq_zero_of_sub_nonpos {δ : ℚ} (hδ : 0 < δ) {x y : ℝ} (h : x - y ≤ 0) :
    ctsInd δ x y = 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  have : (x - y) / (δ : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hδR.le
  rw [max_eq_left this, min_eq_right zero_le_one]

/-! ## 10a — Soft Claim A, one shot (the expert side of `one-shot-hedge` §Proof) -/

/-- **The hedged one-shot quote** `m_i + d · Ind_δ(d > 0)`: the expert's quote of the one-shot
hedge `(1 − θ)O^i + θŜ`, `θ := Ind_δ(E*(Ŝ − O^i) > 0)`, written in the quotes `m_i := E*(O^i)`
and `d := E*(Ŝ) − E*(O^i) = M − m_i` (surrogate linearity, which at quote level is a definition).
Source: [[one-shot-hedge]] §Construction (`T_δ := O^i + D·θ`), §Proof (expert side)
Kind: D
Fidelity: exact (quote level; the LI form is retracted, lean-deference-064) -/
def hedgedOneShot (δ : ℚ) (mi d : ℝ) : ℝ := mi + d * ctsInd δ d 0

/-- The hedged one-shot quote is at most the max `m_i + d`: a convex combination of `m_i ≤ M`
and `M`.
Source: [[one-shot-hedge]] §Proof ("`E*(T_δ) ≤ M_K` always")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ d` -/
theorem hedgedOneShot_le_max (δ : ℚ) {mi d : ℝ} (hd : 0 ≤ d) :
    hedgedOneShot δ mi d ≤ mi + d := by
  unfold hedgedOneShot
  have := mul_le_of_le_one_right hd (ramp_le_one δ d 0)
  linarith

/-- The hedged one-shot quote is at least `M − δ`: if `d ≥ δ` the ramp saturates and the quote
is `M`; if `d < δ` the quote is at least `m_i = M − d > M − δ`. One `δ`-loss, at a near-tie only.
Source: [[one-shot-hedge]] §Proof (the two cases `d ≥ δ`, `0 ≤ d < δ`); lean-deference-2-013
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ`, `0 ≤ d` -/
theorem max_sub_le_hedgedOneShot {δ : ℚ} (hδ : 0 < δ) {mi d : ℝ} (hd : 0 ≤ d) :
    mi + d - δ ≤ hedgedOneShot δ mi d := by
  unfold hedgedOneShot
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  rcases le_or_gt (δ : ℝ) d with h | h
  · rw [ctsInd_eq_one_of_le_sub δ d 0 hδ (by simpa using h)]
    linarith
  · have := mul_nonneg hd (ramp_nonneg δ d 0)
    linarith

/-- **Soft Claim A, one shot**: `M − δ ≤ m_i + d·Ind_δ(d > 0) ≤ M` for `d := M − m_i ≥ 0`.
Source: [[one-shot-hedge]] §Statement (`Γ ⊢ M_K − δ ≤ E*(T_δ) ≤ M_K`), quote level;
lean-deference-2-013; vq-wiki-025
Kind: P
Fidelity: exact (quote level; the `Γ ⊢` form is the retracted surrogate)
Hyps: (a) `0 < δ`, `0 ≤ d` -/
theorem hedgedOneShot_mem {δ : ℚ} (hδ : 0 < δ) {mi d : ℝ} (hd : 0 ≤ d) :
    mi + d - δ ≤ hedgedOneShot δ mi d ∧ hedgedOneShot δ mi d ≤ mi + d :=
  ⟨max_sub_le_hedgedOneShot hδ hd, hedgedOneShot_le_max δ hd⟩

/-- **The hard one-shot quote** `m_i + d · 1[d > 0]` — keep the comparison option on ties.
Source: [[one-shot-hedge]] §Proof ("Hard variant")
Kind: D
Fidelity: exact (quote level) -/
def hardOneShot (mi d : ℝ) : ℝ := mi + d * (if 0 < d then 1 else 0)

/-- **The hard one-shot attains the max exactly**: `m_i + d·1[d > 0] = M` for `d = M − m_i ≥ 0`
(on a tie the comparison option itself attains the max).
Source: [[one-shot-hedge]] §Proof ("Hard variant": "Either way `Γ ⊢ E*(T) = M_K` exactly")
Kind: P
Fidelity: exact (quote level; the "keep on ties" tie-break is explicit)
Hyps: (a) `0 ≤ d` -/
theorem hardOneShot_eq_max {mi d : ℝ} (hd : 0 ≤ d) : hardOneShot mi d = mi + d := by
  unfold hardOneShot
  rcases lt_or_eq_of_le hd with h | h
  · simp [h]
  · simp [← h]

/-- The maximum quote of a finite menu, as `Finset.sup'`.
Source: none: infrastructure (`def-lattice`'s `Menu.maxQuote`, quote level)
Kind: D
Fidelity: n/a -/
def menuMax {J : Type*} [Fintype J] [Nonempty J] (m : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty m

/-- Every quote is at most the menu max.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem le_menuMax {J : Type*} [Fintype J] [Nonempty J] (m : J → ℝ) (i : J) :
    m i ≤ menuMax m :=
  Finset.le_sup' m (Finset.mem_univ i)

/-- **Soft and hard Claim A on a finite menu**: for quotes `m : J → ℝ` and a comparison index
`i`, with `M := max_j m_j` and `d := M − m_i`, the hedged one-shot quote lies in `[M − δ, M]`
and the hard one-shot quote is `M`.
Source: [[one-shot-hedge]] §Statement, §Proof; lean-deference-2-013; vq-wiki-025
Kind: P
Fidelity: exact (quote level)
Hyps: (a) `0 < δ` -/
theorem oneShot_claimA {J : Type*} [Fintype J] [Nonempty J] {δ : ℚ} (hδ : 0 < δ)
    (m : J → ℝ) (i : J) :
    menuMax m - δ ≤ hedgedOneShot δ (m i) (menuMax m - m i) ∧
      hedgedOneShot δ (m i) (menuMax m - m i) ≤ menuMax m ∧
      hardOneShot (m i) (menuMax m - m i) = menuMax m := by
  have hd : 0 ≤ menuMax m - m i := sub_nonneg.2 (le_menuMax m i)
  refine ⟨?_, ?_, ?_⟩
  · have := max_sub_le_hedgedOneShot hδ (mi := m i) hd
    linarith
  · have := hedgedOneShot_le_max δ (mi := m i) hd
    linarith
  · rw [hardOneShot_eq_max hd]
    ring

/-! ## 10a — Soft Claim A, the telescope: the δ-loss does not accumulate -/

/-- **The running maximum** `M_k := max_{j ≤ k} m_j` along the processing order (`m 0` is the
comparison option, promoted to the front).
Source: [[keep-or-switch-telescope]] §Setting ("the *running* max `M_k`")
Kind: D
Fidelity: exact -/
def runMax (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => m 0
  | k + 1 => max (runMax m k) (m (k + 1))

/-- Every earlier quote is at most the running max.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem le_runMax (m : ℕ → ℝ) (j : ℕ) : ∀ k, j ≤ k → m j ≤ runMax m k := by
  intro k
  induction k with
  | zero =>
    intro h
    rw [Nat.le_zero.1 h]
    simp [runMax]
  | succ k ih =>
    intro h
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (by simp [runMax])
    · rw [le_antisymm h hge]
      simp [runMax]

/-- The running max is attained by some earlier quote.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem runMax_mem (m : ℕ → ℝ) : ∀ k, ∃ j, j ≤ k ∧ runMax m k = m j := by
  intro k
  induction k with
  | zero => exact ⟨0, le_rfl, by simp [runMax]⟩
  | succ k ih =>
    obtain ⟨j, hj, hjeq⟩ := ih
    rcases le_total (runMax m k) (m (k + 1)) with h | h
    · exact ⟨k + 1, le_rfl, by simp [runMax, max_eq_right h]⟩
    · exact ⟨j, hj.trans (Nat.le_succ k), by simp only [runMax]; rw [max_eq_left h, hjeq]⟩

/-- **The hard keep-or-switch chain at quote level**: `V_0 := m_0`,
`V_{k+1} := V_k + (m_{k+1} − V_k)·1[m_{k+1} − V_k > 0]` — switch to the newcomer iff the expert
rates it strictly above the incumbent.
Source: [[keep-or-switch-telescope]] §Construction (`Ŝ^(k) := Ŝ^(k−1) + D_k·1[E*(D_k) > 0]`),
quote level; lean-deference-063
Kind: D
Fidelity: exact (quote level) -/
def hardChain (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => m 0
  | k + 1 =>
    hardChain m k + (m (k + 1) - hardChain m k) * (if 0 < m (k + 1) - hardChain m k then 1 else 0)

/-- **The hedged keep-or-switch chain at quote level**: `V_0 := m_0`,
`V_{k+1} := V_k + (m_{k+1} − V_k)·Ind_δ(m_{k+1} − V_k > 0)` — each keep-or-switch hedged across a
ramp of width `δ`; `V_{k+1} = (1 − θ_{k+1})V_k + θ_{k+1} m_{k+1}` is a convex combination.
Source: [[keep-or-switch-telescope]] §Construction (the `δ`-hedged variant), quote level;
vq-wiki-024
Kind: D
Fidelity: exact (quote level) -/
def hedgedChain (δ : ℚ) (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => m 0
  | k + 1 =>
    hedgedChain δ m k +
      (m (k + 1) - hedgedChain δ m k) * ctsInd δ (m (k + 1) - hedgedChain δ m k) 0

/-- **Hard Claim A / Claim B at quote level**: the hard chain *is* the running max — the chain
implements the first-max-wins argmax, `E*(Ŝ^(k)) = M_k` exactly.
Source: [[keep-or-switch-telescope]] §Claim A, §Claim B (first-max-wins); lean-deference-063
Kind: P
Fidelity: exact (quote level; the `Γ ⊢` form is the retracted surrogate, lean-deference-064)
Hyps: (a) none -/
theorem hardChain_eq_runMax (m : ℕ → ℝ) : ∀ k, hardChain m k = runMax m k := by
  intro k
  induction k with
  | zero => simp [hardChain, runMax]
  | succ k ih =>
    simp only [hardChain, runMax]
    rw [ih]
    by_cases h : 0 < m (k + 1) - runMax m k
    · rw [if_pos h, max_eq_right (by linarith)]
      ring
    · have h' := not_lt.1 h
      rw [if_neg h, max_eq_left (by linarith)]
      ring

/-- The hedged chain never exceeds the running max: each step is a convex combination of the
incumbent's value `≤ M_k` and the newcomer's quote `≤ M_{k+1}`.
Source: [[keep-or-switch-telescope]] §Claim A ("Upper bound")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem hedgedChain_le_runMax (δ : ℚ) (m : ℕ → ℝ) : ∀ k, hedgedChain δ m k ≤ runMax m k := by
  intro k
  induction k with
  | zero => simp [hedgedChain, runMax]
  | succ k ih =>
    simp only [hedgedChain, runMax]
    set V := hedgedChain δ m k with hV
    set X := max (runMax m k) (m (k + 1)) with hX
    have hVX : V ≤ X := ih.trans (le_max_left _ _)
    have hmX : m (k + 1) ≤ X := le_max_right _ _
    have hθ0 := ramp_nonneg δ (m (k + 1) - V) 0
    have hθ1 := ramp_le_one δ (m (k + 1) - V) 0
    have key : X - (V + (m (k + 1) - V) * ctsInd δ (m (k + 1) - V) 0) =
        (X - V) * (1 - ctsInd δ (m (k + 1) - V) 0) +
          (X - m (k + 1)) * ctsInd δ (m (k + 1) - V) 0 := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 hVX) (sub_nonneg.2 hθ1),
      mul_nonneg (sub_nonneg.2 hmX) hθ0]

/-- **The δ-loss does not accumulate**: the hedged chain is at least `M_k − δ` at every rung.
Step: with `d := m_{k+1} − V_k`, `θ := Ind_δ(d > 0)`: `d·θ ≥ 0` always (`θ = 0` when `d ≤ 0`), so
`V_{k+1} ≥ V_k ≥ M_k − δ`; and `V_{k+1} ≥ m_{k+1} − δ` (`θ = 1` when `d ≥ δ`; `V_k = m_{k+1} − d >
m_{k+1} − δ` when `d < δ`). The loss is a single `δ`, uniformly in `k` — the page's "⚠ (write-up)
— verified" claim, proved.
Source: [[keep-or-switch-telescope]] §Claim A ("Soft Claim A … the δ-loss does not accumulate");
vq-wiki-024
Kind: P
Fidelity: exact (quote level)
Hyps: (a) `0 < δ` -/
theorem runMax_sub_le_hedgedChain {δ : ℚ} (hδ : 0 < δ) (m : ℕ → ℝ) :
    ∀ k, runMax m k - δ ≤ hedgedChain δ m k := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  intro k
  induction k with
  | zero =>
    simp only [hedgedChain, runMax]
    linarith
  | succ k ih =>
    simp only [hedgedChain, runMax]
    set V := hedgedChain δ m k with hV
    set d := m (k + 1) - V with hd
    have hθ0 := ramp_nonneg δ d 0
    have hdθ : 0 ≤ d * ctsInd δ d 0 := by
      rcases le_or_gt 0 d with h | h
      · exact mul_nonneg h hθ0
      · rw [ramp_eq_zero_of_sub_nonpos hδ (by linarith : d - 0 ≤ 0)]
        simp
    have h2 : d ≤ d * ctsInd δ d 0 + δ := by
      rcases le_or_gt (δ : ℝ) d with h | h
      · rw [ctsInd_eq_one_of_le_sub δ d 0 hδ (by simpa using h)]
        linarith
      · linarith
    rw [sub_le_iff_le_add, max_le_iff]
    constructor
    · linarith
    · linarith

/-- **Soft Claim A, telescope form**: `M_k − δ ≤ V_k ≤ M_k` at every rung of the hedged chain.
Source: [[keep-or-switch-telescope]] §Claim A ("Soft Claim A: `Γ ⊢ M_k − δ ≤ E*(Ŝ^(k)_δ) ≤ M_k`"),
quote level; lean-deference-063; vq-wiki-024
Kind: P
Fidelity: exact (quote level; the `Γ ⊢` form is the retracted surrogate, lean-deference-064)
Hyps: (a) `0 < δ` -/
theorem hedgedChain_mem {δ : ℚ} (hδ : 0 < δ) (m : ℕ → ℝ) (k : ℕ) :
    runMax m k - δ ≤ hedgedChain δ m k ∧ hedgedChain δ m k ≤ runMax m k :=
  ⟨runMax_sub_le_hedgedChain hδ m k, hedgedChain_le_runMax δ m k⟩

/-! ## 10b — The finite-exact novice-side identities on a frame -/

section Frame

variable {W : Type*} [Fintype W]

/-- **The expert's frame estimate** of a bet `X` at world `w`: `∑_v P_wv X_v` — the kernel form
of `def-lattice-arrows`' `value_of_argmax` (`hstar`'s `∑ v, P w v * O j v`).
Source: [[keep-or-switch-telescope]] §Setting ("Derived estimates"); `def-lattice-arrows` `Finite.lean`
Kind: D
Fidelity: exact (finite frame) -/
def est (P : W → W → ℝ) (X : W → ℝ) (w : W) : ℝ := ∑ v, P w v * X v

/-- The frame estimate is additive in the bet.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem est_add (P : W → W → ℝ) (X Y : W → ℝ) (w : W) :
    est P (fun v => X v + Y v) w = est P X w + est P Y w := by
  unfold est
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => by ring)

/-- The frame estimate respects differences of bets.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem est_sub (P : W → W → ℝ) (X Y : W → ℝ) (w : W) :
    est P (fun v => X v - Y v) w = est P X w - est P Y w := by
  unfold est
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun v _ => by ring)

/-- **The strict hard threshold-0 cut** `∑_w π_w X_w 1[0 < e_w]` — the hard indicator of the
telescope and the one-shot hedge (`1[E*(D) > 0]`, switch only on strict improvement), against
`Wedge.lean`'s `hardCut` with DDB's `≥`.
Source: [[keep-or-switch-telescope]] §Construction (`1[E*(D_k) > 0]`); lean-deference-2-015
Kind: D
Fidelity: exact -/
def strictHardCut (π e X : W → ℝ) : ℝ := ∑ w, π w * (X w * if 0 < e w then 1 else 0)

/-- Off the boundary `e = 0` the strict and non-strict hard cuts agree.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem strictHardCut_eq_hardCut (π e X : W → ℝ) (he : ∀ w, e w ≠ 0) :
    strictHardCut π e X = hardCut π e X := by
  unfold strictHardCut hardCut
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : 0 < e w
  · simp [h, h.le]
  · have h' : e w < 0 := lt_of_le_of_ne (not_lt.1 h) (he w)
    simp [h, not_le.2 h']

/-- The bet of the one-shot hedge, `D := S − O^i` (newcomer minus incumbent), as a world function.
Source: [[one-shot-hedge]] §Construction (`D := Ŝ − O^i`)
Kind: D
Fidelity: exact -/
def hedgeBet (Oi S : W → ℝ) : W → ℝ := fun v => S v - Oi v

/-- **The one-shot hedge on the frame**: `T_δ := O^i + D · Ind_δ(est(D) > 0)` with `D := S − O^i`
and the ramp read at the expert's frame estimate of `D` at the same world.
Source: [[one-shot-hedge]] §Construction (`T_δ := O^i + D·θ`)
Kind: D
Fidelity: exact (finite frame) -/
def oneShotHedge (δ : ℚ) (P : W → W → ℝ) (Oi S : W → ℝ) (w : W) : ℝ :=
  Oi w + hedgeBet Oi S w * ctsInd δ (est P (hedgeBet Oi S) w) 0

/-- The one-shot hedge is the convex combination `(1 − θ)O^i + θS`.
Source: [[one-shot-hedge]] §Construction (`T_δ = (1−θ)O^i + θŜ`)
Kind: L
Fidelity: n/a -/
theorem oneShotHedge_eq_blend (δ : ℚ) (P : W → W → ℝ) (Oi S : W → ℝ) (w : W) :
    oneShotHedge δ P Oi S w =
      (1 - ctsInd δ (est P (hedgeBet Oi S) w) 0) * Oi w +
        ctsInd δ (est P (hedgeBet Oi S) w) 0 * S w := by
  unfold oneShotHedge hedgeBet
  ring

/-- **The one-shot identity, soft**: the novice's value gap of the hedge against the incumbent is
the soft threshold-0 cut on `D` — one `loe` split, exact on the frame.
Source: [[one-shot-hedge]] §Proof ("Novice side": `E^H(T_δ) ≈ E^H(O^i) + E^H(D·Ind_δ(E*(D) > 0))`);
lean-deference-2-013
Kind: L
Fidelity: exact (finite frame; `π` unnormalized)
Hyps: (a) none -/
theorem oneShotHedge_identity (δ : ℚ) (P : W → W → ℝ) (π Oi S : W → ℝ) :
    (∑ w, π w * oneShotHedge δ P Oi S w) - (∑ w, π w * Oi w) =
      softCut π (est P (hedgeBet Oi S)) (hedgeBet Oi S) δ := by
  unfold oneShotHedge softCut
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun w _ => by ring)

/-- **Finite-exact δ-hedged Value, one shot**: Value of the hedge against the incumbent ⟺ the soft
threshold-0 cut on `D` is nonnegative — `TT(D, 0)` at width `δ` *is* the one-shot inequality.
Source: [[one-shot-hedge]] §Statement, §Proof ("one `loe`, one TT"); lean-deference-2-013;
vq-wiki-025
Kind: L
Fidelity: exact (finite frame; the LI form is retracted, lean-deference-064)
Hyps: (a) none -/
theorem oneShotHedge_value_iff (δ : ℚ) (P : W → W → ℝ) (π Oi S : W → ℝ) :
    (∑ w, π w * Oi w) ≤ ∑ w, π w * oneShotHedge δ P Oi S w ↔
      0 ≤ softCut π (est P (hedgeBet Oi S)) (hedgeBet Oi S) δ := by
  rw [← sub_nonneg, oneShotHedge_identity]

/-- **The hard one-shot on the frame**: `T := O^i + D·1[est(D) > 0]` — keep the comparison option
on ties.
Source: [[one-shot-hedge]] §Proof ("Hard variant")
Kind: D
Fidelity: exact (finite frame) -/
def oneShotHard (P : W → W → ℝ) (Oi S : W → ℝ) (w : W) : ℝ :=
  Oi w + hedgeBet Oi S w * (if 0 < est P (hedgeBet Oi S) w then 1 else 0)

/-- The hard one-shot selects the newcomer where the expert strictly prefers it and the
incumbent otherwise (the "keep on ties" tie-break, explicit).
Source: [[one-shot-hedge]] §Proof ("if `M_K > m^i` then `T = Ŝ`; if `M_K = m^i` then `T = O^i`")
Kind: L
Fidelity: n/a -/
theorem oneShotHard_eq_ite (P : W → W → ℝ) (Oi S : W → ℝ) (w : W) :
    oneShotHard P Oi S w = if 0 < est P (hedgeBet Oi S) w then S w else Oi w := by
  unfold oneShotHard hedgeBet
  split_ifs <;> ring

/-- **The one-shot identity, hard**: the value gap of the hard one-shot against the incumbent is
the strict hard threshold-0 cut on `D`.
Source: [[one-shot-hedge]] §Proof ("Hard variant"); lean-deference-2-013
Kind: L
Fidelity: exact (finite frame)
Hyps: (a) none -/
theorem oneShotHard_identity (P : W → W → ℝ) (π Oi S : W → ℝ) :
    (∑ w, π w * oneShotHard P Oi S w) - (∑ w, π w * Oi w) =
      strictHardCut π (est P (hedgeBet Oi S)) (hedgeBet Oi S) := by
  unfold oneShotHard strictHardCut
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun w _ => by ring)

/-- **Finite-exact hard Value, one shot**: Value of the hard one-shot against the incumbent ⟺ the
strict hard threshold-0 cut on `D` is nonnegative. In the finite-exact setting the hard indicator
is a legal weight and the wedge is empty (`Wedge.lean` `separation` is where soft and hard part).
Source: [[one-shot-hedge]] §Proof ("Hard variant"); [[keep-or-switch-telescope]] §The wedge
Kind: L
Fidelity: exact (finite frame)
Hyps: (a) none -/
theorem oneShotHard_value_iff (P : W → W → ℝ) (π Oi S : W → ℝ) :
    (∑ w, π w * Oi w) ≤ ∑ w, π w * oneShotHard P Oi S w ↔
      0 ≤ strictHardCut π (est P (hedgeBet Oi S)) (hedgeBet Oi S) := by
  rw [← sub_nonneg, oneShotHard_identity]

/-- **Claim A on the frame, one shot**: under the frame fold at the hedge's ramp (the ramp
`Ind_δ(est(D) > 0)` is constant on the support of `P w ·`, so it factors out of the expert's
estimate — the finite form of "the expert knows its own estimate") and `0 ≤ est(D)` (the newcomer
is rated at least the incumbent, Claim A's input), the expert's frame estimate of the hedge is
`hedgedOneShot δ (est O^i) (est D)`, hence within `δ` of `est O^i + est D`; the hard one-shot's
is exactly `est O^i + est D`.
Source: [[one-shot-hedge]] §Proof (expert side); [[keep-or-switch-telescope]] §Claim A (the
`hknow` ingredient)
Kind: L
Fidelity: exact (finite frame)
Hyps: (c) `hfold`, `hfoldHard` — the frame fold (introspection as a finite hypothesis); (a) `hD` -/
theorem est_oneShot (δ : ℚ) (hδ : 0 < δ) (P : W → W → ℝ) (Oi S : W → ℝ) (w : W)
    (hfold : est P (fun v => hedgeBet Oi S v * ctsInd δ (est P (hedgeBet Oi S) v) 0) w =
      ctsInd δ (est P (hedgeBet Oi S) w) 0 * est P (hedgeBet Oi S) w)
    (hfoldHard : est P (fun v => hedgeBet Oi S v * (if 0 < est P (hedgeBet Oi S) v then 1 else 0)) w =
      (if 0 < est P (hedgeBet Oi S) w then 1 else 0) * est P (hedgeBet Oi S) w)
    (hD : 0 ≤ est P (hedgeBet Oi S) w) :
    est P (oneShotHedge δ P Oi S) w = hedgedOneShot δ (est P Oi w) (est P (hedgeBet Oi S) w) ∧
      est P Oi w + est P (hedgeBet Oi S) w - δ ≤ est P (oneShotHedge δ P Oi S) w ∧
      est P (oneShotHedge δ P Oi S) w ≤ est P Oi w + est P (hedgeBet Oi S) w ∧
      est P (oneShotHard P Oi S) w = est P Oi w + est P (hedgeBet Oi S) w := by
  have h1 : est P (oneShotHedge δ P Oi S) w =
      hedgedOneShot δ (est P Oi w) (est P (hedgeBet Oi S) w) := by
    unfold hedgedOneShot
    rw [mul_comm (est P (hedgeBet Oi S) w), ← hfold, ← est_add]
    rfl
  have h2 : est P (oneShotHard P Oi S) w = hardOneShot (est P Oi w) (est P (hedgeBet Oi S) w) := by
    unfold hardOneShot
    rw [mul_comm (est P (hedgeBet Oi S) w), ← hfoldHard, ← est_add]
    rfl
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h1]
    exact max_sub_le_hedgedOneShot hδ hD
  · rw [h1]
    exact hedgedOneShot_le_max δ hD
  · rw [h2]
    exact hardOneShot_eq_max hD

/-! ### The telescope on the frame -/

/-- **The hard keep-or-switch chain on the frame**: `Ŝ^(0) := O^0` (the comparison option, promoted
to the front), `Ŝ^(k+1) := Ŝ^(k) + (O^{k+1} − Ŝ^(k))·1[est(O^{k+1} − Ŝ^(k)) > 0]` — the expert's
frame estimate of the rung bet decides the switch at each world.
Source: [[keep-or-switch-telescope]] §Construction; lean-deference-063
Kind: D
Fidelity: exact (finite frame) -/
def hardChainFrame (P : W → W → ℝ) (O : ℕ → W → ℝ) : ℕ → W → ℝ
  | 0 => O 0
  | k + 1 => fun w =>
    hardChainFrame P O k w + (O (k + 1) w - hardChainFrame P O k w) *
      (if 0 < est P (fun v => O (k + 1) v - hardChainFrame P O k v) w then 1 else 0)

/-- The rung bet `D_{k+1} := O^{k+1} − Ŝ^(k)` of the hard chain.
Source: [[keep-or-switch-telescope]] §Construction (`D_k := O^k − Ŝ^(k−1)`)
Kind: D
Fidelity: exact -/
def hardRungBet (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) : W → ℝ :=
  fun v => O (k + 1) v - hardChainFrame P O k v

/-- The chain's step, in terms of the rung bet.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hardChainFrame_succ (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) (w : W) :
    hardChainFrame P O (k + 1) w =
      hardChainFrame P O k w +
        hardRungBet P O k w * (if 0 < est P (hardRungBet P O k) w then 1 else 0) := rfl

/-- **The rung identity, hard**: the novice's value gap between consecutive stages is the strict
hard threshold-0 cut on the rung bet — the two-option identity's shape (tie toward the
incumbent, non-constant incumbent), one `loe` per rung.
Source: [[keep-or-switch-telescope]] §Proof (the display: `E^H(Ŝ^(k)) ≈ E^H(Ŝ^(k−1)) +
E^H(D_k·1[E*(D_k) > 0])`); lean-deference-063
Kind: L
Fidelity: exact (finite frame)
Hyps: (a) none -/
theorem hardChainFrame_rung (π : W → ℝ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) :
    (∑ w, π w * hardChainFrame P O (k + 1) w) - (∑ w, π w * hardChainFrame P O k w) =
      strictHardCut π (est P (hardRungBet P O k)) (hardRungBet P O k) := by
  unfold strictHardCut
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hardChainFrame_succ]
  ring

/-- **The telescope, hard**: the value gap of stage `K` against the comparison option is the sum of
the `K` rung cuts.
Source: [[keep-or-switch-telescope]] §Proof ("Telescoping the `K − 1` rungs")
Kind: L
Fidelity: exact (finite frame)
Hyps: (a) none -/
theorem hardChainFrame_telescope (π : W → ℝ) (P : W → W → ℝ) (O : ℕ → W → ℝ) :
    ∀ K, (∑ w, π w * hardChainFrame P O K w) - (∑ w, π w * O 0 w) =
      ∑ k ∈ Finset.range K, strictHardCut π (est P (hardRungBet P O k)) (hardRungBet P O k) := by
  intro K
  induction K with
  | zero => simp [hardChainFrame]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hr := hardChainFrame_rung π P O K
    linarith

/-- **Finite-exact telescoping Value, hard**: `K` nonnegative strict hard threshold-0 cuts (one
per rung) give Value of the chain against the comparison option. Finite-exact; the LI-setting
version is retracted (lean-deference-063/064) and the true-setting replacement is target 9.
Source: [[keep-or-switch-telescope]] §Statement ("hard/finite-exact form"); lean-deference-063
Kind: P
Fidelity: exact (finite frame; uniformly bounded `K`, as the page's ⚠ requires)
Hyps: (a) `hcut` — the rung cuts, the finite form of `TT(D_k, 0)` -/
theorem hardChainFrame_value (π : W → ℝ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (K : ℕ)
    (hcut : ∀ k ∈ Finset.range K,
      0 ≤ strictHardCut π (est P (hardRungBet P O k)) (hardRungBet P O k)) :
    (∑ w, π w * O 0 w) ≤ ∑ w, π w * hardChainFrame P O K w := by
  rw [← sub_nonneg, hardChainFrame_telescope]
  exact Finset.sum_nonneg hcut

/-- **The hedged keep-or-switch chain on the frame**: `Ŝ^(k+1)_δ := Ŝ^(k)_δ + (O^{k+1} −
Ŝ^(k)_δ)·Ind_δ(est(O^{k+1} − Ŝ^(k)_δ) > 0)`.
Source: [[keep-or-switch-telescope]] §Construction (the `δ`-hedged variant); vq-wiki-024
Kind: D
Fidelity: exact (finite frame) -/
def hedgedChainFrame (δ : ℚ) (P : W → W → ℝ) (O : ℕ → W → ℝ) : ℕ → W → ℝ
  | 0 => O 0
  | k + 1 => fun w =>
    hedgedChainFrame δ P O k w + (O (k + 1) w - hedgedChainFrame δ P O k w) *
      ctsInd δ (est P (fun v => O (k + 1) v - hedgedChainFrame δ P O k v) w) 0

/-- The rung bet of the hedged chain (it depends on `δ` through the incumbent).
Source: [[keep-or-switch-telescope]] §Construction ("note `D_k` now depends on `δ`")
Kind: D
Fidelity: exact -/
def hedgedRungBet (δ : ℚ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) : W → ℝ :=
  fun v => O (k + 1) v - hedgedChainFrame δ P O k v

/-- The hedged chain's step, in terms of the rung bet.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hedgedChainFrame_succ (δ : ℚ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) (w : W) :
    hedgedChainFrame δ P O (k + 1) w =
      hedgedChainFrame δ P O k w +
        hedgedRungBet δ P O k w * ctsInd δ (est P (hedgedRungBet δ P O k) w) 0 := rfl

/-- **The rung identity, soft**: the value gap between consecutive hedged stages is the soft
threshold-0 cut on the rung bet.
Source: [[keep-or-switch-telescope]] §Proof ("The soft telescope is verbatim with `Ind_δ`")
Kind: L
Fidelity: exact (finite frame)
Hyps: (a) none -/
theorem hedgedChainFrame_rung (δ : ℚ) (π : W → ℝ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) :
    (∑ w, π w * hedgedChainFrame δ P O (k + 1) w) - (∑ w, π w * hedgedChainFrame δ P O k w) =
      softCut π (est P (hedgedRungBet δ P O k)) (hedgedRungBet δ P O k) δ := by
  unfold softCut
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hedgedChainFrame_succ]
  ring

/-- **The telescope, soft**: the value gap of hedged stage `K` against the comparison option is the
sum of the `K` soft rung cuts.
Source: [[keep-or-switch-telescope]] §Proof
Kind: L
Fidelity: exact (finite frame)
Hyps: (a) none -/
theorem hedgedChainFrame_telescope (δ : ℚ) (π : W → ℝ) (P : W → W → ℝ) (O : ℕ → W → ℝ) :
    ∀ K, (∑ w, π w * hedgedChainFrame δ P O K w) - (∑ w, π w * O 0 w) =
      ∑ k ∈ Finset.range K, softCut π (est P (hedgedRungBet δ P O k)) (hedgedRungBet δ P O k) δ := by
  intro K
  induction K with
  | zero => simp [hedgedChainFrame]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hr := hedgedChainFrame_rung δ π P O K
    linarith

/-- **Finite-exact telescoping δ-hedged Value**: `K` nonnegative soft threshold-0 cuts (the finite
form of `TT(D_k, 0)` at width `δ`, one per rung) give Value of the hedged chain against the
comparison option.
Source: [[keep-or-switch-telescope]] §Statement (the soft form), §Proof; lean-deference-063;
vq-wiki-024
Kind: P
Fidelity: exact (finite frame; uniformly bounded `K`)
Hyps: (a) `hcut` -/
theorem hedgedChainFrame_value (δ : ℚ) (π : W → ℝ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (K : ℕ)
    (hcut : ∀ k ∈ Finset.range K,
      0 ≤ softCut π (est P (hedgedRungBet δ P O k)) (hedgedRungBet δ P O k) δ) :
    (∑ w, π w * O 0 w) ≤ ∑ w, π w * hedgedChainFrame δ P O K w := by
  rw [← sub_nonneg, hedgedChainFrame_telescope]
  exact Finset.sum_nonneg hcut

/-- The frame estimate of a hard rung bet is the newcomer's estimate minus the incumbent's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem est_hardRungBet (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) (w : W) :
    est P (hardRungBet P O k) w = est P (O (k + 1)) w - est P (hardChainFrame P O k) w :=
  est_sub P (O (k + 1)) (hardChainFrame P O k) w

/-- The frame estimate of a hedged rung bet is the newcomer's estimate minus the incumbent's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem est_hedgedRungBet (δ : ℚ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (k : ℕ) (w : W) :
    est P (hedgedRungBet δ P O k) w =
      est P (O (k + 1)) w - est P (hedgedChainFrame δ P O k) w :=
  est_sub P (O (k + 1)) (hedgedChainFrame δ P O k) w

/-- **Claim A on the frame, hard chain**: under the frame fold at every rung's indicator (the
indicator is constant on the support of `P w ·`), the expert's frame estimate of stage `k` is the
quote-level hard chain of the frame estimates `m_j := est(O^j)` at `w` — hence, by
`hardChain_eq_runMax`, the running max `M_k` exactly.
Source: [[keep-or-switch-telescope]] §Claim A (`Γ ⊢ E*(Ŝ^(k)) = M_k`: "introspection — exactly
the fold's `hknow`" + coherence)
Kind: L
Fidelity: exact (finite frame)
Hyps: (c) `hfold` — the frame fold at every rung, the finite form of introspection -/
theorem est_hardChainFrame (P : W → W → ℝ) (O : ℕ → W → ℝ) (w : W)
    (hfold : ∀ k, est P (fun v => hardRungBet P O k v *
        (if 0 < est P (hardRungBet P O k) v then 1 else 0)) w =
      (if 0 < est P (hardRungBet P O k) w then 1 else 0) * est P (hardRungBet P O k) w) :
    ∀ k, est P (hardChainFrame P O k) w = hardChain (fun j => est P (O j) w) k := by
  intro k
  induction k with
  | zero => simp [hardChainFrame, hardChain]
  | succ k ih =>
    have hstep : est P (hardChainFrame P O (k + 1)) w =
        est P (hardChainFrame P O k) w +
          est P (fun v => hardRungBet P O k v *
            (if 0 < est P (hardRungBet P O k) v then 1 else 0)) w := by
      rw [← est_add]
      rfl
    rw [hstep, hfold k, est_hardRungBet, ih]
    simp only [hardChain]
    ring

/-- **Claim A on the frame, hedged chain**: under the frame fold at every rung's ramp, the expert's
frame estimate of hedged stage `k` is the quote-level hedged chain of the frame estimates at `w`
— hence, by `hedgedChain_mem`, within `[M_k − δ, M_k]`.
Source: [[keep-or-switch-telescope]] §Claim A ("Soft Claim A")
Kind: L
Fidelity: exact (finite frame)
Hyps: (c) `hfold` — the frame fold at every rung -/
theorem est_hedgedChainFrame (δ : ℚ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (w : W)
    (hfold : ∀ k, est P (fun v => hedgedRungBet δ P O k v *
        ctsInd δ (est P (hedgedRungBet δ P O k) v) 0) w =
      ctsInd δ (est P (hedgedRungBet δ P O k) w) 0 * est P (hedgedRungBet δ P O k) w) :
    ∀ k, est P (hedgedChainFrame δ P O k) w = hedgedChain δ (fun j => est P (O j) w) k := by
  intro k
  induction k with
  | zero => simp [hedgedChainFrame, hedgedChain]
  | succ k ih =>
    have hstep : est P (hedgedChainFrame δ P O (k + 1)) w =
        est P (hedgedChainFrame δ P O k) w +
          est P (fun v => hedgedRungBet δ P O k v *
            ctsInd δ (est P (hedgedRungBet δ P O k) v) 0) w := by
      rw [← est_add]
      rfl
    rw [hstep, hfold k, est_hedgedRungBet, ih]
    simp only [hedgedChain]
    ring

/-- **Soft Claim A on the frame**: under the frame fold, the expert's frame estimate of the hedged
chain's stage `k` lies within `δ` below the running max of its own frame estimates, and never
above it.
Source: [[keep-or-switch-telescope]] §Statement (`Γ ⊢ M_K − δ ≤ E*(Ŝ^(K)_δ) ≤ M_K`), finite frame
Kind: C
Fidelity: exact (finite frame; the `Γ ⊢` form is the retracted surrogate)
Hyps: (c) `hfold`; (a) `0 < δ` -/
theorem est_hedgedChainFrame_mem {δ : ℚ} (hδ : 0 < δ) (P : W → W → ℝ) (O : ℕ → W → ℝ) (w : W)
    (hfold : ∀ k, est P (fun v => hedgedRungBet δ P O k v *
        ctsInd δ (est P (hedgedRungBet δ P O k) v) 0) w =
      ctsInd δ (est P (hedgedRungBet δ P O k) w) 0 * est P (hedgedRungBet δ P O k) w)
    (k : ℕ) :
    runMax (fun j => est P (O j) w) k - δ ≤ est P (hedgedChainFrame δ P O k) w ∧
      est P (hedgedChainFrame δ P O k) w ≤ runMax (fun j => est P (O j) w) k := by
  rw [est_hedgedChainFrame δ P O w hfold k]
  exact hedgedChain_mem hδ _ k

end Frame

end

end Cleanroom.Deference.DefArgmaxValue.Finite
