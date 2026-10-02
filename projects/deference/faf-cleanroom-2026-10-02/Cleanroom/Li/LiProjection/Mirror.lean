import Cleanroom.Li.LiProjection.Defs

/-!
# `li-projection` · Mirror: the value identities (T1.4)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 3 of the layout. The
denotational transport `(EF.projectOn u q e).denote P = e.denote (project P u q)` and the two
mirror identities in the **kernel-pinned signs** of the dose-response zip's AUDIT §2.6, with the
day-`m` exposure `D_m := Σ e(𝕡)·(P̄_m(α_φ) − P̄_m(β_φ))`:

* `V_{W,n}(T^⊤) = V_{(W,1),n}(T) − Σ_{m ≤ n} (1 − q_m) D_m`,
* `V_{W,n}(T^⊥) = V_{(W,0),n}(T) + Σ_{m ≤ n} q_m D_m`,

and for `S := λ T^⊤ + (1 − λ) T^⊥`:
`V_{W,n}(S) = λ V_{(W,1),n}(T) + (1 − λ) V_{(W,0),n}(T) + Σ_{m ≤ n} (q_m − λ) D_m`.
Here `V_{(W,b),n}(T)` is `T.netWorth (project P u q) (setAtom W u b) n`, FAF's net worth of `T`
against the projected market as assessed by the world with the `u`-bit forced. Also the bound on
the correction term when `q` is constant from day `N` on.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Denotational transport -/

/-- The projected feature, evaluated at the base market in any environment, is the original
feature evaluated at the projected market.
Source: [[dose-response]] §6.1 Lemma A ("extended prices are affine in base prices")
Kind: P
Fidelity: exact -/
lemma EF.projectOn_denoteWith (u : ℕ) (q : ℕ → ℚ) (P : History) (e : EF) :
    ∀ ρ : List ℝ, (EF.projectOn u q e).denoteWith ρ P = e.denoteWith ρ (project P u q) := by
  induction e with
  | price φ m => intro ρ; simp [EF.projectOn, project]
  | const c => intro ρ; simp [EF.projectOn]
  | add a b iha ihb => intro ρ; simp [EF.projectOn, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [EF.projectOn, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [EF.projectOn, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [EF.projectOn, iha ρ]
  | var i => intro ρ; simp [EF.projectOn]
  | letE x body ihx ihb =>
      intro ρ
      simp only [EF.projectOn, EF.denoteWith_letE, ihx ρ]
      exact ihb _

/-- `(EF.projectOn u q e).denote P = e.denote (project P u q)`.
Source: [[dose-response]] §6.1 Lemma A
Kind: P
Fidelity: exact -/
lemma EF.projectOn_denote (u : ℕ) (q : ℕ → ℚ) (P : History) (e : EF) :
    (EF.projectOn u q e).denote P = e.denote (project P u q) :=
  EF.projectOn_denoteWith u q P e []

/-! ## Exposure at strategy level -/

/-- The exposure of a day-`n` strategy to the atom at the projected market:
`Σ_{(e,φ)} e(𝕡) · (P n (φ⟦u:=⊤⟧) − P n (φ⟦u:=⊥⟧))`.
Source: [[dose-response]] §6.1 Lemma A (`D_n`)
Kind: D
Fidelity: exact -/
noncomputable def Strategy.exposure {n : ℕ} (T : Strategy n) (P : History) (u : ℕ) (q : ℕ → ℚ) :
    ℝ :=
  (T.trades.map fun p =>
    p.1.denote (project P u q) * (P n (p.2⟦substAtom u true⟧) - P n (p.2⟦substAtom u false⟧))).sum

/-- `exposure_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exposure_eq (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (m : ℕ) :
    exposure T P u q m = Strategy.exposure (T.strat m) P u q := rfl

/-! ## The per-day mirror identities -/

/-- **Mirror identity, `⊤` side, one day:** `T^⊤`'s day-`n` value at base prices in world `W` is
`T`'s day-`n` value at the projected market in the world `(W, 1)`, minus `(1 − q_n) D_n`.
Source: [[dose-response]] §6.1 Lemma A (zip AUDIT §2.6, the kernel-pinned signs)
Kind: P
Fidelity: exact -/
lemma Strategy.mirror_value_true {n : ℕ} (T : Strategy n) (P : History) (u : ℕ) (q : ℕ → ℚ)
    (W : PCWorld) :
    (Strategy.mirror u q true T).value P W.payout =
      T.value (project P u q) (setAtom W u true).payout -
        (1 - (q n : ℝ)) * Strategy.exposure T P u q := by
  simp only [Strategy.value, Strategy.mirror, Strategy.exposure, List.map_map]
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
      rw [ih, EF.projectOn_denote, payout_setAtom, project_apply]
      ring

/-- **Mirror identity, `⊥` side, one day:** `T^⊥`'s day-`n` value at base prices in world `W` is
`T`'s day-`n` value at the projected market in the world `(W, 0)`, plus `q_n D_n`.
Source: [[dose-response]] §6.1 Lemma A (zip AUDIT §2.6)
Kind: P
Fidelity: exact -/
lemma Strategy.mirror_value_false {n : ℕ} (T : Strategy n) (P : History) (u : ℕ) (q : ℕ → ℚ)
    (W : PCWorld) :
    (Strategy.mirror u q false T).value P W.payout =
      T.value (project P u q) (setAtom W u false).payout + (q n : ℝ) * Strategy.exposure T P u q := by
  simp only [Strategy.value, Strategy.mirror, Strategy.exposure, List.map_map]
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
      rw [ih, EF.projectOn_denote, payout_setAtom, project_apply]
      ring

/-! ## Net-worth identities -/

/-- **Mirror identity, `⊤` side:**
`(T^⊤).netWorth P W n = T.netWorth 𝕡 (W,1) n − Σ_{m ≤ n} (1 − q_m) D_m`.
Source: [[dose-response]] §6.1 Lemma A, first display (zip AUDIT §2.6 signs)
Kind: P
Fidelity: exact -/
theorem Trader.mirror_netWorth_true (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (W : PCWorld)
    (n : ℕ) :
    (Trader.mirror u q true T).netWorth P W n =
      T.netWorth (project P u q) (setAtom W u true) n -
        ∑ m ∈ Finset.range (n + 1), (1 - (q m : ℝ)) * exposure T P u q m := by
  unfold Trader.netWorth
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => Strategy.mirror_value_true (T.strat m) P u q W

/-- **Mirror identity, `⊥` side:**
`(T^⊥).netWorth P W n = T.netWorth 𝕡 (W,0) n + Σ_{m ≤ n} q_m D_m`.
Source: [[dose-response]] §6.1 Lemma A, first display (zip AUDIT §2.6 signs)
Kind: P
Fidelity: exact -/
theorem Trader.mirror_netWorth_false (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (W : PCWorld)
    (n : ℕ) :
    (Trader.mirror u q false T).netWorth P W n =
      T.netWorth (project P u q) (setAtom W u false) n +
        ∑ m ∈ Finset.range (n + 1), (q m : ℝ) * exposure T P u q m := by
  unfold Trader.netWorth
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => Strategy.mirror_value_false (T.strat m) P u q W

/-- The affine combination's day-`n` value is the affine combination of the values.
Source: [[dose-response]] §6.1 Lemma A ([LI 3.4.4])
Kind: L
Fidelity: exact -/
lemma Trader.affineCombo_value (lam : ℚ) (T₁ T₂ : Trader) (n : ℕ) (V : History) (w : Valuation) :
    ((Trader.affineCombo lam T₁ T₂).strat n).value V w =
      (lam : ℝ) * (T₁.strat n).value V w + (1 - (lam : ℝ)) * (T₂.strat n).value V w := by
  simp only [Trader.affineCombo, Strategy.join_value, Strategy.scaleBy_value, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- The affine combination's net worth is the affine combination of the net worths.
Source: [[dose-response]] §6.1 Lemma A
Kind: L
Fidelity: exact -/
lemma Trader.affineCombo_netWorth (lam : ℚ) (T₁ T₂ : Trader) (V : History) (v : PCWorld)
    (n : ℕ) :
    (Trader.affineCombo lam T₁ T₂).netWorth V v n =
      (lam : ℝ) * T₁.netWorth V v n + (1 - (lam : ℝ)) * T₂.netWorth V v n := by
  unfold Trader.netWorth
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => Trader.affineCombo_value lam T₁ T₂ m V v.payout

/-- **The combined identity.** For `S := λ T^⊤ + (1 − λ) T^⊥`:
`S.netWorth P W n = λ · T.netWorth 𝕡 (W,1) n + (1 − λ) · T.netWorth 𝕡 (W,0) n + Σ_{m ≤ n} (q_m − λ) D_m`.
Source: [[dose-response]] §6.1 Lemma A, second display
Kind: P
Fidelity: exact -/
theorem combo_mirror_netWorth (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (lam : ℚ)
    (W : PCWorld) (n : ℕ) :
    (Trader.affineCombo lam (Trader.mirror u q true T) (Trader.mirror u q false T)).netWorth P W n =
      (lam : ℝ) * T.netWorth (project P u q) (setAtom W u true) n +
        (1 - (lam : ℝ)) * T.netWorth (project P u q) (setAtom W u false) n +
        ∑ m ∈ Finset.range (n + 1), ((q m : ℝ) - lam) * exposure T P u q m := by
  rw [Trader.affineCombo_netWorth, Trader.mirror_netWorth_true, Trader.mirror_netWorth_false]
  have hsum : ∑ m ∈ Finset.range (n + 1), ((q m : ℝ) - lam) * exposure T P u q m =
      -((lam : ℝ) * ∑ m ∈ Finset.range (n + 1), (1 - (q m : ℝ)) * exposure T P u q m) +
        (1 - (lam : ℝ)) * ∑ m ∈ Finset.range (n + 1), (q m : ℝ) * exposure T P u q m := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsum]
  ring

/-! ## The correction term is bounded when `q` is eventually constant -/

/-- The bound `C*` on the correction: `Σ_{m < N} |q_m − λ| · |D_m|`, a fixed real (the exposure is
world-independent).
Source: [[dose-response]] §6.1 Lemma A ("uniformly bounded by some `C* < ∞`")
Kind: D
Fidelity: exact -/
noncomputable def correctionBound (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (lam : ℚ)
    (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, |(q m : ℝ) - lam| * |exposure T P u q m|

/-- `correctionBound_nonneg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma correctionBound_nonneg (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (lam : ℚ) (N : ℕ) :
    0 ≤ correctionBound T P u q lam N :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- When `q_m = λ` for every `m ≥ N`, the correction `Σ_{m ≤ n} (q_m − λ) D_m` is bounded by `C*`
on every day `n`.
Source: [[dose-response]] §6.1 Lemma A ("by (ii) the correction is a partial sum of the fixed finite reals")
Kind: P
Fidelity: exact -/
theorem abs_correction_le (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (lam : ℚ) (N : ℕ)
    (hjump : ∀ m, N ≤ m → q m = lam) (n : ℕ) :
    |∑ m ∈ Finset.range (n + 1), ((q m : ℝ) - lam) * exposure T P u q m| ≤
      correctionBound T P u q lam N := by
  have hterm : ∀ m, |((q m : ℝ) - lam) * exposure T P u q m| =
      if m < N then |(q m : ℝ) - lam| * |exposure T P u q m| else 0 := by
    intro m
    by_cases hm : m < N
    · rw [if_pos hm, abs_mul]
    · rw [if_neg hm, hjump m (not_lt.mp hm)]
      simp
  calc |∑ m ∈ Finset.range (n + 1), ((q m : ℝ) - lam) * exposure T P u q m|
      ≤ ∑ m ∈ Finset.range (n + 1), |((q m : ℝ) - lam) * exposure T P u q m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.range (n + 1), (if m < N then |(q m : ℝ) - lam| * |exposure T P u q m| else 0) :=
        Finset.sum_congr rfl fun m _ => hterm m
    _ = ∑ m ∈ (Finset.range (n + 1)).filter (fun m => m < N),
          |(q m : ℝ) - lam| * |exposure T P u q m| := by
        rw [Finset.sum_filter]
    _ ≤ ∑ m ∈ Finset.range N, |(q m : ℝ) - lam| * |exposure T P u q m| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_filter] at hm
          exact Finset.mem_range.mpr hm.2
        · intro m _ _
          exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

end Cleanroom.Li.LiProjection
