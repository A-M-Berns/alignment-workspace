import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# T7 — Asymptotic Value ⟺ Total Trust from linearity; the free converses

Package `def-lattice-arrows`, file 8. lean-deference-010 over `def-lattice`'s objects:

* `hedgedValue_iff_softTotalTrustAbove_instance` — Value against the constant on the hedged
  two-option menu **is** the above-threshold product form, per `(X, s, δ)`; the corpus's
  `hLoe` hypothesis is dissolved (definitional linearity of `LUVCombination.expect`,
  def-lattice F6). This is def-lattice's `twoOptionComb_value_iff_productForm` under the
  arrow's name.
* `value_twoOption_hardAbove_iff` / `value_twoOption_hardBelow_iff` — the `_iff` forms of
  def-lattice's T6d: the per-menu Value instance on `{X, C}` is *equivalent* to the hard
  inequality at the expert's quote `q_n = E*(C_n)` (def-lattice F3), from the same two
  `thm:expprovind` facts (`expect_followed_asympEq`, `expect_const_asympEq`); the converse
  was unshipped in def-lattice (its audit r2 N2 / fidelity 1, probe `Converse.lean`).

The `ccee`→TT bridge of lean-deference-010 (1) is T4's last step (`TowerToTrust.lean`,
`thresholdAbove_instance_of_tower`). The general-menu `Value ⟺ TotalTrust` is
`def-argmax-value`'s and is false unconditionally; no name here suggests it.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- **Hedged Value ⟺ soft Total Trust above, per instance** (lean-deference-010):
`E^H_n(twoOptionComb s XW W n) ≳ₙ s ↔ E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0`. The corpus's `hLoe`
is dissolved: `LUVCombination.expect` is linear in the prices by definition.
Source: lean-deference-010 (`value_iff_totalTrust_asymptotic`); def-lattice T6c
(`twoOptionComb_value_iff_productForm`), F6
Kind: L
Fidelity: exact (both arrows; no `hLoe`)
Hyps: (a) none -/
theorem hedgedValue_iff_softTotalTrustAbove_instance (P : History) (s : ℚ) (XW W : ℕ → LUV) :
    (fun n => (twoOptionComb s XW W n).expect P n) ≳ₙ (fun _ => (s : ℝ)) ↔
      (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) :=
  twoOptionComb_value_iff_productForm P s XW W

/-- **Per-menu Value on `{X, C}` ⟺ the hard above face at the expert's quote** (the `_iff`
form of def-lattice's T6d): `E^H_n(S_n) ≳ₙ E^H_n(C_n) ↔ E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0`,
with `W`, `XW` the hard weight/product at `q_n = E*(C_n)`. `→` is def-lattice's
`value_twoOption_hardAbove`; `←` from the same linearity identity and `E^H_n(C_n) ≈ₙ s`.
Source: [[two-option-value-iff-total-trust]] §Statement ("holds **iff** the boxed right side
is `≥ 0`"); lean-deference-010; def-lattice audit r2 N2 (probe `Converse.lean`)
Kind: C
Fidelity: variant: threshold at the expert's quote of the constant (def-lattice F3)
Hyps: (a) — the data `d` and `hworld` -/
theorem value_twoOption_hardAbove_iff [IsLogicalInductor P DP] {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (C n).expect P n) ↔
      (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  refine ⟨value_twoOption_hardAbove P DP hworld d, fun hTT => ?_⟩
  have hlin := d.expect_followed_asympEq P hworld
  have hconst := d.expect_const_asympEq P hworld
  have h1 : (fun _ => (s : ℝ)) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) := by
    intro ε hε
    filter_upwards [hTT ε hε] with n hn
    linarith
  exact (hconst.trans_asympLE h1).trans_asympEq hlin.symm

/-- **Per-menu Value against `X` on `{X, C}` ⟺ the hard below face at the expert's quote**:
`E^H_n(S_n) ≳ₙ E^H_n(X_n) ↔ s·(1 − E^H_n(W_n)) − (E^H_n(X_n) − E^H_n(XW_n)) ≳ₙ 0`.
Source: [[two-option-value-iff-total-trust]] §Statement; def-lattice audit r2 N2
Kind: C
Fidelity: variant: threshold at the expert's quote (F3)
Hyps: (a) -/
theorem value_twoOption_hardBelow_iff [IsLogicalInductor P DP] {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (X n).expect P n) ↔
      (fun n => (s : ℝ) * (1 - (W n).expect P n) - ((X n).expect P n - (XW n).expect P n)) ≳ₙ
        (fun _ => (0 : ℝ)) := by
  refine ⟨value_twoOption_hardBelow P DP hworld d, fun hTT => ?_⟩
  have hlin := d.expect_followed_asympEq P hworld
  have h1 : (fun n => (X n).expect P n) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) := by
    intro ε hε
    filter_upwards [hTT ε hε] with n hn
    linarith
  exact h1.trans_asympEq hlin.symm

end

end Cleanroom.Deference.DefLatticeArrows
