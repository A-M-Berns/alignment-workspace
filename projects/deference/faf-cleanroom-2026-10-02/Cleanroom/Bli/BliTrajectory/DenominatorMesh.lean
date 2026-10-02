import Cleanroom.Bli.BliTrajectory.Update

/-!
# `bli-trajectory` · DenominatorMesh: the denominator grid as an instance (repair round 1)

Several rows of the package hold "on the denominator grid": `bli_E1r_of_grid`, `bli_TB_on_tierA`,
`bli_update_tierA_exact`/`_ratio`, `b0_balance`, `b0_isBLI_scoped`, `b0_simplified_bli`,
`bli_bayesRatio_small_of_grid` each carry a hypothesis that the actual tables (or the base's
small prices) are grid tables. Audit r1 (fidelity N6) asked for the mesh that makes this an
instance rather than a hypothesis. **`denominatorMesh Q`** is it: `d n` is the product, over the
days `k ≤ n` and the day-`k` small sentences `φ`, of the denominators of `Q k φ` — nested by
construction (`d n ∣ d (n+1)`), positive, and every day-`n` small price of a base in `[0, 1]` is a
grid value of `d n` (`actualTable_mem_grid_denominatorMesh`). The grid rows instantiate at this
mesh with no grid hypothesis (`bli_E1r_denominator`, `bli_TB_on_tierA_denominator`,
`b0_isBLI_scoped_denominator`, `b0_simplified_bli_denominator`), and the actual state *is* the
actual table there (`actualState_eq_actualTable_denominator`).

Not claimed: `2 ≤ d (n+1)` (an all-integer base gives `d ≡ 1`), which only M9's refutation needs.
The mesh is noncomputable (products over `smallSet k`); a coding for it exists
(`exists_stateCoding`), as for any mesh.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

noncomputable section

/-- A rational in `[0, 1]` whose denominator divides `d > 0` is a grid value of `d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_gridVals_of_den_dvd {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {d : ℕ} (hd : 0 < d)
    (hdvd : q.den ∣ d) : q ∈ gridVals d := by
  obtain ⟨c, hc⟩ := hdvd
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q.num : ℚ) / q.den = q := Rat.num_div_den q
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  have hnumle : (q.num : ℚ) ≤ q.den := by
    rw [← hq, div_le_one hden] at h1; exact h1
  have hnumle' : q.num ≤ (q.den : ℤ) := by exact_mod_cast hnumle
  have hnumle'' : q.num.toNat ≤ q.den := by omega
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; omega
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have htn : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have := Int.toNat_of_nonneg hnum0
    exact_mod_cast this
  refine mem_gridVals_iff.mpr ⟨q.num.toNat * c, ?_, ?_⟩
  · rw [hc]; exact Nat.mul_le_mul_right c hnumle''
  · rw [hc, Nat.cast_mul, Nat.cast_mul, htn, mul_div_mul_right _ _ hcq]
    exact hq.symm

/-- **The denominator mesh of a rational base**: `d n` is the product of the denominators of
every price `Q k φ` with `k ≤ n` and `φ ∈ smallSet k`. Nested by construction.
Source: [[bli-program]] §2.2 (the "denominator grid" remark); mandate M5/M6; audit r1 fidelity N6
Kind: D
Fidelity: exact -/
def denominatorMesh (Q : RatHistory) : Mesh where
  d n := ∏ k ∈ Finset.range (n + 1), ∏ φ ∈ smallSet k, (Q k φ).den
  d_pos n := Finset.prod_pos fun k _ => Finset.prod_pos fun φ _ => (Q k φ).den_pos
  d_dvd n := Dvd.intro _ (Finset.prod_range_succ (fun k => ∏ φ ∈ smallSet k, (Q k φ).den) (n + 1)).symm

/-- The denominator of a day-`n` small price divides the day-`n` denominator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma den_dvd_denominatorMesh (Q : RatHistory) {n : ℕ} {φ : Sentence} (hφ : φ ∈ smallSet n) :
    (Q n φ).den ∣ (denominatorMesh Q).d n := by
  show (Q n φ).den ∣ ∏ k ∈ Finset.range (n + 1), ∏ ψ ∈ smallSet k, (Q k ψ).den
  exact (Finset.dvd_prod_of_mem (fun ψ => (Q n ψ).den) hφ).trans
    (Finset.dvd_prod_of_mem (fun k => ∏ ψ ∈ smallSet k, (Q k ψ).den)
      (Finset.mem_range.mpr (Nat.lt_succ_self n)))

/-- **Every actual table of a base in `[0, 1]` is a grid table of its denominator mesh** — the
denominator-grid hypothesis of the grid rows, discharged.
Source: [[bli-program]] §2.2; audit r1 fidelity N6
Kind: P
Fidelity: exact
Hyps: (a) `hQ` (prices in `[0, 1]`) -/
theorem actualTable_mem_grid_denominatorMesh (Q : RatHistory)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) :
    actualTable smallIndex Q n ∈ grid smallIndex (denominatorMesh Q).d n := by
  rw [mem_grid_iff]; intro φ
  exact mem_gridVals_of_den_dvd (hQ n φ.1).1 (hQ n φ.1).2 ((denominatorMesh Q).d_pos n)
    (den_dvd_denominatorMesh Q φ.2)

/-- Every day-`n` small price is a grid value of the *next* day's denominator (B0's hypothesis).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma small_mem_gridVals_denominatorMesh_succ (Q : RatHistory)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    Q n φ ∈ gridVals ((denominatorMesh Q).d (n + 1)) :=
  mem_gridVals_of_den_dvd (hQ n φ).1 (hQ n φ).2 ((denominatorMesh Q).d_pos _)
    ((den_dvd_denominatorMesh Q hφ).trans ((denominatorMesh Q).d_dvd n))

/-- On the denominator mesh the actual state **is** the actual table (no rounding happens).
Source: [[bli-program]] §2.2
Kind: C
Fidelity: exact
Hyps: (a) `hQ` -/
theorem actualState_eq_actualTable_denominator (Q : RatHistory)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) :
    actualState smallIndex (denominatorMesh Q).d Q n = actualTable smallIndex Q n :=
  actualState_eq_of_mem_grid ((denominatorMesh Q).d_pos n) (actualTable_mem_grid_denominatorMesh Q hQ n)

variable {Q : RatHistory} (c : StateCoding (denominatorMesh Q))
  (sk : Skeleton smallIndex (denominatorMesh Q).d)

/-- **`E1r` on the denominator mesh, unconditionally** (`bli_E1r_of_grid` with its grid hypothesis
discharged): Appendix B's rounded constraint 1 holds for `𝐏` at the denominator mesh.
Source: Appendix B (1) rounded; Known issue 4; audit r1 fidelity N6
Kind: C
Fidelity: exact (at the denominator mesh)
Hyps: (a) `hQ` -/
theorem bli_E1r_denominator (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    E1r (bliStateSystem Q (denominatorMesh Q) c) (bliHistory Q (denominatorMesh Q) sk c) :=
  bli_E1r_of_grid c sk Q (actualTable_mem_grid_denominatorMesh Q hQ)

/-- **`TB_on` Tier A on the denominator mesh, unconditionally** (`bli_TB_on_tierA` with its grid
hypothesis discharged): the total update on the state algebra is exact there.
Source: bli-slides-048; mandate M6; audit r1 fidelity N6
Kind: C
Fidelity: exact (Tier A, at the denominator mesh)
Hyps: (a) `hQ` -/
theorem bli_TB_on_tierA_denominator (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    TB_on (TierAUpdatable c) (bliStateSystem Q (denominatorMesh Q) c)
      (bliHistory Q (denominatorMesh Q) sk c) :=
  bli_TB_on_tierA c sk Q (fun n => actualTable_mem_grid_denominatorMesh Q hQ (n + 1))

/-- **B0 passes the scoped constraints on the denominator mesh, unconditionally**
(`b0_isBLI_scoped` with its grid hypothesis discharged).
Source: Appendix B (`main.tex:447`); mandate M2; audit r1 fidelity N6
Kind: C
Fidelity: weaker: scoped (F-1); exact at the denominator mesh
Hyps: (a) `hQ` -/
theorem b0_isBLI_scoped_denominator (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    IsBLI_RomanScoped c (bliStateSystem Q (denominatorMesh Q) c) (ratHistory Q)
      (b0History Q (denominatorMesh Q) c) :=
  b0_isBLI_scoped c Q (fun n _ hφ => small_mem_gridVals_denominatorMesh_succ Q hQ n hφ)

/-- **"Simplified BLI" is satisfied by B0 on the denominator mesh, unconditionally**
(`b0_simplified_bli` with its grid hypothesis discharged; M7 (iv)).
Source: bli-slides-015 (c); mandate M7 (iv); audit r1 fidelity N6
Kind: C
Fidelity: weaker: scoped (F-14); exact at the denominator mesh
Hyps: (a) `hQ` -/
theorem b0_simplified_bli_denominator (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    E1x (ratHistory Q) (b0History Q (denominatorMesh Q) c) ∧
      FaithMarginalScoped c (bliStateSystem Q (denominatorMesh Q) c)
        (b0History Q (denominatorMesh Q) c) ∧
      E3Scoped c (bliStateSystem Q (denominatorMesh Q) c) (b0History Q (denominatorMesh Q) c) ∧
      E4 (bliStateSystem Q (denominatorMesh Q) c) (b0History Q (denominatorMesh Q) c) ∧
      E5 (bliStateSystem Q (denominatorMesh Q) c) (b0History Q (denominatorMesh Q) c) :=
  b0_simplified_bli c Q (fun n _ hφ => small_mem_gridVals_denominatorMesh_succ Q hQ n hφ)

end

end Cleanroom.Bli.BliTrajectory
