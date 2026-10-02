import Cleanroom.Fa.FaForcingTrader.Defs
import Cleanroom.Found.DefLattice.TwoOptionLUV
import Cleanroom.Found.LiAsympCalc.Luv
import Cleanroom.Found.LiAsympCalc.WeightedAverage

/-!
# `fa-forcing-trader` · angle A · Mesh: the closing-grid mesh term vanishes (T5)

The `H`-side trader (T4) sells the day-`n` threshold mesh `(X n).expectAffine (n+1)` at day
`f n`, at the price `price^H_{f n}(bundle_n)` — the day-`f n` market valuation of the *opening*
grid — while `A`'s quote names `𝔼^H_{f n}(X_n)`, the day-`f n` expectation on day `f n`'s own
grid. The gap is FAF's `meshTailError` and tends to `0` by FAF's mesh-independence lemma
(`lem:mesh`, `BoundedSequence.mesh_independence`), whose operational witness is discharged by
`meshSoftmaxOperationalWitness` from def-lattice's compact syntax for the single-LUV combination.
Because the gap is **per-day and vanishes**, it is washed out of every divergent weighted average
by the donor rule (`weightedAverage_tendsto_zero`) — unlike the (R2) approximant mismatch of T9,
which is per-day but only `o(1)`, not `o(W_n)`.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- The single-LUV combination's day-`m` valuation on the grid `n + 1` is the bundle's day-`m`
price.
Source: none: infrastructure (FAF `LUV.expectAffine_value`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ofLUV_expectAt_eq_bundle_price (X : ℕ → LUV) (H : History) (n m : ℕ) :
    (LUVCombination.ofLUV (X n)).expectAt H (n + 1) m = (bundle X n).price H m := by
  simp [LUVCombination.expectAt, LUVCombination.ofLUV, AffineCombination.price,
    LUV.expectAffineSeq, LUV.expectAffine_value]

/-- The single-LUV combination's valuation on day `m`'s own grid is the day-`m` expectation.
Source: none: infrastructure (FAF `LUV.expect`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ofLUV_expectAt_diag (X : ℕ → LUV) (H : History) (n m : ℕ) :
    (LUVCombination.ofLUV (X n)).expectAt H (m + 1) m = (X n).expect H m := by
  simp [LUVCombination.expectAt, LUVCombination.ofLUV, LUV.expect]

/-- **T5 (headline). The closing-grid mesh term vanishes**: the day-`f n` price of the day-`n`
threshold mesh of `X_n` and the day-`f n` expectation `𝔼^H_{f n}(X_n)` become indistinguishable.
FAF's `lem:mesh` (`BoundedSequence.mesh_independence`) for the constant-coefficient family
`0 + 1·X_n`, with the operational witness from def-lattice's `singleCombSyntax`, `WorldValued`
from `hval` (FAF's disclosed linkage of `thm:ec`, as `fa-theorem-a`'s `theoremA` takes it), and the
rational share bound `1`.
Scope: one-way (`H` alone). e.d. family `X`. Any deferral `f`. Grade: full limit.
Source: [[route-recurring-ccee]] §5.4 ("Mesh Independence Lemma (appendix E.2)"); lean-deference-036 (`hmesh`); FAF `lem:mesh`
Kind: C
Fidelity: exact
Hyps: (a) `hcode`, `hworldH`, `hval` (FAF's own premises of `lem:mesh`); no (b), no (c). -/
theorem bundle_price_sub_realized_tendsto {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (f : DeferralFunction) :
    Tendsto (fun n => (bundle X n).price H (f.f n) - (X n).expect H (f.f n)) atTop (𝓝 0) := by
  have hP : ∀ n φ, 0 ≤ H n φ ∧ H n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := H) (DP := DPH) n φ
  have hbs : LUVCombination.BoundedSequence (fun n => LUVCombination.ofLUV (X n)) H :=
    singleComb_boundedSequence H hcode
  have ops : LUVCombination.MeshSoftmaxOperationalWitness
      (fun n => LUVCombination.ofLUV (X n)) H :=
    LUVCombinationSyntax.meshSoftmaxOperationalWitness (singleCombSyntax hcode) hbs hP
  have hvalued : LUVCombination.WorldValued (fun n => LUVCombination.ofLUV (X n)) DPH :=
    worldValued_ofLUV hval
  have hshare : ∀ n, (LUVCombination.ofLUV (X n)).shareNorm H ≤ ((1 : ℚ) : ℝ) := fun n => by
    simp [LUVCombination.shareNorm, LUVCombination.ofLUV]
  have hmesh := hbs.mesh_independence ops hvalued 1 (by norm_num) hshare hworldH
  refine squeeze_zero_norm' (Eventually.of_forall (fun n => ?_)) hmesh
  rw [Real.norm_eq_abs]
  have hbdd := hbs.meshTailError_bddAbove hP n
  refine le_csSup hbdd ⟨f.f n - n, ?_⟩
  have hfn : n + (f.f n - n) = f.f n := by
    have := f.lt n
    omega
  simp only [hfn]
  rw [ofLUV_expectAt_eq_bundle_price, ofLUV_expectAt_diag]

/-- **T5, donor corollary**: under any nonnegative weighting with divergent mass, the weighted
average of the closing-grid mesh term tends to `0` — the bundle's sale price and the realized
expectation `Y_n = 𝔼^H_{f n}(X_n)` agree in `WeightedApprox`.
Source: [[theorem-ss-streamlined]] §1 (the donor rule); lean-deference-036 (`hmesh` washed out)
Kind: C
Fidelity: exact
Hyps: (a) as `bundle_price_sub_realized_tendsto`, plus `hw`, `hdiv`; no (b), no (c). -/
theorem weightedApprox_bundle_realized {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] {X : ℕ → LUV} (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (f : DeferralFunction) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) :
    WeightedApprox w (fun n => (bundle X n).price H (f.f n)) (realized H f X) :=
  weightedAverage_tendsto_zero hw hdiv (bundle_price_sub_realized_tendsto hcode hworldH hval f)

end Cleanroom.Fa.FaForcingTrader.A
