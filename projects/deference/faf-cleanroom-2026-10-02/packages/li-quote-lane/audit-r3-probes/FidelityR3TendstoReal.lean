import Cleanroom.Found.LiQuoteLane.Readability

/-!
# Audit round 3 (fidelity) probe: L4 without `hL` for a table converging to any real

Not imported by the library. The package's `readability_ofTendsto` covers a table converging to a
*rational* `L` (the constant approximant `ẑ ≡ L` is generable for free). The open list, the OPEN
docstring and findings F2 say more: "a convergent table is priced at its values with no
hypothesis" / "a convergent table always is [approximable]". For an irrational limit no constant
rational approximant exists, so `readability_ofApprox` does not apply as stated. This probe checks
that the stronger wording is nevertheless true over FAF: the ε-forms
`PolySequence.affine_provind_theory_le_const` / `_ge_const` at `c := L` give
`𝔼^P_n(α_{j,n}) → L` directly from T1.2, with no approximant at all. So "convergent" is right,
but it is proved by this route, not by `readability_ofTendsto`.
-/

namespace Cleanroom.Found.LiQuoteLane.AuditR3Fid

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- L4 for a table converging to an arbitrary real `L`, with no generability hypothesis. -/
theorem readability_ofTendsto_real (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [hP : IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ) (L : ℝ)
    (hlim : Tendsto (fun n => (a j n : ℝ)) atTop (𝓝 L)) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) := by
  set As : ℕ → AffineCombination := fun n => (ledgerLuv j n).expectAffine (n + 1) with hAs
  have hpoly : AffineCombination.PolySequence As :=
    LUV.expectAffineSeq_polySequence (fun n => ledgerLuv j n) (ledgerLuv_thresholdCodes j)
  have hprices : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := ledgerProcess base a e) n φ
  have hvalue : ∀ n (w : Valuation),
      (As n).value P w = (ledgerLuv j n).expectApprox w (n + 1) := by
    intro n w
    rw [hAs]
    dsimp only
    exact LUV.expectAffine_value _ P w _
  have hprice : ∀ n, (As n).price P n = (ledgerLuv j n).expect P n := by
    intro n
    rw [hAs]
    dsimp only
    exact LUV.expectAffine_price _ P n
  have hbounded : BoundedAffinePrices As P := by
    refine ⟨1, zero_le_one, fun n m => ?_⟩
    rw [AffineCombination.price, hvalue]
    have h1 := (ledgerLuv j n).expectApprox_nonneg (P m) (n + 1) (fun s => (hprices m s).1)
    have h2 := (ledgerLuv j n).expectApprox_le_one (P m) (n + 1) (fun s => (hprices m s).2)
    rw [abs_le]
    constructor <;> linarith
  have hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C := by
    refine ⟨1, fun n => ?_⟩
    rw [hAs]
    dsimp only
    exact LUV.expectAffine_magnitude_le_one _ P _
  -- the completed-theory value is within `1/(n+1) + |a_n − L|` of `L`
  have hnear : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory (ledgerProcess base a e) →
        |(As n).value P v.payout - L| ≤ ε := by
    intro ε hε
    have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim2 : Tendsto (fun n => |(a j n : ℝ) - L|) atTop (𝓝 0) := by
      have := (tendsto_sub_nhds_zero_iff.mpr hlim).abs
      rwa [abs_zero] at this
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hlim2.eventually (eventually_le_nhds (half_pos hε))] with n hn1 hn2 v hv
    rw [hvalue]
    have hdet := ledgerLuv_determinedVia base a e hmem j n v hv
    have hgrid : ∀ i : ℕ, i < n + 1 →
        (((i : ℝ) / ((n + 1 : ℕ) : ℝ) < (a j n : ℝ) →
            v.Holds ((ledgerLuv j n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)))) ∧
          ((a j n : ℝ) < (i : ℝ) / ((n + 1 : ℕ) : ℝ) →
            ¬ v.Holds ((ledgerLuv j n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))))) := by
      intro i _
      have hc : (((i : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have := hdet.2.2 ((i : ℚ) / ((n + 1 : ℕ) : ℚ))
      rw [hc] at this
      exact this
    have hnear := PCWorld.expectApprox_near_ofGrid hdet.1 hdet.2.1 (Nat.succ_pos n) hgrid
    calc |(ledgerLuv j n).expectApprox v.payout (n + 1) - L|
        = |((ledgerLuv j n).expectApprox v.payout (n + 1) - a j n) + ((a j n : ℝ) - L)| := by
          congr 1
          ring
      _ ≤ |(ledgerLuv j n).expectApprox v.payout (n + 1) - a j n| + |(a j n : ℝ) - L| :=
          abs_add_le _ _
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) + |(a j n : ℝ) - L| := by gcongr
      _ = 1 / ((n : ℝ) + 1) + |(a j n : ℝ) - L| := by push_cast; rfl
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  have hle := hpoly.affine_provind_theory_le_const P (ledgerProcess base a e) hbounded hmag
    hworld L (fun ε hε => by
      filter_upwards [hnear ε hε] with n hn v hv
      have := (abs_le.mp (hn v hv)).2
      linarith)
  have hge := hpoly.affine_provind_theory_ge_const P (ledgerProcess base a e) hbounded hmag
    hworld L (fun ε hε => by
      filter_upwards [hnear ε hε] with n hn v hv
      have := (abs_le.mp (hn v hv)).1
      linarith)
  have hconst : (fun n => (As n).price P n) ≈ₙ (fun _ => L) :=
    asympEq_iff_asympLE_asympGE.mpr ⟨hle, hge⟩
  have hexp : (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun _ => L) := by
    unfold AsympEq at hconst ⊢
    refine hconst.congr fun n => ?_
    simp only [hprice]
  have ha : (fun n => (a j n : ℝ)) ≈ₙ (fun _ => L) := by
    unfold AsympEq
    exact tendsto_sub_nhds_zero_iff.mpr hlim
  exact hexp.trans ha.symm

end Cleanroom.Found.LiQuoteLane.AuditR3Fid
