import Cleanroom.Fa.FaTheoremA.Analysis
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.ExpectationConvergence

/-!
# fa-theorem-a · audit r2 (adversarial) probe: the provability-induction bypass

Claim under test: Lemma P at `E ≡ 1` (`lemmaP_const`), Theorem A (`theoremA`), Claim 2
(`claim2`) and the limit-range squeeze (`liminf_realized_le_liminf_quote`,
`limsup_quote_le_limsup_realized`) follow from FAF's **expectation provability induction**
(`thm:expprovind`, LI 4.8.10 — here `PolySequence.affine_provind_theory_{ge,le}_const` on the
quote family's diagonal mesh, with the public mesh bounds) and the quote package alone — with
**no gate, no `PGenerableWeighting`, no `DivergentWeighting`, no
`recurringunbiasednessexp`** (this file does not import `Cleanroom.Fa.FaTheoremA.Half1` or
`LogicalInduction.Construction.Statistics.HistoricalMaturity`).

The statements below are verbatim those of the package's declarations; only the proofs differ.
-/

namespace Cleanroom.Fa.FaTheoremA.AuditR2

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Fa.FaTheoremA
open Filter Topology

/-- The diagonal threshold mesh of the quote family (`ofLUV (Y n)` at precision `n + 1`). -/
noncomputable abbrev qmesh (Y : ℕ → LUV) (n : ℕ) : AffineCombination :=
  (LUVCombination.ofLUV (Y n)).meshAffine (n + 1)

/-- Cross-time price bound of the mesh in an inductor's market: `|price| ≤ l1Norm ≤ 1`. -/
lemma qmesh_bounded {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (Y : ℕ → LUV) : BoundedAffinePrices (qmesh Y) A := by
  refine ⟨1, zero_le_one, fun n m => ?_⟩
  have hP : ∀ φ, 0 ≤ A m φ ∧ A m φ ≤ 1 :=
    fun φ => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) m φ
  calc |(qmesh Y n).price A m| ≤ (qmesh Y n).l1Norm A :=
        (qmesh Y n).abs_price_le_l1Norm A m hP
    _ ≤ (LUVCombination.ofLUV (Y n)).l1Norm A :=
        (LUVCombination.ofLUV (Y n)).meshAffine_l1Norm_le A (n + 1)
    _ = 1 := (l1Norm_ofLUV (Y n) A).2

/-- Uniform magnitude bound of the mesh: `magnitude ≤ shareNorm = 1`. -/
lemma qmesh_mag (A : History) (Y : ℕ → LUV) : ∃ C : ℝ, ∀ n, (qmesh Y n).magnitude A ≤ C :=
  ⟨1, fun n => ((LUVCombination.ofLUV (Y n)).meshAffine_magnitude_le_shareNorm A (n + 1)).trans
    (l1Norm_ofLUV (Y n) A).1.le⟩

/-- `1/(n+1) ≤ ε/2` eventually. -/
lemma eventually_inv_succ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) ≤ ε / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  filter_upwards [eventually_ge_atTop N] with n hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have h2 : 2 < (N : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hN
  have h3 : (N : ℝ) * ε ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_right hNn hε.le
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- From `pkg.reflected` (through `li-quote-lane`'s `approxDetermined_mesh`): if the realized
values are eventually `≥ c − ε/2`, the mesh's completed-theory values are eventually `≥ c − ε`. -/
lemma qmesh_value_ge {H A : History} {DPA : DeductiveProcess} {f : DeferralFunction}
    {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y) {c : ℝ}
    (hY : ∀ ε > 0, ∀ᶠ n in atTop, c - ε ≤ realized H f X n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DPA →
      c - ε ≤ (qmesh Y n).value A v.payout := by
  intro ε hε
  have hmesh := pkg.approxDetermined_mesh A
  filter_upwards [hY (ε / 2) (by positivity), eventually_inv_succ_le hε] with n hn hsmall v hv
  have h1 := hmesh n v hv
  rw [abs_le] at h1
  show c - ε ≤ (qmesh Y n).value A v.payout
  linarith [h1.1]

/-- The dual: eventually `≤ c + ε/2` realized gives eventually `≤ c + ε` mesh values. -/
lemma qmesh_value_le {H A : History} {DPA : DeductiveProcess} {f : DeferralFunction}
    {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y) {c : ℝ}
    (hY : ∀ ε > 0, ∀ᶠ n in atTop, realized H f X n ≤ c + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DPA →
      (qmesh Y n).value A v.payout ≤ c + ε := by
  intro ε hε
  have hmesh := pkg.approxDetermined_mesh A
  filter_upwards [hY (ε / 2) (by positivity), eventually_inv_succ_le hε] with n hn hsmall v hv
  have h1 := hmesh n v hv
  rw [abs_le] at h1
  show (qmesh Y n).value A v.payout ≤ c + ε
  linarith [h1.2]

/-- **Expectation provability induction on the quote, `≥` side:** if the realized values are
eventually `≥ c − ε` for every `ε`, the quote is `≳ₙ c`. FAF's
`PolySequence.affine_provind_theory_ge_const` on the mesh; no gate. -/
theorem quote_asympGE {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {c : ℝ}
    (hY : ∀ ε > 0, ∀ᶠ n in atTop, c - ε ≤ realized H f X n) :
    ∀ ε > 0, ∀ᶠ n in atTop, c ≤ quoteSeq Y A n + ε := by
  have h := (ofLUV_mesh_polySequence Y pkg.quote_codes).affine_provind_theory_ge_const A DPA
    (qmesh_bounded (DPA := DPA) Y) (qmesh_mag A Y) hworldA c (qmesh_value_ge (A := A) pkg hY)
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simpa only [LUVCombination.meshAffine_price_diagonal, ofLUV_expect] using hn

/-- **Expectation provability induction on the quote, `≤` side.** -/
theorem quote_asympLE {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {c : ℝ}
    (hY : ∀ ε > 0, ∀ᶠ n in atTop, realized H f X n ≤ c + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, quoteSeq Y A n ≤ c + ε := by
  have h := (ofLUV_mesh_polySequence Y pkg.quote_codes).affine_provind_theory_le_const A DPA
    (qmesh_bounded (DPA := DPA) Y) (qmesh_mag A Y) hworldA c (qmesh_value_le (A := A) pkg hY)
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simpa only [LUVCombination.meshAffine_price_diagonal, ofLUV_expect] using hn

/-- **`lemmaP_const`'s statement, from provability induction alone.** -/
theorem lemmaP_const_provind {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {c : ℝ}
    (hY : Tendsto (realized H f X) atTop (𝓝 c)) :
    Tendsto (quoteSeq Y A) atTop (𝓝 c) := by
  have hge := quote_asympGE (A := A) pkg hworldA (c := c) (fun ε hε => by
    filter_upwards [(Metric.tendsto_nhds.1 hY) ε hε] with n hn
    rw [Real.dist_eq, abs_sub_lt_iff] at hn
    linarith [hn.2])
  have hle := quote_asympLE (A := A) pkg hworldA (c := c) (fun ε hε => by
    filter_upwards [(Metric.tendsto_nhds.1 hY) ε hε] with n hn
    rw [Real.dist_eq, abs_sub_lt_iff] at hn
    linarith [hn.1])
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hge (ε / 2) (by positivity), hle (ε / 2) (by positivity)] with n h1 h2
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- **`theoremA`'s and `claim2`'s statements, from provability induction alone** (plus FAF's
`expect_converges` on `H`'s side, exactly as the package). -/
theorem theoremA_provind {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    Dominates (fun n => X.expect H n) (quoteSeq Y A) ∧
      AsympEq (quoteSeq Y A) (fun n => X.expect H n) := by
  obtain ⟨L, hL⟩ := LUV.expect_converges H DPH X hcode hworldH hval
  have hL' : Tendsto (fun n => X.expect H n) atTop (𝓝 L) := hL
  have ha := lemmaP_const_provind (A := A) pkg hworldA (tendsto_realized_of_tendsto f X hL)
  exact ⟨dominates_of_tendsto hL' ha, asympEq_of_tendsto ha hL'⟩

/-- **`liminf_realized_le_liminf_quote`'s statement, from provability induction alone.** -/
theorem liminf_squeeze_provind {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    liminf (realized H f X) atTop ≤ liminf (quoteSeq Y A) atTop := by
  have hY01 : ∀ n, realized H f X n ∈ Set.Icc (0 : ℝ) 1 := fun n => by
    obtain ⟨v, hv⟩ := DeductiveProcess.exists_consistentWithTheory _ hworldA
    have h := pkg.reflected n v hv
    exact ⟨h.1, h.2.1⟩
  have ha01 : ∀ n, quoteSeq Y A n ∈ Set.Icc (0 : ℝ) 1 := fun n =>
    LUV.expect_mem_Icc A n (Y n) (fun s => IsLogicalInductor.price_mem_Icc (DP := DPA) n s)
  have hYbdd : IsBoundedUnder (· ≥ ·) atTop (realized H f X) :=
    isBoundedUnder_of ⟨0, fun n => (hY01 n).1⟩
  have hacob : IsCoboundedUnder (· ≥ ·) atTop (quoteSeq Y A) :=
    (isBoundedUnder_of ⟨1, fun n => (ha01 n).2⟩ :
      IsBoundedUnder (· ≤ ·) atTop (quoteSeq Y A)).isCoboundedUnder_ge
  set LY := liminf (realized H f X) atTop with hLY
  have hge := quote_asympGE (A := A) pkg hworldA (c := LY) (fun ε hε =>
    (eventually_lt_of_lt_liminf (show LY - ε < liminf (realized H f X) atTop by linarith)
      hYbdd).mono (fun n hn => hn.le))
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have h1 : LY - ε / 2 ≤ liminf (quoteSeq Y A) atTop :=
    le_liminf_of_le hacob ((hge (ε / 2) (by positivity)).mono (fun n hn => by linarith))
  linarith

/-- **`limsup_quote_le_limsup_realized`'s statement, from provability induction alone.** -/
theorem limsup_squeeze_provind {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    limsup (quoteSeq Y A) atTop ≤ limsup (realized H f X) atTop := by
  have hY01 : ∀ n, realized H f X n ∈ Set.Icc (0 : ℝ) 1 := fun n => by
    obtain ⟨v, hv⟩ := DeductiveProcess.exists_consistentWithTheory _ hworldA
    have h := pkg.reflected n v hv
    exact ⟨h.1, h.2.1⟩
  have ha01 : ∀ n, quoteSeq Y A n ∈ Set.Icc (0 : ℝ) 1 := fun n =>
    LUV.expect_mem_Icc A n (Y n) (fun s => IsLogicalInductor.price_mem_Icc (DP := DPA) n s)
  have hYbdd : IsBoundedUnder (· ≤ ·) atTop (realized H f X) :=
    isBoundedUnder_of ⟨1, fun n => (hY01 n).2⟩
  have hacob : IsCoboundedUnder (· ≤ ·) atTop (quoteSeq Y A) :=
    (isBoundedUnder_of ⟨0, fun n => (ha01 n).1⟩ :
      IsBoundedUnder (· ≥ ·) atTop (quoteSeq Y A)).isCoboundedUnder_le
  set LY := limsup (realized H f X) atTop with hLY
  have hle := quote_asympLE (A := A) pkg hworldA (c := LY) (fun ε hε =>
    (eventually_lt_of_limsup_lt (show limsup (realized H f X) atTop < LY + ε by linarith)
      hYbdd).mono (fun n hn => hn.le))
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have h1 : limsup (quoteSeq Y A) atTop ≤ LY + ε / 2 :=
    limsup_le_of_le hacob ((hle (ε / 2) (by positivity)).mono (fun n hn => by linarith))
  linarith

#print axioms lemmaP_const_provind
#print axioms theoremA_provind
#print axioms liminf_squeeze_provind
#print axioms limsup_squeeze_provind

end Cleanroom.Fa.FaTheoremA.AuditR2
