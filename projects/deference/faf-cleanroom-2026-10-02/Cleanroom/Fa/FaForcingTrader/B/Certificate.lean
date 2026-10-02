import Cleanroom.Fa.FaForcingTrader.B.Feedback

/-!
# `fa-forcing-trader` · angle B · Certificate: what the timing certificate must compute

Angle B's attempt at the mesh-level feedback certificate `C` ([[fa-forcing-trader-mandate]]
§ Attempt angles (B), K4). The finding that shapes this file (F-B1 in
`fa-forcing-trader-findings-B.md`):

**FAF's `luv_wubexp_ofComputation` asks for a certificate on `normalizedMeshTruth`, the value of
the quote's precision-`(n+1)` threshold mesh in `theoryWorld DP hworld` — a `Classical.choose`-
selected completed-theory world.** `PCWorld.ValuesAt` pins a world's threshold payouts strictly
below and strictly above the value and says nothing *at* a grid point `i/(n+1) = y_n`, so over
`pkg.reflected` alone the stream `normalizedMeshTruth n` is not a function of `y_n`: it depends on
the chosen world's vote at the grid point. No program can be certified to write it. (It *is*
canonical when the process decides every threshold atom with strict polarity, as
`li-quote-lane`'s ledger does — `normalizedMeshTruth_eq_gridTruth_of_strict` below.)

**The replacement.** FAF's affine engine `lic_wubaff` is generic in `truth`, and its bridge
`feedbackTruthSequence` only needs `ApproxDeterminedViaTheory` with a vanishing error. So the
certificate can be asked for the **grid rounding** `gridTruth y n := (1/2) · (1/(n+1)) · #{i ≤ n :
i/(n+1) < y_n}` — a computable function of the realized value `y_n = 𝔼^H_{f n}(X_n)` (a rational
when `H` has a `MarketComputation`) — at the price of the `1/(n+1)` mesh slack that the engine
absorbs anyway (`expectApprox_sub_gridRound_abs_le`, `gridTruth_approxDetermined`). The endpoint
`quoteSide_fullLimit_grid` re-runs `BoundedSequence.wubexp`'s scaling argument with this truth.

**What remains open** (`Open.lean`, `exists_gridCertificate_of_marketComputation`): building the
`MachineDigits`-metered code stream from `H`'s `MarketComputation` on an evaluation-sparse
schedule — [[route-sparse-schedule]] §3 Lemma 1(c)/(d)'s truncation argument in FAF's machine
model. The shape that *is* available is `FeedbackTruthComputation.ofMachineRatCodes`: a value
stream that is `MachineRatCodes` in the component index `k` certifies every schedule.

Scope: one-way. e.d. family. Grade: full limit.
-/

namespace Cleanroom.Fa.FaForcingTrader.B

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. The grid rounding and the counting lemma -/

/-- **The grid rounding** of a real at precision `k`: `(1/k) · #{i < k : i/k < x}` — what every
world valuing a LUV at `x` pays on the precision-`k` threshold mesh, up to the one grid point
`i/k = x` on which `PCWorld.ValuesAt` is silent.
Source: FAF `lem:conluvapprox` (`PCWorld.expectApprox_near_ofGrid`'s counting argument); mandate K4
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def gridRound (k : ℕ) (x : ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (if (i : ℝ) / k < x then (1 : ℝ) else 0)

/-- Termwise: a world valuing `X` at `x` pays, on the threshold `i/k`, exactly the grid indicator
except possibly at `i/k = x`, where the difference is at most `1`.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma payout_sub_gridInd_abs_le {v : PCWorld} {X : LUV} {x : ℝ} (hval : v.ValuesAt X x)
    (k : ℕ) (i : ℕ) :
    |v.payout (X.gt ((i : ℚ) / (k : ℚ))) - (if (i : ℝ) / k < x then (1 : ℝ) else 0)| ≤
      (if (i : ℝ) / k = x then (1 : ℝ) else 0) := by
  obtain ⟨-, -, hthr⟩ := hval
  have hcast : (((i : ℚ) / (k : ℚ) : ℚ) : ℝ) = (i : ℝ) / (k : ℝ) := by push_cast; ring
  rcases lt_trichotomy ((i : ℝ) / k) x with hlt | heq | hgt
  · have h1 : v.Holds (X.gt ((i : ℚ) / (k : ℚ))) := (hthr _).1 (by rw [hcast]; exact hlt)
    simp [PCWorld.payout, h1, hlt, hlt.ne]
  · simp only [heq, lt_self_iff_false, if_false, if_true, sub_zero]
    rw [PCWorld.payout]
    split_ifs <;> norm_num
  · have h0 : ¬ v.Holds (X.gt ((i : ℚ) / (k : ℚ))) := (hthr _).2 (by rw [hcast]; exact hgt)
    simp [PCWorld.payout, h0, not_lt.2 hgt.le, hgt.ne']

/-- At most one grid point `i/k` (with `i < k`) equals `x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma card_grid_eq_le_one {k : ℕ} (hk : 0 < k) (x : ℝ) :
    ((Finset.range k).filter (fun i : ℕ => (i : ℝ) / k = x)).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h : (a : ℝ) / k = (b : ℝ) / k := by rw [ha.2, hb.2]
  exact_mod_cast (div_left_inj' hkR).1 h

/-- **The counting lemma.** A world valuing `X` at `x` pays, on the precision-`k` mesh, within
`1/k` of the grid rounding of `x`: the two differ by at most one grid point's worth.
Source: FAF `lem:conluvapprox` (`PCWorld.ValuesAt.expectApprox_near`), sharpened to a named computable centre
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem expectApprox_sub_gridRound_abs_le {v : PCWorld} {X : LUV} {x : ℝ} (hval : v.ValuesAt X x)
    {k : ℕ} (hk : 0 < k) :
    |X.expectApprox v.payout k - gridRound k x| ≤ 1 / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : |∑ i ∈ Finset.range k,
      (v.payout (X.gt ((i : ℚ) / (k : ℚ))) - if (i : ℝ) / k < x then (1 : ℝ) else 0)| ≤ 1 := by
    calc |∑ i ∈ Finset.range k,
            (v.payout (X.gt ((i : ℚ) / (k : ℚ))) - if (i : ℝ) / k < x then (1 : ℝ) else 0)|
        ≤ ∑ i ∈ Finset.range k,
            |v.payout (X.gt ((i : ℚ) / (k : ℚ))) - if (i : ℝ) / k < x then (1 : ℝ) else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range k, (if (i : ℝ) / k = x then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun i _ => payout_sub_gridInd_abs_le hval k i)
      _ = (((Finset.range k).filter (fun i : ℕ => (i : ℝ) / k = x)).card : ℝ) := by
          rw [Finset.sum_boole]
      _ ≤ 1 := by exact_mod_cast card_grid_eq_le_one hk x
  unfold LUV.expectApprox gridRound
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hkR), one_div]
  calc (k : ℝ)⁻¹ * |∑ i ∈ Finset.range k,
          (v.payout (X.gt ((i : ℚ) / (k : ℚ))) - if (i : ℝ) / k < x then (1 : ℝ) else 0)|
      ≤ (k : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hsum (inv_pos.2 hkR).le
    _ = (k : ℝ)⁻¹ := mul_one _

/-! ## B. The grid truth stream and its approximate determination -/

/-- **The grid truth stream**: `(1/2) · gridRound (n+1) (y n)` — the normalized (share bound `1`,
`meshNormScale 1 = 1/2`) grid rounding of the realized value `y_n`. For `y = realized H f X` this
is a computable function of `H`'s day-`f n` prices; it replaces FAF's `normalizedMeshTruth`
(`theoryWorld`-dependent) as the certificate's target.
Source: mandate K4; FAF `thm:wubexp` (`normalizedMeshTruth`)
Kind: D
Fidelity: variant: computable grid centre in place of the chosen world's mesh value
Hyps: n/a -/
noncomputable def gridTruth (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((LUVCombination.meshNormScale 1 : ℚ) : ℝ) * gridRound (n + 1) (y n)

/-- The normalized mesh of a singleton family values, in a world, at the scale times the LUV's
precision-`(n+1)` approximate expectation in that world.
Source: none: infrastructure (FAF `meshAffine_value`, `scale_value`; `li-asymp-calc` `ofLUV_value`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma normalizedMesh_ofLUV_value (Y : ℕ → LUV) (b : ℚ) (P : History) (n : ℕ) (w : Valuation) :
    (LUVCombination.normalizedMesh (fun n => LUVCombination.ofLUV (Y n)) b n).value P w =
      ((LUVCombination.meshNormScale b : ℚ) : ℝ) * (Y n).expectApprox w (n + 1) := by
  simp only [LUVCombination.normalizedMesh, AffineCombination.scale_value, EF.denote_const,
    LUVCombination.meshAffine_value, ofLUV_value]

/-- **The grid truth approximately determines the normalized mesh** (FAF's
`ApproxDeterminedViaTheory`, the `hdet` input of `feedbackTruthSequence`): in every completed-
theory world of `DP`, the mesh's value is within `(1/2)·1/(n+1)` of `gridTruth (realized H f X) n`
— from `pkg.reflected` and the counting lemma. The error vanishes (`herr` in the endpoint).
Source: FAF `WorldValued.normalizedMesh_approxDetermined` (the pattern), re-centred at the grid truth
Kind: C
Fidelity: exact
Hyps: (c) `pkg.reflected` -/
theorem gridTruth_approxDetermined {H P : History} {DP : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DP f X Y) :
    AffineCombination.ApproxDeterminedViaTheory
      (LUVCombination.normalizedMesh (fun n => LUVCombination.ofLUV (Y n)) 1) P DP
      (gridTruth (realized H f X))
      (fun n => ((LUVCombination.meshNormScale 1 : ℚ) : ℝ) * (1 / ((n : ℝ) + 1))) := by
  intro n v hv
  rw [normalizedMesh_ofLUV_value, gridTruth, ← mul_sub, abs_mul,
    abs_of_pos (LUVCombination.meshNormScale_pos 1)]
  refine mul_le_mul_of_nonneg_left ?_ (LUVCombination.meshNormScale_pos 1).le
  have h := expectApprox_sub_gridRound_abs_le (pkg.reflected n v hv) (k := n + 1) n.succ_pos
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The grid rounding of the realized value is within `2/(n+1)` of it (through any completed-theory
world, by the counting lemma and FAF's `expectApprox_near`).
Source: FAF `lem:conluvapprox`
Kind: L
Fidelity: exact
Hyps: (c) `pkg.reflected`; (a) `hworld` -/
theorem gridRound_sub_realized_abs_le {H : History} {DP : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    |gridRound (n + 1) (realized H f X n) - realized H f X n| ≤ 2 / ((n : ℝ) + 1) := by
  obtain ⟨v, hv⟩ := DP.exists_consistentWithTheory hworld
  have hval := pkg.reflected n v hv
  have h1 := expectApprox_sub_gridRound_abs_le hval (k := n + 1) n.succ_pos
  have h2 := hval.expectApprox_near (n := n + 1) n.succ_pos
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h1 h2
  calc |gridRound (n + 1) (realized H f X n) - realized H f X n|
      = |(gridRound (n + 1) (realized H f X n) - (Y n).expectApprox v.payout (n + 1)) +
          ((Y n).expectApprox v.payout (n + 1) - realized H f X n)| := by ring_nf
    _ ≤ |gridRound (n + 1) (realized H f X n) - (Y n).expectApprox v.payout (n + 1)| +
          |(Y n).expectApprox v.payout (n + 1) - realized H f X n| := abs_add_le _ _
    _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
        refine add_le_add ?_ h2
        rw [abs_sub_comm]
        exact h1
    _ = 2 / ((n : ℝ) + 1) := by ring

/-! ## C. The endpoint: the quote-side full limit from a certificate on the grid truth -/

/-- **L3 / L2 from a certificate on the computable grid truth.** The same conclusion as
`quoteSide_fullLimit`, with the certificate asked for `gridTruth (realized H f X)` along `d`
instead of FAF's `normalizedMeshTruth`. Proof: FAF's affine engine `lic_wubaff` on the normalized
mesh with the bridge `feedbackTruthSequence` built from `gridTruth_approxDetermined` (error
`(1/2)/(n+1) → 0`) and `C`, the emission `feedbackTraderEmissionSigns`; then
`BoundedSequence.wubexp`'s scaling argument (mesh price `= (1/2)·a_n`, truth `= (1/2)·g_n`), and
the grid centre's `2/(n+1)` distance from the realized value washed out by the donor rule.
Scope: one-way. e.d. family. Schedule: strictly increasing `DeferralFunction`. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §4 L3 / §3 L2; FAF `thm:wubexp`, `thm:wubaff`; mandate K4
Kind: C
Fidelity: exact (L3 with corrected 4.8.16's timing condition asked of a computable stream)
Hyps: (a) `hworld`, `hW`, `hdiv`, `hd`, `hsupp`; (c) `pkg.reflected`; (b) `C` (corrected 4.8.16's timing condition, on the grid truth — the stream `Open.lean` asks a `MarketComputation` to write). -/
theorem quoteSide_fullLimit_grid {H P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W P)
    {d : DeferralFunction} (hd : StrictlyIncreasingDeferral d)
    (hsupp : WeightingSupportedOnDeferralImage W P d)
    (C : FeedbackTruth.FeedbackTruthComputation (gridTruth (realized H f X)) d) :
    WeightedApprox (fun i => (W i).denote P) (quoteSeq Y P) (realized H f X) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  set q : ℝ := ((LUVCombination.meshNormScale 1 : ℚ) : ℝ) with hqdef
  have hq : 0 < q := LUVCombination.meshNormScale_pos 1
  let As : ℕ → LUVCombination := fun n => LUVCombination.ofLUV (Y n)
  let h : LUVCombination.BoundedSequence As P := pkg.boundedSequence P
  have hshare : ∀ n, (As n).shareNorm P ≤ ((1 : ℚ) : ℝ) := by
    intro n
    show (LUVCombination.ofLUV (Y n)).shareNorm P ≤ ((1 : ℚ) : ℝ)
    rw [shareNorm_ofLUV]
    norm_num
  have herr : Tendsto (fun n : ℕ => q * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := tendsto_const_div_succ_atTop_nhds_zero q
    simpa only [mul_one_div] using this
  let bridge := FeedbackTruth.feedbackTruthSequence (h.normalizedMesh_poly 1)
    (h.normalizedMesh_boundedPrices 1 hP) (gridTruth_approxDetermined pkg (P := P)) herr C hd
    (LUVCombination.normalizedMesh_magnitude_le_one 1 hshare) hP hworld
  have haff := AffineCombination.lic_wubaff (h.normalizedMesh_poly 1) hW hd hsupp
    (FeedbackEmission.feedbackTraderEmissionSigns (h.normalizedMesh_poly 1) hW hd) bridge hdiv
    (LUVCombination.normalizedMesh_magnitude_le_one 1 hshare) hworld
  let w : ℕ → ℝ := fun i => (W i).denote P
  let a : ℕ → ℝ := fun i => (Y i).expect P i
  let g : ℕ → ℝ := fun i => gridRound (i + 1) (realized H f X i)
  have hprice : (fun i => (LUVCombination.normalizedMesh As 1 i).price P i) =
      fun i => q * a i := by
    funext i
    simp [LUVCombination.normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      LUVCombination.meshAffine_price_diagonal, As, a, ofLUV_expect, q]
  have hg : gridTruth (realized H f X) = fun i => q * g i := rfl
  rw [hprice, hg] at haff
  have hscaled : Tendsto (fun n => q * weightedBias w a g n) atTop (𝓝 0) := by
    have heq : weightedBias w (fun i => q * a i) (fun i => q * g i) =
        fun n => q * weightedBias w a g n :=
      funext (fun n => weightedBias_const_mul w a g q n)
    rw [heq] at haff
    simpa only [AsympEq, sub_zero] using haff
  have hag : WeightedApprox w a g := by
    rw [weightedApprox_iff_weightedBias]
    have hu := hscaled.const_mul q⁻¹
    convert hu using 1 <;> simp [hq.ne']
  have hgy : WeightedApprox w g (realized H f X) := by
    refine weightedApprox_of_tendsto_zero (fun i => (hdiv.1 i).1) hdiv.2 ?_
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall fun n => gridRound_sub_realized_abs_le pkg hworld n)
      (tendsto_const_div_succ_atTop_nhds_zero 2)
  exact WeightedApprox.trans hdiv.2 hag hgy

/-! ## D. When FAF's literal certificate coincides with the grid one -/

/-- **Strict reflection**: every completed-theory world of `DP` decides every threshold atom of
`Y n` with strict polarity at the realized value — `⌜Y n > r⌝` holds iff `r < y_n`. Stronger than
`CrossQuotePackage.reflected` (`PCWorld.ValuesAt`, silent at `r = y_n`); it is what a
literal-schedule process that publishes the value as decided atoms with strict polarity gives
(`li-quote-lane`'s ledger: `a j n ≤ r → ¬ Holds`).
Source: `li-quote-lane` `Ledger.lean` (the strict-polarity ledger literal); mandate K4
Kind: D
Fidelity: variant: strict polarity at the grid point added to `reflected`
Hyps: n/a -/
def StrictlyReflected (H : History) (DP : DeductiveProcess) (f : DeferralFunction)
    (X Y : ℕ → LUV) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    ∀ r : ℚ, v.Holds ((Y n).gt r) ↔ (r : ℝ) < (X n).expect H (f.f n)

/-- Under strict reflection a world's mesh payout is exactly the grid indicator, so its
precision-`k` approximate expectation is exactly the grid rounding.
Source: mandate K4
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma expectApprox_eq_gridRound_of_strict {v : PCWorld} {X : LUV} {x : ℝ}
    (hstr : ∀ r : ℚ, v.Holds (X.gt r) ↔ (r : ℝ) < x) (k : ℕ) :
    X.expectApprox v.payout k = gridRound k x := by
  unfold LUV.expectApprox gridRound
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hcast : (((i : ℚ) / (k : ℚ) : ℚ) : ℝ) = (i : ℝ) / (k : ℝ) := by push_cast; ring
  rw [PCWorld.payout, hstr, hcast]

/-- **FAF's mesh truth is the grid truth under strict reflection**: `normalizedMeshTruth` (the
chosen world's mesh value) equals `gridTruth (realized H f X)` pointwise, so FAF's literal
certificate `QuoteCertificate` and the grid certificate are the same object there.
Source: mandate K4; FAF `normalizedMeshTruth`, `theoryWorld`
Kind: L
Fidelity: exact
Hyps: (c) `hstr : StrictlyReflected …` -/
theorem normalizedMeshTruth_eq_gridTruth_of_strict {H P : History} {DP : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (hstr : StrictlyReflected H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n)) P DP hworld 1 n =
      gridTruth (realized H f X) n := by
  rw [LUVCombination.normalizedMeshTruth, LUVCombination.meshTheoryTruth, gridTruth]
  congr 1
  rw [LUVCombination.meshAffine_value, ofLUV_value]
  exact expectApprox_eq_gridRound_of_strict
    (hstr n _ (LUVCombination.theoryWorld_consistent DP hworld)) (n + 1)

/-- A grid certificate is FAF's literal certificate under strict reflection (the data is the
same; only `agrees` is re-pointed).
Source: mandate K4
Kind: L
Fidelity: exact
Hyps: (c) `hstr` -/
def QuoteCertificate.ofGrid {H P : History} {DP : DeductiveProcess} {f : DeferralFunction}
    {X Y : ℕ → LUV} (hstr : StrictlyReflected H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {d : DeferralFunction}
    (C : FeedbackTruth.FeedbackTruthComputation (gridTruth (realized H f X)) d) :
    QuoteCertificate P DP Y hworld d where
  value := C.value
  code := C.code
  computes := C.computes
  computes_at := C.computes_at
  agrees := fun k => by
    rw [C.agrees k, normalizedMeshTruth_eq_gridTruth_of_strict hstr hworld]

/-! ## E. The one certificate shape FAF hands over for free -/

/-- **A value stream metered in the component index certifies every schedule.** If the rational
stream `k ↦ v k` is `MachineRatCodes` (poly-time in the unary `k`) and agrees with `truth (d k)`,
then `code z := ⌜v (unpair z).1⌝` is `MachineDigits` (`MachineRatCodes.toMachineDigits` reindexed
by `UnaryRuler.unpairFst`) and reads `⌜v k⌝` at every paired index `⟨k, _⟩`. This is the
*poly-in-`k`* shape — it never applies to an inductor's prices along a sparse schedule (the value
`y_{d k}` costs at least `f (d k)` steps, not `poly k`); the schedule-metered shape, where the time
allowance is the unary length of `⟨k, d (k+1)⟩`, is what `Open.lean` leaves open.
Source: FAF `FeedbackTruthComputation` docstring ("`MachineRatCodes.toMachineDigits` is the general route for an arbitrary rational stream"); [[route-sparse-schedule]] §3 Lemma 1(b)
Kind: L
Fidelity: weaker: poly in the component index, not in the schedule day
Hyps: (a) `hv`, `hagree` -/
def FeedbackTruthComputation.ofMachineRatCodes {truth : ℕ → ℝ} (d : DeferralFunction)
    (v : ℕ → ℚ) (hv : MachineRatCodes v) (hagree : ∀ k, (v k : ℝ) = truth (d k)) :
    FeedbackTruth.FeedbackTruthComputation truth d where
  value := v
  code := fun z => Encodable.encode (v z.unpair.1)
  computes := (hv.toMachineDigits.comp UnaryRuler.unpairFst).of_eq (fun _ => rfl)
  computes_at := fun k => by simp
  agrees := hagree

end Cleanroom.Fa.FaForcingTrader.B
