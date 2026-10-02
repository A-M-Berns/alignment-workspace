import Cleanroom.Deference.DefArgmaxValue.Endorse
import Cleanroom.Deference.DefArgmaxValue.LiarProbe
import Cleanroom.Deference.DefSqueezeDiamond.SelfPins

/-!
# `def-argmax-value` · Concentration: the introspective-concentration lemma (target 7)

[[total-trust-implies-value]] §Lemma 2 Step 3's named gap (open-problems item 1): *self-prediction
mass concentrates on near-max-quoted options*. **Route A of the mandate** — the fold at a
generable ramp, not `lic_introspection`'s single-price band (finding: the page's "direct
corollary of `lic_introspection`" is misdirected, the selection compares `k+1` mesh
expectations; the fold is the corollary that exists):

* For each pair `(i, j)` and width/threshold `δ, ε'`, the **pairwise ramp**
  `c^{i,j}_n := Ind_δ(m^i_n − m^j_n > ε')` is a `[0,1]` rational feature of day-`f n` prices
  (`pairRampWeight`, `pairRampWeight_pgenerable` — `def-self-trust`'s `rampWeight_pgenerable`
  with the difference of two expectation features in place of one against a constant). Pairwise
  ramps avoid `EF.max` over `k+1` features: on a day with `m^j_n ≤ M_n − ε` the pair
  `(argmax, j)` has ramp `1`.
* The product `⌜I^j_n · c^{i,j}_n⌝` is valued `0` in every world (where the ramp is positive `j`
  is not the argmax, so `I^j = 0`), hence `E*(product) ≈ₙ 0` by deferred provind; **the fold**
  gives `E*(product) ≈ₙ c^{i,j}_n · E*(I^j_n)` — for the self-expert `def-squeeze-diamond`'s
  `selfFold_core` (`gateKnowledge_product` at day `f n`), for a general expert the `(c)` clause
  `ConcentrationFolds` (`PairFold`), the package's H2. Hence `c^{i,j}_n · E*(I^j_n) → 0`, and
  summing over `i`: `E*(I^j_n) · 1[m^j_n ≤ M_n − ε] → 0` (`concentrates_of_folds`).
* `concentrationFolds_self`: the fold clause is a theorem for the self-expert on every menu and
  every selection package; `concentrates_self` is the lemma at grade (a).

The "day-`n` belief about a fact decided at `e(n) ≥ n`" subtlety of the page dissolves: the fold
is same-day at `f n`, and the bit is decided by `A`'s own day-`f n` prices.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable {DP : DeductiveProcess}

/-! ## The fold clause (H2) -/

/-- **A pairwise-ramp fold** for the indicator `I^j` against the pair `(i, j)` at width `δ` and
threshold `ε'`: an e.c. product `Z` valued within a vanishing slack at
`x · Ind_δ(m^i_n − m^j_n > ε')` whenever `I^j_n` is valued `x`, whose estimate the expert folds:
`E*(Z_n) ≈ₙ Ind_δ(m^i_n − m^j_n > ε') · E*(I^j_n)`. The introspection hypothesis (H2) in FAF's
form: the fold at a generable weight, with its slack (design decision 7).
Source: [[total-trust-implies-value]] §Hypotheses (H2) ("used only through Lemma 2's
concentration step"); mandate target 7, route A (ii)
Kind: D
Fidelity: variant: asymptotic fold within FAF's slack (the corpus's exact `E*(⌜E*(X)⌝) = E*(X)`
is uninhabited for FAF inductors) -/
structure PairFold (DP : DeductiveProcess) (E : Expert DP) {k : ℕ} (M : Menu k)
    (I : Fin (k + 1) → ℕ → LUV) (i j : Fin (k + 1)) (δ ε' : ℚ) where
  /-- the product LUV -/
  Z : ℕ → LUV
  /-- it is e.c. -/
  codes : LUV.MachineThresholdCodeSeq Z
  /-- the reflection slack -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- `Z n` is valued within `slack n` of `x · Ind_δ(m^i_n − m^j_n > ε')` -/
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x, v.ValuesAt (I j n) x →
    ∃ z, v.ValuesAt (Z n) z ∧
      |z - x * ctsInd δ (M.quote E i n - M.quote E j n) ε'| ≤ slack n
  /-- the expert folds the ramp out -/
  fold : (fun n => E.estimate Z n) ≈ₙ
    (fun n => ctsInd δ (M.quote E i n - M.quote E j n) ε' * E.estimate (I j) n)

/-- **The fold clause (H2) of the scoped theorem**: a pairwise-ramp fold for every pair and every
positive width/threshold — `ExpertFoldAt` at target 7's ramps. `(c)` for a general expert;
`(a)` for the self-expert (`concentrationFolds_self`).
Source: mandate target 7 ("`(c)` `ExpertFoldAt` for a general `E`"); design decision 7
Kind: D
Fidelity: variant: asymptotic within slack -/
def ConcentrationFolds (DP : DeductiveProcess) (E : Expert DP) {k : ℕ} (M : Menu k)
    (I : Fin (k + 1) → ℕ → LUV) : Prop :=
  ∀ (i j : Fin (k + 1)) (δ ε' : ℚ), 0 < δ → Nonempty (PairFold DP E M I i j δ ε')

/-! ## Concentration from the fold -/

/-- **The concentration lemma, from the fold** (target 7, the proof): for an inductor-expert with
a selection package and the fold clause, `E*(I^j_n) · 1[m^j_n ≤ M_n − ε] → 0`. Mechanism: each
pairwise product is valued `0` in every world (where the ramp is positive, `j` is not the
argmax), so its estimate `→ 0` by deferred provind; the fold turns that into
`c^{i,j}_n · E*(I^j_n) → 0`; on a day with `m^j_n ≤ M_n − ε`, the pair `(argmax, j)` has ramp
`1` at `δ = ε' = ε/2`, so `E*(I^j_n) ≤ Σ_i c^{i,j}_n · E*(I^j_n) → 0`.
Source: [[total-trust-implies-value]] §Lemma 2 Step 3; vq-wiki-016; lean-deference-068 Step 3;
mandate target 7 route A
Kind: C
Fidelity: exact (sharp form)
Hyps: (a); `hf`; `hfold : ConcentrationFolds` ((a) self, `(c)` general) -/
theorem concentrates_of_folds {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (hfold : ConcentrationFolds DP E M I)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Concentrates E M I := by
  intro ε hε j
  obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (half_pos hε)
  have hr : 0 < r := by exact_mod_cast hr0
  -- for each `i`, the pairwise product
  have hpair : ∀ i : Fin (k + 1), Tendsto (fun n =>
      ctsInd r (M.quote E i n - M.quote E j n) r * E.estimate (I j) n) atTop (𝓝 0) := by
    intro i
    obtain ⟨F⟩ := hfold i j r r hr
    have hzero : (fun n => E.estimate F.Z n) ≈ₙ (fun _ => (0 : ℝ)) := by
      have h := expect_deferred_const (P := E.A) (DP := DP) E.f hf 0 F.codes F.slack
        F.slack_tendsto (fun n v hv => by
          obtain ⟨z, hz, hb⟩ := F.reflected n v hv _ (pkg.reflected_I j n v hv)
          refine ⟨z, hz, ?_⟩
          have hprod : (if M.argmax E n = j then (1 : ℝ) else 0) *
              ctsInd r (M.quote E i n - M.quote E j n) r = 0 := by
            by_cases hc : M.argmax E n = j
            · rw [if_pos hc, one_mul]
              apply ctsInd_eq_zero_of_le hr
              have h1 : M.quote E i n ≤ M.maxQuote E n := M.quote_le_maxQuote E i n
              have h2 : M.quote E j n = M.maxQuote E n := hc ▸ M.argmax_attains E n
              have : (0 : ℝ) ≤ r := by exact_mod_cast hr.le
              linarith
            · rw [if_neg hc, zero_mul]
          rw [hprod, _root_.sub_zero] at hb
          simpa using hb) hworld
      simpa using h
    have hfl := F.fold
    exact tendsto_of_asympEq_const (hfl.symm.trans hzero)
  have hsum : Tendsto (fun n => ∑ i : Fin (k + 1),
      ctsInd r (M.quote E i n - M.quote E j n) r * E.estimate (I j) n) atTop (𝓝 0) := by
    have := tendsto_finset_sum Finset.univ (fun i _ => hpair i)
    simpa using this
  refine squeeze_zero (fun n => mul_nonneg (E.estimate_mem_Icc _ _).1 (by split_ifs <;> norm_num))
    (fun n => ?_) hsum
  by_cases hc : M.quote E j n ≤ M.maxQuote E n - ε
  · rw [if_pos hc, mul_one]
    have hone : ctsInd r (M.quote E (M.argmax E n) n - M.quote E j n) r = 1 := by
      apply ctsInd_eq_one_of_le_sub _ _ _ hr
      rw [M.argmax_attains E n]
      have : (2 : ℝ) * r < ε := by
        have : (r : ℝ) < ε / 2 := hrε
        linarith
      linarith
    calc E.estimate (I j) n = ctsInd r (M.quote E (M.argmax E n) n - M.quote E j n) r *
          E.estimate (I j) n := by rw [hone, one_mul]
      _ ≤ ∑ i : Fin (k + 1), ctsInd r (M.quote E i n - M.quote E j n) r * E.estimate (I j) n :=
          Finset.single_le_sum (f := fun i => ctsInd r (M.quote E i n - M.quote E j n) r *
            E.estimate (I j) n)
            (fun i _ => mul_nonneg (ctsInd_mem_Icc _ _ _).1 (E.estimate_mem_Icc _ _).1)
            (Finset.mem_univ (M.argmax E n))
  · rw [if_neg hc, mul_zero]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (ctsInd_mem_Icc _ _ _).1
      (E.estimate_mem_Icc _ _).1)

/-- **The ramp form of concentration**: `E*(I^j_n) · Ind_δ(M_n − m^j_n > ε) → 0` for every
`δ > 0` (the mandate's statement; `Ind_δ(x > ε) ≤ 1[ε ≤ x]`).
Source: mandate target 7 (the statement)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem concentrates_ramp {E : Expert DP} {k : ℕ} {M : Menu k} {I : Fin (k + 1) → ℕ → LUV}
    (hc : Concentrates E M I) (ε δ : ℚ) (hε : 0 < ε) (hδ : 0 < δ) (j : Fin (k + 1)) :
    Tendsto (fun n => E.estimate (I j) n * ctsInd δ (M.maxQuote E n - M.quote E j n) ε) atTop
      (𝓝 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  refine squeeze_zero (fun n => mul_nonneg (E.estimate_mem_Icc _ _).1 (ctsInd_mem_Icc _ _ _).1)
    (fun n => ?_) (hc ε hεR j)
  by_cases h : M.quote E j n ≤ M.maxQuote E n - ε
  · rw [if_pos h, mul_one]
    exact mul_le_of_le_one_right (E.estimate_mem_Icc _ _).1 (ctsInd_mem_Icc _ _ _).2
  · rw [if_neg h, mul_zero]
    push Not at h
    rw [ctsInd_eq_zero_of_le hδ (by linarith), mul_zero]

/-- **The page's eventual form**: if `m^j_n ≤ M_n − ε` eventually, then `E*(I^j_n) → 0`.
Source: [[total-trust-implies-value]] §Lemma 2 Step 3 ("`P^A_n(sel_n = j) → 0` whenever
`m^j_n ≤ M_n − ε`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem concentrates_eventually {E : Expert DP} {k : ℕ} {M : Menu k} {I : Fin (k + 1) → ℕ → LUV}
    (hc : Concentrates E M I) {ε : ℝ} (hε : 0 < ε) (j : Fin (k + 1))
    (hev : ∀ᶠ n in atTop, M.quote E j n ≤ M.maxQuote E n - ε) :
    Tendsto (fun n => E.estimate (I j) n) atTop (𝓝 0) :=
  (hc ε hε j).congr' (hev.mono (fun n hn => by rw [if_pos hn, mul_one]))

/-! ## The self-expert: the fold is a theorem -/

section Self

variable {P : History} (market : MarketComputation P)

/-- **The pairwise ramp weight** `Ind_δ(E_m(X_{f⁻¹ m}) − E_m(Y_{f⁻¹ m}) > ε')` on the image of `f`,
`0` off it (`def-self-trust`'s `rampWeight` with a difference of two expectations in place of
one expectation against a constant).
Source: mandate target 7 route A ("`c_n := ctsInd δ (M_n − m^j_n) ε'` … a `[0,1]` rational
feature of day-`f n` prices"), pairwise
Kind: D
Fidelity: exact -/
def pairRampWeight (f : DeferralFunction) (X Y : ℕ → LUV) (δ ε' : ℚ) (m : ℕ) : ℚ :=
  if deferralImageFlag f m = 1 then
    ratCtsInd δ (market.expectQuoteAt X (deferralPreimage f m) m -
      market.expectQuoteAt Y (deferralPreimage f m) m) ε'
  else 0

/-- The pairwise ramp weight lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pairRampWeight_mem (f : DeferralFunction) (X Y : ℕ → LUV) (δ ε' : ℚ) (m : ℕ) :
    0 ≤ pairRampWeight market f X Y δ ε' m ∧ pairRampWeight market f X Y δ ε' m ≤ 1 := by
  unfold pairRampWeight
  split_ifs
  · exact ratCtsInd_mem_Icc _ _ _
  · exact ⟨le_rfl, zero_le_one⟩

/-- At the deferred day the pairwise ramp weight is the ramp of the difference of the two
deferred expectations, as a real.
Source: none: infrastructure (`rampWeight_at`)
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem pairRampWeight_at_cast (f : DeferralFunction) (hinj : Function.Injective f.f)
    (X Y : ℕ → LUV) (δ ε' : ℚ) (n : ℕ) :
    ((pairRampWeight market f X Y δ ε' (f n) : ℚ) : ℝ) =
      ctsInd δ ((X n).expect P (f n) - (Y n).expect P (f n)) (ε' : ℝ) := by
  simp only [pairRampWeight, deferralImageFlag_at, deferralPreimage_at f hinj, if_true]
  rw [market.expectQuoteAt_cast X n (f n), market.expectQuoteAt_cast Y n (f n), ← Rat.cast_sub,
    ratCtsInd_cast]

/-- **The pairwise ramp weight is P-generable**: FAF's `ctsIndFeature` of the difference of the
two reindexed expectation features against the constant `ε'`, gated by the image flag — the
certificate of `rampWeight_pgenerable` with `EF.add`/`EF.mul` closing the difference.
Source: mandate target 7 route A ("all `EF`-expressible (`price`, `add`, `mul`, `max`, `const`)"
— here `add`, `mul`, `const` suffice: pairwise ramps need no `max`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem pairRampWeight_pgenerable (f : DeferralFunction) {X Y : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hY : LUV.MachineThresholdCodeSeq Y) {δ : ℚ}
    (hδ : 0 < δ) (ε' : ℚ) : PGenerableRat P (pairRampWeight market f X Y δ ε') := by
  have hX' : LUV.MachineThresholdCodeSeq (fun m => X (deferralPreimage f m)) :=
    hX.reindex (unaryRuler_deferralPreimage f)
  have hY' : LUV.MachineThresholdCodeSeq (fun m => Y (deferralPreimage f m)) :=
    hY.reindex (unaryRuler_deferralPreimage f)
  set diff : ℕ → EF := fun m => EF.add (expectFeature (fun m => X (deferralPreimage f m)) m)
    (EF.mul (EF.const (-1)) (expectFeature (fun m => Y (deferralPreimage f m)) m)) with hdiff
  have hdiffgen : PGenerableWeighting diff :=
    PGenerableWeighting.add (expectFeature_pgenerable hX')
      (PGenerableWeighting.mul (constWeighting (-1)) (expectFeature_pgenerable hY'))
  have hcts : PGenerableWeighting (ctsIndFeature (fun _ => δ) diff (fun _ => EF.const ε')) :=
    ctsIndFeature_generated (fun _ => δ) _ _ (MachineRatCodes.const (1 / δ)) hdiffgen
      (constWeighting ε')
  refine ⟨fun m => if deferralImageFlag f m = 0 then EF.const 0 else
      ctsIndFeature (fun _ => δ) diff (fun _ => EF.const ε') m,
    { rank_le := fun m => ?_
      polyTok := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
        hcts.polySeg (unaryRuler_deferralImageFlag f)).of_eq (fun m => by split_ifs <;> rfl)
      closed := fun m ρ V => ?_
      denote := fun m => ?_ }⟩
  · split_ifs
    · simp
    · exact hcts.rank_le m
  · split_ifs
    · simp
    · exact hcts.closed m ρ V
  · unfold pairRampWeight
    rcases deferralImageFlag_zero_or_one f m with h0 | h1
    · simp [h0]
    · rw [if_neg (by omega), if_pos h1,
        ctsIndFeature_denote (fun _ => δ) _ _ (fun _ => hδ) P m]
      simp only [hdiff, EF.denote_add, EF.denote_mul, EF.denote_const, Pi.add_apply, Pi.mul_apply,
        expectFeature_denote]
      rw [market.expectQuoteAt_cast X _ m, market.expectQuoteAt_cast Y _ m]
      have e : ((market.expectQuoteAt X (deferralPreimage f m) m : ℚ) : ℝ) +
          ((-1 : ℚ) : ℝ) * ((market.expectQuoteAt Y (deferralPreimage f m) m : ℚ) : ℝ) =
          ((market.expectQuoteAt X (deferralPreimage f m) m -
            market.expectQuoteAt Y (deferralPreimage f m) m : ℚ) : ℝ) := by
        push_cast; ring
      rw [e, ratCtsInd_cast]

end Self

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The self-expert folds every pairwise ramp of every selection package** (target 7 route A,
(a)): the product is FAF's `meshProductLUV` of the indicator with the quoted pairwise ramp
weight (`paperDeferredWeightQuoteCode` of `pairRampWeight`), reflected within `1/(n+1)`, and
the fold is `def-squeeze-diamond`'s `selfFold_core` (`gateKnowledge_product` at day `f n`).
This closes vq-wiki-018 by lookup: "introspection for market-generable features" is the fold.
Source: mandate target 7 route A (ii); vq-wiki-018 (resolved by lookup); `def-self-trust`
`gateKnowledge_product`; `def-squeeze-diamond` `selfFold_core`
Kind: C
Fidelity: exact (fold within FAF's mesh slack)
Hyps: (a); `hf` -/
theorem concentrationFolds_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {k : ℕ} (M : Menu k) {I Q : Fin (k + 1) → ℕ → LUV}
    (pkg : SelectionPackage (paperDP T) (selfExpert T f) M I Q) :
    ConcentrationFolds (paperDP T) (selfExpert T f) M I := by
  intro i j δ ε' hδ
  set w : ℕ → ℚ := pairRampWeight (paperMarketComputation T) f (M.O i) (M.O j) δ ε' with hw
  have hwgen : PGenerableRat (liaHistory (paperDP T)) w :=
    pairRampWeight_pgenerable (paperMarketComputation T) f (M.codes i) (M.codes j) hδ ε'
  have hwmem : ∀ m, 0 ≤ w m ∧ w m ≤ 1 :=
    pairRampWeight_mem (paperMarketComputation T) f (M.O i) (M.O j) δ ε'
  set q : RationalQuoteCode T (fun n => w (f n)) := paperDeferredWeightQuoteCode T f w hwgen hwmem
    with hq
  have hcast : ∀ n, ((w (f n) : ℚ) : ℝ) =
      ctsInd δ (M.quote (selfExpert T f) i n - M.quote (selfExpert T f) j n) ε' := fun n => by
    rw [hw, pairRampWeight_at_cast (paperMarketComputation T) f hf.injective]
    rfl
  refine ⟨{ Z := meshProductLUV q (I j)
            codes := meshProductLUV_machineThresholdCodeSeq _ (pkg.codes_I j)
            slack := fun n => 1 / ((n : ℝ) + 1)
            slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
            reflected := fun n v hv x hx => ?_
            fold := ?_ }⟩
  · obtain ⟨z, hz, hb⟩ := meshProductLUV_valuesAt (paperQuotationPresentation T) q (I j) n v hv hx
    exact ⟨z, hz, by rwa [hcast] at hb⟩
  · have h := selfFold_core T f hf (pkg.codes_I j) (meshProductLUV_machineThresholdCodeSeq _
      (pkg.codes_I j)) (pkg.valued_I j) hwgen hwmem (fun n => 1 / ((n : ℝ) + 1))
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n v hv x hx => meshProductLUV_valuesAt (paperQuotationPresentation T) q (I j) n v hv hx)
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [Expert.self_estimate]
    rw [hcast n, mul_comm]
    rfl

/-- **The concentration lemma for the self-expert, at grade (a)** (target 7, load-bearing 4): on
every e.c. menu with every selection package, `E*(I^j_n) · 1[m^j_n ≤ M_n − ε] → 0`.
Source: [[total-trust-implies-value]] §Lemma 2 Step 3 (the named gap, closed for the self-expert);
vq-wiki-016; mandate target 7
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem concentrates_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {k : ℕ} (M : Menu k) {I Q : Fin (k + 1) → ℕ → LUV}
    (pkg : SelectionPackage (paperDP T) (selfExpert T f) M I Q) :
    Concentrates (selfExpert T f) M I :=
  concentrates_of_folds hf pkg (concentrationFolds_self T f hf M pkg) (paperDP_hworld T)

end

end Cleanroom.Deference.DefArgmaxValue
