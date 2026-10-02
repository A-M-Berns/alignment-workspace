import Cleanroom.Li.LiDiagonal.Engine
import Cleanroom.Li.LiDiagonal.Family
import Cleanroom.Found.LiAsympCalc.WeightedAverage

/-!
# `li-diagonal` · Forcing: Forcing Theorem A over the diagonal pair (T2c), Theorem C(i) (T3.3)

**Two-way.** Every headline here is stated over `DiagonalPair f` (`Defs.lean`), whose
inhabitation is `li-coupled-pair`'s open row: the ledger (`H` reads `A`) is built, the
`CrossQuotePackage` (`A` reads `H`) is the (c) of record. Ledger status: `partial: over the OPEN
pair`, never `proved`.

**Forcing Theorem A** (lean-deference-048; root-fa-018's "quote pinning";
[[fa-positive-results-corrected-v3]] §6): `A`'s published quote `a_n = A_n(⌜Y_n > ½⌝)` is pinned
at `½`. The engine (`pinning_engine`) runs on `A`'s market at the indicator of the median
threshold `⌜Y_n > ½⌝`: its determined value is the side `s_n` (through `D.cross.reflected` and the
tracking hypothesis `htrack : |𝔼^H_{f(n)}(𝟙 g_n) − s_n| < ¼`, eventually — Lemma B's conclusion,
`Family.lean`), and its expectation is linked to the published price by `thm:ei`
(`lic_expectation_indicator`) and to the side by the ledger (`gDiag_decided`: quote above `½` ⟹
`g_n` false ⟹ side `0`). Because `htrack` holds only eventually, the family is **prefix-patched**
(`patchPrefix`: the first `N` members replaced by `𝟙⊤`, determined at `1`) so that determinacy
holds on every day as the engine requires; the engine's conclusion is unaffected on the tail.

The engine never used the deferral: the same statement holds with the quote at any index of
`A`'s choosing (lean-deference-057) — `forcingA` is parametric in `f`. lean-deference-2-009(c)'s
"reductio meta-move" is this theorem's contrapositive; the scope note's gate argument is not
formalized as stated.

**Theorem C(i)** (lean-deference-2-008): over the same package, for every `A`-generable divergent
weighting `u`, `0` is a limit point of `weightedAverage u (s_n − ½)`: recurring unbiasedness of
`A`'s expectation of `𝟙⌜Y_n > ½⌝` against the side, with the expectation `→ ½` washed out through
`li-asymp-calc`'s weighted-average calculus.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## The median sentence and the H-side expectation -/

/-- `A`'s median-threshold sentence `⌜Y_n > ½⌝` of a diagonal pair — the sentence `A` publishes
the price of (`quoted_eq`).
Source: [[li-diagonal-mandate]] § Definitions of record (`DiagonalPair`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def DiagonalPair.median {f : DeferralFunction} (D : DiagonalPair f) (n : ℕ) : Sentence :=
  (D.Y n).gt (1 / 2)

/-- The median sentences are e.c. (from the cross package's threshold codes at the fixed query
`⟨m, ⟨2, 1⟩⟩`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem DiagonalPair.median_codes {f : DeferralFunction} (D : DiagonalPair f) :
    MachineSentenceCodes D.median := by
  have h := MachineSentenceCodes.comp D.cross.quote_codes
    (UnaryRuler.id.pair ((UnaryRuler.const 2).pair (UnaryRuler.const 1)))
  refine MachineSentenceCodes.of_eq h fun m => ?_
  simp only [Nat.unpair_pair, DiagonalPair.median]
  norm_num

/-- `H`'s realized day-`f n` expectation of the indicator of `g_n` — the quantity `A`'s `Y n` is
determined at (`D.cross.reflected`).
Source: [[li-diagonal-mandate]] T2c (`htrack`'s left side)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def DiagonalPair.eH {f : DeferralFunction} (D : DiagonalPair f) (n : ℕ) : ℝ :=
  (LUV.indicatorOf (gDiag n)).expect D.pair.H (f n)

/-! ## Prefix patching of a LUV family -/

/-- The family `Y` with its first `N` members replaced by the indicator of `⊤` (determined at `1`
in every world).
Source: none: infrastructure (the tail trick for `DeterminedVia`)
Kind: D
Fidelity: n/a -/
def patchPrefix (N : ℕ) (Y : ℕ → LUV) (n : ℕ) : LUV :=
  if n < N then LUV.indicatorOf ⊤ else Y n

/-- `patchPrefix_of_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem patchPrefix_of_le (N : ℕ) (Y : ℕ → LUV) {n : ℕ} (hn : N ≤ n) :
    patchPrefix N Y n = Y n := by
  unfold patchPrefix; rw [if_neg (not_lt.mpr hn)]

/-- The prefix patch of an e.c. family is e.c. (FAF's `MachineSentenceCodes.ifZero` on the
paired index with the ruler test `m.unpair.1 + 1 − N`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem patchPrefix_codes (N : ℕ) (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    LUV.MachineThresholdCodeSeq (patchPrefix N Y) := by
  have htop : LUV.MachineThresholdCodeSeq (fun _ : ℕ => LUV.indicatorOf (⊤ : Sentence)) :=
    LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const (⊤ : Sentence))
  have ht : UnaryRuler (fun m : ℕ => m.unpair.1 + 1 - N) :=
    UnaryRuler.unpairFst.succ.sub (UnaryRuler.const N)
  have h := MachineSentenceCodes.ifZero htop hY ht
  refine MachineSentenceCodes.of_eq h fun m => ?_
  simp only [patchPrefix]
  by_cases hlt : m.unpair.1 < N
  · rw [if_pos (by omega), if_pos hlt]
  · rw [if_neg (by omega), if_neg hlt]

/-- The indicator of `⊤` is determined at `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem indicatorOf_top_determinedVia (DP : DeductiveProcess) :
    LUV.DeterminedVia (LUV.indicatorOf (⊤ : Sentence)) DP 1 := by
  intro v hv
  have h := (LUV.indicatorOf_isIndicator (⊤ : Sentence) DP).valuesAt hv
  rwa [PCWorld.payout, if_pos (PCWorld.holds_top v)] at h

/-- The published number is `A`'s price of the median sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DiagonalPair.median_price {f : DeferralFunction} (D : DiagonalPair f) (n : ℕ) :
    D.pair.A n (D.median n) = (D.pair.a 0 n : ℝ) := by
  rw [D.pair.a_eq 0 n, D.quoted_eq n]; rfl

/-- **The median sentence's completed-world truth is the side**, on a day where `H`'s expectation
tracks the side within `¼`: `A`'s `Y n` is determined at `𝔼^H_{f(n)}(𝟙 g_n)` (`cross.reflected`),
which is above `½` iff the side is `1`.
Source: [[li-diagonal-mandate]] T2c (`hdet` from `D.cross.reflected` plus `htrack`)
Kind: L
Fidelity: exact
Hyps: (c) `D.cross.reflected` -/
theorem DiagonalPair.median_payout {f : DeferralFunction} (D : DiagonalPair f) (n : ℕ)
    (htr : |D.eH n - side (D.pair.a 0) n| < 1 / 4) (v : PCWorld)
    (hv : v.ConsistentWithTheory D.pair.DPA) :
    v.payout (D.median n) = side (D.pair.a 0) n := by
  have hval := D.cross.reflected n v hv
  unfold PCWorld.payout DiagonalPair.median
  rcases side_eq_zero_or_one (D.pair.a 0) n with hs | hs
  · rw [hs] at htr ⊢
    have hlt : D.eH n < (1 / 2 : ℚ) := by
      have := (abs_lt.1 htr).2; push_cast; linarith
    rw [if_neg ((hval.2.2 (1 / 2)).2 hlt)]
  · rw [hs] at htr ⊢
    have hgt : ((1 / 2 : ℚ) : ℝ) < D.eH n := by
      have := (abs_lt.1 htr).1; push_cast; linarith
    rw [if_pos ((hval.2.2 (1 / 2)).1 hgt)]

/-! ## Forcing Theorem A -/

/-- **T2c (headline). Forcing Theorem A, over the diagonal pair**: `A`'s published quote
`A_n(⌜Y_n > ½⌝)` is pinned at `½`, given the tracking hypothesis
`htrack : ∀ᶠ n, |𝔼^H_{f(n)}(𝟙 g_n) − s_n| < ¼` (Lemma B's conclusion). The engine on `A`'s market at
the prefix-patched indicator of the median threshold, with `thm:ei` linking its expectation to the
published price and the ledger (`gDiag_decided`) linking the price to the side.
Scope: **two-way** (`partial: over the OPEN pair`); threshold `½`, deferral `f`; `gDiag` over the ledger.
Source: [[lean-deference-inventory]] 048 (Forcing Theorem A), 057; [[root-fa-inventory]] 018 ("quote pinning"); [[fa-positive-results-corrected-v3]] §6; [[li-diagonal-mandate]] T2c
Kind: C
Fidelity: variant — the published number is `A`'s *price* of the median threshold (disclosed at `DiagonalPair`)
Hyps: (c) `D.cross.reflected` (the Σ₁-completeness of `Γ_A` about `H`; `li-coupled-pair`); (b)-or-derived `htrack` (Lemma B under its certificates, `lemmaB_quarter`; else lean-deference-2-007(a)) -/
theorem forcingA {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) :
    (fun n => D.pair.A n (D.pair.quoted 0 n)) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  haveI := D.pair.A_inductor
  have hmed := D.median_codes
  have hind := LUV.indicatorOf_machineThresholdCodeSeq hmed
  have hei := lic_expectation_indicator D.pair.A D.pair.DPA D.median hmed
    (fun n => LUV.indicatorOf (D.median n)) hind D.hworldA
    (fun n => LUV.indicatorOf_isIndicator _ _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 htrack
  have hmedprice : ∀ n, D.pair.A n (D.median n) = (D.pair.a 0 n : ℝ) := D.median_price
  -- the patched family and its determined values
  set Y'' : ℕ → LUV := patchPrefix N (fun n => LUV.indicatorOf (D.median n)) with hY''
  set y'' : ℕ → ℝ := fun n => if n < N then 1 else side (D.pair.a 0) n with hy''
  have hdet : ∀ n, LUV.DeterminedVia (Y'' n) D.pair.DPA (y'' n) := by
    intro n
    by_cases hn : n < N
    · simp only [hY'', hy'', patchPrefix, if_pos hn]
      exact indicatorOf_top_determinedVia _
    · simp only [hY'', hy'', patchPrefix, if_neg hn]
      intro v hv
      have h := (LUV.indicatorOf_isIndicator (D.median n) D.pair.DPA).valuesAt hv
      rwa [D.median_payout n (hN n (not_lt.mp hn)) v hv] at h
  have hY''codes : LUV.MachineThresholdCodeSeq Y'' := patchPrefix_codes N _ hind
  -- the engine
  have hengine := pinning_engine D.pair.A D.pair.DPA Y'' hY''codes y'' hdet (1 / 2) (1 / 4)
    (by norm_num) (fun ε hε => by
      have hei' := asympEq_iff_eventuallyWithin.1 hei (ε / 2) (by positivity)
      filter_upwards [hei', eventually_ge_atTop N] with n hn hnN
      have hY''n : Y'' n = LUV.indicatorOf (D.median n) := patchPrefix_of_le N _ hnN
      have hy''n : y'' n = side (D.pair.a 0) n := by
        simp only [hy'', if_neg (not_lt.mpr hnN)]
      rw [hY''n, hy''n]
      obtain ⟨h1, h2⟩ := abs_le.1 hn
      rw [hmedprice n] at h1 h2
      constructor
      · intro hgt
        have hgt' : (1 / 2 : ℚ) < D.pair.a 0 n := by
          have : ((1 / 2 : ℚ) : ℝ) < D.pair.a 0 n := by push_cast at hgt ⊢; linarith
          exact_mod_cast this
        rw [(side_eq_zero_iff _ _).2 hgt']
        push_cast; norm_num
      · intro hlt
        have hlt' : D.pair.a 0 n ≤ 1 / 2 := by
          have : (D.pair.a 0 n : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast at hlt ⊢; linarith
          exact le_of_lt (by exact_mod_cast this)
        rw [(side_eq_one_iff _ _).2 hlt']
        push_cast; norm_num) D.hworldA
  -- transfer from the patched family to the price
  have hexp : (fun n => (LUV.indicatorOf (D.median n)).expect D.pair.A n) ≈ₙ
      fun _ => ((1 / 2 : ℚ) : ℝ) := by
    unfold AsympEq at hengine ⊢
    refine hengine.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hY'', patchPrefix_of_le N _ hn]
  have hfinal := hei.symm.trans hexp
  have heq : (fun n => D.pair.A n (D.pair.quoted 0 n)) = fun n => D.pair.A n (D.median n) := by
    funext n; rw [D.quoted_eq n]; rfl
  rw [heq]
  push_cast at hfinal
  exact hfinal

/-- Forcing Theorem A in the published-table form: `a_n → ½`.
Scope: two-way (`partial: over the OPEN pair`).
Source: [[lean-deference-inventory]] 048; [[li-diagonal-mandate]] T2c
Kind: L
Fidelity: as `forcingA`
Hyps: as `forcingA` -/
theorem forcingA_table {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) :
    (fun n => (D.pair.a 0 n : ℝ)) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  have h := forcingA D htrack
  have heq : (fun n => D.pair.A n (D.pair.quoted 0 n)) = fun n => (D.pair.a 0 n : ℝ) :=
    funext fun n => (D.pair.a_eq 0 n).symm
  rwa [heq] at h

/-! ## Theorem C(i) -/

/-- The median sentence family with its first `N` members replaced by `⊤`.
Source: none: infrastructure (the tail trick for `TheoryTruth`)
Kind: D
Fidelity: n/a -/
def DiagonalPair.patchMedian {f : DeferralFunction} (D : DiagonalPair f) (N : ℕ) (n : ℕ) :
    Sentence :=
  if n < N then ⊤ else D.median n

/-- The patched median family is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem DiagonalPair.patchMedian_codes {f : DeferralFunction} (D : DiagonalPair f) (N : ℕ) :
    MachineSentenceCodes (D.patchMedian N) := by
  have ht : UnaryRuler (fun n : ℕ => n + 1 - N) := UnaryRuler.id.succ.sub (UnaryRuler.const N)
  have h := MachineSentenceCodes.ifZero (MachineSentenceCodes.const (⊤ : Sentence))
    D.median_codes ht
  refine MachineSentenceCodes.of_eq h fun n => ?_
  simp only [DiagonalPair.patchMedian]
  by_cases hlt : n < N
  · rw [if_pos (by omega), if_pos hlt]
  · rw [if_neg (by omega), if_neg hlt]

/-- Linearity of the normalized weighted average at a nonzero denominator.
Source: none: infrastructure (FAF `weightedAverage`)
Kind: L
Fidelity: n/a -/
theorem weightedAverage_lin (w x y z : ℕ → ℝ) {n : ℕ} (hden : prefixSum w n ≠ 0) :
    weightedAverage w (fun i => z i + y i - x i) n =
      weightedAverage w z n + weightedAverage w y n - weightedAverage w x n := by
  simp only [weightedAverage, if_neg hden]
  unfold prefixSum
  rw [← add_div, ← sub_div]
  congr 1
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **T3.3 Theorem C(i)** (lean-deference-2-008): over the diagonal pair with the tracking
hypothesis, for every `A`-generable divergent weighting `u`, `0` is a limit point of the
`u`-weighted average of `s_n − ½`. FAF's `thm:recurringunbiasedness` on the prefix-patched
median sentence family (truth = the side, `median_payout`), with `A`'s price of the median
`→ ½` (`forcingA_table`) washed out through `li-asymp-calc`'s `weightedAverage_tendsto_zero`
and the patch washed out through `weightedAverage_tendsto_zero_of_eventually_zero`.
Scope: **two-way** (`partial: over the OPEN pair`); threshold `½`, deferral `f`.
Source: [[lean-deference-2-inventory]] 008 (Theorem C(i)); [[li-diagonal-mandate]] T3.3
Kind: C
Fidelity: exact
Hyps: (c) `D.cross.reflected`; (b)-or-derived `htrack` (as `forcingA`) -/
theorem theoremC_i {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4)
    (u : ℕ → EF) (hu : PGenerableWeighting u) (hdiv : DivergentWeighting u D.pair.A) :
    HasLimitPoint (weightedAverage (fun i => (u i).denote D.pair.A)
      (fun n => side (D.pair.a 0) n - 1 / 2)) 0 := by
  haveI := D.pair.A_inductor
  obtain ⟨N, hN⟩ := eventually_atTop.1 htrack
  set w : ℕ → ℝ := fun i => (u i).denote D.pair.A with hw
  set y'' : ℕ → ℝ := fun n => if n < N then 1 else side (D.pair.a 0) n with hy''
  have htruth : AffineCombination.TheoryTruth (D.patchMedian N) D.pair.DPA y'' := by
    intro n v hv
    simp only [DiagonalPair.patchMedian, hy'']
    by_cases hn : n < N
    · rw [if_pos hn, if_pos hn, PCWorld.payout, if_pos (PCWorld.holds_top v)]
    · rw [if_neg hn, if_neg hn]
      exact D.median_payout n (hN n (not_lt.mp hn)) v hv
  have hlim := AffineCombination.recurringunbiasedness (D.patchMedian N)
    (AffineCombination.sentenceAffine_polySequence _ (D.patchMedian_codes N)) hu htruth hdiv
    D.hworldA
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hdiv.1 i).1
  have hdivS : Tendsto (prefixSum w) atTop atTop := hdiv.2
  have hA : Tendsto (fun i => D.pair.A i (D.patchMedian N i) - 1 / 2) atTop (𝓝 0) := by
    have h := forcingA_table D htrack
    unfold AsympEq at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [DiagonalPair.patchMedian, if_neg (not_lt.mpr hn)]
    rw [D.median_price n]
  have h1 : Tendsto (weightedAverage w (fun i => D.pair.A i (D.patchMedian N i) - 1 / 2))
      atTop (𝓝 0) := weightedAverage_tendsto_zero hw0 hdivS hA
  have h2 : Tendsto (weightedAverage w (fun i => side (D.pair.a 0) i - y'' i)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero_of_eventually_zero hw0 hdivS (N := N)
      (fun n hn => by simp only [hy'', if_neg (not_lt.mpr hn), sub_self])
  rw [hasLimitPoint_zero_iff]
  intro ε hε
  have hX := (hasLimitPoint_zero_iff.1 hlim) (ε / 3) (by positivity)
  have hY := (Metric.tendsto_nhds.1 h1) (ε / 3) (by positivity)
  have hZ := (Metric.tendsto_nhds.1 h2) (ε / 3) (by positivity)
  have hpos := hdiv.eventually_prefixSum_pos
  refine (hX.and_eventually (hY.and (hZ.and hpos))).mono ?_
  rintro n ⟨hx, hy, hz, hp⟩
  rw [Real.dist_eq, sub_zero] at hy hz
  have hden : prefixSum w n ≠ 0 := ne_of_gt hp
  have hside : (fun i => side (D.pair.a 0) i - 1 / 2) =
      fun i => (side (D.pair.a 0) i - y'' i) + (D.pair.A i (D.patchMedian N i) - 1 / 2) -
        (D.pair.A i (D.patchMedian N i) - y'' i) := funext fun i => by ring
  rw [hside, weightedAverage_lin w _ _ _ hden]
  unfold weightedBias at hx
  have hx' : |weightedAverage w (fun i => D.pair.A i (D.patchMedian N i) - y'' i) n| < ε / 3 := hx
  have hz' : |weightedAverage w (fun i => side (D.pair.a 0) i - y'' i) n| < ε / 3 := hz
  have hy' : |weightedAverage w (fun i => D.pair.A i (D.patchMedian N i) - 1 / 2) n| < ε / 3 := hy
  rw [sub_eq_add_neg]
  have ha := abs_add_le (weightedAverage w (fun i => side (D.pair.a 0) i - y'' i) n +
    weightedAverage w (fun i => D.pair.A i (D.patchMedian N i) - 1 / 2) n)
    (-weightedAverage w (fun i => D.pair.A i (D.patchMedian N i) - y'' i) n)
  have hb := abs_add_le (weightedAverage w (fun i => side (D.pair.a 0) i - y'' i) n)
    (weightedAverage w (fun i => D.pair.A i (D.patchMedian N i) - 1 / 2) n)
  rw [abs_neg] at ha
  linarith

/-! ## T4, the cross-process face -/

/-- **T4, cross-process face over the diagonal pair** (`partial: over the OPEN pair`; audit r1
N5): (i) pointwise, `A`'s published quote fails to track the settled side by `½` in the limit —
`a_n → ½` (`forcingA_table`) while `s_n ∈ {0,1}`; (ii) averaged, for every `A`-generable divergent
`u`, `0` is a limit point of the `u`-weighted average of `s_n − ½` (`theoremC_i`). The two faces
of lean-deference-050 in the cross-process reading: pointwise tracking dies, averaged tracking
survives.
Scope: **two-way** (`partial: over the OPEN pair`); threshold `½`, deferral `f`.
Source: [[lean-deference-inventory]] 050 (cross-process reading), 048; [[li-diagonal-mandate]] T4 (the cross-process form over `DiagonalPair`, `partial`)
Kind: C
Fidelity: variant (price of the median threshold, as `forcingA`; the averaged face is against `s_n − ½`, equivalent to `s_n − a_n` under `a_n → ½`)
Hyps: (c) `D.cross.reflected`; (b)-or-derived `htrack` (as `forcingA`) -/
theorem two_faces_pair {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) :
    (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |(D.pair.a 0 n : ℝ) - side (D.pair.a 0) n|) ∧
    ∀ u : ℕ → EF, PGenerableWeighting u → DivergentWeighting u D.pair.A →
      HasLimitPoint (weightedAverage (fun i => (u i).denote D.pair.A)
        (fun n => side (D.pair.a 0) n - 1 / 2)) 0 := by
  refine ⟨?_, fun u hu hdiv => theoremC_i D htrack u hu hdiv⟩
  intro ε hε
  have h := forcingA_table D htrack
  unfold AsympEq at h
  filter_upwards [h.eventually (Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε)] with n hn
  obtain ⟨hlo, hhi⟩ := hn
  rcases side_eq_zero_or_one (D.pair.a 0) n with hs | hs <;> rw [hs]
  · exact le_abs.2 (Or.inl (by linarith))
  · exact le_abs.2 (Or.inr (by linarith))

/-! ## Lemma B's bridge to the expectation (repair round 2)

`htrack` is about the reader's day-`f n` *expectation* `𝔼^H_{f(n)}(𝟙 g_n)`; `lemmaB` is about the
*price* `H_{f(n)}(g_n)`. The bridge (audit r1 fidelity N2, audit r2 fidelity N2) is `thm:ei`
(`lic_expectation_indicator`) on the **padded `g` family** `padG f` — `g_k` at day `f k`, `⊤` off
the image — read at `m = f n`. Its e.c. certificate `hG` is one more cost-model certificate of the
same shape as `hR`/`hR'`; at `succDeferral` it is derived from `gDiag_codes` (`padG_codes_succ`).
-/

open Classical in
/-- **The padded `g` family along `f`**: `g_k` at day `m = f k`, `⊤` at days off the image.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 007 (the family `thm:ei` is applied to); [[li-diagonal-handoff]] item 8
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def padG (f : DeferralFunction) (m : ℕ) : Sentence :=
  if h : ∃ k, f k = m then gDiag (Nat.find h) else ⊤

/-- The padded `g` family reads `g_n` at `f n` when `f` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padG_apply (f : DeferralFunction) (hf : Function.Injective f.f) (n : ℕ) :
    padG f (f n) = gDiag n := by
  unfold padG
  have h : ∃ k, f k = f n := ⟨n, rfl⟩
  rw [dif_pos h]
  congr 1
  exact hf (Nat.find_spec h)

/-- At `succDeferral` the padded `g` family is `⊤` on day `0` and `g_{m−1}` on day `m ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padG_succ (m : ℕ) : padG succDeferral m = if m = 0 then ⊤ else gDiag (m - 1) := by
  cases m with
  | zero =>
    unfold padG
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    have h := padG_apply succDeferral (fun a b hab => Nat.succ_injective hab) k
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    exact h

/-- **The padded `g` family is e.c. at `succDeferral`** (K9: FAF's `ifZero` dispatch on the ruler
`m ↦ m` between the constant `⊤` and `gDiag` composed with `m ↦ m − 1`).
Source: [[li-diagonal-mandate]] K9; [[li-diagonal-handoff]] item 8
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padG_codes_succ : MachineSentenceCodes (padG succDeferral) := by
  have htop : MachineSentenceCodes (fun _ : ℕ => (⊤ : Sentence)) :=
    MachineSentenceCodes.const (⊤ : Sentence)
  have hg : MachineSentenceCodes (fun m : ℕ => gDiag (m - 1)) :=
    MachineSentenceCodes.comp gDiag_codes (UnaryRuler.id.sub (UnaryRuler.const 1))
  have h := MachineSentenceCodes.ifZero htop hg UnaryRuler.id
  refine MachineSentenceCodes.of_eq h fun m => ?_
  simp only [padG_succ]

/-- **Lemma B, expectation form** (the bridge): the reader's day-`f n` expectation of the
indicator of `g_n` tracks the side, `|𝔼^H_{f(n)}(𝟙 g_n) − s_n| → 0`. `thm:ei` on the padded `g`
family read at `f n` gives `𝔼^H_{f(n)}(𝟙 g_n) − H_{f(n)}(g_n) → 0`; `lemmaB` gives the rest.
Scope: one-way; deferral `f` (injective).
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2, T2c (`htrack`)
Kind: C
Fidelity: exact (the expectation reading of the chat's `E^H_{2^n}(g_n)`; `lemmaB` is the price reading)
Hyps: (c) `hR`, `hR'` (as `lemmaB`), `hG` (the padded `g` family's certificate; (a) at `succDeferral` by `padG_codes_succ`) -/
theorem lemmaB_expect (pair : OneWayPair) (f : DeferralFunction) (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide pair.a f))
    (hR' : MachineSentenceCodes (padFalseSide pair.a f))
    (hG : MachineSentenceCodes (padG f)) :
    Tendsto (fun n => |(LUV.indicatorOf (gDiag n)).expect pair.H (f n) - side (pair.a 0) n|)
      atTop (𝓝 0) := by
  haveI := pair.H_inductor
  have hei := lic_expectation_indicator pair.H pair.process (padG f) hG
    (fun m => LUV.indicatorOf (padG f m)) (LUV.indicatorOf_machineThresholdCodeSeq hG)
    pair.hworld (fun m => LUV.indicatorOf_isIndicator _ _)
  have hei' : Tendsto (fun n =>
      (LUV.indicatorOf (gDiag n)).expect pair.H (f n) - pair.H (f n) (gDiag n)) atTop (𝓝 0) := by
    unfold AsympEq at hei
    have := hei.comp f.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp, padG_apply f hf n]
  have hB := lemmaB pair f hf hR hR'
  have hsum : Tendsto (fun n =>
      |(LUV.indicatorOf (gDiag n)).expect pair.H (f n) - pair.H (f n) (gDiag n)| +
        |pair.H (f n) (gDiag n) - side (pair.a 0) n|) atTop (𝓝 0) := by
    simpa using hei'.abs.add hB
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hsum
  exact abs_sub_le _ _ _

/-- **`htrack` from Lemma B** (the bridge at `¼`): the hypothesis `forcingA`, `forcingA_table`,
`theoremC_i` and `two_faces_pair` take, discharged from Lemma B's certificates.
Scope: one-way; deferral `f` (injective).
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T2c
Kind: L
Fidelity: exact
Hyps: (c) `hR`, `hR'`, `hG` as in `lemmaB_expect` -/
theorem lemmaB_expect_quarter (pair : OneWayPair) (f : DeferralFunction)
    (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide pair.a f))
    (hR' : MachineSentenceCodes (padFalseSide pair.a f))
    (hG : MachineSentenceCodes (padG f)) :
    ∀ᶠ n in atTop,
      |(LUV.indicatorOf (gDiag n)).expect pair.H (f n) - side (pair.a 0) n| < 1 / 4 :=
  (lemmaB_expect pair f hf hR hR' hG).eventually (Iio_mem_nhds (by norm_num))

/-- **Forcing Theorem A with `htrack` discharged from Lemma B**: over a diagonal pair whose
reader's padded families are e.c., `A`'s published quote `→ ½`. `htrack` is no longer a
(b)-or-derived hypothesis here; what remains (c) is the pair's `cross.reflected` and the three
cost-model certificates.
Scope: two-way (`partial: over the OPEN pair`); deferral `f` (injective).
Source: [[lean-deference-inventory]] 048; [[li-diagonal-mandate]] T2c
Kind: C
Fidelity: variant (price of the median threshold, as `forcingA`)
Hyps: (c) `D.cross.reflected`; (c) `hR`, `hR'`, `hG` -/
theorem forcingA_of_lemmaB {f : DeferralFunction} (D : DiagonalPair f)
    (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide D.pair.a f))
    (hR' : MachineSentenceCodes (padFalseSide D.pair.a f))
    (hG : MachineSentenceCodes (padG f)) :
    (fun n => D.pair.A n (D.pair.quoted 0 n)) ≈ₙ fun _ => (1 / 2 : ℝ) :=
  forcingA D (lemmaB_expect_quarter D.pair f hf hR hR' hG)

/-- **Two faces over the pair with `htrack` discharged from Lemma B** (`two_faces_pair` with the
tracking hypothesis derived).
Scope: two-way (`partial: over the OPEN pair`); deferral `f` (injective).
Source: [[lean-deference-inventory]] 050 (cross-process reading); [[li-diagonal-mandate]] T4
Kind: C
Fidelity: variant (as `two_faces_pair`)
Hyps: (c) `D.cross.reflected`; (c) `hR`, `hR'`, `hG` -/
theorem two_faces_pair_of_lemmaB {f : DeferralFunction} (D : DiagonalPair f)
    (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide D.pair.a f))
    (hR' : MachineSentenceCodes (padFalseSide D.pair.a f))
    (hG : MachineSentenceCodes (padG f)) :
    (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |(D.pair.a 0 n : ℝ) - side (D.pair.a 0) n|) ∧
    ∀ u : ℕ → EF, PGenerableWeighting u → DivergentWeighting u D.pair.A →
      HasLimitPoint (weightedAverage (fun i => (u i).denote D.pair.A)
        (fun n => side (D.pair.a 0) n - 1 / 2)) 0 :=
  two_faces_pair D (lemmaB_expect_quarter D.pair f hf hR hR' hG)

end Cleanroom.Li.LiDiagonal
