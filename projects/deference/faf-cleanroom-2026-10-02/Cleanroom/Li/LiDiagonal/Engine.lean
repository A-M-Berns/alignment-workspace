import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Found.LiQuoteLane.Feature
import Cleanroom.Found.LiAsympCalc.LimitPoint
import Cleanroom.Found.LiAsympCalc.Luv
import LogicalInduction.Construction.Statistics.HistoricalMaturity
import LogicalInduction.Construction.LUV.Syntax

/-!
# `li-diagonal` · Engine: the pinning engine (T2a) and its diagonal witness (T2b)

**The engine.** Let `Y n` be an e.c. LUV family determined, in `DP`'s completed theory, at
`y n`, and suppose the *anti-inductive link*: whenever the market's expectation of `Y n` is above
`t` (by any fixed margin `ε`, eventually) the determined value is at most `t − c`, and whenever it
is below `t` the value is at least `t + c`. Then `𝔼_n(Y_n) → t`. Proof: for rational `m > 0`,
the ramp `W n := ctsInd (m/2) (𝔼_n(Y_n)) (t + m/2)` is a legal (`PGenerableWeighting`) feature
of day-`n` prices; on its support the bias `𝔼_n(Y_n) − y n` is `≥ c`, so if `W` were divergent,
FAF's `thm:recurringunbiasednessexp` (`HasLimitPoint (weightedBias …) 0`) would contradict
`li-asymp-calc`'s wash-out lemma `DivergentWeighting.not_hasLimitPoint_weightedBias`. A
non-divergent `[0,1]`-weighting is summable, so `W n → 0`, so eventually `W n < 1`, i.e.
`𝔼_n(Y_n) < t + m`. Dually below. Kind C; every hypothesis (a) except `hlink`, which is the
*input* each application derives.

**Strengthening over the mandate's statement.** The mandate's link has margin `0`
(`t < 𝔼_n(Y_n) → y n ≤ t − c`). This file's `pinning_engine` takes the weaker hypothesis "for
every margin `ε > 0`, eventually `t + ε < 𝔼_n(Y_n) → y n ≤ t − c`" (and dually), which the
margin-`0` form implies (`pinning_engine_sharp`). The weaker hypothesis is what the diagonal
witness can actually supply: `𝔼_n(𝟙 χ_n)` is FAF's indicator LUV's expectation, which equals
`P_n(χ_n ⋏ ∼∼χ_n)`, not `P_n(χ_n)` — the two agree only in the limit (`thm:ei`,
`lic_expectation_indicator`), so the reflection "price above `p` ⟹ sentence false" transfers
to the expectation only with a vanishing margin.

**The witness (T2b).** At FAF's diagonal `χ^p_n` with `Y n := 𝟙 χ_n` (FAF's `LUV.indicatorOf`),
`y n := 𝟙[P_n(χ_n) < p]`, `t := p`, `c := min p (1 − p)`: determinacy from
`diagonal_reflected` and `indicatorOf_isIndicator`, the link from the reflection through
`thm:ei`. Conclusion: `𝔼_n(𝟙 χ_n) → p`, hence `P_n(χ_n) → p` — a second proof of `thm:lp` by
recurring unbiasedness instead of the affine certificates, inhabiting the engine's full
hypothesis package on the real construction (N+ over `paperDP T` in `Paper.lean`).

Scope: single-market throughout. The two-way application (Forcing Theorem A over
`DiagonalPair`) is `Forcing.lean`.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. The expectation price feature of an e.c. LUV family -/

/-- The day-`n` expectation of `Y n` as an expressible feature: the price feature of the
precision-`(n+1)` threshold bundle (FAF's `LUV.expectAffine`). Generalizes `li-quote-lane`'s
`ledgerFeature` from the ledger LUV to any family.
Source: none: infrastructure (`li-quote-lane` `ledgerFeature`)
Kind: D
Fidelity: n/a -/
def expectFeature (Y : ℕ → LUV) (n : ℕ) : EF := ((Y n).expectAffine (n + 1)).priceFeature n

/-- The expectation feature denotes the day-`n` expectation.
Source: none: infrastructure (FAF `priceFeature_denote`, `expectAffine_price`)
Kind: L
Fidelity: n/a -/
theorem expectFeature_denote (Y : ℕ → LUV) (P : History) (n : ℕ) :
    (expectFeature Y n).denote P = (Y n).expect P n := by
  unfold expectFeature
  rw [AffineCombination.priceFeature_denote, LUV.expectAffine_price]

/-- The expectation feature of an e.c. LUV family is a legal feature progression (FAF's
`PGenerableWeighting`), by the proof of `li-quote-lane`'s `ledgerFeature_pgenerable` with the
ledger LUV replaced by `Y`.
Source: none: infrastructure (`li-quote-lane` `ledgerFeature_pgenerable`; FAF `expectAffineSeq_polySequence`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem expectFeature_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    PGenerableWeighting (expectFeature Y) := by
  have hpoly := LUV.expectAffineSeq_polySequence Y hY
  refine { polySeg := ?_, rank_le := ?_, closed := ?_ }
  · refine (hpoly.priceFeature_polySeg.comp (UnaryRuler.id.pair UnaryRuler.id)).of_eq
      fun n => ?_
    simp only [Nat.unpair_pair]
    rfl
  · intro n
    refine AffineCombination.priceFeature_rank _ (Nat.zero_le n) (by simp [LUV.expectAffine]) ?_
    intro p hp
    simp only [LUV.expectAffine, List.mem_map, List.mem_range] at hp
    obtain ⟨i, -, rfl⟩ := hp
    simp
  · intro n ρ V
    exact hpoly.priceFeature_closed n n ρ V

/-! ## B. The single-LUV combination as a bounded sequence -/

/-- The compact syntax of the single-LUV combination sequence `n ↦ ofLUV (Y n)`: one share,
coefficient `1`, constant `0`. FAF API request: FAF has no `BoundedSequence` constructor for a
bare e.c. LUV family.
Source: none: infrastructure (FAF `LUVCombinationSyntax`)
Kind: D
Fidelity: n/a -/
noncomputable def ofLUVSyntax (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    LUVCombinationSyntax (fun n => LUVCombination.ofLUV (Y n)) where
  termCount _ := 1
  coefficient _ := EF.const 1
  luv z := Y z.unpair.1
  termCount_poly := UnaryRuler.const 1
  const_poly := MachineSpliceStream.serialize_const 0
  coefficient_poly := MachineSpliceStream.serialize_const 1
  threshold_poly := by
    have h := MachineSentenceCodes.comp hY
      ((UnaryRuler.unpairFst.comp UnaryRuler.unpairFst).pair UnaryRuler.unpairSnd)
    refine MachineSentenceCodes.of_eq h fun m => ?_
    simp only [Nat.unpair_pair]
  terms_eq n := by simp [LUVCombination.ofLUV]
  const_rank n := by simp [LUVCombination.ofLUV]
  coefficient_rank n j _ := by simp
  const_closed n ρ V := by simp [LUVCombination.ofLUV, EF.denoteWith, EF.denote]
  coefficient_closed z ρ V := by simp [EF.denoteWith, EF.denote]

/-- `n ↦ ofLUV (Y n)` is a FAF `BoundedSequence` (`def:blcp`) for an e.c. family `Y`, with
`L¹` bound `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def ofLUV_boundedSequence (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (P : History) : LUVCombination.BoundedSequence (fun n => LUVCombination.ofLUV (Y n)) P where
  poly := (ofLUVSyntax Y hY).polySequence
  bounded := ⟨1, fun n => (l1Norm_ofLUV (Y n) P).2.le⟩

/-! ## C. A non-divergent `[0,1]`-weighting is eventually below `1` -/

/-- A `[0,1]`-valued feature progression that is not a `DivergentWeighting` has summable
denotations, hence denotations tending to `0`, hence eventually `< 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem eventually_lt_one_of_not_divergent {W : ℕ → EF} {P : History}
    (h01 : ∀ n, 0 ≤ (W n).denote P ∧ (W n).denote P ≤ 1)
    (hnot : ¬ DivergentWeighting W P) :
    ∀ᶠ n in atTop, (W n).denote P < 1 := by
  set w : ℕ → ℝ := fun n => (W n).denote P with hw
  have hmono : Monotone (prefixSum w) := monotone_nat_of_le_succ fun n => by
    simp only [prefixSum, Finset.sum_range_succ]
    linarith [(h01 (n + 1)).1]
  have hbdd : BddAbove (Set.range (prefixSum w)) := by
    by_contra hb
    exact hnot ⟨h01, tendsto_atTop_atTop_of_monotone' hmono hb⟩
  obtain ⟨C, hC⟩ := hbdd
  have hsum : Summable w := by
    refine summable_of_sum_range_le (c := C) (fun n => (h01 n).1) fun n => ?_
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      have h0 : prefixSum w 0 ≤ C := hC (Set.mem_range_self 0)
      simp only [prefixSum_zero] at h0
      linarith [(h01 0).1]
    | succ k => exact hC (Set.mem_range_self k)
  have hzero : Tendsto w atTop (𝓝 0) := hsum.tendsto_atTop_zero
  exact hzero.eventually (Iio_mem_nhds one_pos)

/-! ## D. The engine, one side at a time -/

/-- **Engine, upper side**: under the one-sided link "expectation above `t + ε` ⟹ value
`≤ t − c`" (every margin `ε > 0`, eventually), the expectation is eventually `< t + m` for
every rational `m > 0`. The ramp `ctsInd (m/2) (𝔼_n(Y_n)) (t + m/2)` is legal; divergence is
refuted by `thm:recurringunbiasednessexp` against the one-signed bias `≥ c` on its support;
non-divergence makes it eventually `< 1`.
Source: [[lean-deference-inventory]] 048 (Forcing Theorem A's engine); [[fa-positive-results-corrected-v3]] §3, §6; [[li-diagonal-mandate]] T2a
Kind: C
Fidelity: exact
Hyps: (a) none except the link `hlink` (the input) -/
theorem engine_above (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (y : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (y n)) (t : ℚ) (c : ℝ) (hc : 0 < c)
    (hlink : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, (t : ℝ) + ε < (Y n).expect P n → y n ≤ t - c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (m : ℚ) (hm : 0 < m) :
    ∀ᶠ n in atTop, (Y n).expect P n < t + m := by
  have hm2 : 0 < m / 2 := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let W : ℕ → EF :=
    ctsIndFeature (fun _ => m / 2) (expectFeature Y) (fun _ => EF.const (t + m / 2))
  have hWgen : PGenerableWeighting W :=
    ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / (m / 2)))
      (expectFeature_pgenerable Y hY) (pgenerableWeighting_const (t + m / 2))
  have hWden : ∀ n, (W n).denote P =
      ctsInd (m / 2) ((Y n).expect P n) ((t : ℝ) + (m : ℝ) / 2) := by
    intro n
    show (ctsIndFeature (fun _ => m / 2) (expectFeature Y)
      (fun _ => EF.const (t + m / 2)) n).denote P = _
    rw [ctsIndFeature_denote _ _ _ (fun _ => hm2), expectFeature_denote]
    simp
  have h01 : ∀ n, 0 ≤ (W n).denote P ∧ (W n).denote P ≤ 1 := fun n => by
    rw [hWden]; exact ctsInd_mem_Icc _ _ _
  have hnotdiv : ¬ DivergentWeighting W P := by
    intro hdiv
    have hlim := LUVCombination.BoundedSequence.recurringunbiasednessexp
      (ofLUV_boundedSequence Y hY P) (DeterminedVia.worldValued_ofLUV hdet)
      (DeterminedVia.determinedViaTheory_ofLUV P hdet) hWgen hdiv hworld
    have hmk : (fun i => (LUVCombination.ofLUV (Y i)).expect P i) = fun i => (Y i).expect P i :=
      funext fun i => ofLUV_expect _ _ _
    rw [hmk] at hlim
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlink ((m : ℝ) / 2) (by positivity))
    refine DivergentWeighting.not_hasLimitPoint_weightedBias hdiv hc N ?_ hlim
    intro n hn hpos
    rw [hWden] at hpos
    have hgt : (t : ℝ) + (m : ℝ) / 2 < (Y n).expect P n := (ctsInd_pos_iff hm2 _ _).1 hpos
    have hy := hN n hn hgt
    linarith
  filter_upwards [eventually_lt_one_of_not_divergent h01 hnotdiv] with n hn
  rw [hWden] at hn
  have hne : ¬ ((m / 2 : ℚ) : ℝ) ≤ (Y n).expect P n - ((t : ℝ) + (m : ℝ) / 2) :=
    fun h => absurd ((ctsInd_eq_one_iff hm2 _ _).2 h) hn.ne
  push_cast at hne
  linarith

/-- **Engine, lower side**: the mirror of `engine_above` — under "expectation below `t − ε` ⟹
value `≥ t + c`", the expectation is eventually `> t − m`.
Source: [[lean-deference-inventory]] 048; [[li-diagonal-mandate]] T2a
Kind: C
Fidelity: exact
Hyps: (a) none except the link `hlink` (the input) -/
theorem engine_below (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (y : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (y n)) (t : ℚ) (c : ℝ) (hc : 0 < c)
    (hlink : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, (Y n).expect P n < (t : ℝ) - ε → (t : ℝ) + c ≤ y n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (m : ℚ) (hm : 0 < m) :
    ∀ᶠ n in atTop, (t : ℝ) - m < (Y n).expect P n := by
  have hm2 : 0 < m / 2 := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let W : ℕ → EF :=
    ctsIndFeature (fun _ => m / 2) (fun _ => EF.const (t - m / 2)) (expectFeature Y)
  have hWgen : PGenerableWeighting W :=
    ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / (m / 2)))
      (pgenerableWeighting_const (t - m / 2)) (expectFeature_pgenerable Y hY)
  have hWden : ∀ n, (W n).denote P =
      ctsInd (m / 2) ((t : ℝ) - (m : ℝ) / 2) ((Y n).expect P n) := by
    intro n
    show (ctsIndFeature (fun _ => m / 2) (fun _ => EF.const (t - m / 2))
      (expectFeature Y) n).denote P = _
    rw [ctsIndFeature_denote _ _ _ (fun _ => hm2), expectFeature_denote]
    simp
  have h01 : ∀ n, 0 ≤ (W n).denote P ∧ (W n).denote P ≤ 1 := fun n => by
    rw [hWden]; exact ctsInd_mem_Icc _ _ _
  have hnotdiv : ¬ DivergentWeighting W P := by
    intro hdiv
    have hlim := LUVCombination.BoundedSequence.recurringunbiasednessexp
      (ofLUV_boundedSequence Y hY P) (DeterminedVia.worldValued_ofLUV hdet)
      (DeterminedVia.determinedViaTheory_ofLUV P hdet) hWgen hdiv hworld
    have hmk : (fun i => (LUVCombination.ofLUV (Y i)).expect P i) = fun i => (Y i).expect P i :=
      funext fun i => ofLUV_expect _ _ _
    rw [hmk] at hlim
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlink ((m : ℝ) / 2) (by positivity))
    refine DivergentWeighting.not_hasLimitPoint_weightedBias_neg hdiv hc N ?_ hlim
    intro n hn hpos
    rw [hWden] at hpos
    have hlt : (Y n).expect P n < (t : ℝ) - (m : ℝ) / 2 := (ctsInd_pos_iff hm2 _ _).1 hpos
    have hy := hN n hn hlt
    linarith
  filter_upwards [eventually_lt_one_of_not_divergent h01 hnotdiv] with n hn
  rw [hWden] at hn
  have hne : ¬ ((m / 2 : ℚ) : ℝ) ≤ ((t : ℝ) - (m : ℝ) / 2) - (Y n).expect P n :=
    fun h => absurd ((ctsInd_eq_one_iff hm2 _ _).2 h) hn.ne
  push_cast at hne
  linarith

/-! ## E. The engine -/

/-- **T2a (headline). The pinning engine.** An e.c. LUV family `Y`, determined in `DP`'s
completed theory at `y`, whose market expectation is *anti-inductively linked* to its
determined value around `t` — above `t` (by any margin, eventually) the value is `≤ t − c`,
below `t` it is `≥ t + c` — has expectation `𝔼_n(Y_n) → t`. Composition of
`thm:recurringunbiasednessexp` (FAF) with `li-asymp-calc`'s wash-out lemma through the legal
ramps `ctsInd (m/2) (𝔼_n(Y_n)) (t ± m/2)`. Every hypothesis is (a) except `hlink`, the input
each application derives (`pinning_engine_diagonal` from FAF's diagonal reflection; `forcingA`
from the ledger's decided atom). The link is the *weaker* side: the conclusion implies it for any
`y`, `c` (`link_of_asympEq`), so `hlink ↔ 𝔼_n(Y_n) ≈ₙ t` under the package and this theorem is
the non-trivial direction — not a squeeze.
Scope: single-market; threshold `t`; any family `Y`.
Source: [[lean-deference-inventory]] 048 (Forcing Theorem A, the single-market engine); [[root-fa-inventory]] 018 ("quote pinning"); [[fa-positive-results-corrected-v3]] §6
Kind: C
Fidelity: stronger — the link is asked only with a vanishing margin (the margin-`0` form is `pinning_engine_sharp`)
Hyps: (a) `hY`, `hdet`, `hworld` are the family's own certificates; the link `hlink` is the engine's input -/
theorem pinning_engine (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (y : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (y n)) (t : ℚ) (c : ℝ) (hc : 0 < c)
    (hlink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ((t : ℝ) + ε < (Y n).expect P n → y n ≤ t - c) ∧
      ((Y n).expect P n < (t : ℝ) - ε → (t : ℝ) + c ≤ y n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Y n).expect P n) ≈ₙ fun _ => (t : ℝ) := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  obtain ⟨m, hm0, hmε⟩ := exists_rat_btwn hε
  have hm : 0 < m := by exact_mod_cast hm0
  have hab := engine_above P DP Y hY y hdet t c hc
    (fun ε hε => (hlink ε hε).mono fun n h => h.1) hworld m hm
  have hbl := engine_below P DP Y hY y hdet t c hc
    (fun ε hε => (hlink ε hε).mono fun n h => h.2) hworld m hm
  filter_upwards [hab, hbl] with n h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **The engine's link is the weaker side** (repair round 2; audit r2 adversarial N8, probe
`EngineLinkConverse.lean`): the conclusion `𝔼_n(Y_n) ≈ₙ t` implies the vanishing-margin link
`hlink` for *any* `y`, `c` — both antecedents are eventually false. So under the engine's package
`hlink ↔ 𝔼_n(Y_n) ≈ₙ t`, with `pinning_engine` the non-trivial direction: not a squeeze (the
hypothesis is weaker than the conclusion, not equivalent by definition), recorded so a reader does
not suspect `hlink` of smuggling the limit.
Scope: single-market; threshold `t`.
Source: none: infrastructure (an honesty check on `pinning_engine`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem link_of_asympEq (P : History) (Y : ℕ → LUV) (y : ℕ → ℝ) (t : ℚ) (c : ℝ)
    (h : (fun n => (Y n).expect P n) ≈ₙ fun _ => (t : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ((t : ℝ) + ε < (Y n).expect P n → y n ≤ t - c) ∧
      ((Y n).expect P n < (t : ℝ) - ε → (t : ℝ) + c ≤ y n) := by
  intro ε hε
  filter_upwards [asympEq_iff_eventuallyWithin.1 h ε hε] with n hn
  obtain ⟨h1, h2⟩ := abs_le.1 hn
  exact ⟨fun hgt => absurd hgt (by linarith), fun hlt => absurd hlt (by linarith)⟩

/-- **The engine at margin `0`** — the mandate's statement: the link
`t < 𝔼_n(Y_n) → y n ≤ t − c` and `𝔼_n(Y_n) < t → t + c ≤ y n`, eventually, gives
`𝔼_n(Y_n) → t`. A corollary of `pinning_engine` (a margin-`0` link is a link at every margin).
Scope: single-market; threshold `t`.
Source: [[li-diagonal-mandate]] T2a (the statement as written there)
Kind: L
Fidelity: exact (the mandate's form)
Hyps: (a) as `pinning_engine` -/
theorem pinning_engine_sharp (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (y : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (y n)) (t : ℚ) (c : ℝ) (hc : 0 < c)
    (hlink : ∀ᶠ n in atTop,
      ((t : ℝ) < (Y n).expect P n → y n ≤ t - c) ∧
      ((Y n).expect P n < (t : ℝ) → (t : ℝ) + c ≤ y n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Y n).expect P n) ≈ₙ fun _ => (t : ℝ) :=
  pinning_engine P DP Y hY y hdet t c hc
    (fun ε hε => hlink.mono fun n h =>
      ⟨fun hgt => h.1 (by linarith), fun hlt => h.2 (by linarith)⟩) hworld

/-! ## F. The diagonal witness (T2b) -/

/-- FAF's indicator LUV of the diagonal sentence is determined, in the completed theory, at
the diagonal's truth stream `diagTruth`: from `indicatorOf_isIndicator` (the indicator is valued
at the sentence's payout in every world) and `diagonal_reflected` (the payout is `𝟙[P n χ_n < p]`).
Source: [[li-diagonal-mandate]] T2b (`hdet`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indicatorOf_determinedVia_diag (P : History) (DP : DeductiveProcess) (p : ℚ)
    (q : ParadoxResistanceQuote P DP p) (n : ℕ) :
    LUV.DeterminedVia (LUV.indicatorOf (q.sentence n)) DP (diagTruth P q.sentence p n) := by
  intro v hv
  have h := (LUV.indicatorOf_isIndicator (q.sentence n) DP).valuesAt hv
  have hpay : v.payout (q.sentence n) = diagTruth P q.sentence p n := by
    unfold PCWorld.payout diagTruth
    by_cases hlt : P n (q.sentence n) < (p : ℝ)
    · rw [if_pos hlt, if_pos ((q.diagonal_reflected n v hv).2 hlt)]
    · rw [if_neg hlt, if_neg (fun h => hlt ((q.diagonal_reflected n v hv).1 h))]
  rwa [hpay] at h

/-- **T2b (headline, N+). The engine on FAF's diagonal**: at `Y n := 𝟙 χ_n`,
`y n := 𝟙[P_n(χ_n) < p]`, `t := p`, `c := min p (1 − p)`, the engine's full hypothesis package
is inhabited — `hY` by FAF's `indicatorOf_machineThresholdCodeSeq`, `hdet` by
`indicatorOf_determinedVia_diag`, `hlink` by the diagonal reflection through `thm:ei` — and the
engine concludes `𝔼_n(𝟙 χ_n) → p`. Non-degenerate: the family is FAF's genuine diagonal
(any `ParadoxResistanceQuote`; the Kleene instance over `paperDP T` is in `Paper.lean`), the
determined values are the diagonal's actual truth stream, and the link is a theorem, not a
constant.
Scope: single-market; threshold `p`; FAF's same-day diagonal `χ^p_n`.
Source: [[li-diagonal-mandate]] T2b; LI paper `thm:lp` (second proof)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem pinning_engine_diagonal (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (LUV.indicatorOf (q.sentence n)).expect P n) ≈ₙ fun _ => (p : ℝ) := by
  have hcode := LUV.indicatorOf_machineThresholdCodeSeq q.sentence_codes
  have hei := lic_expectation_indicator P DP q.sentence q.sentence_codes
    (fun n => LUV.indicatorOf (q.sentence n)) hcode hworld
    (fun n => LUV.indicatorOf_isIndicator _ _)
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  refine pinning_engine P DP _ hcode (diagTruth P q.sentence p)
    (indicatorOf_determinedVia_diag P DP p q) p (min (p : ℝ) (1 - p))
    (lt_min hp0R (by linarith)) ?_ hworld
  intro ε hε
  filter_upwards [asympEq_iff_eventuallyWithin.1 hei ε hε] with n hn
  obtain ⟨h1, h2⟩ := abs_le.1 hn
  constructor
  · intro hgt
    have hnot : ¬ P n (q.sentence n) < (p : ℝ) := by linarith
    rw [diagTruth, if_neg hnot]
    linarith [min_le_left (p : ℝ) (1 - p)]
  · intro hlt
    have hyes : P n (q.sentence n) < (p : ℝ) := by linarith
    rw [diagTruth, if_pos hyes]
    linarith [min_le_right (p : ℝ) (1 - p)]

/-- **`thm:lp` by recurring unbiasedness**: `P_n(χ_n) → p` from `pinning_engine_diagonal` and
`thm:ei`. A second, independent proof of FAF's `lic_paradox_resistance` — through the
statistics lane (`recurringunbiasednessexp`) instead of the affine-certificate lane.
Scope: single-market; threshold `p`; FAF's same-day diagonal.
Source: LI paper `thm:lp`; [[li-diagonal-mandate]] T2b
Kind: C
Fidelity: exact (FAF's conclusion)
Hyps: (a) none -/
theorem paradox_resistance_via_engine (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (q.sentence n)) ≈ₙ fun _ => (p : ℝ) := by
  have hei := lic_expectation_indicator P DP q.sentence q.sentence_codes
    (fun n => LUV.indicatorOf (q.sentence n))
    (LUV.indicatorOf_machineThresholdCodeSeq q.sentence_codes) hworld
    (fun n => LUV.indicatorOf_isIndicator _ _)
  exact hei.symm.trans (pinning_engine_diagonal P DP p hp0 hp1 q hworld)

end Cleanroom.Li.LiDiagonal
