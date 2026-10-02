import Cleanroom.Deference.DefLatticeArrows.Partition

/-!
# F12 — def-lattice's `BandReflection` contains soft Total Trust as its wide-band case

Package `def-lattice-arrows`, file 16 (repair round 1; the content of audit r1 fidelity B1's
probe `WideBand.lean`, made a finding of record).

def-lattice's `BandReflection P DP E` quantifies over every band half-width `ε > 0` with no
upper bound. A band `bandWt δ (v + ε) ε` with `1 + δ ≤ v + 2ε` equals the up-ramp
`rampAbove δ v` at every `x ≤ 1` — and every expert estimate lies in `[0,1]`
(`Expert.estimate_mem_Icc`) — so any ramp `WeightQuote` at `(v, δ)` is already a `WeightQuote`
at that band with the same `W`, `XW`, and the band's lower face at `s − ε = v` *is* the soft
Total-Trust face at `(v, δ)`. Hence `TotalTrust` follows from `BandReflection` alone: no
`BandQuotesAvailable`, no grid, no partition (`totalTrust_of_bandReflection`).

Consequences. (i) Over def-lattice's predicate, [[reflection-in-li]]'s partition argument is
redundant: the arrow it proves is a special case of its hypothesis. (ii) Its content is that
**narrow** bands suffice: `Partition.lean` states the per-instance theorems from the `K` band
faces (`softAbove_instance_of_bandFaces`) and the predicate-level arrows from
`BandReflectionWithin P DP E c` (half-width `≤ c·δ`), where no band is the ramp at any
`v < 1 − 2cδ` (`bandWt_ne_rampAbove_of_narrow`, below) — so there the wide-band route is
closed and the partition is what proves the face. (iii) The square over the unbounded
predicate (`bandReflection_iff_totalTrust_onQuotes`) has `→` free and `←` at T5 + T4b's cost.

This is a finding about def-lattice's encoding (its `BandReflection` docstring says nothing
of the half-width), not about the wiki, whose bands are the grid's.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-! ### The wide band is the ramp -/

/-- On `x ≤ 1`, the band `bandWt δ (v + ε) ε` with `1 + δ ≤ v + 2ε` is the up-ramp at `v`:
the down-ramp factor `ctsInd δ (v + 2ε) x` is `1` there.
Source: none: infrastructure (audit r1 fidelity B1's probe)
Kind: L
Fidelity: exact -/
theorem bandWt_wide_eq_ramp {δ v ε : ℚ} (hδ : 0 < δ) (hwide : (1 : ℚ) + δ ≤ v + 2 * ε)
    {x : ℝ} (hx : x ≤ 1) : bandWt δ (v + ε) ε x = rampAbove δ v x := by
  have h1 : ((v + ε : ℚ) : ℝ) - (ε : ℝ) = (v : ℝ) := by push_cast; ring
  have h2 : ctsInd δ (((v + ε : ℚ) : ℝ) + (ε : ℝ)) x = 1 := by
    rw [ctsInd_eq_one_iff hδ]
    have : (1 : ℝ) + δ ≤ v + 2 * ε := by exact_mod_cast hwide
    push_cast
    linarith
  simp only [bandWt, rampAbove]
  rw [h1, h2, mul_one]

/-- On `0 ≤ x`, the band `bandWt δ (v − ε) ε` with `v − 2ε + δ ≤ 0` is the down-ramp at `v`.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem bandWt_wide_eq_rampBelow {δ v ε : ℚ} (hδ : 0 < δ) (hwide : v - 2 * ε + δ ≤ 0)
    {x : ℝ} (hx : 0 ≤ x) : bandWt δ (v - ε) ε x = rampBelow δ v x := by
  have h1 : ((v - ε : ℚ) : ℝ) + (ε : ℝ) = (v : ℝ) := by push_cast; ring
  have h2 : ctsInd δ x (((v - ε : ℚ) : ℝ) - (ε : ℝ)) = 1 := by
    rw [ctsInd_eq_one_iff hδ]
    have : (v : ℝ) - 2 * ε + δ ≤ 0 := by exact_mod_cast hwide
    push_cast
    linarith
  simp only [bandWt, rampBelow]
  rw [h1, h2, one_mul]

/-- A ramp `WeightQuote` is a wide-band `WeightQuote` with the same `W`, `XW`: the reflection
clauses evaluate the weight only at the expert's estimate, which lies in `[0,1]`.
Source: none: infrastructure (audit r1 fidelity B1's probe)
Kind: D
Fidelity: exact -/
def WeightQuote.toWideBand {E : Expert DP} {X W XW : ℕ → LUV} {δ v ε : ℚ} (hδ : 0 < δ)
    (hwide : (1 : ℚ) + δ ≤ v + 2 * ε) (q : WeightQuote DP E X (rampAbove δ v) W XW) :
    WeightQuote DP E X (bandWt δ (v + ε) ε) W XW where
  weight_codes := q.weight_codes
  product_codes := q.product_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  weight_reflected := fun n w hw => by
    rw [bandWt_wide_eq_ramp hδ hwide (E.estimate_mem_Icc X n).2]
    exact q.weight_reflected n w hw
  product_reflected := fun n w hw x hx => by
    rw [bandWt_wide_eq_ramp hδ hwide (E.estimate_mem_Icc X n).2]
    exact q.product_reflected n w hw x hx

/-- The mirror: a below-ramp `WeightQuote` is a wide-band `WeightQuote` below `v`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def WeightQuote.toWideBandBelow {E : Expert DP} {X W XW : ℕ → LUV} {δ v ε : ℚ} (hδ : 0 < δ)
    (hwide : v - 2 * ε + δ ≤ 0) (q : WeightQuote DP E X (rampBelow δ v) W XW) :
    WeightQuote DP E X (bandWt δ (v - ε) ε) W XW where
  weight_codes := q.weight_codes
  product_codes := q.product_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  weight_reflected := fun n w hw => by
    rw [bandWt_wide_eq_rampBelow hδ hwide (E.estimate_mem_Icc X n).1]
    exact q.weight_reflected n w hw
  product_reflected := fun n w hw x hx => by
    rw [bandWt_wide_eq_rampBelow hδ hwide (E.estimate_mem_Icc X n).1]
    exact q.product_reflected n w hw x hx

/-! ### Total Trust from the unbounded predicate alone -/

/-- **Soft Total Trust above from `BandReflection` alone** — no band quotes, no grid, no
partition: the wide band centred at `v + ε` with `2ε ≥ 1 + δ − v` is the ramp at `v`, and its
lower face is the soft face at `(v, δ)`.
Source: audit r1 fidelity B1 (probe); [[reflection-in-li]] §It joins the circle (what the
partition is *not* needed for over an unbounded band predicate)
Kind: L
Fidelity: exact
Hyps: (a) none beyond `BandReflection` -/
theorem softTotalTrustAbove_of_bandReflection {E : Expert DP}
    (hB : BandReflection P DP E) {v δ : ℚ} (hδ : 0 < δ) :
    SoftTotalTrustAbove P DP E v δ := by
  intro X W XW hX q
  obtain ⟨ε, hεpos, hwide⟩ : ∃ ε : ℚ, 0 < ε ∧ (1 : ℚ) + δ ≤ v + 2 * ε :=
    ⟨max 1 ((1 + δ - v) / 2 + 1), lt_of_lt_of_le one_pos (le_max_left _ _), by
      have := le_max_right (1 : ℚ) ((1 + δ - v) / 2 + 1)
      linarith⟩
  have hface := (hB (v + ε) ε δ hεpos hδ).1 X W XW hX (WeightQuote.toWideBand hδ hwide q)
  have hs : (v + ε - ε : ℚ) = v := by ring
  simp only [hs] at hface
  exact hface

/-- **Soft Total Trust below from `BandReflection` alone**, via the wide band below `v`.
Source: audit r1 fidelity B1 (probe)
Kind: L
Fidelity: exact
Hyps: (a) none beyond `BandReflection` -/
theorem softTotalTrustBelow_of_bandReflection {E : Expert DP}
    (hB : BandReflection P DP E) {v δ : ℚ} (hδ : 0 < δ) :
    SoftTotalTrustBelow P DP E v δ := by
  intro X W XW hX q
  obtain ⟨ε, hεpos, hwide⟩ : ∃ ε : ℚ, 0 < ε ∧ v - 2 * ε + δ ≤ 0 :=
    ⟨max 1 ((v + δ) / 2 + 1), lt_of_lt_of_le one_pos (le_max_left _ _), by
      have := le_max_right (1 : ℚ) ((v + δ) / 2 + 1)
      linarith⟩
  have hface := (hB (v - ε) ε δ hεpos hδ).2 X W XW hX (WeightQuote.toWideBandBelow hδ hwide q)
  have hs : (v - ε + ε : ℚ) = v := by ring
  simp only [hs] at hface
  exact hface

/-- **`BandReflection ⟹ TotalTrust` with no existence clause at all** (F12): over
def-lattice's unbounded-width predicate the arrow is a special case of its hypothesis. The
mandate's arrow under the mandate's name; the partition argument's content is
`totalTrust_of_bandReflectionWithin` (`Partition.lean`, narrow bands).
Source: [[reflection-in-li]] §It joins the circle ("Hence soft value-Reflection ⟺ TT");
audit r1 fidelity B1
Kind: L
Fidelity: exact (trivially so: a wide band is the ramp)
Hyps: (a) none beyond `BandReflection` -/
theorem totalTrust_of_bandReflection {E : Expert DP} (hB : BandReflection P DP E) :
    TotalTrust P DP E :=
  fun _ _ hδ => ⟨softTotalTrustAbove_of_bandReflection hB hδ,
    softTotalTrustBelow_of_bandReflection hB hδ⟩

/-- **The square `BandReflection ⟺ TotalTrust`, on the quotes** (unbounded predicate): `→` is
free (a wide band is the ramp); `←` runs the loop — Total Trust ⟹ Tower on valued sources by
gap-bets (T5) ⟹ band Reflection at every band (T4b). Every clause charged is `←`'s; the
narrow square `bandReflectionWithin_iff_totalTrust_onQuotes` is the one whose `→` is the
partition.
Source: [[reflection-in-li]] §It joins the circle (the four-face square); mandate T4
Kind: L
Fidelity: exact (modulo the disclosed clauses of `←`)
Hyps: (c) `GapPackagesAvailable`, band `ProductQuotesAvailable` (existence);
`ExpertPinsGaps`, band `ExpertFoldsAt` ((b) self / (c) general); `hworld` — all for `←` -/
theorem bandReflection_iff_totalTrust_onQuotes [IsLogicalInductor P DP] {E : Expert DP}
    (hg : GapPackagesAvailable DP E) (hp : ExpertPinsGaps DP E)
    (hq : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ProductQuotesAvailable DP E (bandWt δ s ε))
    (hf : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ExpertFoldsAt DP E (bandWt δ s ε))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BandReflection P DP E ↔ TotalTrust P DP E :=
  ⟨fun hB => totalTrust_of_bandReflection hB,
    fun hT => bandReflection_of_towerValued (towerValued_of_softTotalTrust_gapBets hT hg hp hworld)
      hq hf hworld⟩

/-! ### No narrow band is the ramp -/

/-- **No narrow band is the ramp**: if `2ε < 1 − v` (and `0 ≤ v`) then `bandWt δ s ε` and
`rampAbove δ v` differ at some point of `[0,1]` — the band's support `(s − ε, s + ε)` has
length `2ε`, the ramp is positive on all of `(v, 1]`. So under `ε ≤ c·δ` the wide-band route
is closed for every threshold `v < 1 − 2cδ`: `BandReflectionWithin P DP E c` does not contain
those faces as instances, and the partition (`Partition.lean`) is what proves them. Whatever
the ramp width `δ`.
Source: audit r1 fidelity B1 ("no wide-band route exists"); none otherwise: infrastructure
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ`, `0 < ε`, `0 ≤ v`, `2ε < 1 − v` -/
theorem bandWt_ne_rampAbove_of_narrow {δ s ε v : ℚ} (hδ : 0 < δ) (hε : 0 < ε) (hv : 0 ≤ v)
    (hnarrow : 2 * ε < 1 - v) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ bandWt δ s ε x ≠ rampAbove δ v x := by
  have hvR : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have hnR : 2 * (ε : ℝ) < 1 - v := by exact_mod_cast hnarrow
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  by_cases hcase : (v : ℝ) < (s : ℝ) - ε
  · -- the band starts above `v`: at `x = min (s − ε) 1` the band is `0`, the ramp positive
    refine ⟨min ((s : ℝ) - ε) 1, ?_, min_le_right _ _, ?_⟩
    · exact le_trans hvR (le_min hcase.le (by linarith))
    · have hband : bandWt δ s ε (min ((s : ℝ) - ε) 1) = 0 := by
        simp only [bandWt]
        rw [(ctsInd_eq_zero_iff hδ _ _).mpr (min_le_left _ _), zero_mul]
      have hramp : 0 < rampAbove δ v (min ((s : ℝ) - ε) 1) := by
        simp only [rampAbove]
        exact (ctsInd_pos_iff hδ _ _).mpr (lt_min hcase (by linarith))
      rw [hband]; exact hramp.ne
  · -- the band starts at or below `v`: it ends below `1`, where the ramp is positive
    have hcase' : (s : ℝ) - ε ≤ v := not_lt.mp hcase
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have hband : bandWt δ s ε 1 = 0 := by
      simp only [bandWt]
      rw [(ctsInd_eq_zero_iff hδ _ _).mpr (by linarith : (s : ℝ) + ε ≤ 1), mul_zero]
    have hramp : 0 < rampAbove δ v 1 := by
      simp only [rampAbove]
      exact (ctsInd_pos_iff hδ _ _).mpr (by linarith)
    rw [hband]; exact hramp.ne

end

end Cleanroom.Deference.DefLatticeArrows
