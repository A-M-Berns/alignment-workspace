import Cleanroom.Found.LiQuoteLane.PullBack
import Cleanroom.Deference.DefSelfTrust.Comb
import Cleanroom.Deference.DefSelfTrust.FeatComb
import Cleanroom.Deference.DefSelfTrust.Weights
import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# `def-squeeze-diamond` · Reindex: deferred-day provability induction (target 1)

FAF's expectation endpoints (`lic_expect_combination_provind_{le,ge,eq}`) are **same-day**:
the `n`-th combination is priced at day `n`. Every expert-side fact of the deference lattice
(`ExpertPin`, `ExpertFoldAt`, `ExpertFoldCond`) is about the expert's estimate at the
*deferred* day `f n`. This file is the bridge, the keystone the whole package rests on:

* `reindexLUV f X m := X (deferralPreimage f m)` — the family read at the preimage of the day
  (FAF's bounded-scan `deferralPreimage`, `0` off the image). It is e.c. by FAF's own
  `LUV.MachineThresholdCodeSeq.reindex` along the ruler `unaryRuler_deferralPreimage`
  (`reindexLUV_codes`), and equals `X n` at `m = f n` (`reindexLUV_apply`).
* `gateFeat f c m` — a day-`m` feature gated by FAF's `deferralImageFlag`: `c m` on the image,
  the constant `0` off it. Generable when `c` is (`gateFeat_pgenerable`, the pattern of
  `def-self-trust`'s `rampWeight_pgenerable`).
* `deferredComb f c₀ terms` — the feature-coefficient combination over reindexed LUVs with
  gated constant and coefficients. At `m = f n` it is the intended combination of the day-`n`
  members with day-`f n` coefficients; off the image it is identically `0` (every coefficient
  `0`, every term still world-valued). Its compact syntax is `def-self-trust`'s
  `featCombSyntax` applied verbatim.
* The endpoints `expect_deferred_asympLE/GE_of_eventually`,
  `expect_deferred_asympEq_zero_of_eventually_abs_le`, `…_of_slack`: a world bound on the
  deferred combination holding from some member `N` on gives, through `def-self-trust`'s
  eventual `thm:expprovind` on the gated sequence (the bound holds from day `f N` on: on the
  image the preimage is `≥ N` because `f` is strictly increasing, off it the value is `0`)
  and restriction along `f` (`asympLE_comp_deferral`), the asymptotic statement about
  `(fun n => Σ cᵢ(f n) · (Xᵢ n).expect P (f n))`.

**Why the guard is in the coefficients, not the LUV** (the mandate's 1a trap, resolved
differently): a junk LUV at off-image days would make the reindexed family *unvalued* there
and break `LUVCombination.WorldValued`, the premise of every FAF endpoint; gating the
coefficients instead keeps the off-image member a legal, world-valued combination of value
`0`. `deferralPreimage f m` off the image is `0`, so the off-image member reads `X 0` — with
coefficient `0`, which is why no guard inside the LUV is needed. li-quote-lane's
`preimageCount`/`preimageIndex` is the same device under FAF's `scheduledMatch`
(`preimageIndex_eq` / `deferralPreimage_at` agree on the image); FAF's is used because its
ruler certificates and `.reindex` are already in the library.

Single market. Every statement takes `hf : StrictlyIncreasingDeferral f` (design decision 7);
`succDeferral` and `doublingDeferral` qualify (`succDeferral_strict`, `doublingDeferral_strict`
in li-quote-lane).
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows

noncomputable section

/-! ## Reindexing a LUV family along a deferral -/

/-- **The family read at the preimage of the day**: `reindexLUV f X m = X (f⁻¹ m)` on the image
of `f` (FAF's `deferralPreimage`; `0` off the image, so there it reads `X 0` — harmless, see
the module docstring).
Source: mandate target 1a (`reindexLUV`); `def-lattice-arrows` F8/F11(6); `def-self-trust` F13
Kind: D
Fidelity: exact (on the image; the off-image value is never read with a nonzero coefficient) -/
def reindexLUV (f : DeferralFunction) (X : ℕ → LUV) (m : ℕ) : LUV := X (deferralPreimage f m)

/-- **1a. Reindexing preserves e.c.** — FAF's `LUV.MachineThresholdCodeSeq.reindex` along the
unary ruler `deferralPreimage f` (`unaryRuler_deferralPreimage`): only the paired query index
is recomputed. No injectivity is needed for the certificate.
Source: mandate target 1a (`reindexLUV_codes`); FAF `Construction/Quotation/DeferralFibre.lean`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem reindexLUV_codes (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) : LUV.MachineThresholdCodeSeq (reindexLUV f X) :=
  hX.reindex (unaryRuler_deferralPreimage f)

/-- On the image of an injective `f` the reindexed family is the original: `reindexLUV f X (f n) = X n`.
Source: mandate target 1a (`reindexLUV_apply`); FAF `deferralPreimage_at`
Kind: L
Fidelity: exact
Hyps: (a); `hinj` -/
theorem reindexLUV_apply (f : DeferralFunction) (hinj : Function.Injective f.f) (X : ℕ → LUV)
    (n : ℕ) : reindexLUV f X (f n) = X n := by
  simp [reindexLUV, deferralPreimage_at f hinj]

/-- A valued family stays valued under reindexing (every member is some member of `X`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem reindexLUV_valued {DP : DeductiveProcess} (f : DeferralFunction) {X : ℕ → LUV}
    (hX : Valued DP X) : Valued DP (reindexLUV f X) :=
  fun m v hv => hX (deferralPreimage f m) v hv

/-! ## Gated day-`m` features -/

/-- **The gated feature**: `c m` on the image of `f` (FAF's `deferralImageFlag f m = 1`), the
constant `0` off it.
Source: mandate target 1b (the guard); `def-self-trust` `rampWeight` (the same gate)
Kind: D
Fidelity: exact -/
def gateFeat (f : DeferralFunction) (c : ℕ → EF) (m : ℕ) : EF :=
  if deferralImageFlag f m = 0 then EF.const 0 else c m

/-- The gated feature is a generable weighting when `c` is: a two-way dispatch of the emitted
streams on the ruler `deferralImageFlag f` (`MachineSpliceStream.ifZero`), rank and closure
inherited.
Source: none: infrastructure (the certificate of `def-self-trust`'s `rampWeight_pgenerable`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem gateFeat_pgenerable (f : DeferralFunction) {c : ℕ → EF} (hc : PGenerableWeighting c) :
    PGenerableWeighting (gateFeat f c) where
  polySeg := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0) hc.polySeg
    (unaryRuler_deferralImageFlag f)).of_eq (fun m => by unfold gateFeat; split_ifs <;> rfl)
  rank_le m := by
    unfold gateFeat
    split_ifs
    · simp
    · exact hc.rank_le m
  closed m ρ V := by
    unfold gateFeat
    split_ifs
    · simp
    · exact hc.closed m ρ V

/-- On the image the gate is open: `gateFeat f c (f n) = c (f n)`.
Source: none: infrastructure (FAF `deferralImageFlag_at`)
Kind: L
Fidelity: n/a -/
@[simp] theorem gateFeat_apply (f : DeferralFunction) (c : ℕ → EF) (n : ℕ) :
    gateFeat f c (f n) = c (f n) := by
  simp [gateFeat, deferralImageFlag_at]

/-- Off the image the gate is shut: the feature is the constant `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gateFeat_off (f : DeferralFunction) (c : ℕ → EF) {m : ℕ}
    (hm : deferralImageFlag f m = 0) : gateFeat f c m = EF.const 0 := by
  simp [gateFeat, hm]

/-! ## The deferred combination -/

/-- **The deferred combination**: the feature-coefficient combination
`c₀ + Σ pᵢ.1 · pᵢ.2` with every LUV reindexed along `f` and every feature gated — at day
`m = f n` it is `c₀ (f n) + Σ pᵢ.1 (f n) · pᵢ.2 n`, the day-`n` members with day-`f n`
coefficients; off the image it is the zero combination over valued LUVs.
Source: mandate target 1b (the combinations of the deferred-day endpoints)
Kind: D
Fidelity: exact -/
def deferredComb (f : DeferralFunction) (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV))) :
    ℕ → LUVCombination :=
  featComb (gateFeat f c₀) (terms.map fun p => (gateFeat f p.1, reindexLUV f p.2))

/-- **The deferred-day diagonal**: `(c₀ (f n)).denote P + Σ (pᵢ.1 (f n)).denote P · (pᵢ.2 n).expect P (f n)`
— the real sequence every deferred-day endpoint is about.
Source: mandate target 1b (the conclusion `(fun n => (A n).expect P (f n))`)
Kind: D
Fidelity: exact -/
def deferredExpect (P : History) (f : DeferralFunction) (c₀ : ℕ → EF)
    (terms : List ((ℕ → EF) × (ℕ → LUV))) (n : ℕ) : ℝ :=
  (c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * (p.2 n).expect P (f n)).sum

/-- At `m = f n` the deferred combination's day-`f n` expectation is the deferred-day diagonal.
Source: none: infrastructure (`featComb_expect`)
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferredComb_expect_at (f : DeferralFunction) (hinj : Function.Injective f.f)
    (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV))) (P : History) (n : ℕ) :
    (deferredComb f c₀ terms (f n)).expect P (f n) = deferredExpect P f c₀ terms n := by
  simp only [deferredComb, deferredExpect, featComb_expect, List.map_map, Function.comp_def,
    gateFeat_apply, reindexLUV_apply f hinj]

/-- At `m = f n` the deferred combination's world value under `ν` is
`(c₀ (f n)).denote P + Σ (pᵢ.1 (f n)).denote P · ν (pᵢ.2 n)`.
Source: none: infrastructure (`featComb_value`)
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferredComb_value_at (f : DeferralFunction) (hinj : Function.Injective f.f)
    (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV))) (P : History) (n : ℕ) (ν : LUV → ℝ) :
    (deferredComb f c₀ terms (f n)).value P ν =
      (c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * ν (p.2 n)).sum := by
  simp only [deferredComb, featComb_value, List.map_map, Function.comp_def, gateFeat_apply,
    reindexLUV_apply f hinj]

/-- Off the image the deferred combination has world value `0` under every valuation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem deferredComb_value_off (f : DeferralFunction) (c₀ : ℕ → EF)
    (terms : List ((ℕ → EF) × (ℕ → LUV))) (P : History) {m : ℕ}
    (hm : deferralImageFlag f m = 0) (ν : LUV → ℝ) :
    (deferredComb f c₀ terms m).value P ν = 0 := by
  simp [deferredComb, featComb_value, List.map_map, Function.comp_def, gateFeat, hm,
    List.map_const', List.sum_replicate]

/-- A valuation coherent for the deferred combination at `m = f n` values every listed member
`pᵢ.2 n` at `ν (pᵢ.2 n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferredComb_valuesAt_at (f : DeferralFunction) (hinj : Function.Injective f.f)
    {c₀ : ℕ → EF} {terms : List ((ℕ → EF) × (ℕ → LUV))} {n : ℕ} {v : PCWorld} {ν : LUV → ℝ}
    (hν : (deferredComb f c₀ terms (f n)).ValuesAt v ν) :
    ∀ p ∈ terms, v.ValuesAt (p.2 n) (ν (p.2 n)) := by
  intro p hp
  have hmem : (gateFeat f p.1 (f n), reindexLUV f p.2 (f n)) ∈
      (deferredComb f c₀ terms (f n)).terms := by
    simp only [deferredComb, featComb, List.mem_map]
    exact ⟨(gateFeat f p.1, reindexLUV f p.2), ⟨p, hp, rfl⟩, rfl⟩
  have := hν _ hmem
  simpa [reindexLUV_apply f hinj] using this

/-- The `L¹` norm of the deferred combination is bounded by any bound on the ungated
coefficients (off the image it is `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem deferredComb_l1Norm_le (f : DeferralFunction) (c₀ : ℕ → EF)
    (terms : List ((ℕ → EF) × (ℕ → LUV))) (P : History) {B : ℝ} (hB : 0 ≤ B)
    (hbdd : ∀ m, |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum ≤ B)
    (m : ℕ) : (deferredComb f c₀ terms m).l1Norm P ≤ B := by
  rcases deferralImageFlag_zero_or_one f m with h0 | h1
  · have : (deferredComb f c₀ terms m).l1Norm P = 0 := by
      simp [deferredComb, featComb_l1Norm, List.map_map, Function.comp_def, gateFeat, h0,
        List.map_const', List.sum_replicate]
    rw [this]; exact hB
  · have hg : ∀ c : ℕ → EF, gateFeat f c m = c m := fun c => by simp [gateFeat, h1]
    have : (deferredComb f c₀ terms m).l1Norm P =
        |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum := by
      simp only [deferredComb, featComb_l1Norm, List.map_map, Function.comp_def, hg]
    rw [this]; exact hbdd m

/-- The deferred combination is world-valued when every listed LUV family is.
Source: none: infrastructure (the pattern of `listComb_worldValued`)
Kind: L
Fidelity: n/a -/
theorem deferredComb_worldValued {DP : DeductiveProcess} (f : DeferralFunction) (c₀ : ℕ → EF)
    (terms : List ((ℕ → EF) × (ℕ → LUV))) (hval : ∀ p ∈ terms, Valued DP p.2) :
    LUVCombination.WorldValued (deferredComb f c₀ terms) DP := by
  intro m v hv
  refine ⟨worldValue v, fun q hq => ?_⟩
  obtain ⟨p', hp', hq2⟩ := mem_featComb_terms hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
  rw [hq2]
  obtain ⟨x, hx⟩ := hval p hp (deferralPreimage f m) v hv
  exact valuesAt_worldValue hx

/-- **Compact syntax for the deferred combination**: `def-self-trust`'s `featCombSyntax` on the
gated features (`gateFeat_pgenerable`) and the reindexed LUVs (`reindexLUV_codes`).
Source: mandate target 1a–1b (the certificate); `def-self-trust` `featCombSyntax`
Kind: D
Fidelity: n/a -/
def deferredCombSyntax (f : DeferralFunction) {c₀ : ℕ → EF} (hc₀ : PGenerableWeighting c₀)
    {terms : List ((ℕ → EF) × (ℕ → LUV))} (hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1)
    (hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) :
    LUVCombinationSyntax (deferredComb f c₀ terms) := by
  unfold deferredComb
  exact featCombSyntax _ (gateFeat_pgenerable f hc₀) _
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact gateFeat_pgenerable f (hcoeff q hq))
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact reindexLUV_codes f (hluv q hq))

/-! ## Restriction of asymptotic statements along a deferral -/

/-- `≲ₙ` restricts along a deferral (`f n → ∞`): the companion of `def-lattice-arrows`'
`asympEq_comp_deferral`.
Source: mandate target 1b (`asympLE_comp_deferral`); FAF `DeferralFunction.tendsto_atTop`
Kind: L
Fidelity: n/a -/
theorem asympLE_comp_deferral {g h : ℕ → ℝ} (hle : g ≲ₙ h) (f : DeferralFunction) :
    (fun n => g (f n)) ≲ₙ (fun n => h (f n)) :=
  fun ε hε => f.tendsto_atTop.eventually (hle ε hε)

/-- `≳ₙ` restricts along a deferral.
Source: mandate target 1b (`asympGE_comp_deferral`)
Kind: L
Fidelity: n/a -/
theorem asympGE_comp_deferral {g h : ℕ → ℝ} (hge : g ≳ₙ h) (f : DeferralFunction) :
    (fun n => g (f n)) ≳ₙ (fun n => h (f n)) :=
  fun ε hε => f.tendsto_atTop.eventually (hge ε hε)

/-! ## The deferred-day endpoints (target 1b) -/

section Endpoints

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

omit [IsLogicalInductor P DP] in
/-- **The transport of an eventual member-wise world bound to the gated sequence**: a predicate
`Q` on world values that holds at `0` and, from member `N` on, at the deferred value of every
coherent valuation, holds from day `f N` on at the world value of the deferred combination
(image: the preimage is `≥ N` by strict monotonicity; off-image: the value is `0`).
Source: mandate target 1b (the tail trick at the deferred day)
Kind: L
Fidelity: n/a
Hyps: (a); `hf` -/
theorem eventually_deferredComb_of_eventually (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {c₀ : ℕ → EF} {terms : List ((ℕ → EF) × (ℕ → LUV))}
    (Q : ℝ → Prop) (hQ0 : Q 0)
    (hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → ∀ ν : LUV → ℝ,
      (∀ p ∈ terms, v.ValuesAt (p.2 n) (ν (p.2 n))) →
        Q ((c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * ν (p.2 n)).sum)) :
    ∀ᶠ m in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → ∀ ν : LUV → ℝ,
      (deferredComb f c₀ terms m).ValuesAt v ν → Q ((deferredComb f c₀ terms m).value P ν) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hval
  refine Filter.eventually_atTop.2 ⟨f.f N, fun m hm v hv ν hν => ?_⟩
  rcases deferralImageFlag_zero_or_one f m with h0 | h1
  · rw [deferredComb_value_off f c₀ terms P h0]
    exact hQ0
  · obtain ⟨k, -, hfk⟩ := (deferralImageFlag_eq_one_iff f m).1 h1
    subst hfk
    have hkN : N ≤ k := by
      by_contra hlt
      exact absurd (hf (not_le.1 hlt)) (not_lt.2 hm)
    rw [deferredComb_value_at f hf.injective]
    exact hN k hkN v hv ν (deferredComb_valuesAt_at f hf.injective hν)

/-- **Deferred-day `thm:expprovind`, `≤` face** (target 1b): for a strictly increasing deferral
`f`, generable day-`m` features `c₀, pᵢ.1` with a uniform `L¹` bound, e.c. valued members
`pᵢ.2`, and a nonnegative `c` bounding the deferred world value
`c₀(f n) + Σ pᵢ.1(f n)·ν(pᵢ.2 n)` from some member on in every completed-theory world:
`(fun n => c₀(f n) + Σ pᵢ.1(f n)·(pᵢ.2 n).expect P (f n)) ≲ₙ c`. Composition: the gated
deferred combination, `def-self-trust`'s eventual `expect_asympLE_of_eventually` on it at every
day, and restriction along `f`.
Source: mandate target 1b (`expect_deferred_le_of_eventually`); root-deference-007 Step 0
("`er` composed with a deferral"); `def-lattice-arrows` F8, F11(6); `def-self-trust` F13
Kind: C
Fidelity: exact (the deferred-day form of FAF's `lic_expect_combination_provind_le`)
Hyps: (a) — `hf : StrictlyIncreasingDeferral f` (design decision 7) -/
theorem expect_deferred_asympLE_of_eventually (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {c₀ : ℕ → EF} (hc₀ : PGenerableWeighting c₀)
    {terms : List ((ℕ → EF) × (ℕ → LUV))} (hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1)
    (hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) (hvalued : ∀ p ∈ terms, Valued DP p.2)
    {B : ℝ} (hB : 0 ≤ B)
    (hbdd : ∀ m, |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum ≤ B)
    {c : ℝ} (hc : 0 ≤ c)
    (hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → ∀ ν : LUV → ℝ,
      (∀ p ∈ terms, v.ValuesAt (p.2 n) (ν (p.2 n))) →
        (c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * ν (p.2 n)).sum ≤ c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    deferredExpect P f c₀ terms ≲ₙ (fun _ => c) := by
  have h := expect_asympLE_of_eventually (P := P) (DP := DP) (deferredCombSyntax f hc₀ hcoeff hluv)
    (deferredComb_l1Norm_le f c₀ terms P hB hbdd) (deferredComb_worldValued f c₀ terms hvalued)
    hc (eventually_deferredComb_of_eventually (P := P) f hf (fun x => x ≤ c) hc hval) hworld
  intro ε hε
  filter_upwards [f.tendsto_atTop.eventually (h ε hε)] with n hn
  rwa [deferredComb_expect_at f hf.injective] at hn

/-- **Deferred-day `thm:expprovind`, `≥` face** (target 1b): the mirror of
`expect_deferred_asympLE_of_eventually` for a nonpositive lower bound `c`.
Source: mandate target 1b (`expect_deferred_ge_of_eventually`)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem expect_deferred_asympGE_of_eventually (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {c₀ : ℕ → EF} (hc₀ : PGenerableWeighting c₀)
    {terms : List ((ℕ → EF) × (ℕ → LUV))} (hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1)
    (hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) (hvalued : ∀ p ∈ terms, Valued DP p.2)
    {B : ℝ} (hB : 0 ≤ B)
    (hbdd : ∀ m, |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum ≤ B)
    {c : ℝ} (hc : c ≤ 0)
    (hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → ∀ ν : LUV → ℝ,
      (∀ p ∈ terms, v.ValuesAt (p.2 n) (ν (p.2 n))) →
        c ≤ (c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * ν (p.2 n)).sum)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    deferredExpect P f c₀ terms ≳ₙ (fun _ => c) := by
  have h := expect_asympGE_of_eventually (P := P) (DP := DP) (deferredCombSyntax f hc₀ hcoeff hluv)
    (deferredComb_l1Norm_le f c₀ terms P hB hbdd) (deferredComb_worldValued f c₀ terms hvalued)
    hc (eventually_deferredComb_of_eventually (P := P) f hf (fun x => c ≤ x) hc hval) hworld
  intro ε hε
  filter_upwards [f.tendsto_atTop.eventually (h ε hε)] with n hn
  rwa [deferredComb_expect_at f hf.injective] at hn

/-- **Deferred-day `thm:expprovind`, two-sided at `0`** (target 1b, the `_eq` form): a deferred
combination whose world value is eventually within every `ε` of `0` has deferred-day diagonal
`≈ₙ 0`.
Source: mandate target 1b (`expect_deferred_eq_of_eventually`)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem expect_deferred_asympEq_zero_of_eventually_abs_le (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {c₀ : ℕ → EF} (hc₀ : PGenerableWeighting c₀)
    {terms : List ((ℕ → EF) × (ℕ → LUV))} (hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1)
    (hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) (hvalued : ∀ p ∈ terms, Valued DP p.2)
    {B : ℝ} (hB : 0 ≤ B)
    (hbdd : ∀ m, |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum ≤ B)
    (hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν : LUV → ℝ, (∀ p ∈ terms, v.ValuesAt (p.2 n) (ν (p.2 n))) →
        |(c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * ν (p.2 n)).sum| ≤ ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    deferredExpect P f c₀ terms ≈ₙ (fun _ => (0 : ℝ)) := by
  have h := expect_asympEq_zero_of_eventually_abs_le (P := P) (DP := DP)
    (deferredCombSyntax f hc₀ hcoeff hluv) (deferredComb_l1Norm_le f c₀ terms P hB hbdd)
    (deferredComb_worldValued f c₀ terms hvalued)
    (fun ε hε => eventually_deferredComb_of_eventually (P := P) f hf (fun x => |x| ≤ ε)
      (by simpa using hε.le) (hval ε hε)) hworld
  have h' := asympEq_comp_deferral h f
  refine (tendsto_congr (fun n => ?_)).mp h'
  simp only [deferredComb_expect_at f hf.injective]

/-- **The slack form**: a deferred combination valued within a vanishing `slack n` of `0` at
every member has deferred-day diagonal `≈ₙ 0` — the shape every quote package's
`slack`/`slack_tendsto` delivers.
Source: mandate target 1b (the slack form)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem expect_deferred_asympEq_zero_of_slack (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {c₀ : ℕ → EF} (hc₀ : PGenerableWeighting c₀)
    {terms : List ((ℕ → EF) × (ℕ → LUV))} (hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1)
    (hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) (hvalued : ∀ p ∈ terms, Valued DP p.2)
    {B : ℝ} (hB : 0 ≤ B)
    (hbdd : ∀ m, |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum ≤ B)
    (slack : ℕ → ℝ) (hslack : Tendsto slack atTop (𝓝 0))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ ν : LUV → ℝ,
      (∀ p ∈ terms, v.ValuesAt (p.2 n) (ν (p.2 n))) →
        |(c₀ (f n)).denote P + (terms.map fun p => (p.1 (f n)).denote P * ν (p.2 n)).sum| ≤
          slack n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    deferredExpect P f c₀ terms ≈ₙ (fun _ => (0 : ℝ)) := by
  refine expect_deferred_asympEq_zero_of_eventually_abs_le f hf hc₀ hcoeff hluv hvalued hB hbdd
    (fun ε hε => ?_) hworld
  filter_upwards [(tendsto_order.1 hslack).2 ε hε] with n hn v hv ν hν
  exact (hval n v hv ν hν).trans hn.le

end Endpoints

/-- Target 1 at `succDeferral` over an arbitrary inductor: no binder left unwitnessed (the
non-vacuity witness on a non-decided family is `Witness.lean`'s).
Source: mandate design decision 7
Kind: L
Fidelity: n/a -/
example {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) (hv : Valued DP X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν : LUV → ℝ, v.ValuesAt (X n) (ν (X n)) → |ν (X n) - 1 / 2| ≤ ε) :
    deferredExpect P succDeferral (fun _ => EF.const (-1 / 2)) [(fun _ => EF.const 1, X)] ≈ₙ
      (fun _ => (0 : ℝ)) :=
  expect_deferred_asympEq_zero_of_eventually_abs_le succDeferral succDeferral_strict
    (constWeighting _) (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact constWeighting _)
    (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hX)
    (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hv)
    (B := 2) (by norm_num) (fun m => by norm_num)
    (fun ε hε => by
      filter_upwards [hval ε hε] with n hn v hv ν hν
      have := hn v hv ν (hν _ (List.mem_singleton_self _))
      have e : ((EF.const (-1 / 2 : ℚ)).denote P) + (((EF.const (1 : ℚ)).denote P) * ν (X n) + 0) =
          ν (X n) - 1 / 2 := by simp; ring
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e]
      exact this) hworld

end

end Cleanroom.Deference.DefSqueezeDiamond
