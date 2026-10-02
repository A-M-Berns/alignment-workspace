import Cleanroom.Deference.DefSqueezeDiamond.SelfPins
import Cleanroom.Deference.DefLatticeArrows.OneWay
import Cleanroom.Deference.DefLatticeArrows.Witness
import Cleanroom.Deference.DefLatticeArrows.WideBand
import Cleanroom.Deference.DefLatticeArrows.ArgmaxValue
import Cleanroom.Found.LiQuoteLane.PaperQuotation

/-!
# `def-squeeze-diamond` · PaperExpert: the paper's inductor as the expert of any extending novice
(targets 4a–4b) and the self-expert's arrow inputs discharged (target 2e)

**One-way** (plan §0.4 rule 1): the novice `H` lives over a process `DPH` whose consistent
worlds are `paperDP T`-consistent (`ExtendsBase DPH T`, design decision 4 — inhabited by
`paperDP T` itself and by every `ledgerProcess (paperDP T) a e` of li-quote-lane); the expert
`A := liaHistory (paperDP T)` never reads `H`. `paperExpert T f DPH : Expert DPH` is the
expert; at `DPH := paperDP T` it is `Expert.self` (`paperExpert_paperDP`, `rfl`), so the
self-case is the diagonal of this family.

**Why "`H` reads `A`'s quotes through arithmetic" is one line.** FAF's quote codes over
`paperDP T` are reflected in every `paperDP T`-consistent world, hence in every `DPH`-world:
the packages (a) are FAF's own objects — `paperDeferredExpectationQuoteCode` (the quotes,
`QuotesAvailable`), `estW`/`estXW` and the below-face twins of `def-self-trust` (the ramp
`WeightQuote`s, slack `1/(n+1)`), the band weight of `SelfPins` quoted the same way
(`paperBandQuote`), and their products quoted again (`ProductQuotesAvailable`,
`CondQuotesReflected`). The ramp and band packages need the source **valued over the expert's
process** (`Valued (paperDP T) X`): FAF's mesh product is reflected only where the source is
valued, and the expert can be pinned or folded only on bets its own theory values (design
decision 4). The gap and probe packages are the one new construction and are **not** built
here (see the report: `GapQuote` for the paper expert is left as a disclosed clause).

**Target 2e.** With `SelfPins`'s folds, the arrows' self-instances close with no `(b)` left:
`softTotalTrustAbove/Below_self`, `totalTrust_self_via_arrows` (a consistency check against
`def-self-trust`'s `selfTotalTrust`), `condTower_self_via_arrows`, `bandReflection_self`, and
`squeeze_self_of_gapQuotes`: given the two gap quotes of an e.c. valued source as data, every
other input of `tower_instance_of_totalTrust_gapBets` is a theorem for the self-expert (the
pins by `selfPinGap`, the ramp packages by `paperRampQuote`, the TT instances by `selfTotalTrust`).
Construction-facing.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## The novice's process extends the expert's -/

/-- **`DPH` extends the paper's process**: every completed-theory world of `DPH` is a
completed-theory world of `paperDP T`. This is all that "`H` reads `A`'s arithmetic quotes"
needs: every FAF quote code over `paperDP T` is then reflected in `DPH`'s worlds.
Source: mandate design decision 4
Kind: D
Fidelity: exact -/
def ExtendsBase (DPH : DeductiveProcess) : Prop :=
  ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory (paperDP T)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The paper's process extends itself (the self-case diagonal).
Source: mandate design decision 4
Kind: L
Fidelity: n/a -/
theorem extendsBase_self : ExtendsBase T (paperDP T) := fun _ hv => hv

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- Every ledger process over `paperDP T` extends it (li-quote-lane's
`consistentWithTheory_base_of_ledger`): the distinct novice of target 4d.
Source: mandate design decision 4; li-quote-lane `consistentWithTheory_base_of_ledger`
Kind: L
Fidelity: n/a -/
theorem extendsBase_ledger (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ExtendsBase T (ledgerProcess (paperDP T) a e) :=
  fun _ hv => consistentWithTheory_base_of_ledger hv

/-! ## The paper expert -/

/-- **The paper's inductor as the expert of a novice over `DPH`** (one-way): history
`liaHistory (paperDP T)`, deferral `f`, range from the inductor instance.
Source: mandate target 4a; root-deference-009 ("observable, coherent, introspective experts")
Kind: D
Fidelity: exact -/
def paperExpert (f : DeferralFunction) (DPH : DeductiveProcess) : Expert DPH :=
  ⟨liaHistory (paperDP T), f, fun n s => paper_price_mem_Icc T n s⟩

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The paper expert's history is the paper's inductor.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem paperExpert_A (f : DeferralFunction) (DPH : DeductiveProcess) :
    (paperExpert T f DPH).A = liaHistory (paperDP T) := rfl

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The paper expert's deferral is `f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem paperExpert_f (f : DeferralFunction) (DPH : DeductiveProcess) :
    (paperExpert T f DPH).f = f := rfl

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The paper expert's estimate is the deferred-day expectation on the paper's inductor.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem paperExpert_estimate (f : DeferralFunction) (DPH : DeductiveProcess)
    (X : ℕ → LUV) (n : ℕ) :
    (paperExpert T f DPH).estimate X n = (X n).expect (liaHistory (paperDP T)) (f n) := rfl

/-- **The self-case is the diagonal of the family**: at `DPH := paperDP T` the paper expert is
`Expert.self` (definitionally).
Source: mandate target 4a
Kind: L
Fidelity: exact -/
theorem paperExpert_paperDP (f : DeferralFunction) :
    paperExpert T f (paperDP T) = Expert.self (liaHistory (paperDP T)) (paperDP T) f := rfl

/-! ## 4b — the packages, (a) -/

section Packages

variable (f : DeferralFunction) {DPH : DeductiveProcess}

/-- **Quotes exist for the paper expert over any extending novice** (a): FAF's
`paperDeferredExpectationQuoteCode`, reflected in `paperDP T`-worlds hence in `DPH`-worlds.
Source: mandate target 4b (`QuotesAvailable`); `def-lattice-arrows` `closedQuote_reflects`
Kind: C
Fidelity: exact
Hyps: (a); `hext` -/
theorem paperExpert_quotesAvailable (hext : ExtendsBase T DPH) :
    QuotesAvailable DPH (paperExpert T f DPH) := by
  intro X hX
  exact ⟨(paperDeferredExpectationQuoteCode T f X hX).luv,
    (paperDeferredExpectationQuoteCode T f X hX).poly,
    fun n v hv => deferredExpectationQuote_reflected T f X hX n v (hext v hv)⟩

/-- **Product quotes exist** at every weight function (a): the product LUV of any `WeightQuote`
is e.c., so `paperExpert_quotesAvailable` quotes it.
Source: mandate target 4b (`ProductQuotesAvailable`)
Kind: L
Fidelity: exact
Hyps: (a); `hext` -/
theorem paperExpert_productQuotesAvailable (hext : ExtendsBase T DPH) (wt : ℝ → ℝ) :
    ProductQuotesAvailable DPH (paperExpert T f DPH) wt :=
  fun _ _ XW _ q => paperExpert_quotesAvailable T f hext XW q.product_codes

/-- **Left-product quotes of conditional packages exist** (a).
Source: mandate target 4b (`CondQuotesReflected`)
Kind: L
Fidelity: exact
Hyps: (a); `hext` -/
theorem paperExpert_condQuotesReflected (hext : ExtendsBase T DPH) :
    CondQuotesReflected DPH (paperExpert T f DPH) :=
  fun _ _ Z _ _ q => paperExpert_quotesAvailable T f hext Z q.left_codes

/-- **The above-ramp `WeightQuote` for the paper expert** on a source valued over `paperDP T`:
`def-self-trust`'s `estW`/`estXW` (FAF's deferred-weight quote and mesh product), reflected in
`DPH`-worlds through `hext`; slack `1/(n+1)`.
Source: mandate target 4b (`RampQuotesAvailable`); `def-self-trust` `Est.lean`
Kind: D
Fidelity: variant: product within FAF's `1/(n+1)` slack -/
def paperRampQuote (hext : ExtendsBase T DPH) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hXv : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ)
    (s : ℚ) :
    WeightQuote DPH (paperExpert T f DPH) X (rampAbove δ s) (estW T f hX hδ s)
      (estXW T f hX hδ s) where
  weight_codes := (paperDeferredWeightQuoteCode T f _ _ _).poly
  product_codes := meshProductLUV_machineThresholdCodeSeq _ hX
  slack := fun n => 1 / ((n : ℝ) + 1)
  slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  source_valued := fun n v hv => hXv n v (hext v hv)
  weight_reflected := fun n v hv => estW_reflected T f hinj hX hδ s n v (hext v hv)
  product_reflected := fun n v hv _ hx => estXW_reflected T f hinj hX hδ s n v (hext v hv) hx

/-- **The below-ramp `WeightQuote` for the paper expert**, likewise.
Source: mandate target 4b
Kind: D
Fidelity: variant: product within FAF's `1/(n+1)` slack -/
def paperRampQuoteBelow (hext : ExtendsBase T DPH) (hinj : Function.Injective f.f)
    {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hXv : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ)
    (s : ℚ) :
    WeightQuote DPH (paperExpert T f DPH) X (rampBelow δ s) (estWBelow T f hX hδ s)
      (estXWBelow T f hX hδ s) where
  weight_codes := (paperDeferredWeightQuoteCode T f _ _ _).poly
  product_codes := meshProductLUV_machineThresholdCodeSeq _ hX
  slack := fun n => 1 / ((n : ℝ) + 1)
  slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  source_valued := fun n v hv => hXv n v (hext v hv)
  weight_reflected := fun n v hv => estWBelow_reflected T f hinj hX hδ s n v (hext v hv)
  product_reflected := fun n v hv _ hx =>
    estXWBelow_reflected T f hinj hX hδ s n v (hext v hv) hx

/-- **Ramp quotes exist for the paper expert** on every e.c. source valued over `paperDP T`
(a) — the clause `RampQuotesAvailable` of the arrows, discharged.
Source: mandate target 4b (`RampQuotesAvailable`)
Kind: C
Fidelity: exact (existence; the quotes within FAF's slack)
Hyps: (a); `hext`, `hinj`; `hXv : Valued (paperDP T) X` (design decision 4) -/
theorem paperExpert_rampQuotesAvailable (hext : ExtendsBase T DPH) (hinj : Function.Injective f.f)
    {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hXv : Valued (paperDP T) X) :
    RampQuotesAvailable DPH (paperExpert T f DPH) X :=
  fun _ _ hδ => ⟨_, _, ⟨paperRampQuote T f hext hinj hX hXv hδ _⟩⟩

/-- **The band `WeightQuote` for the paper expert**: `SelfPins`'s generable `bandWeight` quoted by
FAF's `paperDeferredWeightQuoteCode`, its product by `meshProductLUV`.
Source: mandate target 4b (`BandQuotesAvailable`)
Kind: D
Fidelity: variant: product within FAF's `1/(n+1)` slack -/
def paperBandQuote (hext : ExtendsBase T DPH) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hXv : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ)
    (s ε : ℚ) :
    WeightQuote DPH (paperExpert T f DPH) X (bandWt δ s ε)
      ((paperDeferredWeightQuoteCode T f (bandWeight T f X δ s ε)
        (bandWeight_pgenerable T f hX hδ s ε) (bandWeight_mem T f X δ s ε)).luv)
      (meshProductLUV (paperDeferredWeightQuoteCode T f (bandWeight T f X δ s ε)
        (bandWeight_pgenerable T f hX hδ s ε) (bandWeight_mem T f X δ s ε)) X) where
  weight_codes := (paperDeferredWeightQuoteCode T f _ _ _).poly
  product_codes := meshProductLUV_machineThresholdCodeSeq _ hX
  slack := fun n => 1 / ((n : ℝ) + 1)
  slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  source_valued := fun n v hv => hXv n v (hext v hv)
  weight_reflected := fun n v hv => by
    have h := deferredWeightQuote_reflected T f (bandWeight T f X δ s ε)
      (bandWeight_pgenerable T f hX hδ s ε) (bandWeight_mem T f X δ s ε) n v (hext v hv)
    rwa [bandWeight_at_cast T f hinj] at h
  product_reflected := fun n v hv _ hx => by
    have h := meshProduct_reflected T f X (bandWeight T f X δ s ε)
      (bandWeight_pgenerable T f hX hδ s ε) (bandWeight_mem T f X δ s ε) n v (hext v hv) hx
    rwa [bandWeight_at_cast T f hinj] at h

end Packages

/-! ## 2e — the self-expert's arrow inputs are theorems -/

/-- **Soft Total Trust above, for the self-expert, through the arrow** (a): `def-lattice-arrows`'
`softTotalTrustAbove_self_of_folds` with its `(b)` fold discharged by `selfFoldsAt_rampAbove`.
Not an arrow row (design decision 1: both sides are theorems for the self-expert); it records
that T4's self-instance has no hypothesis left.
Source: mandate target 2e; `def-lattice-arrows` `softTotalTrustAbove_self_of_folds`
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem softTotalTrustAbove_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    SoftTotalTrustAbove (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) s δ :=
  softTotalTrustAbove_self_of_folds T f hδ (selfFoldsAt_rampAbove T f hf s hδ)

/-- **Soft Total Trust below, for the self-expert, through the arrow** (a).
Source: mandate target 2e; `def-lattice-arrows` `softTotalTrustBelow_self_of_folds`
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem softTotalTrustBelow_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    SoftTotalTrustBelow (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) s δ :=
  softTotalTrustBelow_self_of_folds T f hδ (selfFoldsAt_rampBelow T f hf s hδ)

/-- **Total Trust for the self-expert, through Tower ⟹ TT** (a) — a consistency check of the
arrows against `def-self-trust`'s `selfTotalTrust` (`est`), which proves the same predicate
directly from `thm:ccee`; here it is `towerValued_self` + the product quotes + the folds.
Source: mandate target 2e; `def-lattice-arrows` `totalTrust_of_towerValued`
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem totalTrust_self_via_arrows (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    TotalTrust (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  totalTrust_of_towerValued (towerValued_self T f)
    (fun _ _ _ => ⟨productQuotesAvailable_of_marketComputation T _ (paperMarketComputation T) _,
      productQuotesAvailable_of_marketComputation T _ (paperMarketComputation T) _⟩)
    (selfFoldsAt_ramps T f hf) (paperDP_hworld T)

/-- **The conditional tower for the self-expert, through the arrow** (a): `def-lattice-arrows`'
`condTower_self_of_folds` with the generable-weight fold (`selfFoldsCondOver`) in place of the
unrestricted `(b)` fold, through `condTower_of_towerValued_over`. A consistency check against
`def-self-trust`'s `selfCondTower`.
Source: mandate target 2e; finding F2
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem condTower_self_via_arrows (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    CondTower (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  condTower_of_towerValued_over (towerValued_self T f)
    (condQuotesReflected_of_marketComputation T _ (paperMarketComputation T))
    (selfFoldsCondOver T f hf) (paperDP_hworld T)

/-- **Band Reflection for the self-expert** (a): `bandReflection_of_towerValued` with the band
folds `selfFoldsAt_band` — the value form of Reflection toward the future self at every band,
with no hypothesis.
Source: mandate target 2e; [[reflection-in-li]] §The value form is a theorem;
`def-lattice-arrows` `bandReflection_of_towerValued`
Kind: C
Fidelity: exact (unnormalized band form)
Hyps: (a); `hf` -/
theorem bandReflection_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    BandReflection (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  bandReflection_of_towerValued (towerValued_self T f)
    (fun _ _ _ _ _ => productQuotesAvailable_of_marketComputation T _ (paperMarketComputation T) _)
    (selfFoldsAt_band T f hf) (paperDP_hworld T)

/-- **The squeeze's inputs are all theorems for the self-expert** (target 2e; root-007's
Step 0 discharged): given the two gap quotes of an e.c. valued source `Z` with e.c. quote `Y`
as *data*, `tower_instance_of_totalTrust_gapBets`'s every other input is (a) — the pins by
`selfPinGap`, the ramp packages at thresholds `½ − ε` by `paperRampQuote` (on the gap LUVs,
valued by `GapQuote.gap_valued`), their soft-TT instances by `def-self-trust`'s
`selfTotalTrust` — and the Tower instance `E_n(Z_n) ≈ₙ E_n(Y_n)` follows. (For the self-expert
the conclusion is also `towerValued_self` directly; this is the squeeze *run*, not a new
vertex — design decision 1.)
Source: mandate target 2e; [[centered-bet-squeeze]] §2; [[total-trust-implies-mart]] ⚠
Kind: C
Fidelity: exact (rescaled gap; asymptotic pins)
Hyps: (a) given the gap quotes `qP`, `qM` (data; their existence for the self-expert is the
gap-LUV construction, not built here — report §4b); `hf` -/
theorem squeeze_self_of_gapQuotes (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {Z Y G G' : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) (hY : LUV.MachineThresholdCodeSeq Y)
    (qP : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z Y 1 G)
    (qM : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z Y (-1) G') :
    (fun n => (Z n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (Y n).expect (liaHistory (paperDP T)) n) := by
  have hTT := selfTotalTrust T f hf.injective
  refine tower_instance_of_totalTrust_gapBets hZ hY qP qM (selfPinGap T f hf (Or.inl rfl) hZ qP)
    (selfPinGap T f hf (Or.inr rfl) hZ qM)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩) (paperDP_hworld T)
  · have hδ : (0 : ℚ) < ε / 2 := by positivity
    exact ⟨_, _, paperRampQuote T f (extendsBase_self T) hf.injective qP.codes qP.gap_valued
      hδ (1 / 2 - ε),
      hTT.above _ _ (1 / 2 - ε) (ε / 2) hδ G _ _ qP.codes
        (paperRampQuote T f (extendsBase_self T) hf.injective qP.codes qP.gap_valued
          hδ (1 / 2 - ε))⟩
  · have hδ : (0 : ℚ) < ε / 2 := by positivity
    exact ⟨_, _, paperRampQuote T f (extendsBase_self T) hf.injective qM.codes qM.gap_valued
      hδ (1 / 2 - ε),
      hTT.above _ _ (1 / 2 - ε) (ε / 2) hδ G' _ _ qM.codes
        (paperRampQuote T f (extendsBase_self T) hf.injective qM.codes qM.gap_valued
          hδ (1 / 2 - ε))⟩

/-- Target 4b over `𝗣𝗔` at `succDeferral`, with the ledger novice of li-quote-lane: no binder
left unwitnessed.
Source: mandate design decision 7
Kind: L
Fidelity: n/a -/
example (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    QuotesAvailable (ledgerProcess (paperDP 𝗣𝗔) a e)
      (paperExpert 𝗣𝗔 succDeferral (ledgerProcess (paperDP 𝗣𝗔) a e)) :=
  paperExpert_quotesAvailable 𝗣𝗔 succDeferral (extendsBase_ledger 𝗣𝗔 a e)

end

end Cleanroom.Deference.DefSqueezeDiamond
