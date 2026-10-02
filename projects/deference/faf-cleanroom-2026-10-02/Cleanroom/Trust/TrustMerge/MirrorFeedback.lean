import Cleanroom.Trust.TrustMerge.SelfInstance
import Cleanroom.Found.LiQuoteLane.MirrorPair
import Cleanroom.Found.LiQuoteLane.PaperQuotation
import Cleanroom.Found.LiAsympCalc.WeightedAverage

/-!
# `trust-merge` · MirrorFeedback: Prop A over the mirror ledger (T3)

**The first distinct-inductor instance of cross-agent LUV-Total-Trust** (trust-lab-2-007
repaired; trust-lab-012; [[merging-inductors-model]] §(a.2) Prop A). Setting (`li-quote-lane`'s
mirror pair, `MirrorPair.lean`): `H` is any market with a `MarketComputation M` (e.g. FAF's
`paperMarketComputation`), `X` an e.c. source family, `f` a deferral function, and `A`'s process
`DPA := ledgerProcess base (realizedExpectation M X f) σ` records `H`'s **realized** day-`f n`
expectation `𝔼^H_{f n}(X n)` (FAF's exact rational `M.expectQuoteAt X n (f n)`) as decided ledger
literals at the schedule `σ`. The expert is `H` read at the deferred day, as an `Expert DPA`
(`mirrorExpert`), and its quote in `A`'s language is `ledgerLuv 0`.

**Route A (primary, closed).** `luv_wubexp_ofComputation` applies **verbatim**: in `A`'s process
the ledger LUV *is* theory-determined at `H`'s realized expectation
(`crossQuotePackage_mirror`'s `reflected`, i.e. `ledgerLuv_determinedViaTheory`), so the
red-team's objection to the model — "`H`'s price is not a Γ-determined value" (trust-lab-2-007,
A1) — is dissolved by construction: in `A`'s *ledger-augmented* theory it is. What remains is the
deadline program `C` (`FeedbackTruthComputation`), the paper's "`μ_t` computable in `O(f(t+1))`"
— a **time** hypothesis on the expert's estimate, *not* a determinacy hypothesis (the red-team's
distinction, kept). **What `C` asks here is doubly deferred** (audit r1 B2; the lemmas
`deadline_value_at`, `ledger_truth_double_deferral`, `deadline_le_realized` below): its `k`-th
value is the mesh truth of the ledger quote at day `f k`, due on the input `⟨k, f (k+1)⟩`; the
determined value of the day-`f k` ledger quote is `H`'s expectation at day `f (f k)`; and
`f (k+1) ≤ f (f k)` for every strictly increasing `f`. So `C` demands `H`'s day-`f (f k)`
expectation within FAF's `MachineDigits` budget on `⟨k, f (k+1)⟩`, where the realized day never
precedes the deadline and recedes from it as `f` grows — inhabitable only if `H`'s day-`m`
expectations of the family are computable in time polynomial in `m` along those days, a property
of `H`'s running time that no choice of `f` relaxes. The agenda's "fast enough `f`" and the
mandate's "`f (k+1) ≥ τ(f k)` does it" describe a different hypothesis (F-C, F-A′). FAF does not
bound the LIA's running time (`SelfInstance.lean`'s module docstring; findings F-C); `C` is the
one named hypothesis, carried as (b) at the mandate's instruction though it is a hypothesis of
the cited theorem rather than a cited result, and **no instance of it is exhibited**: the N+
grade of the rows below is for the market data (two distinct markets), not for the full
hypothesis package, which no witness inhabits.

**Route B (secondary, the lab's reroute; per-threshold instance closed).** For a *fixed* rational
`q`, `lic_wub_ofComputation` on the decided sentence `⌜α_{0,i} > q⌝` gives `w`-unbiasedness of
`A`'s price of each threshold for its truth `1[q < 𝔼^H_{f i}(X i)]`
(`mirror_threshold_unbiased`). FAF's expectation is the Riemann sum over the day-`i` grid
`j/(i+1)` (`ledgerLuv_expect_grid`), so "integrate over thresholds" is a definition — but the
grid's thresholds **vary with the day**, so Route B's fixed-`q` instances do not assemble into the
expectation without a uniformity step. Over the ledger that step is unnecessary (Route A lands);
Route B's residual is findings F-B, not an OPEN.

**Scope: one-way (`A` reads `H`).** Nothing here says `H` endorses anything; two mirror one-way
pairs do not make a two-way pair (`MirrorPair.lean`). Grade: averaged. Weight class:
`A`-generable (a weight defined from `H`'s prices is not a `PGenerableWeighting` of `A` unless it
reads them through ledger atoms). The scope clause — the ledger literal for day `n` is absent
before stage `(σ 0).e n`, so `A`'s day-`n` price is a forecast when `n < (σ 0).e n` — is
`ledgerLuv_absent_before_payout`; the mandate's publication condition `(σ 0).e n ≥ f n` is the
instance `σ := fun _ => f.toPublicationSchedule`, at which `mirror_feedback_unbiased_lia_forecast`
pins the N+ instance (the theorems hold for every `σ`, and are strongest at late schedules; at an
early one `A`'s day-`n` price is a lookup of a decided atom — audit r1 N1/N3).
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction LogicalInduction.FeedbackTruth LO.Propositional Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Found.LiQuoteLane
open Cleanroom.Bli.BliFound Cleanroom.Deference.DefSelfTrust

noncomputable section

/-! ## The mirror expert and its quote -/

/-- **The mirror expert**: `H` read at the deferred day `f n`, as a `def-lattice` `Expert` over
`A`'s process `DPA`; its estimate is `𝔼^H_{f n}(X n)` (`Expert.estimate`), the range from `H`'s
market certificate. Direction: one-way (`A` reads `H`).
Source: [[merging-inductors-model]] §0 (`μ_t := ℙ^H_{f(t)}(φ_t)`, the realized human future
price); mandate T3
Kind: D
Fidelity: exact
Hyps: n/a -/
def mirrorExpert {H : History} (M : MarketComputation H) (f : DeferralFunction)
    (DPA : DeductiveProcess) : Expert DPA :=
  ⟨H, f, M.price_mem_Icc⟩

/-- `A`'s process of the mirror pair: `H`'s realized day-`f n` expectations of `X n` recorded
as decided ledger literals over `base` at the schedule `σ` (`li-quote-lane`'s
`ledgerProcess base (realizedExpectation M X f) σ`).
Source: mandate T3; `li-quote-lane` `MirrorPair.lean`
Kind: D
Fidelity: exact -/
abbrev mirrorProcess {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (base : DeductiveProcess) (σ : ℕ → PublicationSchedule) :
    DeductiveProcess :=
  ledgerProcess base (realizedExpectation M X f) σ

/-- The mirror table cast to the reals is `H`'s realized expectation (FAF's `expectQuoteAt_cast`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem realizedExpectation_cast {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (j n : ℕ) :
    ((realizedExpectation M X f j n : ℚ) : ℝ) = (X n).expect H (f.f n) :=
  (M.expectQuoteAt_cast X n (f.f n)).symm

/-- **The ledger quote reflects the mirror expert's estimate** — `Reflects DPA (mirrorExpert M f
DPA) X (ledgerLuv 0)` is `crossQuotePackage_mirror`'s `reflected` field: every completed-theory
world of `A`'s ledger process values `α_{0,n}` at `𝔼^H_{f n}(X n)`. This is the determinacy
input the red-team said the model lacked, now a theorem over the ledger.
Source: trust-lab-2-007 (the repair: determinacy by construction); `li-quote-lane`
`crossQuotePackage_mirror` (T2.4)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mirrorExpert_reflects {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (base : DeductiveProcess) (σ : ℕ → PublicationSchedule) :
    Reflects (mirrorProcess M X f base σ) (mirrorExpert M f (mirrorProcess M X f base σ)) X
      (fun n => ledgerLuv 0 n) :=
  fun n v hv => (crossQuotePackage_mirror M X f base σ).reflected n v hv

/-! ## Transfer between reflecting quotes -/

/-- **Unbiasedness transfers between two e.c. quotes of the same estimate**: if `P`'s expectation
of `Y₀` is `w`-unbiased for `E*(X)` and `Y` is another e.c. quote reflecting `E*(X)`, so is
`P`'s expectation of `Y`. Per day `𝔼^P_n(Y_n) ≈ₙ 𝔼^P_n(Y₀_n)` (`thm:expprovind` through
`def-self-trust`'s `expect_asympEq_of_reflected_exact`), and a per-day vanishing difference
averages to `0` under any nonnegative divergent weighting (`li-asymp-calc`).
Source: mandate T3 (the N+ instance of T1 on the quoted family); `def-self-trust`
`expect_asympEq_of_reflected_exact`; `li-asymp-calc` `WeightedApprox.trans`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem quoteUnbiased_transfer {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (E : Expert DP) {X Y₀ Y : ℕ → LUV} (h₀ : LUV.MachineThresholdCodeSeq Y₀)
    (hY : LUV.MachineThresholdCodeSeq Y) (hR₀ : Reflects DP E X Y₀) (hR : Reflects DP E X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hu : QuoteUnbiased P DP E X Y₀) : QuoteUnbiased P DP E X Y := by
  intro W hW hWdiv hsupp
  have h₀' := hu W hW hWdiv hsupp
  have hpd : (fun n => (Y n).expect P n) ≈ₙ (fun n => (Y₀ n).expect P n) :=
    expect_asympEq_of_reflected_exact hY h₀ (fun n _ => E.estimate X n)
      (fun n v hv => hR n v hv) (fun n v hv => hR₀ n v hv) hworld
  have hw0 : ∀ i, 0 ≤ (W i).denote P := fun i => (hWdiv.1 i).1
  have h1 : WeightedApprox (fun i => (W i).denote P) (fun n => (Y n).expect P n)
      (fun n => (Y₀ n).expect P n) :=
    weightedApprox_of_tendsto_zero hw0 hWdiv.2 hpd
  have h2 : WeightedApprox (fun i => (W i).denote P) (fun n => (Y₀ n).expect P n)
      (fun i => E.estimate X i) := by
    rw [weightedApprox_iff_weightedBias]
    simpa only [AsympEq, sub_zero] using h₀'
  have h3 := WeightedApprox.trans hWdiv.2 h1 h2
  rw [weightedApprox_iff_weightedBias] at h3
  simpa only [AsympEq, sub_zero] using h3

/-! ## T3, Route A — Prop A over the mirror ledger -/

/-- **T3 (headline). Prop A over the mirror ledger, Route A:** for any inductor `A` over the
mirror process (with a consistent world at every stage) and any deadline program `C` for the
ledger quote along `f`, `A`'s day-`i` expectation of the ledger LUV naming `𝔼^H_{f i}(X i)` is
`w`-unbiased for it along every `A`-generable divergent weighting supported on `im f`:
`QuoteUnbiased A DPA (mirrorExpert M f DPA) X (ledgerLuv 0)`, i.e.
`weightedBias (fun i => (W i).denote A) (fun i => (ledgerLuv 0 i).expect A i) (fun i => (X i).expect H (f i)) ≈ₙ 0`.
FAF's `luv_wubexp_ofComputation` verbatim (`quoteUnbiased_ofComputation`), with `hdet` the
ledger's determinacy (`mirrorExpert_reflects`): the model's "determined via Γ" is supplied by
`A`'s ledger-augmented theory, not assumed. **`C` is a time hypothesis, not a determinacy
hypothesis** — the doubly deferred deadline program of `thm:wubexp` (module docstring, F-C),
inhabited nowhere in this package. Grade: averaged. Direction: one-way (`A` reads `H`). Weight
class: `A`-generable.
Source: [[merging-inductors-model]] §(a.2) Prop A ("`A` is `w`-unbiased about `H`'s realized
future price"); trust-lab-2-007 (the substitution dissolved over the ledger); trust-lab-012;
root-deference-061 (the first distinct-inductor instance)
Kind: C
Fidelity: variant: ledger-recorded determinacy in place of `Γ_A`-provable determinacy (as
`MirrorPair.lean` discloses); the quote is the ledger LUV
Hyps: (b) `C` — FAF's `FeedbackTruthComputation` for the normalized mesh truth of the ledger
quote along `f`: an undischarged hypothesis of `thm:wubexp`, not a cited result; it asks for
`H`'s day-`f (f k)` expectation by the deadline `f (k+1) ≤ f (f k)` (F-C), and no instance is
exhibited; all else (a) -/
theorem mirror_feedback_unbiased {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f) (base : DeductiveProcess)
    (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (mirrorProcess M X f base σ)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f base σ).D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A
        (mirrorProcess M X f base σ) hworld 1) f) :
    QuoteUnbiased A (mirrorProcess M X f base σ) (mirrorExpert M f (mirrorProcess M X f base σ))
      X (fun n => ledgerLuv 0 n) :=
  quoteUnbiased_ofComputation _ X _ (ledgerLuv_thresholdCodes 0)
    (mirrorExpert_reflects M X f base σ) hstrict hworld C

/-- **T3 in the mandate's display**: `weightedBias (W·A) (𝔼^A_i(α_{0,i})) (𝔼^H_{f i}(X i)) ≈ₙ 0`
for every `A`-generable divergent weighting supported on `im f`. `mirror_feedback_unbiased`
unfolded.
Source: mandate T3 (statement)
Kind: L
Fidelity: exact
Hyps: (b) `C` (undischarged, doubly deferred, F-C); all else (a) -/
theorem mirror_feedback_unbiased_display {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f) (base : DeductiveProcess)
    (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (mirrorProcess M X f base σ)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f base σ).D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A
        (mirrorProcess M X f base σ) hworld 1) f)
    (W : ℕ → EF) (hW : PGenerableWeighting W) (hWdiv : DivergentWeighting W A)
    (hsupp : WeightingSupportedOnDeferralImage W A f) :
    weightedBias (fun i => (W i).denote A) (fun i => (ledgerLuv 0 i).expect A i)
      (fun i => (X i).expect H (f.f i)) ≈ₙ (fun _ => (0 : ℝ)) :=
  mirror_feedback_unbiased M X f hstrict base σ A hworld C W hW hWdiv hsupp

/-- **T3 at the LIA (N+ for the market data of T1):** `A := liaHistory` over the mirror process
is an inductor over it (`mirrorPair_inductor`), every stage of the mirror process has a world
when the base has one and is free of the ledger's atoms (`ledgerProcess_hworld`), so Prop A holds
for FAF's constructed inductor watching any computable-market `H`. Two distinct markets inside
the statement: `H` (any `MarketComputation`) and `liaHistory DPA`. **Witness grade** (audit r1
B2): this discharges the inductor and `hworld`, **not `C`** — no term of `C`'s type is produced
for any `H`, `f`, `X`, so no witness inhabits the full hypothesis package; the N+ is for the
market data only. The schedule `σ` is arbitrary here; the forecast instance
`σ := fun _ => f.toPublicationSchedule` (the mandate's `(σ 0).e n ≥ f n`) is
`mirror_feedback_unbiased_lia_forecast`.
Grade: averaged. Direction: one-way (`A` reads `H`). Weight class: `A`-generable.
Source: mandate T3 (the N+ instance); `li-quote-lane` `mirrorPair_inductor`; audit r1 B2/N1
Kind: C
Fidelity: variant: as `mirror_feedback_unbiased`; plain trader class
Hyps: (b) `C` (undischarged, doubly deferred, no instance; F-C); all else (a) -/
theorem mirror_feedback_unbiased_lia {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f) (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (σ : ℕ → PublicationSchedule)
    (hσ : Computable fun p : ℕ × ℕ => (σ p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (realizedExpectation M X f) σ) base)
    (hbaseworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n))
        (liaHistory (mirrorProcess M X f base σ)) (mirrorProcess M X f base σ)
        (ledgerProcess_hworld hfree hbaseworld) 1) f) :
    QuoteUnbiased (liaHistory (mirrorProcess M X f base σ)) (mirrorProcess M X f base σ)
      (mirrorExpert M f (mirrorProcess M X f base σ)) X (fun n => ledgerLuv 0 n) := by
  haveI := mirrorPair_inductor M X hX f base hbase σ hσ
  exact mirror_feedback_unbiased M X f hstrict base σ _ (ledgerProcess_hworld hfree hbaseworld) C

/-- **T3 at the LIA on the forecast schedule** `σ := fun _ => f.toPublicationSchedule` — the
mandate's publication condition `(σ 0).e n ≥ f n` holds with equality (first conjunct), so the
day-`n` ledger literal is absent from `A`'s process before stage `f n`
(`ledgerLuv_absent_before_payout`) and `A`'s day-`n` price of it is a forecast, not a lookup;
the schedule's computability is `f`'s (`DeferralFunction.computable`). The pinned N+ instance for
the market data (audit r1, adversarial N1); `C` still undischarged.
Grade: averaged. Direction: one-way (`A` reads `H`). Weight class: `A`-generable.
Source: mandate T3 ("`σ` publication schedules with `(σ 0).e n ≥ f.f n`"); `li-quote-lane`
`mirrorPair_inductor`, `DeferralFunction.toPublicationSchedule`; audit r1 N1/N3
Kind: C
Fidelity: variant: as `mirror_feedback_unbiased_lia`, at the forecast schedule
Hyps: (b) `C` (undischarged, doubly deferred, no instance; F-C); all else (a) -/
theorem mirror_feedback_unbiased_lia_forecast {H : History} (M : MarketComputation H)
    (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f) (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base)
    (hfree : ProcessFreeOf (ledgerSchedule (realizedExpectation M X f)
      (fun _ => DeferralFunction.toPublicationSchedule f)) base)
    (hbaseworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n))
        (liaHistory (mirrorProcess M X f base (fun _ => DeferralFunction.toPublicationSchedule f)))
        (mirrorProcess M X f base (fun _ => DeferralFunction.toPublicationSchedule f))
        (ledgerProcess_hworld hfree hbaseworld) 1) f) :
    (∀ n, f.f n ≤ ((fun _ : ℕ => DeferralFunction.toPublicationSchedule f) 0).e n) ∧
    QuoteUnbiased (liaHistory (mirrorProcess M X f base (fun _ => DeferralFunction.toPublicationSchedule f)))
      (mirrorProcess M X f base (fun _ => DeferralFunction.toPublicationSchedule f))
      (mirrorExpert M f (mirrorProcess M X f base (fun _ => DeferralFunction.toPublicationSchedule f))) X
      (fun n => ledgerLuv 0 n) :=
  ⟨fun _ => le_rfl,
    mirror_feedback_unbiased_lia M X hX f hstrict base hbase (fun _ => DeferralFunction.toPublicationSchedule f)
      ((f.computable.comp Computable.snd).of_eq (fun _ => rfl)) hfree hbaseworld C⟩

/-- **T1's N+ instance (market data): `LUVTotalTrustAvgOn` on the quoted family, two distinct
markets.** Over the mirror pair, `A` LUV-Total-Trusts the mirror expert at the averaged grade on
the source class `{X}`: observability by the ledger quote (`ledgerLuv_thresholdCodes`,
`mirrorExpert_reflects`), and unbiasedness at *every* e.c. quote reflecting `𝔼^H_{f n}(X n)` — the
ledger quote's by Route A, any other's by `quoteUnbiased_transfer`. Not `LUVTotalTrustAvg` (all
sources): the mirror ledger records one family (item `0`), so clause (i) holds on `{X}` and is
not claimed beyond it (findings F-T3). **The first constructive case of the definition of record
modulo `C`**: the market data are constructed (two distinct markets), the deadline program is
not — no witness of the full package (audit r1 B2).
Grade: averaged. Direction: one-way (`A` reads `H`). Weight class: `A`-generable.
Source: trust-lab-002 (the first constructive case of the definition); root-deference-061
("discharged in zero constructive cases" — now one, averaged grade, one-way, on the quoted
family, modulo `C`); mandate T3; audit r1 B2
Kind: C
Fidelity: variant: on the quoted family `{X}`; ledger-recorded determinacy
Hyps: (b) `C` (one deadline program, for the ledger quote; undischarged hypothesis of
`thm:wubexp`, doubly deferred, no instance; F-C); all else (a) -/
theorem luvTotalTrustAvgOn_mirror {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f) (base : DeductiveProcess)
    (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (mirrorProcess M X f base σ)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f base σ).D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A
        (mirrorProcess M X f base σ) hworld 1) f) :
    LUVTotalTrustAvgOn A (mirrorProcess M X f base σ)
      (mirrorExpert M f (mirrorProcess M X f base σ)) {X} := by
  refine ⟨fun X' hX' _ => ?_, fun X' Y hX' _ hY hR => ?_⟩
  · rw [Set.mem_singleton_iff] at hX'
    subst hX'
    exact ⟨fun n => ledgerLuv 0 n, ledgerLuv_thresholdCodes 0, mirrorExpert_reflects M X' f base σ⟩
  · rw [Set.mem_singleton_iff] at hX'
    subst hX'
    exact quoteUnbiased_transfer _ (ledgerLuv_thresholdCodes 0) hY
      (mirrorExpert_reflects M X' f base σ) hR hworld
      (mirror_feedback_unbiased M X' f hstrict base σ A hworld C)

/-! ## T3, Route B — the per-threshold instance (the lab's reroute) -/

/-- The fixed-threshold sentence family `⌜α_{j,n} > q⌝` is e.c.: one poly-fueled program emits its
code from `n` (the atom shell of `li-quote-lane`'s `encode_ledgerLuv_gt` with `q` a constant).
Source: trust-lab-012 ("price the decidable sentences `ψ^q_t`"); `li-quote-lane` `Codes.lean`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerThreshold_sentenceCodes (j : ℕ) (q : ℚ) :
    MachineSentenceCodes (fun n => (ledgerLuv j n).gt q) := by
  apply MachineSentenceCodes.ofPolySentenceCodes
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const (cleanroomBaseTag + ledgerFamily)).pair
      (PolyFueled.id.pair ((PolyFueled.const j).pair
        (PolyFueled.const (Encodable.encode q)))))).succ_comp
  exact ⟨_, fullPF.of_eq (fun n => (encode_ledgerLuv_gt j n q).symm)⟩

/-- **The threshold sentence's truth is decided by the ledger**: in every completed-theory world
of `ledgerProcess base a σ`, `⌜α_{j,n} > q⌝` pays `1` if `q < a j n` and `0` otherwise — FAF's
`TheoryTruth`, the input of `lic_wub_ofComputation` (`ledgerLuv_decided_by`, strict polarity at
`q = a j n`).
Source: trust-lab-012 ("truth `A`-decidable"); `li-quote-lane` `ledgerLuv_decided_by`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerThreshold_theoryTruth (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (σ : ℕ → PublicationSchedule) (j : ℕ) (q : ℚ) :
    AffineCombination.TheoryTruth (fun n => (ledgerLuv j n).gt q) (ledgerProcess base a σ)
      (fun n => if q < a j n then 1 else 0) := by
  intro n v hv
  have hs : n ≤ max (max n j) (max (Encodable.encode q) ((σ j).e n)) ∧
      j ≤ max (max n j) (max (Encodable.encode q) ((σ j).e n)) ∧
      Encodable.encode q ≤ max (max n j) (max (Encodable.encode q) ((σ j).e n)) ∧
      (σ j).e n ≤ max (max n j) (max (Encodable.encode q) ((σ j).e n)) :=
    ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have h := ledgerLuv_decided_by base a σ j n q hs v (hv _)
  unfold PCWorld.payout
  by_cases hq : q < a j n
  · rw [if_pos (h.1 hq)]
    exact (if_pos hq).symm
  · rw [if_neg (h.2 (not_lt.mp hq))]
    exact (if_neg hq).symm

/-- **T3, Route B, per-threshold instance:** for a fixed rational `q`, `A`'s price of the decided
sentence `⌜α_{0,i} > q⌝` is `w`-unbiased for its truth `1[q < 𝔼^H_{f i}(X i)]` along every
`A`-generable divergent weighting supported on `im f` — FAF's `lic_wub_ofComputation`
(`thm:wub`, the sentence form) with `TheoryTruth` from the ledger. The deadline program `C` here
computes the Boolean `1[q < μ_{f k}]`, the same time clause as Route A's.
Grade: averaged. Direction: one-way (`A` reads `H`). Weight class: `A`-generable.
Source: trust-lab-012 (the reroute); trust-lab-2-007 ("`thm:wub` on threshold sentences");
`redteam/merging-inductors-redteam.md` A1 (d)1
Kind: C
Fidelity: exact (per fixed threshold)
Hyps: (b) `C` (Boolean deadline program — the same double deferral: the truth at `f k` is
`1[q < 𝔼^H_{f (f k)}(X_{f k})]`, due on `⟨k, f (k+1)⟩`; undischarged, F-C); all else (a) -/
theorem mirror_threshold_unbiased {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f) (base : DeductiveProcess)
    (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (mirrorProcess M X f base σ)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f base σ).D n))
    (q : ℚ) (W : ℕ → EF) (hW : PGenerableWeighting W) (hWdiv : DivergentWeighting W A)
    (hsupp : WeightingSupportedOnDeferralImage W A f)
    (C : FeedbackTruthComputation (fun n => if q < realizedExpectation M X f 0 n then 1 else 0)
      f) :
    weightedBias (fun i => (W i).denote A) (fun i => A i ((ledgerLuv 0 i).gt q))
      (fun n => if q < realizedExpectation M X f 0 n then (1 : ℝ) else 0) ≈ₙ
      (fun _ => (0 : ℝ)) :=
  lic_wub_ofComputation A (mirrorProcess M X f base σ) (fun i => (ledgerLuv 0 i).gt q)
    (ledgerThreshold_sentenceCodes 0 q) _
    (ledgerThreshold_theoryTruth base (realizedExpectation M X f) σ 0 q) W hW hWdiv f hstrict C
    hsupp hworld

/-- **"Integrate over thresholds" is FAF's definition of expectation**: `A`'s day-`i` expectation
of `α_{0,i}` is the Riemann sum of its prices of the grid thresholds `⌜α_{0,i} > j/(i+1)⌝`,
`j < i + 1`. The grid thresholds **vary with the day `i`**, so Route B's fixed-`q` instances
(`mirror_threshold_unbiased`) do not sum to this without a uniformity step — the residual the
lab names, located exactly (findings F-B). Over the ledger that step is bypassed by Route A.
Source: trust-lab-012 ("integrate over `q`"); trust-lab-2-007 ("FAF's `LUV.expect` is the
Riemann sum … the uniformity gap becomes a uniform-in-`i` bound on `k+1` applications of
`thm:wub`, with the grid size growing with the day"); FAF `LUV.expect`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_expect_grid (A : History) (j i : ℕ) :
    (ledgerLuv j i).expect A i =
      ((i + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (i + 1),
        A i ((ledgerLuv j i).gt ((k : ℚ) / ((i + 1 : ℕ) : ℚ))) :=
  rfl

/-! ## What the deadline program asks: the double deferral (F-C, proved)

Three field projections, no new mathematics, recorded as package facts so that the ledger's
description of `C` is kernel-anchored (audit r1 B2; the fidelity auditor's probe
`DoubleDeferral.lean`, ported). -/

/-- **The deadline program's `k`-th value is the mesh truth of the ledger quote at day `f k`, due
on the input `⟨k, f (k+1)⟩`** — FAF's `agrees` and `computes_at` at the mirror instance.
Source: FAF `FeedbackTruthComputation` (fields `agrees`, `computes_at`); LI `thm:wub`
("`thmind(φ_{f(n)})` is computable in `O(f(n+1))` time", `main.tex:1251`); audit r1 B2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem deadline_value_at {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (base : DeductiveProcess) (σ : ℕ → PublicationSchedule) (A : History)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f base σ).D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A
        (mirrorProcess M X f base σ) hworld 1) f) (k : ℕ) :
    (C.value k : ℝ) = LUVCombination.normalizedMeshTruth
        (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A (mirrorProcess M X f base σ) hworld 1
        (f.f k) ∧
      C.code (Nat.pair k (f.f (k + 1))) = Encodable.encode (C.value k) :=
  ⟨C.agrees k, C.computes_at k⟩

/-- **The determined value of the day-`f k` ledger quote is `H`'s day-`f (f k)` expectation**:
the `Expert` reads `H` at day `f n`, and on a support day `n = f k` that is day `f (f k)`.
Source: `li-quote-lane` `realizedExpectation` (`M.expectQuoteAt X n (f n)`); audit r1 B2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledger_truth_double_deferral {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (k : ℕ) :
    ((realizedExpectation M X f 0 (f.f k) : ℚ) : ℝ) = (X (f.f k)).expect H (f.f (f.f k)) :=
  realizedExpectation_cast M X f 0 (f.f k)

/-- **The realized day is never before the deadline day**: `f (k+1) ≤ f (f k)` for every
strictly increasing deferral, with equality only when `f k = k + 1`. A faster `f` moves the
realized day further past the deadline, not nearer — the opposite of "fast enough `f`" (F-C).
Source: audit r1 B2; `AGENDA.md` "Fast Student, Slow Teacher" (the clause this corrects)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem deadline_le_realized (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (k : ℕ) : f.f (k + 1) ≤ f.f (f.f k) :=
  hstrict.monotone (Nat.succ_le_of_lt (f.lt k))

/-- **The middle link of the double-deferral chain, which is approximate, not exact:** the
deadline program's `k`-th value is within `(1/2) · 1/(f k + 1)` of `(1/2) · 𝔼^H_{f (f k)}(X (f k))`.
FAF's mesh truth is only approximately determined (`WorldValued.meshTheoryTruth_near`, error
`shareNorm/(n+1)` with `shareNorm (ofLUV ·) = 1`, and FAF deliberately has no exact mesh
determination lemma), and `normalizedMeshTruth` scales it by `meshNormScale 1 = 1/2`. So what
`C` must emit on `⟨k, f (k+1)⟩` is a rational within `1/(2 (f k + 1))` of half `H`'s day-`f (f k)`
expectation — the chain `deadline_value_at` → (this) → `ledger_truth_double_deferral` is now
closed in Lean, with the slack the ledger's "exact" wording had glossed (audit r2 fidelity N1).
Source: FAF `WorldValued.meshTheoryTruth_near`, `normalizedMeshTruth`; `li-asymp-calc`
`l1Norm_ofLUV`; audit r2 fidelity N1
Kind: L
Fidelity: exact (the chain closed; the mesh slack stated)
Hyps: (a) none -/
theorem deadline_value_near_realized {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (base : DeductiveProcess) (σ : ℕ → PublicationSchedule) (A : History)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f base σ).D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A
        (mirrorProcess M X f base σ) hworld 1) f) (k : ℕ) :
    |(C.value k : ℝ) - (1 / 2) * (X (f.f k)).expect H (f.f (f.f k))| ≤
      (1 / 2) * (1 / ((f.f k : ℝ) + 1)) := by
  have hdet : ∀ n, LUV.DeterminedVia (ledgerLuv 0 n) (mirrorProcess M X f base σ)
      ((X n).expect H (f.f n)) := fun n v hv => mirrorExpert_reflects M X f base σ n v hv
  have hnear := (DeterminedVia.worldValued_ofLUV hdet).meshTheoryTruth_near
    (DeterminedVia.determinedViaTheory_ofLUV A hdet) hworld (f.f k)
  simp only [(l1Norm_ofLUV (ledgerLuv 0 (f.f k)) A).1, one_mul] at hnear
  rw [C.agrees k]
  unfold LUVCombination.normalizedMeshTruth
  have hscale : ((LUVCombination.meshNormScale 1 : ℚ) : ℝ) = 1 / 2 := by
    rw [LUVCombination.meshNormScale_cast]
    norm_num
  rw [hscale, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left hnear (by norm_num)

end

end Cleanroom.Trust.TrustMerge
