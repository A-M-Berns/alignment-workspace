import Cleanroom.Trust.TrustMerge.MirrorFeedback
import Cleanroom.Trust.TrustMerge.WeightClass

/-!
# `trust-merge` · Hop2: the standpoint shift (T4(a), T4(b)); the LI Aumann OPEN (T9(3))

**Hop 2 is the merge's one true gap** (trust-lab-011; [[merging-inductors-model]] §(b.2)):
substituting `B_t(φ) = 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)` for `ℙ^H_{f(t)}(φ)` *inside `𝔼^H_t`*. The model
offers two routes — A (mutual good feedback: both `wub` martingales fire and Hop 2 is a triangle
inequality on `w`-averages) and B (relocate: assume `H → A` LUV-Total-Trust on the class
`{⌜ℙ^H_{f(t)}(φ)⌝}`, so Hop 2 holds by definition).

**T4(a) — the dichotomy as a kernel fact.** `Hop2Day` is the per-day substitution, a predicate;
`merge_premise_iff_hop2_of_hop1` says: given Hop 1 (the self-expert's `ccee`, `mergeHop1` /
`selfCondTower`), the §10 premise toward `B` at a quoted instance holds iff Hop 2 does — Route B
*is* the premise relocated (Kind L, exact). No refutation of the per-day form is requested at this
grade; what the agenda intends by the dichotomy is ATTRIBUTION-UNVETTED (findings F-T4a).

**T4(b) — Route A in the averaged grade (headline).** Over a two-sided bundle `MergeBundle`
(`A`'s process decides `H`'s realized `𝔼^H_{f n}(X n)` as ledger atoms — T3's data; `H`'s process
has an e.c. self-quote `Y` of the same number and an e.c. quote `β` of `A`'s day-`n` estimate
`B_n`; both inductors, both `hworld`, three deadline programs), for every weight **bi-generable**
— realized by an `A`-generable weighting on `A` *and* by an `H`-generable weighting on `H` —
divergent and supported on `im f`: `weightedBias w (𝔼^H_n(Y_n)) (B_n) ≈ₙ 0`
(`hop2_avg_of_bigenerable`) and, with `H`'s own `wubexp` on `β`,
`weightedBias w (𝔼^H_n(Y_n)) (𝔼^H_n(β_n)) ≈ₙ 0` (`hop2_avg_quoted_of_bigenerable`): two (three)
unbiasedness statements about the same future quantity `μ_n = 𝔼^H_{f n}(X n)`, subtracted —
[[faithful-acceleration]] §5 Steps 1–3 made two-market. **The standpoint shift is a theorem about
weight classes: bi-generability suffices** (the LI theorem is the sufficiency direction; necessity
is known only as the finite shadow `meanZero_transfer_iff`, `Hop2Finite.lean` — audit r1,
adversarial N3).

**Status: `partial: over the OPEN pair`; no witness of the full package.** `MergeBundle` carries
both inductors as fields. The *market data* of each one-sided input is inhabited (N+ for the
data): `A` reading `H` is `mirror_feedback_unbiased_lia` (`MirrorFeedback.lean`), `H` reading a
fixed `A` is `li-quote-lane`'s `paperOneWayPair`, the self-quote side is
`selfTrust_day`/`selfQuoteUnbiased_ofComputation`. The three deadline-program fields `C_A`,
`C_Y`, `C_β` are inhabited nowhere in this package (F-C): no term of any of their types is
produced, for any `H`, `f`, `X`, so no witness inhabits the full hypothesis package of any
theorem below (audit r1, fidelity B2). The *simultaneous* bundle — `A`'s process reading `H`'s
expectations while `H`'s process reads `A`'s — is the two-way pair, `li-coupled-pair`'s OPEN row
of record; two mirror one-way pairs do not make one (`MirrorPair.lean`). Every theorem over
`MergeBundle` inherits that status.

**Publication scope** (audit r1, fidelity N3 / adversarial N1). The bundle carries `σ_late`:
`f n ≤ (σ 0).e n` — the ledger literal naming `𝔼^H_{f n}(X n)` is published no earlier than the
day it names, so `A`'s day-`n` price is a forecast, not a lookup of a decided atom
(`ledgerLuv_absent_before_payout`; the instance `σ := fun _ => f.toPublicationSchedule`). Without
it the per-day clauses of `li_aumann_failure_open` could be met by an early schedule for a trivial
reason.

**T9(3).** `li_aumann_failure_open` (trust-lab-2-022) is stated over the bundle with `sorry`,
listed in `trust-merge-open.txt`: it rests on the bundle's existence, so it is OPEN twice over.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction LogicalInduction.FeedbackTruth Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Found.LiQuoteLane
open Cleanroom.Bli.BliFound

noncomputable section

/-! ## T4(a) — the per-day dichotomy -/

/-- **Hop 2, per-day form:** `H`'s expectations of two quotes agree in the limit — `Z'` the quote
of `ℙ^H_{f n}(φ_n) · w_{f n}` (the self-quote product, Hop 1's right side) and `Z''` the quote of
`B_n(φ) · w_{f n}` (the merge's product, the §10 premise's right side). The predicate is the bare
`≈ₙ` of the two price sequences; which LUVs play `Z'`, `Z''` is the caller's data.
Source: trust-lab-011 ("swap `ℙ^H_{f(t)}(φ)` for `B_t(φ)` inside `𝔼^H_t(·)`");
[[merging-inductors-model]] §(b.2) Hop 2
Kind: D
Fidelity: exact (per-day grade)
Hyps: n/a -/
def Hop2Day (H : History) (Z' Z'' : ℕ → LUV) : Prop :=
  (fun n => (Z' n).expect H n) ≈ₙ (fun n => (Z'' n).expect H n)

/-- **The §10 premise toward `B` is Hop 1 ∘ Hop 2 (T4(a), the dichotomy as a kernel fact):**
given Hop 1 at a quoted instance — `𝔼^H_n(Z_n) ≈ₙ 𝔼^H_n(Z'_n)` with `Z` the left product
`⌜X_n w_{f n}⌝` and `Z'` the self-quote product (the self-expert's `ccee`, `def-self-trust`'s
`mergeHop1` / `selfCondTower`) — the premise toward `B` at `(Z, Z'')`, `𝔼^H_n(Z_n) ≈ₙ 𝔼^H_n(Z''_n)`,
holds **iff** `Hop2Day H Z' Z''`. So Route B ("assume `H → A` LUV-Total-Trust on the class
`{⌜ℙ^H_{f(t)}(φ)⌝}`") relocates the premise exactly, neither more nor less: the finding of record
for T4(a).
Source: trust-lab-011 (Routes A/B); [[merging-inductors-model]] §(b.2) ("Route B … makes Hop 2
true by definition … relocates"); `redteam/merging-inductors-redteam.md` (b)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem merge_premise_iff_hop2_of_hop1 (H : History) (Z Z' Z'' : ℕ → LUV)
    (h1 : (fun n => (Z n).expect H n) ≈ₙ (fun n => (Z' n).expect H n)) :
    ((fun n => (Z n).expect H n) ≈ₙ (fun n => (Z'' n).expect H n)) ↔ Hop2Day H Z' Z'' :=
  ⟨fun h => h1.symm.trans h, fun h => h1.trans h⟩

/-! ## T4(b) — the two-sided bundle and Route A in the averaged grade -/

/-- **The merge bundle** (two-sided, `partial: over the OPEN pair`): `H` with market program `M`
and process `DPH`; `A` over the mirror process `mirrorProcess M X f baseA σ` (its ledger decides
`H`'s realized `𝔼^H_{f n}(X n)` — T3's data); both inductors with a world at every stage; in `H`'s
language an e.c. self-quote `Y` of `𝔼^H_{f n}(X n)` (FAF's `paperDeferredExpectationQuoteCode`
over a `paperDP` base, lifted along `consistentWithTheory_base_of_ledger`) and an e.c. quote `β`
of `A`'s day-`n` merge estimate `B_n = 𝔼^A_n(α_{0,n})` (`li-quote-lane`'s one-way ledger with
`A`'s expectations as the table, `ledgerLuv_determinedVia`); the publication-scope clause
`σ_late` (`f n ≤ (σ 0).e n`, so `A` forecasts rather than looks up — module docstring); and the
three deadline programs (`C_A` for `A` watching `H`, `C_Y` for `H`'s self-quote, `C_β` for `H`
watching `A`), each the doubly deferred program of `thm:wubexp` (F-C), **inhabited nowhere in
this package**. **The simultaneous pair is the OPEN two-way question** (`li-coupled-pair`): the
market data of each one-sided field is inhabited, the three `C` fields are not, the structure
is not built here. Direction: two-way.
Source: [[merging-inductors-model]] §(b.2) Route A ("the good-feedback + deferral-time bounds hold
simultaneously for `H`-watching-`A` and `A`-watching-`H`"); mandate T4(b); audit r1 B2/N3
Kind: D
Fidelity: variant: ledger-recorded determinacy on both sides; the deadline programs as fields;
publication scope as a field (repair r1)
Hyps: n/a (a structure; its inhabitation is `li-coupled-pair`'s OPEN) -/
structure MergeBundle where
  /-- the human market -/
  H : History
  /-- `H`'s market program (the realized table is computed from it) -/
  M : MarketComputation H
  /-- the source family -/
  X : ℕ → LUV
  /-- the source is e.c. -/
  hX : LUV.MachineThresholdCodeSeq X
  /-- the deferral -/
  f : DeferralFunction
  /-- strictly increasing (FAF's `thm:wubexp` hypothesis) -/
  hstrict : StrictlyIncreasingDeferral f
  /-- the base of `A`'s process -/
  baseA : DeductiveProcess
  /-- the publication schedules of `A`'s ledger -/
  σ : ℕ → PublicationSchedule
  /-- publication scope: the day-`n` ledger literal (naming `𝔼^H_{f n}(X n)`) is published no
  earlier than day `f n`, so `A`'s day-`n` price of it is a forecast (the mandate's
  `(σ 0).e n ≥ f n`; instance `σ := fun _ => f.toPublicationSchedule`) -/
  σ_late : ∀ n, f.f n ≤ (σ 0).e n
  /-- the AI market -/
  A : History
  /-- `A` is an inductor over the mirror process -/
  A_inductor : IsLogicalInductor A (mirrorProcess M X f baseA σ)
  /-- every stage of `A`'s process has a world -/
  A_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M X f baseA σ).D n)
  /-- `H`'s process -/
  DPH : DeductiveProcess
  /-- `H` is an inductor over its process -/
  H_inductor : IsLogicalInductor H DPH
  /-- every stage of `H`'s process has a world -/
  H_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)
  /-- `H`'s self-quote of `𝔼^H_{f n}(X n)` -/
  Y : ℕ → LUV
  /-- the self-quote is e.c. -/
  hY : LUV.MachineThresholdCodeSeq Y
  /-- the self-quote reflects `H`'s realized day-`f n` expectation in every `DPH`-world -/
  Y_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
    v.ValuesAt (Y n) ((X n).expect H (f.f n))
  /-- `H`'s quote of `A`'s day-`n` merge estimate `B_n = 𝔼^A_n(α_{0,n})` -/
  β : ℕ → LUV
  /-- the merge quote is e.c. -/
  hβ : LUV.MachineThresholdCodeSeq β
  /-- the merge quote reflects `A`'s same-day estimate in every `DPH`-world -/
  β_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
    v.ValuesAt (β n) ((ledgerLuv 0 n).expect A n)
  /-- the deadline program for `A` watching `H` -/
  C_A : FeedbackTruthComputation
    (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (ledgerLuv 0 n)) A
      (mirrorProcess M X f baseA σ) A_hworld 1) f
  /-- the deadline program for `H`'s self-quote -/
  C_Y : FeedbackTruthComputation
    (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n)) H DPH H_hworld 1) f
  /-- the deadline program for `H` watching `A` -/
  C_β : FeedbackTruthComputation
    (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (β n)) H DPH H_hworld 1) f

/-- The merge estimate of a bundle: `B_n := 𝔼^A_n(α_{0,n})`, `A`'s same-day expectation of the
ledger LUV naming `𝔼^H_{f n}(X n)` (`MergeExpert.est` at the mirror quote).
Source: [[merging-inductors-model]] §0
Kind: D
Fidelity: exact -/
def MergeBundle.est (B : MergeBundle) (n : ℕ) : ℝ := (ledgerLuv 0 n).expect B.A n

/-- `H`'s realized day-`f n` expectation of `X n` — the quantity both sides estimate.
Source: [[merging-inductors-model]] §0 (`μ_t`)
Kind: D
Fidelity: exact -/
def MergeBundle.μ (B : MergeBundle) (n : ℕ) : ℝ := (B.X n).expect B.H (B.f.f n)

/-- **Bi-generability**: a real weight sequence realized by an `A`-generable weighting on `A`'s
market *and* by an `H`-generable weighting on `H`'s market. The weight class the standpoint shift
costs.
Source: [[faithful-acceleration]] §5 ("the weight `w_n` is recognizable to **both** inductors");
trust-lab-2-008; mandate T4(b)
Kind: D
Fidelity: exact
Hyps: n/a -/
def BiGenerable (B : MergeBundle) (w : ℕ → ℝ) : Prop :=
  (∃ W : ℕ → EF, PGenerableWeighting W ∧ ∀ i, (W i).denote B.A = w i) ∧
    (∃ W' : ℕ → EF, PGenerableWeighting W' ∧ ∀ i, (W' i).denote B.H = w i)

/-- A realized weighting of a bundle side, from the real data: `[0,1]`, divergent, supported on
`im f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem divergentWeighting_of_realized {P : History} {W : ℕ → EF} {w : ℕ → ℝ}
    (hWw : ∀ i, (W i).denote P = w i) (hmem : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hdiv : Tendsto (prefixSum w) atTop atTop) : DivergentWeighting W P := by
  refine ⟨fun n => by rw [hWw n]; exact hmem n, ?_⟩
  have : (fun n => (W n).denote P) = w := funext hWw
  rw [this]
  exact hdiv

open Cleanroom.Deference.DefSelfTrust in
/-- **The bi-generable class of T4(b) is inhabited for every bundle** (N+ guard; audit r2
adversarial N10, probe ported): the indicator of `im f`, `pullBack f (fun _ => EF.const 1)`,
denotes the same reals on every history (`pullBackOne_denote_hist_indep`), so one feature
realizes a `[0,1]`, divergent, `im f`-supported weight on both markets. This guards the
quantifier of `hop2_avg_of_bigenerable`, not the bundle: the bundle's own inhabitation is the
OPEN pair.
Source: audit r2 adversarial N10 (probe `BiGenerableInhabited.lean`); `WeightClass.lean`
Kind: N+ (guard)
Fidelity: exact
Hyps: (a) none -/
theorem biGenerable_class_inhabited (B : MergeBundle) :
    ∃ w : ℕ → ℝ, BiGenerable B w ∧ (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
      Tendsto (prefixSum w) atTop atTop ∧ ∀ n, w n ≠ 0 → ∃ k, B.f.f k = n := by
  refine ⟨fun i => (pullBack B.f (fun _ => EF.const 1) i).denote B.A, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨pullBack B.f (fun _ => EF.const 1),
      pullBack_pgenerable B.f B.hstrict (constWeighting 1), fun _ => rfl⟩,
      ⟨pullBack B.f (fun _ => EF.const 1),
      pullBack_pgenerable B.f B.hstrict (constWeighting 1),
      fun i => pullBackOne_denote_hist_indep B.H B.A B.f i⟩⟩
  · exact fun i => pullBackOne_denote_mem B.A B.f i
  · exact (pullBackOne_divergent B.A B.f B.hstrict).2
  · exact fun n hn => pullBack_supported B.f _ B.A n hn

/-- **T4(b) (headline). Route A in the averaged grade — bi-generability suffices for Hop 2:**
over a merge bundle, for every bi-generable `[0,1]` weight `w`, divergent and supported on
`im f`, `H`'s expectation of its self-quote `Y_n` (of `μ_n = 𝔼^H_{f n}(X n)`) is `w`-unbiased
for `A`'s merge estimate `B_n`: `weightedBias w (𝔼^H_n(Y_n)) (B_n) ≈ₙ 0`. Proof: `A`'s side,
`weightedBias w B μ → 0` (T3, `mirror_feedback_unbiased`, at the `A`-generable realization);
`H`'s side, `weightedBias w (𝔼^H Y) μ → 0` (`thm:wubexp` on `H`'s own self-quote,
`wub_at_quote`, at the `H`-generable realization); subtract (`WeightedApprox.trans`). The
common `μ` cancels — [[faithful-acceleration]] §5 Steps 1–3, two-market. Sufficiency only:
that bi-generability is *necessary* is known at the finite level (`meanZero_transfer_iff`), not
here.
Grade: averaged. Direction: two-way. Weight class: bi-generable. **Status: `partial: over the
OPEN pair`** (the bundle); no witness of the full package (the `C` fields, F-C).
Source: trust-lab-011 (Route A: "Both martingales fire; Hop 2 is a triangle inequality on
`w`-averages"); [[merging-inductors-model]] §(b.2); [[faithful-acceleration]] §5 Steps 1–3;
trust-lab-2-008 (the class question: bi-generability suffices)
Kind: C
Fidelity: variant: averaged grade (the model's Hop 2 is per-day); ledger determinacy
Hyps: (b) `C_A`, `C_Y` — deadline programs of `thm:wubexp`, fields of the bundle, undischarged
hypotheses of the cited theorem (doubly deferred, F-C), inhabited nowhere; the bundle's existence
is the OPEN two-way pair; all else (a) -/
theorem hop2_avg_of_bigenerable (B : MergeBundle) (w : ℕ → ℝ) (hbi : BiGenerable B w)
    (hmem : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hsupp : ∀ n, w n ≠ 0 → ∃ k, B.f.f k = n) :
    weightedBias w (fun n => (B.Y n).expect B.H n) B.est ≈ₙ (fun _ => (0 : ℝ)) := by
  obtain ⟨⟨W, hW, hWA⟩, ⟨W', hW', hWH⟩⟩ := hbi
  haveI := B.A_inductor
  haveI := B.H_inductor
  have hWfun : (fun i => (W i).denote B.A) = w := funext hWA
  have hW'fun : (fun i => (W' i).denote B.H) = w := funext hWH
  -- A's side
  have hA := mirror_feedback_unbiased B.M B.X B.f B.hstrict B.baseA B.σ B.A B.A_hworld B.C_A
    W hW (divergentWeighting_of_realized hWA hmem hdiv)
    (fun n hn => hsupp n (by rwa [hWA n] at hn))
  rw [hWfun] at hA
  -- H's side
  have hH := wub_at_quote B.Y B.hY (fun n v hv => B.Y_reflected n v hv) B.hstrict B.H_hworld
    B.C_Y W' hW' (divergentWeighting_of_realized hWH hmem hdiv)
    (fun n hn => hsupp n (by rwa [hWH n] at hn))
  rw [hW'fun] at hH
  -- subtract
  have h1 : WeightedApprox w (fun n => (B.Y n).expect B.H n) B.μ := by
    rw [weightedApprox_iff_weightedBias]
    delta MergeBundle.μ
    simpa only [AsympEq, sub_zero] using hH
  have h2 : WeightedApprox w B.est B.μ := by
    rw [weightedApprox_iff_weightedBias]
    delta MergeBundle.μ MergeBundle.est
    simpa only [AsympEq, sub_zero, mirrorExpert, Expert.estimate] using hA
  have h3 := WeightedApprox.trans hdiv h1 h2.symm
  rw [weightedApprox_iff_weightedBias] at h3
  simpa only [AsympEq, sub_zero] using h3

/-- **T4(b), the quoted form:** with `H`'s own `wubexp` on its quote `β` of `B_n`
(`weightedBias w (𝔼^H β) B → 0`, the averaged substitute for `readability`, which would cost
(L)), `weightedBias w (𝔼^H_n(Y_n)) (𝔼^H_n(β_n)) ≈ₙ 0` — Hop 2 with both sides *inside* `𝔼^H`,
in the averaged grade. Three unbiasedness statements about `μ_n` subtracted.
Grade: averaged. Direction: two-way. Weight class: bi-generable. Status: `partial: over the
OPEN pair`.
Source: trust-lab-011; mandate T4(b) ("plus `readability` to replace `𝔼^H_n(⌜B_n⌝)` by `B_n`"
— here the averaged form, no (L))
Kind: C
Fidelity: variant: averaged grade; the replacement of `𝔼^H(β)` by `B` is averaged, not per-day
Hyps: (b) `C_A`, `C_Y`, `C_β` — deadline programs of `thm:wubexp`, undischarged (F-C), inhabited
nowhere; the bundle; all else (a) -/
theorem hop2_avg_quoted_of_bigenerable (B : MergeBundle) (w : ℕ → ℝ) (hbi : BiGenerable B w)
    (hmem : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hsupp : ∀ n, w n ≠ 0 → ∃ k, B.f.f k = n) :
    weightedBias w (fun n => (B.Y n).expect B.H n) (fun n => (B.β n).expect B.H n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
  have h12 := hop2_avg_of_bigenerable B w hbi hmem hdiv hsupp
  obtain ⟨_, ⟨W', hW', hWH⟩⟩ := hbi
  haveI := B.H_inductor
  have hW'fun : (fun i => (W' i).denote B.H) = w := funext hWH
  have hβ := wub_at_quote B.β B.hβ (fun n v hv => B.β_reflected n v hv) B.hstrict B.H_hworld
    B.C_β W' hW' (divergentWeighting_of_realized hWH hmem hdiv)
    (fun n hn => hsupp n (by rwa [hWH n] at hn))
  rw [hW'fun] at hβ
  have h1 : WeightedApprox w (fun n => (B.Y n).expect B.H n) B.est := by
    rw [weightedApprox_iff_weightedBias]
    simpa only [AsympEq, sub_zero] using h12
  have h2 : WeightedApprox w (fun n => (B.β n).expect B.H n) B.est := by
    rw [weightedApprox_iff_weightedBias]
    delta MergeBundle.est
    simpa only [AsympEq, sub_zero] using hβ
  have h3 := WeightedApprox.trans hdiv h1 h2.symm
  rw [weightedApprox_iff_weightedBias] at h3
  simpa only [AsympEq, sub_zero] using h3

/-! ## T9(3) — the LI Aumann failure, OPEN -/

/-- **OPEN (trust-lab-2-022, the LI Aumann failure).** Two inductors with mutual good feedback
(a merge bundle on the indicator family of a sentence `φ`), `φ` undecided at every stage of `H`'s
process in both polarities (the hypothesis form of `lic_nonDogmatism`), each's expectation of the
other's estimate tracking it per day (`A`'s read of `H`'s realized expectation, `H`'s read of
`A`'s merge estimate), yet their prices of `φ` not `≈ₙ`-agreeing. Typed over `MergeBundle`, so
it rests on the bundle's existence (`li-coupled-pair`'s OPEN pair) and is OPEN twice over; the
per-day tracking clauses are per-day readability statements that cost (L) each. The bundle's
`σ_late` keeps the tracking clauses honest: an early schedule would decide `⌜𝔼^H_{f n}(φ)⌝` in
`A`'s process before day `f n` and satisfy `B.est ≈ₙ B.μ` as a lookup (audit r1 N3). The source's
warning stands: "common knowledge" must be defined via the right prior or the result is vacuous
or false — here it is the bundle's mutual quotes. Not attempted: a construction would need two
LIAs with interlocking processes and a pseudorandom `φ`.
Source: trust-lab-2-022 ([[weak-endorsement-deference-ideate]] Idea 3, "The LI analog
(CONJECTURE, harder)"); mandate T9(3)
Kind: OPEN
Fidelity: variant: over the merge bundle; per-day tracking clauses
Hyps: n/a -/
theorem li_aumann_failure_open :
    ∃ (B : MergeBundle) (φ : Sentence),
      (B.X = fun _ => literalIndicator φ) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (B.DPH.D n) ∧ v.Holds φ) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (B.DPH.D n) ∧ ¬ v.Holds φ) ∧
      ((fun n => B.est n) ≈ₙ (fun n => B.μ n)) ∧
      ((fun n => (B.β n).expect B.H n) ≈ₙ (fun n => B.est n)) ∧
      ¬ ((fun n => B.H n φ) ≈ₙ (fun n => B.A n φ)) := by
  sorry

end

end Cleanroom.Trust.TrustMerge
