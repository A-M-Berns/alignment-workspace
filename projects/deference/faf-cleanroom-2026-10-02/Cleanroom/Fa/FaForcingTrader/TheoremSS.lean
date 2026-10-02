import Cleanroom.Fa.FaForcingTrader.Bridge
import Cleanroom.Fa.FaForcingTrader.A.TheoremSS
import Cleanroom.Fa.FaForcingTrader.B.Certificate
import Cleanroom.Fa.FaForcingTrader.Compat

/-!
# `fa-forcing-trader` · TheoremSS: Theorem SS and scheduled soft Total Trust, of record (T6, T7)

Main module of the reconciled package ([[fa-forcing-trader-mandate]] T6, T7, T12 (a)). Three
grades of Theorem SS live here, each stated once over the definitions of record (`Defs.lean`:
`schedGate`, `LegibleOn`, `WindowDisjoint`), with the (b)/(c) price of each in its docstring:

1. **Limit point, no certificate** — `theoremSS_limitPoint` (angle A's; (c) `pkg.reflected`,
   (c) `hL`): the `A` side is fa-theorem-a's `quote_unbiased` (FAF's `recurringunbiasednessexp`,
   a limit point), the `H` side is the trader bridge T4 (grade (a)).
2. **Full limit, one certificate** — `theoremSS_fullLimit_oneCert` (**the reconciler's**; (c)
   `pkg.reflected`, (c) `hL`, (b) `CA`): the `A` side is angle B's engine `quoteSide_fullLimit`
   (FAF's corrected 4.8.16 `luv_wubexp_ofComputation` under the timing certificate `CA`), the
   `H` side is again T4. This is strictly cheaper than angle B's T6′: no `cee` carrier `hq`,
   no `H`-side certificate `CH`. The grid-certificate variant `theoremSS_fullLimit_gridCert`
   takes angle B's repaired certificate on the computable grid truth instead (findings F-B1).
3. **Full limit, two certificates** — `theoremSS_fullLimit_twoCert` (angle B's T6′, restated over
   the record definitions through `Compat`; (c) `pkg.reflected`, (c) `hL`, (b) `CA`, `CH`, (a)
   `hq`): both sides by citation of 4.8.16; it needs only `StrictlyIncreasingDeferral d`, not
   window-disjointness (findings F-B2).

Scheduled soft Total Trust follows from each at its grade: `SchedThresholdAbove` (the record's
`∃ᶠ` form, angle A's and the mandate's) from grade 1, and `SchedThresholdAboveEv` (the `∀ᶠ` form,
angle B's `SchedThresholdAbove` under its record name) from grades 2 and 3. The two angles used
**the same name `SchedThresholdAbove` for the two different filters**; the reconciled package
names the grade (findings R-1).

No N+ witness inhabits the full package of grades 2 and 3: the certificates are the OPEN
`exists_gridCertificate_of_marketComputation` (`Open.lean`). Grade 1's full package is inhabited
by `theoremSS_paper_self_top` (`Witnesses`, repair round 1: same market, `X ≡ 𝟙(⊤)`, `hdiv`
derived at every content threshold `t + δ < 1`; N+ package, N− content); the round-0 instance
`A.theoremSS_paper_self` is conditional on `hdiv` and is N−, not an inhabitant. No two-market
inhabitant of (L) is known (T11, OPEN). Every grade is stated for the divergent-mass case
(`hdiv`); the note's finite-mass remark (`∑ w < ∞` ⟹ `w → 0` along the schedule and the
unnormalized forms hold with an additive constant) is the real-sequence lemma
`unnormBias_bounded_of_summable` (`Analysis`, repair round 2), not part of these statements.

(Angle A's declarations are referenced fully qualified, `_root_.Cleanroom.Fa.FaForcingTrader.A.…`,
wherever a theorem binds a market named `A`: the variable would otherwise shadow the namespace.)
-/
namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

export A (theoremSS_limitPoint_general legibleOn_schedGate legibleOn_schedGateBelow
  theoremSS_tower_of_readable SchedThresholdAbove SchedThresholdBelow SchedThresholdAboveUnnorm
  schedThresholdAbove_iff_unnorm schedThresholdAbove_of_limitPoint
  schedThresholdBelow_of_limitPoint schedThresholdAbove_eventually_of_fullLimit
  schedThresholdAbove_of_perDay gated_theoremSS hasLimitPoint_zero_of_add_tendsto
  weightedAverage_three)

export B (QuoteCertificate quoteSide_fullLimit selfSide_fullLimit theoremSS_fullLimit_general
  quoteSide_fullLimit_grid gridRound gridTruth gridTruth_approxDetermined
  expectApprox_sub_gridRound_abs_le StrictlyReflected normalizedMeshTruth_eq_gridTruth_of_strict
  shareNorm_ofLUV)

/-! ## A. Grade 1: limit point, no certificate (angle A) -/

/-- **T6 (headline, of record). Theorem SS, one-way, limit-point grade, on the scheduled quote
gate.** For inductors `A`, `H`, a quote package, a window-disjoint schedule `d`, rationals `t`,
`δ > 0`, the corpus's (L) for the quote (`hL`), and the gate
`w_n = 1[n ∈ im d] · Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t)` divergent in `A`'s prices: `0` is a limit
point of `(∑_{i≤n} w_i (𝔼^A_i(⌜𝔼^H_{f i}(X_i)⌝) − 𝔼^H_i(X_i))) / ∑_{i≤n} w_i`. Angle A's theorem,
restated: `quote_unbiased` on the `A`-native gate + T4 on its `H`-legible copy + T5.
Scope: one-way (`H` reads `A`'s quote only under (L); `A` never reads `H`'s prices). e.d. family
`X`. Schedule: window-disjoint `DeferralFunction`. Grade: limit point.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Junk width: at `δ = 0` the gate is `≡ 0` and `hdiv` unsatisfiable (vacuous, not false); the
headline takes `0 < δ`. Content region: `hdiv` is unsatisfiable at `t ≥ 1 + δ` (empty ramp) and
free at `t ≤ −δ` (the gate is the whole schedule, `schedGate_divergent_of_le_neg`); the
selection the gate expresses lives in `0 < t < 1`.
Witness (`Witnesses`): full package at a content threshold, `theoremSS_paper_self_top` (same
market, `X ≡ 𝟙(⊤)`, any `t + δ < 1`; `hdiv` derived by `schedGate_divergent_of_realized_tendsto_one`);
N− for content (`A = H`). Two-market: T11 OPEN.
Source: vq-wiki-050 (Theorem SS, agreement form); lean-deference-038; [[theorem-ss-streamlined]] §0, §6; [[route-sparse-schedule]] §8
Kind: C
Fidelity: weaker: limit point, not the note's two-sided full limit (grades 2 and 3 below)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hδ`, `hdiv`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hL : LegibleOn H (quoteSeq Y A)` (the corpus's (L); no two-market inhabitant known, T11). -/
theorem theoremSS_limitPoint {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A) :
    HasLimitPoint (weightedBias (fun n => (schedGate Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.theoremSS_limitPoint
    pkg hcode hworldA hworldH hval hwd t hδ hL hdiv

/-- **T6, mirror (of record).** Theorem SS at limit-point grade on the scheduled lower gate
`1[n ∈ im d] · Ind_δ(a_n < t)`. Angle A's theorem, restated.
Scope: one-way. e.d. family. Grade: limit point.
Source: [[theorem-ss-streamlined]] §8 ("the mirror ramp — a genuinely separate application")
Kind: C
Fidelity: weaker: limit point
Hyps: as `theoremSS_limitPoint`: (c) `pkg.reflected`; (c) `hL`. -/
theorem theoremSS_limitPoint_below {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A) :
    HasLimitPoint (weightedBias (fun n => (schedGateBelow Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.theoremSS_limitPoint_below
    pkg hcode hworldA hworldH hval hwd t hδ hL hdiv

/-! ## B. Grade 2: full limit from one certificate (the reconciler's assembly) -/

/-- **The assembly: an `A`-side full limit plus the trader bridge gives Theorem SS at full-limit
grade.** For any real weighting `w ∈ [0,1]` with divergent mass, supported on the window-disjoint
schedule `d` and legible on `H` (`hL`), if the `w`-average of `𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_{f n}(X_n)`
tends to `0` (`hA`, the `A`-side input), then so does the `w`-average of
`𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)`: T4 on the `H`-legible copy of `w` gives
`price_{f n}(bundle_n) ≈_w 𝔼^H_n(X_n)`, T5 gives `price_{f n}(bundle_n) ≈_w 𝔼^H_{f n}(X_n)`, and
`WeightedApprox.trans` chains `a ≈_w Y ≈_w p ≈_w h`. The `A`-side input is what distinguishes the
grades: a limit point (grade 1, `A.theoremSS_limitPoint_general`), or a full limit under a timing
certificate (grade 2, below).
Scope: one-way. e.d. family. Schedule: window-disjoint `DeferralFunction`. Grade: full limit.
Source: [[theorem-ss-streamlined]] §6 (Assembly), with the `H` side by the trader variant (§3 Remark); mandate § Reconciler
Kind: C
Fidelity: exact (the assembly step of the agreement form)
Hyps: (a) `hcode`, `hworldH`, `hval`, `hwd`, `hw01`, `hdiv`, `hsupp`; input `hA` (the consumer's `A`-side full limit — not derived here: discharged by `quoteSide_fullLimit` under (b) `CA` at grade 2, or absent at grade 1); (c) `hL` (the corpus's (L) for `w`). -/
theorem theoremSS_fullLimit_of_quoteSide {H A : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d)
    {w : ℕ → ℝ} (hw01 : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hsupp : ∀ n, w n ≠ 0 → ∃ k, d.f k = n) (hL : LegibleOn H w)
    (hA : WeightedApprox w (quoteSeq Y A) (realized H f X)) :
    WeightedApprox w (quoteSeq Y A) (fun n => (X n).expect H n) := by
  obtain ⟨GH, hGH, hGHw⟩ := hL
  have hfun : (fun n => (GH n).denote H) = w := funext hGHw
  have hdivH : DivergentWeighting GH H := by
    refine ⟨fun n => by rw [hGHw]; exact hw01 n, ?_⟩
    rw [hfun]
    exact hdiv
  have hsuppH : ∀ n, (GH n).denote H ≠ 0 → ∃ k, d.f k = n :=
    fun n hn => hsupp n (by rwa [hGHw] at hn)
  have hH : WeightedApprox w (fun n => (bundle X n).price H (f.f n))
      (fun n => (X n).expect H n) := by
    have := hSideBridge hcode hworldH hwd hGH hsuppH hdivH
    rwa [hfun] at this
  have hpY : WeightedApprox w (fun n => (bundle X n).price H (f.f n)) (realized H f X) :=
    weightedApprox_bundle_realized hcode hworldH hval f (fun i => (hw01 i).1) hdiv
  exact WeightedApprox.trans hdiv hA (WeightedApprox.trans hdiv hpY.symm hH)

/-- **Theorem SS at full-limit grade from one certificate, general gate.** For any
`PGenerableWeighting G` of `A`'s market supported on the window-disjoint schedule `d`, divergent in
`A`'s prices and legible on `H` (`hL`), and the timing certificate `CA` for `A`'s quote family on
`d` (FAF's `FeedbackTruthComputation` of the normalized mesh truth; corrected 4.8.16's timing
condition, K4): the `G`-weighted average of `𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)` tends to `0`.
The `A` side is angle B's `quoteSide_fullLimit` (FAF's `luv_wubexp_ofComputation`); the `H` side
is angle A's trader bridge T4 — so neither FAF's `cee` carrier `hq` nor an `H`-side certificate
`CH` is needed (compare `theoremSS_fullLimit_twoCert`).
Scope: one-way. e.d. family. Schedule: window-disjoint `DeferralFunction`. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §0 (Theorem SS, agreement form), §4 L3 (the `A` side), §3 Remark (the trader variant on the `H` side); mandate § Reconciler
Kind: C
Fidelity: exact (agreement form, full limit, general gate; divergent-mass case only (`hdiv`) — the note's finite-mass clause is `unnormBias_bounded_of_summable` (`Analysis`), not part of this statement)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hG`, `hsupp`, `hdiv`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hL` (the corpus's (L) for the gate); (b) `CA` (corrected 4.8.16's timing condition on `A`'s mesh, LI Thm 4.8.16 / FAF `thm:wubexp`; no inhabitant for a quote family of an inductor is known — F-B1, OPEN `exists_gridCertificate_of_marketComputation`). -/
theorem theoremSS_fullLimit_general_oneCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : WeightingSupportedOnDeferralImage G A d)
    (hL : LegibleOn H (fun n => (G n).denote A)) (hdiv : DivergentWeighting G A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    WeightedApprox (fun n => (G n).denote A) (quoteSeq Y A) (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_of_quoteSide hcode hworldH hval hwd hdiv.1 hdiv.2 hsupp hL
    (quoteSide_fullLimit pkg hworldA hG hdiv hwd.1 hsupp CA)

/-- **T6′ (headline, of record). Theorem SS, agreement form, full limit, on the scheduled quote
gate, from one certificate.** Under the hypotheses of `theoremSS_limitPoint` plus the timing
certificate `CA` for `A`'s quote family on the schedule: the gate-weighted average of
`𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)` on `w_n = 1[n ∈ im d] · Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t)`
tends to `0`, two-sided — [[theorem-ss-streamlined]]'s Theorem SS in agreement form. The
reconciler's merge of the two angles: angle B's `A`-side engine with angle A's `H`-side trader.
Scope: one-way (`H` reads `A`'s quote only under (L); `A` never reads `H`'s prices). e.d. family
`X`. Schedule: window-disjoint `DeferralFunction`. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Witness: none for the full package (the certificate is OPEN, and FAF's literal certificate has
no inhabitant expected on an inductor pair — F-B1; the grid form `theoremSS_fullLimit_gridCert`
is the one the OPEN row can discharge); the same-market instance inhabits everything but `CA`
(`theoremSS_paper_self_top` at grade 1, `hdiv` included).
Source: [[theorem-ss-streamlined]] §0 Theorem SS (agreement form, vq-wiki-050); lean-deference-038; [[route-sparse-schedule]] §10
Kind: C
Fidelity: exact (agreement form, full limit; the note's statement; the Tower form costs (L) again — `theoremSS_tower_of_readable`; divergent-mass case only (`hdiv`) — the note's finite-mass clause is `unnormBias_bounded_of_summable` (`Analysis`), not part of this statement)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hδ`, `hdiv`; (c) `pkg.reflected`; (c) `hL : LegibleOn H (quoteSeq Y A)` (the corpus's (L); T11 OPEN); (b) `CA` (corrected 4.8.16's timing condition on `A`'s mesh; OPEN). -/
theorem theoremSS_fullLimit_oneCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    WeightedApprox (fun n => (schedGate Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_general_oneCert pkg hcode hworldA hworldH hval hwd
    (schedGate_pgenerable Y pkg.quote_codes d t δ) (schedGate_supported Y d t δ A)
    (legibleOn_schedGate hL d t hδ) hdiv CA

/-- **T6′, mirror, one certificate.** The same on the scheduled lower gate.
Scope, grade, hypotheses as `theoremSS_fullLimit_oneCert`.
Source: [[route-sparse-schedule]] §8, §10 (the `w^-` half)
Kind: C
Fidelity: exact
Hyps: as `theoremSS_fullLimit_oneCert`: (c) `pkg.reflected`; (c) `hL`; (b) `CA`. -/
theorem theoremSS_fullLimit_oneCert_below {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    WeightedApprox (fun n => (schedGateBelow Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_general_oneCert pkg hcode hworldA hworldH hval hwd
    (schedGateBelow_pgenerable Y pkg.quote_codes d t δ) (schedGateBelow_supported Y d t δ A)
    (legibleOn_schedGateBelow hL d t hδ) hdiv CA

/-- **Theorem SS at full-limit grade from a certificate on the computable grid truth, general
gate.** As `theoremSS_fullLimit_general_oneCert`, with the `A`-side engine angle B's
`quoteSide_fullLimit_grid` (FAF's `lic_wubaff` through `feedbackTruthSequence`) and the certificate
asked of `gridTruth (realized H f X)` — the stream computable from `H`'s day-`f n` quotes — instead
of FAF's `Classical.choice`-selected mesh truth (findings F-B1). Under strict reflection the two
certificates coincide (`normalizedMeshTruth_eq_gridTruth_of_strict`).
Scope: one-way. e.d. family. Schedule: window-disjoint `DeferralFunction`. Grade: full limit.
Source: [[theorem-ss-streamlined]] §4 L3; FAF `thm:wubaff`; mandate K4; angle B's F-B1 repair
Kind: C
Fidelity: exact (agreement form, full limit; the timing condition asked of a computable stream; divergent-mass case only (`hdiv`) — the note's finite-mass clause is `unnormBias_bounded_of_summable` (`Analysis`), not part of this statement)
Hyps: (a) as `theoremSS_fullLimit_general_oneCert`; (c) `pkg.reflected`; (c) `hL`; (b) `C` (the grid-truth certificate; OPEN `exists_gridCertificate_of_marketComputation`). -/
theorem theoremSS_fullLimit_general_gridCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : WeightingSupportedOnDeferralImage G A d)
    (hL : LegibleOn H (fun n => (G n).denote A)) (hdiv : DivergentWeighting G A)
    (C : FeedbackTruth.FeedbackTruthComputation (gridTruth (realized H f X)) d) :
    WeightedApprox (fun n => (G n).denote A) (quoteSeq Y A) (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_of_quoteSide hcode hworldH hval hwd hdiv.1 hdiv.2 hsupp hL
    (quoteSide_fullLimit_grid pkg hworldA hG hdiv hwd.1 hsupp C)

/-- **T6′ from the grid certificate, scheduled quote gate.** `theoremSS_fullLimit_oneCert` with
the certificate on the computable grid truth `gridTruth (realized H f X)` — the certificate
form of record (repair round 1, audit r1 N1/N2): its (b) is exactly what the OPEN row
`exists_gridCertificate_of_marketComputation` would discharge, whereas the literal FAF
certificate of `_oneCert` pins a `Classical.choice`-selected world's mesh value (F-B1).
Scope, grade as `theoremSS_fullLimit_oneCert`.
Source: as `theoremSS_fullLimit_general_gridCert`
Kind: C
Fidelity: exact
Hyps: (c) `pkg.reflected`; (c) `hL`; (b) `C` (grid-truth certificate; OPEN). -/
theorem theoremSS_fullLimit_gridCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (C : FeedbackTruth.FeedbackTruthComputation (gridTruth (realized H f X)) d) :
    WeightedApprox (fun n => (schedGate Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_general_gridCert pkg hcode hworldA hworldH hval hwd
    (schedGate_pgenerable Y pkg.quote_codes d t δ) (schedGate_supported Y d t δ A)
    (legibleOn_schedGate hL d t hδ) hdiv C

/-! ## C. Grade 3: full limit from two certificates (angle B, restated over the record) -/

/-- **T6′ (angle B's, of record). Theorem SS, agreement form, full limit, on the scheduled quote
gate, both sides by citation of corrected 4.8.16.** With FAF's `cee` carrier
`hq : ExpectedFutureExpectationQuote H DPH f X Z` (`Z n` is `H`'s own `⌜𝔼^H_{f n}(X_n)⌝`), a
strictly increasing deferral `d` (window-disjointness is **not** consumed — findings F-B2), the
gate divergent on `A` and legible on `H`, and the two certificates `CA`, `CH`: the gate-weighted
average of `𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)` tends to `0`. Angle B's `theoremSS_fullLimit`,
restated over the record `schedGate`/`LegibleOn` through `Compat`. Compare
`theoremSS_fullLimit_oneCert`, which reaches the same conclusion without `hq` and `CH` (at the
price of window-disjointness, which the trader needs).
Scope: one-way. e.d. family. Schedule: strictly increasing `DeferralFunction`. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §0 Theorem SS (agreement form), §6 Assembly; lean-deference-038; [[route-sparse-schedule]] §10
Kind: C
Fidelity: exact (agreement form, full limit; divergent-mass case only (`hdiv`) — the note's finite-mass clause is `unnormBias_bounded_of_summable` (`Analysis`), not part of this statement)
Hyps: (a) `hworldA`, `hworldH`, `hd`, `hδ`, `hdiv`; (b) `hq` (FAF's `thm:cee` carrier `ExpectedFutureExpectationQuote`, taken as given for a general `H`; (a) only at `paperDP T`, `crossQuotePackage_paper_self`); (c) `pkg.reflected`; (c) `hL : LegibleOn H (schedGate-denote)`; (b) `CA`, `CH` (corrected 4.8.16's timing condition on each market's mesh; OPEN). -/
theorem theoremSS_fullLimit_twoCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGate Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    WeightedApprox (fun n => (schedGate Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) := by
  have hLB : B.LegibleOn H (fun n => (B.schedGate Y d t δ n).denote A) := by
    rw [B_legibleOn_eq, B_schedGate_denote_fun]
    exact hL
  have h := B.theoremSS_fullLimit pkg hq hworldA hworldH d hd t δ hδ (B_schedGate_divergent hdiv)
    hLB CA CH
  rwa [B_schedGate_denote_fun] at h

/-- **T6′, mirror, two certificates** (angle B's `theoremSS_fullLimit_below`, restated).
Scope, grade, hypotheses as `theoremSS_fullLimit_twoCert`.
Source: [[route-sparse-schedule]] §8, §10 (the `w^-` half)
Kind: C
Fidelity: exact
Hyps: as `theoremSS_fullLimit_twoCert`. -/
theorem theoremSS_fullLimit_twoCert_below {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGateBelow Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    WeightedApprox (fun n => (schedGateBelow Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) := by
  have hLB : B.LegibleOn H (fun n => (B.schedGateBelow Y d t δ n).denote A) := by
    rw [B_legibleOn_eq, B_schedGateBelow_denote_fun]
    exact hL
  have h := B.theoremSS_fullLimit_below pkg hq hworldA hworldH d hd t δ hδ
    (B_schedGateBelow_divergent hdiv) hLB CA CH
  rwa [B_schedGateBelow_denote_fun] at h

/-! ## D. Scheduled soft Total Trust (T7): the `∃ᶠ` form of record and the `∀ᶠ` form -/

/-- **The scheduled, averaged above-threshold inequality, eventually form**: for every `ρ > 0`,
eventually the `w`-weighted average of `h` through day `n` is at least `t − ρ`. This is the
record's `SchedThresholdAbove` (angle A's and the mandate's, `∃ᶠ`) with the filter upgraded to
`∀ᶠ`: what a full limit buys (`schedThresholdAboveEv_of_weightedApprox`). It is angle B's
`SchedThresholdAbove` under the record's name for the grade (findings R-1: the two angles used
one name for the two filters). Named with `Sched` and never `TotalTrust`: a variant of
def-lattice's per-day `ThresholdIneqAbove` (averaged along a real gate, scheduled).
Source: [[theorem-ss-streamlined]] §8; lean-deference-039 (`total_trust_above_ramp`); [[route-sparse-schedule]] §8
Kind: D
Fidelity: variant: averaged along the gate, scheduled, eventually — not def-lattice's per-day `ThresholdIneqAbove`
Hyps: n/a -/
def SchedThresholdAboveEv (w h : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, t - ρ ≤ weightedAverage w h n

/-- **The scheduled, averaged below-threshold inequality, eventually form.**
Source: [[theorem-ss-streamlined]] §8
Kind: D
Fidelity: variant: averaged, scheduled, eventually
Hyps: n/a -/
def SchedThresholdBelowEv (w h : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, weightedAverage w h n ≤ t + ρ

/-- The eventually form implies the frequently form of record.
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem SchedThresholdAboveEv.frequently {w h : ℕ → ℝ} {t : ℝ} (H : SchedThresholdAboveEv w h t) :
    SchedThresholdAbove w h t :=
  fun ρ hρ => (H ρ hρ).frequently

/-- The eventually form implies the frequently form of record (below).
Source: none: infrastructure (reconciler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem SchedThresholdBelowEv.frequently {w h : ℕ → ℝ} {t : ℝ} (H : SchedThresholdBelowEv w h t) :
    SchedThresholdBelow w h t :=
  fun ρ hρ => (H ρ hρ).frequently

/-- Angle B's `SchedThresholdAbove` (rational threshold) is the record's eventually form.
Source: none: infrastructure (reconciler; findings R-1)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedThresholdAbove_iff {w h : ℕ → ℝ} {t : ℚ} :
    B.SchedThresholdAbove w h t ↔ SchedThresholdAboveEv w h t :=
  Iff.rfl

/-- Angle B's `SchedThresholdBelow` (rational threshold) is the record's eventually form.
Source: none: infrastructure (reconciler; findings R-1)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem B_schedThresholdBelow_iff {w h : ℕ → ℝ} {t : ℚ} :
    B.SchedThresholdBelow w h t ↔ SchedThresholdBelowEv w h t :=
  Iff.rfl

/-- **From a full-limit agreement to the eventually above-threshold inequality**: `a ≥ t` on the
support, `w ≥ 0` divergent, `a ≈_w h` ⟹ `SchedThresholdAboveEv w h t`. Angle A's
`schedThresholdAbove_eventually_of_fullLimit` under the record's name.
Source: [[theorem-ss-streamlined]] §8; lean-deference-039
Kind: L
Fidelity: exact
Hyps: (a) none (`hfull` is the full-limit input) -/
theorem schedThresholdAboveEv_of_weightedApprox {w a h : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → t ≤ a i)
    (hfull : WeightedApprox w a h) : SchedThresholdAboveEv w h t :=
  schedThresholdAbove_eventually_of_fullLimit hw hdiv hsupp hfull

/-- **From a full-limit agreement to the eventually below-threshold inequality**: `a ≤ t` on the
support, `w ≥ 0` divergent, `a ≈_w h` ⟹ `SchedThresholdBelowEv w h t`.
Source: [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedThresholdBelowEv_of_weightedApprox {w a h : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → a i ≤ t)
    (hfull : WeightedApprox w a h) : SchedThresholdBelowEv w h t := by
  intro ρ hρ
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  have hfull' : Tendsto (weightedAverage w (fun i => a i - h i)) atTop (𝓝 0) := hfull
  have hsm := (Metric.tendsto_nhds.1 hfull') ρ hρ
  filter_upwards [hev, hsm] with n h2 h1
  have hle : weightedAverage w a n ≤ t := weightedAverage_le_of_support hw hsupp h2
  rw [Real.dist_eq, sub_zero, weightedAverage_sub w a h h2.ne', abs_lt] at h1
  linarith [h1.1]

/-- **T7 (headline, of record). Scheduled soft Total Trust, above-threshold inequality, as a
conclusion, frequently.** Under T6's hypotheses: for every `ρ > 0`, frequently
`(∑_{i≤n} w_i 𝔼^H_i(X_i)) / ∑_{i≤n} w_i ≥ t − ρ` on the gate
`w_i = 1[i ∈ im d] · Ind_δ(𝔼^A_i(⌜𝔼^H_{f i}(X_i)⌝) > t)` — the human's present credence, averaged
over the scheduled days on which the forecaster quotes above `t`, has **limsup at least `t`**
(the `∃ᶠ` grade; the sources' "liminf ≥ t − ε − δ" is the eventually form below).
Angle A's theorem, restated. The forcing is in the conclusion: no per-day hypothesis.
Scope: one-way. e.d. family. Schedule: window-disjoint `DeferralFunction`. Grade: limit point
(frequently); `schedThresholdAboveEv_oneCert` upgrades to eventually under a certificate.
Content region: at `t ≤ 0` the conclusion is trivially true for `h ∈ [0,1]`; at `t ≥ 1 + δ`
`hdiv` is unsatisfiable; content lives in `0 < t < 1`.
Witness (`Witnesses`): full package at a content threshold, `schedThresholdAbove_paper_self_top`
(same market, `X ≡ 𝟙(⊤)`); N− for content (`𝔼^H_n(𝟙(⊤)) → 1` makes the conclusion immediate).
Source: [[theorem-ss-streamlined]] §8; lean-deference-039 (`total_trust_above_ramp`, with its `hbias`/`hbdd` discharged); [[route-sparse-schedule]] §8; root-deference-050's "liminf ≥ t − ε − δ"
Kind: C
Fidelity: variant: averaged along the gate, scheduled, frequently (not def-lattice's per-day `ThresholdIneqAbove`; T8 shows the per-day form is not implied)
Hyps: as `theoremSS_limitPoint`: (c) `pkg.reflected`; (c) `hL`. -/
theorem schedThresholdAbove_of_theoremSS {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A) :
    SchedThresholdAbove (fun n => (schedGate Y d t δ n).denote A) (fun n => (X n).expect H n) t :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.schedThresholdAbove_of_theoremSS
    pkg hcode hworldA hworldH hval hwd t hδ hL hdiv

/-- **T7, mirror (of record). Scheduled soft Total Trust, below-threshold inequality**, frequently,
on the lower gate. Angle A's theorem, restated.
Scope: one-way. Grade: limit point.
Source: [[theorem-ss-streamlined]] §8
Kind: C
Fidelity: variant: averaged, scheduled, frequently
Hyps: (c) `pkg.reflected`; (c) `hL`. -/
theorem schedThresholdBelow_of_theoremSS {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A) :
    SchedThresholdBelow (fun n => (schedGateBelow Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.schedThresholdBelow_of_theoremSS
    pkg hcode hworldA hworldH hval hwd t hδ hL hdiv

/-- **T7′ (of record). Scheduled soft Total Trust, above-threshold, eventually, from one
certificate.** Under `theoremSS_fullLimit_oneCert`'s hypotheses: for every `ρ > 0`, eventually the
gate-weighted average of `𝔼^H_n(X_n)` on the scheduled days where `A` quotes above `t` is at
least `t − ρ` — lean-deference-039's `total_trust_above_ramp` with `hbias`/`hbdd` replaced by
FAF's criterion (angle B's engine on the `A` side, angle A's trader on the `H` side).
Scope: one-way. e.d. family. Schedule: window-disjoint `DeferralFunction`. Grade: full limit
(eventually).
Source: [[theorem-ss-streamlined]] §8 Corollaries; lean-deference-039; [[route-sparse-schedule]] §8
Kind: C
Fidelity: variant: averaged along the scheduled gate, eventually; not def-lattice's per-day `ThresholdIneqAbove`
Hyps: as `theoremSS_fullLimit_oneCert`: (c) `pkg.reflected`; (c) `hL`; (b) `CA`. -/
theorem schedThresholdAboveEv_oneCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    SchedThresholdAboveEv (fun n => (schedGate Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdAboveEv_of_weightedApprox (fun i => (schedGate_mem_Icc Y d t hδ A i).1) hdiv.2
    (fun i hi => ((schedGate_pos_iff Y d t hδ A i).1 hi).2.le)
    (theoremSS_fullLimit_oneCert pkg hcode hworldA hworldH hval hwd t hδ hL hdiv CA)

/-- **T7′, mirror, one certificate.** The below-threshold inequality, eventually, on the lower gate.
Scope, grade, hypotheses as `schedThresholdAboveEv_oneCert`.
Source: [[theorem-ss-streamlined]] §8
Kind: C
Fidelity: variant: averaged, scheduled, eventually
Hyps: (c) `pkg.reflected`; (c) `hL`; (b) `CA`. -/
theorem schedThresholdBelowEv_oneCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    SchedThresholdBelowEv (fun n => (schedGateBelow Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdBelowEv_of_weightedApprox (fun i => (schedGateBelow_mem_Icc Y d t hδ A i).1)
    hdiv.2 (fun i hi => ((schedGateBelow_pos_iff Y d t hδ A i).1 hi).2.le)
    (theoremSS_fullLimit_oneCert_below pkg hcode hworldA hworldH hval hwd t hδ hL hdiv CA)

/-- **T7′ from two certificates** (angle B's `theoremSS_schedThresholdAbove`, over the record):
the eventually above-threshold inequality under `theoremSS_fullLimit_twoCert`'s hypotheses.
Scope: one-way. Schedule: strictly increasing `DeferralFunction`. Grade: full limit (eventually).
Source: [[theorem-ss-streamlined]] §8 Corollaries; lean-deference-039
Kind: C
Fidelity: variant: averaged along the scheduled gate, eventually
Hyps: as `theoremSS_fullLimit_twoCert`: (c) `pkg.reflected`; (c) `hL`; (b) `CA`, `CH`. -/
theorem schedThresholdAboveEv_twoCert {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGate Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    SchedThresholdAboveEv (fun n => (schedGate Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdAboveEv_of_weightedApprox (fun i => (schedGate_mem_Icc Y d t hδ A i).1) hdiv.2
    (fun i hi => ((schedGate_pos_iff Y d t hδ A i).1 hi).2.le)
    (theoremSS_fullLimit_twoCert pkg hq hworldA hworldH d hd t δ hδ hdiv hL CA CH)

end Cleanroom.Fa.FaForcingTrader
