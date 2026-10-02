import Cleanroom.Fa.FaForcingTrader.B.Defs
import Cleanroom.Fa.FaTheoremA.Analysis
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Construction.Statistics.FeedbackTruth

/-!
# `fa-forcing-trader` · angle B · Feedback: Theorem SS at full-limit grade by two citations

Angle B of [[fa-forcing-trader-mandate]]: both halves of Theorem SS by FAF's corrected
4.8.16, `FeedbackTruth.luv_wubexp_ofComputation` (`thm:wubexp`, with PE2's support clause
where it belongs), each applied to a market's own quote family of the human's future credence,
plus `cee` (`lic_expected_future_expectations`, `thm:cee`) for the human's present credence —
[[theorem-ss-streamlined]]'s L1 + L2 + L3, assembled by same-weighting additivity (§6).

* `quoteSide_fullLimit` — **the one engine**: for any inductor `P` over `DP`, any
  `CrossQuotePackage H DP f X Y` (a quote family `Y` of `P`'s language reflected at `H`'s realized
  day-`f n` expectations), any generable divergent weighting of `P` supported on a strictly
  increasing deferral `d`, and FAF's delayed-truth certificate `C` on the normalized mesh of the
  quote family along `d`: the weighted bias of `P`'s quotes against the realized values is a
  **full limit** `0`. At `P = A` with `pkg` this is L3; at `P = H` with FAF's own `cee` carrier it
  is L2.
* `selfSide_fullLimit` — L1 + L2 on `H`: `𝔼^H_n(X_n) ≈_w 𝔼^H_{f n}(X_n)`.
* `theoremSS_fullLimit_general` / **`theoremSS_fullLimit`** (T6′) — the agreement form of Theorem
  SS at full-limit grade on the scheduled gate, under (L) and the two certificates.
* `SchedThresholdAbove` / **`theoremSS_schedThresholdAbove`** (T7′) — scheduled soft Total Trust,
  above-threshold inequality, as an `∀ᶠ` conclusion; and the dual below-threshold form.

**Grades.** Every hypothesis is (a) except: `pkg.reflected` (c) (Σ₁-completeness of `Γ_A` about
`H`, `li-quote-lane`), `hL : LegibleOn H …` (c) (the corpus's (L), T11), and the two certificates
`CA`, `CH` (b): FAF's `FeedbackTruthComputation` on the normalized mesh — corrected 4.8.16's
timing condition rendered at the machine model (vq-wiki-046 Lemma 1(b), on the mesh, vq-wiki-2-002,
mandate K4). `Certificate.lean` is the attempt to inhabit them. **No N+ witness of the full
hypothesis package ships** (see `fa-forcing-trader-report-B.md`); the headline is a conditional of
record whose every hypothesis is a named FAF or package object.

**What the citation route does not consume.** FAF's `luv_wubexp_ofComputation` takes
`StrictlyIncreasingDeferral d` and `WeightingSupportedOnDeferralImage W P d`; v3's window
condition `f (d k) < d (k+1)` never enters — the certificate `C` (the value of component `d k`
available at `⟨k, d (k+1)⟩`) is where the lookahead window lives. So the headlines here take only
`hd : StrictlyIncreasingDeferral d`; `WindowDisjoint f d` implies it (`WindowDisjoint.strict`).

Scope: one-way (`H` reads `A`'s quote only through (L); `A` never reads `H`'s prices). e.d. family
`X : ℕ → LUV` (the note's actual statement). Grade: full limit. The LI content enters only
through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
-/

namespace Cleanroom.Fa.FaForcingTrader.B

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice
open Filter Topology

/-! ## A. The certificate type and the share bound of a singleton -/

/-- The share norm of the singleton combination `0 + 1·X` is `1` in every market.
Source: none: infrastructure (`li-asymp-calc` `l1Norm_ofLUV`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem shareNorm_ofLUV (X : LUV) (P : History) : (LUVCombination.ofLUV X).shareNorm P = 1 := by
  simp [LUVCombination.shareNorm, LUVCombination.ofLUV]

/-- **The delayed-truth certificate of a quote family along a schedule**: FAF's
`FeedbackTruth.FeedbackTruthComputation` (corrected 4.8.16's timing condition at the machine
model: the value of component `d k` is written, as a canonical rational code, at the paired index
`⟨k, d (k+1)⟩` by a `MachineDigits`-metered program) for the **normalized mesh truth** of the
singleton family `n ↦ 0 + 1·Y n` at share bound `1`. This is the mandate's `C` (angle B), stated
once so that both sides of Theorem SS name the same object. Its `truth` is
`normalizedMeshTruth (ofLUV ∘ Y) P DP hworld 1 n = (1/2) · (mesh value of `Y n` at precision `n+1`
in `theoryWorld DP hworld`)` — a `Classical.choice`-selected world's valuation; see
`Certificate.lean` for why that is not a computable stream over `pkg.reflected` alone and what
replaces it.
Source: mandate § Attempt angles (B), K4; FAF `thm:wubexp` (`FeedbackTruthComputation`); vq-wiki-046 Lemma 1(b); vq-wiki-2-002
Kind: D
Fidelity: exact (FAF's own premise, at `b = 1`)
Hyps: n/a -/
abbrev QuoteCertificate (P : History) (DP : DeductiveProcess) (Y : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (d : DeferralFunction) : Type :=
  FeedbackTruth.FeedbackTruthComputation
    (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n)) P DP hworld 1) d

/-! ## B. The engine: one market's quote of the human's future, full limit -/

/-- **L3 / L2 (the one engine).** For `[IsLogicalInductor P DP]`, a quote package
`pkg : CrossQuotePackage H DP f X Y` (`Y n` names `𝔼^H_{f n}(X n)` and `DP`'s completed theory
values it there), every stage of `DP` satisfiable, a generable weighting `W` of `P`'s market,
divergent in `P`'s realized prices and supported on the strictly increasing deferral `d`, and the
certificate `C`: the `W`-weighted average of
`𝔼^P_n(Y_n) − 𝔼^H_{f n}(X_n)` tends to `0` — a **full limit** (`WeightedApprox`), two-sided.
This is FAF's `luv_wubexp_ofComputation` on `As := ofLUV ∘ Y` with the package's three bridges
(`boundedSequence`, `worldValued`, `determinedViaTheory`), the share bound `1`, and the market
rewritten by `ofLUV_expect`. At `P = A` it is [[theorem-ss-streamlined]] §4 Lemma L3 ("no
relativization is involved"); at `P = H` with FAF's `cee` carrier it is §3's L2.
Scope: one-way (`P` reads nothing of `H`'s prices; `H` enters through the LUV `Y n` of `P`'s
language and through `C`). e.d. family. Schedule: strictly increasing `DeferralFunction`
(window-disjointness not consumed — module docstring). Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §4 Lemma L3, §3 Lemma L2 (vq-wiki-050, vq-wiki-047); lean-deference-038; FAF `thm:wubexp`
Kind: C
Fidelity: exact (L3 as stated; corrected 4.8.16 with PE2's support clause)
Hyps: (a) `hworld`, `hW`, `hdiv`, `hd`, `hsupp`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_P` about `H` — li-quote-lane); (b) `C` (corrected 4.8.16's timing condition on the mesh, LI 4.8.16 / FAF `thm:wubexp`). -/
theorem quoteSide_fullLimit {H P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DP f X Y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W P)
    {d : DeferralFunction} (hd : StrictlyIncreasingDeferral d)
    (hsupp : WeightingSupportedOnDeferralImage W P d)
    (C : QuoteCertificate P DP Y hworld d) :
    WeightedApprox (fun i => (W i).denote P) (quoteSeq Y P) (realized H f X) := by
  have hshare : ∀ n, (LUVCombination.ofLUV (Y n)).shareNorm P ≤ ((1 : ℚ) : ℝ) := by
    intro n
    rw [shareNorm_ofLUV]
    norm_num
  have h := FeedbackTruth.luv_wubexp_ofComputation (pkg.boundedSequence P) pkg.worldValued
    (pkg.determinedViaTheory P) 1 hshare hW hdiv hd hworld C hsupp
  rw [weightedApprox_iff_weightedBias]
  simpa only [AsympEq, sub_zero, ofLUV_expect] using h

/-- **L1 + L2 on the human's market.** For `[IsLogicalInductor H DPH]`, FAF's `cee` carrier
`hq : ExpectedFutureExpectationQuote H DPH f X Z` (`Z n` is `H`'s own quote `⌜𝔼^H_{f n}(X n)⌝`,
e.c., reflected, with the fixed-portfolio law), a generable divergent weighting `G` of `H`'s
market supported on `d`, and the certificate `CH` for `Z`:
the `G`-weighted average of `𝔼^H_n(X_n) − 𝔼^H_{f n}(X_n)` tends to `0`. L1 is FAF's
`lic_expected_future_expectations` (`𝔼^H_n(X_n) ≈ₙ 𝔼^H_n(Z_n)`, per-day, carried to `≈_w` by the
donor rule `DivergentWeighting.weightedApprox`); L2 is `quoteSide_fullLimit` at `P = H` on
`hq.toCross`. This is trust-lab-2-042's H1/H2/H3 with H1–H3 as FAF instances.
Scope: same market (`H` alone); nothing here reads `A`. e.d. family. Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §2 (L1, `cee` "free"), §3 (L2, 4.8.16 at `H`); trust-lab-2-042; FAF `thm:cee`, `thm:wubexp`
Kind: C
Fidelity: exact (L1 + L2; (S2′)/(R′) of the note are FAF's own `hq` and the plain trader class)
Hyps: (a) `hq` (FAF's `thm:cee` premise — the Σ₁ quotation of `H`'s own run; a theorem at `paperDP T`, `li-quote-lane` `crossQuotePackage_paper_self`), `hworldH`, `hG`, `hdivH`, `hd`, `hsuppH`; (b) `CH` (corrected 4.8.16's timing condition on `H`'s mesh). -/
theorem selfSide_fullLimit {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Z : ℕ → LUV} (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    {G : ℕ → EF} (hG : PGenerableWeighting G) (hdivH : DivergentWeighting G H)
    {d : DeferralFunction} (hd : StrictlyIncreasingDeferral d)
    (hsuppH : WeightingSupportedOnDeferralImage G H d)
    (CH : QuoteCertificate H DPH Z hworldH d) :
    WeightedApprox (fun i => (G i).denote H) (fun n => (X n).expect H n) (realized H f X) := by
  have hL2 : WeightedApprox (fun i => (G i).denote H) (quoteSeq Z H) (realized H f X) :=
    quoteSide_fullLimit (ExpectedFutureExpectationQuote.toCross hq) hworldH hG hdivH hd hsuppH CH
  have hcee : AsympEq (fun n => (X n).expect H n) (fun n => (Z n).expect H n) :=
    lic_expected_future_expectations H DPH f X Z hworldH hq
  have hL1 : WeightedApprox (fun i => (G i).denote H) (fun n => (X n).expect H n) (quoteSeq Z H) :=
    DivergentWeighting.weightedApprox hdivH hcee
  exact WeightedApprox.trans hdivH.2 hL1 hL2

/-! ## C. Theorem SS, agreement form, full limit (T6′) -/

/-- **Theorem SS (agreement form, full limit) on an arbitrary legible weighting.** Two inductors
`A` over `DPA`, `H` over `DPH`; `pkg` ties `A`'s quote family `Y` to `H`'s realized day-`f n`
expectations; `hq` is `H`'s own `cee` carrier for the same source family; `W` is a generable
weighting of `A`'s market, divergent there and supported on `d`, **legible on `H`** (`hL`: some
generable weighting of `H`'s market denotes the same numbers); `CA`, `CH` the two certificates.
Then the `W`-weighted average of
`𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)` tends to `0`: L3 at `A`, L1 + L2 at `H` on the same
numbers (`DivergentWeighting.transfer`, `WeightingSupportedOnDeferralImage.transfer`), chained by
`WeightedApprox.trans` — [[theorem-ss-streamlined]] §6's assembly, agreement form.
Scope: one-way (`H` reads `A`'s quote only through (L); `A` never reads `H`'s prices). e.d. family.
Schedule: strictly increasing `DeferralFunction`. Grade: full limit, two-sided.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §0 Theorem SS (agreement form), §6 Assembly (vq-wiki-050); lean-deference-038; [[route-sparse-schedule]] §7
Kind: C
Fidelity: exact (agreement form; the Tower form needs `li-quote-lane`'s `readability`, not done here)
Hyps: (a) `hq`, `hworldA`, `hworldH`, `hW`, `hdiv`, `hd`, `hsupp`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hL : LegibleOn H …` (the corpus's (L); no two-market inhabitant known, T11); (b) `CA`, `CH` (corrected 4.8.16's timing condition on each market's mesh). -/
theorem theoremSS_fullLimit_general {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W A)
    {d : DeferralFunction} (hd : StrictlyIncreasingDeferral d)
    (hsupp : WeightingSupportedOnDeferralImage W A d)
    (hL : LegibleOn H (fun n => (W n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    WeightedApprox (fun n => (W n).denote A) (quoteSeq Y A) (fun n => (X n).expect H n) := by
  obtain ⟨G, hG, hGeq⟩ := hL
  have hA : WeightedApprox (fun n => (W n).denote A) (quoteSeq Y A) (realized H f X) :=
    quoteSide_fullLimit pkg hworldA hW hdiv hd hsupp CA
  have hH : WeightedApprox (fun n => (G n).denote H) (fun n => (X n).expect H n)
      (realized H f X) :=
    selfSide_fullLimit hq hworldH hG (DivergentWeighting.transfer hGeq hdiv) hd
      (WeightingSupportedOnDeferralImage.transfer d hGeq hsupp) CH
  have hfun : (fun n => (G n).denote H) = fun n => (W n).denote A := funext hGeq
  rw [hfun] at hH
  exact WeightedApprox.trans hdiv.2 hA hH.symm

/-- **T6′ (headline). Theorem SS, agreement form, full limit, on the scheduled quote gate.** For
`[IsLogicalInductor A DPA]`, `[IsLogicalInductor H DPH]`, the quote package `pkg`, `H`'s `cee`
carrier `hq`, every stage of both processes satisfiable, a strictly increasing deferral `d`,
rationals `t`, `δ > 0`, the gate `w_n = 1[n ∈ im d] · Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t)`
divergent in `A`'s realized prices, (L) for that gate, and the two certificates:
the gate-weighted average of `𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)` tends to `0`
(two-sided full limit) — [[theorem-ss-streamlined]]'s Theorem SS in agreement form, with its
Tower form left to `li-quote-lane`'s `readability` (which costs (L) again). The gate's `A`-legality
is `schedGate_pgenerable` (FAF's `PGenerableWeighting.mul` of the schedule indicator and
`fa-theorem-a`'s T2 ramp certificate); its support on `im d` is `schedGate_supported`.
Scope: one-way (`H` reads `A`'s quote only through (L); `A` never reads `H`'s prices). e.d. family.
Schedule: strictly increasing `DeferralFunction` (v3's window-disjointness not consumed; see the
module docstring and findings). Grade: full limit.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Junk width: at `δ = 0` the gate is `≡ 0` (`fa-theorem-a`'s `not_divergent_zero_width`) and `hdiv`
is unsatisfiable, so the theorem is vacuous there, not false; `hδ` keeps the semantic reading.
Source: [[theorem-ss-streamlined]] §0 Theorem SS, agreement form (vq-wiki-050); lean-deference-038; [[route-sparse-schedule]] §10 Theorem SS (clean form)
Kind: C
Fidelity: exact (agreement form, full limit; the note's statement) — stronger than angle A's T6 (limit point) at the price of (b) `CA`, `CH`
Hyps: (a) `hq`, `hworldA`, `hworldH`, `hd`, `hdiv`, `hδ`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hL : LegibleOn H (schedGate-denote)` (the corpus's (L); no two-market inhabitant known, T11); (b) `CA`, `CH` (corrected 4.8.16's timing condition on the mesh, LI Thm 4.8.16 / FAF `thm:wubexp`; `Certificate.lean`). -/
theorem theoremSS_fullLimit {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (_hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGate Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    WeightedApprox (fun n => (schedGate Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_general pkg hq hworldA hworldH (schedGate_pgenerable Y pkg.quote_codes d t δ)
    hdiv hd (schedGate_supported Y d t δ A) hL CA CH

/-- **T6′, dual gate.** The same on `w⁻_n = 1[n ∈ im d] · Ind_δ(a_n < t)`.
Scope, grade, hypotheses as `theoremSS_fullLimit`.
Source: [[route-sparse-schedule]] §8, §10 (the `w^-` half)
Kind: C
Fidelity: exact
Hyps: as `theoremSS_fullLimit`. -/
theorem theoremSS_fullLimit_below {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (_hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGateBelow Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    WeightedApprox (fun n => (schedGateBelow Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_general pkg hq hworldA hworldH
    (schedGateBelow_pgenerable Y pkg.quote_codes d t δ) hdiv hd
    (schedGateBelow_supported Y d t δ A) hL CA CH

/-! ## D. Scheduled soft Total Trust as an `∀ᶠ` conclusion (T7′) -/

/-- **Scheduled soft Total Trust, above-threshold inequality, `∀ᶠ` form**: for every `ρ > 0`,
eventually the `w`-weighted average of `h` is at least `t − ρ`. Named with `Sched` (averaged along
the scheduled weighting `w`, not per day) and never `TotalTrust`: it is a *variant* of
`def-lattice`'s per-day `ThresholdIneqAbove` — the weight is a real gate and the average is along
`w` (mandate T7's bridge note).
Source: [[theorem-ss-streamlined]] §8; lean-deference-039 (`total_trust_above_ramp`); [[route-sparse-schedule]] §8
Kind: D
Fidelity: variant: averaged along `w`, scheduled, `∀ᶠ` (full-limit grade); not `def-lattice`'s per-day `ThresholdIneqAbove`
Hyps: n/a -/
def SchedThresholdAbove (w h : ℕ → ℝ) (t : ℚ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, (t : ℝ) - ρ ≤ weightedAverage w h n

/-- The below-threshold dual: eventually the average is at most `t + ρ`.
Source: [[theorem-ss-streamlined]] §8; [[route-sparse-schedule]] §8
Kind: D
Fidelity: variant: averaged along `w`, scheduled, `∀ᶠ`
Hyps: n/a -/
def SchedThresholdBelow (w h : ℕ → ℝ) (t : ℚ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, weightedAverage w h n ≤ (t : ℝ) + ρ

/-- **From a full-limit agreement to the above-threshold inequality.** If `a_i ≥ t` wherever
`w_i > 0`, `w ≥ 0` divergent, and `a ≈_w h`, then eventually `weightedAverage w h ≥ t − ρ`:
`weightedAverage w a n ≥ t` on positive mass (`fa-theorem-a`'s `le_weightedAverage_of_support`)
and `weightedAverage w h n = weightedAverage w a n − weightedAverage w (a − h) n`
(FAF's `weightedAverage_sub`), the last term eventually `< ρ`.
Source: [[theorem-ss-streamlined]] §8 ("both one-sided inequalities of scheduled soft Total Trust follow"); root-deference-050 ("liminf ≥ t − ε − δ")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedThresholdAbove_of_weightedApprox {w a h : ℕ → ℝ} {t : ℚ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → (t : ℝ) ≤ a i)
    (happ : WeightedApprox w a h) : SchedThresholdAbove w h t := by
  intro ρ hρ
  have h1 : ∀ᶠ n in atTop, |weightedAverage w (fun i => a i - h i) n| < ρ := by
    have := (Metric.tendsto_nhds.1 happ) ρ hρ
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [h1, eventually_prefixSum_pos hdiv] with n hn hpos
  have h2 : (t : ℝ) ≤ weightedAverage w a n := le_weightedAverage_of_support hw hsupp hpos
  rw [weightedAverage_sub w a h hpos.ne'] at hn
  have h3 := (abs_lt.1 hn).2
  linarith

/-- The dual: `a_i ≤ t` on the support and `a ≈_w h` give the below-threshold inequality.
Source: [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedThresholdBelow_of_weightedApprox {w a h : ℕ → ℝ} {t : ℚ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → a i ≤ (t : ℝ))
    (happ : WeightedApprox w a h) : SchedThresholdBelow w h t := by
  intro ρ hρ
  have h1 : ∀ᶠ n in atTop, |weightedAverage w (fun i => a i - h i) n| < ρ := by
    have := (Metric.tendsto_nhds.1 happ) ρ hρ
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [h1, eventually_prefixSum_pos hdiv] with n hn hpos
  have h2 : weightedAverage w a n ≤ (t : ℝ) := weightedAverage_le_of_support hw hsupp hpos
  rw [weightedAverage_sub w a h hpos.ne'] at hn
  have h3 := (abs_lt.1 hn).1
  linarith

/-- **T7′ (headline). Scheduled soft Total Trust, above-threshold, as a conclusion, `∀ᶠ`.** Under
`theoremSS_fullLimit`'s hypotheses: for every `ρ > 0`, eventually the gate-weighted average of
`H`'s present credence `𝔼^H_n(X_n)` on the days `A` advertises above `t` (on the schedule) is at
least `t − ρ`. From T6′ and the gate's support law `schedGate_pos_imp` (positive weight ⟹
`t < 𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝)`). This is lean-deference-039's `total_trust_above_ramp` with
`hbias`/`hbdd` replaced by FAF's criterion inside `luv_wubexp_ofComputation`.
Scope: one-way. e.d. family. Schedule: strictly increasing `DeferralFunction`. Grade: full limit
(`∀ᶠ`, not angle A's `∃ᶠ`).
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[theorem-ss-streamlined]] §8 Corollaries (vq-wiki-050); lean-deference-039; [[route-sparse-schedule]] §8
Kind: C
Fidelity: variant: averaged along the scheduled gate, `∀ᶠ`; not `def-lattice`'s per-day `ThresholdIneqAbove` (angle A's T8 witnesses the gap)
Hyps: as `theoremSS_fullLimit`: (c) `pkg.reflected`, (c) `hL`, (b) `CA`, `CH`. -/
theorem theoremSS_schedThresholdAbove {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGate Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    SchedThresholdAbove (fun n => (schedGate Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdAbove_of_weightedApprox (fun i => (schedGate_mem_Icc Y d hδ A i).1) hdiv.2
    (fun _ hi => (schedGate_pos_imp Y d hδ A hi).2.le)
    (theoremSS_fullLimit pkg hq hworldA hworldH d hd t δ hδ hdiv hL CA CH)

/-- **T7′, dual. Scheduled soft Total Trust, below-threshold.** On the days `A` advertises below
`t`, eventually the gate-weighted average of `𝔼^H_n(X_n)` is at most `t + ρ`.
Scope, grade, hypotheses as `theoremSS_schedThresholdAbove` (with the dual gate).
Source: [[theorem-ss-streamlined]] §8; [[route-sparse-schedule]] §8 (the `w^-` inequality)
Kind: C
Fidelity: variant: averaged along the scheduled dual gate, `∀ᶠ`
Hyps: as `theoremSS_fullLimit_below`. -/
theorem theoremSS_schedThresholdBelow {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH]
    {f : DeferralFunction} {X Y Z : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hq : ExpectedFutureExpectationQuote H DPH f X Z)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (d : DeferralFunction) (hd : StrictlyIncreasingDeferral d) (t δ : ℚ) (hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A)
    (hL : LegibleOn H (fun n => (schedGateBelow Y d t δ n).denote A))
    (CA : QuoteCertificate A DPA Y hworldA d) (CH : QuoteCertificate H DPH Z hworldH d) :
    SchedThresholdBelow (fun n => (schedGateBelow Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdBelow_of_weightedApprox (fun i => (schedGateBelow_mem_Icc Y d hδ A i).1) hdiv.2
    (fun _ hi => (schedGateBelow_pos_imp Y d hδ A hi).2.le)
    (theoremSS_fullLimit_below pkg hq hworldA hworldH d hd t δ hδ hdiv hL CA CH)

end Cleanroom.Fa.FaForcingTrader.B
