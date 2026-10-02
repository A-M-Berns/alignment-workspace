import Cleanroom.Found.DefLattice.Notions
import LogicalInduction.Properties.Calibration
import LogicalInduction.Properties.Pseudorandomness

/-!
# `trust-merge` · Defs: cross-agent LUV-Total-Trust, two grades; the merge expert's notions

Package `Cleanroom.Trust.TrustMerge` ([[trust-merge-mandate]]). This file holds the definitions of
record; theorem files import it.

**T1 — the definition of record** (trust-lab-002, root-deference-061, trust-lab-2-018). "Inductor
`N` LUV-Total-Trusts inductor `M`" is read over `def-lattice`'s `Expert DP` (`M`'s history `E.A`,
its deferral `E.f`, its estimate `E.estimate X n = (X n).expect E.A (E.f n)`), the novice being
the market `P` over the process `DP`:

* `Observable DP E` — clause (i), **quotability**: every e.c. source `X` has an e.c. LUV `Y` of
  `N`'s language valued, in every completed-theory world of `DP`, at `M`'s estimate
  (`Reflects DP E X Y`). FAF's `EF` has no constructor for a posted number (trust-lab-2-009,
  settled in `li-quote-lane`), so "`M`'s estimates are `ℙ^N`-generable" is rendered as: they are
  *named* by decided sentences of `N`'s process; generability of the *reader's estimate of the
  quote* then follows (`ledgerFeature_pgenerable`). Without (i), `CondTower` is vacuously true for
  an unquotable expert (`def-lattice`'s own warning). (i) supplies quotes of the *estimate*; (ii)'s
  `CondTower` is instantiated only at `CondQuote` *product* packages `⌜X w⌝`, `⌜E*(X) w⌝`, which
  (i) does not by itself provide — so `LUVTotalTrustDay` still holds vacuously for an expert whose
  estimates are quotable but whose products are not (audit r1, adversarial N5). (i) is a
  necessary condition for (ii) to have content, not a sufficient one.
* `LUVTotalTrustDay P DP E` — clause (ii) at the **per-day** grade: `Observable ∧ CondTower`, the
  lab's definition as written (`𝔼^N_n(⌜X_n w_{f n}⌝) ≈ₙ 𝔼^N_n(⌜M*(X_n) w_{f n}⌝)` for every
  `N`-generable `[0,1]` weight, within FAF's mesh slack; weight at the deferred day, def-lattice F2).
* `LUVTotalTrustAvg P DP E` — clause (ii) at the **averaged** grade: `Observable` and, for every
  quoted pair `(X, Y)` and every `N`-generable divergent weighting supported on `im E.f`, `N`'s
  expectation of the quote is `w`-unbiased for `M`'s realized estimate (FAF's `weightedBias`): the
  grade the feedback theorems `thm:wub`/`thm:wubexp` deliver and the merge model's Prop A asserts.

The two grades are **not** ordered by an arrow here (mandate T1: "do not force an arrow"): the
per-day clause compares two *products* `⌜X w⌝` vs `⌜M*(X) w⌝`, the averaged clause compares the
quote's price with its value along a weighting. `day_imp_avg_on_quotes` is not stated; the gap is
findings F-T1.

**Junk guards.** `weightedBias` is FAF's total weighted average, `0` while the prefix sum is `0`:
the averaged clause demands `DivergentWeighting`, so the zero branch is eventually never taken.
`Reflects` quantifies over worlds consistent with the completed theory; over a process with a
contradictory stage both clauses degenerate (`Observable` becomes trivially true, the tower clauses
become refutable), so every *headline* over these predicates carries `hworld`
(`∀ n, ∃ v, v.ConsistentWith (DP.D n)`), discharged for the instances from FAF/`li-quote-lane`.

**T5 — the merge expert's notions.** `def-lattice`'s `Expert` reads its history at the *deferred*
day `E.f n`, but the merge estimate `B_n(X) := 𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝)` is `A`'s **same-day**
expectation of a quote (def-lattice F1: same-day is unrepresentable as an `Expert`). So the
notions are restated with an abstract estimate function `est : (ℕ → LUV) → ℕ → ℝ` in place of
`E.estimate` and a deferral `f` in place of `E.f` (the weight stays at `w (f n)`, the indexing
convention of FAF's `thm:ccee`): `CondQuoteEst`, `CondTowerEst`, `WeightQuoteEst`,
`ThresholdIneqAboveEst`, `SoftTotalTrustAboveEst`. `condTowerEst_expert_iff` and
`thresholdIneqAboveEst_expert_iff` show the lattice's objects are the `Expert` instances
(`est := E.estimate`, `f := E.f`). `MergeExpert` packages `A`, `f` and a quote assignment `Q`,
with `MergeExpert.est X n := (Q X n).expect A n`. Fidelity of every `Est` row: `variant`.

**The premise must be read per source** (audit r1, B1 of both lenses). `CondTowerEst` quantifies
over *every* e.c. source. At an estimate that does not depend on the source — the ledger
instance's `readEst H (fun _ n => ledgerLuv j n)`, the same number `𝔼^H_n(α_{j,n})` for every
`X` — the universal premise identifies the prices of the left products of *any two* sources that
share a right quote, hence (at a source valued `1` and one valued `0` everywhere) forces the gate
`𝔼^H_n(W_n) → 0` and, given a same-day quote, is outright false (`MergeUniversal.lean`). The
source-restricted form `CondTowerEstOn P DP f est 𝒳` is the premise T5 uses, at `𝒳 = {X}`
(`Merge.lean`), matching `LUVTotalTrustAvgOn` and the mirror ledger's one quoted family.

**Scope tags** (mandate): every cross-agent theorem over these definitions says, in its docstring,
its grade (`per-day` / `averaged`), its direction (`one-way: A reads H` / `one-way: H reads A` /
`two-way`) and its weight class (`A`-generable / `H`-generable / bi-generable).
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice

noncomputable section

/-! ## T1 — the definition of record -/

/-- **Clause (i), observability as quotability.** Every e.c. source `X` has an e.c. quote `Y` in
the novice's language that every completed-theory world of `DP` values at the expert's estimate
`E.estimate X n = (X n).expect E.A (E.f n)` (`Reflects`). The FAF-faithful reading of
"`M`'s estimates are `ℙ^N`-generable": `EF` has no constructor for a posted number
(trust-lab-2-009; `li-quote-lane` F4), so a published estimate enters `N`'s language only through
decided sentences naming it. Over a process with a contradictory stage this is trivially true
(`Reflects` is vacuous): headlines carry `hworld`.
Source: trust-lab-002 (clause (i)); root-deference-061; [[merging-inductors-model]] §(b.1) (i)
("`H`-observability"); [[deference-in-logical-induction-v2]] §10.4 ("observability is
structural, not cosmetic")
Kind: D
Fidelity: variant: "generable estimates" rendered as "quotable estimates" (FAF has no posted-number
feature; generability of the reader's estimate of the quote is then a theorem,
`li-quote-lane`'s `ledgerFeature_pgenerable`)
Hyps: n/a -/
def Observable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ X : ℕ → LUV, LUV.MachineThresholdCodeSeq X →
    ∃ Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Y ∧ Reflects DP E X Y

/-- **LUV-Total-Trust, per-day grade (the lab's definition as written).** `N` (market `P` over
`DP`) LUV-Total-Trusts the expert `E` iff (i) `E` is observable from `N`'s process and (ii) for
every `N`-generable `[0,1]` weight the cross-defect vanishes per day: `CondTower P DP E`, i.e.
`𝔼^N_n(⌜X_n · w_{f n}⌝) ≈ₙ 𝔼^N_n(⌜E*(X_n) · w_{f n}⌝)` for every e.c. `X`, every
`PGenerableRat P w` in `[0,1]`, and every `CondQuote` pair (left product within FAF's vanishing
slack, right product exact, weight at the deferred day `w (E.f n)`). Grade: **per-day**.
Source: trust-lab-002 ("`N` LUV-Total-Trusts `M` iff (i) … (ii) for every `ℙ^N`-generable weight
`w`, the cross-defect `𝔼^N_n(⌜X_n·w_n⌝) − 𝔼^N_n(⌜𝔼^M(X_n)·w_n⌝) → 0`"); root-deference-061;
[[deference-in-logical-induction-v2]] §10.1 boxed display
Kind: D
Fidelity: variant: weight at `w (f n)` and left product within slack (as `CondTower` and FAF
disclose; def-lattice F2); clause (i) as quotability
Hyps: n/a -/
def LUVTotalTrustDay (P : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  Observable DP E ∧ CondTower P DP E

/-- **The averaged cross-defect for one quoted pair.** For every `P`-generable weighting `W`
(FAF's `PGenerableWeighting`) that is divergent on `P` and supported on the image of the
deferral `E.f`, the normalized `w`-average of `𝔼^P_i(Y_i) − E*(X_i)` tends to `0`
(FAF's `weightedBias`, the conclusion of `thm:wubexp`). `DivergentWeighting` is what keeps
`weightedBias`'s zero-denominator branch from firing eventually.
Source: [[merging-inductors-model]] §(a.2) Prop A (the display
`Σ_{i≤t} w_i (B_i(φ_i) − μ_i) / Σ_{i≤t} w_i ≂_t 0`); LI `thm:wubexp`
Kind: D
Fidelity: exact (FAF's `weightedBias`)
Hyps: n/a -/
def QuoteUnbiased (P : History) (DP : DeductiveProcess) (E : Expert DP) (X Y : ℕ → LUV) :
    Prop :=
  ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W P →
    WeightingSupportedOnDeferralImage W P E.f →
    weightedBias (fun i => (W i).denote P) (fun i => (Y i).expect P i)
      (fun i => E.estimate X i) ≈ₙ (fun _ => (0 : ℝ))

/-- **LUV-Total-Trust, averaged grade.** `Observable DP E` and, for every e.c. source `X` and e.c.
quote `Y` reflecting `E*(X)`, `N`'s expectation of the quote is `w`-unbiased for `M`'s realized
estimate along every `N`-generable divergent weighting supported on `im E.f`
(`QuoteUnbiased`). This is the grade `thm:wub`/`thm:wubexp` deliver and the merge model's Prop A
asserts; it is not the per-day clause and no arrow between the two is forced here (findings
F-T1). Grade: **averaged**.
Source: trust-lab-002 (clause (ii) at the grade of [[merging-inductors-model]] §(a.2) Prop A);
root-deference-061; LI `thm:wubexp`
Kind: D
Fidelity: variant: the averaged grade of the lab's per-day clause; clause (i) as quotability
Hyps: n/a -/
def LUVTotalTrustAvg (P : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  Observable DP E ∧
    ∀ X Y : ℕ → LUV, LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
      Reflects DP E X Y → QuoteUnbiased P DP E X Y

/-! ### The source-restricted (question-relative) forms -/

/-- **Observability on a source class** `𝒳`: clause (i) restricted to the sources in `𝒳`. A
ledger that records one family's realized expectations (the mirror pair, item `0`) quotes that
family and no other; the question-relative reading of DDB §5 / root-deference-062.
Source: trust-lab-002 (clause (i)); root-deference-062 (local deference); mandate T3 ("on the
quoted family")
Kind: D
Fidelity: variant: restricted to a source class
Hyps: n/a -/
def ObservableOn (DP : DeductiveProcess) (E : Expert DP) (𝒳 : Set (ℕ → LUV)) : Prop :=
  ∀ X : ℕ → LUV, X ∈ 𝒳 → LUV.MachineThresholdCodeSeq X →
    ∃ Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Y ∧ Reflects DP E X Y

/-- **LUV-Total-Trust, averaged grade, on a source class** `𝒳`: `ObservableOn` and the
averaged cross-defect on every quoted pair whose source lies in `𝒳`. At `𝒳 = Set.univ` this is
`LUVTotalTrustAvg` (`luvTotalTrustAvgOn_univ_iff`).
Source: trust-lab-002; root-deference-062; mandate T3
Kind: D
Fidelity: variant: restricted to a source class
Hyps: n/a -/
def LUVTotalTrustAvgOn (P : History) (DP : DeductiveProcess) (E : Expert DP)
    (𝒳 : Set (ℕ → LUV)) : Prop :=
  ObservableOn DP E 𝒳 ∧
    ∀ X Y : ℕ → LUV, X ∈ 𝒳 → LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
      Reflects DP E X Y → QuoteUnbiased P DP E X Y

/-- At the full source class the restricted form is the definition of record.
Source: mandate T3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem luvTotalTrustAvgOn_univ_iff (P : History) (DP : DeductiveProcess) (E : Expert DP) :
    LUVTotalTrustAvgOn P DP E Set.univ ↔ LUVTotalTrustAvg P DP E := by
  unfold LUVTotalTrustAvgOn LUVTotalTrustAvg ObservableOn Observable
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun X hX => h₁ X (Set.mem_univ X) hX,
      fun X Y hX hY hR => h₂ X Y (Set.mem_univ X) hX hY hR⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun X _ hX => h₁ X hX, fun X Y _ hX hY hR => h₂ X Y hX hY hR⟩

/-! ### Calibrated anticipation — the lab's proposal, restricted to a weight class -/

/-- **Calibrated anticipation on a weight class** (trust-lab-2-018 / 031): clause (i) plus clause
(ii) restricted to the `N`-generable weights lying in a class `𝒲 ⊆ (ℕ → ℚ)` (the lab's "market-
generable anticipation algebra"). The class is a set of weight *sequences*; `def-lattice`'s
`BetClass` restricts the *sources*, which is a different coarsening (T11).
Source: trust-lab-2-018 ([[updateless-deference-ideate]] §6 Idea F: "`N` deferrable-trusts `M`'s
updates iff `M`'s estimates form an `N`-calibrated anticipation (market-generable anticipation
algebra `Ā` plus reflection-coherence on every generable weight)"); trust-lab-031
Kind: D
Fidelity: variant: the "anticipation algebra" rendered as a set of weight sequences
Hyps: n/a -/
def CalibratedAnticipation (P : History) (DP : DeductiveProcess) (E : Expert DP)
    (𝒲 : Set (ℕ → ℚ)) : Prop :=
  Observable DP E ∧
    ∀ (X : ℕ → LUV) (w : ℕ → ℚ), w ∈ 𝒲 → (∀ n, 0 ≤ w n ∧ w n ≤ 1) → PGenerableRat P w →
      LUV.MachineThresholdCodeSeq X → ∀ Z Z' : ℕ → LUV, CondQuote DP E X w Z Z' →
      (fun n => (Z n).expect P n) ≈ₙ (fun n => (Z' n).expect P n)

/-- **At the full class, calibrated anticipation *is* `LUVTotalTrustDay`** — the proposal of
trust-lab-2-018 is the definition of trust-lab-002 under a new name (the circularity the
`real-gaps` brainstorm charged L1 with), now a kernel fact. Content survives only for a coarser
class (T11, `stretch`).
Source: trust-lab-2-018 (flag: "as stated it appears to *be* LUV-Total-Trust with 'calibrated
anticipation' as a name"); mandate T1
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem calibratedAnticipation_univ_iff (P : History) (DP : DeductiveProcess) (E : Expert DP) :
    CalibratedAnticipation P DP E Set.univ ↔ LUVTotalTrustDay P DP E := by
  unfold CalibratedAnticipation LUVTotalTrustDay CondTower
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun X w hmem hgen hX Z Z' q => h₂ X w (Set.mem_univ w) hmem hgen hX Z Z' q⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun X w _ hmem hgen hX Z Z' q => h₂ X w hmem hgen hX Z Z' q⟩

/-- Calibrated anticipation is antitone in the class: a finer class demands more.
Source: trust-lab-2-018; mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem CalibratedAnticipation.mono {P : History} {DP : DeductiveProcess} {E : Expert DP}
    {𝒲₁ 𝒲₂ : Set (ℕ → ℚ)} (h : 𝒲₁ ⊆ 𝒲₂) (hc : CalibratedAnticipation P DP E 𝒲₂) :
    CalibratedAnticipation P DP E 𝒲₁ :=
  ⟨hc.1, fun X w hw hmem hgen hX Z Z' q => hc.2 X w (h hw) hmem hgen hX Z Z' q⟩

/-! ## T5 — the merge expert's notions (`Est` forms) -/

/-- **The conditional-tower quote package for an abstract estimate** (`def-lattice`'s `CondQuote`
with `E.estimate` replaced by `est` and `E.f` by `f`): `Z n` reflects `x · w (f n)` within
`slack n` whenever `X n` is valued at `x`, `Z' n` reflects `est X n · w (f n)` exactly; both e.c.;
the source world-valued; the weight read at the deferred index `w (f n)`.
Source: [[deference-notions]] §The conditional tower; `def-lattice` `CondQuote`; mandate T5
Kind: D
Fidelity: variant: `E.estimate` abstracted to `est` (same-day estimates become representable);
left product within slack (as FAF)
Hyps: n/a -/
structure CondQuoteEst (DP : DeductiveProcess) (f : DeferralFunction)
    (est : (ℕ → LUV) → ℕ → ℝ) (X : ℕ → LUV) (w : ℕ → ℚ) (Z Z' : ℕ → LUV) where
  /-- the left product `⌜X_n · w_{f(n)}⌝` is efficiently describable -/
  left_codes : LUV.MachineThresholdCodeSeq Z
  /-- the right product `⌜est(X_n) · w_{f(n)}⌝` is efficiently describable -/
  right_codes : LUV.MachineThresholdCodeSeq Z'
  /-- the per-day reflection slack of the left product -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- every completed-theory world values the source -/
  source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x
  /-- the left product is valued within `slack n` of `x · w (f n)` -/
  left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (X n) x → ∃ z, v.ValuesAt (Z n) z ∧ |z - x * (w (f n) : ℝ)| ≤ slack n
  /-- the right product is valued at `est X n · w (f n)`, exactly -/
  right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Z' n) (est X n * (w (f n) : ℝ))

/-- **The conditional tower toward an abstract estimate** — `def-lattice`'s `CondTower` with
`E.estimate` replaced by `est` and `E.f` by `f`: for every e.c. source, every `P`-generable `[0,1]`
weight and every `CondQuoteEst` pair, the two expectations agree in the limit. For the merge
expert `B` this is the §10 premise "LUV-Total-Trust (`H → B`)" of [[merging-inductors-model]]
§(b.1), at the per-day grade. **Degeneracy warning** (audit r1 B1): at an estimate that does not
depend on `X` this universal identifies the left products of any two sources sharing a right
quote; use `CondTowerEstOn` at the quoted family for such an estimate.
Source: [[merging-inductors-model]] §(b.1) ("LUV-Total-Trust (`H → B`), the §10 premise");
[[deference-in-logical-induction-v2]] §10.1 boxed display; `def-lattice` `CondTower`
Kind: D
Fidelity: variant: `E.estimate` abstracted to `est`
Hyps: n/a -/
def CondTowerEst (P : History) (DP : DeductiveProcess) (f : DeferralFunction)
    (est : (ℕ → LUV) → ℕ → ℝ) : Prop :=
  ∀ (X : ℕ → LUV) (w : ℕ → ℚ), (∀ n, 0 ≤ w n ∧ w n ≤ 1) → PGenerableRat P w →
    LUV.MachineThresholdCodeSeq X → ∀ Z Z' : ℕ → LUV, CondQuoteEst DP f est X w Z Z' →
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Z' n).expect P n)

/-- **The conditional tower toward an abstract estimate, on a source class** `𝒳`: the §10
premise restricted to the sources in `𝒳` — the analogue of `LUVTotalTrustAvgOn`, and the form
the ledger instance of T5 must take, since a ledger item quotes one family and an estimate read
through one item is the same number for every source (audit r1 B1; module docstring). At
`𝒳 = Set.univ` it is `CondTowerEst` (`condTowerEstOn_univ_iff`).
Source: [[merging-inductors-model]] §(b.1); root-deference-062 (question-relative deference);
audit r1 B1 (fidelity and adversarial lenses)
Kind: D
Fidelity: variant: `E.estimate` abstracted to `est`; restricted to a source class
Hyps: n/a -/
def CondTowerEstOn (P : History) (DP : DeductiveProcess) (f : DeferralFunction)
    (est : (ℕ → LUV) → ℕ → ℝ) (𝒳 : Set (ℕ → LUV)) : Prop :=
  ∀ (X : ℕ → LUV) (w : ℕ → ℚ), X ∈ 𝒳 → (∀ n, 0 ≤ w n ∧ w n ≤ 1) → PGenerableRat P w →
    LUV.MachineThresholdCodeSeq X → ∀ Z Z' : ℕ → LUV, CondQuoteEst DP f est X w Z Z' →
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Z' n).expect P n)

/-- At the full source class the restricted premise is `CondTowerEst`.
Source: audit r1 B1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem condTowerEstOn_univ_iff (P : History) (DP : DeductiveProcess) (f : DeferralFunction)
    (est : (ℕ → LUV) → ℕ → ℝ) : CondTowerEstOn P DP f est Set.univ ↔ CondTowerEst P DP f est := by
  constructor
  · intro h X w hmem hgen hX Z Z' q
    exact h X w (Set.mem_univ X) hmem hgen hX Z Z' q
  · intro h X w _ hmem hgen hX Z Z' q
    exact h X w hmem hgen hX Z Z' q

/-- The universal premise restricts to every source class.
Source: audit r1 B1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem CondTowerEst.toOn {P : History} {DP : DeductiveProcess} {f : DeferralFunction}
    {est : (ℕ → LUV) → ℕ → ℝ} (h : CondTowerEst P DP f est) (𝒳 : Set (ℕ → LUV)) :
    CondTowerEstOn P DP f est 𝒳 :=
  fun X w _ hmem hgen hX Z Z' q => h X w hmem hgen hX Z Z' q

/-- `CondQuoteEst` at `est := E.estimate`, `f := E.f` is `CondQuote`, field by field.
Source: mandate T5
Kind: L
Fidelity: exact -/
def CondQuoteEst.toCondQuote {DP : DeductiveProcess} {E : Expert DP} {X : ℕ → LUV}
    {w : ℕ → ℚ} {Z Z' : ℕ → LUV} (q : CondQuoteEst DP E.f E.estimate X w Z Z') :
    CondQuote DP E X w Z Z' where
  left_codes := q.left_codes
  right_codes := q.right_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  left_reflected := q.left_reflected
  right_reflected := q.right_reflected

/-- `CondQuote` is a `CondQuoteEst` at `est := E.estimate`, `f := E.f`.
Source: mandate T5
Kind: L
Fidelity: exact -/
def condQuoteToEst {DP : DeductiveProcess} {E : Expert DP} {X : ℕ → LUV} {w : ℕ → ℚ}
    {Z Z' : ℕ → LUV} (q : CondQuote DP E X w Z Z') :
    CondQuoteEst DP E.f E.estimate X w Z Z' where
  left_codes := q.left_codes
  right_codes := q.right_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  left_reflected := q.left_reflected
  right_reflected := q.right_reflected

/-- **The lattice's `CondTower` is the `Est` form at the expert's own estimate** (T5's
`condTowerEst_expert_iff`): the `Est` notions are a conservative extension of `def-lattice`'s.
Source: mandate T5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem condTowerEst_expert_iff (P : History) (DP : DeductiveProcess) (E : Expert DP) :
    CondTowerEst P DP E.f E.estimate ↔ CondTower P DP E := by
  constructor
  · intro h X w hmem hgen hX Z Z' q
    exact h X w hmem hgen hX Z Z' (condQuoteToEst q)
  · intro h X w hmem hgen hX Z Z' q
    exact h X w hmem hgen hX Z Z' q.toCondQuote

/-- **The weighted-product quote package for an abstract estimate** (`def-lattice`'s
`WeightQuote` with `E.estimate` replaced by `est`): `W n` is valued at `wt (est X n)` exactly,
`XW n` within `slack n` of `x · wt (est X n)`; both e.c.; the source world-valued.
Source: [[deference-notions]] §Total Trust; `def-lattice` `WeightQuote`; mandate T5
Kind: D
Fidelity: variant: `E.estimate` abstracted to `est`; product within slack (as FAF)
Hyps: n/a -/
structure WeightQuoteEst (DP : DeductiveProcess) (est : (ℕ → LUV) → ℕ → ℝ) (X : ℕ → LUV)
    (wt : ℝ → ℝ) (W XW : ℕ → LUV) where
  /-- the weight LUV is efficiently describable -/
  weight_codes : LUV.MachineThresholdCodeSeq W
  /-- the product LUV is efficiently describable -/
  product_codes : LUV.MachineThresholdCodeSeq XW
  /-- the per-day reflection slack of the product -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- every completed-theory world values the source -/
  source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x
  /-- the weight LUV is valued at `wt` of the estimate, exactly -/
  weight_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (W n) (wt (est X n))
  /-- the product LUV is valued within `slack n` of `x · wt (est X n)` -/
  product_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (X n) x → ∃ z, v.ValuesAt (XW n) z ∧ |z - x * wt (est X n)| ≤ slack n

/-- `WeightQuoteEst` at `est := E.estimate` is `WeightQuote`.
Source: mandate T5
Kind: L
Fidelity: exact -/
def WeightQuoteEst.toWeightQuote {DP : DeductiveProcess} {E : Expert DP} {X : ℕ → LUV}
    {wt : ℝ → ℝ} {W XW : ℕ → LUV} (q : WeightQuoteEst DP E.estimate X wt W XW) :
    WeightQuote DP E X wt W XW where
  weight_codes := q.weight_codes
  product_codes := q.product_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  weight_reflected := q.weight_reflected
  product_reflected := q.product_reflected

/-- `WeightQuote` is a `WeightQuoteEst` at `est := E.estimate`.
Source: mandate T5
Kind: L
Fidelity: exact -/
def weightQuoteToEst {DP : DeductiveProcess} {E : Expert DP} {X : ℕ → LUV} {wt : ℝ → ℝ}
    {W XW : ℕ → LUV} (q : WeightQuote DP E X wt W XW) :
    WeightQuoteEst DP E.estimate X wt W XW where
  weight_codes := q.weight_codes
  product_codes := q.product_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  weight_reflected := q.weight_reflected
  product_reflected := q.product_reflected

/-- **The above-threshold inequality, product form, toward an abstract estimate**:
`𝔼^P_n(XW_n) − s · 𝔼^P_n(W_n) ≳ₙ 0` for every e.c. source and every `WeightQuoteEst` at `wt`.
Source: [[deference-notions]] §Total Trust; `def-lattice` `ThresholdIneqAbove`; mandate T5
Kind: D
Fidelity: variant: `E.estimate` abstracted to `est`
Hyps: n/a -/
def ThresholdIneqAboveEst (P : History) (DP : DeductiveProcess) (est : (ℕ → LUV) → ℕ → ℝ)
    (wt : ℝ → ℝ) (s : ℚ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuoteEst DP est X wt W XW →
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ))

/-- **Soft Total Trust above threshold at `(s, δ)` toward an abstract estimate**: the
above-threshold inequality at the ramp weight `rampAbove δ s = ctsind_δ(· > s)`. Dependents' rule
as in `def-lattice`: headlines take `0 < δ`.
Source: [[deference-notions]] §Total Trust; `def-lattice` `SoftTotalTrustAbove`; mandate T5
Kind: D
Fidelity: variant: `E.estimate` abstracted to `est`
Hyps: n/a -/
abbrev SoftTotalTrustAboveEst (P : History) (DP : DeductiveProcess)
    (est : (ℕ → LUV) → ℕ → ℝ) (s δ : ℚ) : Prop :=
  ThresholdIneqAboveEst P DP est (rampAbove δ s) s

/-- **The lattice's `ThresholdIneqAbove` is the `Est` form at the expert's own estimate.**
Source: mandate T5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thresholdIneqAboveEst_expert_iff (P : History) (DP : DeductiveProcess) (E : Expert DP)
    (wt : ℝ → ℝ) (s : ℚ) :
    ThresholdIneqAboveEst P DP E.estimate wt s ↔ ThresholdIneqAbove P DP E wt s := by
  constructor
  · intro h X W XW hX q
    exact h X W XW hX (weightQuoteToEst q)
  · intro h X W XW hX q
    exact h X W XW hX q.toWeightQuote

/-- **The merge expert** `B`: an AI market `A`, the deferral `f`, and a quote assignment `Q`
(`Q X n` is the LUV of `A`'s language meant to name `𝔼^H_{f n}(X n)`; over the mirror ledger of
`li-quote-lane` it is `ledgerLuv 0 n`, one item index per source family — the ledger's item index
`j` is how several families would be carried). Its estimate is `A`'s **same-day** expectation
of the quote, `B_n(X) := 𝔼^A_n(Q X n)` — [[merging-inductors-model]] §0's
`B_t(φ) := 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)` with the LUV source `X` in place of the sentence `φ`
(`literalIndicator φ` recovers the sentence case). Not an `Expert` (def-lattice F1), whence the
`Est` notions above. Nothing here says `Q X n` *does* name `𝔼^H_{f n}(X n)`: that is the mirror
pair's `crossQuotePackage_mirror` (`MirrorFeedback.lean`), a theorem over the ledger.
Source: [[merging-inductors-model]] §0 (the merge `B_t`); trust-lab-009; mandate T5
Kind: D
Fidelity: variant: the quote is a LUV-source quote (`Q X n`), the sentence form is its
`literalIndicator` instance; one quote assignment per package instance
Hyps: n/a -/
structure MergeExpert where
  /-- the AI market -/
  A : History
  /-- the deferral: `B_n` estimates `H`'s day-`f n` expectation -/
  f : DeferralFunction
  /-- the quote assignment: `Q X n` names `𝔼^H_{f n}(X n)` in `A`'s language -/
  Q : (ℕ → LUV) → ℕ → LUV

/-- The merge estimate `B_n(X) := 𝔼^A_n(Q X n)` — `A`'s same-day expectation of the quote.
Source: [[merging-inductors-model]] §0 (`B_t(φ) := 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`)
Kind: D
Fidelity: exact (over FAF's grid expectation `LUV.expect`, precision `n + 1`)
Hyps: n/a -/
def MergeExpert.est (B : MergeExpert) (X : ℕ → LUV) (n : ℕ) : ℝ := (B.Q X n).expect B.A n

/-- The merge estimate lies in `[0,1]` when `A`'s prices do.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem MergeExpert.est_mem_Icc (B : MergeExpert) (hA : ∀ n s, 0 ≤ B.A n s ∧ B.A n s ≤ 1)
    (X : ℕ → LUV) (n : ℕ) : 0 ≤ B.est X n ∧ B.est X n ≤ 1 :=
  LUV.expect_mem_Icc B.A n (B.Q X n) (hA n)

/-- **The reader's estimate of the merge quote through its own process**: the novice `H`'s
day-`n` expectation of a LUV `β X n` of *its* language that names `B_n(X)` — the number the
reader's legal features can see (`li-quote-lane` F2/F4: a published number enters the reader's
feature language only as the reader's estimate of the decided sentences naming it). This is the
estimate at which the T5 instance over the ledger is stated; `readEst = est` per day is
`readability`, which costs (L).
Source: [[route-recurring-ccee]] §2 (R2) (`â_n := 𝔼^H_n(⌜a_n⌝)`); `li-quote-lane` F2, F4;
mandate T5
Kind: D
Fidelity: variant: the reader's estimate of the published estimate, not the estimate itself
Hyps: n/a -/
def readEst (H : History) (β : (ℕ → LUV) → ℕ → LUV) (X : ℕ → LUV) (n : ℕ) : ℝ :=
  (β X n).expect H n

end

end Cleanroom.Trust.TrustMerge
