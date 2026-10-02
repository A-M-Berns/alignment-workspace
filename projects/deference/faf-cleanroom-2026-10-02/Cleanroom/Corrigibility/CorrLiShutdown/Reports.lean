import Cleanroom.Corrigibility.CorrLiShutdown.Map
import LogicalInduction.Construction.Statistics.HistoricalMaturity
import LogicalInduction.Properties.NonDogmatism

/-!
# `corr-li-shutdown` — Reports (T12, T17): trust in reports; non-dogmatism and no-FUD

* **T12(a)** `report_trust` (C): the board's retrospective report "continuation on day `n` was
  wrong" enters the agent's process as **item `1` of the same ledger** (`reportAtom n :=
  ⌜α_{1,n} > 1/2⌝`, true iff the published report number exceeds `1/2`); its `TheoryTruth` is
  derived from the ledger stages (`reportAtom_theoryTruth`), its e.c. certificate is the same
  fixed shell as the press atom's (`reportAtom_codes`), and FAF's Recurring Unbiasedness on it
  is forced at **every** generable divergent weighting. **(b)** The report → truth link is *not*
  forced (finding F8: the report ledger is a second table, and nothing in FAF relates `table 1`
  to the world's verdict; the counterpossible pointer is the LI paper's `main.tex:3265`).
  **(c)** Base rates of other agents' shutdowns are learnable by `thm:benford` — this is
  `li-pseudorandom`'s `truthStar_learned` verbatim (`partial` over that package's T7) and is
  cited, not renamed.
  **Disclosure (c):** what the report table contains — which days the board judges, on what
  basis — is a modelling choice (corr-wf13-070's own flag); the theorem is about the published
  number as a decided atom.
* **T17** `value_hypothesis_positive_limit` (L): FAF's `thm:nd` — a sentence consistent with
  every stage of the agent's process has an eventually positive price and a positive limit; no
  "raise a prior-zero hypothesis" correction is needed, and positive limit belief is *not*
  "the hypothesis is in the space" (richness, T11, not formalized here).
  `noFUD_is_cee` (L): T9's declaration under its second name.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc
open Filter Topology
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-! ## T12(a): the report family as a second ledger item -/

/-- **The report atom** `rep_n := ⌜α_{1,n} > 1/2⌝`: "the board's published day-`n` report number
on continuation day `n` exceeds `1/2`" — the board judges continuation on day `n` to have been
wrong. Item `1` of the agent's ledger.
Source: [[corr-wf13-inventory]] 070 (I15.3, `positive/li.md` l. 240: the board's verdicts as "ledger atoms … an e.c. decidable family")
Kind: D
Fidelity: variant: the report as a decided threshold atom of a published `[0,1]` number
Hyps: n/a -/
def reportAtom (n : ℕ) : Sentence := (ledgerLuv 1 n).gt (1 / 2)

/-- The report ledger's truth value: `1` iff the published report number exceeds `1/2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def reportTruth (S : ShutdownPair) (n : ℕ) : ℝ :=
  if (1 / 2 : ℚ) < S.table 1 n then 1 else 0

/-- Every completed-theory world of the agent's process affirms `rep_n` iff the published report
number exceeds `1/2` (stage form of determinacy at a late stage; no same-day publication is
needed for item `1`).
Source: `li-quote-lane` `ledgerLuv_decided_by`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem holds_reportAtom_iff (S : ShutdownPair) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory S.agentProcess) :
    v.Holds (reportAtom n) ↔ (1 / 2 : ℚ) < S.table 1 n := by
  have h := ledgerLuv_decided_by S.base S.table S.e 1 n (1 / 2)
    (s := max (max n 1) (max (Encodable.encode (1 / 2 : ℚ)) ((S.e 1).e n)))
    ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
    v (hv _)
  unfold reportAtom
  constructor
  · intro hh
    by_contra hnot
    exact h.2 (not_lt.mp hnot) hh
  · exact h.1

/-- **The report atom's `TheoryTruth`**, derived from the ledger stages.
Source: [[corr-wf13-inventory]] 070; `li-quote-lane` `ledgerLuv_decided_by`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem reportAtom_theoryTruth (S : ShutdownPair) :
    AffineCombination.TheoryTruth reportAtom S.agentProcess (reportTruth S) := by
  intro n v hv
  unfold reportTruth PCWorld.payout
  by_cases hp : (1 / 2 : ℚ) < S.table 1 n
  · rw [if_pos hp, if_pos ((holds_reportAtom_iff S n v hv).mpr hp)]
  · rw [if_neg hp, if_neg (fun h => hp ((holds_reportAtom_iff S n v hv).mp h))]

/-- One poly-fueled program emits `⌜rep_n⌝` from `n` (the item-`1` shell).
Source: none: infrastructure (`Setting.lean` `pressAtom_polySentenceCodes`)
Kind: L
Fidelity: n/a -/
lemma reportAtom_polySentenceCodes : PolySentenceCodes reportAtom :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const (cleanroomBaseTag + ledgerFamily)).pair
    (PolyFueled.id.pair ((PolyFueled.const 1).pair
      (PolyFueled.const (Encodable.encode (1 / 2 : ℚ))))))).succ_comp).of_eq
    fun n => (encode_ledgerLuv_gt 1 n (1 / 2)).symm⟩

/-- The report-atom family is e.c.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem reportAtom_codes : MachineSentenceCodes reportAtom :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes reportAtom_polySentenceCodes)

/-- **Trust in reports is forced** (T12(a)): for **every** generable divergent weighting `W` of
the agent's market, the `W`-weighted bias of the agent's prices of the report atoms against the
published reports has `0` as a limit point — FAF's `thm:recurringunbiasedness` on the report
family, with the `TheoryTruth` derived from the ledger. The agent cannot be predictably biased
about what the board will report, on any class it can generate. Scope: one-way; averaged grade.
Source: [[corr-wf13-inventory]] 070 (I15.3, `positive/li.md` l. 240: "Recurring Unbiasedness on it is forced: `A`'s credence in the *report* family is unbiased against realized reports on any generable weighting")
Kind: C
Fidelity: variant: the report as a decided atom of a published number
Hyps: (a) `hW`, `hdiv` named; (c) what the report table contains is a modelling choice (the item's own flag) -/
theorem report_trust (S : ShutdownPair) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (hdiv : DivergentWeighting W S.agent) :
    HasLimitPoint (weightedBias (realized S W) (fun i => S.agent i (reportAtom i))
      (reportTruth S)) 0 :=
  AffineCombination.recurringunbiasedness reportAtom
    (AffineCombination.sentenceAffine_polySequence reportAtom reportAtom_codes) hW
    (reportAtom_theoryTruth S) hdiv S.hworld

/-! ## T17: non-dogmatism and no-FUD -/

/-- **A value hypothesis consistent with every stage keeps positive belief** (T17): FAF's
`thm:nd` over the agent's process — eventually bounded away from `0`, and with a positive
limit. No "raise a prior-zero hypothesis" correction is needed; positive limit belief is not
"the hypothesis is in the space" (that is richness, a syntactic assumption; T11, not
formalized here).
Source: [[corr-core-inventory]] 010; FAF `lic_nonDogmatism`, `lic_exists_limit_pos`
Kind: L
Fidelity: exact
Hyps: (a) (`hφ`: `φ` is consistent with every stage, FAF's own premise) -/
theorem value_hypothesis_positive_limit (S : ShutdownPair) (φ : Sentence)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.agentProcess.D n) ∧ v.Holds φ) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ε ≤ S.agent n φ) ∧
      ∃ L, ConvergesTo (fun n => S.agent n φ) L ∧ 0 < L :=
  ⟨lic_nonDogmatism S.agent S.agentProcess φ hφ, lic_exists_limit_pos S.agent S.agentProcess φ hφ⟩

section Paper

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **No FUD is `cee`** (T17, second name of T9): "the agent does not have a fully-updated-
deference problem with respect to its own future self" and "the thesis sentence" are the same
theorem, FAF's `thm:cee` on the verdict indicator. Self-pushes only (corr-core-011's register);
the identification of "no FUD" and "the FUD mechanism" as one theorem is a gloss
(ATTRIBUTION-UNVETTED).
Source: [[corr-core-inventory]] 011; [[corr-wf13-inventory]] 067
Kind: L
Fidelity: exact (self-pushes only)
Hyps: (a) -/
theorem noFUD_is_cee (f : DeferralFunction) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    (fun n => (LUV.indicatorOf (φ n)).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n => ((paperDeferredExpectationQuoteCode T f (fun n => LUV.indicatorOf (φ n))
        (LUV.indicatorOf_machineThresholdCodeSeq hφ)).luv n).expect (liaHistory (paperDP T)) n :=
  thesis_sentence_is_cee T f φ hφ

end Paper

end Cleanroom.Corrigibility.CorrLiShutdown
