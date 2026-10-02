import Cleanroom.Fa.FaEisenstatConj.Companion
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Fa.FaTheoremA.Half1
import Cleanroom.Trust.TrustMerge.Defs

/-!
# `fa-eisenstat-conj` · SamStructure: Sam Eisenstat's information structure as a definition of record (T5)

**Two-way.** Sam's intended information structure ([[eisenstat-conjecture-attribution]] §2, as
relayed by Abram 2026-08-10; ATTRIBUTION-UNVETTED by Sam throughout): *the AI knows the human's
beliefs immediately; the humans learn the AI's beliefs only at a delay.* No corpus setting
instantiates it (attribution page §3 table); Abram's original formalism ([[li-deference]] lines
106–111, `n < e(n) < F(n) < σ(n)`) is the nearest. `SamPair` makes it a definition of record over
`li-quote-lane`'s ledger processes:

* **AI side, immediate:** `A`'s process is `DPA0 ⊕ (the full price ledger of H)` — item `j`
  (a sentence code), day `m`, records `H`'s exact day-`m` price of `decodeSentence j`
  (`aH_eq`), published at `PublicationSchedule.succ` (stage `m + 1`: the one-stage delay of a
  well-founded recursion is the FAF rendering of "immediately" — a process at stage `m` cannot
  contain the day-`m` prices it is itself an input to). Every sentence, every day.
* **Human side, delayed:** `H`'s process is `DPH0 ⊕ (the ledger of the merge's beliefs)` — item
  `j`, day `n`, records `𝔼^∗_n(decodeSentence j) = mergeMarket A (samQuote f) n (…)` (`aA_eq`),
  published at a schedule `e` with `n < e n` (`human_delay`). The published object is the merge's
  belief `𝔼^∗_n`, not `A`'s raw prices: what Sam's "the humans learn the AI's beliefs" names in
  this construction is the lookahead expectation.
* The quote `A` prices on day `n` for `ℙ^H_{f n}(φ)` is `samQuote f φ n = ledgerLuv ⌜φ⌝ (f n)`,
  the pull-back of the price ledger along `f` (the deferral inside the index). Its e.c. certificate
  `hQ` is carried as a field: it holds when `f n` is polynomially writable (`succDeferral`,
  `doublingDeferral`), which FAF's `DeferralFunction` alone does not give (Known issue 6).
* **Regimes** `PublishesBeforeLookahead` (`e n ≤ f n`, [[li-deference]]'s `e(n) < F(n)`, where the
  Gödel-coin diagonal of the tower refutation can be run) and `PublishesAfterLookahead`
  (`f n < e n`, where it cannot; attribution page §4 item 1).

**Derived:** `samPair_mergeQuotes` — Sam's structure yields the package of record `MergeQuotes`
(determinacy from `ledgerLuv_determinedVia`, the certificate from `hQ`); hence every one-way
positive result transfers verbatim: `samPair_asympEq` (Claim 2 on every sentence),
`samPair_provind`, `samPair_beh_limitPoint` (Half 1 on a divergent generable weighting). This is
the first time a corpus positive result is *stated* in Sam's structure (attribution page §4 item 6
says none transfers "without new work"; the new work is `samPair_mergeQuotes`).

**Status of every row here: `partial: over the OPEN pair`** — the two ledgers are mutually
recursive (`H`'s table reads the merge's beliefs, `A`'s table reads `H`'s prices), the same joint
well-founded recursion as `li-coupled-pair`'s `twoWayPair_exists`, OPEN there on
`UniformLIAEvaluator` (a private FAF lemma, API request). `samPair_exists` (`Open.lean`) is OPEN
on the same obstacle; no inhabitant exists in the run. **Not `TwoWayPair`:** that structure's
`A`-side is the lookahead family `𝔼^H_{f n}(XH n)` published at `σ > f n`; Sam's is the full
price ledger at `succ` — different objects, cited for the existence obstacle only.

**Trust half.** `samEst p X n` is `A`'s day-`n` estimate of `𝔼^H_{f n}(X n)` through the price
ledger — the grid average of `A`'s expectations of the ledger items naming
`H (f n) ((X n).gt (i/(f n + 1)))` — so that `trust-merge`'s `Est`-notions are statable of the
merge on every LUV family; at a price LUV it is the merge market (`samEst_priceLuv`). The
trust-half OPEN `samPair_trust_half` (`Open.lean`) is `SoftTotalTrustAboveEst p.H p.processH
(samEst p)`, *pending* the accuracy notion Sam locates trust in (findings T6 (a)).

Computable branch: FAF's criterion makes both inductors computable markets over computable
processes (attribution page §2, "the computability fork"); the eventual-knowledge variant
(no schedule) is not a FAF process (findings T6 (c)).
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Fa.FaTheoremA Cleanroom.Trust.TrustMerge
open Filter Topology

/-! ## A. The definition of record -/

/-- **Sam's information structure** (definition of record, two-way): `A` an inductor over
`DPA0 ⊕ (the full price ledger of H, published next stage)`, `H` an inductor over
`DPH0 ⊕ (the ledger of the merge's beliefs 𝔼^∗_n, published at e n > n)`. A carrier, not a claim:
its inductor fields are *assumed* here and discharged nowhere in the run (`samPair_exists`,
`Open.lean`, OPEN on `li-coupled-pair`'s obstacle). `MH` is `H`'s exact rational price program —
what `A` reads (derivable from `H_inductor.marketComputable`; carried to name the channel).
Scope: two-way — Sam's structure (AI reads `H`'s prices at the next stage; humans read `𝔼^∗` at
`e(n) > n`); existence is OPEN (`samPair_exists`, the obstacle of `li-coupled-pair`'s
`twoWayPair_exists`); status `partial: over the OPEN pair`. ATTRIBUTION-UNVETTED as to Sam's
intent on every detail the attribution page §2 leaves unpinned (fixed vs eventual delay, `e ≶ f`,
further clauses). Computable branch (attribution page §2). **One atom family on both sides**
(audit r1 fidelity N5): `A`'s process decides `ledgerLuv j m` at `H m (decodeSentence j)` and
`H`'s process decides the same family-3 atoms at `𝔼^∗_m(decodeSentence j)`; each process is
internally consistent (`li-coupled-pair`'s `TwoWayPair` makes the same choice), but under a
shared-language reading the same sentence means different things to `H` and `A` — a trust-half
proof will have to face this (its quote LUV `W` lives in `H`'s language).
Source: [[eisenstat-conjecture-attribution]] §2 (Sam's two bullets), §5 ("a publication schedule `e(n)` on the human side …, AI-side immediate reading of `H`'s prices"); [[li-deference]] lines 106–111 (`n < e(n) < F(n) < σ(n)`); root-deference-2-004 (d); vq-wiki-044 ("M to define Sam's setting"); mandate T5
Kind: D
Fidelity: variant: FAF's ledger rendering — "immediately" is next-stage publication of the full price ledger; "at a delay" is a `PublicationSchedule` with `n < e n` (the eventual-knowledge variant has no FAF process); plain trader class
Hyps: n/a (a structure; its inductor fields are the OPEN existence) -/
structure SamPair where
  /-- `H`'s base process. -/
  DPH0 : DeductiveProcess
  /-- `A`'s base process. -/
  DPA0 : DeductiveProcess
  /-- The human market. -/
  H : History
  /-- The AI market. -/
  A : History
  /-- The lookahead. -/
  f : DeferralFunction
  /-- `H`'s exact rational price program (what `A` reads). -/
  MH : MarketComputation H
  /-- The full price ledger of `H`: item `j` (a sentence code), day `m`. -/
  aH : ℕ → ℕ → ℚ
  /-- The ledger is `H`'s prices. -/
  aH_eq : ∀ j m, (aH j m : ℝ) = H m (decodeSentence j)
  /-- `A` is an inductor over its base plus the price ledger of `H`, published next stage. -/
  A_inductor : IsLogicalInductor A (ledgerProcess DPA0 aH (fun _ => PublicationSchedule.succ))
  /-- Every stage of `A`'s process has a consistent world. -/
  A_hworld : ∀ n, ∃ v : PCWorld,
    v.ConsistentWith ((ledgerProcess DPA0 aH (fun _ => PublicationSchedule.succ)).D n)
  /-- The human-side publication schedule. -/
  e : PublicationSchedule
  /-- The humans see the merge's day-`n` beliefs only after day `n`. -/
  human_delay : ∀ n, n < e.e n
  /-- The ledger of the merge's beliefs: item `j` (a sentence code), day `n`. -/
  aA : ℕ → ℕ → ℚ
  /-- The ledger is the merge's beliefs `𝔼^∗_n`. -/
  aA_eq : ∀ j n, (aA j n : ℝ) = mergeMarket A (samQuote f) n (decodeSentence j)
  /-- `H` is an inductor over its base plus the ledger of the merge's beliefs, published at `e`. -/
  H_inductor : IsLogicalInductor H (ledgerProcess DPH0 aA (fun _ => e))
  /-- Every stage of `H`'s process has a consistent world. -/
  H_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess DPH0 aA (fun _ => e)).D n)
  /-- The pull-back certificate: every quote family `samQuote f φ` is e.c. -/
  hQ : ∀ φ, LUV.MachineThresholdCodeSeq (samQuote f φ)

namespace SamPair

/-- `A`'s process: the base plus the price ledger of `H`.
Source: mandate T5
Kind: D
Fidelity: exact -/
abbrev processA (p : SamPair) : DeductiveProcess :=
  ledgerProcess p.DPA0 p.aH (fun _ => PublicationSchedule.succ)

/-- `H`'s process: the base plus the ledger of the merge's beliefs.
Source: mandate T5
Kind: D
Fidelity: exact -/
abbrev processH (p : SamPair) : DeductiveProcess := ledgerProcess p.DPH0 p.aA (fun _ => p.e)

/-- **Regime: publication before the lookahead**, `e n ≤ f n` ([[li-deference]]'s `e(n) < F(n)`):
the humans have absorbed the merge's day-`n` belief by the day `f n` that serves as its forecast
target — the regime in which the Gödel-coin diagonal of the tower refutation can be run.
Source: [[li-deference]] lines 106–111; [[eisenstat-conjecture-attribution]] §2 (the unpinned detail), §4 item 1; mandate T5
Kind: D
Fidelity: exact
Hyps: n/a -/
def PublishesBeforeLookahead (p : SamPair) : Prop := ∀ n, p.e.e n ≤ p.f.f n

/-- **Regime: publication after the lookahead**, `f n < e n`: the forecast target `H (f n)` is
sealed from the merge's day-`n` belief — the regime in which the diagonal cannot be run as
written (attribution page §4 item 1; vq-wiki-045's conjecture that the tower verdict flips with
`e ≶ f` is recorded in the findings, not targeted).
Source: [[eisenstat-conjecture-attribution]] §2, §4 item 1, §5; mandate T5
Kind: D
Fidelity: exact
Hyps: n/a -/
def PublishesAfterLookahead (p : SamPair) : Prop := ∀ n, p.f.f n < p.e.e n

/-- The price ledger is `[0,1]`-valued (from `H`'s `marketComputable`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem aH_mem (p : SamPair) (j m : ℕ) : 0 ≤ p.aH j m ∧ p.aH j m ≤ 1 := by
  haveI := p.H_inductor
  have h := IsLogicalInductor.price_mem_Icc (P := p.H)
    (DP := ledgerProcess p.DPH0 p.aA (fun _ => p.e)) m (decodeSentence j)
  rw [← p.aH_eq] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

end SamPair

/-! ## B. Sam's structure yields the package of record -/

/-- **T5 (headline, C). Sam's structure yields the good-feedback package of record:**
`MergeQuotes p.H p.processA p.f (samQuote p.f)` — for every sentence `φ`, `A`'s completed theory
determines the pulled-back ledger item `ledgerLuv ⌜φ⌝ (f n)` at `H`'s day-`f n` price of `φ`
(`li-quote-lane`'s `ledgerLuv_determinedVia` on the price ledger, `aH_eq`, `priceLuv_expect`), and
the family is e.c. (`hQ`). The deferral is inside the index, so no `realizedExpectation` table is
needed. Consequently every one-way positive result applies to Sam's structure verbatim
(`samPair_asympEq`, `samPair_provind`, `samPair_beh_limitPoint`) — the "new work" of the
attribution page §4 item 6.
Scope: two-way — Sam's structure; status `partial: over the OPEN pair` (`samPair_exists`).
The package's (c), `reflected`, is here (a) at variant fidelity (ledger-recorded determinacy).
ATTRIBUTION-UNVETTED as to Sam's intent.
Source: [[eisenstat-conjecture-attribution]] §2, §4 item 6 ("no corpus verdict transfers to it without new work"); mandate T5 (`samPair_mergeQuotes`)
Kind: L (an instantiation at the derived package; relabelled from C in repair round 1)
Fidelity: variant: ledger-recorded determinacy in place of `Γ_A`-provable determinacy
Hyps: (a) none beyond the structure's fields (the structure's inductor fields are the OPEN existence) -/
theorem samPair_mergeQuotes (p : SamPair) : MergeQuotes p.H p.processA p.f (samQuote p.f) :=
  MergeQuotes.of_price p.hQ fun φ n => by
    have h := ledgerLuv_determinedVia p.DPA0 p.aH (fun _ => PublicationSchedule.succ) p.aH_mem
      (Encodable.encode φ) (p.f.f n)
    rw [p.aH_eq, decodeSentence_encode] at h
    exact h

/-! ## C. The one-way positives, transferred -/

/-- **Claim 2 in Sam's structure:** `𝔼^∗_n(φ) − ℙ^H_n(φ) → 0` for every sentence
(`mergeMarket_asympEq` at the derived package).
Scope: two-way — Sam's structure; status `partial: over the OPEN pair`. ATTRIBUTION-UNVETTED.
Source: [[eisenstat-lookahead-construction]] §3.1 Claim 2; [[eisenstat-conjecture-attribution]] §4 item 6; mandate T5 (the transfer)
Kind: L (an instantiation at the derived package; relabelled from C in repair round 1)
Fidelity: exact (over the structure)
Hyps: (a) none beyond the structure's fields -/
theorem samPair_asympEq (p : SamPair) (φ : Sentence) :
    AsympEq (fun n => mergeMarket p.A (samQuote p.f) n φ) (fun n => p.H n φ) :=
  haveI := p.H_inductor
  haveI := p.A_inductor
  mergeMarket_asympEq (H := p.H) (A := p.A) p.H_hworld p.A_hworld (samPair_mergeQuotes p) φ

/-- **The surviving neighbour in Sam's structure:** on every sentence true in every
completed-theory world of `H`'s process, `𝔼^∗_n(φ) → 1`.
Scope: two-way — Sam's structure; status `partial: over the OPEN pair`. ATTRIBUTION-UNVETTED.
Source: trust-lab-008 (surviving neighbour); mandate T5 (the transfer)
Kind: L (an instantiation at the derived package; relabelled from C in repair round 1)
Fidelity: exact (over the structure)
Hyps: (a) `hφ` -/
theorem samPair_provind (p : SamPair) (φ : Sentence)
    (hφ : ∀ v : PCWorld, v.ConsistentWithTheory p.processH → v.Holds φ) :
    Tendsto (fun n => mergeMarket p.A (samQuote p.f) n φ) atTop (𝓝 1) :=
  haveI := p.H_inductor
  haveI := p.A_inductor
  mergeMarket_provind (H := p.H) (A := p.A) p.H_hworld p.A_hworld (samPair_mergeQuotes p) φ hφ

/-- **(Beh), limit-point form, in Sam's structure, at a fixed sentence:** for every
`A`-generable divergent weighting `W`, `0` is a limit point of the `W`-weighted bias of the merge
against `H`'s realized price of one fixed sentence `φ` — `fa-theorem-a`'s `quote_unbiased` (FAF's
`thm:recurringunbiasednessexp`) at the derived package. **Fixed sentence:** Prop A's display is
over a *varying* sentence sequence `φ_t` (`μ_t := ℙ^H_{f(t)}(φ_t)`); this is its constant-sequence
case. The varying-sentence form is `samPair_beh_limitPoint_seq` below, which needs the uniform
machine certificate for `n ↦ samQuote f (φ n) n` as a hypothesis (findings F17). The full-limit
form on a weighting supported on `im f` (the model's Prop A) is OPEN (`samPair_beh_seq`,
`samPair_beh`, `Open.lean`).
Scope: two-way — Sam's structure; status `partial: over the OPEN pair`. ATTRIBUTION-UNVETTED.
Source: [[merging-inductors-model]] §(a.2) Proposition A (trust-lab-008, (Beh)); mandate T5
Kind: L (one instantiation of `quote_unbiased` at the price LUV plus a rewrite)
Fidelity: weaker: fixed sentence `φ` (Prop A's constant-sequence case); limit point along a subsequence, not the full `≈ₙ 0` limit; no support-in-`im f` clause (the full form is OPEN)
Hyps: (a) `hW`, `hdiv` -/
theorem samPair_beh_limitPoint (p : SamPair) (φ : Sentence) {W : ℕ → EF}
    (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W p.A) :
    HasLimitPoint (weightedBias (fun i => (W i).denote p.A)
      (fun i => mergeMarket p.A (samQuote p.f) i φ) (fun i => p.H (p.f.f i) φ)) 0 := by
  haveI := p.A_inductor
  have h := quote_unbiased (H := p.H) (A := p.A) ((samPair_mergeQuotes p) φ) p.A_hworld hW hdiv
  rw [mergeMarket_eq_quoteSeq, ← realized_priceLuv]
  exact h

/-- **The varying-sentence quote package in Sam's structure, given the uniform certificate:**
for a sentence sequence `φ : ℕ → Sentence`, the family `n ↦ samQuote f (φ n) n` names
`H (f n) (φ n)` in `A`'s completed theory on every day (from the per-sentence package
`samPair_mergeQuotes` at `φ n`), and is e.c. by the hypothesis `hcode`. `hcode` is the real gap
between the fixed- and varying-sentence forms: `MergeQuotes` gives a certificate *per sentence*
and `QuoteTable` a plain `Computable` table, neither a uniform machine certificate for an e.c.
sentence sequence (findings F17).
Source: [[merging-inductors-model]] §0 (`μ_t := ℙ^H_{f(t)}(φ_t)`, a varying sentence); repair round 1 (audit r1 adversarial B3)
Kind: L
Fidelity: exact (given `hcode`)
Hyps: (a) `hcode` (the uniform certificate; discharged at no instance in the run) -/
theorem samPair_crossQuotePackage_seq (p : SamPair) (φ : ℕ → Sentence)
    (hcode : LUV.MachineThresholdCodeSeq fun n => samQuote p.f (φ n) n) :
    CrossQuotePackage p.H p.processA p.f (fun n => priceLuv (φ n))
      (fun n => samQuote p.f (φ n) n) :=
  ⟨hcode, fun n => ((samPair_mergeQuotes p) (φ n)).reflected n⟩

/-- **(Beh), limit-point form, in Sam's structure, on a varying sentence sequence** (Prop A's
display, limit-point grade): for an e.c. sentence sequence `φ_t` — given the uniform certificate
`hcode` for `n ↦ samQuote f (φ n) n` — and every `A`-generable divergent weighting `W`, `0` is a
limit point of the `W`-weighted bias of `𝔼^∗_t(φ_t)` against `ℙ^H_{f t}(φ_t)`. The full-limit
form is OPEN (`samPair_beh_seq`, `Open.lean`).
Scope: two-way — Sam's structure; status `partial: over the OPEN pair`. ATTRIBUTION-UNVETTED.
Source: [[merging-inductors-model]] §(a.2) Proposition A (trust-lab-008, (Beh)); repair round 1
Kind: L (one instantiation of `quote_unbiased` at the varying-sentence package)
Fidelity: weaker: limit point, not the full `≈ₙ 0` limit; no support-in-`im f` clause; the sentence sequence is varying (Prop A's) given `hcode`
Hyps: (a) `hcode`, `hW`, `hdiv` -/
theorem samPair_beh_limitPoint_seq (p : SamPair) (φ : ℕ → Sentence)
    (hcode : LUV.MachineThresholdCodeSeq fun n => samQuote p.f (φ n) n) {W : ℕ → EF}
    (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W p.A) :
    HasLimitPoint (weightedBias (fun i => (W i).denote p.A)
      (fun i => mergeMarket p.A (samQuote p.f) i (φ i)) (fun i => p.H (p.f.f i) (φ i))) 0 := by
  haveI := p.A_inductor
  have h := quote_unbiased (H := p.H) (A := p.A) (samPair_crossQuotePackage_seq p φ hcode)
    p.A_hworld hW hdiv
  have hr : realized p.H p.f (fun n => priceLuv (φ n)) = fun i => p.H (p.f.f i) (φ i) :=
    funext fun n => priceLuv_expect (φ n) p.H (p.f.f n)
  rw [hr] at h
  exact h

/-! ## D. The merge estimate on LUV families, for the trust half -/

/-- **The merge estimate of a LUV family through the price ledger**: `A`'s day-`n` estimate of
`𝔼^H_{f n}(X n)` as the grid average of its expectations of the ledger items naming the prices
`H (f n) ((X n).gt (i/(f n + 1)))` — the same arithmetic as FAF's `expectApprox`, with each price
replaced by `A`'s belief about it. At a price LUV it is the merge market (`samEst_priceLuv`).
This is the `est : (ℕ → LUV) → ℕ → ℝ` that `trust-merge`'s `Est`-notions take, so "`H` endorses
`𝔼^∗`" is statable (`samPair_trust_half`, `Open.lean`).
Source: mandate T5 (the trust-half statement); [[merging-inductors-model]] §0 (`B_t` on a LUV source, as `trust-merge`'s `MergeExpert.est`)
Kind: D
Fidelity: variant: the LUV-family extension of `mergeMarket` through the price ledger
Hyps: n/a -/
noncomputable def samEst (p : SamPair) (X : ℕ → LUV) (n : ℕ) : ℝ :=
  ((p.f.f n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (p.f.f n + 1),
    (ledgerLuv (Encodable.encode ((X n).gt ((i : ℚ) / ((p.f.f n + 1 : ℕ) : ℚ)))) (p.f.f n)).expect
      p.A n

/-- At a price LUV the merge estimate is the merge market: every grid threshold of `priceLuv φ`
is `φ`, so the average is of `f n + 1` copies of `A`'s expectation of `samQuote f φ n`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem samEst_priceLuv (p : SamPair) (φ : Sentence) (n : ℕ) :
    samEst p (fun _ => priceLuv φ) n = mergeMarket p.A (samQuote p.f) n φ := by
  unfold samEst
  have hgrid : ∀ i ∈ Finset.range (p.f.f n + 1),
      (ledgerLuv (Encodable.encode ((priceLuv φ).gt ((i : ℚ) / ((p.f.f n + 1 : ℕ) : ℚ))))
        (p.f.f n)).expect p.A n = (ledgerLuv (Encodable.encode φ) (p.f.f n)).expect p.A n := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [priceLuv_gt_of_mem φ (by positivity) ?_]
    rw [div_lt_one (by positivity)]
    exact_mod_cast hi
  rw [Finset.sum_congr rfl hgrid, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    inv_mul_cancel_left₀ (by positivity : ((p.f.f n + 1 : ℕ) : ℝ) ≠ 0)]
  rfl

/-- The merge estimate at a price LUV is `A`'s expectation of the pulled-back ledger item (the
`MergeExpert.est` form of the same number; the bridge to `trust-merge` is recorded in prose,
report T1 and findings F4 — no `Bridge.lean` exists).
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem samEst_priceLuv_expect (p : SamPair) (φ : Sentence) (n : ℕ) :
    samEst p (fun _ => priceLuv φ) n =
      (ledgerLuv (Encodable.encode φ) (p.f.f n)).expect p.A n :=
  samEst_priceLuv p φ n

/-! ## E. The pull-back certificate at the cheapest deferral (S2 (i), partial) -/

/-- **S2 (i) at `succDeferral`: the pull-back certificate holds** — `samQuote succDeferral φ n =
ledgerLuv ⌜φ⌝ (n + 1)` is e.c., by `li-quote-lane`'s `ledgerLuv_thresholdCodes` reindexed along
the successor ruler on the day coordinate (FAF's `MachineSentenceCodes.comp`). At
`doublingDeferral` the same reindexing needs a machine-metered writer of the pair shell around
`2^n` — not a `UnaryRuler` (the value `2^n` is not polynomially bounded) — and is left as the
lemma S2 (i) names (report S2).
Source: mandate S2 (i) ("and at `succDeferral`"); Known issue 6
Kind: L
Fidelity: weaker: the `succDeferral` case only (the `doublingDeferral` case is the open lemma)
Hyps: (a) none -/
theorem samQuote_codes_succ (φ : Sentence) :
    LUV.MachineThresholdCodeSeq (samQuote succDeferral φ) :=
  ((ledgerLuv_thresholdCodes (Encodable.encode φ)).comp
    (UnaryRuler.unpairFst.succ.pair UnaryRuler.unpairSnd)).of_eq (fun m => by
      simp [samQuote, succDeferral])

end Cleanroom.Fa.FaEisenstatConj
