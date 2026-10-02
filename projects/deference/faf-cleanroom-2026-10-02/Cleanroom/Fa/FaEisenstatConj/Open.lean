import Cleanroom.Fa.FaEisenstatConj.SamStructure
import Cleanroom.Fa.FaEisenstatConj.Witnesses

/-!
# `fa-eisenstat-conj` · Open: the OPEN statements (T3, T5's OPEN rows)

The deliberately open statements of the package, each `sorry`'d and listed in
`run/wp/fa-eisenstat-conj/fa-eisenstat-conj-open.txt`. This is a **leaf** module: nothing in the
package imports it except the root, so no proved declaration rests on a `sorry` by accident (the
gate lists what does).

* **T3 — the inductor half, corpus construal (Abram's version):** `inductor_half_noExploit` and
  `inductor_half` — is `𝔼^∗ = mergeMarket A Q` a logical inductor over `H`'s process `DPH`, given
  the package of record `MergeQuotes` and the uniform quote table? The market half is **proved**
  (`mergeMarket_computableMarket`, T2), so the `sorry` sits on `noExploit` alone. Stated at grade
  (a) throughout: both `hworld`s carried, `Q` total on every sentence, `A`'s process arbitrary.
  **Inhabited:** `inductor_half_w1` applies the OPEN at the all-sentences mirror pair W1 with every
  hypothesis discharged on two real LIA markets (N+ for the package).
* **T5 — Sam's structure:** `samPair_beh_seq` (the model's Prop A on a varying sentence
  sequence, full-limit form, without the deadline program `C` that `trust-merge` needed and found
  uninhabited; the uniform certificate for the quote sequence is a hypothesis) and its
  constant-sequence case `samPair_beh` (derived from it — not a second `sorry`),
  `samPair_trust_half` (the trust half of Eisenstat's conjecture, as `trust-merge`'s
  `SoftTotalTrustAboveEst` at the merge estimate `samEst`), `samPair_exists` (the two-way pair
  over `paperDP 𝗜𝚺₁` at `doublingDeferral`, publication after the lookahead).
* **T4 / S1 — the note's own (Gen) instance and its fallback (repair round 1):**
  `gen_honestQuote_noFeedback_w1` — the merge of the paper LIA with the *honest quote atoms kept*
  and no feedback about them (the note's "`B_t(φ_t) = 𝔼^A_t(⌜μ_t⌝)` can be anything `A` likes"),
  stated in the note's direction (not an inductor), direction unknown; and
  `fallback_evenDays_noExploit` / `fallback_evenDays_w1` — the note's "at best an inductor on the
  good-feedback subsequence", as the criterion along the even days (`InductorOn`,
  `GenRefuted.lean` § E) for the mixed merge honest there. What T4/S1 *prove* is the ∃-over-`Q`
  reading of (Gen) (at the substituted quote `⊥`) and the odd-day complement of the fallback
  (`gen_refuted_mixed_oddDays`); these three OPENs are the note's own claims.

What is **not** here, and why: (R2) the inductor half judged against `A`'s own process `DPA`
(same statement with `DPA` in place of `DPH`) is a second statable reading; it is recorded in the
report as a remark and not stated as a third `sorry` (no evidence selects it over (R1)). (R3) the
timing-clause variant (`ImmediateFeedback`) would be a *weaker* conjecture; it is not stated
because no refutation of (R1) was found at W1 (the known obstacle is `fa-theorem-a` F15: no
pinned prices), so (R1) remains the row of record. The "`f` fast enough" and weighting-relative
"good feedback" clauses of the sources have no FAF object (`trust-merge` F-A/F-C) and are not
hypotheses of the OPEN — a `FeedbackTruthComputation` hypothesis would make it vacuous at every
known instance.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Bli.BliFound Cleanroom.Fa.FaTheoremA Cleanroom.Trust.TrustMerge
open Filter Topology

/-! ## A. T3: the inductor half (one-way, corpus construal) -/

/-- **OPEN — T3, the inductor half of the lookahead construction (corpus construal, Abram's
version), `noExploit` form.** For inductors `H` over `DPH` and `A` over `DPA` (both with
consistent stages), a deferral `f`, and a quote assignment `Q` that is uniformly computable
(`hQ`) and names `H`'s realized day-`f n` price of every sentence in `A`'s completed theory
(`pkg : MergeQuotes H DPA f Q`): no efficiently computable trader exploits the merge market
`𝔼^∗ = mergeMarket A Q` against `H`'s process `DPH`. Reading (R1) of record: judged against
`DPH` — `𝔼^∗` prices the sentences `H` deliberates about and is meant to replace `H`, so it is
judged where `H` is; in the shared-theory reading of the sources `DPH` is the base both extend
(at the mirror witness `DPA = DPH ⊕ ledger`).

**Why OPEN.** The inductor half has zero cases discharged anywhere in the corpus (vq-wiki-044;
[[eisenstat-lookahead-construction]] §7 item 8; deference-v6 §8 D3). Under the package,
`𝔼^∗_n(φ) − ℙ^H_n(φ) → 0` for every sentence (`mergeMarket_asympEq`, E1), but per-sentence
asymptotic equality to an inductor does not transfer the criterion in general
(`Transfer.lean`), so E1 settles this in neither direction. A refutation at W1 would need
pinned LIA prices on undecided sentences (`fa-theorem-a` F15), which nothing available gives.
**Stated, not weakened:** the sorry sits on `noExploit` alone — the market half is proved (T2);
`hworldA` is in the statement so that the package cannot be discharged vacuously over a
contradictory `DPA`; `MergeQuotes` is all-sentences, so no default on "unquoted" sentences
(`GenRefuted.lean` is exactly that mechanism); the direction is `A` reads `H`.
**Inhabited:** `inductor_half_w1` below — every hypothesis discharged at W1 (N+ for the package).
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`. This is
the lookahead construction in the **corpus construal (Abram's version)**, not Sam Eisenstat's
intended information structure ([[eisenstat-conjecture-attribution]] §2, §5); claims about Sam's
intent are ATTRIBUTION-UNVETTED. The only modelling step is the quote's determinacy,
`pkg.reflected` (`MergeQuotes`) — `A`'s theory determines `H`'s realized prices; at the mirror
witness it is (a) at variant fidelity (ledger-recorded). Computable branch: FAF's criterion makes
both inductors computable markets over computable processes (attribution page §2, "the
computability fork").
Source: [[eisenstat-conjecture-attribution]] §1 (both records: "Would they also be a logical inductor (satisfy the logical induction criterion)?"; "`B_t` will itself be a logical inductor"); root-deference-018; trust-lab-008 ((Gen)); vq-wiki-044 ("S to state, XL to prove or refute"); lean-deference-075 (ill-posed until the quotes are a market — now they are, T2)
Kind: OPEN
Fidelity: stronger: the criterion, FAF's `def:lic`, at the merge market with the note's two clauses dropped — no timing clause (good feedback as a rate) and no "`f` fast enough" (neither has a FAF object, Known issue 3) — so this conjecture is strictly stronger than the sources'; (R3) with `ImmediateFeedback` is the faithful-weaker form, to be stated if (R1) is refuted; (R1) `DPH` of record
Hyps: (a) `hworldH`, `hworldA`, `hQ`; (c) `pkg.reflected` as above. -/
theorem inductor_half_noExploit {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (hQ : QuoteTable Q)
    (pkg : MergeQuotes H DPA f Q) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (mergeMarket A Q) DPH := by
  sorry

/-- **OPEN — T3, the inductor half, criterion form:** `IsLogicalInductor (mergeMarket A Q) DPH`.
The market half is `mergeMarket_computableMarket` (T2, proved), the process half is `H`'s own
`processComputable`, and the `noExploit` half is `inductor_half_noExploit` — this theorem rests
on that sorry and nothing else.
Scope: as `inductor_half_noExploit` (one-way, corpus construal; ATTRIBUTION-UNVETTED as to Sam;
computable branch).
Source: [[eisenstat-conjecture-attribution]] §1; root-deference-018; vq-wiki-044
Kind: OPEN
Fidelity: exact
Hyps: (a) `hworldH`, `hworldA`, `hQ`; (c) `pkg.reflected`. -/
theorem inductor_half {H A : History} {DPH DPA : DeductiveProcess}
    [hH : IsLogicalInductor H DPH] [hA : IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (hQ : QuoteTable Q)
    (pkg : MergeQuotes H DPA f Q) : IsLogicalInductor (mergeMarket A Q) DPH :=
  ⟨mergeMarket_computableMarket hA.marketComputable hQ, hH.processComputable,
    inductor_half_noExploit hworldH hworldA hQ pkg⟩

/-- **The OPEN inductor half applied at W1** — the all-sentences mirror pair over `paperDP 𝗜𝚺₁`:
every hypothesis of `inductor_half` is discharged (`w1_inductorH`, `w1_inductorA`,
`paperDP_hworld 𝗜𝚺₁`, `w1_hworldA`, `ledgerQuotes_quoteTable`, `w1_pkg`), on two real LIA
markets over distinct processes, every sentence quoted as a determined forecast. Rests on the sorry of
`inductor_half_noExploit` (listed); its point is that the hypothesis package of the OPEN is
*inhabited*, graded N+ for the package (`Witnesses.lean`).
Source: mandate W1 ("the statement `inductor_half_noExploit` *applied* at W1 type-checks with every hypothesis discharged")
Kind: OPEN
Fidelity: exact (an instance of the OPEN)
Hyps: (a) none (every hypothesis discharged) -/
theorem inductor_half_w1 : IsLogicalInductor (mergeMarket w1A ledgerQuotes) (paperDP 𝗜𝚺₁) :=
  haveI := w1_inductorH
  haveI := w1_inductorA
  inductor_half (H := w1H) (A := w1A) (paperDP_hworld 𝗜𝚺₁) w1_hworldA ledgerQuotes_quoteTable
    w1_pkg

/-! ## B. T5: the OPEN rows of Sam's structure -/

/-- **OPEN — (Beh), full-limit form, in Sam's structure, on a varying sentence sequence** (the
model's Proposition A): for an e.c. sentence sequence `φ_t` — given the uniform machine
certificate `hcode` for the quote sequence `n ↦ samQuote f (φ n) n` — and every `A`-generable
divergent weighting `W` supported on the image of the deferral, the `W`-weighted bias of
`𝔼^∗_t(φ_t)` against `H`'s realized price `ℙ^H_{f t}(φ_t)` tends to `0`. `trust-merge` proves the
one-way mirror form only modulo the deadline program `C` of `thm:wubexp`
(`mirror_feedback_unbiased`), which its F-C finds doubly deferred and uninhabited; here it is
stated *without* `C`. Reason OPEN: whether immediacy of the full price ledger (Sam's bullet 1)
makes `C`'s doubly deferred demand dischargeable is the open step (`trust-merge` F-C). The
limit-point form is proved (`samPair_beh_limitPoint_seq`). **`hcode` is a hypothesis** because
neither `MergeQuotes` (a certificate per sentence) nor `QuoteTable` (a plain `Computable` table)
yields a uniform certificate for an e.c. sentence sequence; at a constant sequence it is the
structure's own `hQ` (`samPair_beh`); no varying instance discharges it in the run (findings F17).
Scope: two-way — Sam's structure (AI reads `H`'s prices at the next stage; humans read `𝔼^∗` at
`e(n) > n`); existence is OPEN (`samPair_exists`); status `partial: over the OPEN pair`.
ATTRIBUTION-UNVETTED as to Sam's intent. Computable branch (attribution page §2).
Source: [[merging-inductors-model]] §(a.2) Proposition A (trust-lab-008, (Beh)); `trust-merge` F-C; mandate T5; repair round 1 (audit r1 adversarial B3)
Kind: OPEN
Fidelity: exact (Prop A's display on `φ_t`, without the deadline program, given `hcode`)
Hyps: (a) `hcode`, `hW`, `hdiv`, `hsupp` -/
theorem samPair_beh_seq (p : SamPair) (φ : ℕ → Sentence)
    (hcode : LUV.MachineThresholdCodeSeq fun n => samQuote p.f (φ n) n) {W : ℕ → EF}
    (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W p.A)
    (hsupp : WeightingSupportedOnDeferralImage W p.A p.f) :
    AsympEq (weightedBias (fun i => (W i).denote p.A)
      (fun i => mergeMarket p.A (samQuote p.f) i (φ i)) (fun i => p.H (p.f.f i) (φ i)))
      (fun _ => 0) := by
  sorry

/-- **OPEN — (Beh), full-limit form, in Sam's structure, at a fixed sentence** — the
constant-sequence case of `samPair_beh_seq` (derived from it with `hcode := p.hQ φ`; it rests on
that sorry and nothing else, and is listed as such). Prop A's display is over a *varying*
sentence sequence, so this is strictly weaker than Prop A (audit r1 adversarial B3).
Scope: as `samPair_beh_seq`.
Source: [[merging-inductors-model]] §(a.2) Proposition A (trust-lab-008, (Beh)); `trust-merge` F-C; mandate T5
Kind: OPEN
Fidelity: weaker: fixed sentence `φ` (Prop A's constant-sequence case), without the deadline program
Hyps: (a) `hW`, `hdiv`, `hsupp` -/
theorem samPair_beh (p : SamPair) (φ : Sentence) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (hdiv : DivergentWeighting W p.A) (hsupp : WeightingSupportedOnDeferralImage W p.A p.f) :
    AsympEq (weightedBias (fun i => (W i).denote p.A)
      (fun i => mergeMarket p.A (samQuote p.f) i φ) (fun i => p.H (p.f.f i) φ)) (fun _ => 0) :=
  samPair_beh_seq p (fun _ => φ) (p.hQ φ) hW hdiv hsupp

/-- **OPEN — the trust half of Eisenstat's conjecture in Sam's structure:** `H` endorses `𝔼^∗` in
the LI-weak sense — stated as `trust-merge`'s soft Total Trust above threshold toward the merge
estimate, `SoftTotalTrustAboveEst p.H p.processH (samEst p) s δ` for every threshold `s` and
every ramp width `0 < δ` (the above-threshold inequality: on every e.c. source, `H`'s expectation
of the source weighted by `ctsind_δ(𝔼^∗ > s)` is asymptotically at least `s` times the weight).
Reason OPEN: the trust half of Eisenstat's conjecture in Sam's structure; no corpus result bears
on it (attribution page §4 item 6). Stated over `trust-merge`'s menu *pending* the accuracy
notion Sam locates trust in (attribution page §2 (ii); findings T6 (a)) — ATTRIBUTION-UNVETTED
as to which notion, if any, Sam means; the menu's other entries (`CondTowerEst`,
`LUVTotalTrustAvg`-type averages) are equally statable at `samEst`. **Inhabitation obligation
(audit r1 N3, both lenses):** `SoftTotalTrustAboveEst` unfolds to `∀ X W XW, … →
WeightQuoteEst p.processH (samEst p) X (rampAbove δ s) W XW → …`, whose `weight_reflected`
clause needs an e.c. LUV `W n` that `H`'s completed theory values *exactly* at
`rampAbove δ s (samEst p X n)`; `H`'s ledger records the merge's prices of *sentences*
(`aA j n`), and `samEst p X n` for a non-price `X` is a grid average of such prices, so no field
of `SamPair` supplies a quote LUV for the ramp. If no `(W, XW)` inhabits `WeightQuoteEst` at the
pinned instance, the OPEN is vacuously true there — the natural repair once a `SamPair` exists
is a `W`-constructor from the ledger at `succDeferral`, or the `CondTowerEstOn` /
`LUVTotalTrustAvgOn` form whose premises the ledger inhabits. Not machine-checked (cost); moot
while no `SamPair` exists.
Scope: two-way — Sam's structure; existence OPEN (`samPair_exists`); status `partial: over the
OPEN pair`. Computable branch.
Source: [[eisenstat-conjecture-attribution]] §1 ("Would they be trusted by `H`?"; "its beliefs will be endorsed by `H_t` (in the weak sense that makes sense in a logical induction context)"), §2 (ii), §4 item 6; root-deference-018; mandate T5
Kind: OPEN
Fidelity: variant: `trust-merge`'s `SoftTotalTrustAboveEst` at the merge estimate `samEst`, pending the accuracy notion
Hyps: (a) `hδ` -/
theorem samPair_trust_half (p : SamPair) (s δ : ℚ) (hδ : 0 < δ) :
    SoftTotalTrustAboveEst p.H p.processH (samEst p) s δ := by
  sorry

/-- **OPEN — existence of Sam's structure over `paperDP 𝗜𝚺₁`**, at `doublingDeferral`, with
publication after the lookahead. Reason OPEN: the two ledgers are mutually recursive (`H`'s table
reads the merge's beliefs, `A`'s table reads `H`'s prices) — the same joint well-founded
recursion as `li-coupled-pair`'s `twoWayPair_exists`, OPEN there on `UniformLIAEvaluator` (a
private FAF lemma, API request; `li-coupled-pair-open.txt`). The conditional construction
`twoWayPair_exists_of_uniform` is the model for a conditional `samPair_exists_of_uniform`, not
attempted here (report S2). **Second obstacle** (audit r1 fidelity N4): the row pins
`f = doublingDeferral`, so even granted `UniformLIAEvaluator` the `hQ` field needs
`samQuote_codes_doubling`, which is open (report S2 (i); only `samQuote_codes_succ` is proved).
Scope: two-way — Sam's structure. ATTRIBUTION-UNVETTED. Computable branch.
Source: [[eisenstat-conjecture-attribution]] §5 ("Formalizing Sam's intended structure is filed as open work"); `li-coupled-pair` `twoWayPair_exists`; mandate T5
Kind: OPEN
Fidelity: exact (the witness's data pinned: both bases `paperDP 𝗜𝚺₁`, `f = doublingDeferral`, publication after the lookahead)
Hyps: (a) none -/
theorem samPair_exists :
    ∃ p : SamPair, p.DPH0 = paperDP 𝗜𝚺₁ ∧ p.DPA0 = paperDP 𝗜𝚺₁ ∧ p.f = doublingDeferral ∧
      p.PublishesAfterLookahead := by
  sorry

/-! ## C. T4 / S1: the note's own (Gen) instance and its fallback (repair round 1) -/

/-- **OPEN — the note's own (Gen) instance at W1: the honest quote atom with no feedback.**
`w1H = liaHistory (paperDP 𝗜𝚺₁)` is FAF's paper LIA over the bare `paperDP 𝗜𝚺₁`, and
`ledgerQuotes φ n = ledgerLuv ⌜φ⌝ n` is the *same* quote atom W1's `A` prices honestly — but
here no ledger records it, so `A`'s process never decides it: the feedback clause is vacuous on
every sentence *with the quote kept*. This is [[merging-inductors-model]] §(a.1)'s no-feedback
hole as written — "`B_t(φ_t) = 𝔼^A_t(⌜μ_t⌝)` can be anything `A` likes. A trader that knows
`A`'s bias there exploits `B`" — stated in the note's direction. The market half is proved
(`honestQuote_noFeedback_w1_computable`, T2), so the open step is `noExploit`. **Direction
unknown:** nothing available pins the paper LIA's prices of never-decided atoms in either
direction (`fa-theorem-a` F15); the note's "trader that knows `A`'s bias" is the object a
refutation needs, and a proof would need the LIA's prices on the free atom family to be
unexploitable *as a sentence-indexed market over `paperDP`* — neither is a corpus result. What
T4 proves instead (`gen_refuted`) is the ∃-over-`Q` reading at the substituted quote `⊥`. The
general form of the note's scenario — honest quotes on every sentence with feedback (a ledger)
on a decidable *subclass* only — needs a partial ledger process, which `li-quote-lane`'s
`ledgerProcess` (all items, each with a schedule) does not provide; recorded as the next step
(findings F18).
Scope: one-way (corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam).
Source: [[merging-inductors-model]] §(a.1) (the no-feedback hole); trust-lab-008 ((Gen)); repair round 1 (audit r1 fidelity B2 (iv) / adversarial B1 (iv))
Kind: OPEN
Fidelity: variant: the paper LIA over the bare base in place of the note's `A` over a shared `Γ` with feedback on the observable class only (the all-vacuous end of the note's scenario); the quote is the note's
Hyps: (a) none -/
theorem gen_honestQuote_noFeedback_w1 :
    ¬ IsLogicalInductor (mergeMarket w1H ledgerQuotes) (paperDP 𝗜𝚺₁) := by
  sorry

/-- **OPEN — the note's fallback, "`B` is at best an inductor *on the good-feedback
subsequence*": the criterion along the even days.** For inductors `H` over `DPH` and `A` over
`DPA` (both with consistent stages) and the package of record `pkg` on every sentence, the mixed
merge `mergeMarket A (mixedQuotes Q)` — honest on the even days, `⊥` on the odd days — satisfies
the criterion along the even days (`InductorOn … {n | n % 2 = 0}`, `GenRefuted.lean` § E): no
e.c. trader *supported on the even days* exploits it against `DPH`. Its odd-day complement is
refuted (`gen_refuted_mixed_oddDays`); its unrestricted form is refuted (S1,
`gen_refuted_mixed_notInductor`) — this row is what S1 left open. **Why OPEN:** on the even days
the mixed merge is the honest merge (`mergeMarket_mixedQuotes_even`), so this is T3's question
restricted to even-day traders (whose coefficients may still read the odd-day prices
`ℙ^A_n(⊥) → 0`); it does not follow from `inductor_half_noExploit` (a different market off the
even days) and a refutation at W1 meets `fa-theorem-a` F15. `hworldH` is carried for the
fake-success trap (over a contradictory `DPH` every market satisfies `InductorOn` vacuously).
**Inhabited:** `fallback_evenDays_w1` below.
Scope: one-way (corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam).
Source: [[merging-inductors-model]] §(a.1) last sentence; [[merging-inductors-ideate]] Idea 1 ("inductor-like on the good-feedback subsequence, unconstrained off it"); repair round 1 (audit r1 fidelity B1 (optional) / adversarial B2)
Kind: OPEN
Fidelity: variant: one reading of the note's phrase (traders supported on the day-set; off it the refutable `⊥` in place of an undecided quote); no timing clause
Hyps: (a) `hworldH`, `hworldA`; (c) `pkg.reflected`; (c) `priceLuv ⊥` off the even days -/
theorem fallback_evenDays_noExploit {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q) :
    InductorOn (mergeMarket A (mixedQuotes Q)) DPH {n | n % 2 = 0} := by
  sorry

/-- **The fallback OPEN applied at W1:** the mixed merge over the all-sentences mirror pair,
honest on the even days, satisfies the criterion along the even days against `paperDP 𝗜𝚺₁`.
Every hypothesis of `fallback_evenDays_noExploit` is discharged (`w1_inductorH`, `w1_inductorA`,
both `hworld`s, `w1_pkg`); rests on its sorry (listed). Its point: the hypothesis package of the
fallback OPEN is inhabited (N+ for the package, as `inductor_half_w1`); the complementary
odd-day statement at the same instance is *refuted* (`gen_refuted_mixed_oddDays_w1`).
Source: repair round 1
Kind: OPEN
Fidelity: exact (an instance of the OPEN)
Hyps: (a) none (every hypothesis discharged) -/
theorem fallback_evenDays_w1 :
    InductorOn (mergeMarket w1A (mixedQuotes ledgerQuotes)) (paperDP 𝗜𝚺₁) {n | n % 2 = 0} :=
  haveI := w1_inductorH
  haveI := w1_inductorA
  fallback_evenDays_noExploit (H := w1H) (A := w1A) (paperDP_hworld 𝗜𝚺₁) w1_hworldA w1_pkg

end Cleanroom.Fa.FaEisenstatConj
