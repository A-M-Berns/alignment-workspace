import Cleanroom.Fa.FaEisenstatConj.Computable
import Cleanroom.Fa.FaEisenstatConj.GenRefuted
import Cleanroom.Fa.FaEisenstatConj.Companion
import Cleanroom.Fa.FaEisenstatConj.Transfer
import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Found.LiQuoteLane.MirrorPair
import Cleanroom.Li.LiPseudorandom.Market

/-!
# `fa-eisenstat-conj` · Witnesses: the N+ instances (W1–W3)

The only file of the package allowed to import `li-quote-lane`'s `Witnesses`/`MirrorPair`,
`li-pseudorandom`'s `Market` and (through them) FAF's `LIACompiler`.

* **W1 — the all-sentences mirror pair (N+; inhabits T3's full hypothesis package).**
  `H := liaHistory (paperDP 𝗜𝚺₁)` (FAF's paper LIA, price program `paperM`), `f := succDeferral`
  (the cheapest deferral; the instance is at `f n = n + 1`), the table
  `w1Table j n := paperM.quote (n + 1) ⌜decodeSentence j⌝` (`H`'s exact rational day-`f n` price
  of sentence `j`, junk-safe on non-codes), published at `σ n = f n + 1 = n + 2` — strictly
  after day `n`, so the quote is a *forecast* on day `n` (`w1_forecast`); `A := liaHistory` over
  `paperDP 𝗜𝚺₁ ⊕ ledger`, an inductor over it (`w1_inductorA`); `Q φ n := ledgerLuv ⌜φ⌝ n`.
  Every hypothesis of the OPEN `inductor_half_noExploit` is discharged: two real LIA markets
  over two distinct processes (`w1H ≠ w1A` is not stated), every sentence quoted (`w1_pkg`), the
  uniform quote table (`w1_quoteTable`), both `hworld`s. `w1_computableMerge` is T2 instantiated;
  `inductor_half_w1` (`Open.lean`) is the OPEN applied at W1 — the point is that the package is
  inhabited. Grade **N+** for the package: the markets are real, over distinct processes, the
  quotes are determined forecasts of every sentence's price, nothing is constant or empty. No
  claim about *which* prices the LIA assigns is made (`fa-theorem-a` F15: LIA prices of an
  undecided sentence are not pinned by anything available).
* **W2 — the (Gen) instance (grade split, repair round 1).** W1's `H` and `A` with the
  feedback-free quotes `botQuotes`: `gen_refuted`, the existential of T4 with the explicit
  trader. The *markets, trader and exploitation* are N+ (two real LIA markets over distinct
  processes, an e.c. trader with a certificate, exploitation proved); the *quote data* is N−:
  `botQuotes` is a constant family and the merged market is constant across sentences on every
  day (`mergeMarket_botQuotes`), and the exploitation uses nothing about `H`, `DPH` or `f` —
  those conjuncts of the existential are decorative (`gen_refuted_of` has no `H`). S1's instance
  `gen_refuted_evenDays` uses `mixedQuotes ledgerQuotes` — W1's honest quote on the even days —
  and is the non-constant variant; its even-day honesty conjunct is a disclosure, not an
  ingredient. The note's own (Gen) instance — the honest quote atom with no feedback — is
  `gen_honestQuote_noFeedback_w1` (`Open.lean`, OPEN), whose market half
  `honestQuote_noFeedback_w1_computable` is proved here; the note's fallback along the odd days
  is refuted here (`gen_refuted_mixed_oddDays_w1`) and along the even days OPEN
  (`fallback_evenDays_w1`, `Open.lean`).
* **W3 — the decided case with content (N+ for E1).** `fa-theorem-a`'s W2 lifted to the
  all-sentences ledger: `H := liaHistory (atomDP id x (·+1))` for any primitive recursive stream
  `x` (`li-pseudorandom`), which decides `atom k` at stage `k + 1` with truth `x k`; `A` the
  all-sentences mirror ledger of `H` over `paperDP 𝗜𝚺₁` (the ledger is added to `A`'s base, so
  `atomDP`'s atoms are not in question for the free-of check). Conclusion:
  `𝔼^∗_n(atom k) → truthR x k` with the limit *named* and day-varying (`decided_w3`) — a family of
  instances over all primitive recursive `x` and all `k`, on two real LIA markets over distinct
  processes.

Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`
(corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). Fidelity of the package at
every witness: `variant` (ledger-recorded determinacy in place of `Γ_A`-provable determinacy).
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Bli.BliFound Cleanroom.Fa.FaTheoremA Cleanroom.Li.LiPseudorandom
open Filter Topology

/-! ## A. The all-sentences price ledger of a market program -/

/-- **The all-sentences realized-price table** of a market program `M` along the deferral `f`:
item `j` (a sentence code), day `n`, is `M`'s exact rational day-`f n` price of `decodeSentence j`
(`⊤` on a non-code, so every entry is a real price and the table is `[0,1]`-valued).
Source: mandate W1 (`aH j n := paperM.quote (f.f n) j`, junk-safe)
Kind: D
Fidelity: exact
Hyps: n/a -/
def priceTable {P : History} (M : MarketComputation P) (f : DeferralFunction) (j n : ℕ) : ℚ :=
  M.quote (f.f n) (Encodable.encode (decodeSentence j))

/-- The table's cast at a sentence code is the market's realized price.
Source: none: infrastructure (FAF `quote_exact`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem priceTable_cast {P : History} (M : MarketComputation P) (f : DeferralFunction)
    (φ : Sentence) (n : ℕ) : (priceTable M f (Encodable.encode φ) n : ℝ) = P (f.f n) φ := by
  unfold priceTable
  rw [decodeSentence_encode, M.quote_exact]

/-- The table is `[0,1]`-valued (every entry is a real price).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem priceTable_mem {P : History} (M : MarketComputation P) (f : DeferralFunction) (j n : ℕ) :
    0 ≤ priceTable M f j n ∧ priceTable M f j n ≤ 1 := by
  have h := M.price_mem_Icc (f.f n) (decodeSentence j)
  rw [M.quote_exact] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The table is computable (the market program on the computable deferral and decoder).
Source: none: infrastructure (FAF `quote_comp_computable`, `DeferralFunction.computable`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem priceTable_computable {P : History} (M : MarketComputation P) (f : DeferralFunction) :
    Computable fun p : ℕ × ℕ => priceTable M f p.1 p.2 :=
  (quote_comp_computable M (f.computable.comp Computable.snd)
    (Computable.encode.comp (decodeSentence_computable.comp Computable.fst)) : _)

/-- **The payout schedule of the all-sentences mirror ledger**: `σ n = f n + 1`, immediately after
the lookahead — the day-`f n` price is in `A`'s process at stage `f n + 1`, and not before.
Source: mandate W1 (`σ := fun n => f.f n + 1`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def afterLookahead (f : DeferralFunction) : PublicationSchedule :=
  ⟨fun n => f.f n + 1, fun n => by have := f.lt n; omega⟩

/-- The payout schedule is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem afterLookahead_computable (f : DeferralFunction) :
    Computable fun p : ℕ × ℕ => ((fun _ : ℕ => afterLookahead f) p.1).e p.2 :=
  (Primrec.succ.to_comp.comp (f.computable.comp Computable.snd)).of_eq fun _ => rfl

/-- **The all-sentences mirror process**: the base plus the price ledger of `M`'s market along `f`,
published at `f n + 1`.
Source: mandate W1
Kind: D
Fidelity: exact
Hyps: n/a -/
def mirrorAllProcess {P : History} (M : MarketComputation P) (f : DeferralFunction)
    (base : DeductiveProcess) : DeductiveProcess :=
  ledgerProcess base (priceTable M f) (fun _ => afterLookahead f)

/-- **The all-sentences quote assignment**: `Q φ n := ledgerLuv ⌜φ⌝ n`, the ledger item of
sentence `φ` on day `n` (which records `P (f n) φ`).
Source: mandate W1 (`Q φ n := ledgerLuv (encode φ) n`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ledgerQuotes : Sentence → ℕ → LUV := fun φ n => ledgerLuv (Encodable.encode φ) n

/-- **The all-sentences quote table is computable**: the threshold sentence `⌜α_{⌜φ⌝,n} > r⌝` is
one atom whose code is a fixed pair shell around `(n, ⌜φ⌝, ⌜r⌝)` (`li-quote-lane`'s
`encode_ledgerLuv_gt`), primitive recursive in the three.
Source: mandate W1 (`hQ : QuoteTable Q` from `ledgerLuv`'s computable thresholds)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerQuotes_quoteTable : QuoteTable ledgerQuotes := by
  unfold QuoteTable ledgerQuotes
  refine Computable.encode_iff.mp ?_
  have hcode : Primrec fun p : (Sentence × ℕ) × ℚ =>
      Nat.pair 1 (Nat.pair (cleanroomBaseTag + ledgerFamily)
        (Nat.pair p.1.2 (Nat.pair (Encodable.encode p.1.1) (Encodable.encode p.2)))) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.const _)
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
          (Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.encode.comp Primrec.snd)))))
  exact hcode.to_comp.of_eq fun p => (encode_ledgerLuv_gt _ _ _).symm

/-- Every all-sentences quote family is e.c. (`li-quote-lane`'s `ledgerLuv_thresholdCodes`).
Source: mandate W1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerQuotes_codes (φ : Sentence) : LUV.MachineThresholdCodeSeq (ledgerQuotes φ) :=
  ledgerLuv_thresholdCodes (Encodable.encode φ)

/-- **The package of record is a theorem over the all-sentences mirror process** (N+ for the
package): `A`'s process determines every `ledgerLuv ⌜φ⌝ n` at `P (f n) φ` (`li-quote-lane`'s
`ledgerLuv_determinedVia` on the price table), and every family is e.c. The package's (c) is here
(a) at variant fidelity (ledger-recorded).
Source: mandate W1 (`pkg : MergeQuotes H DPA f Q` from `ledgerLuv_determinedVia`)
Kind: C
Fidelity: variant: ledger-recorded determinacy in place of `Γ_A`-provable determinacy
Hyps: (a) none -/
theorem mergeQuotes_mirrorAll {P : History} (M : MarketComputation P) (f : DeferralFunction)
    (base : DeductiveProcess) : MergeQuotes P (mirrorAllProcess M f base) f ledgerQuotes :=
  MergeQuotes.of_price ledgerQuotes_codes fun φ n => by
    have h := ledgerLuv_determinedVia base (priceTable M f) (fun _ => afterLookahead f)
      (priceTable_mem M f) (Encodable.encode φ) n
    rw [priceTable_cast] at h
    exact h

/-- The mirror LIA is an inductor over the all-sentences mirror process (FAF's
`LIA_is_logical_inductor` on `ledgerProcess_computable`).
Source: mandate W1 (the `mirrorPair_inductor` pattern)
Kind: C
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem mirrorAll_inductor {P : History} (M : MarketComputation P) (f : DeferralFunction)
    (base : DeductiveProcess) (hbase : ComputableDeductiveProcess base) :
    IsLogicalInductor (liaHistory (mirrorAllProcess M f base)) (mirrorAllProcess M f base) :=
  LIA_is_logical_inductor _
    (ledgerProcess_computable hbase (priceTable_computable M f) (afterLookahead_computable f))

/-- **The quote is a forecast, not a lookup:** no literal of `ledgerLuv ⌜φ⌝ n` is in `A`'s
schedule before stage `f n + 1 > n` (`li-quote-lane`'s `ledgerLuv_absent_before_payout`).
Source: mandate W1 (the `w1_forecast`-style lemma)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mirrorAll_forecast {P : History} (M : MarketComputation P) (f : DeferralFunction)
    (φ : Sentence) (n : ℕ) (r : ℚ) (b : Bool) {s : ℕ} (hs : s ≤ f.f n) :
    (ledgerFamily, ledgerPayload (Encodable.encode φ) n (Encodable.encode r), b) ∉
      (ledgerSchedule (priceTable M f) (fun _ => afterLookahead f)).lits s :=
  ledgerLuv_absent_before_payout _ _ (Encodable.encode φ) n r b
    (by show s < f.f n + 1; omega)

/-! ## B. W1: the all-sentences mirror pair over `paperDP 𝗜𝚺₁` -/

/-- W1's `H`: FAF's LIA over `paperDP 𝗜𝚺₁`.
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1H : History := liaHistory (paperDP 𝗜𝚺₁)

/-- W1's `A`-process: `paperDP 𝗜𝚺₁` plus the all-sentences price ledger of `H` along
`succDeferral`, published at `n + 2`.
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1Process : DeductiveProcess :=
  mirrorAllProcess paperM succDeferral (paperDP 𝗜𝚺₁)

/-- W1's `A`: FAF's LIA over `w1Process` (a different process from `H`'s, hence a different
market).
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1A : History := liaHistory w1Process

/-- W1: `H` is a logical inductor over `paperDP 𝗜𝚺₁`.
Source: mandate W1; FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w1_inductorH : IsLogicalInductor w1H (paperDP 𝗜𝚺₁) :=
  LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁)

/-- W1: `A` is a logical inductor over its ledger process.
Source: mandate W1
Kind: L
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem w1_inductorA : IsLogicalInductor w1A w1Process :=
  mirrorAll_inductor paperM succDeferral (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)

/-- W1: every stage of `A`'s process is satisfiable (`li-quote-lane`'s
`ledgerProcess_paperDP_hworld`: the ledger's atoms are free of `paperDP`'s and `IΣ₁` is consistent).
Source: mandate W1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w1_hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (w1Process.D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- W1: the package of record on every sentence, derived.
Source: mandate W1
Kind: L
Fidelity: variant (ledger-recorded determinacy)
Hyps: (a) none -/
theorem w1_pkg : MergeQuotes w1H w1Process succDeferral ledgerQuotes :=
  mergeQuotes_mirrorAll paperM succDeferral (paperDP 𝗜𝚺₁)

/-- W1: the quote is a forecast — at day `n` no literal of `ledgerLuv ⌜φ⌝ n` is in `A`'s schedule
(it enters at `n + 2`).
Source: mandate W1 (`w1_forecast`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem w1_forecast (φ : Sentence) (n : ℕ) (r : ℚ) (b : Bool) :
    (ledgerFamily, ledgerPayload (Encodable.encode φ) n (Encodable.encode r), b) ∉
      (ledgerSchedule (priceTable paperM succDeferral)
        (fun _ => afterLookahead succDeferral)).lits n :=
  mirrorAll_forecast paperM succDeferral φ n r b (succDeferral.lt n).le

/-- **W1 (N+): T2 instantiated — the merge market over the all-sentences mirror pair is a
computable market.** Every hypothesis of the OPEN `inductor_half_noExploit` is inhabited here:
`[IsLogicalInductor w1H (paperDP 𝗜𝚺₁)]`, `[IsLogicalInductor w1A w1Process]`,
`paperDP_hworld 𝗜𝚺₁`, `w1_hworldA`, `ledgerQuotes_quoteTable`, `w1_pkg` — see `inductor_half_w1`
(`Open.lean`) for the application.
Source: mandate W1 (`w1_inductorMerge`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w1_computableMerge : ComputableMarket (mergeMarket w1A ledgerQuotes) :=
  haveI := w1_inductorA
  mergeMarket_computableMarket_of_inductor (DPA := w1Process) ledgerQuotes_quoteTable

/-- **W1 (N+ for the package): Claim 2 on every sentence at the mirror pair** — `𝔼^∗_n(φ) − ℙ^H_n(φ)
→ 0` for every `φ`, every hypothesis of `mergeMarket_asympEq` discharged on two real LIA markets.
Content grade: `fa-theorem-a` F15 — which values the LIA assigns an undecided sentence is not
pinned, so non-degeneracy of the *convergence* (a day with `𝔼^∗_n(φ) ≠ ℙ^H_n(φ)`) is not proved;
the instance with named limits is W3.
Source: mandate E1 (witness)
Kind: N+
Fidelity: variant (as `mergeQuotes_mirrorAll`)
Hyps: (a) none -/
theorem mergeMarket_asympEq_w1 (φ : Sentence) :
    AsympEq (fun n => mergeMarket w1A ledgerQuotes n φ) (fun n => w1H n φ) :=
  haveI := w1_inductorH
  haveI := w1_inductorA
  mergeMarket_asympEq (H := w1H) (A := w1A) (paperDP_hworld 𝗜𝚺₁) w1_hworldA w1_pkg φ

/-- **W1: the surviving neighbour at `⊤`** — `𝔼^∗_n(⊤) → 1` over the mirror pair (N−: `⊤` is the
degenerate theorem; W3 has day-varying limits).
Source: mandate E1 (witness)
Kind: N-
Fidelity: variant
Hyps: (a) none -/
theorem mergeMarket_provind_w1_top :
    Tendsto (fun n => mergeMarket w1A ledgerQuotes n ⊤) atTop (𝓝 1) :=
  haveI := w1_inductorH
  haveI := w1_inductorA
  mergeMarket_provind (H := w1H) (A := w1A) (paperDP_hworld 𝗜𝚺₁) w1_hworldA w1_pkg ⊤
    (fun v _ => PCWorld.holds_top v)

/-! ## C. W2: the (Gen) instance over the mirror pair -/

/-- **T4 (headline). (Gen) refuted over the one-way pair, in the ∃-over-`Q` reading:** two real
LIA markets over distinct processes (`H := liaHistory (paperDP 𝗜𝚺₁)`, `A := liaHistory` over the
all-sentences mirror ledger of `H`), a legal feedback-free quote assignment (`botQuotes`: e.c.,
uniformly computable, `[0,1]`-valued), and an explicit e.c. trader (`buyOneDaily ⊤`, certificate
`buyOneDaily_efficientlyComputable`) that exploits the merge market against `H`'s process.
**What the statement does not carry:** no clause ties `Q` to `H` — the exploitation is from
`A`'s data alone (`gen_refuted_of`), so the `H`, `DPH` and `f` witnesses are decorative (the
binder `f` is unused, by design: the statement is the mandate's). The quote data is the
substituted `⊥` (`GenRefuted.lean` module docstring), under which the merge is constant across
sentences; this is why the witness grade is split: **N+** for the markets, trader and
exploitation, **N−** for the quote data. The note's own instance is OPEN
(`gen_honestQuote_noFeedback_w1`). The surviving neighbour is `mergeMarket_provind`.
Scope: one-way (corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam).
Source: trust-lab-008 ((Gen), "L"); [[merging-inductors-model]] §(a.1); [[merging-inductors-ideate]] Idea 1 (1b); mandate T4
Kind: P
Fidelity: variant: the ∃-over-`Q` reading at the substituted quote `botQuotes` (see `gen_refuted_of`)
Hyps: (a) none; (c) `botQuotes` in place of the honest quote without feedback -/
theorem gen_refuted :
    ∃ (H A : History) (DPH DPA : DeductiveProcess) (f : DeferralFunction)
      (Q : Sentence → ℕ → LUV),
      IsLogicalInductor H DPH ∧ IsLogicalInductor A DPA ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      QuoteTable Q ∧ (∀ φ, LUV.MachineThresholdCodeSeq (Q φ)) ∧
      ∃ Tr : Trader, EfficientlyComputable Tr ∧ Tr.Exploits (mergeMarket A Q) DPH :=
  haveI := w1_inductorA
  ⟨w1H, w1A, paperDP 𝗜𝚺₁, w1Process, succDeferral, botQuotes, w1_inductorH, w1_inductorA,
    paperDP_hworld 𝗜𝚺₁, w1_hworldA, botQuotes_quoteTable, botQuotes_codes,
    buyOneDaily ⊤, buyOneDaily_efficientlyComputable ⊤,
    gen_refuted_of (A := w1A) w1_hworldA (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)⟩

/-- **T4, criterion form at W1:** the feedback-free merge over the mirror pair is not a logical
inductor over `H`'s process — nor over any process with consistent stages. Same scope as
`gen_refuted` (the substituted quote `botQuotes`).
Source: trust-lab-008; mandate T4 (stronger form)
Kind: P
Fidelity: variant: as `gen_refuted`
Hyps: (a) none; (c) `botQuotes` -/
theorem gen_refuted_w1 : ¬ IsLogicalInductor (mergeMarket w1A botQuotes) (paperDP 𝗜𝚺₁) :=
  haveI := w1_inductorA
  gen_refuted_notInductor (A := w1A) w1_hworldA (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)

/-- **The market half of the note's own (Gen) instance at W1:** the merge of the paper LIA
`w1H = liaHistory (paperDP 𝗜𝚺₁)` with the honest quote atoms `ledgerQuotes` — atoms its process
`paperDP 𝗜𝚺₁` never decides (no ledger; the feedback clause is vacuous on every sentence *with
the quote kept*) — is a `ComputableMarket` (T2), so the OPEN `gen_honestQuote_noFeedback_w1`
(`Open.lean`) sits on `noExploit` alone.
Source: [[merging-inductors-model]] §(a.1) (the no-feedback hole, with the honest quote); repair round 1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem honestQuote_noFeedback_w1_computable :
    ComputableMarket (mergeMarket w1H ledgerQuotes) :=
  mergeMarket_computableMarket w1_inductorH.marketComputable ledgerQuotes_quoteTable

/-- **S1 (headline). Honest quotes on the even days do not make the merge an inductor
unrestricted, over the mirror pair:** with W1's honest determined quote `ledgerLuv ⌜φ⌝ n` on the
even days and `priceLuv ⊥` on the odd days, `buyOneDaily ⊤` exploits the merge against `H`'s
process. The even days are a divergent `A`-generable day-set (`fa-theorem-a`'s
`evenDays_pgenerable`), the model's own `w`. The even-day determinacy conjunct is a
*disclosure* of the instance (so an auditor can see the even-day quote is the honest one), not
an ingredient of the exploitation, which uses the odd days only. This *agrees with* the note's
"unconstrained off it"; the note's fallback proper is `fallback_evenDays_w1` (OPEN) and its
odd-day complement `gen_refuted_mixed_oddDays_w1` (refuted), below. Grade: N+ for the markets,
trader and exploitation; the quote data is honest on the even days and the substituted `⊥` on
the odd days.
Scope: one-way (corpus construal; ATTRIBUTION-UNVETTED as to Sam).
Source: [[merging-inductors-model]] §(a.1) last sentence; [[merging-inductors-ideate]] Idea 1; mandate S1
Kind: P
Fidelity: variant: odd-day quotes are the refutable `⊥`, not undecided honest quotes (as `gen_refuted_mixed_of`)
Hyps: (a) none; (c) `priceLuv ⊥` off the even days -/
theorem gen_refuted_evenDays :
    ∃ (H A : History) (DPH DPA : DeductiveProcess) (f : DeferralFunction)
      (Q : Sentence → ℕ → LUV),
      IsLogicalInductor H DPH ∧ IsLogicalInductor A DPA ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      QuoteTable Q ∧ (∀ φ, LUV.MachineThresholdCodeSeq (Q φ)) ∧
      (∀ φ n, n % 2 = 0 → LUV.DeterminedVia (Q φ n) DPA (H (f.f n) φ)) ∧
      ∃ Tr : Trader, EfficientlyComputable Tr ∧ Tr.Exploits (mergeMarket A Q) DPH :=
  haveI := w1_inductorA
  ⟨w1H, w1A, paperDP 𝗜𝚺₁, w1Process, succDeferral, mixedQuotes ledgerQuotes, w1_inductorH,
    w1_inductorA, paperDP_hworld 𝗜𝚺₁, w1_hworldA, mixedQuotes_quoteTable ledgerQuotes_quoteTable,
    mixedQuotes_codes ledgerQuotes_codes,
    fun φ n hn => by
      have h := w1_pkg.reflected_price φ n
      simpa [mixedQuotes, hn] using h,
    buyOneDaily ⊤, buyOneDaily_efficientlyComputable ⊤,
    gen_refuted_mixed_of (A := w1A) w1_hworldA ledgerQuotes (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)⟩

/-- **S1, the odd-day complement at W1 (refuted):** along the odd days — where the mixed quote
is the refutable `⊥` — the mixed merge over the mirror pair fails the criterion along the day-set
(`InductorOn`), exploited by the certified odd-day trader `buyTopOdd` against `H`'s process.
The even-day half, the note's fallback proper, is OPEN (`fallback_evenDays_w1`, `Open.lean`).
Scope: one-way (corpus construal; ATTRIBUTION-UNVETTED as to Sam).
Source: [[merging-inductors-model]] §(a.1) last sentence ("unconstrained off it"); repair round 1
Kind: P
Fidelity: variant: as `gen_refuted_mixed_oddDays`
Hyps: (a) none; (c) `priceLuv ⊥` off the even days -/
theorem gen_refuted_mixed_oddDays_w1 :
    ¬ InductorOn (mergeMarket w1A (mixedQuotes ledgerQuotes)) (paperDP 𝗜𝚺₁) {n | n % 2 = 1} :=
  haveI := w1_inductorA
  gen_refuted_mixed_oddDays (A := w1A) w1_hworldA ledgerQuotes (paperDP 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁)

/-! ## D. W3: the decided case with content -/

/-- W3's `H`-process: `li-pseudorandom`'s `atomDP id x (·+1)`, which decides `atom k` at stage
`k + 1` with truth `x k`.
Source: mandate W3; `fa-theorem-a` W2
Kind: D
Fidelity: n/a -/
abbrev w3DP (x : ℕ → Bool) : DeductiveProcess := atomDP id x (fun j => j + 1)

/-- W3's `H`: FAF's LIA over `w3DP x`.
Source: mandate W3
Kind: D
Fidelity: n/a -/
noncomputable abbrev w3H (x : ℕ → Bool) : History := liaHistory (w3DP x)

/-- W3: `H` is a logical inductor over `w3DP x` for primitive recursive `x`.
Source: mandate W3; `li-pseudorandom` `atomDP_succ_isLogicalInductor`
Kind: L
Fidelity: n/a
Hyps: (a) `hx` -/
theorem w3_inductorH {x : ℕ → Bool} (hx : Primrec x) : IsLogicalInductor (w3H x) (w3DP x) :=
  atomDP_succ_isLogicalInductor Primrec.id hx

/-- W3: every stage of `H`'s process is satisfiable (the atom world).
Source: mandate W3; `li-pseudorandom` `atomDP_hworld`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w3_hworldH (x : ℕ → Bool) : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((w3DP x).D n) :=
  atomDP_hworld Function.injective_id x _

/-- W3: `H`'s exact market program, read off the inductor certificate.
Source: none: infrastructure (W3)
Kind: D
Fidelity: n/a -/
noncomputable def w3M {x : ℕ → Bool} (hx : Primrec x) : MarketComputation (w3H x) :=
  (w3_inductorH hx).marketComputable.nonemptyComputation.some

/-- W3's `A`-process: `paperDP 𝗜𝚺₁` plus the all-sentences price ledger of `H` along
`succDeferral`.
Source: mandate W3
Kind: D
Fidelity: n/a -/
noncomputable abbrev w3Process {x : ℕ → Bool} (hx : Primrec x) : DeductiveProcess :=
  mirrorAllProcess (w3M hx) succDeferral (paperDP 𝗜𝚺₁)

/-- W3's `A`: FAF's LIA over `w3Process hx`.
Source: mandate W3
Kind: D
Fidelity: n/a -/
noncomputable abbrev w3A {x : ℕ → Bool} (hx : Primrec x) : History := liaHistory (w3Process hx)

/-- W3: `A` is a logical inductor over its ledger process.
Source: mandate W3
Kind: L
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem w3_inductorA {x : ℕ → Bool} (hx : Primrec x) :
    IsLogicalInductor (w3A hx) (w3Process hx) :=
  mirrorAll_inductor (w3M hx) succDeferral (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)

/-- W3: every stage of `A`'s process is satisfiable.
Source: mandate W3
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w3_hworldA {x : ℕ → Bool} (hx : Primrec x) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((w3Process hx).D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- W3: the package of record on every sentence, derived.
Source: mandate W3
Kind: L
Fidelity: variant (ledger-recorded determinacy)
Hyps: (a) none -/
theorem w3_pkg {x : ℕ → Bool} (hx : Primrec x) :
    MergeQuotes (w3H x) (w3Process hx) succDeferral ledgerQuotes :=
  mergeQuotes_mirrorAll (w3M hx) succDeferral (paperDP 𝗜𝚺₁)

/-- **W3: the determinacy of `priceLuv (atom k)` at `truthR x k` is derived** from
`li-pseudorandom`'s `atomDP_theoryTruth` (the literal of `k` is in stage `k + 1`) and
`priceLuv_valued`.
Source: mandate W3; root-fa-2-006
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem w3_determined (x : ℕ → Bool) (k : ℕ) :
    LUV.DeterminedVia (priceLuv (Formula.atom k)) (w3DP x) (truthR x k) := by
  intro v hv
  have h := atomDP_theoryTruth (a := id) (g := fun j => j + 1) (fun j => Nat.lt_succ_self j) x k
    v hv
  have h2 := priceLuv_valued (Formula.atom k) v
  rw [← h]
  exact h2

/-- **W3 (headline, N+). The decided case of E1 with content:** for every primitive recursive
truth stream `x` and every `k`, over two real LIA markets, over distinct processes, `w3H x` (which decides
`atom k` at stage `k + 1` with truth `x k`) and `w3A hx` (the all-sentences mirror ledger of
`H`), `𝔼^∗_n(atom k) → truthR x k` — the limit named and day-varying (`1` or `0` according to
`x k`), every hypothesis of `mergeMarket_decided` discharged on a family of instances that
includes non-constant streams.
Source: mandate W3 (`decided_w2`'s standard); root-fa-2-006
Kind: N+
Fidelity: variant (as `mergeQuotes_mirrorAll`)
Hyps: (a) `hx` -/
theorem decided_w3 {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    Tendsto (fun n => mergeMarket (w3A hx) ledgerQuotes n (Formula.atom k)) atTop
      (𝓝 (truthR x k)) :=
  haveI := w3_inductorH hx
  haveI := w3_inductorA hx
  mergeMarket_decided (H := w3H x) (A := w3A hx) (w3_hworldH x) (w3_hworldA hx) (w3_pkg hx) (Formula.atom k)
    (w3_determined x k)

/-- W3: T2 instantiated — the merge market over W3's pair is a computable market.
Source: mandate W3
Kind: L
Fidelity: exact
Hyps: (a) `hx` -/
theorem w3_computableMerge {x : ℕ → Bool} (hx : Primrec x) :
    ComputableMarket (mergeMarket (w3A hx) ledgerQuotes) :=
  haveI := w3_inductorA hx
  mergeMarket_computableMarket_of_inductor (DPA := w3Process hx) ledgerQuotes_quoteTable

/-! ## E. E2: per-sentence asymptotic equality does not transfer the criterion, at the paper LIA -/

/-- **E2 (headline, N+). Per-sentence asymptotic equality to an inductor does not transfer the
criterion:** at FAF's paper LIA `P := liaHistory (paperDP 𝗜𝚺₁)`, the damped market `damped P` is a
computable market per-sentence (indeed uniformly) asymptotically equal to `P` and is not a logical
inductor over `paperDP 𝗜𝚺₁` (`Transfer.lean`). So E1's `𝔼^∗_n(φ) − ℙ^H_n(φ) → 0` settles the
inductor half in neither direction.
Source: mandate E2 (i) (stated there as an OPEN "direction unknown"; the direction is settled: the transfer fails)
Kind: P
Fidelity: stronger: uniform in the sentence
Hyps: (a) none -/
theorem asympEq_not_transfer :
    ∃ (P P' : History) (DP : DeductiveProcess), IsLogicalInductor P DP ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧ ComputableMarket P' ∧
      (∀ φ, AsympEq (fun n => P' n φ) (fun n => P n φ)) ∧ ¬ IsLogicalInductor P' DP :=
  haveI := w1_inductorH
  ⟨w1H, damped w1H, paperDP 𝗜𝚺₁, w1_inductorH, paperDP_hworld 𝗜𝚺₁,
    damped_computableMarket w1_inductorH.marketComputable,
    damped_asympEq (IsLogicalInductor.price_mem_Icc (P := w1H) (DP := paperDP 𝗜𝚺₁)),
    damped_not_inductor (P := w1H) (paperDP_hworld 𝗜𝚺₁)⟩

end Cleanroom.Fa.FaEisenstatConj
