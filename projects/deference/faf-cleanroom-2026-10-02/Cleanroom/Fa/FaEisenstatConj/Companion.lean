import Cleanroom.Fa.FaEisenstatConj.Defs
import Cleanroom.Fa.FaTheoremA.TheoremA
import Cleanroom.Fa.FaTheoremA.LemmaP
import Cleanroom.Fa.FaTheoremA.Decided

/-!
# `fa-eisenstat-conj` · Companion: the positive companion on every sentence (E1)

The largest fragment of the conjecture the corpus can already prove, restated for the merge
market `𝔼^∗ = mergeMarket A Q` on **all sentences**: under the package of record `MergeQuotes`,

* **`mergeMarket_asympEq`** — `𝔼^∗_n(φ) − ℙ^H_n(φ) → 0` for every sentence `φ`, with arbitrary
  delay `f` and no human-side visibility (`fa-theorem-a`'s Claim 2 at `X := priceLuv φ`);
* `mergeMarket_dominates` / `mergeMarket_dominates_below` — Theorem A both ways;
* **`mergeMarket_lemmaP`** — Lemma P on a generable `{0,1}`-valued day-set;
* **`mergeMarket_provind`** (+ `_neg`) — the surviving neighbour of the (Gen) refutation: on every
  theorem of `DPH`, `𝔼^∗_n(φ) → 1` (and on every refutable sentence `→ 0`) — exactly the property
  the feedback-free instances of `GenRefuted.lean` violate.

In words: **the merge is per-sentence asymptotically equal to `H`'s own prices.** The inductor half
(`Open.lean`) therefore asks whether a market per-sentence asymptotically equal to an inductor
(not uniformly in the sentence) is an inductor over the same process — a sharper phrasing of the
OPEN. `Transfer.lean` shows this does *not* follow in general (even uniform asymptotic equality
fails to transfer the criterion), so E1 settles the inductor half in neither direction.

Hypothesis grading: `fa-theorem-a` graded Theorem A's `hval` "(c) per FAF" and discharged it at
witnesses; here `priceLuv_valued` discharges it for every `φ` at headline level — (a), a strict
improvement (Known issue 9). The package's one (c) remains `pkg.reflected` (per sentence).

Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`. This is
the lookahead construction in the **corpus construal (Abram's version)**, not Sam Eisenstat's
intended information structure ([[eisenstat-conjecture-attribution]] §2, §5); claims about Sam's
intent are ATTRIBUTION-UNVETTED.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Fa.FaTheoremA
open Filter Topology

/-- The merge market at `φ` is `fa-theorem-a`'s quote sequence of the family `Q φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mergeMarket_eq_quoteSeq (A : History) (Q : Sentence → ℕ → LUV) (φ : Sentence) :
    (fun n => mergeMarket A Q n φ) = quoteSeq (Q φ) A := rfl

/-- `fa-theorem-a`'s realized target at the price LUV is `H`'s realized price.
Source: none: infrastructure (`priceLuv_expect`)
Kind: L
Fidelity: n/a -/
theorem realized_priceLuv (H : History) (f : DeferralFunction) (φ : Sentence) :
    realized H f (fun _ => priceLuv φ) = fun n => H (f.f n) φ :=
  funext fun n => priceLuv_expect φ H (f.f n)

/-- **E1 (headline). Claim 2 on every sentence:** under the package of record,
`𝔼^∗_n(φ) − ℙ^H_n(φ) → 0` for every sentence `φ` (FAF's `AsympEq`) — `fa-theorem-a`'s `claim2` at
`X := priceLuv φ`, with `hcode := priceLuv_codes φ` and `hval` discharged by `priceLuv_valued`.
Arbitrary delay `f`, no human-side visibility. In words: the merge is per-sentence
asymptotically equal to `H`'s own prices.
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`
(corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The only modelling step is
the quote's determinacy, `pkg.reflected` (`MergeQuotes`) — `A`'s theory determines `H`'s realized
prices; at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[eisenstat-lookahead-construction]] §3.1 Claim 2 (vq-wiki-058); [[eisenstat-conjecture-attribution]] §1 ("`A`'s beliefs about `H` should converge to the same limit as `H` does" — limit agreement, the easy lemma, here per day); vq-wiki-044 (the positives "about Abram's version"); mandate E1
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) `hworldH`, `hworldA` (FAF's disclosed world boundaries), `hcode`/`hval` discharged by `priceLuv_codes`/`priceLuv_valued`; (c) `pkg.reflected` as above. -/
theorem mergeMarket_asympEq {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) :
    AsympEq (fun n => mergeMarket A Q n φ) (fun n => H n φ) := by
  have h := claim2 (H := H) (A := A) (priceLuv φ) (priceLuv_codes φ) hworldH
    (fun v _ => ⟨_, priceLuv_valued φ v⟩) hworldA (pkg φ)
  rw [mergeMarket_eq_quoteSeq]
  simpa only [priceLuv_expect] using h

/-- **E1, Theorem A (above):** `H`'s price dominates the merge's — for every `c > 0` only finitely
many days have `𝔼^∗_n(φ) ≥ ℙ^H_n(φ) + c`.
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A` (corpus
construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The only modelling step is
`pkg.reflected`; at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[eisenstat-lookahead-construction]] §3.1 (vq-wiki-058); mandate E1
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) as `mergeMarket_asympEq`; (c) `pkg.reflected` -/
theorem mergeMarket_dominates {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) :
    Dominates (fun n => H n φ) (fun n => mergeMarket A Q n φ) := by
  have h := theoremA (H := H) (A := A) (priceLuv φ) (priceLuv_codes φ) hworldH
    (fun v _ => ⟨_, priceLuv_valued φ v⟩) hworldA (pkg φ)
  rw [mergeMarket_eq_quoteSeq]
  simpa only [priceLuv_expect] using h

/-- **E1, Theorem A (below):** the merge's price dominates `H`'s.
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A` (corpus
construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The only modelling step is
`pkg.reflected`; at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[route-recurring-ccee]] §4 (the dual gate); mandate E1
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) as `mergeMarket_asympEq`; (c) `pkg.reflected` -/
theorem mergeMarket_dominates_below {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) :
    Dominates (fun n => mergeMarket A Q n φ) (fun n => H n φ) := by
  have h := theoremA_below (H := H) (A := A) (priceLuv φ) (priceLuv_codes φ) hworldH
    (fun v _ => ⟨_, priceLuv_valued φ v⟩) hworldA (pkg φ)
  rw [mergeMarket_eq_quoteSeq]
  simpa only [priceLuv_expect] using h

/-- **E1, Lemma P on a day-set:** for a generable `{0,1}`-valued day-set feature `E` of `A`'s
market, if `H`'s realized price `ℙ^H_{f n}(φ) → c` along `E` then `𝔼^∗_n(φ) → c` along `E`
(`fa-theorem-a`'s `lemmaP` at `X := priceLuv φ`). No `H`-side convergence hypothesis beyond the
along-`E` one; the human-side visibility is nil.
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A` (corpus
construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The only modelling step is
`pkg.reflected`; at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[route-negative-introspective]] §7 Lemma P (vq-wiki-058); mandate E1
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: variant: as `fa-theorem-a`'s `lemmaP` (`E` a `{0,1}`-valued `PGenerableWeighting`; "along `E`" is `atTop ⊓ 𝓟 {E = 1}`; finite-support `E` makes the filter `⊥`, disclosed there)
Hyps: (a) `hworldA`, `hE`, `hE01`, `hY`; (c) `pkg.reflected` -/
theorem mergeMarket_lemmaP {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) {E : ℕ → EF} (hE : PGenerableWeighting E)
    (hE01 : ∀ n, (E n).denote A = 0 ∨ (E n).denote A = 1) {c : ℝ}
    (hY : Tendsto (fun n => H (f.f n) φ) (atTop ⊓ 𝓟 {n | (E n).denote A = 1}) (𝓝 c)) :
    Tendsto (fun n => mergeMarket A Q n φ) (atTop ⊓ 𝓟 {n | (E n).denote A = 1}) (𝓝 c) := by
  have hY' : Tendsto (realized H f (fun _ => priceLuv φ))
      (atTop ⊓ 𝓟 {n | (E n).denote A = 1}) (𝓝 c) := by
    rw [realized_priceLuv]; exact hY
  exact lemmaP (H := H) (A := A) (pkg φ) hworldA hE hE01 hY'

/-- A sentence true in every completed-theory world of `DPH` determines its price LUV at `1`.
Source: none: infrastructure (`priceLuv_valued`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem priceLuv_determinedVia_one {DPH : DeductiveProcess} {φ : Sentence}
    (hφ : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.Holds φ) :
    LUV.DeterminedVia (priceLuv φ) DPH 1 := by
  intro v hv
  have h := priceLuv_valued φ v
  simpa [PCWorld.payout, hφ v hv] using h

/-- A sentence false in every completed-theory world of `DPH` determines its price LUV at `0`.
Source: none: infrastructure (`priceLuv_valued`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem priceLuv_determinedVia_zero {DPH : DeductiveProcess} {φ : Sentence}
    (hφ : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ¬ v.Holds φ) :
    LUV.DeterminedVia (priceLuv φ) DPH 0 := by
  intro v hv
  have h := priceLuv_valued φ v
  simpa [PCWorld.payout, hφ v hv] using h

/-- **The surviving neighbour of the (Gen) refutation (headline).** Under the package of record,
on every sentence true in every completed-theory world of `DPH` (every theorem of `H`'s process),
`𝔼^∗_n(φ) → 1` — `fa-theorem-a`'s `decided_quote_tendsto` at `X := priceLuv φ`, `v := 1`, the
determinacy from `priceLuv_valued`. This is exactly the property the feedback-free instances
of `GenRefuted.lean` violate (`mergeMarket_botQuotes`: the merge prices `⊤` at `ℙ^A_n(⊥) → 0`),
now proved under the package of record: the (Gen) refutation is about the *missing feedback*,
not about the merge construction.
Scope: one-way, mirror direction (corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to
Sam). The only modelling step is `pkg.reflected`; at the mirror witness it is (a) at variant
fidelity (ledger-recorded).
Source: trust-lab-008 ((Gen), the surviving neighbour); [[merging-inductors-model]] §(a.1); root-fa-2-006 (the decided case); mandate T4
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) `hworldH`, `hworldA`, `hφ`; (c) `pkg.reflected` -/
theorem mergeMarket_provind {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) (hφ : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.Holds φ) :
    Tendsto (fun n => mergeMarket A Q n φ) atTop (𝓝 1) :=
  decided_quote_tendsto (H := H) (A := A) (priceLuv φ) (priceLuv_codes φ) hworldH
    (priceLuv_determinedVia_one hφ) hworldA (pkg φ)

/-- **The surviving neighbour, dual:** on every sentence false in every completed-theory world of
`DPH`, `𝔼^∗_n(φ) → 0`.
Source: trust-lab-008; mandate T4 (the `∼φ` dual)
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) `hworldH`, `hworldA`, `hφ`; (c) `pkg.reflected` -/
theorem mergeMarket_provind_neg {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) (hφ : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ¬ v.Holds φ) :
    Tendsto (fun n => mergeMarket A Q n φ) atTop (𝓝 0) :=
  decided_quote_tendsto (H := H) (A := A) (priceLuv φ) (priceLuv_codes φ) hworldH
    (priceLuv_determinedVia_zero hφ) hworldA (pkg φ)

/-- **The decided case with a named value:** on a sentence whose price LUV `DPH` determines at
`v`, `𝔼^∗_n(φ) → v`.
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A` (corpus
construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The only modelling step is
`pkg.reflected`; at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: root-fa-2-006; mandate E1 (the `decided` pattern)
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) `hworldH`, `hworldA`, `hdec`; (c) `pkg.reflected` -/
theorem mergeMarket_decided {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) {v : ℝ} (hdec : LUV.DeterminedVia (priceLuv φ) DPH v) :
    Tendsto (fun n => mergeMarket A Q n φ) atTop (𝓝 v) :=
  decided_quote_tendsto (H := H) (A := A) (priceLuv φ) (priceLuv_codes φ) hworldH hdec hworldA (pkg φ)

/-- **The surviving neighbour along the even days** (S1's companion): Lemma P at
`E := evenDays` for a theorem of `DPH` — `𝔼^∗_n(φ) → 1` along the even days. Content grade: at a
decided sentence this is implied by the all-days limit `mergeMarket_provind`
(`fa-theorem-a` F16: a day-set that *selects* needs an undecided target); stated through
`mergeMarket_lemmaP` to record that the behavioural convergence on the good-feedback subsequence
survives the S1 refutation.
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A` (corpus
construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The only modelling step is
`pkg.reflected`; at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[merging-inductors-model]] §(a.1) (the good-feedback subsequence); mandate S1 (surviving neighbour)
Kind: L (one instantiation of an audited `fa-theorem-a` theorem at the price LUV plus a rewrite; relabelled from C in repair round 1)
Fidelity: exact
Hyps: (a) `hworldH`, `hworldA`, `hφ`; (c) `pkg.reflected` -/
theorem mergeMarket_provind_evenDays {H A : History} {DPH DPA : DeductiveProcess}
    [IsLogicalInductor H DPH] [IsLogicalInductor A DPA]
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (pkg : MergeQuotes H DPA f Q)
    (φ : Sentence) (hφ : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.Holds φ) :
    Tendsto (fun n => mergeMarket A Q n φ)
      (atTop ⊓ 𝓟 {n | (evenDays n).denote A = 1}) (𝓝 1) := by
  refine mergeMarket_lemmaP (H := H) (A := A) hworldA pkg φ evenDays_pgenerable (evenDays_01 A) ?_
  have h := decided_realized_tendsto (H := H) (priceLuv φ) (priceLuv_codes φ) hworldH
    (priceLuv_determinedVia_one hφ) f
  rw [realized_priceLuv] at h
  exact h.mono_left inf_le_left

end Cleanroom.Fa.FaEisenstatConj
