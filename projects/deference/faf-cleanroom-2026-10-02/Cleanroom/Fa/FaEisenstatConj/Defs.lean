import Cleanroom.Found.LiQuoteLane.Defs
import Cleanroom.Found.LiAsympCalc.Defs
import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.Machine.ThresholdMachine

/-!
# `fa-eisenstat-conj` · Defs: the lookahead expectation as a market (T1)

The definitions module of the package `Cleanroom.Fa.FaEisenstatConj`
([[fa-eisenstat-conj-mandate]]). Everything is stated over FAF's objects (`LUV`, `History`,
`DeferralFunction`, `PCWorld.ValuesAt`, `LUV.MachineThresholdCodes`) and `li-quote-lane`'s
`CrossQuotePackage` / `ledgerLuv`.

* `priceLuv φ` is the LUV whose expectation **is** the price: `(priceLuv φ).expect P m = P m φ`
  for every market and every day (`priceLuv_expect`). It is the "degenerate reading" FAF's
  `LUV.indicatorOf` deliberately avoids (to keep `thm:ei` non-trivial); here it is exactly right,
  because the object of the conjecture is `𝔼^A_n(⌜ℙ^H_{f(n)}(φ)⌝)` — the quote of a *price* —
  and `fa-theorem-a`'s theorems are stated for `X.expect H (f n)`, which at `X := priceLuv φ`
  reads `H (f n) φ` verbatim.
* `mergeMarket A Q` is **`𝔼^∗_n(·)`**, the lookahead expectation as a market: `A`'s day-`n`
  expectation of the quote LUV `Q φ n` meant to name `ℙ^H_{f n}(φ)`. A `History`, so FAF's
  criterion `IsLogicalInductor (mergeMarket A Q) DP` is statable of it (lean-deference-075).
* `MergeQuotes H DPA f Q` is the good-feedback package of record: for **every** sentence `φ`,
  `Q φ` is an e.c. LUV family of `A`'s language and `A`'s completed theory determines `Q φ n` at
  `H`'s realized day-`f n` price of `φ` (`li-quote-lane`'s `CrossQuotePackage` at
  `X := fun _ => priceLuv φ`). All-sentences on purpose: a market must price every sentence.
* `decodeSentence`, `samQuote` — the sentence decoder and the pull-back of a price ledger along a
  deferral function, used by `SamStructure.lean` (T5).

**Scope.** Everything here is the lookahead construction in the **corpus construal (Abram's
version)** — one-way, mirror direction: `A` reads `H` through a ledger, `H` never reads `A`
([[eisenstat-conjecture-attribution]] §2, §5). It is not Sam Eisenstat's intended information
structure (that is `SamPair`, `SamStructure.lean`); claims about Sam's intent are
ATTRIBUTION-UNVETTED. Notation: `B_t` (AGENDA, trust lab, `trust-merge`'s `MergeExpert`) =
`𝔼^∗_n` (attribution page §1) = `mergeMarket` here.

This file imports no `Cleanroom.Fa.FaTheoremA.*` module and no `Construction.*` module, so a
later package can state over these definitions cheaply.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. The price LUV -/

/-- **The price LUV** of a sentence: thresholds `⊤` below `0`, `φ` itself on `[0,1)`, `⊥` at and
above `1`. Its expectation under any market on any day is exactly that market's price of `φ`
(`priceLuv_expect`), so `⌜ℙ^H_{f n}(φ)⌝` is the quote of `(priceLuv φ).expect H (f n)`. This is
the "degenerate reading" FAF's `LUV.indicatorOf` deliberately avoids (`Expectations.lean`, "Taking
the threshold to be `φ` itself would be the degenerate reading"); here the object *is* a price.
Scope: one-way (a LUV of the language, no market in it).
Source: [[eisenstat-conjecture-attribution]] §1 (the object `𝔼^∗_n(·) := 𝔼^A_n(⌜ℙ^H_{f(n)}(·)⌝)`, a quote of a *price*); mandate T1, Known issue 4
Kind: D
Fidelity: exact
Hyps: n/a -/
def priceLuv (φ : Sentence) : LUV :=
  ⟨fun r => if r < 0 then (⊤ : Sentence) else if r < 1 then φ else (⊥ : Sentence)⟩

/-- `priceLuv_gt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma priceLuv_gt (φ : Sentence) (r : ℚ) :
    (priceLuv φ).gt r = if r < 0 then (⊤ : Sentence) else if r < 1 then φ else (⊥ : Sentence) :=
  rfl

/-- On the unit interval `[0,1)` the threshold sentence of `priceLuv φ` is `φ` itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLuv_gt_of_mem (φ : Sentence) {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) :
    (priceLuv φ).gt r = φ := by
  simp [priceLuv, not_lt.mpr h0, h1]

/-- **T1. The expectation of the price LUV is the price:** `(priceLuv φ).expect P m = P m φ` for
every market `P` and day `m`. Every grid point `i/(m+1)`, `i < m+1`, lies in `[0,1)`, so FAF's
`expectApprox` averages `m+1` copies of `P m φ`. Needs nothing about `P`.
Source: mandate T1 (`priceLuv_expect`); FAF `Expectations.lean` ("`𝔼ₙ` would then average `n+1` copies of `Pₙ(φₙ)`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem priceLuv_expect (φ : Sentence) (P : History) (m : ℕ) :
    (priceLuv φ).expect P m = P m φ := by
  unfold LUV.expect LUV.expectApprox
  have hgrid : ∀ i ∈ Finset.range (m + 1),
      P m ((priceLuv φ).gt ((i : ℚ) / ((m + 1 : ℕ) : ℚ))) = P m φ := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [priceLuv_gt_of_mem φ (by positivity) ?_]
    rw [div_lt_one (by positivity)]
    exact_mod_cast hi
  rw [Finset.sum_congr rfl hgrid, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ (by positivity) _

/-- Every p.c. world values the price LUV of `φ` at its payout of `φ` (FAF's `PCWorld.ValuesAt`):
thresholds below the payout affirmed, above it denied. In particular every completed-theory
world of every process values it — the `hval` input of `fa-theorem-a`'s Theorem A, discharged
for every sentence with no hypothesis (Known issue 9).
Source: mandate T1 (`priceLuv_valued`); FAF `LUV.indicatorOf_isIndicator` (the same case split)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem priceLuv_valued (φ : Sentence) (v : PCWorld) :
    v.ValuesAt (priceLuv φ) (v.payout φ) := by
  have hpay := payout_mem_Icc v φ
  refine ⟨hpay.1, hpay.2, fun r => ?_⟩
  have hnotbot : ¬ v.Holds (⊥ : Sentence) := fun h => h
  constructor
  · intro hr
    by_cases h0 : r < 0
    · simpa [priceLuv, h0] using PCWorld.holds_top v
    · have hr1 : r < 1 := by
        have : (r : ℝ) < 1 := lt_of_lt_of_le hr hpay.2
        exact_mod_cast this
      rw [priceLuv_gt_of_mem φ (not_lt.mp h0) hr1]
      by_contra hφ
      have h0' : (0 : ℝ) ≤ r := by exact_mod_cast not_lt.mp h0
      unfold PCWorld.payout at hr
      rw [if_neg hφ] at hr
      linarith
  · intro hr
    by_cases h1 : 1 ≤ r
    · have h0 : ¬ r < 0 := not_lt.mpr (le_trans zero_le_one h1)
      simpa [priceLuv, h0, not_lt.mpr h1] using hnotbot
    · by_cases h0 : r < 0
      · exfalso
        have h0' : (r : ℝ) < 0 := by exact_mod_cast h0
        linarith [hpay.1]
      · rw [priceLuv_gt_of_mem φ (not_lt.mp h0) (not_le.mp h1)]
        intro hφ
        have h1' : (r : ℝ) < 1 := by exact_mod_cast not_le.mp h1
        unfold PCWorld.payout at hr
        rw [if_pos hφ] at hr
        linarith

/-- **The price LUV is e.c.** (FAF's `LUV.MachineThresholdCodes`): one machine-metered program
writes `⌜priceLuv φ > i/k⌝` from the unary paired index `⟨k, i⟩`. At a grid index the rational
`i/k ≥ 0`, so the `r < 0` branch is unreachable and the family is a two-way dispatch — `φ` when
`i/k < 1`, `⊥` otherwise — on the ruler `((i + 1) - k) * k`, which vanishes exactly when `k = 0`
(where `i/k = 0`) or `i < k`. This is FAF's `indicatorOf_machineThresholdCodeSeq` with the
constant sentence `φ` in the middle branch.
Source: mandate T1 (`priceLuv_codes`); FAF `LUV.indicatorOf_machineThresholdCodeSeq` (the same ruler)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem priceLuv_codes (φ : Sentence) : (priceLuv φ).MachineThresholdCodes := by
  have hk : UnaryRuler (fun m : ℕ => m.unpair.1) := UnaryRuler.unpairFst
  have hi : UnaryRuler (fun m : ℕ => m.unpair.2) := UnaryRuler.unpairSnd
  have ht : UnaryRuler (fun m : ℕ => (m.unpair.2 + 1 - m.unpair.1) * m.unpair.1) :=
    (hi.succ.sub hk).mul hk
  show MachineSentenceCodes (fun m => (priceLuv φ).gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ)))
  refine MachineSentenceCodes.of_eq
    (MachineSentenceCodes.ifZero (MachineSentenceCodes.const φ)
      (MachineSentenceCodes.const (⊥ : Sentence)) ht) (fun m => ?_)
  have hnn : ¬ ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ) < 0) :=
    not_lt.mpr (div_nonneg (by positivity) (by positivity))
  have hkey : ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ) < 1) ↔
      (m.unpair.2 + 1 - m.unpair.1) * m.unpair.1 = 0 := by
    rcases Nat.eq_zero_or_pos m.unpair.1 with hk0 | hk0
    · simp [hk0]
    · rw [div_lt_one (by exact_mod_cast hk0)]
      constructor
      · intro h
        have hlt : m.unpair.2 < m.unpair.1 := by exact_mod_cast h
        simp [Nat.sub_eq_zero_of_le hlt]
      · intro h
        have hz : m.unpair.2 + 1 - m.unpair.1 = 0 := by
          rcases Nat.mul_eq_zero.mp h with h' | h'
          · exact h'
          · omega
        have hlt : m.unpair.2 < m.unpair.1 := by omega
        exact_mod_cast hlt
  by_cases hlt : (m.unpair.2 : ℚ) / (m.unpair.1 : ℚ) < 1
  · rw [if_pos (hkey.mp hlt)]
    simp [priceLuv, hnn, hlt]
  · rw [if_neg (fun h => hlt (hkey.mpr h))]
    simp [priceLuv, hnn, hlt]

/-- A single LUV's e.c. certificate, as the constant family's (`MachineThresholdCodeSeq` of
`fun _ => X` from `MachineThresholdCodes X`, by precomposition with the second unpairing).
Restated from `fa-theorem-a`'s `Decided.lean` so that this file imports none of it.
Source: none: infrastructure (FAF `MachineSentenceCodes.comp`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma thresholdCodeSeq_const {X : LUV} (h : X.MachineThresholdCodes) :
    LUV.MachineThresholdCodeSeq (fun _ => X) :=
  (MachineSentenceCodes.comp h UnaryRuler.unpairSnd).of_eq (fun _ => rfl)

/-- The constant price-LUV family is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma priceLuv_codeSeq (φ : Sentence) : LUV.MachineThresholdCodeSeq (fun _ => priceLuv φ) :=
  thresholdCodeSeq_const (priceLuv_codes φ)

/-! ## B. The merge market `𝔼^∗` -/

/-- **The lookahead expectation as a market, `𝔼^∗_n(φ) := 𝔼^A_n(Q φ n)`** — `A`'s day-`n`
expectation of the quote LUV `Q φ n` meant to name `ℙ^H_{f n}(φ)` — the sentence-indexed form
FAF's criterion needs (a `History`). The deferral `f` and the human market `H` are not in the
definition: they enter through the package `MergeQuotes`, which says what the quotes name.
`trust-merge`'s `MergeExpert.est` is the LUV-source form of the same estimate
(recorded in prose as `mergeMarket_eq_mergeExpert_est`, report T1 and findings F4; no `Bridge.lean` exists).
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`. This is
the lookahead construction in the **corpus construal (Abram's version)**, not Sam Eisenstat's
intended information structure ([[eisenstat-conjecture-attribution]] §2, §5); claims about Sam's
intent are ATTRIBUTION-UNVETTED.
Source: [[eisenstat-conjecture-attribution]] §1 (`𝔼^∗_n(·) := 𝔼^A_n(⌜ℙ^H_{f(n)}(·)⌝)`; root-deference-018); [[li-deference]] lines 106–108 (`E^*_n(V) := E^A_n E^H_{F(n)}(V)`); [[merging-inductors-model]] §0 (`B_t(φ) := 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`; trust-lab-008)
Kind: D
Fidelity: exact (over FAF's grid expectation `LUV.expect`, precision `n + 1`)
Hyps: n/a -/
noncomputable def mergeMarket (A : History) (Q : Sentence → ℕ → LUV) : History :=
  fun n φ => (Q φ n).expect A n

/-- `mergeMarket_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mergeMarket_apply (A : History) (Q : Sentence → ℕ → LUV) (n : ℕ) (φ : Sentence) :
    mergeMarket A Q n φ = (Q φ n).expect A n := rfl

/-- The merge market prices in `[0,1]` whenever `A` does (FAF's `LUV.expect_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem mergeMarket_mem_Icc {A : History} (hA : ∀ n s, 0 ≤ A n s ∧ A n s ≤ 1)
    (Q : Sentence → ℕ → LUV) (n : ℕ) (φ : Sentence) :
    0 ≤ mergeMarket A Q n φ ∧ mergeMarket A Q n φ ≤ 1 :=
  LUV.expect_mem_Icc A n (Q φ n) (hA n)

/-! ## C. The good-feedback package of record -/

/-- **The good-feedback package of record** (Kind D): for every sentence `φ`, `Q φ` is an e.c. LUV
family of `A`'s language and `A`'s completed theory `DPA` determines `Q φ n` at `H`'s realized
day-`f n` price of `φ` — `li-quote-lane`'s `CrossQuotePackage H DPA f (fun _ => priceLuv φ) (Q φ)`,
whose `reflected` clause reads `LUV.DeterminedVia (Q φ n) DPA ((priceLuv φ).expect H (f n))`,
i.e. `… (H (f n) φ)` by `priceLuv_expect`. **All sentences, on purpose**: a market must price every
sentence, and a `Q` with a default on "unquoted" sentences makes the inductor half trivially
false (`GenRefuted.lean` is exactly that mechanism; Known issue 8). **Carries no timing**: as
Theorem A and Lemma P needed none, the package says only what the quotes name, not when `A`'s
process decides them. **Carries no world** (as `CrossQuotePackage`): every headline over it carries
`hworldA : ∀ n, ∃ v, v.ConsistentWith (DPA.D n)` itself (`isLogicalInductor_of_stage_unsatisfiable`).
Its `reflected` clause is the package's one (c) — Σ₁-completeness of `Γ_A` about `H`'s machine,
`li-coupled-pair`'s row — discharged (a) at the mirror witness at `variant` fidelity
(ledger-recorded determinacy, `Witnesses.lean`).
Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`
(corpus construal, Abram's version; attribution page §2, §5; ATTRIBUTION-UNVETTED as to Sam).
Source: [[eisenstat-conjecture-attribution]] §1 (AGENDA's "if the AI has good feedback about the human beliefs"); [[merging-inductors-model]] §0 (the standing setup); mandate T1 (`MergeQuotes`)
Kind: D
Fidelity: variant: `CrossQuotePackage` at the price LUV of every sentence (determinacy only; no timing clause, no "`f` fast enough" — those have no FAF object, Known issue 3)
Hyps: (c) `reflected` (per sentence), as above -/
def MergeQuotes (H : History) (DPA : DeductiveProcess) (f : DeferralFunction)
    (Q : Sentence → ℕ → LUV) : Prop :=
  ∀ φ : Sentence, CrossQuotePackage H DPA f (fun _ => priceLuv φ) (Q φ)

/-- The projection: the package of record at one sentence is a `CrossQuotePackage` at the price
LUV, so every `fa-theorem-a` theorem applies at `X := priceLuv φ`, `hcode := priceLuv_codes φ`,
`hval := fun v _ => ⟨_, priceLuv_valued φ v⟩`.
Source: mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem MergeQuotes.crossQuotePackage {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (h : MergeQuotes H DPA f Q)
    (φ : Sentence) : CrossQuotePackage H DPA f (fun _ => priceLuv φ) (Q φ) :=
  h φ

/-- Every quote family of the package is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem MergeQuotes.quote_codes {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (h : MergeQuotes H DPA f Q)
    (φ : Sentence) : LUV.MachineThresholdCodeSeq (Q φ) :=
  (h φ).quote_codes

/-- The package's determinacy clause in price form: `A`'s completed theory values `Q φ n` at
`H`'s realized day-`f n` price `H (f n) φ`.
Source: none: infrastructure (`priceLuv_expect`)
Kind: L
Fidelity: exact
Hyps: (c) `h.reflected` -/
theorem MergeQuotes.reflected_price {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {Q : Sentence → ℕ → LUV} (h : MergeQuotes H DPA f Q)
    (φ : Sentence) (n : ℕ) : LUV.DeterminedVia (Q φ n) DPA (H (f.f n) φ) := by
  have := (h φ).reflected n
  rwa [priceLuv_expect] at this

/-- The converse packaging: a determinacy clause in price form plus an e.c. certificate for every
sentence is the package of record.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem MergeQuotes.of_price {H : History} {DPA : DeductiveProcess} {f : DeferralFunction}
    {Q : Sentence → ℕ → LUV} (hcodes : ∀ φ, LUV.MachineThresholdCodeSeq (Q φ))
    (hdet : ∀ φ n, LUV.DeterminedVia (Q φ n) DPA (H (f.f n) φ)) : MergeQuotes H DPA f Q :=
  fun φ => ⟨hcodes φ, fun n => by rw [priceLuv_expect]; exact hdet φ n⟩

/-! ## D. Sentence codes and the pull-back of a price ledger (for `SamStructure.lean`) -/

/-- The sentence named by a code (`⊤` on a non-code): the junk convention under which a price
ledger indexed by sentence codes is a table on all of `ℕ`.
Source: none: infrastructure (mandate T5, `decodeSentence`)
Kind: D
Fidelity: n/a -/
def decodeSentence (j : ℕ) : Sentence := (Encodable.decode (α := Sentence) j).getD ⊤

/-- `decodeSentence_encode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma decodeSentence_encode (φ : Sentence) : decodeSentence (Encodable.encode φ) = φ := by
  simp [decodeSentence]

/-- **The pull-back of a price ledger along the deferral**: the quote LUV `samQuote f φ n` is the
ledger item of sentence `φ` (item index `⌜φ⌝`) on day `f n` — `A`'s name, on day `n`, for
`H`'s day-`f n` price of `φ`, when `A`'s process carries the full price ledger of `H` published
at `PublicationSchedule.succ`. The deferral is *inside the index*: no `realizedExpectation`
table is needed, the ledger already records every price of every day. Two-way (Sam's structure).
Source: [[eisenstat-conjecture-attribution]] §2 (Sam's bullet 1: "the AI knows the human's beliefs immediately"); mandate T5 (`samQuote`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def samQuote (f : DeferralFunction) (φ : Sentence) (n : ℕ) : LUV :=
  ledgerLuv (Encodable.encode φ) (f.f n)

/-- `samQuote_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma samQuote_apply (f : DeferralFunction) (φ : Sentence) (n : ℕ) :
    samQuote f φ n = ledgerLuv (Encodable.encode φ) (f.f n) := rfl

end Cleanroom.Fa.FaEisenstatConj
