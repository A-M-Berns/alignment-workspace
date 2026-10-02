import Cleanroom.Deference.DefTrackingPin.Encoding
import Cleanroom.Deference.DefTrackingPin.Column

/-!
# `def-tracking-pin` · Relabel: the relabeling market and Claim 2 (T9)

anson-2-020 (chat 11 L639–675; chat 01 L1494–1512): the genesis criterion `LI(H,F)` — a `φ`-share
bought on day `n` pays `H_{F(n)}(φ)` — and its three claims.

* (i) **"The copy `A_n := H_{F(n)}` is in `LI(H,F)` for every trader class"** — trivial under the
  real-payout accounting: every trade is valued `(H_{F(n)}(φ) − A_n(φ)) = 0`
  (`realPayoutWorth_copy`, kind T, N−: the statement has no content beyond `x − x = 0`). The chat's
  own Claim 1 (L639–650) is about traders *without* oracle access to `H`; the sentence "the copy …
  is just a relabeling" is a remark inside Claim 2 (L652), and the "(i) the copy is unexploitable"
  statement is the inventory's synthesis and the mandate's T9 (i). Its **FAF reading** — `n ↦ H (F n)`
  is a logical inductor over `DP` whenever `H` is and `F` is strictly increasing and computable — is
  **not proved, and its direction is unknown**. What is established: the mandate's pull-back
  argument ("the exploiter pulls back to a trader against `H` on the days `im F`") is not a proof,
  because `Trader.Exploits` assesses a trader's day-`n` net worth against the worlds consistent
  with `D n` while `H_{F(n)}` is priced against `D (F n)`, and `PC(D (F n)) ⊆ PC(D n)` makes the
  pulled-back trader's assessment set *smaller* — the pull-back does not preserve exploitation.
  Round 1's conjectured refutation (fresh atoms `φ_n` adjoined at stage `F n`, and a trader selling
  `φ_n` on day `n` when `H_{F(n)}(φ_n) > 1 − 2^{-n}`) does **not** work as sketched: provability
  induction gives `H_{F(n)}(φ_n) → 1` with no rate, so the sell trigger need never fire; and at
  `F = id` the identical argument would "exploit" `H` itself, which is an inductor (audit r1
  fidelity B2). A refutation would need an inductor whose day-`m` prices on the members of `D m` are
  pinned at their decided values (so that `H ∘ F` prices stage-`F(n)` decisions exactly on day `n`,
  giving the trigger a rate), which the OPEN statement's `∃ P` permits and nothing here constructs.
  The statement is `relabel_not_inductor` (OPEN, findings F-G). Machine-checked that it is not
  true for a trivial reason: `ComputableMarket` re-indexes along computable `F`
  (`computableMarket_relabel`), `processComputable` is `DP`'s, so only `noExploit` can fail
  (`relabel_only_noExploit_can_fail`); and the empty process gives the positive direction, so a
  witness must be a genuine exploit. For `F = id` the claim is `H` itself. Over the *accelerated* process `n ↦ DP.D (F n)` the relabeled market is expected to be an
  inductor (the pull-back then works with the price variables re-indexed), not attempted.
* (ii) **Claim 2** (`A_n(φ) − H_{F(n)−1}(φ) → 0` for each fixed `φ`): at the deferred pair this is
  **grade (a)** for **any** reader over the deferred process — not a T1 instance needing `hz`, as
  the mandate expected, and not for one construction, as round 1 stated it: for a *fixed* sentence
  the column converges (T6), and `H_{F(n)−1}(φ) → H_∞(φ)` too (`claim2_fixed_sentence`; the LIA
  instance `claim2_fixed_sentence_lia`). The day-varying form (sentence `quoted j n` changing with
  `n`) is T1's `deferred_tracking`, with `hz` (c); cite, do not re-prove.
* (iii) "restricting traders to `H_{≤n}` trivializes the criterion the other way": recorded only
  (findings) — FAF has no second trader class.

Roles as in `Column.lean`: reader = any inductor over the deferred process (the corpus's `A`,
rendered as the reader's expectation of the ledger contract under FAF's criterion — the T8 (i)
encoding, F-J), fixed market = `liaHistory DPA` (the corpus's `H`). Scope: one-way.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- **T9 (i), real-payout reading: the copy is unexploitable** — when the market's price *is* the
real payout (`p = v`), every trade is valued `0` and the real-payout net worth vanishes
identically. Kind T, N−: `x − x = 0` standing in for an unmodeled argument ([[AUDIT]] §0.2); the
"for every trader class" of the source is the absence of any trader in the statement. Not a
headline. Single market.
Source: anson-2-020 (i) (chat 11 L639–675; the inventory's synthesis of L652)
Kind: T
Fidelity: exact (and empty: the claim has this much content)
Hyps: (a) none -/
theorem realPayoutWorth_copy (t v : ℕ → ℝ) (n : ℕ) : realPayoutWorth t v v n = 0 := by
  simp [realPayoutWorth]

/-- **`ComputableMarket` is preserved by computable relabeling**: `n ↦ P (F n)` is a computable
market whenever `P` is and `F` is computable (FAF's `ComputableMarket.ofComputableTable` with the
re-indexed quote table; the code's totality recovered by `Partrec.of_eq_tot`). Lifted from audit r2
adversarial N6's probe: the first half of "the OPEN `relabel_not_inductor` is not true for a
trivial reason". Single market.
Source: none: infrastructure (the market field of `IsLogicalInductor` under relabeling)
Kind: L
Fidelity: n/a -/
theorem computableMarket_relabel {P : History} (h : ComputableMarket P) {F : ℕ → ℕ}
    (hF : Computable F) : ComputableMarket (fun n φ => P (F n) φ) := by
  obtain ⟨hrange, quote, code, hexact, hcode⟩ := h
  have htab : Computable fun z : ℕ => Encodable.encode (quote z.unpair.1 z.unpair.2) :=
    Partrec.of_eq_tot (Partrec.nat_iff.mpr (Nat.Partrec.Code.exists_code.mpr ⟨code, rfl⟩)) hcode
  have hg : Computable fun z : ℕ => Nat.pair (F z.unpair.1) z.unpair.2 :=
    Primrec₂.natPair.to_comp.comp (hF.comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair)
  refine ComputableMarket.ofComputableTable (fun n k => quote (F n) k)
    (fun n φ => hrange (F n) φ) (fun n φ => hexact (F n) φ) ?_
  exact (htab.comp hg).of_eq fun z => by simp [Nat.unpair_pair]

/-- **Only `noExploit` can fail under relabeling**: the relabeled market is an inductor over `DP`
as soon as no e.c. trader exploits it — `marketComputable` by `computableMarket_relabel`,
`processComputable` is `DP`'s and does not see the market. So a witness of `relabel_not_inductor`
must be a genuine exploit (the second half of "not true for a trivial reason"; audit r2
adversarial N6). Single market.
Source: none: infrastructure (the fields of `IsLogicalInductor` under relabeling)
Kind: L
Fidelity: n/a -/
theorem relabel_only_noExploit_can_fail {P : History} {DP : DeductiveProcess} {F : ℕ → ℕ}
    [hLI : IsLogicalInductor P DP] (hF : Computable F)
    (hno : ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun n φ => P (F n) φ) DP) :
    IsLogicalInductor (fun n φ => P (F n) φ) DP :=
  ⟨computableMarket_relabel hLI.marketComputable hF, hLI.processComputable, hno⟩

/-- **OPEN (the FAF reading of T9 (i), stated as its negation; direction unknown).** Some inductor
`P` over some process `DP` with every stage satisfiable, and some strictly increasing computable
lookahead `F`, have the relabeled market `n ↦ P (F n)` **not** a logical inductor over `DP`. The
mandate's positive claim ("`n ↦ H (F n)` is an inductor over `DP`; the exploiter pulls back") is
not proved: `Trader.Exploits` assesses day-`n` net worth against the worlds consistent with `D n`,
not `D (F n)`, so the pull-back does not preserve exploitation. No refutation is sketched that
survives the absence of a rate in provability induction (round 1's sell-near-`1` trader, module
docstring, would equally "exploit" `H` at `F = id`); a refutation would need an inductor whose
day-`m` prices on `D m`'s members are pinned, which `∃ P` permits and nothing here builds. Not
true for a trivial reason — machine-checked: `ComputableMarket` is preserved by computable `F`
(`computableMarket_relabel`), `processComputable` is `DP`'s, so the only field that can fail is
`noExploit` (`relabel_only_noExploit_can_fail`). Single market.
Source: anson-2-020 (i), FAF reading (mandate T9 (i)); findings F-G (corrected at audit r1 fidelity B2)
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem relabel_not_inductor :
    ∃ (P : History) (DP : DeductiveProcess) (F : ℕ → ℕ),
      IsLogicalInductor P DP ∧ (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      StrictMono F ∧ Computable F ∧ ¬ IsLogicalInductor (fun n φ => P (F n) φ) DP := by
  sorry

/-- **T9 (ii). Claim 2 at a fixed sentence, grade (a), any reader:** in the deferred pair with
`quoted j n := φ j`, for **any** inductor `P` over the deferred process, the reader's day-`n`
expectation of `α_{j,n}` (the corpus's `A_n(φ_j)`, under the T8 (i) encoding) and the fixed
market's day-`(F(n) − 1)` price of `φ_j` (the corpus's `H_{F(n)−1}(φ)`) have vanishing difference —
**with no generability hypothesis** and no computability hypothesis on the reader: both tend to
`limitingBelief (liaHistory DPA) (φ j)` (T6 (ii) and FAF's `thm:con` along `F n − 1 → ∞`). The
source's "for every `A ∈ LI(H,F)`" is this quantifier (audit r1 adversarial N2). The source's proof
("the standard buy/sell trader exploits an `ε`-gap") is the T1 route and needs the trader to read
`H_{F(n)−1}(φ)`, i.e. `hz`; for a fixed sentence the column argument makes that unnecessary. The
day-varying form is `deferred_tracking` (T1 at the pair, `hz` (c)). `F n − 1` is `Nat`
subtraction: it is `0` only when `F n = 0`, i.e. at `n = 0` under `n ≤ F n`, and the limit along
`F n − 1 ≥ n − 1 → ∞` is unaffected. Reader: `P`; fixed market: `liaHistory DPA`; one-way.
Source: anson-2-020 (ii) (chat 11 L639–675, Claim 2); anson-2-022 Theorem 2
Kind: C
Fidelity: stronger: no class hypothesis at a fixed sentence (the source's `H_{F(n)−1}`-reading trader is not needed), any reader; variant: item-indexed columns; autonomous target; the reader's expectation of the ledger contract under FAF's criterion in place of `A`'s price of `φ` under `LI(H,F)` (T8 (i) encoding, transport not built)
Hyps: (a) none -/
theorem claim2_fixed_sentence (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F (fun j _ => φ j) e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    Tendsto (fun n => (ledgerLuv j n).expect P n - liaHistory DPA (F n - 1) (φ j)) atTop
      (𝓝 0) := by
  haveI := LIA_is_logical_inductor DPA hA
  have h1 := deferred_column_tendsto DPA DPH hA F hF φ e P hfree hworldH hworldA j
  have hF1 : Tendsto (fun n => F n - 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.sub_le_sub_right (hF n) 1) (tendsto_sub_atTop_nat 1)
  have h2 : Tendsto (fun n => liaHistory DPA (F n - 1) (φ j)) atTop
      (𝓝 (limitingBelief (liaHistory DPA) (φ j))) :=
    ((lic_limitingBelief_tendsto (liaHistory DPA) DPA hworldA (φ j)).comp hF1).congr
      fun n => rfl
  have := h1.sub h2
  rwa [sub_self] at this

/-- **T9 (ii) at FAF's LIA** — `claim2_fixed_sentence` with the reader `deferredReader …`, the
instance T5's witness inhabits. Reader: the deferred LIA; fixed market: `liaHistory DPA`; one-way.
Source: anson-2-020 (ii) (Claim 2)
Kind: L (instance of `claim2_fixed_sentence`)
Fidelity: as `claim2_fixed_sentence`, at one reader
Hyps: (a) none -/
theorem claim2_fixed_sentence_lia (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (hFc : Computable F) (φ : ℕ → Sentence) (hφ : Computable φ)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    Tendsto (fun n => (ledgerLuv j n).expect (deferredReader DPA DPH F (fun j _ => φ j) e) n -
      liaHistory DPA (F n - 1) (φ j)) atTop (𝓝 0) :=
  haveI := deferred_inductor DPA DPH hA hH F hFc (fun j _ => φ j) (hφ.comp Computable.fst) e he
  claim2_fixed_sentence DPA DPH hA F hF φ e _ hfree hworldH hworldA j

end Cleanroom.Deference.DefTrackingPin
