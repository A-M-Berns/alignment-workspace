import Cleanroom.Deference.DefTrackingPin.Pin
import Cleanroom.Found.LiQuoteLane.OneWay

/-!
# `def-tracking-pin` · Deferred: the deferred one-way pair (T5)

anson-2-022 Theorem 1 / lean-deference-020's honest T1 / v6 §5.1's blind retarget: a fixed market
`A := liaHistory DPA` (FAF's LIA over `DPA`), a computable lookahead `F`, and a reader
`H⁺ := liaHistory (DPH ⊕ ledger)` over the ledger that publishes the **deferred table**
`a j n := liaQuote DPA (F n) (quoted j n)` — the fixed market's **day-`F(n)`** price of the day-`n`
question — at stage `(e j).e n`. In the deference story the reader is the predictor `A` of the
corpus and the fixed market is `H`; `li-quote-lane`'s letters are the opposite (its `OneWayPair.H`
is the reader, `.A` the fixed market). Every docstring below names roles, not letters.

**Why this is not a `OneWayPair`** (the mandate asked for one; the structure refuses): `OneWayPair.a_eq`
pins the published table to the fixed market's **same-day** price, `(a j n : ℝ) = A n (quoted j n)`.
The deferred table is the day-`F(n)` price, so the only `A` that satisfies `a_eq` is the relabeled
market `n ↦ liaHistory DPA (F n)`, and `A_inductor` would then demand that the relabeled market be a
logical inductor over `DPA` — T9 (i)'s FAF reading (`Relabel.lean`), which is OPEN in both
directions (`relabel_not_inductor` is its negation; neither is proved). So the packaging is **not
satisfiable from what is proved**. Defining a second pair type is forbidden by the mandate. So the
deferred pair is shipped as named objects (`deferredTable`, `deferredProcess`, `deferredReader`)
and explicit theorems — the four facts the mandate lists plus the honest T1 — and the conflict is
recorded in the findings (F-H). A dependent that wants a bundle composes these names.

**The criterion substitution.** anson-2-022 Theorem 1 is existence of `A ∈ LI(H,F)` — the
*real-payout* criterion (a `φ`-share bought on day `n` pays `H_{F(n)}(φ)`) against `H`-aware
traders. `deferred_inductor` proves FAF's standard 0/1-payout criterion over the ledger-augmented
process; the bridge is T8 (`Encoding.lean`: the contract `C_n` as the precision-`n` mesh, and the
valuation-level transport bound), whose FAF-trader lift is not built (findings F-J). Every
headline about the reader in this file and in `Column.lean` is under that rendering.

**The publication-after-lookahead condition** `F n ≤ (e j).e n` ("the day-`n` item is published no
earlier than day `F n`, when the fixed market's day-`F(n)` price exists") is a modelling constraint
FAF cannot see: the ledger process is a fixed computable set sequence, so **no theorem in this file
or in `Column.lean` depends on it** — each holds for any schedule `e`, including one revealing
`H_{F(n)}(φ)` on day `n`. `deferredSchedule` publishes exactly at day `F n` and is what the
witnesses use; the deferred story's causality lives in that choice, not in the statements.

Scope: one-way. This is the package's only file importing `Construction.LIACompiler` (through
`li-quote-lane`'s `OneWay`).
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## The deferred table and process -/

/-- **The deferred table of record**: item `j`, day `n` ↦ the fixed market `liaHistory DPA`'s exact
rational **day-`F(n)`** price of the day-`n` quoted sentence, `liaQuote DPA (F n) (quoted j n)` —
the corpus's `H_{F(n)}(P^{(n)})` (its `H` is this file's fixed market). Fixed market: FAF's LIA
over `DPA`. One-way.
Source: anson-2-022 Theorem 1 (chat 01 L1513–1521); lean-deference-020; [[deference-in-logical-induction-v6]] §5.1
Kind: D
Fidelity: variant: autonomous target `H_{F(n)}(P^{(n)})` (the fixed market never reads the reader) in place of the sealed sibling `H^{[n]}_{F(n)}(P^{(n)})`, which is `li-coupled-pair`'s
Hyps: n/a -/
noncomputable def deferredTable (DPA : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (j n : ℕ) : ℚ :=
  liaQuote DPA (F n) (quoted j n)

/-- The deferred table is the fixed market's real day-`F(n)` price, definitionally.
Source: none: infrastructure (FAF `liaHistory_eq_quote_cast`)
Kind: L
Fidelity: n/a -/
theorem deferredTable_eq_liaHistory (DPA : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (j n : ℕ) :
    (deferredTable DPA F quoted j n : ℝ) = liaHistory DPA (F n) (quoted j n) :=
  (liaHistory_eq_quote_cast DPA (F n) (quoted j n)).symm

/-- The deferred table lies in `[0,1]` (FAF's `liaHistory_range`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem deferredTable_mem (DPA : DeductiveProcess) (F : ℕ → ℕ) (quoted : ℕ → ℕ → Sentence)
    (j n : ℕ) : 0 ≤ deferredTable DPA F quoted j n ∧ deferredTable DPA F quoted j n ≤ 1 :=
  liaQuote_mem DPA (F n) (quoted j n)

/-- **T5 (i): the deferred table is computable** — through the `MarketComputation` that FAF's
`LIA_is_logical_inductor` supplies for the fixed market (`quote_exact`, `code_spec`), along the
computable day indexer `F ∘ snd` and the sentence codes (`li-quote-lane`'s
`marketComputation_quote_computable` with an arbitrary computable day map). `Computable`, not
`Primrec`. One-way.
Source: anson-2-022 Theorem 1 ("there is a computable `A ∈ LI(H,F)`"); `li-quote-lane` `liaQuote_computable` generalized to a deferred day
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem deferredTable_computable (DPA : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (F : ℕ → ℕ) (hF : Computable F) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) :
    Computable fun p : ℕ × ℕ => deferredTable DPA F quoted p.1 p.2 := by
  obtain ⟨M⟩ := (LIA_is_logical_inductor DPA hA).marketComputable.nonemptyComputation
  have hM := marketComputation_quote_computable M (d := fun p : ℕ × ℕ => F p.2)
    (g := fun p : ℕ × ℕ => Encodable.encode (quoted p.1 p.2)) (hF.comp Computable.snd)
    (Computable.encode.comp hq)
  refine hM.of_eq fun p => ?_
  have h := M.quote_exact (F p.2) (quoted p.1 p.2)
  rw [liaHistory_eq_quote_cast] at h
  unfold deferredTable
  exact_mod_cast h.symm

/-- **The deferred ledger process**: the reader's base `DPH` plus the ledger of the deferred table
on the schedules `e` — `li-quote-lane`'s `ledgerProcess` at `deferredTable`. One-way.
Source: anson-2-022 Theorem 1; [[deference-in-logical-induction-v6]] §0.4 (the quote ledger)
Kind: D
Fidelity: variant: autonomous target (as `deferredTable`)
Hyps: n/a -/
noncomputable abbrev deferredProcess (DPA DPH : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (e : ℕ → PublicationSchedule) : DeductiveProcess :=
  ledgerProcess DPH (deferredTable DPA F quoted) e

/-- **The reader of the deferred pair**: FAF's LIA over the deferred ledger process (the
corpus's predictor `A`, reading the fixed market's deferred credences). One-way.
Source: anson-2-022 Theorem 1
Kind: D
Fidelity: variant: autonomous target; plain trader class
Hyps: n/a -/
noncomputable abbrev deferredReader (DPA DPH : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (e : ℕ → PublicationSchedule) : History :=
  liaHistory (deferredProcess DPA DPH F quoted e)

/-- **The publication schedule that posts day `n`'s item exactly at day `F n`** (the mandate's
`F n ≤ (e j).e n`, with equality), for a lookahead with `n ≤ F n`.
Source: anson-2-022 Theorem 1 (payout vector `H_{F(n)}`); [[deference-in-logical-induction-v6]] §0.4
Kind: D
Fidelity: exact
Hyps: n/a -/
def deferredSchedule (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) : PublicationSchedule := ⟨F, hF⟩

/-- `(deferredSchedule F hF).e n = F n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem deferredSchedule_e (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (n : ℕ) :
    (deferredSchedule F hF).e n = F n := rfl

/-! ## T5: existence, determinacy, computability -/

/-- **T5 (ii): the deferred ledger process is a `ComputableDeductiveProcess`** (`li-quote-lane`'s
`ledgerProcess_computable` at the computable deferred table). One-way.
Source: anson-2-022 Theorem 1; lean-deference-020 (honest restatement)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem deferredProcess_computable (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : Computable F) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    ComputableDeductiveProcess (deferredProcess DPA DPH F quoted e) :=
  ledgerProcess_computable hH (deferredTable_computable DPA hA F hF quoted hq) he

/-- **T5 (iii) (headline). The deferred one-way pair exists:** FAF's LIA over the deferred ledger
process is a logical inductor over it (`LIA_is_logical_inductor`). The reader prices a language in
which the fixed market's day-`F(n)` credences of the day-`n` questions are decided threshold
literals. **No `hworld` here**: FAF's `LIA_is_logical_inductor` needs only computability, so over a
`DPH` already holding opposite ledger literals this is FAF's degenerate branch; `deferredProcess_hworld`
is what excludes it, and every headline about the reader's prices carries it. The statement holds
for any schedule `e`: the publication-after-lookahead condition `F n ≤ (e j).e n` is not in it
(module docstring). Reader: this LIA; fixed market: `liaHistory DPA`; one-way.
Source: anson-2-022 Theorem 1 (chat 01 L1513–1521: "for every `H`, `F` there is a computable `A ∈ LI(H,F)`"); lean-deference-020 / root-deference-038 (honest T1's existence half); [[deference-in-logical-induction-v6]] §5.1
Kind: L (one application of FAF's `LIA_is_logical_inductor`; the work is `deferredTable_computable`, C)
Fidelity: variant: FAF's 0/1-payout criterion over the ledger process in place of `LI(H,F)`'s real-payout criterion (encoding T8 (i), transport partial, F-J); autonomous target `H_{F(n)}(P^{(n)})` (the fixed market never reads the reader) in place of the sealed sibling; one-way; plain trader class (`EfficientlyComputable`) in place of `H`-aware traders
Hyps: (a) none -/
theorem deferred_inductor (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : Computable F) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    IsLogicalInductor (deferredReader DPA DPH F quoted e) (deferredProcess DPA DPH F quoted e) :=
  LIA_is_logical_inductor _ (deferredProcess_computable DPA DPH hA hH F hF quoted hq e he)

/-- **`hworld` for the deferred process**: every stage is satisfiable when the reader's base is
free of the ledger family and satisfiable (`li-quote-lane` T1.5). One-way.
Source: `li-quote-lane` T1.5 (`ledgerProcess_hworld`); anson-012
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem deferredProcess_hworld {DPA DPH : DeductiveProcess} {F : ℕ → ℕ}
    {quoted : ℕ → ℕ → Sentence} {e : ℕ → PublicationSchedule}
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F quoted) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((deferredProcess DPA DPH F quoted e).D n) :=
  ledgerProcess_hworld hfree hworldH

/-- **T5 (iv): every ledger LUV of the deferred process is settled at the deferred credence** —
`LUV.DeterminedVia (ledgerLuv j n) (deferredProcess …) (deferredTable … j n)`, i.e. at the fixed
market's day-`F(n)` price of `quoted j n` (`li-quote-lane` T1.2 with `hmem` from
`liaQuote_mem`). This is the FAF fact the pinning lemma consumes; no settlement stage appears.
One-way.
Source: anson-2-022 Theorem 1; [[deference-in-logical-induction-v6]] §0.4 lines 100–104
Kind: L (one application of `li-quote-lane`'s `ledgerLuv_determinedVia` with `liaQuote_mem`)
Fidelity: exact, with `li-quote-lane`'s disclosures (α) code-bounded thresholds, (β) strict polarity
Hyps: (a) none -/
theorem deferred_determined (DPA DPH : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (e : ℕ → PublicationSchedule) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (deferredProcess DPA DPH F quoted e)
      (deferredTable DPA F quoted j n) :=
  ledgerLuv_determinedVia DPH _ e (fun j n => deferredTable_mem DPA F quoted j n) j n

/-! ## The honest T1 at the deferred pair -/

/-- **The honest T1 (lean-deference-020, root-deference-038) for any reader over the deferred
process:** if `P` is an inductor over `deferredProcess DPA DPH F quoted e` and the deferred table
is `P`-generable (`hz`), then `𝔼^P_n(α_{j,n}) ≈ₙ liaQuote DPA (F n) (quoted j n)`. `pinning_exact`
at `deferred_determined`. The sources quantify over every market in the class ("for every
`A ∈ LI(H,F)`"), which this form renders; the LIA instance is `deferred_tracking` (audit r2
adversarial N7). `hz` is the one (c), as in `deferred_tracking`. Reader: `P` (the corpus's `A`,
under the T8 (i) encoding); fixed market: `liaHistory DPA`; one-way.
Source: lean-deference-020 (`faithful_tracking`, re-founded); root-deference-038 ([[deference-in-logical-induction-v6]] §5.4 T1); anson-2-022 Theorem 2
Kind: L (instance of `pinning_exact`, Kind C)
Fidelity: variant: FAF's criterion over the ledger process in place of `LI(H,F)`'s real-payout criterion (T8 (i) encoding, transport partial, F-J); autonomous target; one-way; plain trader class; `hz` for the corpus's `𝒞_A`-computability of `Y_n`
Hyps: (c) `hz` — generability of the deferred table at the reader; all else (a) -/
theorem deferred_tracking_any (DPA DPH : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F quoted e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F quoted) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (j : ℕ)
    (hz : PGenerableRat P (fun n => deferredTable DPA F quoted j n)) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ
      (fun n => (deferredTable DPA F quoted j n : ℝ)) :=
  pinning_exact (ledgerLuv_thresholdCodes j) (deferredProcess_hworld hfree hworldH)
    (fun n => deferredTable DPA F quoted j n)
    (fun n => deferred_determined DPA DPH F quoted e j n) hz

/-- **The honest T1 (lean-deference-020, root-deference-038): at the deferred pair, if the
contract settles to the fixed market's deferred credence and the reader is an inductor over the
process that decides it, then `a_n − Y_n → 0`** — here: the reader's day-`n` expectation of the
day-`n` ledger LUV tracks the deferred table, `𝔼^{reader}_n(α_{j,n}) ≈ₙ liaQuote DPA (F n)
(quoted j n)`, **given `hz`**: the deferred table is `P`-generable at the reader (`PGenerableRat`).
`deferred_tracking_any` at FAF's LIA (`deferred_inductor`). **`hz` is undischarged at a genuine
lookahead**: no FAF fact is known that would discharge it for a day-varying LIA table, and none is
expected — the table costs a LIA run of the fixed market to day `F(n)` (`F(n) = 2^n` in the
corpus), and nothing in FAF gives a `GeneratedRatFeature` of the reader's own prices that computes
it (`li-quote-lane` findings F2 says the same); "not dischargeable" is a belief, not a theorem.
This is 2b / (A4) — the formalization's honest end point (findings F-A, F-B), not a gap to paper
over. **Witness of the full package: N−** — `deferred_tracking_constLookahead` (`Witnesses.lean`):
the statement asks only `Computable F`, not `n ≤ F n`, so a constant lookahead `F ≡ c` with a
day-constant quoted sentence makes the table the constant `liaQuote DPA c ψ`, which
`MachineRatCodes.const` generates at any market; `hz` is idle there (`_hzFree` proves the same
through T3), and `hz` at a genuine lookahead — the intended instance — is unexhibited (audit r2
adversarial N1). The statement holds for any schedule `e` (the publication-after-lookahead
condition is not in it; module docstring). The `hz`-free facts about the same pair are T2
(`deferred_snapshot`, eventual per LUV), T3/T6 (`Column.lean`, convergent columns, any reader) and
T4's (a) instance. Reader: the deferred LIA (the corpus's `A`, under the T8 (i) encoding); fixed
market: `liaHistory DPA` (the corpus's `H`); one-way.
Source: lean-deference-020 (`FrozenDeliberation.faithful_tracking`, the [[AUDIT]] §3.3 squeeze, re-founded); root-deference-038 ([[deference-in-logical-induction-v6]] §5.4 T1); anson-2-022 Theorem 2
Kind: L (instance of `deferred_tracking_any`, itself an instance of `pinning_exact`, Kind C)
Fidelity: variant: FAF's criterion over the ledger process in place of `LI(H,F)`'s real-payout criterion (T8 (i) encoding, transport partial, F-J); autonomous target in place of the sealed sibling; one-way; plain trader class; `hz` for the corpus's `𝒞_A`-computability of `Y_n`
Hyps: (c) `hz` — generability of the deferred table at the reader, standing in for the corpus's (A4) power; all else (a) -/
theorem deferred_tracking (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : Computable F) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F quoted) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (j : ℕ)
    (hz : PGenerableRat (deferredReader DPA DPH F quoted e)
      (fun n => deferredTable DPA F quoted j n)) :
    (fun n => (ledgerLuv j n).expect (deferredReader DPA DPH F quoted e) n) ≈ₙ
      (fun n => (deferredTable DPA F quoted j n : ℝ)) :=
  haveI := deferred_inductor DPA DPH hA hH F hF quoted hq e he
  deferred_tracking_any DPA DPH F quoted e _ hfree hworldH j hz

/-- **The snapshot identity for any reader over the deferred process** (anson-043): if `P` is an
inductor over `deferredProcess DPA DPH F quoted e`, its limiting expectation of the day-`n` ledger
LUV is the fixed market's day-`F(n)` price of `quoted j n`, exactly. `pinning_fixed` at
`deferred_determined`, rewritten by `deferredTable_eq_liaHistory`; the LIA instance is
`deferred_snapshot` (audit r2 adversarial N7). With `DPH = DPA` this holds for any inductor over
`DPA ⊕ ledger` — [[deference-in-logical-induction-v6]]'s `H⁺`; chat 05 L11043's `H` conditioned on
the quote stream is a different object, covered only if it is such an inductor. Reader: `P`; fixed
market: `liaHistory DPA`; one-way.
Source: anson-043 (chat 03 L4437–4455, the identity); anson-042 ("eventual" grade)
Kind: L (instance of `pinning_fixed`, Kind C)
Fidelity: stronger: exact, no rounding — at the LUV (`expectInf`) in place of the precision-`n` contract; any reader; autonomous target
Hyps: (a) none -/
theorem deferred_snapshot_any (DPA DPH : DeductiveProcess) (F : ℕ → ℕ)
    (quoted : ℕ → ℕ → Sentence) (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F quoted e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F quoted) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (j n : ℕ) :
    Tendsto (fun m => (ledgerLuv j n).expect P m) atTop
      (𝓝 (liaHistory DPA (F n) (quoted j n))) :=
  (deferredTable_eq_liaHistory DPA F quoted j n) ▸
    pinning_fixed (P := P) (ledgerLuv_thresholdCodes_single j n)
      (deferredProcess_hworld hfree hworldH)
      (deferred_determined DPA DPH F quoted e j n)

/-- **The snapshot identity at the deferred pair** (anson-043, "`H⁺_∞(C_n) = H_{F(n)}(P^{(n)})
± 1/2n`"): the reader's limiting expectation (FAF's `LUV.expectInf`) of the day-`n` ledger LUV is
the fixed market's day-`F(n)` price of `quoted j n`, **exactly** — no `1/2n` rounding. T2
(`pinning_fixed_expectInf`) at `deferred_determined`, through `deferred_snapshot_any` at FAF's LIA;
grade (a), no `hz`: the LUV is fixed, so the target is a constant. Stated at the LUV (the
full-precision limit), not at the corpus's precision-`n` contract `C_n` (T8 (i): `contract X n`):
the contract-level form, `lim_m` of the precision-`k` contract's price within `1/k` of the value,
is a corollary of `contract_value_near` and a constant-family affine coherence FAF does not package
(no constant `PolySequence`), and is not shipped. With `DPH = DPA` the reader is an inductor over
`DPA ⊕ ledger` — [[deference-in-logical-induction-v6]]'s `H⁺` ((A1), L567) — and this is its
identity; chat 05 L11043's `H⁺_t = H_t(· | Q_A^{(t)})` is a different object (audit r2 fidelity
N3). Reader: the deferred LIA; fixed market: `liaHistory DPA`; one-way.
Source: anson-043 (chat 03 L4437–4455, the identity); anson-042 ("eventual" grade)
Kind: L (instance of `deferred_snapshot_any`, itself an instance of `pinning_fixed`, Kind C)
Fidelity: stronger: exact, no rounding — at the LUV (`expectInf`) in place of the precision-`n` contract; the contract-level form within `1/n` is a corollary of T8 (i), not shipped; autonomous target
Hyps: (a) none -/
theorem deferred_snapshot (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : Computable F) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F quoted) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (j n : ℕ) :
    Tendsto (fun m => (ledgerLuv j n).expect (deferredReader DPA DPH F quoted e) m) atTop
      (𝓝 (liaHistory DPA (F n) (quoted j n))) :=
  haveI := deferred_inductor DPA DPH hA hH F hF quoted hq e he
  deferred_snapshot_any DPA DPH F quoted e _ hfree hworldH j n

end Cleanroom.Deference.DefTrackingPin
