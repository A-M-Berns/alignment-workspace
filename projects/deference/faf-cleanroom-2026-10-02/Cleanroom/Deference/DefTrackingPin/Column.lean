import Cleanroom.Deference.DefTrackingPin.Deferred
import Cleanroom.Deference.DefTrackingPin.Atoms
import LogicalInduction.Properties.AffinePersistence

/-!
# `def-tracking-pin` · Column: the apparatus reaches `H_∞` column-wise (T6)

anson-043's corollary, lean-deference-075's limit-agreement half, anson-030 at the deferred pair,
anson-2-022 Theorem 3: with `quoted j n := φ j` for a `φ : ℕ → Sentence` — item `j` **is** sentence
`φ_j`, published every day; the ledger's item index does what the corpus's repetition enumeration
`P^{(⟨i,k⟩)} := φ_i` does, without a subsequence — and a lookahead `F` with `n ≤ F n`:

* (i) `deferredTable_tendsto_limitingBelief`: the deferred table's column `n ↦ a_{j,n} =
  A_{F(n)}(φ_j)` tends to `limitingBelief A (φ_j)` (FAF's `P∞`, `lic_limitingBelief_tendsto`,
  along `F n → ∞`);
* (ii) `deferred_column_tracking` / `deferred_column_tendsto`: **any** reader `P` that is an inductor
  over the deferred process has its day-`n` expectation of `α_{j,n}` track the column and tend to
  the same limit — T3 at (i), grade (a), **no `hz`**, and no computability hypothesis (the
  *criterion* forces the tracking, as the sources' "for every `A ∈ LI(H,F)`" says; audit r1
  adversarial N2). The LIA forms `_lia` are the instances T5's witness inhabits;
* (iii) `limitingBelief_eq_one_of_decided` / `_zero_of_refuted` and `deferred_column_decided`: on a
  sentence decided by the fixed market's process the column limit is its truth value — the corpus's
  "on decidable `φ_i` the column limit is `𝟙[Γ ⊢ φ_i]`";
* `trivialPredictor_error_tendsto_zero` / `thm3_unconditional`: anson-2-022 Theorem 3's conclusion
  holds with **no predictor hypothesis** — it is (ii). The source states it under "for every `φ`
  some asymptotically calibrated e.c. predictor of `H_{F(n)}(φ)` converges to `H_∞(φ)`", where
  "asymptotically calibrated" is the source's §6.1 *cumulative* condition (chat 11 L2994–2996: the
  signed error sum against every e.c. comparator stays bounded). That condition is neither assumed
  nor discharged here: what Theorem 2's proof actually uses is the *pointwise* vanishing of the
  per-trade error, which the trivial predictor `Ĥ_n(φ) := H_n(φ)` has for every inductor
  (`thm:con`), so the hypothesis is **bypassed**, not proved true (audit r2 fidelity B1; findings
  F-D, rewritten at repair round 2).

F-C: anson-030's "`A_∞(φ)`" is not a price on `φ`; the diagonal limit is defined here as
`lim_n 𝔼^{reader}_n(α_{j,n})` for item `j = φ`, and the per-sentence statement holds there at grade
(a). F-E: lean-deference-075's "the quote sequence is itself an inductor" is not stated (ill-posed
until the quotes are a market over a language); its limit-agreement half is (ii). The corpus's
`A_n(φ)` is a price of `φ` under the real-payout criterion `LI(H,F)`; here it is the reader's
expectation of the ledger contract under FAF's criterion over the ledger process — the encoding of
T8 (i), whose trader-level transport is not built (F-J). Every "(the corpus's `A_n(φ_j)`)" below is
under that rendering.

**T6 stretch (proved at repair round 2).** The literal diagonal reading along a subsequence of
days, `quoted 0 n := φ (n.unpair.1)`, is `deferred_diagonal_subsequence`: two padded families
(`columnPad` — FAF's `𝟙(∼⊤)`, settled at `0`, off the column for `≲ₙ`; `𝟙(⊤)`, settled at `1`,
for `≳ₙ`) through the one-sided T3 forms `pinning_asympLE` / `pinning_asympGE` (`Pin.lean`), then
the restriction to the column `k ↦ ⟨i,k⟩`. The e.c. certificate of the if-split family
(`columnPad_thresholdCodes`) needed no new machine infrastructure: `MachineThresholdCodeSeq` is a
`MachineSentenceCodes` on the paired index, so `MachineSentenceCodes.ifZero` on the column test
does it.

Roles: the reader is `P` (any inductor over the deferred process; the corpus's `A`), in the
`_lia` forms `deferredReader …`; the fixed market is `liaHistory DPA` (the corpus's `H`), whose
`hworldA` every statement about *its* prices carries (`OneWayPair.ofLIA_A_hworld`'s lesson). With
`DPH = DPA` the reader is any inductor over `DPA ⊕ ledger` — [[deference-in-logical-induction-v6]]'s
`H⁺` ((A1), L567); chat 05 L11043's `H⁺_t = H_t(· | Q_A^{(t)})`, `H` conditioned on the quote
stream, is a different object, covered only if it is an inductor over the augmented process.
Scope: one-way.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- A lookahead with `n ≤ F n` tends to infinity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tendsto_lookahead {F : ℕ → ℕ} (hF : ∀ n, n ≤ F n) : Tendsto F atTop atTop :=
  tendsto_atTop_mono hF tendsto_id

/-- **T6 (i) (headline). The deferred column converges to the fixed market's limiting belief:**
for `quoted j n := φ j` and a lookahead with `n ≤ F n`, item `j`'s deferred table
`n ↦ liaQuote DPA (F n) (φ j)` tends to `limitingBelief (liaHistory DPA) (φ j)` — FAF's
`lic_limitingBelief_tendsto` (`thm:con`, every price converges to its `P∞` coordinate) composed with
`F n → ∞`. `hworldA` is for the fixed market's process (not supplied by its being an inductor).
Fixed market: `liaHistory DPA`; one-way.
Source: anson-043 corollary (chat 03 L4437–4455: "`lim_j a_⟨i,j⟩ = H_∞(φ_i)`"); anson-030; FAF `thm:con`
Kind: L (one application of FAF's `thm:con` along `F → ∞`)
Fidelity: variant: item-indexed columns instead of the pairing enumeration
Hyps: (a) none -/
theorem deferredTable_tendsto_limitingBelief (DPA : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    Tendsto (fun n => (deferredTable DPA F (fun j _ => φ j) j n : ℝ)) atTop
      (𝓝 (limitingBelief (liaHistory DPA) (φ j))) := by
  haveI := LIA_is_logical_inductor DPA hA
  have h := lic_limitingBelief_tendsto (liaHistory DPA) DPA hworldA (φ j)
  exact (h.comp (tendsto_lookahead hF)).congr fun n => rfl

/-- **T6 (ii) (headline). Any reader tracks the column:** for **any** inductor `P` over the
deferred process with `quoted j n := φ j`, the reader's day-`n` expectation of `α_{j,n}` tracks the
deferred table, `𝔼^P_n(α_{j,n}) ≈ₙ liaQuote DPA (F n) (φ j)`, with **no generability hypothesis**
and **no computability hypothesis on the reader** — T3 (`pinning_ofTendsto`) at the convergent
column (i). The sources' quantifier is "for every `A ∈ LI(H,F)`": the criterion forces the
tracking, not one construction; FAF's LIA is the instance `deferred_column_tracking_lia`. This is
lean-deference-075's limit-agreement half and anson-030's per-sentence limit agreement at the pair,
grade (a). Reader: `P` (the corpus's `A`, rendered as the reader's expectation of the ledger
contract under FAF's criterion — the T8 (i) encoding, F-J); fixed market: `liaHistory DPA`;
one-way.
Source: anson-043 corollary; anson-030 ([[trust-between-inductors-summary-v2]] §2.1); lean-deference-075 (limit-agreement half); anson-2-022 Theorem 2 (convergent case) and Theorem 3 (unconditional)
Kind: C
Fidelity: variant: item-indexed columns; autonomous target; the reader's expectation of the ledger contract under FAF's criterion in place of `A`'s price of `φ` under `LI(H,F)` (T8 (i) encoding, transport not built)
Hyps: (a) none -/
theorem deferred_column_tracking (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F (fun j _ => φ j) e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ
      (fun n => (deferredTable DPA F (fun j _ => φ j) j n : ℝ)) :=
  pinning_ofTendsto (P := P) (ledgerLuv_thresholdCodes j) (deferredProcess_hworld hfree hworldH)
    (fun n => deferred_determined DPA DPH F (fun j _ => φ j) e j n)
    (deferredTable_tendsto_limitingBelief DPA hA F hF φ hworldA j)

/-- **T6 (ii), limit form: any reader's column tends to `H_∞`:**
`𝔼^P_n(α_{j,n}) → limitingBelief (liaHistory DPA) (φ j)` for any inductor `P` over the deferred
process. This is the definition of record of the corpus's "`A_∞(φ)`" (F-C): the diagonal limit of
the reader's day-`n` prices of the day-`n` contracts on `φ`, which equals the fixed market's
limiting belief. It is also the conclusion of anson-2-022 Theorem 3, with no predictor hypothesis
(`thm3_unconditional`). Reader: `P` (the corpus's `A`, under the T8 (i) encoding); fixed market:
`liaHistory DPA`; one-way.
Source: anson-030 (the "idle" positive, with its flag resolved); anson-043 corollary; anson-2-022 Theorem 3 (chat 01 L1550), unconditional
Kind: C
Fidelity: variant: item-indexed columns; the diagonal limit made explicit; the reader's expectation of the ledger contract in place of `A`'s price under `LI(H,F)` (T8 (i) encoding). Stronger than anson-2-022 Theorem 3: no predictor hypothesis
Hyps: (a) none -/
theorem deferred_column_tendsto (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F (fun j _ => φ j) e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    Tendsto (fun n => (ledgerLuv j n).expect P n) atTop
      (𝓝 (limitingBelief (liaHistory DPA) (φ j))) :=
  pinning_tendsto (P := P) (ledgerLuv_thresholdCodes j) (deferredProcess_hworld hfree hworldH)
    (fun n => deferred_determined DPA DPH F (fun j _ => φ j) e j n)
    (deferredTable_tendsto_limitingBelief DPA hA F hF φ hworldA j)

/-- **T6 (ii) at FAF's LIA** — `deferred_column_tracking` with the reader `deferredReader …`, the
instance T5's witness inhabits (the computability hypotheses are what `deferred_inductor` needs).
Reader: the deferred LIA; fixed market: `liaHistory DPA`; one-way.
Source: anson-043 corollary; anson-030
Kind: L (instance of `deferred_column_tracking`)
Fidelity: as `deferred_column_tracking`, at one reader
Hyps: (a) none -/
theorem deferred_column_tracking_lia (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (hFc : Computable F) (φ : ℕ → Sentence) (hφ : Computable φ)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    (fun n => (ledgerLuv j n).expect (deferredReader DPA DPH F (fun j _ => φ j) e) n) ≈ₙ
      (fun n => (deferredTable DPA F (fun j _ => φ j) j n : ℝ)) :=
  haveI := deferred_inductor DPA DPH hA hH F hFc (fun j _ => φ j) (hφ.comp Computable.fst) e he
  deferred_column_tracking DPA DPH hA F hF φ e _ hfree hworldH hworldA j

/-- **T6 (ii), limit form, at FAF's LIA** — `deferred_column_tendsto` with the reader
`deferredReader …`. Reader: the deferred LIA; fixed market: `liaHistory DPA`; one-way.
Source: anson-030; anson-043 corollary
Kind: L (instance of `deferred_column_tendsto`)
Fidelity: as `deferred_column_tendsto`, at one reader
Hyps: (a) none -/
theorem deferred_column_tendsto_lia (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (hFc : Computable F) (φ : ℕ → Sentence) (hφ : Computable φ)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    Tendsto (fun n => (ledgerLuv j n).expect (deferredReader DPA DPH F (fun j _ => φ j) e) n)
      atTop (𝓝 (limitingBelief (liaHistory DPA) (φ j))) :=
  haveI := deferred_inductor DPA DPH hA hH F hFc (fun j _ => φ j) (hφ.comp Computable.fst) e he
  deferred_column_tendsto DPA DPH hA F hF φ e _ hfree hworldH hworldA j

/-! ## anson-2-022 Theorem 3 is unconditional -/

/-- **The trivial predictor's per-day error vanishes, and it converges to `H_∞(φ)`** — for every
inductor `H` over a process with satisfiable stages and every lookahead `F → ∞`, the predictor
`Ĥ_n(φ) := H_n(φ)` (a lookup of the fixed market's own day-`n` price) has
`H_n(φ) − H_{F(n)}(φ) → 0` and `H_n(φ) → limitingBelief H φ`, both from FAF's `thm:con`. This is
**weaker than** the source's "asymptotically calibrated" (anson-2-022 §6.1, chat 11 L2994–2996:
`Σ_n (H_{F(n)}(φ) − Ĥ_n(φ)) · sign(Ĥ_n(φ) − p_n)` bounded for every e.c. comparator `p_n` — a
*cumulative* condition, which pointwise vanishing does not give; FAF's `thm:con` carries no rate,
and the harmonic error `1/(n+1)` vanishes with unbounded partial sums), and it is **the property
Theorem 2's proof actually uses**: the per-trade value `A_n − H_{F(n)} = (A_n − Ĥ_n) + (Ĥ_n −
H_{F(n)})` exceeds `ε/2` on all but finitely many trading days as soon as the error vanishes
pointwise. So anson-2-022 Theorem 3's predictor hypothesis is *bypassed* by `thm3_unconditional`,
not shown "always true"; whether the trivial predictor meets the cumulative condition at the
corpus's `F(n) = 2^n` is not established (it holds by telescoping at `F n = n + 1`). The source's
L1558 remark that the condition is "a non-trivial assumption about `H`'s convergence rate" is right
about the *stated* condition; its error is to present the conclusion as depending on it (findings
F-D, rewritten at repair round 2 after audit r2 fidelity B1). Fixed market `H`; one-way.
Source: anson-2-022 Theorem 2's proof sketch (chat 01 L1541–1544) and Theorem 3 (chat 01 L1550, L1558; the definition at chat 11 L2994–2996); [[trust-between-inductors-summary-v2]] §2.1; FAF `thm:con`
Kind: L (two applications of FAF's `thm:con`)
Fidelity: weaker: pointwise vanishing of the error (the form Theorem 2's proof uses) in place of the source's cumulative "asymptotically calibrated"; "e.c. from `H_{≤n}`" is a lookup, not stated
Hyps: (a) none -/
theorem trivialPredictor_error_tendsto_zero (H : History) (DP : DeductiveProcess)
    [IsLogicalInductor H DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (F : ℕ → ℕ)
    (hF : Tendsto F atTop atTop) (φ : Sentence) :
    Tendsto (fun n => H n φ - H (F n) φ) atTop (𝓝 0) ∧
      Tendsto (fun n => H n φ) atTop (𝓝 (limitingBelief H φ)) := by
  have h := lic_limitingBelief_tendsto H DP hworld φ
  refine ⟨?_, h⟩
  have h2 : Tendsto (fun n => H (F n) φ) atTop (𝓝 (limitingBelief H φ)) :=
    (h.comp hF).congr fun n => rfl
  have := h.sub h2
  rwa [sub_self] at this

/-- **anson-2-022 Theorem 3, unconditional per sentence:** at the deferred pair with `quoted j n :=
φ j`, (a) the pointwise-vanishing weakening of the theorem's predictor hypothesis holds at the
trivial predictor `n ↦ liaHistory DPA n (φ j)` (error against `H_{F(n)}(φ_j)` vanishing,
converging to `H_∞(φ_j)` — `trivialPredictor_error_tendsto_zero`; the source's cumulative
"asymptotically calibrated" is neither assumed nor discharged), and (b) its conclusion
`A_∞(φ_j) = H_∞(φ_j)` holds for **any** inductor over the deferred process — the diagonal limit of
the reader's expectations of the day-`n` contracts is `limitingBelief (liaHistory DPA) (φ j)`
(`deferred_column_tendsto`, whose proof uses no predictor at all). The Lean is stronger than the
source: no predictor hypothesis (bypassed, not proved true), any reader. Part (c) of the source's
statement ("`A_∞` is coherent") is FAF's limit-coherence fact, not re-proved here. Reader: `P` (the
corpus's `A`, under the T8 (i) encoding); fixed market: `liaHistory DPA`; one-way.
Source: anson-2-022 Theorem 3 (chat 01 L1550; chat 11 L3010–3019); findings F-D (rewritten at repair round 2 after audit r2 fidelity B1)
Kind: L (the pairing of two instances: `trivialPredictor_error_tendsto_zero` and `deferred_column_tendsto`)
Fidelity: stronger: the predictor hypothesis bypassed — its pointwise-vanishing weakening (the form Theorem 2's proof uses) is proved at the trivial predictor, the source's cumulative "asymptotically calibrated" (chat 11 §6.1) is neither assumed nor discharged, and the conclusion holds for any reader; variant: item-indexed columns; the reader's expectation of the ledger contract in place of `A`'s price under `LI(H,F)` (T8 (i) encoding)
Hyps: (a) none -/
theorem thm3_unconditional (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F (fun j _ => φ j) e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    (Tendsto (fun n => liaHistory DPA n (φ j) - liaHistory DPA (F n) (φ j)) atTop (𝓝 0) ∧
      Tendsto (fun n => liaHistory DPA n (φ j)) atTop
        (𝓝 (limitingBelief (liaHistory DPA) (φ j)))) ∧
    Tendsto (fun n => (ledgerLuv j n).expect P n) atTop
      (𝓝 (limitingBelief (liaHistory DPA) (φ j))) := by
  haveI := LIA_is_logical_inductor DPA hA
  exact ⟨trivialPredictor_error_tendsto_zero (liaHistory DPA) DPA hworldA F (tendsto_lookahead hF)
      (φ j),
    deferred_column_tendsto DPA DPH hA F hF φ e P hfree hworldH hworldA j⟩

/-! ## Decided sentences: the column limit is the truth value -/

/-- **A sentence lying in some stage of the process has limiting belief `1`** at any inductor over
it (FAF's `lic_provind_true` at the constant family, with `thm:con`'s limit identified by
uniqueness). Fixed-market-side fact; one-way.
Source: anson-043 ("on decidable `φ_i` the column limit is `𝟙[Γ ⊢ φ_i]`"); FAF `thm:provind`, `thm:con`
Kind: C
Fidelity: exact (stage membership is the sufficient condition FAF names for "theorem")
Hyps: (a) none -/
theorem limitingBelief_eq_one_of_decided (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : ∃ k, φ ∈ DP.D k) : limitingBelief P φ = 1 := by
  have h1 := lic_provind_true P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => hv.holds_of_mem_stage hφ) hworld
  have h2 := lic_limitingBelief_tendsto P DP hworld φ
  exact tendsto_nhds_unique h2 (convergesTo_iff_asympEq_const.2 h1)

/-- **A sentence whose negation lies in some stage has limiting belief `0`**. Dual of
`limitingBelief_eq_one_of_decided`. One-way.
Source: anson-043; FAF `thm:provind`, `thm:con`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_eq_zero_of_refuted (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : ∃ k, ∼φ ∈ DP.D k) : limitingBelief P φ = 0 := by
  have h1 := lic_provind_false P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => hv.holds_of_mem_stage hφ) hworld
  have h2 := lic_limitingBelief_tendsto P DP hworld φ
  exact tendsto_nhds_unique h2 (convergesTo_iff_asympEq_const.2 h1)

/-- **T6 (iii). On a sentence decided by the fixed market's process, any reader's column tends to
its truth value** — `1` if `φ j` lies in some stage of `DPA`, `0` if `∼φ j` does. The corpus's
"on decidable `φ_i` the column limit is `𝟙[Γ ⊢ φ_i]`". Reader: any inductor `P` over the deferred
process (the LIA instance is `deferred_column_decided_lia`); fixed market: `liaHistory DPA`;
one-way.
Source: anson-043 corollary (chat 03 L4437–4455)
Kind: C
Fidelity: variant: item-indexed columns; "decidable" rendered as stage membership; any reader (the sources' class quantifier)
Hyps: (a) none -/
theorem deferred_column_decided (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F (fun j _ => φ j) e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    ((∃ k, φ j ∈ DPA.D k) →
      Tendsto (fun n => (ledgerLuv j n).expect P n) atTop (𝓝 1)) ∧
    ((∃ k, ∼φ j ∈ DPA.D k) →
      Tendsto (fun n => (ledgerLuv j n).expect P n) atTop (𝓝 0)) := by
  haveI := LIA_is_logical_inductor DPA hA
  have h := deferred_column_tendsto DPA DPH hA F hF φ e P hfree hworldH hworldA j
  constructor
  · intro hdec
    rwa [limitingBelief_eq_one_of_decided (liaHistory DPA) DPA hworldA hdec] at h
  · intro hdec
    rwa [limitingBelief_eq_zero_of_refuted (liaHistory DPA) DPA hworldA hdec] at h

/-- **T6 (iii) at FAF's LIA** — `deferred_column_decided` with the reader `deferredReader …`.
Reader: the deferred LIA; fixed market: `liaHistory DPA`; one-way.
Source: anson-043 corollary
Kind: L (instance of `deferred_column_decided`)
Fidelity: as `deferred_column_decided`, at one reader
Hyps: (a) none -/
theorem deferred_column_decided_lia (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (hFc : Computable F) (φ : ℕ → Sentence) (hφ : Computable φ)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun j _ => φ j)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (j : ℕ) :
    ((∃ k, φ j ∈ DPA.D k) →
      Tendsto (fun n => (ledgerLuv j n).expect (deferredReader DPA DPH F (fun j _ => φ j) e) n)
        atTop (𝓝 1)) ∧
    ((∃ k, ∼φ j ∈ DPA.D k) →
      Tendsto (fun n => (ledgerLuv j n).expect (deferredReader DPA DPH F (fun j _ => φ j) e) n)
        atTop (𝓝 0)) :=
  haveI := deferred_inductor DPA DPH hA hH F hFc (fun j _ => φ j) (hφ.comp Computable.fst) e he
  deferred_column_decided DPA DPH hA F hF φ e _ hfree hworldH hworldA j

/-! ## T6 stretch: the diagonal reading along a subsequence of days -/

/-- A completed-theory world that holds `ψ` values FAF's indicator LUV `𝟙(ψ)` at `1` — FAF's
`indicatorOf_isIndicator` read as a `ValuesAt`.
Source: none: infrastructure (FAF `LUV.indicatorOf_isIndicator`)
Kind: L
Fidelity: n/a -/
theorem indicatorOf_valuesAt_one {DP : DeductiveProcess} {w : PCWorld}
    (hw : w.ConsistentWithTheory DP) {ψ : Sentence} (hψ : w.Holds ψ) :
    w.ValuesAt (LUV.indicatorOf ψ) 1 := by
  refine ⟨zero_le_one, le_rfl, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · obtain ⟨h0, h01, _⟩ := LUV.indicatorOf_isIndicator ψ DP w hw r
    by_cases hr0 : (r : ℝ) < 0
    · exact h0 hr0
    · exact (h01 (not_lt.1 hr0) hr).2 hψ
  · exact (LUV.indicatorOf_isIndicator ψ DP w hw r).2.2 hr.le

/-- A completed-theory world that does not hold `ψ` values `𝟙(ψ)` at `0`.
Source: none: infrastructure (FAF `LUV.indicatorOf_isIndicator`)
Kind: L
Fidelity: n/a -/
theorem indicatorOf_valuesAt_zero {DP : DeductiveProcess} {w : PCWorld}
    (hw : w.ConsistentWithTheory DP) {ψ : Sentence} (hψ : ¬ w.Holds ψ) :
    w.ValuesAt (LUV.indicatorOf ψ) 0 := by
  refine ⟨le_rfl, zero_le_one, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · exact (LUV.indicatorOf_isIndicator ψ DP w hw r).1 hr
  · obtain ⟨_, h01, h1⟩ := LUV.indicatorOf_isIndicator ψ DP w hw r
    by_cases hr1 : (r : ℝ) < 1
    · exact fun h => hψ ((h01 hr.le hr1).1 h)
    · exact h1 (not_lt.1 hr1)

/-- **The padded family of the diagonal reading**: the single item's ledger LUV `α_{0,n}` on the
column `n.unpair.1 = i`, FAF's indicator LUV `𝟙(ψ)` off it (`ψ := ⊤`, settled at `1`, pads for
the lower bound; `ψ := ∼⊤`, settled at `0`, for the upper bound).
Source: mandate T6 stretch (the route the open list named at repair round 1)
Kind: D
Fidelity: n/a -/
def columnPad (i : ℕ) (ψ : Sentence) (n : ℕ) : LUV :=
  if n.unpair.1 = i then ledgerLuv 0 n else LUV.indicatorOf ψ

/-- **The padded family is e.c.** — the if-split threshold-code certificate the open list named as
the cost. FAF's `MachineThresholdCodeSeq` *is* a `MachineSentenceCodes` on the paired index
`⟨n, ⟨k, i'⟩⟩`, so `MachineSentenceCodes.ifZero` on the ruler `m ↦ (unpair₁(unpair₁ m) − i) +
(i − unpair₁(unpair₁ m))` (zero exactly on the column) dispatches between
`ledgerLuv_thresholdCodes 0` and FAF's `indicatorOf_machineThresholdCodeSeq` at the constant
sentence; no new machine infrastructure is needed.
Source: none: infrastructure (closes the open list's "not built" for `deferred_diagonal_subsequence`)
Kind: L
Fidelity: n/a -/
theorem columnPad_thresholdCodes (i : ℕ) (ψ : Sentence) :
    LUV.MachineThresholdCodeSeq (columnPad i ψ) := by
  have hfst : UnaryRuler (fun m : ℕ => m.unpair.1.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairFst
  have ht : UnaryRuler (fun m : ℕ => (m.unpair.1.unpair.1 - i) + (i - m.unpair.1.unpair.1)) :=
    (hfst.sub (UnaryRuler.const i)).add ((UnaryRuler.const i).sub hfst)
  have hA : MachineSentenceCodes (fun m : ℕ => (ledgerLuv 0 m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    ledgerLuv_thresholdCodes 0
  have hB : MachineSentenceCodes (fun m : ℕ => (LUV.indicatorOf ψ).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const ψ)
  show MachineSentenceCodes (fun m => (columnPad i ψ m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
  refine (MachineSentenceCodes.ifZero hA hB ht).of_eq (fun m => ?_)
  by_cases h : m.unpair.1.unpair.1 = i
  · simp [columnPad, h]
  · have h0 : (m.unpair.1.unpair.1 - i) + (i - m.unpair.1.unpair.1) ≠ 0 := by omega
    rw [if_neg h0]
    simp [columnPad, h]

/-- **The padded family is settled**: on the column at the deferred table (`deferred_determined`),
off it at the pad's value `y` (a world fact about `𝟙(ψ)` supplied by the caller).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem columnPad_determined (DPA DPH : DeductiveProcess) (F : ℕ → ℕ) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (i : ℕ) (ψ : Sentence) (y : ℝ)
    (hψ : ∀ w : PCWorld,
      w.ConsistentWithTheory (deferredProcess DPA DPH F (fun _ n => φ n.unpair.1) e) →
      w.ValuesAt (LUV.indicatorOf ψ) y) (n : ℕ) :
    LUV.DeterminedVia (columnPad i ψ n) (deferredProcess DPA DPH F (fun _ n => φ n.unpair.1) e)
      (if n.unpair.1 = i then (deferredTable DPA F (fun _ n => φ n.unpair.1) 0 n : ℝ) else y) := by
  intro w hw
  by_cases h : n.unpair.1 = i
  · simp only [columnPad, if_pos h]
    exact deferred_determined DPA DPH F _ e 0 n w hw
  · simp only [columnPad, if_neg h]
    exact hψ w hw

/-- **T6 stretch (proved at repair round 2; OPEN until then). The literal diagonal reading:** with a
single item whose quoted sentence cycles through `φ` along the pairing, `quoted 0 n :=
φ (n.unpair.1)`, any inductor `P` over the deferred process has, for every `i`, the reader's
expectation of the day-`⟨i,k⟩` contract at day `⟨i,k⟩` tend (in `k`) to
`limitingBelief (liaHistory DPA) (φ i)` — the corpus's `lim_k A_{⟨i,k⟩}(C_{⟨i,k⟩}) = H_∞(φ_i)`
with its repetition enumeration, rather than the item-indexed column of `deferred_column_tendsto`.
Route, as the open list sketched: pad the family `n ↦ α_{0,n}` off the column with `𝟙(∼⊤)`
(settled at `0`) for `≲ₙ L` and with `𝟙(⊤)` (settled at `1`) for `≳ₙ L`
(`columnPad`, e.c. by `columnPad_thresholdCodes`, settled by `columnPad_determined`); the padded
targets have no limit but are eventually within `ε` of `L` on the column (`thm:con` along `F`) and
trivially on the right side of `L` off it (`0 ≤ L ≤ 1`), so the one-sided T3 forms
`pinning_asympLE` / `pinning_asympGE` give the two bounds for all `n`; on the column the padded
LUV *is* `α_{0,n}`, and restricting along `k ↦ ⟨i,k⟩` (which tends to `∞`) gives the limit. No
generability anywhere (the (a) grade of T3). Reader `P`; fixed market `liaHistory DPA`; one-way.
Source: anson-043 corollary (chat 03 L4437–4455, the pairing enumeration); mandate T6 stretch
Kind: C
Fidelity: exact (the source's enumeration); the reader's expectation of the ledger contract in place of `A`'s price under `LI(H,F)` (T8 (i) encoding)
Hyps: (a) none -/
theorem deferred_diagonal_subsequence (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (F : ℕ → ℕ) (hF : ∀ n, n ≤ F n) (φ : ℕ → Sentence)
    (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (deferredProcess DPA DPH F (fun _ n => φ n.unpair.1) e)]
    (hfree : ProcessFreeOf (ledgerSchedule (deferredTable DPA F (fun _ n => φ n.unpair.1)) e) DPH)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (i : ℕ) :
    Tendsto (fun k => (ledgerLuv 0 (Nat.pair i k)).expect P (Nat.pair i k)) atTop
      (𝓝 (limitingBelief (liaHistory DPA) (φ i))) := by
  haveI := LIA_is_logical_inductor DPA hA
  have hworld := deferredProcess_hworld hfree hworldH
  set L := limitingBelief (liaHistory DPA) (φ i) with hLdef
  have hcol : Tendsto (fun n => liaHistory DPA (F n) (φ i)) atTop (𝓝 L) :=
    ((lic_limitingBelief_tendsto (liaHistory DPA) DPA hworldA (φ i)).comp
      (tendsto_lookahead hF)).congr fun n => rfl
  have hmem : ∀ n, 0 ≤ liaHistory DPA (F n) (φ i) ∧ liaHistory DPA (F n) (φ i) ≤ 1 := fun n => by
    rw [liaHistory_eq_quote_cast]
    exact_mod_cast liaQuote_mem DPA (F n) (φ i)
  have hL0 : 0 ≤ L := ge_of_tendsto' hcol fun n => (hmem n).1
  have hL1 : L ≤ 1 := le_of_tendsto' hcol fun n => (hmem n).2
  have hpair : Tendsto (fun k : ℕ => Nat.pair i k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.right_le_pair i k) tendsto_id
  have htab : ∀ n, n.unpair.1 = i →
      (deferredTable DPA F (fun _ n => φ n.unpair.1) 0 n : ℝ) = liaHistory DPA (F n) (φ i) := by
    intro n hn
    rw [deferredTable_eq_liaHistory]
    simp only [hn]
  have hLE : (fun n => (columnPad i (∼(⊤ : Sentence)) n).expect P n) ≲ₙ fun _ => L := by
    refine pinning_asympLE (P := P) (columnPad_thresholdCodes i _) hworld
      (columnPad_determined DPA DPH F φ e i _ 0 fun w hw =>
        indicatorOf_valuesAt_zero hw fun h => ((PCWorld.holds_neg w _).1 h) (PCWorld.holds_top w))
      ?_
    intro ε hε
    filter_upwards [hcol.eventually (eventually_le_nhds (lt_add_of_pos_right L hε))] with n hn
    by_cases h : n.unpair.1 = i
    · rw [if_pos h, htab n h]; exact hn
    · rw [if_neg h]; linarith
  have hGE : (fun n => (columnPad i (⊤ : Sentence) n).expect P n) ≳ₙ fun _ => L := by
    refine pinning_asympGE (P := P) (columnPad_thresholdCodes i _) hworld
      (columnPad_determined DPA DPH F φ e i _ 1 fun w hw =>
        indicatorOf_valuesAt_one hw (PCWorld.holds_top w))
      ?_
    intro ε hε
    filter_upwards [hcol.eventually (eventually_ge_nhds (sub_lt_self L hε))] with n hn
    by_cases h : n.unpair.1 = i
    · rw [if_pos h, htab n h]; exact hn
    · rw [if_neg h]; linarith
  have hcolLE : (fun k => (ledgerLuv 0 (Nat.pair i k)).expect P (Nat.pair i k)) ≲ₙ
      fun _ => L := by
    intro ε hε
    filter_upwards [hpair.eventually (hLE ε hε)] with k hk
    simpa [columnPad, Nat.unpair_pair] using hk
  have hcolGE : (fun k => (ledgerLuv 0 (Nat.pair i k)).expect P (Nat.pair i k)) ≳ₙ
      fun _ => L := by
    intro ε hε
    filter_upwards [hpair.eventually (hGE ε hε)] with k hk
    simpa [columnPad, Nat.unpair_pair] using hk
  exact convergesTo_iff_asympEq_const.2 (asympEq_iff_asympLE_asympGE.2 ⟨hcolLE, hcolGE⟩)

end Cleanroom.Deference.DefTrackingPin
