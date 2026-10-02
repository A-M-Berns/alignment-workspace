import Cleanroom.Fa.FaEisenstatConj.Computable
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Efficiency

/-!
# `fa-eisenstat-conj` · GenRefuted: the (Gen) refutation with an explicit FAF trader (T4, S1)

**The reading refuted** ([[merging-inductors-model]] §(a.1), quoted): "The bare derived sequence
`B` does **not** satisfy the LI criterion unrestricted. … on the unobservable class … the
good-feedback hypothesis is *vacuous* and `B_t(φ_t) = 𝔼^A_t(⌜μ_t⌝)` can be anything `A` likes. A
trader that knows `A`'s bias there exploits `B`." (trust-lab-008's (Gen): "`B` satisfies the LI
criterion for its own market".) **Precise reading formalized** (ATTRIBUTION-UNVETTED as a choice
among the note's phrasings): *for the merge construction with the feedback clause vacuous — a
quote assignment `Q` that is e.c. and in `A`'s language but constrained by nothing about `H` —
the merge market is exploited.* Here `Q φ n := priceLuv ⊥` (`botQuotes`): a legal quote
assignment (e.c., `[0,1]`-valued, in `A`'s language) that names nothing about `H`; then
`𝔼^∗_n(φ) = ℙ^A_n(⊥) → 0` for every `φ` (FAF's `lic_provind_false`), and the trader
`buyOneDaily ⊤` — one share of `⊤` every day, FAF's `APITests` trader re-declared here with its
fuel certificate — gains `1 − ℙ^A_i(⊥) ≥ 1/2` on every late day in every world, so it exploits
`𝔼^∗` against **every** deductive process with consistent stages (`gen_refuted_of`,
`exploits_of_ge_partialSums_from`). The existential form over the mirror pair's real markets is
`gen_refuted` (`Witnesses.lean`).

**The substitution, disclosed (repair round 1; audit r1 fidelity B2 / adversarial B1).** The
note's no-feedback hole *keeps the honest quote* `⌜ℙ^H_{f(t)}(φ)⌝` and removes `A`'s feedback
about it: the quote atom is left **undecided** by `A`'s theory, so `A`'s price of it "can be
anything `A` likes" and the exploiter is "a trader that knows `A`'s bias". `botQuotes` renders
that hole as a quote `A`'s theory **refutes** (`⊥`), so the merge's bias is *forced* to `0` by
`thm:provind` and the dumbest trader collects it. That is a modelling substitution in the sense
of [[STANDARDS]] §3 (c): a different, strictly more tractable object (any `Q` whose merge is a
non-inductor would do; the proof never looks at `H` or `f`). What T4 refutes is therefore the
**∃-over-`Q` reading** of (Gen) — *some* legal e.c. quote assignment constrained by nothing about
`H` makes the merge exploited — not the note's own instance. The note's own instance, the
honest quote atom with no feedback, is stated OPEN at W1 (`gen_honestQuote_noFeedback_w1`,
`Open.lean`): its direction turns on the LIA's prices of never-decided atoms, which nothing
available pins (`fa-theorem-a` F15).

**S1** (`mixedQuotes`): with the honest quote on the even days and `priceLuv ⊥` on the odd days,
the same trader exploits the merge on the odd days — so honesty on a divergent generable
day-set (the model's own `w`) does not make the market an inductor *unrestricted*. **What this
does and does not say about the note's fallback** (repair round 1; audit r1 fidelity B1 /
adversarial B2): the note's last sentence, "`B` is at best an inductor *on the good-feedback
subsequence* and unconstrained off it", is a *concession* — it already asserts unrestricted
failure, and S1 *agrees with* it (the proof uses the odd days only; `Q` is universally
quantified, so the even-day honesty is a disclosure of the instance, not an ingredient). S1
refutes nothing the note claims. The note's phrase had no FAF object; § E below gives it one —
`InductorOn P DP S`, the criterion restricted to traders supported on the day-set `S` — and then:
along the **odd** days the mixed merge is *refuted* (`gen_refuted_mixed_oddDays`, with the
certified odd-day trader `buyTopOdd`), while along the **even** days — the note's fallback
proper — it is **OPEN** (`fallback_evenDays_noExploit`, `Open.lean`), for the same reason as the
inductor half T3. The *behavioural* reading of the fallback survives as a theorem
(`mergeMarket_provind_evenDays`, `Companion.lean`).

**Surviving neighbour** (the artifact check of [[STANDARDS]] §3): the refutation is about the
*missing feedback*, not the merge construction — under the package of record `MergeQuotes`,
`𝔼^∗_n(φ) → 1` on every theorem of `DPH` (`mergeMarket_provind`, `Companion.lean`), exactly the
property these instances violate.

Scope: one-way, mirror direction — `A` reads `H` through the ledger; `H` never reads `A`. This is
the lookahead construction in the **corpus construal (Abram's version)**, not Sam Eisenstat's
intended information structure ([[eisenstat-conjecture-attribution]] §2, §5); claims about Sam's
intent are ATTRIBUTION-UNVETTED.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. The trader -/

/-- The trader that buys one share of `φ` every day (FAF's `APITests.LogicalInduction.buyOneDaily`,
re-declared because `APITests` is not an importable module of the package).
Source: FAF `APITests/LogicalInduction.lean:34`; mandate T4
Kind: D
Fidelity: exact
Hyps: n/a -/
def buyOneDaily (φ : Sentence) : Trader where
  strat _ :=
    { trades := [(EF.const 1, φ)]
      rank_le := by simp }

/-- The trader carries a fuel certificate (FAF's `APITests` certificate, verbatim).
Source: FAF `APITests/LogicalInduction.lean:68`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyOneDaily_polyFueled (φ : Sentence) : PolyFueledTrader (buyOneDaily φ) :=
  PolyFueledTrader.ofSingleTradeBlocksBig _ (fun _ => EF.const 1) (fun _ => φ)
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1))
    (fun _ => trivial)
    (BigSentenceCodes.const φ)
    (fun _ => rfl)

/-- **The trader is efficiently computable** in the paper's own sense (`def:ec`), by FAF's bridge
`PolyFueledTrader.toEfficientlyComputable` — a certificate, not an assumption.
Source: FAF `APITests/LogicalInduction.lean:77`; mandate T4 ("e.c. by certificate")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyOneDaily_efficientlyComputable (φ : Sentence) :
    EfficientlyComputable (buyOneDaily φ) :=
  (buyOneDaily_polyFueled φ).toEfficientlyComputable

/-- The trader's net worth: `∑_{i ≤ n} (payout(φ) − V_i(φ))` — one share a day, bought at the
day's price, worth the world's payout.
Source: none: infrastructure (FAF `Trader.netWorth`, `Strategy.value`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyOneDaily_netWorth (φ : Sentence) (V : History) (v : PCWorld) (n : ℕ) :
    (buyOneDaily φ).netWorth V v n = ∑ i ∈ Finset.range (n + 1), (v.payout φ - V i φ) := by
  simp [Trader.netWorth, Strategy.value, buyOneDaily]

/-- **The exploitation engine for the `⊤`-share trader**: against any `[0,1]`-valued market with
consistent stages, if the price of `⊤` is at most `1/2` on every late day of a set `S` met
infinitely often, `buyOneDaily ⊤` exploits — its net worth is `∑_{i ≤ n} (1 − P_i(⊤))` in every
world (the payout of `⊤` is `1` everywhere), each term `≥ 0`, and `≥ 1/2` on the late days of
`S` (FAF's `exploits_of_ge_partialSums_from`, world-independent lower bound).
Source: mandate T4 (the net-worth arithmetic); FAF `exploits_of_ge_partialSums_from`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem buyOneDaily_top_exploits (P : History) (DP : DeductiveProcess)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (S : Set ℕ) (hS : ∃ᶠ n in atTop, n ∈ S) (k : ℕ)
    (hk : ∀ i, k ≤ i → i ∈ S → P i ⊤ ≤ 1 / 2) :
    (buyOneDaily ⊤).Exploits P DP := by
  classical
  refine exploits_of_ge_partialSums_from (buyOneDaily ⊤) P DP hP
    (fun i => if k ≤ i ∧ i ∈ S then (1 / 2 : ℝ) else 0) (1 / 2) (by norm_num)
    (fun i => by split_ifs <;> norm_num) k ?_ ?_ hcons
  · intro n _ v _
    rw [buyOneDaily_netWorth]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpay : v.payout (⊤ : Sentence) = 1 := by
      unfold PCWorld.payout
      rw [if_pos (PCWorld.holds_top v)]
    rw [hpay]
    split_ifs with h
    · linarith [hk i h.1 h.2]
    · linarith [(hP i ⊤).2]
  · refine (hS.and_eventually (eventually_ge_atTop k)).mono fun n hn => ?_
    rw [if_pos ⟨hn.2, hn.1⟩]

/-! ## B. The price of `⊥` under an inductor -/

/-- Every inductor's price of `⊥` tends to `0` (FAF's `lic_provind_false` at the constant family
`⊥`, which fails in every world).
Source: FAF `thm:provind` (`lic_provind_false`)
Kind: L
Fidelity: exact
Hyps: (a) `hworldA` (FAF's disclosed world boundary) -/
theorem bot_price_tendsto_zero {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    Tendsto (fun n => A n (⊥ : Sentence)) atTop (𝓝 0) := by
  have h := lic_provind_false A DPA (fun _ => (⊥ : Sentence)) (MachineSentenceCodes.const ⊥)
    (fun _ v _ => (PCWorld.holds_neg v ⊥).mpr (fun hb => hb)) hworldA
  simpa [AsympEq] using h

/-! ## C. T4: the feedback-free quote assignment -/

/-- **The feedback-free quote assignment**: every quote is `priceLuv ⊥`. A *legal* quote
assignment — e.c. (`botQuotes_codes`), uniformly computable (`botQuotes_quoteTable`),
`[0,1]`-valued, in `A`'s language — constrained by nothing about `H`. **Not the note's quote:**
the note's no-feedback hole keeps the honest quote atom `⌜ℙ^H_{f(t)}(φ)⌝` and leaves it
*undecided* by `A`'s theory; `botQuotes` puts in its place a sentence `A`'s theory *refutes*, so
that the merge's bias is forced rather than free (a (c) substitution, module docstring). The
merge under it is constant across sentences on every day (`mergeMarket_botQuotes`).
Source: [[merging-inductors-model]] §(a.1) (the no-feedback hole); trust-lab-008 ((Gen)); mandate T4
Kind: D
Fidelity: variant: the undecided honest quote atom replaced by the refutable constant `⊥` (the ∃-over-`Q` reading of "constrained by nothing about `H`")
Hyps: n/a -/
def botQuotes : Sentence → ℕ → LUV := fun _ _ => priceLuv ⊥

/-- `priceLuv_bot_gt`: the thresholds of `priceLuv ⊥` are `⊤` below `0` and `⊥` from `0` on.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLuv_bot_gt (r : ℚ) : (priceLuv ⊥).gt r = if r < 0 then (⊤ : Sentence) else ⊥ := by
  simp only [priceLuv_gt]
  split_ifs <;> rfl

/-- The feedback-free quote table is computable.
Source: mandate T4 (`QuoteTable` by constancy)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem botQuotes_quoteTable : QuoteTable botQuotes := by
  unfold QuoteTable botQuotes
  have hc : PrimrecPred fun p : (Sentence × ℕ) × ℚ => (0 : ℚ) ≤ p.2 :=
    ratLE_prim.comp (Primrec.const 0) Primrec.snd
  refine (Primrec.ite hc (Primrec.const (⊥ : Sentence))
    (Primrec.const (⊤ : Sentence))).to_comp.of_eq fun p => ?_
  rw [priceLuv_bot_gt]
  by_cases h : (0 : ℚ) ≤ p.2
  · rw [if_pos h, if_neg (not_lt.mpr h)]
  · rw [if_neg h, if_pos (not_le.mp h)]

/-- Every feedback-free quote family is e.c.
Source: mandate T4
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem botQuotes_codes (φ : Sentence) : LUV.MachineThresholdCodeSeq (botQuotes φ) :=
  priceLuv_codeSeq ⊥

/-- Under the feedback-free assignment the merge market prices every sentence at `A`'s price of
`⊥`: `𝔼^∗_n(φ) = ℙ^A_n(⊥)` (`priceLuv_expect`).
Source: [[merging-inductors-model]] §(a.1) ("`B_t(φ_t) = 𝔼^A_t(⌜μ_t⌝)` can be anything `A` likes")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mergeMarket_botQuotes (A : History) (n : ℕ) (φ : Sentence) :
    mergeMarket A botQuotes n φ = A n ⊥ :=
  priceLuv_expect ⊥ A n

/-- **T4 (headline, general form). (Gen) refuted with an explicit trader:** for any inductor `A`
over a process with consistent stages, the feedback-free merge market `mergeMarket A botQuotes` is
exploited by `buyOneDaily ⊤` against **every** deductive process `DP` with consistent stages —
`H`'s process `DPH` in particular (the existential over the mirror pair's real markets is
`gen_refuted`, `Witnesses.lean`). The merge prices `⊤` at `ℙ^A_n(⊥) → 0`
(`bot_price_tendsto_zero`), so from some day on the trader gains `≥ 1/2` a day in every world.
The refuted object is the merge construction `mergeMarket` at a *legal* quote assignment
(`botQuotes_codes`, `botQuotes_quoteTable`, `[0,1]`-valued) — not a bespoke bad market — but
**not the note's own `B`**: `botQuotes` replaces the note's undecided honest quote atom by the
refutable `⊥`, so the bias is forced by `thm:provind` instead of free, and no `H` or `f` enters
the proof (the statement has no `H`). This refutes the ∃-over-`Q` reading of (Gen); the note's
own instance is OPEN (`gen_honestQuote_noFeedback_w1`; module docstring, repair round 1).
The trader is e.c. by certificate (`buyOneDaily_efficientlyComputable`). `hcons` is used: over a
contradictory `DP` every market is an inductor and nothing is refuted.
Scope: one-way (corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam). The reading
refuted and the surviving neighbour are in the module docstring.
Source: trust-lab-008 ((Gen), "L"); [[merging-inductors-model]] §(a.1) ("A trader that knows `A`'s bias there exploits `B`"); [[merging-inductors-ideate]] Idea 1 (1b)
Kind: P
Fidelity: variant: the no-feedback quote rendered as the refutable constant `⊥` (bias forced by provind), not as the note's honest-but-undecided quote atom (whose LIA price is unpinned, `fa-theorem-a` F15)
Hyps: (a) `hworldA`, `hcons` (FAF's disclosed world boundaries); (c) `botQuotes` in place of the honest quote without feedback -/
theorem gen_refuted_of {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (DP : DeductiveProcess) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyOneDaily ⊤).Exploits (mergeMarket A botQuotes) DP := by
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    ((bot_price_tendsto_zero (A := A) hworldA).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine buyOneDaily_top_exploits _ DP
    (mergeMarket_mem_Icc (fun n s => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) n s) _)
    hcons Set.univ (Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => Set.mem_univ _))
    k fun i hi _ => ?_
  rw [mergeMarket_botQuotes]
  exact hk i hi

/-- **T4, criterion form (stronger):** the feedback-free merge market is not a logical inductor
over *any* deductive process with consistent stages. Same scope as `gen_refuted_of`: the
∃-over-`Q` reading, at the substituted quote `botQuotes`.
Source: trust-lab-008 ((Gen)); mandate T4 ("stronger form to state")
Kind: P
Fidelity: variant: as `gen_refuted_of`
Hyps: (a) `hworldA`, `hcons`; (c) `botQuotes` -/
theorem gen_refuted_notInductor {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (DP : DeductiveProcess) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (mergeMarket A botQuotes) DP :=
  fun hLI => hLI.noExploit _ (buyOneDaily_efficientlyComputable ⊤) (gen_refuted_of hworldA DP hcons)

/-! ## D. S1: good feedback on the even days does not rescue (Gen) -/

/-- **The mixed quote assignment**: the given quotes on the even days, `priceLuv ⊥` on the odd
days. At `Q := ledgerLuv ⌜φ⌝` over the all-sentences mirror ledger (`Witnesses.lean`) the even-day
quote is the honest, determined mirror quote of `H (f n) φ` and the odd-day quote is the
refutable `⊥` (the same (c) substitution as `botQuotes`, on the odd days) — the model's
"good-feedback subsequence" is the even days, a divergent `A`-generable day-set
(`fa-theorem-a`'s `evenDays_pgenerable`).
Source: [[merging-inductors-model]] §(a.1) last sentence ("at best an inductor on the good-feedback subsequence"); [[merging-inductors-ideate]] Idea 1; mandate S1
Kind: D
Fidelity: variant: honest quotes on the even days; off them the refutable constant `⊥`, not an undecided quote
Hyps: n/a -/
def mixedQuotes (Q : Sentence → ℕ → LUV) : Sentence → ℕ → LUV :=
  fun φ n => if n % 2 = 0 then Q φ n else priceLuv ⊥

/-- On the odd days the mixed merge market prices every sentence at `A`'s price of `⊥`.
Source: mandate S1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mergeMarket_mixedQuotes_odd (A : History) (Q : Sentence → ℕ → LUV) {n : ℕ}
    (hn : n % 2 = 1) (φ : Sentence) : mergeMarket A (mixedQuotes Q) n φ = A n ⊥ := by
  have h : ¬ n % 2 = 0 := by omega
  simp [mixedQuotes, h, priceLuv_expect]

/-- On the even days the mixed merge market is the given merge market.
Source: mandate S1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mergeMarket_mixedQuotes_even (A : History) (Q : Sentence → ℕ → LUV) {n : ℕ}
    (hn : n % 2 = 0) (φ : Sentence) : mergeMarket A (mixedQuotes Q) n φ = mergeMarket A Q n φ := by
  simp [mixedQuotes, hn]

/-- The mixed quote table is computable when the given one is (Mathlib's `Computable.cond` on the
parity test).
Source: mandate S1 (`QuoteTable` by cases)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem mixedQuotes_quoteTable {Q : Sentence → ℕ → LUV} (hQ : QuoteTable Q) :
    QuoteTable (mixedQuotes Q) := by
  unfold QuoteTable mixedQuotes
  obtain ⟨_, hc⟩ : PrimrecPred fun p : (Sentence × ℕ) × ℚ => p.1.2 % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2))
      (Primrec.const 0)
  have hbot : Computable fun p : (Sentence × ℕ) × ℚ => (priceLuv ⊥).gt p.2 :=
    (botQuotes_quoteTable : _)
  refine (Computable.cond hc.to_comp (hQ : _) hbot).of_eq fun p => ?_
  by_cases h : p.1.2 % 2 = 0
  · rw [decide_eq_true h, if_pos h]
    rfl
  · rw [decide_eq_false h, if_neg h]
    rfl

/-- The mixed quote families are e.c. when the given ones are: FAF's `MachineSentenceCodes.ifZero`
on the parity ruler `n ↦ n % 2` (from FAF's `divmodc_polyFueled`), dispatching between the given
threshold family and the constant family of `priceLuv ⊥`.
Source: mandate S1 (`MachineThresholdCodeSeq (Q φ)` by `ifZero` on the parity ruler); FAF `MachineSentenceCodes.modDispatch` (the same ruler)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem mixedQuotes_codes {Q : Sentence → ℕ → LUV} (hQ : ∀ φ, LUV.MachineThresholdCodeSeq (Q φ))
    (φ : Sentence) : LUV.MachineThresholdCodeSeq (mixedQuotes Q φ) := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  have hrem : UnaryRuler (fun z : ℕ => z.unpair.1 % 2) :=
    UnaryRuler.of_polyFueled
      ((PolyFueled.right.comp (hdm.comp PolyFueled.left)).of_eq (fun z => by simp))
  have h := MachineSentenceCodes.ifZero (hQ φ) (priceLuv_codeSeq ⊥) hrem
  refine h.of_eq fun m => ?_
  by_cases hm : m.unpair.1 % 2 = 0
  · simp [mixedQuotes, hm]
  · simp [mixedQuotes, hm]

/-- **S1 (headline). Honest quotes on the even days, `⊥` on the odd days: still not an inductor
unrestricted.** For any inductor `A` with consistent stages and *any* quote assignment `Q`
(honest or not — `Q` is universally quantified and the proof uses the odd days only), the mixed
merge market `mergeMarket A (mixedQuotes Q)` is exploited by `buyOneDaily ⊤` against every
deductive process with consistent stages — the trader gains `≥ 0` every day and `≥ 1/2` on every
late odd day. At `Q := ledgerLuv ⌜·⌝` over the mirror ledger (`gen_refuted_evenDays`,
`Witnesses.lean`) the even days carry the honest determined quote; that conjunct *discloses* the
instance and is not used by the exploitation. **This agrees with the note** ("unconstrained off
it" entails unrestricted failure) and does **not** decide the note's fallback "at best an
inductor *on* the good-feedback subsequence": that fallback, made a FAF object as
`InductorOn … {n | n % 2 = 0}` (§ E), is OPEN (`fallback_evenDays_noExploit`, `Open.lean`), while
its odd-day complement is refuted (`gen_refuted_mixed_oddDays`). The *behavioural* reading of
the fallback survives: Lemma P along the even days (`mergeMarket_provind_evenDays`,
`Companion.lean`).
Scope: one-way (corpus construal, Abram's version; ATTRIBUTION-UNVETTED as to Sam).
Source: [[merging-inductors-model]] §(a.1) last sentence; [[merging-inductors-ideate]] Idea 1 ("inductor-like on the good-feedback subsequence, unconstrained off it"); mandate S1
Kind: P
Fidelity: variant: odd-day quotes are the refutable `⊥` (the (c) of `botQuotes`), not undecided honest quotes; conclusion is unrestricted failure, which the note asserts
Hyps: (a) `hworldA`, `hcons`; (c) `priceLuv ⊥` off the even days -/
theorem gen_refuted_mixed_of {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (Q : Sentence → ℕ → LUV)
    (DP : DeductiveProcess) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyOneDaily ⊤).Exploits (mergeMarket A (mixedQuotes Q)) DP := by
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    ((bot_price_tendsto_zero (A := A) hworldA).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine buyOneDaily_top_exploits _ DP
    (mergeMarket_mem_Icc (fun n s => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) n s) _)
    hcons {n | n % 2 = 1} (Filter.frequently_atTop.2 fun N => ⟨2 * N + 1, by omega, by show (2 * N + 1) % 2 = 1; omega⟩)
    k fun i hi hodd => ?_
  rw [mergeMarket_mixedQuotes_odd A Q hodd]
  exact hk i hi

/-- **S1, criterion form:** the mixed merge market is not a logical inductor over any deductive
process with consistent stages (unrestricted failure; same scope as `gen_refuted_mixed_of`).
Source: mandate S1
Kind: P
Fidelity: variant: as `gen_refuted_mixed_of`
Hyps: (a) `hworldA`, `hcons`; (c) `priceLuv ⊥` off the even days -/
theorem gen_refuted_mixed_notInductor {A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (Q : Sentence → ℕ → LUV) (DP : DeductiveProcess)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (mergeMarket A (mixedQuotes Q)) DP :=
  fun hLI => hLI.noExploit _ (buyOneDaily_efficientlyComputable ⊤)
    (gen_refuted_mixed_of hworldA Q DP hcons)

/-! ## E. The criterion along a day-set — the note's "inductor on the good-feedback subsequence"
as a FAF object (repair round 1) -/

/-- **A trader supported on a day-set `S`**: on every day off `S`, every coefficient of its
strategy denotes `0` against every history — it buys nothing off `S`, so its net worth is the
sum of its strategy values on the days of `S` alone (`TraderSupportedOn.value_eq_zero`). FAF's
`Trader`, unrestricted; the empty trade list qualifies, and so does a coefficient `EF.const 0`.
Introduced so that the model's phrase "an inductor *on the good-feedback subsequence*" has an
object (audit r1, fidelity B1 / adversarial B2).
Source: [[merging-inductors-model]] §(a.1) last sentence; [[merging-inductors-ideate]] Idea 1
Kind: D
Fidelity: variant: FAF has no day-set-relative trader class; this is `Trader` restricted by support
Hyps: n/a -/
def TraderSupportedOn (Tr : Trader) (S : Set ℕ) : Prop :=
  ∀ n, n ∉ S → ∀ p ∈ (Tr.strat n).trades, ∀ V : History, p.1.denote V = 0

/-- Off its support, a trader's day strategy has value `0` in every world against every history.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem TraderSupportedOn.value_eq_zero {Tr : Trader} {S : Set ℕ} (h : TraderSupportedOn Tr S)
    {n : ℕ} (hn : n ∉ S) (V : History) (w : Sentence → ℝ) : (Tr.strat n).value V w = 0 := by
  unfold Strategy.value
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  rw [h n hn p hp V, zero_mul]

/-- **The criterion along a day-set `S`** — the note's "inductor on the subsequence `S`", made a
FAF object: no e.c. trader supported on `S` exploits `P` against `DP`. At `S = Set.univ` it is
FAF's `noExploit` clause verbatim (`inductorOn_univ`); it is antitone in `S` (`InductorOn.mono`);
every inductor satisfies it on every `S` (`InductorOn.of_inductor`) — a *weakening* of the
criterion, as "at best an inductor on the subsequence" requires. The quantifier has content:
`buyTopEven` / `buyTopOdd` below are certified e.c. traders supported on the even / odd days
that buy a share of `⊤` on each of them, and `buyTopOdd` refutes the mixed merge along the odd
days (`gen_refuted_mixed_oddDays`). The sources have no definition of the phrase; this is one
reading (a trader *trades* only on `S`; its coefficients may still read every day's prices).
Source: [[merging-inductors-model]] §(a.1) last sentence ("`B` is at best an inductor *on the good-feedback subsequence* and unconstrained off it"); [[merging-inductors-ideate]] Idea 1
Kind: D
Fidelity: variant: FAF's criterion (`def:lic`, the `noExploit` clause) restricted to traders supported on `S`; the note has no definition
Hyps: n/a -/
def InductorOn (P : History) (DP : DeductiveProcess) (S : Set ℕ) : Prop :=
  ∀ Tr : Trader, EfficientlyComputable Tr → TraderSupportedOn Tr S → ¬ Tr.Exploits P DP

/-- At the full day-set the criterion along `S` is FAF's `noExploit` clause.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem inductorOn_univ (P : History) (DP : DeductiveProcess) :
    InductorOn P DP Set.univ ↔ ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits P DP :=
  ⟨fun h Tr hTr => h Tr hTr fun n hn => absurd (Set.mem_univ n) hn,
   fun h Tr hTr _ => h Tr hTr⟩

/-- The criterion along a day-set is antitone in the day-set.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem InductorOn.mono {P : History} {DP : DeductiveProcess} {S T : Set ℕ} (hST : S ⊆ T)
    (h : InductorOn P DP T) : InductorOn P DP S :=
  fun Tr hTr hsupp => h Tr hTr fun n hn => hsupp n fun hS => hn (hST hS)

/-- Every logical inductor satisfies the criterion along every day-set.
Source: none: infrastructure (FAF `IsLogicalInductor.noExploit`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem InductorOn.of_inductor {P : History} {DP : DeductiveProcess}
    [hLI : IsLogicalInductor P DP] (S : Set ℕ) : InductorOn P DP S :=
  fun Tr hTr _ => hLI.noExploit Tr hTr

/-- **A parity trader is e.c.**: a trader whose day-`n` strategy is the single trade
`(EF.const (if n % 2 = 0 then q₀ else q₁), φ)` carries FAF's machine-side certificate
(`EfficientlyComputable.ofSingleTradeBlocksBig`): the coefficient stream is
`MachineTokenStream.ifZero` on the parity ruler `n ↦ n % 2` (from FAF's `divmodc_polyFueled`)
between the two constant serializations, the sentence family is `MachineSentenceCodes.const`.
Source: none: infrastructure (FAF `def:ec`; the parity ruler of `mixedQuotes_codes`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem parityTrader_efficientlyComputable (Tr : Trader) (q₀ q₁ : ℚ) (φ : Sentence)
    (hTr : ∀ n, (Tr.strat n).trades = [(EF.const (if n % 2 = 0 then q₀ else q₁), φ)]) :
    EfficientlyComputable Tr := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  have hrem : UnaryRuler (fun n : ℕ => n % 2) :=
    UnaryRuler.of_polyFueled ((PolyFueled.right.comp hdm).of_eq (fun z => by simp))
  refine EfficientlyComputable.ofSingleTradeBlocksBig Tr
    (fun n => EF.const (if n % 2 = 0 then q₀ else q₁)) (fun _ => φ) ?_ (fun _ => trivial)
    (MachineSentenceCodes.const φ) hTr
  refine ((MachineTokenStream.const (EF.const q₀).serialize).ifZero
    (MachineTokenStream.const (EF.const q₁).serialize) hrem).of_eq fun n => ?_
  by_cases h : n % 2 = 0 <;> simp [h]

/-- The trader that buys one share of `⊤` on every even day and nothing on the odd days
(coefficient `1` on even days, `0` on odd days).
Source: none: infrastructure (the non-vacuity witness of `InductorOn` on the even days)
Kind: D
Fidelity: exact
Hyps: n/a -/
def buyTopEven : Trader where
  strat n :=
    { trades := [(EF.const (if n % 2 = 0 then 1 else 0), ⊤)]
      rank_le := by simp }

/-- The trader that buys one share of `⊤` on every odd day and nothing on the even days.
Source: none: infrastructure (the refuting trader of `gen_refuted_mixed_oddDays`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def buyTopOdd : Trader where
  strat n :=
    { trades := [(EF.const (if n % 2 = 0 then 0 else 1), ⊤)]
      rank_le := by simp }

/-- `buyTopEven` is e.c. by certificate.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyTopEven_efficientlyComputable : EfficientlyComputable buyTopEven :=
  parityTrader_efficientlyComputable _ 1 0 ⊤ fun _ => rfl

/-- `buyTopOdd` is e.c. by certificate.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyTopOdd_efficientlyComputable : EfficientlyComputable buyTopOdd :=
  parityTrader_efficientlyComputable _ 0 1 ⊤ fun _ => rfl

/-- `buyTopEven` is supported on the even days.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyTopEven_supportedOn : TraderSupportedOn buyTopEven {n | n % 2 = 0} := by
  intro n hn p hp V
  have hn' : ¬ n % 2 = 0 := hn
  simp only [buyTopEven, List.mem_singleton] at hp
  subst hp
  simp [hn']

/-- `buyTopOdd` is supported on the odd days.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem buyTopOdd_supportedOn : TraderSupportedOn buyTopOdd {n | n % 2 = 1} := by
  intro n hn p hp V
  have hn' : n % 2 = 0 := by
    have : ¬ n % 2 = 1 := hn
    omega
  simp only [buyTopOdd, List.mem_singleton] at hp
  subst hp
  simp [hn']

/-- **The exploitation engine for the odd-day `⊤`-share trader**: against any `[0,1]`-valued
market with consistent stages whose price of `⊤` is at most `1/2` on every late odd day,
`buyTopOdd` exploits — its day-`i` value is `1 − P_i(⊤) ≥ 1/2` on late odd days and `0` on even
days (FAF's `exploits_of_ge_partialSums_from`, world-independent lower bound).
Source: none: infrastructure (as `buyOneDaily_top_exploits`, on the odd days only)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem buyTopOdd_exploits (P : History) (DP : DeductiveProcess)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k : ℕ) (hk : ∀ i, k ≤ i → i % 2 = 1 → P i ⊤ ≤ 1 / 2) :
    buyTopOdd.Exploits P DP := by
  classical
  refine exploits_of_ge_partialSums_from buyTopOdd P DP hP
    (fun i => if k ≤ i ∧ i % 2 = 1 then (1 / 2 : ℝ) else 0) (1 / 2) (by norm_num)
    (fun i => by split_ifs <;> norm_num) k ?_ ?_ hcons
  · intro n _ v _
    unfold Trader.netWorth
    refine Finset.sum_le_sum fun i _ => ?_
    have hpay : v.payout (⊤ : Sentence) = 1 := by
      unfold PCWorld.payout
      rw [if_pos (PCWorld.holds_top v)]
    simp only [buyTopOdd, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, EF.denote_const, hpay]
    by_cases hi : i % 2 = 0
    · have hw : ¬ (k ≤ i ∧ i % 2 = 1) := fun h => by omega
      rw [if_neg hw, if_pos hi]
      simp
    · rw [if_neg hi]
      simp only [Rat.cast_one, one_mul]
      split_ifs with h
      · linarith [hk i h.1 h.2]
      · linarith [(hP i ⊤).2]
  · have hodd : ∃ᶠ n in atTop, n % 2 = 1 :=
      Filter.frequently_atTop.2 fun N => ⟨2 * N + 1, by omega, by omega⟩
    refine (hodd.and_eventually (eventually_ge_atTop k)).mono fun n hn => ?_
    rw [if_pos ⟨hn.2, hn.1⟩]

/-- **S1, the complement along the odd days (P): the mixed merge market is refuted along the
odd days** — `InductorOn … {n | n % 2 = 1}` fails: the certified odd-day trader `buyTopOdd`,
supported on the odd days, exploits `mergeMarket A (mixedQuotes Q)` against every process with
consistent stages (on the odd days the merge prices `⊤` at `ℙ^A_n(⊥) → 0`). Together with the
OPEN `fallback_evenDays_noExploit` (`Open.lean`) this locates the note's fallback exactly: along
the days where the quote is the refutable `⊥`, the criterion fails; along the honest days it is
the open question T3 restricted to even-day traders.
Source: [[merging-inductors-model]] §(a.1) last sentence ("unconstrained off it"); repair round 1
Kind: P
Fidelity: variant: odd-day quotes are the refutable `⊥` (the (c) of `botQuotes`); day-set criterion `InductorOn` (one reading of the note's phrase)
Hyps: (a) `hworldA`, `hcons`; (c) `priceLuv ⊥` off the even days -/
theorem gen_refuted_mixed_oddDays {A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (Q : Sentence → ℕ → LUV) (DP : DeductiveProcess)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ InductorOn (mergeMarket A (mixedQuotes Q)) DP {n | n % 2 = 1} := by
  intro h
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    ((bot_price_tendsto_zero (A := A) hworldA).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine h buyTopOdd buyTopOdd_efficientlyComputable buyTopOdd_supportedOn ?_
  refine buyTopOdd_exploits _ DP
    (mergeMarket_mem_Icc (fun n s => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) n s) _)
    hcons k fun i hi hodd => ?_
  rw [mergeMarket_mixedQuotes_odd A Q hodd]
  exact hk i hi

end Cleanroom.Fa.FaEisenstatConj
