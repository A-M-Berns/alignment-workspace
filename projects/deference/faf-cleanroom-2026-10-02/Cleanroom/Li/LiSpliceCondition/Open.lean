import Cleanroom.Li.LiSpliceCondition.Splice
import Cleanroom.Li.LiSpliceCondition.Translate
import Cleanroom.Li.LiProjection.Fragments
import LogicalInduction.Framework.Machine.WriteOutMachine

/-!
# `li-splice-condition` · Open: the open statements of record

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 5 of the layout.
Every `sorry` in the package is in this file, and every theorem here is listed in
`run/wp/li-splice-condition/li-splice-condition-open.txt` with its reason. Nothing load-bearing
rests on them except where the report says so (T3.4/T3.5 rest on `translateStreamRewriter`).

* **(B1) `translateStreamRewriter`** — the one `Complexity.FP` obligation of T3.4/T3.5: every
  polynomial-time output word can be rewritten in polynomial time into one whose decoded day-`n`
  strategy is the zeroed (resp. re-priced) strategy of the original's. Stated at the
  decoded-strategy level like li-projection's `mirrorStreamRewriter`. What a proof needs: a
  frame pass that tests each trade frame's sentence block for `ψ` or the shape `φ ⋏ ψ` with
  `φ ∈ Φ` (finitely many fixed codes, so a `FiberTest`-style comparison), drops or rescales the
  frame, and a leaf pass on price leaves (FAF's `FreezeStreamRewriter`/`EF.conditionPrices` shape
  covers the leaves; the frames are the new part — li-projection findings F1). **Wrong-quantifier
  hazard** (mandate): the rewriter is needed for *every* e.c. trader `T`, not for a class — this is
  why it is a statement about `Complexity.FP` words, not a hypothesis on `T`. The derivations
  `EfficientlyComputable.zeroTranslate` / `.repriceTranslate` are plumbing (hypothesis ⟺
  conclusion, `zeroStreamRewriter_iff` / `repriceStreamRewriter_iff`), never rowed as content.
* **(B2) `exists_inductor_pair_harmonic_disagreement`** — the antecedent of T1.6(ii).
* **(B3) `exists_inductor_pos_on_refuted`** — the free horn's positivity hypothesis (063(c)); the
  obstruction is sharper than summability: `summable_schedule_mul_price_of_refuted`
  (`DayIndexed.lean`, repair round 1).
* **(B4) `stale_finite_isLogicalInductor`**, **(B5) `stale_infinite_isLogicalInductor`** — T2.7.
* **(B6)** — *withdrawn in repair round 1*: the former `conditioned_dayIndexed_floor` (063(a)) was
  trivially true (its `∃ DP'` admitted an unsatisfiable process, both round-1 audits). 063(a) now
  lives in `DayIndexed.lean` and `Candidate.lean` (repair round 2): the growing-conjunction
  reading is FAF's theorem with no floor (`conditioned_prefix_isLogicalInductor`, the inventory's
  own covered case); the learned-past reading is proved with the floor *derived* by provability
  induction (`conditioned_learnedPast_isLogicalInductor`), a reading in which the source's floor
  conjecture is vacuous and which is not the source's use case; the single-condition reading over
  any accumulating process is refuted at the alternating instance
  (`conditioned_alternating_exploited`, `conditioned_dayIndexed_floor_false`); and the source's
  own candidate reading (unchosen candidates with an exploration floor) is not an "inductor over a
  process" claim — what holds is gated non-exploitation under a uniform floor
  (`conditioned_candidate_not_gatedExploits`). No *statement* of 063(a) is open here; what is
  recorded, not attempted, is the source's decaying `ε_n` "with `Σ` constraints" (outside FAF's
  translator, which takes one rational floor) and any limit claim about `P_n(· | a_n)` in the
  candidate reading (findings F14).
* **(B7) `truth_price_apart_iff_undecided`** — 063(b).
* **(B8) `ccLimit_realizedValue_summable`** — dp-core-110's Claim CC-limit in a *realized-value*
  reading that the source's own mechanics sentence does not support (its `c_t`, `q_t` are both
  market prices; ATTRIBUTION-UNVETTED, findings F9); kept as a statement of record only. Its
  unconditional analogue is refuted outright (`ccLimit_realized_refuted`, below, no `sorry`); the
  source's price-versus-price claim needs a refundable conditional-contract good FAF does not have
  and is neither stated nor refuted here.
* **(B9) `splice_summable_conjecture`** — R1.5's replacement conjecture; the parity trader is
  proved harmless under it in `Splice.lean` (`parityTrader_not_exploits_paritySplice_of_summable`).
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Filter Topology

/-! ## (B1) The translation certificate -/

/-- **The zeroing stream rewriter**: every polynomial-time output word can be rewritten in
polynomial time into one whose decoded day-`n` strategy is the zeroed strategy of the original's.
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i), "`T̃` is efficiently computable"); mandate T3.4
Kind: D
Fidelity: exact -/
def ZeroStreamRewriter (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) : Prop :=
  ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧
      ∀ n, strategyOfOutput n (G (unaryDay n)) =
        Strategy.zeroTranslate ψ Φ N (strategyOfOutput n (F (unaryDay n)))

/-- **The re-pricing stream rewriter**: likewise for the re-priced strategy.
Source: [[corr-legit-neg-inventory]] 061 (E7 proof of (ii), "a syntactic rewrite of the same kind as FAF's `EF.conditionPrices`, linear in the size of `T`'s day-`m` strategy plus the cost of `r`"); mandate T3.4–T3.5
Kind: D
Fidelity: exact -/
def RepriceStreamRewriter (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ) : Prop :=
  ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧
      ∀ n, strategyOfOutput n (G (unaryDay n)) =
        Strategy.repriceTranslate ψ Φ r (strategyOfOutput n (F (unaryDay n)))

/-- The zeroing rewriter makes every e.c. trader's zeroed trader e.c. (plumbing).
Source: mandate T3.4 ("`EfficientlyComputable.translate` as its one-line consumer")
Kind: L
Fidelity: n/a -/
theorem EfficientlyComputable.zeroTranslate {ψ : Sentence} {Φ : Finset Sentence} {N : ℕ}
    (hrw : ZeroStreamRewriter ψ Φ N) {T : Trader} (hT : EfficientlyComputable T) :
    EfficientlyComputable (Trader.zeroTranslate ψ Φ N T) := by
  obtain ⟨F, hF, hs⟩ := hT
  obtain ⟨G, hG, hGspec⟩ := hrw F hF
  exact ⟨G, hG, fun n => by rw [hGspec n, hs n]; rfl⟩

/-- The re-pricing rewriter makes every e.c. trader's re-priced trader e.c. (plumbing).
Source: mandate T3.4–T3.5
Kind: L
Fidelity: n/a -/
theorem EfficientlyComputable.repriceTranslate {ψ : Sentence} {Φ : Finset Sentence}
    {r : Sentence → ℕ → ℚ} (hrw : RepriceStreamRewriter ψ Φ r) {T : Trader}
    (hT : EfficientlyComputable T) :
    EfficientlyComputable (Trader.repriceTranslate ψ Φ r T) := by
  obtain ⟨F, hF, hs⟩ := hT
  obtain ⟨G, hG, hGspec⟩ := hrw F hF
  exact ⟨G, hG, fun n => by rw [hGspec n, hs n]; rfl⟩

/-- The zeroing rewriter **is** closure of e.c. traders under the zeroing translation (so the
derivation above is plumbing, hypothesis ⟺ conclusion; li-projection repair round 1).
Source: none: infrastructure (the shape of li-projection's `mirrorStreamRewriter_iff`)
Kind: L
Fidelity: n/a -/
theorem zeroStreamRewriter_iff (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) :
    ZeroStreamRewriter ψ Φ N ↔
      ∀ T : Trader, EfficientlyComputable T → EfficientlyComputable (Trader.zeroTranslate ψ Φ N T) := by
  constructor
  · intro h T hT
    exact EfficientlyComputable.zeroTranslate h hT
  · intro h F hF
    obtain ⟨G, hG, hGspec⟩ :=
      h ⟨fun n => strategyOfOutput n (F (unaryDay n))⟩ ⟨F, hF, fun _ => rfl⟩
    exact ⟨G, hG, fun n => hGspec n⟩

/-- The re-pricing rewriter **is** closure of e.c. traders under the re-pricing translation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem repriceStreamRewriter_iff (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ) :
    RepriceStreamRewriter ψ Φ r ↔
      ∀ T : Trader, EfficientlyComputable T →
        EfficientlyComputable (Trader.repriceTranslate ψ Φ r T) := by
  constructor
  · intro h T hT
    exact EfficientlyComputable.repriceTranslate h hT
  · intro h F hF
    obtain ⟨G, hG, hGspec⟩ :=
      h ⟨fun n => strategyOfOutput n (F (unaryDay n))⟩ ⟨F, hF, fun _ => rfl⟩
    exact ⟨G, hG, fun n => hGspec n⟩

/-- **OPEN (B1).** The translation stream rewriters exist: the zeroing one for every `ψ`, `Φ`, `N`,
and the re-pricing one for every e.c. rational family `r` on `Φ` (FAF's `MachineRatCodes`). Neither
proved nor refuted; believed true (each step is polynomial time: a frame pass with a comparison of
the sentence block against finitely many fixed codes, a leaf rewrite, and the day-indexed
constants `r φ n`). The headlines `zeroOut_isLogicalInductor` and `reprice_isLogicalInductor`
(`Transfer.lean`) rest on this and are listed as such.
Source: [[corr-legit-neg-inventory]] 060–061 (E7's "efficiently computable" step, which the source waves through); mandate T3.4 ("isolate it as one named OPEN fact `translateStreamRewriter`")
Kind: OPEN
Fidelity: exact
Hyps: (a) `hr` is the e.c. hypothesis on `r` of E7 (ii) -/
theorem translateStreamRewriter (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) :
    ZeroStreamRewriter ψ Φ N ∧
    ∀ r : Sentence → ℕ → ℚ, (∀ φ ∈ Φ, MachineRatCodes (r φ)) → RepriceStreamRewriter ψ Φ r := by
  sorry

/-! ## (B2) The harmonic inductor pair -/

/-- **OPEN (B2).** Over a computable process with a consistent world at every stage and a fresh atom
`u`, there are two inductors whose prices on `u` are the harmonic paths `1/2 ∓ 1/(2(n+1))` and which
agree within `1/(n+1)` on every sentence. The antecedent of `splice_o1_conjecture_refuted_of_inductors`.
Obstruction: no FAF construction controls a price path on infinitely many days (finite-support
patches move finitely many coordinates, `prescribe_finiteSupport`; a projection with a day-varying
weight `q n = 1/2 ∓ 1/(2(n+1))` would do it on `u` *if* Lemma A held for a weight of finite total
variation — li-projection's OPEN `finiteVariation_projection`, which would also give the agreement
off `u` exactly). Neither proved nor refuted.
Source: [[corr-wf14-inventory]] 048 (R1.5); mandate T1.6(ii)
Kind: OPEN
Fidelity: exact -/
theorem exists_inductor_pair_harmonic_disagreement (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (u : ℕ) (hu : AtomFreeProcess u DP) :
    ∃ P₁ P₂ : History, IsLogicalInductor P₁ DP ∧ IsLogicalInductor P₂ DP ∧
      (∀ n, P₁ n (Formula.atom u) = harmonicLow (Formula.atom u) n (Formula.atom u)) ∧
      (∀ n, P₂ n (Formula.atom u) = harmonicHigh (Formula.atom u) n (Formula.atom u)) ∧
      (∀ n χ, |P₁ n χ - P₂ n χ| ≤ 1 / ((n : ℝ) + 1)) := by
  sorry

/-! ## (B3) Positivity on a refuted sentence -/

/-- **OPEN (B3).** Is there an inductor pricing a stage-refuted sentence positively on every day
from some day on? (063(c); the hypothesis of E7's free horn.) The obstruction is sharper than
summability: for *every* nonnegative e.c. selling schedule `Q`, `Σ_n Q_n · P_n(ψ) < ∞`
(`summable_schedule_mul_price_of_refuted`, `DayIndexed.lean`; li-projection's
`summable_price_neg_of_mem_stage` is `Q ≡ 1`). FAF's `EF` has a sharing `letE`, so price-free e.c.
constants as large as `2^{2^n}` cost `O(n)` tokens; hence a positive price must decay faster than
the reciprocal of every such schedule — a geometric `2^{−n}` is *not* a candidate (the schedule
`Q_n = 2^n` exploits it; its certificate was not built here). Whether any inductor keeps a positive
price decaying that fast is neither proved nor refuted: no FAF construction exhibits one and none
excludes it.
Source: [[corr-legit-neg-inventory]] 063(c); `clusters/E/VERIFY.md` "E7 — narrowed" (no inductor pricing a refuted sentence positively is exhibited); mandate T3.5
Kind: OPEN
Fidelity: exact -/
theorem exists_inductor_pos_on_refuted (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : Sentence) (N : ℕ) (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ) :
    ∃ P : History, IsLogicalInductor P DP ∧ ∀ n, N ≤ n → 0 < P n ψ := by
  sorry

/-! ## (B4)–(B5) Refreezing -/

/-- **OPEN (B4).** Finitely many refreezes: for an inductor `P` and a monotone refreeze map `g`
with `g n ≤ n` and `g n = n` from day `M` on, the stale history `n ↦ P (g n)` (a computable market
by hypothesis) is an inductor. **Not** a finite-support perturbation (each stale day moves infinitely
many coordinates), so FAF's corrected `thm:ifp` does not apply, and FAF's `not_overgeneral_ifp`
shows that *some* overwritten days carry advice. Diagnosis (this package, not proved): a stale copy
of the same inductor's earlier day carries no advice an e.c. trader could not already read from `P`
(the leaf `price φ (g k)` has rank `g k ≤ k`), so the transfer `T ↦ T̃` is a leaf rewrite
`price φ k ↦ price φ (g k)` on the finitely many days `< M` plus dropping those days' trades (a
bounded difference) — the statement is believed **true**, and what is open is its efficiency
certificate, of li-projection F1's kind. Neither proved nor refuted here.
Source: [[bli-soto-b-inventory]] 016 (Soto PDF 15 p. 4, "re-freezing … I think it does (proof coming soon)" — never delivered); mandate T2.7(ii)
Kind: OPEN
Fidelity: variant: the reading of record (`staleHistory`) is ATTRIBUTION-UNVETTED -/
theorem stale_finite_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (g : ℕ → ℕ) (hmono : Monotone g) (hle : ∀ n, g n ≤ n) (M : ℕ)
    (hM : ∀ n, M ≤ n → g n = n) (hcm : ComputableMarket (staleHistory P g)) :
    IsLogicalInductor (staleHistory P g) DP := by
  sorry

/-- **OPEN (B5).** Infinitely many refreezes: for a monotone `g` with `g n ≤ n`, `g → ∞` and
`g n < n` infinitely often, is the stale history an inductor? Neither proved nor refuted. The
natural exploit — on day `n` buy a sentence that entered `DP.D n` after day `g n` at its stale
price — needs an e.c. trader that recognises stage membership; FAF's `ComputableDeductiveProcess`
is not polynomial-time, and a fixed sentence's stale price `P (g n) φ` tends to `1` too once
`g n` passes its entry day, so the exploit needs a *family* of sentences entering at known days
with a price gap before entry. Over `paperDP` the literal stream is a dovetail
(`Construction/Paper/TheoremDP.lean`) whose stage recognisability was not established here.
Source: [[bli-soto-b-inventory]] 016(iii); mandate T2.7(iii)
Kind: OPEN
Fidelity: variant: the reading of record is ATTRIBUTION-UNVETTED -/
theorem stale_infinite_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (g : ℕ → ℕ) (hmono : Monotone g) (hle : ∀ n, g n ≤ n)
    (hinf : Tendsto g atTop atTop) (hfreq : ∃ᶠ n in atTop, g n < n)
    (hcm : ComputableMarket (staleHistory P g)) :
    IsLogicalInductor (staleHistory P g) DP := by
  sorry

/-! ## (B7) 063(b) — 063(a) is settled in `DayIndexed.lean` (repair round 1) -/

/-- **OPEN (B7).** 063(b), made precise: for an inductor and an e.c. sentence family `c`, the price
`P n (c n)` tracks the realized truth value in every completed-theory world iff `c n` is
eventually decided by the completed theory. (⇒) is cheap (two completed worlds disagreeing on `c n`
infinitely often cannot both be tracked); (⇐) needs provability induction on the two eventual
subfamilies. Neither proved nor refuted here.
Source: [[corr-legit-neg-inventory]] 063(b) ("truth-indicator vs price-feature `cdot` come apart in the limit iff the condition is not eventually decided")
Kind: OPEN
Fidelity: variant: "decided" rendered as decided by the completed theory (not by the day's stage, where the statement is false) -/
theorem truth_price_apart_iff_undecided (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (c : ℕ → Sentence) (hcode : MachineSentenceCodes c) :
    (∀ v : PCWorld, v.ConsistentWithTheory DP →
        Tendsto (fun n => P n (c n) - v.payout (c n)) atTop (𝓝 0)) ↔
      ∀ᶠ n in atTop, (∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (c n)) ∨
        (∀ v : PCWorld, v.ConsistentWithTheory DP → ¬ v.Holds (c n)) := by
  sorry

/-! ## (B8) Claim CC-limit -/

/-- **OPEN (B8).** dp-core-110's Claim CC-limit in a **realized-value reading** — ATTRIBUTION-UNVETTED
and, per the round-1 audits, *not the source's*: `wiki/non-responsiveness.md` l. 51 defines "the
enforcer's payoff is `q − c` if `A = a` is realized and exactly `0` otherwise, in every world", so
both `c_t` and `q_t` are market prices (of the refundable contract good and of the conditional) and
the claim is that non-exploitability pins one price to the other along realized rounds; the
refundable contract good has no FAF object, so that claim is neither stated nor refuted here. What
*this* statement says: for every inductor, every realized world and every e.c. condition and
target family, the conditional price's error against the realized value is summable along the
realized-condition rounds. Kept only as a statement of record of the rendering the mandate steered
(T6.1). Its unconditional analogue (`A ≡ ⊤`, `X` a fresh atom, the error of `P_t(u)` against the
realized value) is refuted outright by `ccLimit_realized_refuted`; the instance of this statement
at `A ≡ ⊤` differs from it by the ratio `P_t(u ⋏ ⊤)/P_t(⊤)` and the cap, not identified here.
Source: [[dp-core-inventory]] 110 (`wiki/non-responsiveness.md` l. 51, "logical-induction non-exploitability forces `Σ_{t : A_t = a} |c_t − q_t| < ∞`")
Kind: OPEN
Fidelity: variant: realized-value reading (ATTRIBUTION-UNVETTED; not the source's price-versus-price claim) -/
theorem ccLimit_realizedValue_summable (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (A X : ℕ → Sentence) (hA : MachineSentenceCodes A) (hX : MachineSentenceCodes X)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    Summable (fun t => v.payout (A t) * |conditionedHistory P A t (X t) - v.payout (X t)|) := by
  sorry

/-- **The realized-value reading of Claim CC-limit fails on an undecided sentence (unconditional
analogue)**: over any process with a fresh atom `u` and a consistent world at every stage, for every
inductor the limit price of `u` is interior (li-projection's `limitingBelief_atom_mem_Ioo`), while a
completed-theory world refuting `u` (which exists: `consistentWithTheory_setAtom_iff`) values it at
`0` — so the error `|P_t(u) − 0|` tends to a positive limit and is not summable. This refutes a
*realized-value* reading of the claim, which is not the source's (its `c_t`, `q_t` are both market
prices; see (B8) and findings F9), and it is stated at the unconditional price `P_t(u)`, not at
the `A ≡ ⊤` instance `P_t(u | ⊤) = min (P_t(u ⋏ ⊤)/P_t(⊤)) 1` of `ccLimit_realizedValue_summable`;
the two agree only up to the ratio and the cap, not identified here. Ledger status `proved`, not
`refuted`: no claim the source makes is refuted by it.
Source: [[dp-core-inventory]] 110; mandate T6.1 ("the summability form is stronger than anything the criterion gives")
Kind: P
Fidelity: variant: the unconditional analogue of a realized-value reading that is not the source's
Hyps: (a) -/
theorem ccLimit_realized_refuted (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP) :
    ∃ v : PCWorld, v.ConsistentWithTheory DP ∧
      ¬ Summable (fun t => |P t (Formula.atom u) - v.payout (Formula.atom u)|) := by
  obtain ⟨v₀, hv₀⟩ := DP.exists_consistentWithTheory hcons
  refine ⟨setAtom v₀ u false, (consistentWithTheory_setAtom_iff hu v₀ false).mp hv₀, ?_⟩
  intro hsum
  have hpay : (setAtom v₀ u false).payout (Formula.atom u) = 0 := by
    rw [PCWorld.payout, if_neg (setAtom_not_holds_atom_false v₀ u)]
  have hL := limitingBelief_atom_mem_Ioo P DP hcons u hu
  have hT := lic_limitingBelief_tendsto P DP hcons (Formula.atom u)
  have h0 := hsum.tendsto_atTop_zero
  simp only [hpay, sub_zero] at h0
  have hT' : Tendsto (fun t => |P t (Formula.atom u)|) atTop (𝓝 |limitingBelief P (Formula.atom u)|) :=
    hT.abs
  have := tendsto_nhds_unique h0 hT'
  rw [abs_of_pos hL.1] at this
  exact hL.1.ne this

/-! ## (B9) Summable disagreement -/

/-- **OPEN (B9).** R1.5's replacement conjecture: two inductors over `DP` whose prices disagree
summably along every e.c. sentence sequence have every computable splice an inductor. Diagnosis
(findings): (i) an e.c. trader's coefficients read prices (`EF.price`), so its trades against the
splice differ from its trades against `P₁` and the two net-worth streams are not
`Σ q_m (S_m − P₁_m)`; (ii) even for price-free coefficients, e.c. quantities are not bounded (a
shared `letE` squares a value with constant cost), so summable disagreement does not bound
`Σ |q_m| |S_m − P₁_m|`. The one trader family for which the conjecture *is* proved is the parity
trader (`parityTrader_not_exploits_paritySplice_of_summable`, `Splice.lean`). Neither proved nor
refuted.
Source: [[corr-wf14-inventory]] 048 (R1.5, "a *summable* disagreement along every e.c. sequence is the plausible sufficient condition [conjectured, ~0.6]"); mandate Extension
Kind: OPEN
Fidelity: exact -/
theorem splice_summable_conjecture (P₁ P₂ : History) (DP : DeductiveProcess)
    [IsLogicalInductor P₁ DP] [IsLogicalInductor P₂ DP]
    (hsum : ∀ φ : ℕ → Sentence, MachineSentenceCodes φ →
      Summable (fun n => |P₁ n (φ n) - P₂ n (φ n)|))
    (g : ℕ → Bool) (hg : Computable g) :
    IsLogicalInductor (splice P₁ P₂ g) DP := by
  sorry

end Cleanroom.Li.LiSpliceCondition
