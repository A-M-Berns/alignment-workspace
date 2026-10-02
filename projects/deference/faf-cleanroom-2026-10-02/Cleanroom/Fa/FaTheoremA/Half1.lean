import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Fa.FaTheoremA.Analysis
import Cleanroom.Found.LiQuoteLane.CrossQuote
import Cleanroom.Found.LiAsympCalc.LimitPoint
import LogicalInduction.Construction.Statistics.HistoricalMaturity

/-!
# `fa-theorem-a` · Half1: the quote is honest on any gate `A` can recognize (T3, T4)

**Half 1** of the Eisenstat-slide factoring ([[delay-program]] §2): on any gate `A` *itself* can
recognize, `A`'s quotes are limit-point unbiased for the realized `Y_n = 𝔼^H_{f n}(X_n)`. The
engine is FAF's corrected Recurring Unbiasedness for expectations,
`LUVCombination.BoundedSequence.recurringunbiasednessexp` (LI 4.8.15 with the erratum PE2: no deferral
function, no support clause), applied in `A`'s market to the quote family `⌜Y⌝` with the inputs
that `li-quote-lane`'s `CrossQuotePackage` supplies (`boundedSequence`, `worldValued`,
`determinedViaTheory`) and the gate's generability certificate (T2, `Defs.lean`).

* `quote_unbiased`: the engine on *any* generable divergent weighting of `A`'s market.
* `half1` (T3, headline): the engine on the ramp `Ind_δ(a_n > t)` of `A`'s own quote — the
  statement of [[faithful-acceleration-result]] §3 and [[route-recurring-ccee]] §4 (Theorem T2
  with the triple (BLCS-A) = `pkg.boundedSequence`, (DET-A) = `pkg.determinedViaTheory`,
  (DIV) = `hdiv`), and its dual `half1_below`.
* `half1_realized_frequently_ge` / `_le`: "on the days `A` advertises above `t`, the human's
  realized credence averages at least `t − o(1)` along a subsequence" (the gridless companion of
  [[fa-positive-results-corrected-v2]] §5.7 is this statement verbatim).
* `engine_no_persistent_bias_general` / `engine_no_persistent_bias` (T4, headline): the
  gate-generability engine — no generable divergent weighting can sit on persistently one-signed,
  bounded-away error — composed from the FAF endpoint and `li-asymp-calc`'s wash-out.

**Conclusion is a limit point along a subsequence (`HasLimitPoint … 0`), not a limit** — the
corpus once misread 4.8.15 as a full limit (root-fa-024 Flags; [[delay-program]] T1). The full
limit is Lemma P (`LemmaP.lean`), and only on a day-set where `Y_n` converges.

Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory
determines `H`'s run outputs, a form of `A` "seeing" `H` logically rather than through prices
(root-fa-027); at the mirror witness it is (a) at variant fidelity (ledger-recorded). Every
statement over `CrossQuotePackage` carries `hworldA` explicitly: the package has no world.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. The engine on an arbitrary generable divergent weighting -/

/-- **Half 1 on an arbitrary gate.** For any logical inductor `A` over `DPA`, any quote package
tying `⌜Y⌝` to `H`'s realized expectations, and any `PGenerableWeighting` `W` of `A`'s market
that is divergent in `A`'s realized prices, `0` is a limit point of the `W`-weighted bias of the
quote `a_n = 𝔼^A_n(Y_n)` against the realized `Y_n = 𝔼^H_{f n}(X_n)`. This is FAF's
`LUVCombination.BoundedSequence.recurringunbiasednessexp` with the market rewritten from
`(ofLUV (Y i)).expect A i` to `(Y i).expect A i`.
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory
determines `H`'s run outputs, a form of `A` "seeing" `H` logically rather than through prices
(root-fa-027); at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Conclusion is a limit point along a subsequence (`HasLimitPoint … 0`), not a limit.
Source: [[delay-program]] §2 lines 60–66 (Half 1 "is exactly Recurring Unbiasedness (4.8.15, corrected)"); root-fa-024; FAF `thm:recurringunbiasednessexp`
Kind: L
Fidelity: exact
Hyps: (a) `hworldA` (FAF's disclosed world boundary), `hW`, `hdiv`; (c) `pkg.reflected` as above. -/
theorem quote_unbiased {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W A) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote A) (quoteSeq Y A) (realized H f X)) 0 := by
  have h := LUVCombination.BoundedSequence.recurringunbiasednessexp (pkg.boundedSequence A) pkg.worldValued
    (pkg.determinedViaTheory A) hW hdiv hworldA
  simpa only [ofLUV_expect] using h

/-! ## B. T3: Half 1 on the ramp of `A`'s own quote -/

/-- **T3 (headline). Half 1: the quote is honest on the gate `Ind_δ(a_n > t)` of `A`'s own
quote.** For `[IsLogicalInductor A DPA]`, a quote package `pkg`, every stage of `DPA`
satisfiable, rational `t δ`, and the gate divergent in `A`'s realized prices (`hdiv`, the (DIV) of
[[route-recurring-ccee]] §4): `0` is a limit point of the gate-weighted average of
`a_n − Y_n`. The triple of vq-wiki-2-013 is (BLCS-A) = `pkg.boundedSequence A` (from
`quote_codes` alone), (DET-A) = `pkg.determinedViaTheory A` (from `reflected`), (DIV) = `hdiv`.
The gate's legality is T2 (`quoteRampAbove_pgenerable`): "a market is never stale to itself".
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory
determines `H`'s run outputs, a form of `A` "seeing" `H` logically rather than through prices
(root-fa-027); at the mirror witness it is (a) at variant fidelity (ledger-recorded).
**Conclusion is a limit point along a subsequence (`HasLimitPoint … 0`), not a limit.** `hdiv` is a
genuine hypothesis about `A`'s realized prices (for `δ < 0` the ramp is reversed, and at `δ = 0`
it is identically `0` — Lean's `1/0 = 0` — so `hdiv` is unsatisfiable and the theorem vacuous
there, `not_divergent_zero_width`; the semantic reading of the gate needs `0 < δ`,
`quoteRampAbove_pos_iff`).
Source: [[faithful-acceleration-result]] §3 (root-fa-024, vq-wiki-030); [[route-recurring-ccee]] §4 Theorem T2 (vq-wiki-2-013); [[delay-program]] §2 lines 60–66
Kind: C
Fidelity: exact
Hyps: (a) `hworldA`, `hdiv`; (c) `pkg.reflected` as above. -/
theorem half1 {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (t δ : ℚ)
    (hdiv : DivergentWeighting (quoteRampAbove Y t δ) A) :
    HasLimitPoint
      (weightedBias (fun i => (quoteRampAbove Y t δ i).denote A) (quoteSeq Y A)
        (realized H f X)) 0 :=
  quote_unbiased pkg hworldA (quoteRampAbove_pgenerable Y pkg.quote_codes t δ) hdiv

/-- **T3, the dual gate** `Ind_δ(a_n < t)` (vq-wiki-2-013: "every statement below dualizes").
Scope: one-way; conclusion is a limit point, not a limit; the (c) is `pkg.reflected`.
Source: [[route-recurring-ccee]] §4 (vq-wiki-2-013, "Dual gate")
Kind: C
Fidelity: exact
Hyps: (a) `hworldA`, `hdiv`; (c) `pkg.reflected`. -/
theorem half1_below {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (t δ : ℚ)
    (hdiv : DivergentWeighting (quoteRampBelow Y t δ) A) :
    HasLimitPoint
      (weightedBias (fun i => (quoteRampBelow Y t δ i).denote A) (quoteSeq Y A)
        (realized H f X)) 0 :=
  quote_unbiased pkg hworldA (quoteRampBelow_pgenerable Y pkg.quote_codes t δ) hdiv

/-- **T3, corollary (i):** on the days `A` advertises above `t`, the human's realized credence
averages at least `t − ε` infinitely often, for every `ε > 0` — "along a subsequence". Uses
`0 < u_i → t < a_i` (no false positives), so the gate-weighted average of `a` is `≥ t` wherever the
mass is positive, and `hasLimitPoint_zero_iff`. The weighted average is FAF's `weightedAverage`
(`0` at zero mass), harmless here because `hdiv` makes the mass eventually positive. The gridless
companion of [[fa-positive-results-corrected-v2]] §5.7 is this statement verbatim.
Scope: one-way; the (c) is `pkg.reflected`.
Source: [[faithful-acceleration-result]] §3 ("on the days `A` advertises above `t`, the human's realized future credence averages at least `t − o(1)` along a subsequence"); [[route-recurring-ccee]] §4; [[fa-positive-results-corrected-v2]] §5.7
Kind: L
Fidelity: exact
Hyps: (a) `hworldA`, `hdiv`, `hδ`; (c) `pkg.reflected`. -/
theorem half1_realized_frequently_ge {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {t δ : ℚ} (hδ : 0 < δ)
    (hdiv : DivergentWeighting (quoteRampAbove Y t δ) A) :
    ∀ ε > 0, ∃ᶠ n in atTop, (t : ℝ) - ε ≤
      weightedAverage (fun i => (quoteRampAbove Y t δ i).denote A) (realized H f X) n := by
  intro ε hε
  have hlp := hasLimitPoint_zero_iff.1 (half1 pkg hworldA t δ hdiv) ε hε
  have hpos := hdiv.eventually_prefixSum_pos
  refine (hlp.and_eventually hpos).mono ?_
  rintro n ⟨hn, hden⟩
  have hge : (t : ℝ) ≤ weightedAverage (fun i => (quoteRampAbove Y t δ i).denote A)
      (quoteSeq Y A) n :=
    le_weightedAverage_of_support (fun i => (hdiv.1 i).1)
      (fun i hi => ((quoteRampAbove_pos_iff Y hδ A i).1 hi).le) hden
  rw [weightedBias_eq_market_sub_truth _ _ _ hden.ne', abs_sub_lt_iff] at hn
  linarith [hn.1]

/-- **T3, corollary (ii):** on the days `A` advertises below `t`, the human's realized credence
averages at most `t + ε` infinitely often, for every `ε > 0`.
Scope: one-way; the (c) is `pkg.reflected`.
Source: [[route-recurring-ccee]] §4 (vq-wiki-2-013: "with `u⁻_n` one gets `Ȳ^{u⁻}_n ≤ t + o(1)` along an infinite set")
Kind: L
Fidelity: exact
Hyps: (a) `hworldA`, `hdiv`, `hδ`; (c) `pkg.reflected`. -/
theorem half1_realized_frequently_le {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {t δ : ℚ} (hδ : 0 < δ)
    (hdiv : DivergentWeighting (quoteRampBelow Y t δ) A) :
    ∀ ε > 0, ∃ᶠ n in atTop,
      weightedAverage (fun i => (quoteRampBelow Y t δ i).denote A) (realized H f X) n ≤
        (t : ℝ) + ε := by
  intro ε hε
  have hlp := hasLimitPoint_zero_iff.1 (half1_below pkg hworldA t δ hdiv) ε hε
  have hpos := hdiv.eventually_prefixSum_pos
  refine (hlp.and_eventually hpos).mono ?_
  rintro n ⟨hn, hden⟩
  have hle : weightedAverage (fun i => (quoteRampBelow Y t δ i).denote A)
      (quoteSeq Y A) n ≤ (t : ℝ) :=
    weightedAverage_le_of_support (fun i => (hdiv.1 i).1)
      (fun i hi => ((quoteRampBelow_pos_iff Y hδ A i).1 hi).le) hden
  rw [weightedBias_eq_market_sub_truth _ _ _ hden.ne', abs_sub_lt_iff] at hn
  linarith [hn.2]

/-! ## C. T4: the gate-generability engine over FAF -/

/-- **T4 (headline, general form — root-fa-025's "M").** For a logical inductor `P` over `DP`,
a bounded `ℙ`-generable LUV-combination sequence `As` (FAF's `BoundedSequence`) whose completed
worlds value it (`WorldValued`) at `truth` (`DeterminedViaTheory`), and a `PGenerableWeighting`
`W`: it is not the case that `W` is divergent in `P`'s prices *and* from some day on every
positive-weight day has `𝔼^P_n(As n) − truth n ≥ c` for a fixed `c > 0`. Composition: FAF's
`recurringunbiasednessexp` gives the limit point, `li-asymp-calc`'s wash-out
(`DivergentWeighting.not_hasLimitPoint_weightedBias`) refutes it. **Not a squeeze:** neither
hypothesis mentions `weightedBias` or `HasLimitPoint`. No deferral function appears anywhere
(PE2, `Errata.lean`). root-fa-025's converse — a gate that is *not* asymptotically
`P`-generable can carry persistent bias — is OPEN and needs a definition of "asymptotically
`P`-generable"; not attempted here.
Source: root-fa-025 ("for LI `A`, determined bounded `B`, generable divergent `W`: `¬(∃ c > 0, ∀^∞ i, W_i > 0 → 𝔼^A_i(B_i) − Val(B_i) ≥ c)`"); [[delay-program]] §6 T1
Kind: C
Fidelity: exact
Hyps: (a) `hworld` (FAF's disclosed world boundary); `h`, `hvalued`, `hdet` are FAF's `thm:recurringunbiasednessexp` premises, discharged for the quote by `CrossQuotePackage` in the specialization below. -/
theorem engine_no_persistent_bias_general {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {As : ℕ → LUVCombination}
    (h : LUVCombination.BoundedSequence As P) (hvalued : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) :
    ¬ (DivergentWeighting W P ∧ ∃ c > 0, ∃ N, ∀ n ≥ N,
        0 < (W n).denote P → c ≤ (As n).expect P n - truth n) := by
  rintro ⟨hdiv, c, hc, N, hN⟩
  exact DivergentWeighting.not_hasLimitPoint_weightedBias hdiv hc N hN
    (LUVCombination.BoundedSequence.recurringunbiasednessexp h hvalued hdet hW hdiv hworld)

/-- **T4, general form, the other sign** (`𝔼^P_n(As n) − truth n ≤ −c` on the support).
Source: root-fa-025; [[delay-program]] §6 T1
Kind: C
Fidelity: exact
Hyps: (a) as `engine_no_persistent_bias_general`. -/
theorem engine_no_persistent_bias_general_neg {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {As : ℕ → LUVCombination}
    (h : LUVCombination.BoundedSequence As P) (hvalued : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) :
    ¬ (DivergentWeighting W P ∧ ∃ c > 0, ∃ N, ∀ n ≥ N,
        0 < (W n).denote P → (As n).expect P n - truth n ≤ -c) := by
  rintro ⟨hdiv, c, hc, N, hN⟩
  exact DivergentWeighting.not_hasLimitPoint_weightedBias_neg hdiv hc N hN
    (LUVCombination.BoundedSequence.recurringunbiasednessexp h hvalued hdet hW hdiv hworld)

/-- **T4 (headline). The gate-generability engine on the quote.** In the context of T3, for any
`PGenerableWeighting` `W` of `A`'s market: `W` cannot be divergent in `A`'s prices while, from
some day on, every positive-weight day has `a_n − Y_n ≥ c` for a fixed `c > 0`. This is
`engine_no_persistent_bias_general` at the quote family, with `CrossQuotePackage` discharging
FAF's three premises (`boundedSequence` from `quote_codes`; `worldValued`,
`determinedViaTheory` from `reflected`).
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory
determines `H`'s run outputs, a form of `A` "seeing" `H` logically rather than through prices
(root-fa-027); at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Conclusion is the negation of a limit-point statement's hypotheses (via `HasLimitPoint … 0`,
a limit point along a subsequence, not a limit).
Source: root-fa-025; [[delay-program]] §6 T1
Kind: C
Fidelity: exact
Hyps: (a) `hworldA`, `hW`; (c) `pkg.reflected` as above. -/
theorem engine_no_persistent_bias {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) :
    ¬ (DivergentWeighting W A ∧ ∃ c > 0, ∃ N, ∀ n ≥ N,
        0 < (W n).denote A → c ≤ quoteSeq Y A n - realized H f X n) := by
  rintro ⟨hdiv, c, hc, N, hN⟩
  exact DivergentWeighting.not_hasLimitPoint_weightedBias hdiv hc N hN (quote_unbiased pkg hworldA hW hdiv)

/-- **T4, the other sign** on the quote (`a_n − Y_n ≤ −c` on the support).
Scope: one-way; the (c) is `pkg.reflected`.
Source: root-fa-025; [[delay-program]] §6 T1
Kind: C
Fidelity: exact
Hyps: (a) `hworldA`, `hW`; (c) `pkg.reflected`. -/
theorem engine_no_persistent_bias_neg {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) :
    ¬ (DivergentWeighting W A ∧ ∃ c > 0, ∃ N, ∀ n ≥ N,
        0 < (W n).denote A → quoteSeq Y A n - realized H f X n ≤ -c) := by
  rintro ⟨hdiv, c, hc, N, hN⟩
  exact DivergentWeighting.not_hasLimitPoint_weightedBias_neg hdiv hc N hN (quote_unbiased pkg hworldA hW hdiv)

/-! ## The junk value `δ = 0` of the gate's width (record) -/

/-- At width `0` the upper gate denotes `0` on every day (Lean's `1/0 = 0` inside FAF's
`ctsInd`): it is not "reversed", it is identically zero.
Source: audit r1 (adversarial) N5, probe `DeltaZeroGate.lean`; none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quoteRampAbove_zero_width_denote (Y : ℕ → LUV) (t : ℚ) (A : History) (n : ℕ) :
    (quoteRampAbove Y t 0 n).denote A = 0 := by
  unfold quoteRampAbove ctsIndFeature
  simp [clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const, Pi.mul_apply,
    Pi.add_apply]

/-- Hence `half1`'s `hdiv` is unsatisfiable at `δ = 0`: the headline is vacuous at that one
width (and only there, since `half1` quantifies over every rational width).
Source: audit r1 (adversarial) N5, probe `DeltaZeroGate.lean`; none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem not_divergent_zero_width (Y : ℕ → LUV) (t : ℚ) (A : History) :
    ¬ DivergentWeighting (quoteRampAbove Y t 0) A := by
  rintro ⟨-, hdiv⟩
  have hzero : prefixSum (fun n => (quoteRampAbove Y t 0 n).denote A) = fun _ => 0 := by
    funext n
    simp [prefixSum, quoteRampAbove_zero_width_denote]
  rw [hzero] at hdiv
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hdiv) 1
  have := hN N le_rfl
  norm_num at this

end Cleanroom.Fa.FaTheoremA
