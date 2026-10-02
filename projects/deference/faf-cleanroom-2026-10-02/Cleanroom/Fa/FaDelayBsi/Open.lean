import Cleanroom.Fa.FaDelayBsi.Deficit
import Cleanroom.Fa.FaDelayBsi.SelfInstance

/-!
# `fa-delay-bsi` · Open: the three open statements

Precise Lean statements of the package's deliberately open claims, each with `sorry`, listed in
`run/wp/fa-delay-bsi/fa-delay-bsi-open.txt`. Nothing else in the package rests on them.

* **T4** `deficit_bound_open`: the frozen-term-free deficit bound over a pair of inductors. Needs
  the v3 trader (`fa-forcing-trader`'s Kelly engine, outside this package's import closure).
* **T7** `factoring_of_determined_gate_open`: the factoring step at a *non-convergent* determined
  rational gate — needs a varying-coefficient `LUVCombinationSyntax` (FAF's
  `MachineSpliceStream.serialize_const_write` supplies the coefficient stream; not assembled).
* **T6** `deckTT_self_luv_open`: the LUV-family form of the self-trust instance — FAF's `thm:st`
  is for sentence families through their indicators; the exact product LUV for a general e.c.
  source is what FAF's `dd:mesh` disclosure says its machinery does not build.
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Propositional
open Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Filter Topology Finset

/-- **T4 (OPEN). The deficit bound: violations on a within-block window-disjoint schedule are
bounded by `O(1) + (2/ε)` times the human's within-freeze update mass — no frozen term.** Stated
over a one-way pair (`H` reads `A`'s table through the ledger; `hquoted`: the ledger publishes the
quote's threshold prices, so `H` sees `𝔼^A_n(Y_n)`), a cross-quote package (`A`'s theory
determines `H`'s realized within-block expectation of the current question), and an `A`-side
frozen ledger (`Z n` determined in `A`'s theory at `H`'s last-freeze credence — BSI's "the
forecaster's weightings may use the human's prices through the last freeze"), on a schedule `d`
with lookahead `f` that is window-disjoint and closes **by the block boundary** (`ClosesByBoundary`,
the inclusive clause: BSI's own horizon `T_{k(d)+1}` is an instance, `closesByBoundary_of_horizon_T`;
the strict `ClosesWithinBlocks` implies it, `ClosesWithinBlocks.toByBoundary` — audit r1
adversarial B2 found the earlier strict hypothesis excluded BSI's horizon). **Open: needs the v3 trader**
— `A`'s recurring unbiasedness on the frozen gate (`A`-generable: `quoteRampAbove` times the ramp
of `Z`'s expectation feature) forces realized end-of-window credences to average `≥ t − o(1)` on
fired days, and a human-side Kelly trader buying the current question at its live price on fired
current-violation days and selling at the horizon exploits `H` unless the fired weight
(`frozenWeight · 𝟙[live < t − ε]`, the first sum of `deficit_finite_sum_live`) is finite; declined
days are dominated by displacement (T2). That machinery is `fa-forcing-trader`'s; discharge at
consolidation. Not the split minus a term: T3 (`frozen_not_finite_witness`) refutes that route.
Scope: **two-way** (`partial: over the OPEN pair`): `pkg.reflected` (A reads H), the ledger (H reads A), and `hZdet` (A reads H's frozen prices) are all (c).
Source: [[delay-program]] §6 T6 lines 252–260 (root-fa-029 (Bound)); BSI §5 line 100 (lean-deference-054 "surviving form"); [[delay-and-visibility]] §5 (vq-wiki-039 (b), ~0.75 in source)
Kind: OPEN
Fidelity: exact (the surviving form, constant `C = 2`, with the hypothesis package named; the schedule clause inclusive, so BSI's horizon is an instance)
Hyps: (c) `pkg.reflected`, `pair` (ledger determinacy), `hZdet`; (a) the rest -/
theorem deficit_bound_open (pair : OneWayPair) (S : FreezeSchedule) (X : ℕ → LUV)
    (f d : DeferralFunction) (hclose : ClosesByBoundary S f d)
    (hwd : StrictMono d.f ∧ ∀ k, f.f (d.f k) < d.f (k + 1))
    (Y : ℕ → LUV) (pkg : CrossQuotePackage pair.H pair.DPA f (fun n => X (S.blockOf n)) Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (pair.DPA.D n))
    (hquoted : ∀ n i, i ≤ n → pair.quoted i n = (Y n).gt ((i : ℚ) / ((n : ℚ) + 1)))
    (Z : ℕ → LUV) (hZ : LUV.MachineThresholdCodeSeq Z)
    (hZdet : ∀ n, LUV.DeterminedVia (Z n) pair.DPA (frozenCredence S pair.H X n))
    {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ K : ℕ,
      ∑ k ∈ range K, violWeight t ε δ (quoteSeq Y pair.A (d.f k)) (liveCredence S pair.H X (d.f k))
        ≤ C + (2 / (ε : ℝ)) * ∑ k ∈ range K, withinFreezeUpdate S pair.H X (d.f k) := by
  sorry

/-- **T3 (ii) at the inductor level (OPEN). Is BSI Theorem C's second display false for some pair
of logical inductors?** For every admissible triple (`t + δ ≤ 1`, `0 ≤ t − ε/2 − δ`, BSI's
constants included): a one-way pair, a freeze schedule, a block-indexed question family `X`, a
window-disjoint schedule `d` with lookahead `f` closing by the boundary, and a quote family `Y`
of `H`'s realized credence (`CrossQuotePackage`, published through the ledger — `hquoted`), such
that the frozen-gated weight `Ind_δ(𝔼^A_{d_k}(Y_{d_k}) > t)·Ind_δ(𝔼^H_{T_k}(X_k) < t − ε/2)` is
**not summable** along the schedule. The sequence-level fact that the per-day arithmetic cannot
force summability is `frozen_not_finite_witness` (W1, N−: constant sequences); this statement is
what BSI's "`∑_k w^{frozen}_{d_k} < ∞` in any block-stale pair" (§5 line 96) actually denies, and
what the sources' "concrete refutation" ([[delay-program]] T6, [[delay-and-visibility]] §5)
would need to exhibit. **Why it is open rather than proved:** the sources' scenario ("frozen
credence `≈ 0`, live credence jumps to `≈ 1` mid-block, quote `≈ 1`, forecasts perfect") is not
realizable on a learnable family — an all-true e.c. family is a family of theorems of `H`'s
theory, and provability induction lifts `H`'s *frozen* credence `𝔼^H_{T_k}(X_k) → 1` too, so the
frozen gate dies (findings F3); a realizable scenario needs a family whose truth `H` cannot
anticipate at the freeze but `A`'s process decides before `H`'s does (`A` ahead of `H`, quoting
`≈ 1` on exactly the true blocks, infinitely many of them at density below `t − ε/2 − δ`) — a
pseudorandom-to-`H` family of `li-pseudorandom`'s kind, whose inductor certificate rests on that
package's OPEN `starDP_computable`. The minimal refutation of BSI's display is this statement at
one admissible triple; it is stated for all because the sources' scenario, if realizable, is
constant-independent. (Audit r1 fidelity B2 / adversarial B1: the display's inductor-level
status is open, not `refuted`.)
Scope: **two-way** (`partial: over the OPEN pair`): `pkg.reflected` (A reads H) and the ledger (H reads A) are (c); existential, so not vacuous.
Source: BSI §5 line 96 (lean-deference-054); [[delay-program]] §6 T6 line 254 (root-fa-029 (Refutation)); [[delay-and-visibility]] §5 (vq-wiki-039 (a)); [[fa-delay-bsi-mandate]] T3 (iii)
Kind: OPEN
Fidelity: exact (the display's negation, over the package the display is stated for; A-side block-staleness is `OneWayPair`'s — `A` sees none of `H`'s prices — which is stricter than BSI's "through the last freeze")
Hyps: (a) `hε`, `hδ`, `ht1`, `ht0`; (c) inside the existential: `pkg.reflected`, the ledger determinacy -/
theorem frozen_divergent_pair_open {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (ht1 : t + δ ≤ 1)
    (ht0 : 0 ≤ t - ε / 2 - δ) :
    ∃ (pair : OneWayPair) (S : FreezeSchedule) (X : ℕ → LUV) (f d : DeferralFunction)
      (Y : ℕ → LUV),
      ClosesByBoundary S f d ∧ (StrictMono d.f ∧ ∀ k, f.f (d.f k) < d.f (k + 1)) ∧
      CrossQuotePackage pair.H pair.DPA f (fun n => X (S.blockOf n)) Y ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (pair.DPA.D n)) ∧
      (∀ n i, i ≤ n → pair.quoted i n = (Y n).gt ((i : ℚ) / ((n : ℚ) + 1))) ∧
      ¬ Summable (fun k => frozenWeight t ε δ (quoteSeq Y pair.A (d.f k))
        (frozenCredence S pair.H X (d.f k))) := by
  sorry

/-- **T7 (OPEN). The factoring step at a determined, non-convergent rational gate.** For an e.c.
valued family `V`, a machine-codeable rational gate `q n ∈ [0,1]` (world-independent, as the
ramp of a ledger value is), and an e.c. family `A` with `A n` valued at `x · q n` whenever `V n`
is valued at `x`: `𝔼_n(A n) ≈ₙ q n · 𝔼_n(V n)`. The convergent-gate case is
`factoring_of_convergent_gate`. Open only for lack of plumbing: the combination `A n − q n · V n`
with the day-varying rational coefficient needs a `LUVCombinationSyntax` whose
`coefficient_poly` is FAF's `MachineSpliceStream.serialize_const_write hq.toMachineDigits`
(the pattern of `ctsIndFeature_generated`), after which `def-self-trust`'s eventual
`thm:expprovind` faces close it at value `0`.
Scope: one market; the gate's determinacy is the "H reads A" direction where it is used.
Source: [[delay-program]] §6 T7 line 264 (root-fa-033); [[fa-delay-bsi-mandate]] T7 (`factoring_of_determined`)
Kind: OPEN
Fidelity: exact (the note's step at a determined gate)
Hyps: (a) `hV`, `hworld`, `hq01`, `hq`, `hA`; (c) per FAF `hval`; `hArefl` the reflecting field -/
theorem factoring_of_determined_gate_open {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] (V : ℕ → LUV) (hV : LUV.MachineThresholdCodeSeq V)
    (hval : ∀ n (w : PCWorld), w.ConsistentWithTheory DPH → ∃ x : ℝ, w.ValuesAt (V n) x)
    (hworld : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (q : ℕ → ℚ) (hq01 : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (hq : MachineRatCodes q)
    (A : ℕ → LUV) (hA : LUV.MachineThresholdCodeSeq A)
    (hArefl : ∀ n (w : PCWorld), w.ConsistentWithTheory DPH →
      ∀ x, w.ValuesAt (V n) x → w.ValuesAt (A n) (x * q n)) :
    (fun n => (A n).expect H n) ≈ₙ fun n => (q n : ℝ) * (V n).expect H n := by
  sorry

section Paper

variable (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] [𝗜𝚺₁ ⪯ T]

/-- **T6 (OPEN). The LUV-family form of the self-trust instance.** Over the paper market, for
every e.c. valued LUV family `V`, every constant threshold `v ∈ [0,1]` and width `δ > 0`, there is
a reflecting pair `(A, B)` for the expert `n ↦ 𝔼^H_{f n}(V_n)` and the deck inequality holds for
it. The sentence case (`V n = 𝟙(φ n)`, expert the future *price*) is `deckTT_self_paper` with
`deckTT_self_paper_inhabited`. Open: FAF's `thm:st` is for sentence families; an *exact* product
LUV `V_n · Ind_δ(…)` for a general e.c. source is what FAF's `dd:mesh` disclosure
(`ConditionalExpectationQuote`) says its machinery realizes only to within a vanishing slack,
and the deck's statement quantifies over LUV sequences. Stated with the existential so that it
is not vacuous where no exact pair exists.
Scope: same market; expert = own future expectation; LUV families.
Source: [[delay-program]] §4 line 182 (root-fa-036: "quantified over e.c. LUV sequences … the sentence-vs-LUV gap is the work"); [[fa-delay-bsi-mandate]] T6 (`deckTT_self_luv`)
Kind: OPEN
Fidelity: exact (the deck's LUV form; constant thresholds)
Hyps: (a) `hV`; (c) per FAF `hval` -/
theorem deckTT_self_luv_open (f : DeferralFunction) (V : ℕ → LUV)
    (hV : LUV.MachineThresholdCodeSeq V)
    (hval : ∀ n (w : PCWorld), w.ConsistentWithTheory (paperDP T) → ∃ x : ℝ, w.ValuesAt (V n) x)
    (v δ : ℚ) (hv : 0 ≤ v ∧ v ≤ 1) (hδ : 0 < δ) :
    ∃ A B : ℕ → LUV,
      DeckTrustQuote (liaHistory (paperDP T)) (paperDP T)
        (fun n => (V n).expect (liaHistory (paperDP T)) (f.f n)) V (fun _ => v) (fun _ => δ) A B ∧
      AsympGE (fun n => (A n).expect (liaHistory (paperDP T)) n)
        (fun n => (v : ℝ) * (B n).expect (liaHistory (paperDP T)) n) := by
  sorry

end Paper

end Cleanroom.Fa.FaDelayBsi
