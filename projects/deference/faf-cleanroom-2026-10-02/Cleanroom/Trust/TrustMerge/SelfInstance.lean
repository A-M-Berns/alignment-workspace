import Cleanroom.Trust.TrustMerge.Defs
import Cleanroom.Found.DefLattice.Witness
import Cleanroom.Deference.DefSelfTrust.SelfInstances
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Construction.Statistics.FeedbackTruth

/-!
# `trust-merge` · SelfInstance: the self instance is free (T2), and the averaged engine

**T2 (trust-lab-002: "for `M = N`'s own day-`f(n)` self it is `ccee`").** Over FAF's paper
inductor `liaHistory (paperDP T)` the self-expert `Expert.self P DP f` is LUV-Total-Trusted at the
per-day grade outright: clause (i) is FAF's deferred-expectation quote
`paperDeferredExpectationQuoteCode` (e.c. by `.poly`, reflecting by
`deferredExpectationQuote_reflected`), clause (ii) is `def-self-trust`'s `selfCondTower`
(`thm:ccee` at every `CondQuote`). **Grade N− on its own**: one market, the expert is the
novice's own future self. The N+ for T1 (two distinct markets) is T3 (`MirrorFeedback.lean`).

**The averaged engine** (`quoteUnbiased_ofComputation`) is stated for *any* inductor `P` over any
`DP` and any expert `E` whose estimate an e.c. quote `Y` reflects: it is FAF's
`luv_wubexp_ofComputation` (`thm:wubexp`) at the singleton combinations `0 + 1·Y_n`, with the
determinacy input `DeterminedViaTheory` read off `Reflects` through `li-asymp-calc`'s bridge. Its
one undischarged input is FAF's deadline program `C : FeedbackTruthComputation (…) E.f` — the
paper's "the value is computable in `O(f(k+1))`" clause, a **time** hypothesis on the expert's
estimate, not a determinacy hypothesis (the red-team's distinction, trust-lab-2-007). **What `C`
asks, read off FAF's fields** (audit r1 B2; `MirrorFeedback.lean`'s `deadline_value_at` /
`ledger_truth_double_deferral` / `deadline_le_realized`): on the input `⟨k, f (k+1)⟩`, within the
`MachineDigits` budget, emit the mesh truth of the quote at day `f k`. For a quote of a day-`f n`
expectation that truth is **doubly deferred** — `𝔼^P_{f (f k)}(X_{f k})` for the self instance
(`selfTrust_avg_ofComputation`), `𝔼^H_{f (f k)}(X_{f k})` for the mirror instance — and
`f (k+1) ≤ f (f k)` for every strictly increasing `f`, with equality only at `f = succ`: the
realized day never precedes the deadline and recedes from it as `f` grows. So `C` is inhabitable
only if the expert's day-`m` expectations are computable in time polynomial in `m` along those
days — a property of the **expert's running time** that no choice of `f` relaxes. The agenda's
"fast enough `f`" and the mandate's "a schedule with `f (k+1) ≥ τ(f k)` does it" describe a
*different* hypothesis (the model's `O(f(t+1))` at `t = f k` is `O(f(f k + 1))`, which is not the
paper's `O(f(k+1))`; F-C, F-A′). FAF has no time bound on `liaHistory` and no clocked universal
constructor for `FeedbackTruthComputation` (its three witnesses are a constant, a parity test and
a cast — `ordinaryFeedbackTruthComputation`, `alternatingFeedbackTruthComputation_nonempty`,
`unboundedFeedbackTruthComputation_nonempty`), so `C` stays a **named, undischarged hypothesis of
`thm:wubexp`** — carried in the ledger's Hyps cells as (b) at the mandate's instruction, but it
is a hypothesis of the cited theorem, not a cited result, and **no instance of it is exhibited
anywhere in this package** (no witness inhabits the full package of any averaged cross-agent
row). Findings F-C records what was tried.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction LogicalInduction.FeedbackTruth Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Found.LiQuoteLane
open Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The averaged engine: `thm:wubexp` at a reflecting quote -/

/-- **`thm:wubexp` at a determined e.c. quote, any truth stream** (the engine in its general
form): for an inductor `P` over `DP` with a world at every stage, an e.c. family `Y` with
`Y n` determined at `truth n` in every completed-theory world, a strictly increasing deferral
`f` and a deadline program `C` for the normalized mesh truth of `Y` along `f`, `P`'s expectation
of `Y` is `w`-unbiased for `truth` along every `P`-generable divergent weighting supported on
`im f`. The `truth` need not be an `Expert.estimate`: it can be another market's *same-day*
expectation (the merge estimate `B_n`, T4(b)), which `def-lattice`'s `Expert` cannot express
(F1). `C` is the deadline program of `thm:wubexp`, doubly deferred for a quote of a deferred
expectation (module docstring); no instance exhibited.
Source: LI `thm:wubexp`; FAF `luv_wubexp_ofComputation`; mandate T3/T4
Kind: C
Fidelity: exact (FAF's `thm:wubexp` at singleton combinations)
Hyps: (b) `C` — an undischarged hypothesis of the cited theorem, not a cited result (F-C);
all else (a) -/
theorem wub_at_quote {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) {truth : ℕ → ℝ}
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (truth n)) {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n)) P DP hworld 1)
      f)
    (W : ℕ → EF) (hW : PGenerableWeighting W) (hWdiv : DivergentWeighting W P)
    (hsupp : WeightingSupportedOnDeferralImage W P f) :
    weightedBias (fun i => (W i).denote P) (fun i => (Y i).expect P i) truth ≈ₙ
      (fun _ => (0 : ℝ)) := by
  have h : LUVCombination.BoundedSequence (fun n => LUVCombination.ofLUV (Y n)) P :=
    ⟨⟨ofLUV_mesh_polySequence Y hY⟩, ⟨1, fun n => (l1Norm_ofLUV (Y n) P).2.le⟩⟩
  have hwub := luv_wubexp_ofComputation h (DeterminedVia.worldValued_ofLUV hdet)
    (DeterminedVia.determinedViaTheory_ofLUV P hdet) 1
    (fun n => by rw [(l1Norm_ofLUV (Y n) P).1]; norm_num) hW hWdiv hstrict hworld C hsupp
  simpa only [ofLUV_expect] using hwub

/-- **`thm:wubexp` at a reflecting quote (the averaged engine).** For any inductor `P` over `DP`
with a consistent world at every stage, any expert `E`, any source `X` and any e.c. quote `Y`
reflecting `E*(X)` in every completed-theory world, and any deadline program `C` for the
normalized mesh truth of the quote family along `E.f` (strictly increasing): `P`'s expectation
of the quote is `w`-unbiased for `E`'s realized estimate along every `P`-generable divergent
weighting supported on `im E.f` — `QuoteUnbiased P DP E X Y`. The `BoundedSequence` is the
singleton mesh (`ofLUV_mesh_polySequence`, `L¹` bound `1`), `WorldValued` and
`DeterminedViaTheory` are `Reflects` through `li-asymp-calc`'s `DeterminedVia` bridges, the
share bound is `1`. **`C` is a time hypothesis**, not a determinacy hypothesis: determinacy is
`hR`, discharged by construction at every instance of this package; `C` is discharged at none
(it asks for the expert's day-`f (f k)` expectation by the deadline `f (k+1) ≤ f (f k)`, F-C).
Grade: averaged. Direction: generic (the instance decides). Weight class: `P`-generable.
Source: [[merging-inductors-model]] §(a.2) Prop A ("literally `thm:wubexp` applied to `A` with
target LUV-sequence `(⌜μ_t⌝)` and weighting `w`"); LI `thm:wubexp`; FAF
`luv_wubexp_ofComputation`
Kind: C
Fidelity: exact (FAF's `thm:wubexp` at singleton combinations)
Hyps: (b) `C` — FAF's `FeedbackTruthComputation`, the paper's deferral-time clause ("`μ_t`
computable in `O(f(t+1))`", at `t = f k` the deadline `f (k+1)`); an undischarged hypothesis of
the cited theorem, no instance exhibited (F-C); all else (a) -/
theorem quoteUnbiased_ofComputation {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (E : Expert DP) (X Y : ℕ → LUV)
    (hY : LUV.MachineThresholdCodeSeq Y) (hR : Reflects DP E X Y)
    (hstrict : StrictlyIncreasingDeferral E.f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n)) P DP hworld 1)
      E.f) :
    QuoteUnbiased P DP E X Y := fun W hW hWdiv hsupp =>
  wub_at_quote Y hY (fun n v hv => hR n v hv) hstrict hworld C W hW hWdiv hsupp

/-! ## T2 — the self instance -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

omit [Entailment.Consistent T] in
/-- **Clause (i) for the self-expert is FAF's quote code**: every e.c. source `X` is quoted by
`paperDeferredExpectationQuoteCode T f X hX`, e.c. (`.poly`) and valued at `𝔼^P_{f n}(X n)` in
every completed-theory world of `paperDP T` (`deferredExpectationQuote_reflected`).
Source: trust-lab-002 (clause (i) at `M = N`); FAF `paperDeferredExpectationQuoteCode`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem selfObservable (f : DeferralFunction) :
    Observable (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  fun X hX => ⟨(paperDeferredExpectationQuoteCode T f X hX).luv,
    (paperDeferredExpectationQuoteCode T f X hX).poly,
    fun n v hv => deferredExpectationQuote_reflected T f X hX n v hv⟩

/-- **T2 (headline). The self instance is free, per-day grade:** the paper inductor
LUV-Total-Trusts its own day-`f n` self — clause (i) by FAF's quote code (`selfObservable`),
clause (ii) by `thm:ccee` (`def-self-trust`'s `selfCondTower`). Grade: per-day. Direction:
self (one market; N− as a witness for T1, the N+ is T3). Weight class: `P`-generable.
Source: trust-lab-002 ("for `M = N`'s own day-`f(n)` self it is FAF's
`lic_no_expected_net_update_conditional`"); root-deference-020 (row ccee)
Kind: C
Fidelity: variant: as `LUVTotalTrustDay` (weight at `w (f n)`, product within slack)
Hyps: (a) none -/
theorem selfTrust_day (f : DeferralFunction) :
    LUVTotalTrustDay (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  ⟨selfObservable T f, selfCondTower T f⟩

/-- **The averaged clause for the self-expert at one quoted pair**, given the deadline program:
`𝔼^P_n(Y_n)` is `w`-unbiased for `𝔼^P_{f n}(X_n)` along every `P`-generable divergent weighting
supported on `im f`. `quoteUnbiased_ofComputation` at `paperDP T` (`hworld := paperDP_hworld`).
Grade: averaged. Direction: self. Weight class: `P`-generable.
Source: trust-lab-002 (clause (ii), averaged grade, `M = N`); LI `thm:wubexp`
Kind: C
Fidelity: exact
Hyps: (b) `C` (the deferral-time clause; see the module docstring); all else (a) -/
theorem selfQuoteUnbiased_ofComputation (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f) (X Y : ℕ → LUV)
    (hY : LUV.MachineThresholdCodeSeq Y)
    (hR : Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X Y)
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n))
        (liaHistory (paperDP T)) (paperDP T) (paperDP_hworld T) 1) f) :
    QuoteUnbiased (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X Y :=
  quoteUnbiased_ofComputation _ X Y hY hR hstrict (paperDP_hworld T) C

/-- **T2, averaged grade, under a uniform deadline program:** if every e.c. quote family has a
deadline program along `f`, the paper inductor LUV-Total-Trusts its own day-`f n` self at the
averaged grade. The hypothesis `C` is `thm:wubexp`'s deadline program for every e.c. quote: on
`⟨k, f (k+1)⟩` emit the mesh truth of `Y_{f k}`, i.e. the LIA's own `𝔼^P_{f (f k)}(X_{f k})` —
doubly deferred (module docstring), so what it needs is a bound on the LIA's running time, which
FAF neither proves nor bounds; it is **not** discharged here and no instance is exhibited.
Grade: averaged. Direction: self. Weight class: `P`-generable. N− (one market; for the market
data — no witness of the full package).
Source: trust-lab-002; [[merging-inductors-model]] §(a.2) ("the 'fast enough `f`' clause" — a
different hypothesis, F-C); `AGENDA.md` "Fast Student, Slow Teacher"
Kind: C
Fidelity: variant: as `LUVTotalTrustAvg`; the deadline program quantified over the reflecting
e.c. quoted pairs (restricted from all e.c. quotes in repair r2, audit r2 fidelity N7 — the
conclusion needs it only there)
Hyps: (b) `C` (deadline program per reflecting pair, undischarged hypothesis of `thm:wubexp`,
F-C); all else (a) -/
theorem selfTrust_avg_ofComputation (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f)
    (C : ∀ X Y : ℕ → LUV, LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
      Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X Y →
      FeedbackTruthComputation
        (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n))
          (liaHistory (paperDP T)) (paperDP T) (paperDP_hworld T) 1) f) :
    LUVTotalTrustAvg (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  ⟨selfObservable T f, fun X Y hX hY hR =>
    selfQuoteUnbiased_ofComputation T f hstrict X Y hY hR (C X Y hX hY hR)⟩

/-- The `𝗣𝗔` instance at `succDeferral`: the section binders are discharged.
Source: mandate T2
Kind: L
Fidelity: n/a -/
example : LUVTotalTrustDay (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔)
    (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) :=
  selfTrust_day 𝗣𝗔 succDeferral

end

end Cleanroom.Trust.TrustMerge
