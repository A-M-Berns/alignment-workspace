import Cleanroom.Bli.BliLeak.Leak
import LogicalInduction.Construction.Freeze.Counterexample

/-!
# `bli-leak` · Transport: the sources' transfer statement is false (L3.0)

The sources justify "`ℙ` is a logical inductor" by "it agrees with `ℚ` on small prices"
(`main.tex:444`; bli-slides-030: "since traders don't touch large sentences, we can modify them
however we like without messing up any rationality properties of the market"). Read as a
transfer — *`E1x`-agreement with a computable market transports `IsLogicalInductor`* — this is
**false**, and FAF already holds the witness: its refutation of the paper's `thm:ifp` (PE1,
`exists_advice_perturbation_ofTheory`) exhibits `liaHistory (paperDP T)` and `cxPerturbed T`, the
same market with **day `0` alone** replaced by an advice row on the atoms `schedAtom n`,
`signAtom n`. On day `0` only `⊥` is small (`smallSet_zero`), and the advice row leaves `⊥` at its
base price, so `E1x (liaHistory (paperDP T)) (cxPerturbed T)` holds — while `cxPerturbed T` is
exploited by FAF's efficiently computable `adviceTrader` and so is no inductor.

This file transports that witness through `E1x`: no pseudorandom family, no dependence on
`li-pseudorandom`'s open computability. The pseudorandom leak (`Exploit.lean`, `Instance.lean`)
answers the retreat "day `0` is degenerate; edit only late days".

Memory: this file reaches `LIACompiler` through `Freeze.Counterexample`; one `lean-check` at a
time, own file (mandate K10).
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Cleanroom.Bli.BliFound
open FinitePerturbationCounterexample

/-- FAF's advice row leaves `⊥` at its base price: `⊥` is neither a `schedAtom` nor a `signAtom`.
Source: mandate L3.0 (proof of `E1x`: "`adviceRow` falls through to `base` on `⊥`")
Kind: L
Fidelity: exact -/
lemma adviceRow_falsum (base : Valuation) (gate sign : ℕ → ℝ) :
    adviceRow base gate sign ⊥ = base ⊥ :=
  adviceRow_of_not_advice base gate sign ⊥
    (fun n h => by
      have h' : (Formula.falsum : Sentence) = Formula.atom (Nat.pair 7 n) := h
      cases h')
    (fun n h => by
      have h' : (Formula.falsum : Sentence) = Formula.atom (Nat.pair 8 n) := h
      cases h')

section Theory

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]

omit [Entailment.Consistent T] in
/-- **FAF's PE1 witness satisfies `E1x`.** `cxPerturbed T` — the constructed inductor with day `0`
republished as the advice table — agrees with `liaHistory (paperDP T)` on every sentence small on
the day it is priced: on day `0` the small set is `{⊥}` (`smallSet_zero`) and the advice row leaves
`⊥` alone; on days `≥ 1` the two markets are equal (`advicePerturbed_agree`).
Scope: day-`0` edit; `smallSet 0 = {⊥}`; FAF's PE1 witness transported through `E1x`.
Source: mandate L3.0 (`cxPerturbed_E1x`); FAF `Construction/Freeze/Counterexample.lean`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cxPerturbed_E1x : E1x (liaHistory (paperDP T)) (cxPerturbed T) := by
  intro n φ hφ
  rw [mem_smallSet] at hφ
  cases n with
  | zero =>
      rw [smallOn_zero_iff] at hφ
      subst hφ
      unfold cxPerturbed advicePerturbed
      rw [advicePerturb, if_pos rfl, adviceRow_falsum]
  | succ n =>
      exact (advicePerturbed_agree _ _ _ (n + 1) (by omega) φ).symm

/-- **FAF's advice trader exploits the PE1 witness** — the exploitation clause of
`exists_advice_perturbation_ofTheory`, restated with the witness named (FAF packages it
existentially): the settled-day dichotomy from the paradox quote, the price range from the
market's computability, `hworld` from `paperDP_hworld`, and the two interface laws of the advice
trader.
Source: mandate L3.0; FAF `FinitePerturbationCounterexample.exploits`, `exists_advice_perturbation_ofTheory`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cxPerturbed_exploited :
    (adviceTrader schedAtom signAtom (cxDiagonal T)).Exploits (cxPerturbed T) (paperDP T) :=
  FinitePerturbationCounterexample.exploits _ (cxPerturbed T) (paperDP T) (cxDiagonal T)
    (fun j => dichotomy_of_paradoxQuote (cxQuote T) (advicePerturbed_agree _ _ _)
      (one_le_sched _ _ _ j))
    (computableMarket_cxPerturbed T).1
    (paperDP_hworld T)
    (fun v i hi => adviceTrader_value_off_sched schedAtom signAtom (cxDiagonal T) _ _
      (advicePerturbed_schedAtom_off _ _ _) v i hi)
    (fun v j => adviceTrader_value_on_sched schedAtom signAtom (cxDiagonal T) _ _
      (advicePerturbed_schedAtom_on _ _ _) (advicePerturbed_signAtom_on _ _ _) v j)

/-- **The PE1 witness is no logical inductor** over `paperDP T`: an efficiently computable trader
(`adviceTrader_efficient`) exploits it, against `IsLogicalInductor.noExploit`.
Source: mandate L3.0 (`cxPerturbed_not_logicalInductor`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem cxPerturbed_not_logicalInductor : ¬ IsLogicalInductor (cxPerturbed T) (paperDP T) :=
  fun h => h.noExploit _
    (adviceTrader_efficient machineSentenceCodes_schedAtom machineSentenceCodes_signAtom
      (MachineSentenceCodes.ofPolySentenceCodes (cxDiagonal_poly T)))
    (cxPerturbed_exploited T)

/-- The edit is real: the PE1 witness differs from the constructed inductor (else it would be one).
Source: mandate L3.0 (N+: the transport is not vacuous)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem cxPerturbed_ne_liaHistory : cxPerturbed T ≠ liaHistory (paperDP T) := by
  intro h
  exact cxPerturbed_not_logicalInductor T
    (h ▸ LIA_is_logical_inductor (paperDP T) (paperDP_computable T))

include T in
/-- **L3.0. The sources' transfer is false**, over any consistent `Δ₁` theory extending `𝗜𝚺₁`:
it is *not* the case that every computable market `E1x`-agreeing with a logical inductor over
`DP` is itself a logical inductor over `DP`. Witness: `Q = liaHistory (paperDP T)`,
`P = cxPerturbed T` (FAF's PE1 witness), `DP = paperDP T`; `E1x` by `cxPerturbed_E1x`,
computability by FAF's `computableMarket_cxPerturbed`, the failure of the criterion by
`cxPerturbed_not_logicalInductor`.
Scope: day-`0` edit; `smallSet 0 = {⊥}`; FAF's PE1 witness transported through `E1x`. The
refuted reading is the *transfer* reading of bli-slides-030 / bli-slides-005 / `main.tex:444`
("`ℙ` is now a logical inductor, since it agrees with `ℚ` on small prices"), ATTRIBUTION-UNVETTED
as a choice among readings (findings K8); the surviving neighbours are FAF's
`lic_iff_of_finiteSupportPerturbation` (finite support), `bli-transfer`'s expressible-overlay
transfer (L1) and restricted-class transfer (L4), and this package's `exploits_leakHistory_iff`
(a trader that never reads a leak is unaffected).
Source: mandate L3.0; bli-slides-030, bli-slides-005, `main.tex:427/444`; [[bli-program]] §3.2(b),
§3.11(j)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem posthoc_transfer_refuted_ofTheory :
    ¬ ∀ (Q P : History) (DP : DeductiveProcess),
        IsLogicalInductor Q DP → ComputableMarket P → E1x Q P → IsLogicalInductor P DP := by
  intro h
  exact cxPerturbed_not_logicalInductor T
    (h _ _ _ (LIA_is_logical_inductor (paperDP T) (paperDP_computable T))
      (computableMarket_cxPerturbed T) (cxPerturbed_E1x T))

end Theory

/-- **L3.0, closed at `𝗜𝚺₁`** (which is `Δ₁`-definable, extends itself and is consistent, as in
FAF's `not_overgeneral_ifp`): `E1x`-agreement with a computable market does not transport
`IsLogicalInductor`. No theory parameter, no hypothesis.
Source: mandate L3.0 (`posthoc_transfer_refuted`, N+ at `paperDP 𝗜𝚺₁`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem posthoc_transfer_refuted :
    ¬ ∀ (Q P : History) (DP : DeductiveProcess),
        IsLogicalInductor Q DP → ComputableMarket P → E1x Q P → IsLogicalInductor P DP :=
  posthoc_transfer_refuted_ofTheory 𝗜𝚺₁

end Cleanroom.Bli.BliLeak
