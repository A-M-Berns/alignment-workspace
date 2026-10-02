import Cleanroom.Bli.BliLeak.Instance
import Cleanroom.Bli.BliLeak.Computable
import LogicalInduction.Construction.LIACompiler

/-!
# `bli-leak` · Closed: the closed forms over `paperDP T`, resting on `li-pseudorandom` T7

Everything here rests on the two OPEN statements of `Instance.lean` (`leakStream_computable`,
`leakDP_computable`), which are `li-pseudorandom` T7 in the union shape, and is listed in
`bli-leak-open.txt` as such: the inductor certificate of the base (`leakQ_isLogicalInductor`,
through FAF's `LIA_is_logical_inductor` — the one use of `LIACompiler` in this package, kept in
its own file), the computability of the leak market of record (`leakMarket_computableMarket`,
through L3.6's grade-(a) `leakHistory_computableMarket` in `Computable.lean`),
and the closed refutations: the trader of record exploits the leak market of record, the leak
market is no inductor, and **the finite-prefix retreat is refuted** (`posthoc_transfer_refuted_late`,
L3.4): for every `N₀`, a computable market agreeing with an inductor exactly on days `< N₀` and on
every day-small sentence need not be an inductor.

Scope (mandate L3.4/L3.5): exploitation (a); the counterexample market's computability and the
instance's inductor certificate rest on `li-pseudorandom` T7 (OPEN). Ledger status of every row
here: `partial: over OPEN computability (li-pseudorandom T7)`.
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Li.LiPseudorandom

section Theory

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The base inductor of record is a logical inductor over the process of record — FAF's
`LIA_is_logical_inductor` on the OPEN `leakDP_computable`.
Source: mandate L3.5 (the instance is T7)
Kind: OPEN
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) `leakDP_computable` -/
theorem leakQ_isLogicalInductor : IsLogicalInductor (leakQ T) (leakDP T) :=
  LIA_is_logical_inductor (leakDP T) (leakDP_computable T)

/-- **L3.6 at the instance of record**: the leak market of record is a computable market —
`leakHistory_computableMarket` (grade (a)) on the base's table (from the OPEN inductor
certificate), the constant edit day, and the OPEN `leakStream_computable`.
Source: mandate L3.6 (`hx` is T7)
Kind: C
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) `leakQ_isLogicalInductor` (the base's table), `leakStream_computable` -/
theorem leakMarket_computableMarket (N₀ : ℕ) : ComputableMarket (leakMarket T N₀) :=
  leakHistory_computableMarket (leakQ_isLogicalInductor T).marketComputable
    (Computable.const N₀) (leakStream_computable T) (recordPad N₀)

/-- **L3.5, closed form**: the trader of record exploits the leak market of record over the
process of record.
Source: mandate L3.5
Kind: C
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) `leakQ_isLogicalInductor` -/
theorem leak_instance_exploits_closed [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (N₀ : ℕ) :
    (leakTraderRecord N₀).Exploits (leakMarket T N₀) (leakDP T) :=
  haveI := leakQ_isLogicalInductor T
  leak_instance_exploits T N₀

/-- **The leak market of record is no logical inductor**, closed form.
Source: mandate L3.4/L3.5
Kind: C
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) `leakQ_isLogicalInductor` -/
theorem leak_instance_not_logicalInductor_closed [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (N₀ : ℕ) :
    ¬ IsLogicalInductor (leakMarket T N₀) (leakDP T) :=
  haveI := leakQ_isLogicalInductor T
  leak_instance_not_logicalInductor T N₀

/-- **L3.4. The finite-prefix retreat is refuted**, closed form: for every `N₀`, it is not the case
that a computable market agreeing with an inductor exactly on days `< N₀` and on every
day-small sentence is an inductor. Witness: the leak market of record with all edits on day
`N₀`, exploited by the trader of record.
Scope: exploitation (a); the counterexample market's computability and the instance's inductor
certificate rest on `li-pseudorandom` T7 (OPEN).
Source: mandate L3.4 (`posthoc_transfer_refuted_late`)
Kind: C
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) `leakQ_isLogicalInductor`, `leakMarket_computableMarket` -/
theorem posthoc_transfer_refuted_late [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (N₀ : ℕ) :
    ¬ ∀ (Q P : History) (DP : DeductiveProcess), IsLogicalInductor Q DP →
        ComputableMarket P → (∀ n < N₀, ∀ φ, P n φ = Q n φ) → E1x Q P →
        IsLogicalInductor P DP := by
  haveI := leakQ_isLogicalInductor T
  intro h
  exact leak_instance_not_logicalInductor T N₀
    (h _ _ _ inferInstance (leakMarket_computableMarket T N₀) (leakMarket_agree_before T N₀)
      (leakMarket_E1x T N₀))

end Theory

end Cleanroom.Bli.BliLeak
