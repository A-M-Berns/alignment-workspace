import Cleanroom.Bli.BliLeak.Trader
import Cleanroom.Bli.BliFound.Bridge

/-!
# `bli-leak` · audit round 1 · adversarial lens · probe: the trader of record reads the leak on the edit day itself

**Not imported by the library.** Evidence for an item of `bli-leak-audit-r1-adversarial.md`.

* P3 — the package's own trader of record (`leakTrader (leakAtom (4 ^ sizeBound N₀)) (fun _ ↦ N₀) memberAtom`,
  which is `Instance.leakTraderRecord N₀`) is efficiently computable **and** on day `N₀` mentions
  (in a `price` leaf) the leak atom `leakAtom (4 ^ sizeBound N₀) N₀`, which is **large on day `N₀`**.
  So an e.c. trader can name a sentence large on the day it is priced, on that very day: E1's
  "unreadable before a day of order `(2 ^ k / A) ^ (1 / E)`" is a statement about a *fixed*
  trader as `k` varies (its `A` may exceed `2 ^ k`), not a uniform delay after the edit day; and
  the bridge lemma's "traders don't touch large sentences" holds only *eventually*, per trader.
  This is why L3.4 refutes the finite-prefix retreat for every `N₀` without any waiting time.
-/

namespace Cleanroom.Bli.BliLeak.AuditR1

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLeak

/-- The trader of record mentions a day-`N₀`-large sentence on day `N₀`, and is e.c. -/
theorem record_trader_reads_large_on_edit_day (N₀ : ℕ) :
    MentionedBy ((leakTrader (leakAtom (4 ^ sizeBound N₀)) (fun _ => N₀) memberAtom).strat N₀)
        (leakAtom (4 ^ sizeBound N₀) N₀) ∧
      ¬ SmallOn N₀ (leakAtom (4 ^ sizeBound N₀) N₀) ∧
      EfficientlyComputable (leakTrader (leakAtom (4 ^ sizeBound N₀)) (fun _ => N₀) memberAtom) := by
  refine ⟨?_, leakAtom_large_pow N₀ le_rfl N₀, leakTrader_record_ec _ _⟩
  refine Or.inr ⟨(leakCoef (leakAtom (4 ^ sizeBound N₀)) (fun _ => N₀) N₀, memberAtom N₀), ?_,
    N₀, ?_⟩
  · simp [leakTrader_trades]
  · simp [leakCoef, EF.priceQueries]

end Cleanroom.Bli.BliLeak.AuditR1
