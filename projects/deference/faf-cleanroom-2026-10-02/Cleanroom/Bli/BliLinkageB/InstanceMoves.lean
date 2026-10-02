import Cleanroom.Bli.BliLeak.Instance
import Cleanroom.Bli.BliLinkageB.InstanceCells

/-!
# bli-linkage, angle B — the "moves" clause at `bli-leak`'s family (OPEN)

**Cross-package import, disclosed:** this module imports `Cleanroom.Bli.BliLeak.Instance`,
which is outside the mandate's dependency edges (`bli-trajectory`, `li-pseudorandom`), as the
mandate's § K3 (ii) directs ("import `Cleanroom.Bli.BliLeak.Instance`, not `.Closed`, and never
`Cleanroom.Bli.BliLeak` as a root"). Nothing else in `BliLinkageB` depends on it.

The conclusion of record (`InstanceCells.no_degenerate_linked_bli_LIA`) is conditional on
`hmove`: the inductor's rounded price of a listed coordinate moves infinitely often. The
mandate's candidate for discharging it is `bli-leak`'s family: the LIA over
`leakDP T = paperDP T ∪ atomDP member (leakStream T) recordDelay` (delay one) prices the
pseudorandom coordinate `memberAtom n` at `≈ ½` on day `n` (`leakStream_pseudorandom` with
`lic_learning_pseudorandom_frequency`, grade (a) modulo li-pseudorandom T7), and the program's
reading was that the day-`(n+1)` price is the decided truth value, so the `halfRound` cell moves
whenever the day-`n` price falls on the other side of `½`. The second half has no FAF route
(mandate § K3; findings FB-5): `lic_provind` needs an e.c. family of theorems, the decided
literals are not one, and an inductor that keeps `½` on day `n+1` is not exploited by any
trader this run can build. So the statement is **OPEN**, listed in `bli-linkage-b-open.txt`.

**What a proof would need.** For the day-`n` half: `leakQ T n (memberAtom n) ∈ (½ − ε, ½ + ε)`
on a set of days of density one, from `PseudorandomFrequency` at the identity deferral — this
is grade (a) modulo T7 and would say the day-`n` cell is `0` or `1` unpredictably, not that it
*changes*. For the day-`(n+1)` half: a price target for a just-decided pseudorandom atom, i.e.
an exploiting trader against "`leakQ T (n+1) (memberAtom n)` stays near `½` although
`memberAtom n` entered a stage of `leakDP T` at day `n+1`" — which needs the construction's
budgeter (`MarketMaker`/`LIAComputation`, size L–XL) rather than the criterion. The real-valued
form below (`< ½` on day `n+1` iff not `< ½` on day `n`) is `halfRound` of the exact rational
quote, by `MarketComputation.quote_exact`.
-/

namespace Cleanroom.Bli.BliLinkageB

namespace InstanceMoves

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLeak

/-- **OPEN — the LIA over `bli-leak`'s process moves the `halfRound` cell of the pseudorandom
coordinate infinitely often**: for infinitely many `n`, `leakQ 𝗜𝚺₁ (n+1) (memberAtom n) < ½`
holds iff `leakQ 𝗜𝚺₁ n (memberAtom n) < ½` fails. The day-`n` half is
`leakStream_pseudorandom` + `lic_learning_pseudorandom_frequency` (grade (a) modulo
li-pseudorandom T7); the day-`(n+1)` half has no FAF route (mandate § K3, FB-5, FB-16). Stated,
not proved; listed in `bli-linkage-b-open.txt`.
Source: mandate § K3 (iii) (`leakQ_rounded_price_moves`); [[bli-program]] §3.6(iii)
Kind: OPEN
Fidelity: exact (the real-valued `< ½` is `halfRound` of the exact rational quote)
Hyps: n/a -/
theorem leakQ_rounded_price_moves :
    Set.Infinite {n | ¬ ((leakQ 𝗜𝚺₁ (n + 1) (memberAtom n) < 1 / 2) ↔
      (leakQ 𝗜𝚺₁ n (memberAtom n) < 1 / 2))} := by
  sorry

end InstanceMoves

end Cleanroom.Bli.BliLinkageB
