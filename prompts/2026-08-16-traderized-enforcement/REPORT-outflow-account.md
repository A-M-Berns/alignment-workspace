# Report — the outflow account

Answers to the dispatch's §XXVI. An unanswered question is a blocker; each below
is either answered or named as an open problem.

**1. Can infinitely many individually finite endorsement budgets destroy aggregate
safety?** Yes. `∀e. B_e < ∞` does not give `Σ_e B_e < ∞`. Exact fixture: one
endorsement live per date, each spending `2` and retiring; aggregate `2n`.
`test_outflow.PerEndorsementCapsDoNotAggregate`.

**2. Can finite gating prevent that?** No. Gating bounds rows per date and says
nothing about the number of dates. `test_outflow.GatingIsNotALifetimeBound`.

**3. Is the account global, summably decomposed, or per-source?** Global, with
optional summable decomposition. `allocate` checks each reservation against
global capital, so `Σ_e B_e ≤ B` holds by construction rather than by hypothesis.
Per-source alone is exactly what question 1 refutes.

**4. Can outside funding replenish the account?** A constitutional choice,
reserved, and flagged as the queue's highest-risk item.

**5. If yes, why does that not reintroduce unbounded liability?** It does, if
unbounded. This is precisely the failure `NL-SI-P1` names — an outside source
replenishing every paid loss while only current positions are tracked.
Replenishment must be bounded globally or confined to a new era with its own
finite allocation. No third option is known.

**6. What happens when the account is exhausted?** `spend` raises rather than
emitting force it cannot fund, and the caller selects a behaviour. Refusal is the
guarantee; an account that overdrafts certifies nothing.

**7. Weaken tolerance, remove force, quarantine, or breach?** All four are
implemented or implementable and are not equivalent. Reserved. Weakening the
declared **core minimum** is not among them — the worst deficit `max(0, r − m_c)`
contains no `θ`, so it buys nothing.

**8. Can an endorsement remain unresolved forever and still receive safe nonzero
force forever?** Yes, if and only if its exclusion deficit decays fast enough.
Witness: deficit `2^-t` against volume `t+1`, fixed tolerance `1/2` at every date,
closed-form bound `17/2`. And **only** then: no finite account funds meaningful
force at infinitely many dates when the deficit stays above a positive floor,
under any protocol. `meaningful_dates_are_finite`.

**9. Is liability accounting invariant under equivalent row rescaling?** Yes, at a
fixed *actual* conformance target. Rescaling by `λ` scales violation and deficit
by `λ` and intensity by `λ⁻²`; the position and the charge are unchanged.

**10. If not, what is canonical about the presentation?** The question survives in
weakened form: a fixed **declared** `δ` *is* presentation-dependent, because `δ`
promises something about the violation in the presentation's own units. The
interface therefore requires tolerance stated against a normalized row or against
an actual conformance target.

**11. Does duplicate-row presentation create extra safety cost?** No, at fixed
actual conformance: `k` copies divide the intensity by `k` and the cancellation
is exact.

**12. Can the source manipulate its presentation to buy stronger force for the
same account?** No, by 9 and 11.

**13. Realized loss or declared worst-case certificate?** Certificate.

**14. How conservative?** Two separate gaps, and neither is measured. It
maximizes over live worlds *independently at each date*, where the criterion
follows one world across dates; and it charges per-row worst cases, where realized
positions can cancel in price space. Open.

**15. Is the charge computable before the trade is emitted?** Yes. `ε_t` from the
market, `C_t` a declared bound, `δ_t` the tolerance about to be promised, `d_t`
from the semantic/settlement state. No realized price appears.

**16. Does the account theorem use the same live-world quantifier as the LI
preservation theorem?** It uses a **strictly stronger** sufficient one, and the
note says so rather than eliding it.

**17. Does the clause say more than "assume `B < ∞`"?** Yes. It gives an
operational charge in advance-known quantities, an affordability relation
`δ_t ≥ (ε_t + C_t)‖d_t‖₁/b_t` that constrains what force may be bought, an
admission check that makes summability true rather than hoped for, and a
limitative theorem that no account can evade. It also has independent normative
content: *a practice may impose reasons beyond what is settled, but may not
finance unbounded resistance to indefinitely unresolved disagreement.*

**18. Is there a clean mathematical reason it belongs in the Normativity
architecture?** Yes, and it is the type comparison: the quantifier structure is
identical to `P2`'s — worldwise, cumulative, uniform in horizon — while bearer,
holdings and means differ. That is the signature of a sibling under a shared
principle rather than a coincidence, and the corpus already adopted the same
repair for the same failure in `NL-SI-P1`.

## §XXIV verdict — A, with a stated limit

Safety is **implemented**: a concrete outflow protocol is defined and shown to
imply bounded enforcement liability. Normative statics are force-compilable,
tolerance-enforceable, and safe under the installed outflow discipline — and no
finite account funds meaningful force forever against a demand whose distance
from the record does not close.

## §XXV — the paper verdict is unchanged

Nothing here touches the generalized construction. Generalized-LI paper:
available conditional on formalizing the live-world Budgeter/TradingFirm lift.
Traderized-force mechanism: conformance established, safety preservation
established conditional on bounded liability. Normativity application: the
outflow protocol succeeds, with the limitative theorem as its boundary.

## What did not survive review

The intensity-free liability ceiling (withdrawn earlier, still withdrawn). The
empty-interior exactness impossibility (`PRIORITIES.md` item 43, repaired this
pass). Result 27's derivation of deductive recovery from the price region (marked
withdrawn this pass). The word "unsafe" for the never-vindicated fixture, which
earned only certificate failure at the time and now earns realized divergence at a
followed world — still not an exhibited exploitation.
