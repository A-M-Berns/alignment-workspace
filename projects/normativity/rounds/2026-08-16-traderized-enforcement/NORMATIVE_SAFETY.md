# Can the motivating normative statics discharge safety?

Not "can some region be enforced safely" — can *these* statics, the settlement and
core construction already in the normativity line, satisfy the
bounded-enforcement-liability hypothesis that preserves nonexploitability.

Exactness is not the question. The market maker's own finite-time contract carries
slack, ordinary coherence is not exact at finite dates either, and the application
wants `g_{t,j}(P_t) ≤ δ_t` with a declared schedule. What the application must not
do is destroy the no-exploitation guarantee.

**Verdict: 2 — one natural additional clause is needed, and it already exists in
the corpus in another context.**

## 1. The motivating region, and its two families

At date `t`: a post-settlement simplex, an endorsed region inside it, a declared
core minimum `θ_min`, and `NL-SI-A2`'s admissible-reference polytope compiled to
price-space rows by `CORE_CONDITION.md`. The resulting `K_t^norm` has rows from
two sources, and they behave differently.

**Settlement / coherence rows.** Right-hand sides are minima over the assessed
worlds, so every assessed world satisfies every one of them. Their exclusion
deficit is **identically zero**, and by the kernel-checked nonnegativity reading
they contribute nothing to enforcement liability — ever, at any intensity.
Checked at three stages in `test_normative`.

**Core / endorsement rows.** These are useful precisely when they exclude a credal
state the settled record still permits, and they carry all the liability.

There is no third source in the motivating statics.

## 2. What a core row's deficit actually is

For an endorsement `⟪c, q⟫ ≥ r` with `c` indexed by worlds, write
`m_c = min_ω c_ω` — the least any assessed world delivers. `NL-SI-A2`'s row is
`(1−θ)⟪c,q⟫ ≥ r − θ·m_c`, and its worst deficit over assessed worlds is

    d = max(0, r − m_c) ,

attained at a world achieving the minimum. **It does not depend on `θ`.** The core
minimum sets how deep the reference must sit inside the endorsed region; it does
not change how far the endorsement outruns what the worlds deliver. Verified at
three values of `θ`.

So the liability is governed by one quantity per endorsement: **how far the
book's demand exceeds the worst still-assessed world**.

## 3. What the existing statics already give

Settlement is monotone (`NL-SI-C4`) and never reopened (`NL-SI-P1`), so the
assessed worlds shrink and `m_c` is **non-decreasing**. Hence `d` is
**non-increasing** along any settlement trajectory: `1/2, 1/2, 0` on the displayed
instance, reaching zero exactly when the record entails the endorsement.

Finite gating (`P3`) bounds how many rows are live per date, hence the length of
the deficit vector.

**That is monotonicity and a bounded row count. It is not summability**, and the
declared-quantity ceiling `(ε_t + C_t)·‖d_t‖₁/δ_t` has `C_t` — a bound on
cumulative ordinary trading volume — growing in the numerator.

## 4. Two trajectories

**Safe.** The endorsement is vindicated by settlement after two dates; the deficit
is `1/2, 1/2, 0, 0, …`. Cumulative bound `135/8`, and **identical at horizons 4, 8
and 12** — finitely many dates carry any deficit at all, so `B < ∞` is discharged
outright.

**Unsafe.** Minimally altered: nothing ever settles, the deficit stays `1/2`, and
`C_t = t`. Cumulative bound `52.3 → 182.5 → 392.5` at the same horizons, growing
quadratically. And it is not only the bound: the compiled position is short the
endorsement's direction at a world the record still permits, so the loss is real.

Both are exact-rational and run in `test_normative`.

## 5. The type comparison the addendum asks for

The one candidate with the right shape is the settlement interface's `P2`.

```text
P2 downside limit
  bearer:      the engine
  quantifiers: worldwise, against the book's holdings
  trajectory:  a guarantee at each date, with declared means
  what it bounds: the engine's loss on the book's positions
  declared means: refusal, or bounded aggregate participant budgets

enforcement liability
  bearer:      the enforcement trader
  quantifiers: every date n, every world in Omega_n^live, cumulative to n
  trajectory:  uniform over the whole horizon
  what it bounds: omega( sum_{t<=n} E_t ), the compiled position's own value
  declared means: none — the trader is exempt from budget caps by construction
```

The **quantifier structure matches exactly**: worldwise, cumulative, uniform in
horizon. What differs is the bearer, the holdings, and — decisively — the declared
means. `P2`'s two means are refusal and bounded aggregate participant budgets, and
the enforcement trader is exempt from both: unit weight and no budget cap are its
defining privileges (`SOURCE_AUDIT.md` §7). **So `P2` as written does not cover
it**, and identifying them by shape alone would be exactly the vocabulary error
the round has been avoiding.

## 6. Per-endorsement caps do not aggregate

The first thing to try is the modular clause: each endorsement declares a finite
bound on the cumulative outflow of its own compiled position. It fails, and the
failure is not subtle.

Let endorsement `e` be live at date `e` alone, with exclusion deficit `1`, at
tolerance `1/2` against `ε + C = 1`. Its whole-lifetime outflow is `2`, finite.
Exactly one row is live at every date, so finite gating is obeyed everywhere. And
the aggregate certificate after `n` dates is exactly `2n`.

    for all e, B_e < ∞     does not give     Σ_e B_e < ∞ ,

and a source can walk that gap forever by retiring each endorsement as it admits
the next. `test_outflow.PerEndorsementCapsDoNotAggregate`.

**Finite gating does not close it.** Gating bounds how many rows are live *per
date*; nothing in it bounds the number of dates. A clause citing gating for
lifetime safety claims more than gating gives, and
`test_outflow.GatingIsNotALifetimeBound` is the named regression.

So the account must be **global over the enforcement channel**, or decomposed
into an allocation that is *summable* rather than merely finite termwise.

## 7. The account

`src/outflow.py`. Finite lifetime capital `B`, spent down as force is emitted.

**The charge.** A date's force costs `(ε_t + C_t)·‖d_t‖₁ / δ_t` — the
declared-quantity liability ceiling, renamed. That rename is the move: a quantity
the safety analysis could previously only report after the fact becomes a price
paid in advance. It uses no realized price, so §6's timing question answers
cleanly — the charge is computable *before* the trade is emitted, from the
market's slack, a declared volume bound, the tolerance the mechanism is about to
promise, and the deficit vector the semantic/settlement state supplies.

**Allocation.** `allocate` reserves capital per endorsement against global
capital and refuses when it is short. Summability is then imposed at admission
rather than hoped for in the limit, and §6's counterexample dies at the fourth
admission rather than running forever.

**Additivity.** The certificate is exactly additive over rows and identically
zero on settlement rows, so per-endorsement charging is well defined. It is
*conservative*: realized liability of a sum can be smaller than the sum of
component liabilities, because positions cancel in price space.

## 8. Safety theorem

    account discipline  ⟹  Σ_t charge_t ≤ B  ⟹  for all n, ω ∈ Ω_n^live,
                                                 Σ_{t≤n} E_t(ω) ≥ −B .

The second arrow needs care about the quantifier. The criterion picks a world at
horizon `n` and follows it back; the certificate maximizes over live worlds
*independently at each date*. The certificate is therefore a **strictly stronger
sufficient condition** than the criterion needs, not a restatement of it —
`charge_is_conservative` checks the domination on a trajectory, and
`test_outflow.ChargeIsAdditiveOverRowsAndConservativeOverWorlds` exhibits the gap
rather than hiding it. This is the price of a certificate computable in advance.

Conditional on the live-world Budgeter/TradingFirm lift, `B < ∞` then gives
nonexploitability with assessed net worth at most `1 + B`.

## 9. Force is purchased, and some force cannot be bought

Inverting the charge against a per-date allowance `b_t` gives the pass's central
relation:

    δ_t  ≥  (ε_t + C_t)·‖d_t‖₁ / b_t .

So the system stops being "pick `δ_t`, hope safety holds" and becomes "the
remaining account determines how tightly the reasoner may be forced". A free date
— nothing live excluded — is reported as free rather than as zero tolerance, and
a required `δ_t > 1` is reported as unaffordable rather than rounded down.

**And there is a hard limit.** A date whose promise says anything needs
`δ_t ≤ 1`, so it costs at least `‖d_t‖₁`. If the exclusion deficit never falls
below a positive floor, those charges are bounded away from zero and finitely
many fit in finite capital:

> **No finite account funds meaningful operative force at infinitely many dates
> against an endorsement whose exclusion deficit does not decay to zero.**

Against every protocol, not against one policy — `meaningful_dates_are_finite`.
The `proportional` policy makes the shape vivid: spending a fixed share of what
remains never exhausts the capital, and the tolerance it buys still diverges, so
force goes vacuous anyway. Never running out is not the same as keeping force
available.

**What survives is weaker than settlement.** An endorsement need never be
vindicated. Its *depth* must close. `test_outflow.ForeverUnvindicatedAndSafe`:
deficit `2^-t`, ordinary volume `t+1` growing without bound, a fixed nonvacuous
tolerance `1/2` at every date forever, total charge under the closed form `17/2`.
The endorsement is never settled and never fully satisfied, and the account holds.
That is the conceptual payoff — safety does not demand that normative
disagreement be deductively resolved, only that unresolved disagreement be
resisted with summably decreasing force.

## 10. What happens at exhaustion, and what does not help

**Quarantine** withholds force and spends nothing; the endorsement keeps its
normative standing and loses operative effect. **Relaxation** buys the tightest
affordable promise. **Refusal at admission** is `allocate` failing. **Tolling**,
if force is withheld for account reasons, is the behaviour that fits the existing
answerability architecture — a deadline should not count a failure the substrate
caused — and it is a constitutional choice, recorded as one and not made here.

**Weakening the core minimum does not help.** The worst deficit is
`max(0, r − m_c)`, in which `θ` does not appear. Lowering the declared core
minimum weakens the demand on the reference and leaves the charge exactly where
it was. A protocol answering exhaustion by weakening the core has paid nothing —
`test_outflow.ExhaustionBehaviour.test_weakening_the_core_minimum_does_not_reduce_the_charge`.

## 11. Presentation

A half-space has many presentations, and if the account were presentation-
dependent a source could buy the same constraint cheaply by rescaling. It is not:

> At a fixed **actual** conformance target, the compiled position and the charge
> are identical across row rescalings and row duplications.

Rescaling by `λ` multiplies the violation and the deficit by `λ` and divides the
intensity by `λ²`; duplication into `k` copies divides the intensity by `k`. Both
cancel exactly. What *is* presentation-dependent is a fixed **declared** `δ`,
because `δ` is a promise about the violation in the presentation's own units. The
force API must therefore state tolerance against a normalized row or against an
actual conformance target — and having done so, no rescaling or duplication buys
stronger force for the same account. `test_outflow.LiabilityIsInvariantUnderRowPresentation`.

## 12. Where the clause belongs

The corpus already adopted this discipline for the same failure. `NL-SI-P1`'s
proof describes the structure it refutes —

> a false exposed constraint survives arbitrarily many tests when an outside
> source replenishes every paid loss and only current locks are tracked

— and records the repair as *"a limit on cumulative net outflow, not a
re-litigation of what was settled."* An externally funded enforcement trader
propping up an endorsement the record never vindicates **is** an outside source
replenishing every paid loss while only current positions are tracked.

**Not a rename of `P2`.** `P2` bounds the engine's downside on book holdings; its
declared means are refusal and bounded participant budgets, and the enforcement
trader is exempt from both by construction. The quantifier structure matches
exactly — worldwise, cumulative, uniform in horizon — but the bearer, holdings
and means do not. The correct move is a **sibling clause under a shared
principle**, not a broadening of `P2`:

> Every privileged channel that can impose losses unavailable to ordinary bounded
> participants carries a finite cumulative downside account.

That covers `P2` and traderized force as two instances with different bearers.
Whether to state the shared principle, or only the sibling, is reserved.

**Replenishment is the load-bearing detail.** If an outside source may top the
account up without limit, the guarantee is gone — that is exactly the failure
`NL-SI-P1` names. Replenishment must be bounded globally, or admitted only under
a new constitutional era with its own finite allocation. This is the one place
where a plausible-looking implementation choice silently destroys the theorem.

**Source-owned or market-owned.** Source-owned budgeting makes an endorsement's
persistence its author's responsibility and fits answerability; market-owned
allowance makes safety architectural and independent of who authored the
constraint. The theorem is indifferent — it needs only that the total be finite.
The choice is constitutional and is reserved.

## 13. Two sufficient trajectory conditions, neither necessary

**Deficit route.** `Σ_t (ε_t + C_t)·‖d_t(ω)‖₁ / δ_t < ∞`. Satisfied by the safe
fixture with finitely many nonzero terms, and by the forever-unvindicated fixture
with infinitely many. Nothing shows it necessary.

**Support route.** `Σ_t (1 − θ_t(ω))·U_t / θ_t(ω) < ∞`. The motivating statics
supply no lower bound on live-world support capacity and no summable bound on
`U_t`, so this route is **not** discharged by them; it remains available to a
source that supplies those quantities. Nothing shows it necessary either.

## 14. What is not established

That the account is necessary (`PRIORITIES.md` item 40). That the deficit route is
the best available. That the charge is anywhere near tight — it is a worst-case
certificate over worlds, and how conservative it is has not been measured. That an
efficient trader exploits the bounded-liability-failing fixture: the realized
cumulative loss at a followed world diverges, which is a failure of the
hypothesis, and **not** an exhibited exploitation.

Whether a revisable normative practice keeps the depth non-increasing at all:
**it need not** — revision can raise `r` or reopen `m_c` — and revision is outside
the live-world lift's nesting hypothesis for the same reason.

And the whole chain is conditional on the live-world Budgeter/TradingFirm lift,
which is `derived` and unformalized.
