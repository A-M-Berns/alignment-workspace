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

## 6. The clause that is needed, and where it already is

What is missing is a **cumulative-outflow discipline on the enforcement position**.
And the corpus already adopted that discipline, for the same failure, in another
context. `NL-SI-P1`'s proof describes the structure it refutes:

> a false exposed constraint survives arbitrarily many tests when an outside
> source replenishes every paid loss and only current locks are tracked

and records the repair:

> the repair adopted there is a limit on cumulative net outflow, not a
> re-litigation of what was settled.

That is this problem. An externally funded enforcement trader propping up an
endorsement the record never vindicates *is* an outside source replenishing every
paid loss while only current positions are tracked. The adopted repair — a limit
on cumulative net outflow — is precisely bounded enforcement liability.

**Proposed clause (provisional name: enforcement outflow limit).** The book
declares, per endorsement, a finite bound on the cumulative outflow its compiled
enforcement position may take across worlds the record still assesses. It is a
generalization of `P2` from the engine's exposure on book holdings to the book's
exposure through its own compiled force.

**Theorem shape it buys.** Statics + the clause ⟹ `B < ∞` ⟹ (conditional on the
live-world lift) nonexploitability with bound `1 + B`.

**What it means.** An endorsement may outrun the settled record — that is what an
endorsement is for — but the book must be willing to say in advance how much that
outrunning is allowed to cost, and to stop when the account is spent. It is the
same discipline the corpus already imposes on exposed content, applied to the
mechanism that gives endorsements operative force. `P1` says what force an
endorsement gets; the clause says how much damage granting it may do.

## 7. Two sufficient trajectory conditions, neither necessary

**Deficit route.** `Σ_t (ε_t + C_t)·‖d_t(ω)‖₁ / δ_t < ∞` over worlds live along
the trajectory. The safe fixture satisfies it by having finitely many nonzero
terms. Nothing shows it necessary.

**Support route.** `Σ_t (1 − θ_t(ω))·U_t / θ_t(ω) < ∞`, with `U_t` the position's
cube maximum gain. The motivating statics supply no lower bound on live-world
support capacity and no summable bound on `U_t`, so this route is **not**
discharged by them; it remains available to a source that supplies those
quantities. Nothing shows it necessary either.

## 8. What is not established

That the clause is necessary. That the deficit route is the best available.
That every natural settlement trajectory vindicates its endorsements — the unsafe
fixture is a settlement trajectory in good standing that simply never does.
Whether a revisable normative practice, which can raise `r` or reopen `m_c`, keeps
the depth non-increasing at all: **it need not**, and revision is outside the
live-world lift's nesting hypothesis for the same reason.

And the whole chain is conditional on the live-world Budgeter/TradingFirm lift,
which is `derived` and unformalized.
