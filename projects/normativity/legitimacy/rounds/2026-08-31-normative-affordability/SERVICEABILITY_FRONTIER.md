# The serviceability frontier: liability against timeliness

## 1. What the deadline buys

The fixed-era composition does not require bounded delay for its own sake. It
requires the transport stability inequality `d_t <= L d_s + eps` whenever claim `t`
is serviced at `s`. Bounded delay is one way to get it, and it is the way that
converts a semantic obligation into a scheduling parameter.

**Assume temporal regularity.** Suppose the reason's defect has a modulus of
continuity in time: `|d_t - d_s| <= omega(|s - t|)` with `omega` nondecreasing and
`omega(0) = 0`. Then a plan with delay at most `H` satisfies

    d_t  <=  d_s + omega(H) ,

which is `(T3)` with `L_r = 1` and `eps_r = omega(H)`.

So the transport residual of `FIXED_ERA_THEOREM.md` F3 is *not* a free parameter: it
is the modulus evaluated at the deadline the scheduler could afford.

## 2. The frontier

Two monotonicities, in opposite directions.

**`Cost_H` is nonincreasing in `H`.** A wider window is a superset, so every
sliding-window minimum can only fall. Checked over delays `0` through `5` on a dip
sequence.

**`omega(H)` is nondecreasing in `H`**, by assumption.

Hence the affordable delays form an up-set and there is a least one.

**Definition.** `H*(B) = min { H : Cost_H(c) <= B }`, and `infinity` if no delay is
affordable.

**Theorem SF1 (serviceability frontier).** If `H*(B) < infinity` then there is a
bounded-delay plan at `H*(B)` costing at most `B`, and the fixed-era theorem gives,
for that reason,

    limsup_N  E_{mu^r_N}[d^r]   <=   L_r K_r F_r  +  omega( H*(B) ) .

`H*` is nonincreasing in `B`, so the residual is nonincreasing in `B`.

> **A larger liability budget buys a shorter affordable deadline, and a shorter
> deadline buys a smaller transport residual. Liability converts into semantic
> timeliness at the exchange rate `omega ∘ H*`.**

`tests/test_bounded_delay.py::TheCriticalDelay` computes `H*` exactly on a dip
sequence: at budget `1` no delay up to `2` is affordable; at budget `4` the least
affordable delay is `3`; and raising the budget to `70` brings it down.

## 3. Reading the two residuals

The fixed-era bound has two residuals and they are now differently sourced.

`F_r`, the **settlement-friction residual**, is the norm's own weighted
mean-square exclusion of the still-live worlds. No scheduler touches it and no
budget buys it down. It is a property of the norm against what can still be true.

`omega(H*(B))`, the **transport residual**, is now *purchasable*. It is the price of
the deadline the budget could afford, and it falls as the budget rises or as the
cheap dates get denser.

That asymmetry is the useful content: of the two ways a claim-weighted Progress
statement is weakened, exactly one is a resource question.

## 4. Where the frontier is degenerate

**If the norm's cheap dates are dense**, `H*(B)` is small for modest `B` and the
transport residual is `omega` of a small number. This is the good regime and it is
what a well-behaved reason looks like: enforcing it is nearly free often enough that
timely service is affordable.

**If the cheap dates are sparse but exist**, `H*(B)` is large — of the order of the
dip spacing — and the residual is `omega` at that spacing. The reason is
persistently enforceable and not *timely* enforceable, which is exactly the
separation of `BOUNDED_DELAY_AFFORDABILITY.md` §6.

**If the friction is floored**, `Cost_H` is infinite at every `H` — every claim pays
at least the floor and there are infinitely many — so `H*(B) = infinity` and there
is no bounded-delay plan at any budget. Unconstrained persistence also fails here,
so this regime is not new.

The interesting regime is the middle one, and it is the one the round had no
vocabulary for before: a reason can be *affordable* and *untimely*.

## 5. What this does not establish

That any reason type has a modulus `omega`. The inequality `(T3)` was always a
semantic hypothesis and this document only shows what a deadline buys *given* one;
`SERVICE_TRANSFER.md` §6 still records that no construction for the constants is
offered. That `omega` is the right shape — a reason whose defect can jump has
`omega` bounded away from zero and the frontier is flat, so the deadline buys
nothing. That `H*` is computable in the closed loop.
