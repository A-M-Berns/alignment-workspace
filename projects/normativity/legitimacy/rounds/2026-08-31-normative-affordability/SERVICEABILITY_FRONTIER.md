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

    limsup_N  E_{mu^r_N}[d^r]   <=   L_r K_r F_r(a)  +  omega( H*(B) ) ,

which on the sharp linear branch is just `omega(H*(B))` by SS1. In general the right
object is the constrained residual

    R_H(B)  =  inf { F_r(a) : (a,T) has delay <= H and costs at most B } ,
    BestResidual(B)  =  inf_H [ L_r K_r R_H(B) + omega(H) ] ,

and `JOINT_SERVICEABILITY.md` is where that optimization lives.

`H*` is nonincreasing in `B`, so the residual is nonincreasing in `B`.

> **A larger liability budget buys a shorter affordable deadline, and a shorter
> deadline buys a smaller transport residual. Liability converts into semantic
> timeliness at the exchange rate `omega ∘ H*`.**

`tests/test_bounded_delay.py::TheCriticalDelay` computes `H*` exactly on a dip
sequence: at budget `1` no delay up to `2` is affordable; at budget `4` the least
affordable delay is `3`; and raising the budget to `70` brings it down.

## 3. Reading the two residuals

The fixed-era bound has two residuals and they are differently sourced — but not in
the way an earlier version of this section said.

`F_r(a)` is **schedule-dependent**. The misfit landscape `s^r_t(omega)` is supplied
by the norm and by settlement, and the residual is that landscape read against the
*service measure the scheduler chose*. Servicing a reason on dates where the norm is
nearly satisfied gives a small residual; servicing it on dates of deep exclusion does
not. The sentence claiming no scheduler touches it is withdrawn.

**And on the sharp charge's linear branch the scheduler does not have to try.** By
`SHARP_SERVICEABILITY.md` SS1 the friction numerator is exactly four times the
liability charge, so any affordable schedule with divergent allocation has
`F_r(a) = 0` at rate `4B/A_N`. In that regime the frontier below degenerates: the
only residual left is the transport one, and

    limsup_N E_{mu^r_N}[d^r]  <=  omega(H) .

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

**`H*(B)` can be infinite while eventual full service is affordable.** The weight
sequence of `EVENTUAL_VS_UNIFORM_SERVICE.md` E1 has divergent gaps between cheap
dates, so every fixed deadline misses unboundedly many claims while unbounded-delay
batching costs under `1/2`. A reason can therefore be *eventually answerable* and
*not timely answerable at any deadline*, which is a third regime beyond the two
below.

The interesting regime is the middle one, and it is the one the round had no
vocabulary for before: a reason can be *affordable* and *untimely*.

## 5. What this does not establish

That any reason type has a modulus `omega`. The inequality `(T3)` was always a
semantic hypothesis and this document only shows what a deadline buys *given* one;
`SERVICE_TRANSFER.md` §6 still records that no construction for the constants is
offered. That `omega` is the right shape — a reason whose defect can jump has
`omega` bounded away from zero and the frontier is flat, so the deadline buys
nothing. That `H*` is computable in the closed loop.
