# Affordable scheduling in authority space

## 1. The viability problem, correctly typed

State at date `t`: a service backlog `b_t in R_+^R` and the worldwise account
`V_{t-1}(·)` on the live set. The controller picks a predictable allocation `a_t`;
the engine then produces the fixed point, and the account moves reactively:

    b^r_{t+1}      =  [ b^r_t + c^r_{t+1} - a^r_t ]_+
    V_{t+1}(omega) =  V_t(omega) + sum_j a_{t,j} d_{t,j} ( d_{t,j} - s_{t,j}(omega) )

The two dynamics consume different inputs — the backlog a predictable one, the
account an endogenous one — and that asymmetry is the whole difficulty. A causal
policy is affordable when it keeps the backlog controlled (enough for the transport
plan of `SERVICE_TRANSFER.md`) and the account above `-B` at every horizon and every
live world.

## 2. Adding reasons is free in conformance and costly only in liability

The per-date modulus reads, **per row**,

    a_{t,j} d_{t,j}^2  <=  sum_i a_{t,i} d_{t,i}^2  <=  eps_t + M_t ,

so `d_{t,j} <= sqrt((eps_t + M_t)/a_{t,j})` with **no dependence on how many other
rows are active**. The source states the same consequence directly.

So there is no service-capacity competition in the conformance guarantee: a
hundred reasons each allocated `a` get the same tolerance as one reason allocated
`a`. Every form of overload in this theory is **liability overload**. That is worth
saying plainly, because the scheduling intuition imported from queueing —
a shared server, reasons contending for slots — does not apply to the force layer
at all. What is shared is the liability allowance.

## 3. A positive existence theorem, one reason

**Theorem S1.** Suppose `eps_t + M_t <= c` and the row's worst live exclusion
depth satisfies `s^+_t <= sigma_t`. If

    sum_t sqrt( a_t c ) · sigma_t  <=  B      and      sum_t a_t = infinity ,

then the schedule `a_t` is affordable and persistently serves the reason, and
`E_{nu^a_N}[d] = O( A_N^{-1/2} )` when a compatible live world exists.

*Proof.* The date's worst-case charge is
`a_t d_t s^+_t <= sqrt(a_t (eps_t+M_t)) · sigma_t <= sqrt(a_t c) sigma_t` by the
modulus, so the account never falls below `-B`; `A_N -> infinity` is the second
hypothesis; `FIXED_ERA_THEOREM.md` F2 supplies the rate. `square`

**Corollary S2 (explicit family).** With `a_t = t^p` and `sigma_t = t^{-q}` the two
conditions are `p >= -1` and `q > p/2 + 1`. So constant authority forever
(`p = 0`) needs only `q > 1`: **any exclusion depth decaying faster than `1/t`
supports unbounded persistent authority on a finite lifetime budget.** Growing
authority `p = 1` needs `q > 3/2`.

The mechanism is the square-root exposure relation: the charge is
`O(sqrt(a) · sigma)` rather than `O(a · sigma)`, because the authority buys
conformance precision and the position it actually takes shrinks as the violation
does. Doubling the authority costs `sqrt(2)` in exposure.

## 4. Many reasons: concentration beats splitting

The per-date liability allowance `b_t` is what reasons contend for. Splitting it as
`b_{t,r}` buys `a_{t,r} = b_{t,r}^2 / ((eps_t+M_t) D_{t,r}^2)` — **quadratic** in
the share. Two consequences.

**The per-date authority-capacity set is not convex.** With two rows at unit
budget and depth `1/2`, allocations `(4, 0)` and `(0, 4)` each cost allowance
exactly `1`, and their midpoint `(2, 2)` costs `2 · sqrt(1/2) = sqrt(2) > 1`. The
set `{ a >= 0 : sum_r sqrt(a_r (eps+M)) D_r <= b }` is the sublevel set of a
concave function and is star-shaped but not convex.
`tests/test_reasonwise.py::ConcentrationBeatsSplitting` pins the arithmetic.

**Time-sharing dominates proportional splitting by the number of reasons.** With
`R` reasons, allowance `1`, budget `1`, depth `1/2`: proportional splitting gives
each reason `(1/R)^2/(1/4) = 4/R^2` per date, so `4T/R^2` over `T` dates; round
robin gives each `4` on `T/R` dates, so `4T/R`. The ratio is exactly `R`, checked
at `R = 4`.

So the right policies here are **concentrating** ones — round robin, weighted fair
queueing over dates rather than within a date, max-weight on backlog — and the
reason is the convexity of the cap in the allowance, not any property of the
arrival process.

**Theorem S3 (many reasons, all persistent).** Let `R` be countable, with a
predictable allowance schedule `b_t` such that `sum_t b_t <= B`. Suppose each row's
depth decays fast enough that for a partition of the dates into infinitely many
infinite classes `T_1, T_2, ...`, `sum_{t in T_r} b_t^2/((eps_t+M_t) D_{t,r}^2) =
infinity`. Then round-robin over the classes gives `A^r_N -> infinity` for every
`r` while SafeCert holds at `B`.

`tests/test_reasonwise.py::DivergentServiceOnAFiniteBudget` exhibits three reasons
with allowance `1/(t+1)^2` — summable to under `2` — and depth `4^{-(t+1)}`,
whose allocated service exceeds `10^12` for every reason by date 480 and keeps
growing.

The condition is a joint one on the allowance schedule and the depths, and it can
fail: if a row's depth is bounded below, its cap is `O(b_t^2)`, which is summable
whenever `b_t` is, so that row cannot be persistently served under Route A at all.
**A reason whose norm permanently excludes a live world by a fixed depth cannot be
persistently enforced on a finite conservative budget.** That is the sharp negative
statement, and it is the correct form of the intuition the round earlier
misstated as "persistent service must be self-financing".

## 5. Signed-account scheduling strictly enlarges the region

Route B of `CAPACITY_VS_SAFETY.md` spends the realized slack rather than an
exogenous split. It strictly dominates: a date on which the account earns `g`
raises the next date's cap from `(B/2)^2/(cD^2)` to `(B+g)^2/(cD^2)`, a factor of
`(2(B+g)/B)^2`. At `B = 1`, `g = 1/4`, budget `1`, depth `1/2` the caps are `1` and
`25/4`.

Whether the account earns is not the scheduler's choice: it earns exactly when
`d_t > s_t(omega)`, that is when the reasoner is further from the norm than the
world is. So Route B's extra capacity is real but is supplied by the engine's
non-compliance, and it disappears as conformance improves. A policy relying on it
must be prepared to stall.

## 6. The capacity region

Define the **sustainable authority-rate region**

    A  =  { lambda in R_+^R : some causal policy achieves
            liminf_N A^r_N / N >= lambda_r for every r, with SafeCert }.

Three properties follow from §4.

**Downward closed.** Allocating less is always feasible; `a = 0` costs nothing.

**Its per-date generator is not convex**, by §4, so the natural LP/Farkas
machinery does not apply date by date.

**`A` itself is convex**, because time-sharing between two policies achieves any
convex combination of their long-run rates, and SafeCert is preserved by
interleaving when the budgets are interleaved with them. So `A` is the convex hull
of the per-date generator's achievable long-run rates, and **the convexification is
performed by the schedule, not assumed of the geometry.** That is the formal object
"normative capacity" should name, and the useful slack notion is a demand rate in
its interior.

## 7. Overload, refined but not solved

The primal is now clean enough to say what a dual would have to do, and not clean
enough to build one.

A per-path Farkas certificate remains sound and incomplete, and §4 adds a second
reason it is the wrong shape: the per-date feasible set is non-convex, so a
separating hyperplane does not exist per date even before the causal quantifier
appears. Convexity is recovered only asymptotically, by time-sharing.

What a complete certificate has to separate is a **claim/service load** from the
**causal safe authority capacity** — a rate vector from the region `A` — and the
witness must survive the adversary's choice of settlement path. The candidate
objects, in the order they look plausible: a potential on the state
`(backlog, account slack)` that decreases along every admissible allocation and
starts below what the load demands; equivalently a supermartingale over the live
set when the settlement process is given a measure. A flow or cut cannot see the
signed account, since a cut is a sum of per-date capacities and the account is not.
No theorem is claimed and no name is coined.

## 8. What Answerability should export

Not a schedule, and not a scalar quota.

> Answerability exports the claim stream together with the set of **admissible
> service traces**; affordability selects a safe trace from that set.

This is consistent with the transport machinery, and in fact is what the transport
machinery already is: a plan `T^r(t,s)` matching claim mass to allocated service is
precisely a choice of trace, and the constraints Answerability wants — deadlines,
ordering, minimum cumulative allocation `A^r_N >= F(C^r_N) - O(1)` — are
constraints on which plans are admissible. Keeping the adjudication of *which*
traces are owed inside Answerability and the choice of *which admissible trace to
run* inside affordability is the split that keeps normative content out of the
scheduler.

The derived scalar interface — a lower bound on cumulative allocation as a function
of cumulative claims — is a useful summary of a trace family and the right input to
§3 and §4, but it is a summary, not the primitive.

## 9. Open

1. Existence against an adversarial docket: §4's theorem fixes the depths and the
   allowance schedule in advance. With arrivals and depths chosen adversarially and
   predictably observable, does a policy achieving every persistent reason's
   divergence exist whenever the demand is in the interior of `A`?
2. Is `A` nonempty above zero for a docket a practice actually produces? This is
   the non-vacuity question and it needs §4's depth-decay condition to hold for
   real endorsements — the round's statics generate such trajectories for affine
   demands and not for sentence-shaped ones.
3. Does Route B's adaptive region admit a stationary characterization, or does its
   dependence on the realized account make the sustainable region policy-dependent?
4. The dual, per §7.
