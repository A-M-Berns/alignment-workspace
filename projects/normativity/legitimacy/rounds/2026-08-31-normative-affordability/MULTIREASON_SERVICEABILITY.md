# Timely service competes; persistence does not

## 1. Why the earlier result does not carry over

`CAUSAL_CAPACITY.md` §3 proved that the persistence region is the full power set of
the individually persistable reasons: splitting a lifetime budget geometrically
serves every one of them, because the persistence criterion `liminf_t L^r_t(1) = 0`
does not mention the budget.

That argument depends entirely on the criterion being **budget-free**, and it is
budget-free because persistence costs *nothing in the limit*: the geometric tranche
construction spends `B 2^{-(k+1)}` at the `k`-th cheap date, and the tranches can be
made as small as one likes.

Bounded-delay service is not like that. By `BOUNDED_DELAY_AFFORDABILITY.md` D4 the
minimum cost of serving a claim stream within delay `H` is a **fixed positive
number**

    Cost^r_{H_r}  =  sum_t c^r_t · min_{s in [t, t+H_r]} w^r_s ,

determined by the reason's claims, deadline and date weights. It does not shrink
when the budget does. So budgets add, and competition is immediate.

## 2. The theorem, and the counterexample it implies

**Theorem M1.** Suppose the reasons' date costs are independent — each reason's
enforcement charges its own rows and the charges add. Then a family `R` is jointly
serviceable on lifetime budget `B` if and only if

    sum_{r in R}  Cost^r_{H_r}  <=  B ,

and reason `r` is individually serviceable on `B` iff `Cost^r_{H_r} <= B`.

*Proof.* The costs are separable and the only coupling is the shared budget, so the
joint problem is the sum of the per-reason minima. `square`

**Corollary M2 (competition, and the smallest instance).** Two reasons with
`Cost^1 = Cost^2 = 3B/5` are each individually serviceable on `B` and are not
jointly serviceable, since `6B/5 > B`. Nothing subtler is needed, and nothing
subtler is available: with separable costs the joint criterion is one addition.

So the correction to the earlier reading is exact and it is not a caveat:

> **Unconstrained persistence does not compete, because it costs nothing in the
> limit. Timely service competes, because it costs a definite amount.**

## 3. What replaces a Hall condition

There is none to look for, in this model. A Hall-type condition arises when
resources are shared *structurally* — when serving one claimant consumes a slot
another needed. Here the liability budget is shared *scalarly*, and the force layer
supplies no shared slot at all: by `OVERLOAD_TARGET.md` N1 the per-row conformance
bound does not depend on how many rows are active. So the joint condition is a
single additive inequality rather than a family of subset inequalities.

That is worth stating because it inverts the usual scheduling intuition twice
over. Reasons do not contend for enforcement capacity; they contend only for
underwriting; and because the contention is scalar, the certificate of joint
infeasibility is a sum rather than a cut.

## 4. Where separability fails

M1's hypothesis is that the per-reason costs add. Three ways it can fail, none
resolved here.

**Shared rows.** If two reasons are served by the same row, one enforcement
position discharges both and the costs are subadditive rather than additive. Then
`sum_r Cost^r` overstates the joint cost, and joint serviceability can hold where
M1's test fails. The correct object is `Cost` of the union of the claim streams
against the shared row.

**Shared dates under strict concavity.** Past the sharp charge's branch point the
cost is strictly concave, so serving two reasons' claims at the *same* date is
cheaper than at two dates. Again subadditive, and again M1 is conservative.

**Policy-dependent weights.** If enforcing one reason changes the market's volume
or the live set, the other reason's weights move. That is the closed-loop problem
of `CLOSED_LOOP_EXISTENCE.md` E4 and nothing here applies to it.

In all three the failure is in the same direction — the additive test is
*sufficient* for joint serviceability and possibly not necessary — so M1 is safe to
use as a sufficient condition and unsafe as an impossibility certificate outside
the separable case.

## 5. What this does not establish

That the separable case is the common one; shared rows look likely in any real
docket. That there is no Hall condition in the non-separable case — there may well
be, and the subadditive structure is where to look. That `Cost^r` is computable
without knowing the reason's claim stream in advance, which
`ONLINE_SERVICEABILITY.md` shows is a real difficulty.
