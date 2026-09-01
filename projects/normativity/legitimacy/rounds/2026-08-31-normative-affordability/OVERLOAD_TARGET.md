# Two failures, and the certificate each one needs

## 1. Normative infeasibility

The force layer cannot act at all. Its instances are prior to any question of
cost:

- the joint normative region is empty, so the enforcement inequality has no
  region point to evaluate at and there is no positive work term;
- a row is unpriceable — its violation is not a functional of what the market
  displays, so no trading strategy can respond to it;
- the compiled control is not a legal strategy, or not continuous, so the market
  maker's fixed point argument does not apply;
- the service timing Answerability demands has no admissible transport plan.

These are **semantic or structural** failures. They are detected before the
account is consulted, and their certificates are ordinary: a Farkas pair for an
empty region, a failure of the priceability solve, a plan-marginal infeasibility.
The workspace already carries the first as the unsupported-authority certificate of
covered-compatibility duality.

## 2. Normative insolvency

The load is force-feasible and no causal policy can service it while keeping the
account viable. This is a statement about **underwriting capacity over time**, and
it is the one with no certificate yet.

The distinction matters at the interface: an overload event fed back to
Answerability should say which of the two occurred, because the permissible
responses differ. Infeasibility asks for adjudication between conflicting demands
or for a revision of the settlement model. Insolvency asks for priority, deferral,
or a controlled schedule — the demands are individually fine and collectively
unaffordable.

## 3. The lemma the round had stated too broadly

The previous pass wrote that every form of overload here is liability overload.
That is right only after force feasibility is granted, and the correct statement is
narrower.

**Lemma N1 (no conformance competition).** Conditional on force feasibility, the
enforcement modulus gives, for every active row `j` at date `t`,

    d_{t,j}  <=  sqrt( (eps_t + M_t) / a_{t,j} ) ,

with no dependence on how many other rows are active.

*Proof.* `a_{t,j} d_{t,j}^2 <= sum_i a_{t,i} d_{t,i}^2 <= eps_t + M_t`, the middle
sum being over nonnegative terms. `square`

So adding reasons consumes **underwriting**, not a finite total of enforcement
force: a hundred reasons each allocated `a` get the tolerance one reason allocated
`a` would get. The queueing picture of reasons contending for a shared server does
not describe the force layer. What it does describe, correctly, is the liability
allowance, which is shared and whose division is quadratic in effect.

N1 is conditional. Where force feasibility fails there is no tolerance to talk
about, and the failure is §1's, not §2's.

## 4. What an insolvency certificate would have to do

The primal, from `CAUSAL_CAPACITY.md` and `PERSISTENT_AFFORDABILITY.md`:

    state:      (service state z_t, account profile V_t on the live set)
    control:    predictable a_t, hence the compiled law kappa_t
    dynamics:   the engine returns d_t at the fixed point; settlement shrinks the
                live set; V_{t+1}(omega) = V_t(omega) + sum_j a_{t,j} d_{t,j}
                                                        (d_{t,j} - s_{t,j}(omega))
    requirement: the service trace is admissible under Answerability, every
                persistent reason has A^r_N -> infinity, and V_N(omega) >= -B for
                every N and every live omega.

Affordability existence is `exists pi forall admissible exterior histories`, and
insolvency is its negation: `forall pi exists a history` on which the requirement
fails.

Three things follow about the certificate's shape, and they are constraints rather
than a construction.

**It cannot be a flow or a cut.** A cut is a sum of per-date capacities; the
binding resource is a signed cumulative account, and `SIGNED_VS_CONSERVATIVE.md`
exhibits a trajectory where every per-date worst case is positive and the account
is identically zero. Per-date capacities cannot see that.

**It cannot be a per-path Farkas certificate.** Those are sound and incomplete, and
`CAUSAL_CAPACITY.md` §1 adds a second reason: the per-date feasible set in
authority space is non-convex, so a separating hyperplane does not exist per date
even before the causal quantifier appears. Convexity appears only in the flow model
of C1.

**It has to carry the account profile, not a scalar.** `CAUSAL_CAPACITY.md` §5
shows the minimum over live worlds is not a sufficient statistic, because the
argmin world can settle away. So a value function or potential has to be defined on
profiles over the live set, whose dimension is the size of that set.

The remaining candidate is therefore a **potential on `(z, V)`** whose decrease
along every admissible allocation is too small to discharge the incoming load — a
viability-kernel emptiness witness, equivalently a supermartingale when the
settlement process carries a measure. That is the exact dual problem to state; no
theorem is claimed, and the object is not named.

## 5. What the existence results settle, and what they do not certify

The insolvency question is answered *mathematically* for the exogenous benchmark,
and that is not the same as being certifiable.

- **One reason:** insolvent iff `liminf_t L^r_t(1) > 0` — `liminf q^r_t > 0` under
  the conservative charge, `liminf s^r_t > 0` under the sharp one in the normal
  regime.
- **Countably many reasons:** insolvent for `r` iff insolvent for `r` alone, since
  persistence does not compete under exogenous independent frictions. So there is no
  *joint* insolvency beyond the per-reason ones, and no Hall-type obstruction.

**But `liminf > 0` is a claim about the infinite future, and no finite prefix
establishes it.** A scheduler that has observed `L_t(1) >= q_0` for a thousand dates
has observed exactly that and nothing about date one thousand and one. The earlier
sentence calling the friction floor "as checkable as a certificate gets" is
withdrawn: a single number is the *content* of the certificate, not the certificate.

An authenticated insolvency certificate therefore has two parts:

    (T, q_0)        the claimed tail bound: L_t(1) >= q_0 for all t >= T
    a proof object  establishing the universal tail statement

and the second part has to come from somewhere other than observation — from the
settlement model, from a monotonicity argument about how the live set can shrink,
from a symbolic property of the row, or from a theorem about the docket. Where no
such object exists, insolvency may be **true but not settleably certified**, and the
record should say so rather than record a floor as if it were a proof.

This is the same discipline the round applies elsewhere: a reason is not dropped
because a scheduler predicts it will become unaffordable. An observed floor licenses
deferral and an inquiry into whether the floor is permanent; only a proved tail
bound licenses recording the reason as unaffordable.

What a dynamic dual would still be for: the **rate** problem, where the
finite-horizon frontier is non-convex and reasons genuinely contend; the **signed**
class, where no criterion in terms of the friction sequence can exist; the
**service-admissible** problem, where a per-window floor turns the dip criterion
into a summability one; and **closed-loop friction**, where the docket and the
market respond to the scheduler.

## 6. Feeding it back

An insolvency event should carry `(T, q_0)`, the rows it applies to, **and** the
proof object for the tail bound; without the third it is an observation with a
deferral attached rather than a settled impossibility. An infeasibility event should
carry its own certificate — the unsupported-authority multipliers, or the failed
priceability solve — and those are genuinely finite, which is the asymmetry between
the two failures worth recording.

Both are settleable records rather than silent drops, which is the property the
round wanted from an overload certificate in the first place. The response protocol
is unchanged and remains a proposal rather than a consequence.
