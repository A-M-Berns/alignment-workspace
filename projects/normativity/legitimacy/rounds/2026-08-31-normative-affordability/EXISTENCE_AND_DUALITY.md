# Affordability existence, and overload certificates

## 1. The viability problem

The composition theorem consumes a witness. Existence is a causal game.

State at date `n`: a backlog vector `b_n in R_+^R` of unserviced claim mass, an
account `a_n`, and whatever local state determines `J_n`. The controller picks
`(w_n, u_n) in J_n(h_{n-1})`; the exterior then settles, producing new claims
`c_{n+1}` and resolving the round's exposure. Dynamics:

    b_{n+1}^r = max(0, b_n^r + c_{n+1}^r - w_n^r) ,
    a_{n+1}   = a_n - l_n(w_n, xi_{n+1}) .

The objective is simultaneous: **service fidelity** and **settlement-relative
safety**.

Fidelity is stated on the backlog rather than on measures, and the translation is
the one place a scheduling condition earns its keep.

**Lemma E1.** If the backlog is bounded — `b^r_n <= beta` for all `n` — then FIFO
matching of claim mass to service defines an adapted transport plan `T^r` with
`(T1)`–`(T2)` and residual density `<= beta / C^r_N -> 0`. If in addition every
window of `W` consecutive dates delivers at least `s > 0` service to `r`, the plan
is supported within delay `W(1 + beta/s)` of the diagonal.

*Proof.* FIFO assigns each unit of claim mass the service unit that clears it;
`(T2)` holds because each service unit clears at most itself, and the unmatched
mass at horizon `N` is exactly `b^r_N <= beta`. Under the window condition a unit
waits behind at most `beta` units of backlog, which clear within
`ceil(beta/s)` windows. `square`

So bounded backlog supplies `(T1)`–`(T2)` and the delay bound; `(T3)` remains a
semantic obligation on the reason and no scheduler supplies it. This is the exact
division of labour the dispatch asked about between queue conditions and
contiguity.

## 2. A fixed budget funds only a transient

The safety constraint is `a_n >= -B` for a *fixed* `B`, robustly over the live
assessment set. Sustaining service forever therefore cannot cost anything forever.

**Observation E2.** If every admissible control servicing `r` has robust liability
increment bounded below by `delta > 0` — that is,
`sup_{W in Assess} -W(l_n(w)) >= delta` whenever `w^r > 0` — then the total mass
ever served to `r` is at most `B/delta`, so `W^r_N` is bounded and `r` cannot be
persistently relevant.

The consequence is structural. **Persistent service must be self-financing.**
Write

    Z_n(h) = { w in J_n(h) : sup_{W in Assess(h)} -W(l_n(w)) <= 0 }

for the self-financing controls: those whose exposure is nonnegative in every live
assessment. The budget `B` funds departures from `Z`, and departures are
necessarily transient. This is why the liability theory's covered-underwriting
condition turns up here: a barycenter admitted by every active row makes the
projection portfolio's value nonnegative on a `theta`-covered mixture, which is
exactly what puts a control in `Z` up to the coverage discount `U(1-theta)/theta`.
Affordability existence and covered underwriting are the same question asked
prospectively and retrospectively.

## 3. Theorem T7 (a sufficient condition, drift form)

**Theorem T7 (proof sketch; not machine-checked).** Suppose

1. `J_n(h)` is convex and compact with `0 in J_n(h)` — automatic for the minimal
   type of `JOINT_ACTIONABILITY.md` §6 when the control set is a convex body;
2. `l_n` is convex in `w` with `l_n(0) = 0`, so `Z_n(h)` is convex and contains
   `0`;
3. claims arrive at bounded rate, `c^r_n <= c_max`;
4. **self-financing slack**: there are `eta > 0` and, at every reachable history,
   a control `v in Z_n(h)` with `v^r >= (1 + eta) c_max` for every persistent `r`.

Then the max-weight policy `w_n in argmax { <b_n, w> : w in Z_n(h_{n-1}) }` keeps
the backlog bounded and the account nondecreasing. A witness exists, with `B = 0`.

*Proof sketch.* Safety is immediate: every chosen control lies in `Z`, so the
robust account never decreases. For fidelity take `V(b) = |b|^2 / 2`. From the
dynamics, `V(b_{n+1}) - V(b_n) <= <b_n, c_{n+1} - w_n> + (|c_{n+1}| + |w_n|)^2 / 2`.
The max-weight choice gives `<b_n, w_n> >= <b_n, v> >= (1 + eta) c_max |b_n|_1 >=
(1 + eta) <b_n, c_{n+1}>`, so the drift is at most
`-eta <b_n, c_{n+1}> + M` for a constant `M` depending on `c_max` and the diameter
of `J`. The drift is negative outside a bounded set, and the increments are
bounded, so the backlog is confined to a bounded set. Lemma E1 converts this into
the transport plan. `square`

Condition 4 is the one with content, and it is a *joint* condition: it asks for a
single self-financing control that outpaces the arrival rate of every persistent
reason at once. Its failure is exactly overload, which is §4.

Of the sufficient conditions the dispatch lists, this identifies which are
structure the traderization already supplies and which are hypotheses. Convex
local response sets: supplied, by the minimal type. Convex safe regions: supplied,
by convexity of the liability functional in the position. Linear aggregation:
supplied, positions add. Bounded arrival rates and slack/interiority: **not**
supplied — they are hypotheses about the normative load, and they are where
affordability can fail.

## 4. Theorem T8 (finite-horizon overload certificates)

Fix a horizon `N` and one settlement-consistent path, so the round data are known.
The affordability program is

    choose  w_t in J_t = conv(V_t) ,  t < N ,
    s.t.    sum_t w_t^r >= demand_r          (service fidelity)
            sum_t <cost_t, w_t> <= B         (settlement-relative safety).

**Theorem T8.** If there are `y >= 0` and `z >= 0` with

    deficit(y, z) = <y, demand> - z B
                    - sum_t max_{v in V_t} ( <y, v> - z <cost_t, v> )  >  0 ,

the program is infeasible.

*Proof.* For feasible `w`, `<y, sum_t w_t> >= <y, demand>` and
`z sum_t <cost_t, w_t> <= z B`, so
`sum_t ( <y, w_t> - z <cost_t, w_t> ) >= <y, demand> - z B`. Each summand is at
most the maximum over `V_t`, because `w_t in conv(V_t)` and the summand is linear.
Contradiction. `square`

The pair `(y, z)` is an **overload certificate**: a weighting of the reasons and a
price on liability under which the total jointly-actionable, safely-financeable
service available over the horizon is worth strictly less than what is owed. Two
instances, exact in `tests/test_overload.py`:

- *capacity overload*: one round, two unit demands, `y = (1,1)`, `z = 0`, deficit
  `1` — no liability price is needed, the round simply cannot serve both;
- *liability overload*: two rounds, two unit demands, unit cost per unit served,
  budget `1`; `y = (1,1)`, `z = 1`, deficit `1`. Here `z = 0` certifies nothing
  (deficit `0`), so the certificate genuinely needs the liability price. Raising
  the budget to `2` makes the instance affordable, a primal witness is exhibited,
  and no multiplier pair on a rational grid produces a positive deficit.

**Soundness and completeness.** T8 is sound for the causal problem in the
direction that matters: a causal policy induces, on each settlement-consistent
path, a feasible point of that path's program, so a certificate for *any* live
path refutes affordability outright. Completeness fails: the relaxation gives the
controller the path in advance, so a program that is feasible on every path
separately may still admit no causal policy. Under a Slater point the per-path
program has strong duality and the certificate is exact *for that program*; no
exact alternative for the dynamic problem is offered here, and the dispatch's
speculative "either a service-faithful safe controller or a checkable overload
certificate" is therefore **not** established as a dichotomy. What is established
is one sound half.

The workspace already has the synchronic half of this: covered-compatibility
duality's unsupported-authority certificate is T8 restricted to a single round
with no service demands and the rows read as compatibility constraints. T8 adds
the scheduling dimension — a demand accumulated over a horizon, and a budget spent
across rounds — and the two agree where they overlap, since a one-round instance
with `z = 0` is a pure row-conflict certificate.

## 5. Feeding a certificate back into Answerability

A verified certificate is a finite object: the multipliers, the round data it was
computed against, and the reason identifiers whose demands it prices. It is
therefore settleable. The protocol this suggests — and it is a protocol proposal,
not a consequence of T8 — is that overload is recorded as an authenticated event
citing `(y, z)` and the priced reasons, so that a reason whose service is
suspended has a receipt naming what displaced it and at what liability price. That
is the difference between an unaffordable claim and a dropped one: the first has a
record with a respondent, the second has nothing.

The adjudication interface the liability round proposes for the synchronic
certificate applies unchanged: permissible answers are priority adjudication,
inquiry, a justified revision of the settlement model, or a controlled enforcement
schedule. Silently dropping a reason is not one of them, and neither is enforcing
everything at full authority on the strength of a receipt that says the opposite.

## 6. What this section does not establish

T7 is a proof sketch with a standard drift argument; it is not machine-checked and
no fixture inhabits its full hypothesis package. Lemma E1's delay bound assumes a
window service floor that T7 does not establish. T8's converse is open and is the
main unresolved question this round leaves. Whether condition 4 of T7 is ever
satisfiable in a traderized instance with unboundedly many live reasons is not
addressed.
