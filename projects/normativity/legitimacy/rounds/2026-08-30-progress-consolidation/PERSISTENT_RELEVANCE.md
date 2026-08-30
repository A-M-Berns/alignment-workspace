# Persistent Relevance from service-interface fairness

## The gap Continuity intentionally leaves

Continuity proves unbounded service mass `A_N(m)` for a live matter. It does not say
which decision surface inside that matter is exposed. `Reach/Work` names the work
eligible for service; it does not by itself provide intra-matter fairness among
reason-specific answer surfaces. Attention theater therefore remains possible unless
the service interface adds one small scheduling contract.

For a reason `r`, let `e_n(r) in [0,1]` be the fraction of date `n`'s service that
exposes a recognized answer surface for `r`, and let `c_n(r)` be the confidence with
which the registered repair applies there. The simplest implementation sets
`c_n=e_n`; if semantic confidence is separate, require `c_n >= kappa e_n` on the
operative tail for some `kappa>0`.

## Surface Fairness, deficit form

> **Surface Fairness.** While `r` remains operative and unanswered, there are
> `eta>0`, `C<infinity`, and `N_0` such that for all `N>=N_0`,
>
> \[
> \sum_{N_0\le n<N}a_n e_n(r)
> \ge \eta\sum_{N_0\le n<N}a_n-C.
> \tag{SF}
> \]

If `c_n >= kappa e_n`, then

\[
W_N-W_{N_0}\ge \kappa\eta(A_N-A_{N_0})-\kappa C.
\]

Thus Continuity service `A_N -> infinity` implies Persistent Relevance
`W_N -> infinity`. The proof is a one-line comparison, but the hypothesis is
operational: a scheduler can expose and audit `e_n`.

## Concrete sufficient interfaces

### 1. Fixed surface on every service date

If every positive service to the owning issue exposes one registered surface and
`c_n>=c_*>0`, then

\[
W_N-W_{N_0}\ge c_*(A_N-A_{N_0}).
\]

This is strongest and easiest to implement. It is appropriate for a reason whose
answer mode is always available, such as recording an explicit acknowledgment.

### 2. Finite fair rotation

Suppose the issue has a fixed finite family of surfaces `J`, and `J(r) subseteq J`
is nonempty. Let `e_{n,j}` be service share assigned to surface `j`. A scheduler
provides, for each persistently owned `j`,

\[
\sum_{N_0\le n<N}a_ne_{n,j}\ge
\eta_j\sum_{N_0\le n<N}a_n-C_j.
\]

Choosing any `j in J(r)` with semantic confidence at least `kappa_j>0` proves
Persistent Relevance. A weighted round-robin or least-recently-exposed scheduler on
a fixed finite family gives this bounded-deficit form. The scheduler need not expose
every reason every date.

### 3. Owning work node

Register a reason-to-work-node ownership map

\[
owner_q(r)=z\in Work(q).
\]

Require that unresolved ownership persists, that service of `z` exposes a surface
for `r`, and that the intra-matter scheduler gives every persistent owned work node a
positive bounded-deficit share. Continuity supplies the live/reachable/work lifecycle;
this extra scheduler rule supplies the missing intra-matter allocation.

This version is preferable when a matter contains inquiry, adjudication and revision
subtasks that cannot all be exposed together.

### 4. Service-mass windows

For an atomic scheduler, calendar windows are misleading because a matter may not be
served in every period. Instead require that every block containing at least `L`
units of service mass to the matter allocates at least `eta L-C` to an answer surface
for `r`. Summing blocks yields `(SF)`. This is stable under intermittent matter-level
service.

## What does not suffice

- `A_N -> infinity` alone: all service may remain on an irrelevant surface.
- Mere membership of `r` in the reasons graph: representation does not schedule it.
- Exposure at infinitely many calendar dates: the exposed weights may be summable.
- A positive share with no lower bound: shares `2^{-n}` leave `W_N<infinity`.
- Fairness among matters: it says nothing about surfaces within one matter.

## Recommended interface

Use reason-to-work-node ownership plus bounded-deficit Surface Fairness as the
realization interface. Keep `(SF)` in the schematic theorem and prove it from the
scheduler in a realization lemma:

> **Surface Scheduling Lemma.** On a fixed finite episode, persistent ownership,
> positive semantic confidence and bounded-deficit service of every owned work node
> imply `(SF)` for every operative unanswered reason.

This is a small scheduler theorem, not a new liveness ontology.

