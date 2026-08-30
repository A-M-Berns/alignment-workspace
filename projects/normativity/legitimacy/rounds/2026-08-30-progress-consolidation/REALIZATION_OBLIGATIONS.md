# Concrete realization obligations

## Interface map

| schematic object | concrete candidate | status |
| --- | --- | --- |
| reason occurrence and episode | reasons multihypergraph node with Continuity owner | interface exists; compiler missing |
| finite service alphabet | episode-local service-response labels | realization requirement |
| Answer-Mode certificate | typed reason/protocol schema plus provenance | missing compiler theorem |
| `K_n` | nonempty rational polytope over value-security coordinates | projection input supported |
| robust gain certificate | finite conic rows / LP dual proof object | mathematics available; graph record design missing |
| `dist_infty(hat v,K)<=tau` | rational constraint schedule projection | available per date |
| weighted vanishing error | vanishing rational tolerances plus weighted Cesaro | elementary bridge lemma |
| Uptake | finite confidence-rated causal modification regret | standard ingredients; exact package missing |
| market safety | bounded assessed liability of projection enforcer | preservation theorem available conditionally |
| row legitimacy | Operative Row Grounding | conditional theorem from Grounded Replay |
| successor integrity | Reason Carry plus fresh successor authorization | realization requirement |

## Reason-to-value compiler

The smallest typed compiler accepts only reason targets with declared answer-mode
semantics:

```text
ActionCompare(source, answer, margin)
InquiryDuty(ignore, inquiry-modes, margin, feasibility-test)
AdjudicationDuty(silent-conflict, adjudication-modes, margin)
DefeaterDuty(ignore-defeater, assessment-modes, margin)
RevisionDuty(silent-reset, explicit-revision-modes, margin)
```

At `H_n` it:

1. checks episode ownership, applicability, feasibility and current/anchored license;
2. ignores defeated or withdrawn occurrences without deleting their history;
3. emits rational affine rows annotated with reason id, schema id, license and source
   surface;
4. checks the cube plus all rows for nonemptiness;
5. if inconsistent, emits no silent subset: it opens a Continuity conflict issue and
   withholds the conflicting constraint set until an explicit priority, defeater or
   conditional face resolves it;
6. compiles local reasons only under their predictable applicability guard. A face
   restriction is a new response surface, not a global row retroactively imposed on
   all service dates.

The compiler theorem still missing is:

> **Answer-Mode Compilation.** Every accepted typed certificate compiles to a
> nonempty rational polytope and a finite repair kernel whose conic rows imply the
> certificate's Sensitivity inequality, with all emitted rows retaining source and
> license provenance.

Nonemptiness cannot be hidden in projection: `RationalPolytope` already requires it.

## Dual certificates

For `K={v:Gv>=h}` and repair direction `c`, a record

\[
\lambda\ge0,\qquad G^T\lambda=c,\qquad h^T\lambda\ge\gamma
\]

certifies `inf_{v in K} c^T v>=gamma`. Store this as a **derived certificate attached
to the repair edge**, citing the source reason rows. It is neither a new primitive
reason occurrence nor a self-licensing graph node. It may be exposed as a proof object
in the service protocol, but its authority is inherited from cited rows.

Bounded cube coordinates and a nonempty rational polytope give finite rational LP
certificates in the intended fragment. The conic kernel lemma often avoids solving a
general LP because the requisite rows are already explicit.

## Traderized Value Realization Lemma

The eventual theorem should state:

> Let a strict-prefix compiler produce, at every date, a finite coordinate list, a
> nonempty rational polytope `K_n subseteq [0,1]^{X_n}`, and a positive rational
> tolerance `tau_n`. The canonical projection market has a point
> `tilde v_n in K_n` with
> `||hat v_n-tilde v_n||_infty<=tau_n`. If `tau_n->0`, then for every predictable
> `w_n in [0,1]` with `W_N->infinity`, the service-weighted projection error vanishes.

The first sentence is already supplied by
`RationalConstraintSchedule.criterion_of_constraints` (or Euclidean
`conformance_of_constraints`) plus `sup_conformance_of_dist2`. The second is an
elementary weighted-Cesaro lemma. Arbitrarily changing `K_n` and finite coordinate
lists are supported. Computability of the canonical representation remains subject
to the schedule's effective representation interface when the full Logical-Inductor
claim, rather than conformance alone, is required.

## Liability audit

The exact existing preservation theorem is
`EnforcementPreservation.no_efficient_trader_exploits`: if the added enforcer's
assessed cumulative net worth is uniformly bounded below by `-B` at every live
assessed world, the modified market preserves the generalized LI non-exploitation
criterion.

Projection gives three relevant sufficient routes:

1. **World inclusion:** if every live assessed world's service-value vector belongs
   to every date's `K_n`, `ProjectionBudget.cumValue_nonneg_of_forall_mem` gives zero
   liability.
2. **Summable geometric charge:** generic projection liability or a homothetic core
   plus a uniform bound on accumulated charges gives bounded liability;
   `ProjectionCore.core_netWorth_ge_of_summable` explicitly requires the partial-sum
   bound. A positive core alone is insufficient.
3. **Certified settlement semantics:** episode-local securities may settle only at
   vectors admitted by the anchored evaluator. This reduces to route 1, but risks
   baking normative constraints into settlement and therefore requires an independent
   settlement-legitimacy theorem.

PR #50, `2026-08-24-enforcement-affordability` at open-PR head `fa22b8a`, adds a
fourth, genuinely useful candidate route:

4. **War-chest affordability:** in its one-coordinate model, a stationary interior
   peg has tolerance-independent bounded liability when it is contained in the
   deductive region, has a uniform positive plausibility margin, and opposing flow
   cannot receive cross-coordinate subsidy. Its proposed moving-region extension
   replaces stationarity by a summable set-gap path and retains a positive margin.

This route matters because it permits a normative constraint to exclude live
valuations; it is not merely the zero-liability world-inclusion case. A pairwise row
can sometimes be isolated as one derived difference security, so it gives a plausible
restricted realization of a single Answer-Mode certificate.

The qualification is load-bearing. PR50 is an open, unregistered research artifact,
not a theorem of record. Its continuation says six of eight proof steps lack Contrib
support. More importantly, its two-coordinate witness lets losses on a moving
unconstrained coordinate refill the opposition's war chest and drive a static,
perfectly margined peg's liability geometrically. The multi-coordinate joint-margin
problem is explicitly left open. A general service response alphabet and several
simultaneous repair rows therefore do not satisfy PR50's hypotheses automatically.

Compiled service-value constraints do **not** automatically satisfy any route.
A strict row `v(y)-v(x)>=gamma` excludes a live world whose anchored settlements rank
`x` above `y`; repeated projection can then accumulate unbounded assessed loss.
Changing polytopes and later evaluator disagreement do not erase accrued liability.
Tight margins and tolerances do not cure this. Conflicting rows make `K_n` empty and
must be diverted before enforcement.

The missing theorem is therefore substantive, but PR50 splits it into a restricted
promotion target and a general open target:

> **Restricted Service-Value Affordability.** For one isolated derived repair
> coordinate, prove the PR50 war-chest bound from stationary interior margin (or a
> summable set-gap path), deductive containment and an explicit no-subsidy/fenced-flow
> condition, then feed that bound to
> `EnforcementPreservation.no_efficient_trader_exploits`.
>
> **General Service-Value Liability Theorem.** Replace coordinate isolation by a
> multi-coordinate joint-margin or other non-recycling condition and prove a uniform
> cumulative bound for the full compiled repair family.

World inclusion proves a useful restricted case and is used by the toy model. For
contestable evaluator-score securities, PR50 gives serious evidence for the first
restricted affordability theorem but also supplies a necessity witness against naive
composition. Existing traderization/liability results provide the conditional
composition; neither the PR50 model nor current Contrib proves the general premise.

## Operative Row Grounding

Let `birth(q)` be the episode opening date. An operative row record at date `n` must
cite either:

- a current license `lambda in L_n`; or
- an episode-anchored license `lambda in L_birth(q)` for the same continuing episode.

In both cases the compiler records `lambda in Adm_n`. Normative Continuity's
`grounded_replay_admitted` then gives finite Grounded Replay ancestry for `lambda`.
Hence:

\[
row\ operative\Longrightarrow
licensed\ occurrence\Longrightarrow
grounded\ authority\ ancestry.
\]

Removed authority may continue governing an already anchored episode only through
the recorded historical admission rule. A successor `q'` must obtain a fresh current
license at `birth(q')`; reason translation does not transport authority by itself.
This is a genuine downstream consumer of Grounded Replay. It proves provenance, not
Proper Exercise or truth of the row.

## Reason Carry

For an unresolved eligible reason at a successor transition require

\[
r@q\ unresolved,\ q\to q'
\Longrightarrow Disposition(r)\ \lor\ Translate(r,r',q').
\]

The cheap **burden carry** record preserves predecessor identity/provenance, unresolved
burden status, declared answer-mode and surface mapping, and the need for a fresh
successor license. It need not preserve the numerical comparison. **Comparison
invariance** additionally proves that the surface map transports the repair and
margin; it is optional and stronger. Cross-era progress remains deferred.

Reason Carry should be a basic realization requirement because it prevents silent
reason shedding at one transition. It does not make infinite revision a stagnant
tail or justify dynamic regret.

## Richer joint-satisfiability toy

Use the service alphabet

\[
X=\{repeat,mitigate,ignore,investigate\}.
\]

Episode `q_0` has an action reason `repeat -> mitigate`, an inquiry reason
`ignore -> investigate`, and an old contrary reason. At an explicit evaluator
revision `q_0 -> q_1`, the contrary reason is defeated, while the two unresolved
reasons are translated with provenance and freshly licensed. In `q_1` compile

\[
v(mitigate)-v(repeat)\ge1/3,
\qquad
v(investigate)-v(ignore)\ge1/4.
\]

The vector `(1/5,3/5,1/10,1/2)` is in the cube and satisfies both, so `K` is nonempty.
Let the scheduler allocate confidence/exposure `1/2` to each reason on every unit of
matter service. Then `W_N=A_N/2`. Let `tau_n=1/(n+1)` and choose settlements equal to
the displayed admitted vector; world inclusion gives zero liability.

A finite repair learner registers the two pairwise maps and, on this toy loss stream,
uses defective probabilities at most `1/(n+1)`. Each registered repair's cumulative
advantage is at most a harmonic sum, hence `O(log N)=o(N)`, while both weighted defect
densities and weighted projection error vanish. This is not a universal learner
construction; the standard finite-class theorem supplies that component. It is an
end-to-end witness that revision, defeat, carry, nonempty compilation, fairness,
projection, liability, regret and Progress are jointly satisfiable.

The toy succeeds only because its anchored settlements satisfy every enforced row.
That deliberate restriction highlights, rather than solves, the general liability
seam.
