# Closing the Progress witness bridge in a restricted fragment

Status: research specification and paper proof; unregistered; not frozen or settled.
This round consumes PR69 and does not alter its Uptake, stagnant-tail strategy,
schematic/realization separation, or Continuity lifecycle.

## 1. Result

PR69's single `SW-density` package decomposes without loss into three independent
obligations:

\[
\boxed{
\text{Persistent Relevance}
+\text{Typed Witness Completeness}
+\text{Stagnation Persistence}
\Longrightarrow\text{SW-density}.}
\]

In the finite, fixed-alphabet fragment below, Typed Witness Completeness is a theorem.
Persistent Relevance is a service-surface fairness condition. Stagnation Persistence is
the behavioral part of the semantic meaning of “still unanswered,” and contains no
value or repair claim. Their composition proves a Restricted Stagnant-Tail Witness
Lemma and, with PR69's Uptake theorem, rules out persistent stagnation in this fragment.

This closes a real fragment of the bridge. It does not show that arbitrary reasons have
action-comparative or service-comparative content.

## 2. Decomposing `SW-density`

Fix matter `m`, reason occurrence `r`, and candidate repair `rho`.

### 2.1 Persistent Relevance (engagement)

Continuity supplies `A_N(m)->infinity`, but a particular reason needs

\[
W_N(m,r)=\sum_{n<N}a_n(m)c_n(m,r)\to\infty.
\tag{PR}
\]

Here `c_n(m,r)` is a predictable indicator or fractional confidence that service at
`n` exposes the decision surface named by `r`. It is not another allocation.

**Persistent Relevance** is the implication

\[
\begin{aligned}
&r\text{ remains operative and event-unanswered on a tail},\\
&A_N(m)\to\infty
\quad\Longrightarrow\quad W_N(m,r)\to\infty.
\end{aligned}
\]

A convenient sufficient condition is a service-weighted exposure floor: for some
`eta>0`, tail index `N_0`, and finite `C`,

\[
W_N-W_{N_0}\ge\eta(A_N-A_{N_0})-C.
\tag{Surface Fairness}
\]

For a fixed alphabet in which the reason's surface is present at every service date,
`c_n=1`, `W_N=A_N` on the tail, and Continuity discharges Persistent Relevance.

This bridge is not normative dominance. It is a conformance/fairness condition on the
service interface: unbounded service of the matter must not forever avoid a fixed
operative reason's recognized answer surface. Defining “unanswered” to include this
would hide attention theater, so it remains separately checkable.

### 2.2 Typed Witness Completeness (dominance)

For a reason type whose semantic payload already says

\[
v(y)-v(x)\ge\gamma>0,
\]

compiler correctness and pairwise repair expressivity imply

\[
g_n(rho_{x\to y})\ge\gamma d_n,
\qquad d_n=p_n(x).
\tag{TWC}
\]

This is a semantic/representational theorem in the restricted language below. It says
nothing about why an arbitrary reason should possess this payload.

### 2.3 Stagnation Persistence (defect)

For the designated source response `x`, let

\[
d_n(r)=p_n(x),\qquad D_N(r)=\sum_{n<N}a_nc_nd_n.
\]

The reason is **behaviorally answered** when `D_N/W_N->0`. It is behaviorally stagnant
when

\[
\limsup_N D_N/W_N>0.
\tag{SP}
\]

This definition names observable service behavior only. It does not mention `K`, value,
gain, a repair, regret, or a market, so it does not trivialize witness completeness.

The three bridges can fail independently:

- `A_N->infinity` with `W_N=0`: relevance failure, whatever the values and behavior;
- `W_N->infinity` and persistent `p(x)` with no comparison row: dominance failure;
- a stable strict comparison with `W_N->infinity` but `D_N/W_N->0`: no behavioral
  stagnation, and correctly no contradiction.

## 3. Restricted reason language

### 3.1 Fixed episode and response surface

Fix an issue episode `q` and a nonempty finite service alphabet `X`. Labels are
semantic service responses, stable throughout the episode. Each coordinate has an
episode-local bounded value security `V_(q,x)`, so `v(x) in [0,1]`.

The response distribution is `p_n in Delta(X)`. The repair family contains every fixed
pairwise map

\[
f_{x\to y}(z)=\begin{cases}y,&z=x,\\z,&z\ne x,\end{cases}
\]

and its linear lift `Phi_(x->y)` to distributions. Program identity is fixed before the
tail.

### 3.2 Typed targets

The existing reason-state `Atom` target is refined downstream by a finite data type:

```text
ReasonTarget :=
  | ServiceCompare(surface, source : X, target : X, margin : Q_pos)
  | ConditionalServiceCompare(condition, surface, source, target, margin)
  | Evidence(content)
  | Question(content)
  | Incompatibility(contents)
```

Only the first target compiles unconditionally to a value row. A conditional comparison
compiles when its public strict-prefix condition is true. Evidence, questions, and
incompatibility do not silently become value inequalities.

A reason occurrence `r` retains the prior multihypergraph structure:

- immutable identity, sources, and target;
- an explicit `App(schema,case,stage)` among its sources;
- enabledness exactly from adopted claim sources and transcript receipt sources;
- defeat/withdrawal by loss of an applicability/source claim, never deletion;
- a fixed episode and surface in the typed target.

### 3.3 Operative rows

At strict prefix `H_n`, `r` is **row-operative** when:

1. `r` is enabled under the reason-state query;
2. its applicability condition is true at `H_n`;
3. its service surface and coordinates are available;
4. its row has an authenticated license (separated in `AUTHORITY_TO_CONSTRAINTS.md`);
5. no accepted reason disposition has defeated, discharged, or translated it away.

An operative target `ServiceCompare(s,x,y,gamma)` contributes

\[
v(y)-v(x)\ge\gamma.
\tag{row(r)}
\]

Together with structural cube rows and every other operative comparison, this defines
`K_n`. The compiler must verify `K_n` is nonempty before exposing it to Progress.

### 3.4 Recognized answer modes

The typed reason registers three disjoint answer modes:

1. **defeat/discharge:** an accepted record removes a required source, supplies a
   defeater, or resolves the reason under its anchored protocol;
2. **translation:** a successor carries an explicitly linked occurrence whose payload
   preserves or deliberately changes the burden;
3. **behavioral uptake:** normalized use of the designated defective source label tends
   to zero on the reason's exposed service mass.

The first two are event answers. The third is behavioral. Mere attention, a generic
successor, or an unrelated inquiry receipt is not an answer to `r`.

## 4. Non-circular stagnation semantics

Three proposed notions should not be conflated.

### Event stagnation

After `N_0`, no accepted defeat, discharge, burden-preserving translation, inquiry
result, or other answer event recognized by `r` occurs. This is necessary for a stable
episode witness but insufficient: behavior may take the reason up asymptotically with
no event.

### Normative unansweredness

`r` remains enabled, applicable, undefeated, and undisposed under its anchored reason
semantics. This says the burden remains operative. It neither asserts exposure nor
defective behavior.

### Behavioral stagnation

The response named defective by `r` is not asymptotically eliminated on exposed service
mass: `limsup D_N/W_N>0`.

### Recommended restricted definition

A typed reason is **persistently unanswered on a stagnant tail** when:

1. it is normatively unanswered throughout the tail;
2. the tail is event-stagnant for that reason;
3. it is behaviorally stagnant.

Persistent Relevance is deliberately not folded into this definition. It is an
interface obligation connecting Continuity service to the reason's surface.

This is the weakest non-circular definition supporting the restricted theorem. Event
stagnation alone is too weak. Behavioral stagnation alone ignores legitimate defeat.
The combined definition never mentions positive gain or existence of a repair.

## 5. Restricted Stagnant-Tail Witness Lemma

**Theorem.** Fix a matter `m`, one issue episode with fixed finite alphabet `X`, distinct
labels `x,y in X`, and `gamma>0`. Suppose from some `N_0` onward:

1. a fixed reason occurrence `r` is normatively unanswered and row-operative, with
   payload `ServiceCompare(s,x,y,gamma)`;
2. compiler soundness gives a nonempty `K_n subset [0,1]^X` whose every valuation
   satisfies the row `v(y)-v(x)>=gamma`;
3. the registered repair family contains the fixed pairwise repair `rho_(x->y)`;
4. Persistent Relevance gives `W_N=sum_{n<N}a_nc_n->infinity`;
5. the reason is behaviorally stagnant, with `d_n=p_n(x)` and
   `limsup_N D_N/W_N>0`.

Then `rho_(x->y)` is a stable SW-density witness:

\[
g_n(m,rho_{x\to y})\ge\gamma d_n
\quad(n\ge N_0),
\qquad W_N\to\infty,
\qquad\limsup_ND_N/W_N>0.
\]

**Proof.** The repair changes only the probability at `x`, moving all of it to `y`.
For every `v in K_n`,

\[
\begin{aligned}
\langle\Phi_{x\to y}(p_n)-p_n,v\rangle
&=p_n(x)(v(y)-v(x))\\
&\ge p_n(x)\gamma=\gamma d_n.
\end{aligned}
\]

Taking the infimum over nonempty `K_n` preserves the inequality, proving Sensitivity.
The repair is one fixed map because `X,x,y` are fixed. The last two SW-density clauses
are hypotheses 4 and 5, supplied by different bridges. QED.

### Repair-realizable affine generalization

The same proof works for a typed affine reason `u^Tv>=gamma` only when its target also
identifies a feasible fixed repair and a nonnegative defect satisfying

\[
\Phi^rho(p_n)-p_n=d_nu.
\]

Then gain is `d_n u^Tv>=gamma d_n`. An arbitrary affine row need not be the difference
of two distributions and need not correspond to any feasible repair. “Affine reason”
alone is therefore insufficient; **repair realizability** is load-bearing.

## 6. Restricted no-stagnation theorem

**Corollary.** Add Continuity's eventual-live service conclusion, Persistent Relevance,
and PR69 Uptake for `rho_(x->y)`. No typed reason satisfying the theorem's compiler and
repair hypotheses can remain persistently unanswered on a stagnant tail.

**Proof.** The lemma derives SW-density. PR69's Uptake + Sensitivity theorem gives
`D_N/W_N->0`, contradicting behavioral stagnation. QED.

This is stronger than PR69: PR69 assumed SW-density, while this result derives it from
a typed reason semantics, service engagement, and a behavior-only stagnation predicate.

## 7. What the theorem teaches

The open bridge was not one mysterious implication:

- **Relevance** asks whether service reaches the reason's answer surface.
- **Dominance** asks whether the reason type semantically supplies a strict comparison
  that a feasible stable repair realizes.
- **Persistence** asks whether the designated defect remains behaviorally present.

Only the middle step is closed by the reason-to-value compiler. Continuity plus a fixed
surface can close the first. The third is the substantive behavioral half of
stagnation, not a theorem from event bookkeeping.

## 8. Generalization obstacles

1. Bare evidence, questions, incompatibilities, and expressive demands do not entail a
   comparison without a typed answer-mode norm.
2. Conflicting operative comparisons can make `K_n` empty. No robust gain is then
   defined; conflict must become a Continuity-visible service problem.
3. A reason robust only on a valuation face needs an independently justified context
   selecting that face. Taking an infimum over the face by fiat launders disagreement.
4. Changing applicability can make `W_N` finite. Predictability prevents hindsight but
   not starvation of the reason's surface.
5. Varying alphabets or translated labels can destroy fixed repair identity.
6. Infinite successors can repeatedly translate rather than defeat a burden. Provenance
   carry is cheap; stable comparison semantics across translations is not.
7. Some legitimate reasons have several incomparable answer modes. A finite service
   alphabet expands the comparison surface but does not manufacture a strict ordering.

## 9. Dependency map

```text
Continuity eventual service A_N -> infinity
        + Surface Fairness / Persistent Relevance
        -----------------------------------------  gives W_N -> infinity

enabled typed ServiceCompare reason
        + sound nonempty row compiler
        + complete pairwise repair family
        -----------------------------------------  gives g_n >= gamma d_n

non-circular behavioral stagnation
        -----------------------------------------  gives limsup D_N/W_N > 0

the three lines
        -----------------------------------------  give SW-density

SW-density + PR69 Uptake
        -----------------------------------------  rule out persistent stagnation
```

Operative Constraint Grounding authenticates the second line's rows but is not used in
the gain inequality. Traderization and regret realize Uptake but are not used in the
witness lemma.
