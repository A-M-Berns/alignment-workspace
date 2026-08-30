# Service-response semantics

Status: research note; unregistered. This note tests the proposal

\[
\text{unanswered reason}\Longrightarrow
\text{better service response},
\]

not the stronger and often false proposal that every reason entails a better external
action.

## 1. Why the shift matters

Continuity guarantees service to a live matter. It does not guarantee that service is
relevant or responsive. Progress can act at exactly this seam if the response alphabet
contains the ways a reasoner can answer a reason: act, inquire, test a defeater, expose a
conflict, or explicitly revise the episode.

The shift is substantive. “Investigate whether action `x` harms a third party” need not
entail an external alternative `y` better than `x`. It can entail that, **as a way of
servicing the live issue**, `investigate` is better than `ignore-and-repeat-x`.

This does not make the comparison free. The inquiry reason must carry or be combined
with a procedural norm that licenses the service comparison. A bare question does not
numerically rank inquiry over every alternative.

## 2. Typed response surfaces

A response surface is episode-local finite data:

```text
Surface:
  id
  labels : finite set X
  recognized answer modes for each reason type
  decoder from labels to feasible service records/actions
  episode anchor and license
```

Useful labels include:

- `act(x)` and `act(y)`;
- `investigate(question)`;
- `requestEvidence(kind)`;
- `assessDefeater(r)`;
- `acknowledgeConflict(R)`;
- `openAdjudication(R)`;
- `openSuccessor(transition)`;
- `deferWithGrounds(d)`;
- `ignore(r)` or a type-specific no-response baseline.

Labels must denote genuinely feasible service moves at the strict prefix. A label that
only names an impossible ideal cannot support a repair.

## 3. Five compilable reason patterns

### 3.1 Action-directed criticism

Reason: “On this episode's anchored standard, using `x` rather than `y` is worse by at
least `gamma`.”

```text
source = act(x)
target = act(y)
row    = v(act(y)) - v(act(x)) >= gamma
repair = act(x) -> act(y)
defect = p(act(x))
```

This is the direct fragment of `WITNESS_BRIDGE.md`.

### 3.2 Inquiry-directed reason

Reason: “The unresolved risk must be investigated before repetition counts as an
adequate response.”

```text
source = ignore-and-repeat
target = investigate(risk)
row    = v(investigate) - v(ignore-and-repeat) >= gamma
repair = ignore-and-repeat -> investigate
defect = p(ignore-and-repeat)
```

No external-action ordering is asserted. The inquiry may later defeat the criticism,
support action change, or reveal a conflict. Uptake is already progress at the service
level.

### 3.3 Conflict-directed reason

Two undefeated reasons support incompatible external acts. Neither act robustly
dominates over the combined value region. A separately licensed procedural reason can
say:

```text
source = silently-select-one-side
target = open-adjudication / acknowledge-conflict
row    = v(open-adjudication) - v(silent-selection) >= gamma
```

The two conflicting reasons alone do **not** entail this row. The comparison comes from
a conflict-handling norm. If no such norm is represented, Progress correctly remains
silent rather than inventing one.

### 3.4 Defeater-directed reason

A criticism may be answerable by a legitimate defeater rather than adoption:

```text
source = dismiss-without-assessment
target = assess-and-record-defeater
row    = v(assess-defeater) - v(dismiss) >= gamma
```

If assessment yields an accepted defeater, the original reason becomes disabled or
disposed through existing reason/Continuity events. Repeating unsupported defeater
claims is not uptake; the service label denotes the anchored assessment protocol and
its record, not merely uttering “defeated.”

### 3.5 Evaluator-revision request

A reason can allege that the episode's current evaluator is inadequate. It cannot
retroactively change that evaluator. It can compare service responses:

```text
source = silently-rescore-current-episode
target = resolve-and-open-explicit-successor
row    = v(open-successor) - v(silent-rescore) >= gamma
```

The target is an ordinary Continuity successor event with explicit state continuation
and a prospective anchor. The comparison must itself be licensed under the current
episode; a hoped-for future evaluator cannot authorize its own adoption.

## 4. What counts as behavioral uptake

For a typed comparison with source label `x`, behavioral uptake means

\[
\frac{\sum_{n<N}a_nc_np_n(x)}{\sum_{n<N}a_nc_n}\to0.
\]

This does not require deterministic eventual adoption. It allows exploration,
occasional mistakes, and other service modes. It says only that the specifically
diagnosed inferior response becomes negligible on relevant service mass.

Issue closure is not required. An inquiry reason can be behaviorally answered by doing
the inquiry even while the larger matter remains live; a conflict reason can be answered
by opening adjudication; an action reason can be taken up while the episode remains open
for monitoring.

## 5. Does every genuine reason fit?

No theorem currently supports the universal claim. The response ontology materially
expands the closed fragment, but three obstructions remain.

### 5.1 No represented answer-mode norm

A bare receipt or question can make inquiry intelligible without entailing that inquiry
is better than ignore. The comparison needs typed semantic content or a licensed
procedural schema. The reason multihypergraph deliberately stores reasons without
running a closure policy, so the compiler may not manufacture this implication.

### 5.2 Incomparable legitimate answers

A tragic conflict may have several permissible responses with no robust ordering. If
all the reason requires is “do not pretend there is no conflict,” a comparison to
`acknowledgeConflict` may exist. If even acknowledgement and silence are not ordered by
the represented standards, no strict repair witness follows.

### 5.3 Missing feasible response

A reason may demand restitution that is no longer possible. `acknowledge`, `explain
impossibility`, or `seek partial repair` can be answer modes only if the represented
practice recognizes them. Adding these labels to `X` does not itself make them adequate.

The right prospective completeness condition is therefore:

> **Answer-Mode Adequacy.** Every reason type admitted as answerable registers at least
> one feasible recognized service mode or explicit conflict/impossibility procedure;
> when continued nonresponse is defective, its semantics supplies a strict comparison
> between that nonresponse and one registered mode.

This is much smaller than “derive utility dominance from arbitrary normativity,” but it
is still a normative/semantic condition, not a structural theorem.

## 6. Pressure test of the ontology

| Reason | Better external act forced? | Better service response available? | What licenses it? |
|---|---:|---:|---|
| direct criticism of `x` | sometimes | yes in typed fragment | comparison payload |
| unresolved empirical risk | no | investigate over ignore | inquiry-duty schema |
| conflicting action reasons | no | possibly adjudicate over conceal | conflict procedure, not conflict alone |
| alleged defeater | no | assess defeater over dismiss | defeater protocol |
| evaluator defect | no | explicit successor over silent rescore | revision protocol |
| impossible restitution | no | perhaps acknowledge/partial repair | impossibility disposition rule |
| purely expressive demand | no | not necessarily | may lack any strict service comparison |

The service-response ontology therefore **substantially reduces** witness completeness:
many non-action reasons become pairwise service comparisons. It does not close the
general problem, because adequacy and comparative force of answer modes still need
represented authority.

## 7. Engagement is not scheduling a repair

All pairwise repairs can be evaluated counterfactually from the same `p_n` and value
vector. Persistent Relevance asks whether matter service exposes the surface at all; it
does not allocate separate physical effort among repairs.

For a fixed service alphabet, set `c_n=1` while the reason remains operative. For a
larger alphabet or several subprotocols, `c_n` can be the predictable fraction of the
serviced decision to which the comparison applies. Surface Fairness then prevents a
process from assigning infinite “service” entirely to irrelevant labels.

## 8. Revision and burden propagation

PR69 permits infinitely many explicit successors at the basic level. A cheap
intermediate provenance rule is nevertheless available:

\[
\boxed{
r\text{ enabled and undisposed at }q, q\to q'
\Longrightarrow
\text{Disposition}(r)\text{ in the transition}
\ \lor\ r\leadsto r'\text{ at }q'.}
\tag{Reason Carry}
\]

`r -> r'` here is an explicit translation/provenance link, not Continuity's issue
successor relation. It prevents evaluator succession from erasing a burden by omission.
The translation must record whether it preserves the service comparison, changes its
surface, or defeats it.

Reason Carry does not solve endless churn. If every successor changes labels and
comparison content, no fixed repair survives. If translations preserve one fixed
surface and margin, the restricted witness theorem can continue across episodes; that
is a useful special case but no longer episode-local. General cross-era equivalence is
a larger diachronic theory and remains deferred.

## 9. Conclusion

“Better service response” survives the hostile cases in a qualified form:

\[
\boxed{
\text{Every typed answerable reason with Answer-Mode Adequacy}
\text{ exposes a better service response when nonresponse persists}.}
\]

It is false without the qualification. The important reduction is real: the compiler
need not turn inquiry, conflict, defeater, or revision reasons into better external
actions. It needs a typed, licensed comparison between nonresponse and a feasible
answer mode.
