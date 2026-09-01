# Proper Exercise as a typed transition judgment

## Result

Proper Exercise is fundamentally transition-level and proof-relevant.  The smallest
useful shell is

\[
\begin{aligned}
&\mathsf{ExerciseType}\;\tau,\\
&\mathsf{Affected}_\tau(S,e),\\
&\mathsf{Cert}_\tau(S,e,S'),\\
&\mathsf{Sound}_\tau(S,e,S',\xi),\\
&\mathsf{PE}^\tau(S,e,S') :\!\iff
  \exists\xi\;\mathsf{Sound}_\tau(S,e,S',\xi).
\end{aligned}
\tag{PE}
\]

The exercise is legitimate only when both independent judgments hold:

\[
\mathsf{LegitimateExercise}_\tau(S,e,S') :\!\iff
\mathsf{Authorized}_\tau(S,e)\land\mathsf{PE}^\tau(S,e,S').
\]

`Authorized` says that this actor may attempt this kind of transformation.  `PE`
certifies that this particular pre/post transition handles the live claims it affects.
Neither implies the other.

## Why the post-state is indispensable

Suppose a pre-state contains an adequate inquiry route and a live coverage matter.  One
batch deletes the route and terminally resolves the matter.  A strict-prefix predicate
sees the old route and can accept the resolution.  A transition judgment sees the
post-state defect and rejects it.  The same issue arises when one batch replaces an
evaluator and deletes the interpretation of its outstanding criticisms.

Accordingly, PE may *realize* the semantic oracles `Resolve`, `Continue`, `Met`, and
standing revision, but cannot in general be reduced to predicates of the strict prefix.
Where a proposed event contains a complete authenticated post-state, an implementation
may check PE before committing it; this does not change its logical type.

## The generic shell is intentionally weak

There is no domain-independent algorithm for `Affected`.  Each exercise type supplies a
scope rule and a completeness certificate: every live burden whose carrier,
interpretation, applicability, or required quality can change must be included.  Omitting
this requirement makes the calculus vacuous—a fake certificate can simply decline to
name the burden it destroys.

Likewise, `Sound` is typed.  Its useful common shape is proof-relevant transition
refinement, not one universal predicate:

| exercise type | certificate mathematics |
| --- | --- |
| coverage terminal resolution | post-state discharge or a live carrier |
| continuation/translation | many-to-many burden transport |
| prerequisite satisfaction | witness-backed rising edge of `Met` |
| standing revision | preservation/transport of affected interpretations and claims |
| joint enforcement | liability feasibility or a dual underwriting certificate |

Liability therefore fits the outer interface but not the burden-transport semantics.
The two-row fixture has individually feasible rows \(v_1\ge3/4\) and \(v_2\ge3/4\)
on \(V=\{(0,1),(1,0)\}\), while their conjunction is impossible.  The equal-weight
dual deficit is exactly \(1/4\).  Thus

\[
\mathsf{PE}(e_1)\land\mathsf{PE}(e_2)
\not\Rightarrow \mathsf{PE}(e_1\cup e_2).
\]

## Calculus laws

**Identity.** A no-op transports every burden to itself.

**Sequential composition.** Sound transport certificates compose by relational
composition; disposition receipts terminate only the branches they completely
discharge.  Typed certificates with incompatible intermediate states do not compose.

**Restriction.** A consumer may track a subset of burdens only when the exercise-type
scope proof establishes completeness for that subset.  Arbitrary weakening is unsound.

**Parallel composition.** No general rule exists.  Independent-looking exercises need a
joint certificate whenever their feasibility, interpretation, or resources interact.

## `Permit`, `Continue`, and `Met`

`Permit` should remain authorization/provenance.  It can coexist with
`PE^standing`; folding all post-state semantic obligations into `Permit` would erase the
very distinction the hostile examples exhibit.

`PE^continue` supplies a transport relation for targets, applicability, live criticisms,
exceptions, open failures, and response-quality requirements.  A function is too narrow:
splitting and merging require a relation or nonempty finite successor family.

Because settled Continuity makes `Met` persistent, PE should govern its rising edge:

\[
\neg\mathsf{Met}_n(d)\land\mathsf{Met}_{n+1}(d)
\Rightarrow \exists\xi\;\mathsf{PE}^{met}(S_n,e_n,S_{n+1};d,\xi).
\]

Acceptable witnesses include qualifying receipt plus registration, direct satisfaction,
authorized obsolescence, and target-relative disposition.  Sensor deletion, concept
deletion, route loss, and procedural issue removal are not satisfaction witnesses.  PE
need only give a sufficient realization class until the certificate language is known to
be exhaustive; a concrete implementation should nevertheless require every rising edge
to be backed.
