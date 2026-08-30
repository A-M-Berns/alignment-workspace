# Answer-Mode Adequacy

## Purpose

Basic Progress should not apply to every represented sentence called a reason. It
applies to reason types whose answerability semantics identify a feasible way of
servicing the reason that is strictly preferable to a designated nonresponse mode.
This is weaker than “every reason entails a better external action” and stronger
than mere graph membership.

## Typed certificate

For an episode-local finite service alphabet `X`, an **Answer-Mode certificate** for
a reason occurrence `r` contains:

1. a nonempty finite set `S_r subseteq X` of defective nonresponse modes;
2. for each `x in S_r`, a probability distribution `mu_{r,x}` over finite recognized
   answer modes `T_{r,x} subseteq X`;
3. applicability and feasibility predicates fixed from the strict prefix;
4. a positive rational margin `gamma_{r,x}`;
5. semantic rows asserting, on the applicable admissible region,

   \[
   \mathbb E_{y\sim\mu_{r,x}}v(y)-v(x)\ge\gamma_{r,x};
   \]

6. provenance, authority and disposition rules for those rows.

The defect is `d_r(p)=p(S_r)`. The induced stochastic repair fixes modes outside
`S_r` and sends each source `x` to `mu_{r,x}`. The finite kernel witness lemma in
`FINAL_SCHEMATIC.md` then derives Sensitivity.

This definition allows several incomparable legitimate answers. It requires neither
a privileged deterministic response nor an ordering among answer modes. It requires
only one licensed distribution over acceptable answers for every defective source.

## Is `ServiceCompare` primitive?

The semantic theory may generate the comparison in two ways:

- **comparison-bearing reason:** the reason's payload directly contains the affine
  row and its target service modes;
- **answer-mode norm:** the reason declares an obligation type, and a separately
  licensed protocol schema compiles “answer mode versus nonresponse” into the row.

The schematic should consume the resulting Answer-Mode certificate rather than
choose between these implementations. Calling `ServiceCompare` primitive would be
too restrictive; allowing an unauthenticated compiler would be too permissive.

## Examples and boundaries

### Action-directed criticism

“Current option `x` wrongs a third party; use mitigation `y`.” The source is
`repeat x`, the acceptable mode is `adopt y`, and the reason directly licenses
`v(y)-v(x)>=gamma`. This is the original pairwise fragment.

### Inquiry-directed reason

“Whether `x` causes harm is unresolved and evidence `E` is obtainable.” The source
is `ignore`, and acceptable modes may include `run E`, `request E`, or a declared
equivalent inquiry. The strict comparison is licensed by a duty-to-investigate
schema plus feasibility and value-of-information conditions. Inquiry is not always
better: if evidence is unobtainable, duplicative, excessively costly, or already
settled, the certificate is inapplicable or defeated.

### Conflict

Two undefeated reasons may make direct action comparisons incompatible. A procedural
reason can nevertheless compare `open adjudication / acknowledge unresolved conflict`
against `silently act as if no conflict exists`. Acknowledgment counts as an adequate
answer only if the protocol declares that it changes the burden or public status; an
empty log message is not adequate.

### Defeater assessment

A proposed defeater does not automatically defeat a reason. A reason for assessment
may compare `test and record disposition` against `ignore the defeater`. If the test
succeeds, Continuity records defeat; if it fails, the original reason remains.

### Revision request

A challenge to an evaluator may compare `open an explicit successor/revision episode`
against `silently keep or silently replace the evaluator`. The answer mode is the
auditable transition, not any particular new evaluator. This supports one transition;
it does not prove progress through infinitely many eras.

### Impossibility

`Certify impossibility with evidence and register the prescribed disposition` can be
an answer mode if the protocol recognizes it. Merely asserting impossibility is not.
The comparison favors an honest impossibility record over continued pretense, not
the impossible substantive outcome.

## Failed formulations

1. **Every unanswered reason has a better action.** Fails for inquiry and conflict.
2. **Every answer event is better than ignoring.** Permits defeater spam and empty
   acknowledgments.
3. **Every represented reason gets a row.** Makes questions and mutually inconsistent
   demands silently empty the admissible region.
4. **Any acceptable set is enough.** Without a uniform strict comparison, no repair
   witness follows.
5. **Define unansweredness by positive gain.** Circularly assumes the bridge.

## Recommended semantic boundary

> **Answer-Mode Adequacy.** A reason is eligible for basic Progress exactly when its
> licensed reason type and current applicability state yield a stable finite
> Answer-Mode certificate whose defective modes are independently recognizable and
> whose acceptable modes are feasible on the exposed response surface.

This subsumes Typed Witness Completeness for the finite-kernel fragment: the semantic
certificate is the input and the kernel lemma proves the witness. Stagnation remains
independently defined as continued operative nonresponse with positive defect density.

The main remaining semantic problem is not arbitrary normative witness completeness.
It is specifying and authenticating the admitted answerable reason types and their
protocol schemas. Reasons outside this class remain represented and answerable in the
broader sense, but basic Progress correctly stays silent about them.

