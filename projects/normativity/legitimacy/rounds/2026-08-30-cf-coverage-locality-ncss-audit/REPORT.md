# Report: locality and exact NCSS audit

Status: adversarial follow-up to PR71; unregistered. Coverage and Proper Exercise remain
open.

## Result

Both objections succeed, and both have local repairs.

`(CFP)` certifies an exterior-fixed comparison but no residual-agent invariance. Neither
`res(alpha(q,r))=r` nor a named residual equivalence fixes the problem: either can be a
label while \(q\) selects the whole agent. The minimal meaningful condition is
extensional and observable-relative. For a contract-authenticated residual observation
\(p_R:\Omega_h\to W_R\), require

\[
\forall q,q',r,e,
\quad p_R(\alpha(q,r)\star e)=p_R(\alpha(q',r)\star e).
\]

CF contributes the ambient agent/exterior split and quantification against every exterior.
It does not select \(p_R\), prove that it covers every intended residual behavior, or
identify \(Q\) as inquiry. Existing subagent notions do not remove those modeling
choices. Coverage needs inquiry semantics from the contract; it needs the behavioral
condition only when it claims the counterfactual is a local agent variation.

PR71's NCSS theorem also omits a necessary post-transition relevance fact. A criticism
active before the transition can genuinely cease to apply during it, making `(IMP)` true
despite route loss. The exact theorem assumes the one-criticism post-state defect:

\[
\operatorname{Active}_{n+1}(c)\land
\neg\operatorname{Rep}_{n+1}(c)\land
\neg\exists R\,\mathsf{Adeq}_{n+1}(R,c).
\]

Local closure adequacy requires a terminal resolution certificate to show post-state
representation, an adequate route, or authorized disposition. With exact outstanding-set
evolution and fresh-successor ancestry, the post-defect implies both a live descendant of
\(m_\sigma\) and false `Implements`. This is not circular: the semantic premise checks one
proposed closure; Continuity supplies cross-prefix matter persistence.

## Exact repairs

The corrected interaction object adds one field with a demonstrated consumer:
\(p_R\) and its behavioral-locality proof. `res` and `qry` projections are omitted.
Target/applicability and registration-capability certificates remain route data.

The corrected NCSS theorem uses post-transition `Active`. `PreserveRel` is an optional
transition certificate which can derive that hypothesis. Inquiry-local applicability,
self-revision relevance transport, and genuine external applicability change remain
separate because their consumers differ.

`Adeq` means registration-capable, not already registered. Route existence, exercise,
receipt, and registration are four distinct states. PR71's implementation test already
used counterfactual capability, but its method name is corrected.

## Verification

`python3 tests/run.py` runs nine tests over nine finite locality models and an exhaustive
64-case NCSS Boolean model. It checks:

- `(CFP)+(RP)` with whole-agent replacement;
- a canonical but behaviorally fake residual projection;
- extensional locality under predictors, strategic responders, and self-modification;
- both delegation decompositions;
- absence of a nontrivial local patch;
- the relevance-loss countermodel; and
- a countermodel for every load-bearing NCSS hypothesis.

No Lean is added. The correction is entirely in the Coverage realization layer and
continues to require zero changes to `IssueTrace` or its theorem spine.

## What was not shown

- No intrinsic CF construction identifies the true residual agent or inquiry component.
- Authentication/completeness of \(p_R\) remains a modeling and contract obligation.
- A constant residual observation is mathematically valid and substantively vacuous.
- The local closure certificate is a semantic norm, not derived by Continuity.
- No eventual repair, exercise, registration, Progress, liability, or scope-selection
  result is claimed.
- The results are test-supported research architecture, not registered statements of
  record.

## Deviations

No FFS/FSM or Lean work was needed: the counterexamples and repairs are decided by the
existing CF outcome map and settled Continuity update law. The pass amends PR71's live
files in addition to adding this audit so the open PR does not retain the two statements
the audit refutes.

## New names introduced

All provisional: **behavioral locality**, **protected residual observation**,
**extensional residual observation equivalence**, **local closure adequacy**, and
**post-defect**.

## Outstanding maintainer actions

None. The follow-up adopts both corrections and preserves PR71's unregistered status.

### BOTH-REQUIRE-LOCAL-REPAIRS
