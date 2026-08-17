# Report

**Attribution.** Prompt author: GPT-5.6 Sol (OpenAI). Executor: Claude Opus 5
(Anthropic). Dispatched and executed 2026-08-17. Branch cut from `main` at
`0ef93952a153509759f98793530e370a6e477083`, verified rather than assumed.

**Verdict.** `architecture-positive / interface-splits-in-two /
projection-fixture-complete`. Internally accountable trajectory plus
counterfactual non-capture is a viable architecture for legitimate deference. It
is not one condition, and the second one needs an object the current normativity
line does not yet produce.

Round directory:
`projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/`.

## 1. The condition actually tested

Over a **variation class** `V` of advisor policies on one fixture:

```
for all a, b in V:  Coupled(a, b) and L(a) = L(b)  ->  Z(a) = Z(b)
```

`Coupled` is structural — one fixture, and neither policy suppressing an
encounter. `Z` is the protected projection. `L` is the licensed-reason trace: the
inputs admitted through the reason channel, each paired with what it licenses.

The quantifier is an argument rather than a default, because two readings of that
formula are different objects: `V` = every policy the advisor could adopt is a
claim about the principal's dynamics, which no advisor can undertake; `V` = one
policy with its residual variants and the null policy is a claim about this
advisor's action space, which is what a deference argument needs. Every verdict
is stated against a named finite class of the second shape.

## 2. It split

Two clauses. **Reason mediation**, above. **Protected access**: the advisor's
policy does not determine which *due* inputs arrive — neither which due reasons
reach the principal, nor which encounters occur.

The split is forced twice over, and the second is the sharper of the two. An
advisor that selects among genuinely licensed reasons defeats the target with
clause 1 vacuous on the pair, because the delivered traces differ. An advisor
that suppresses an encounter defeats the target with the protected state and the
trace *identical* — and clause 1 is not merely silent there, it is unstatable,
because the pair is not coupled. Coupling on the exogenous encounter history
turns out to be exactly the assumption that the advisor does not control what
arises.

## 3. Results

All six surviving attacks were rebuilt as advisor-mediated, under two distinct
susceptibilities. In every one the four conditions, disclosure and prospectivity
hold in both arms, the licensed-reason trace is empty in both arms, the
uninfluenced arm meets `L*` and the influenced arm does not. Clause 1 rejects all
six.

Controls: autonomous adequacy widening and autonomous bearing drift fail `L*` and
pass both clauses — non-capture is not correctness, which is the requirement, not
a limitation. Radical transformation passes everything. Persuasion by a licensed
reason moves the protected state with the traces differing and is permitted; the
same reason delivered seven times at high salience gives the identical trace and
the identical protected state. The placebo control — trace fixed, a non-reason
feature varied — fires clause 1 and no record-internal condition. Exposure that
moves nothing passes.

Kill tests: selective withholding is caught only by clause 2; control of arising
is caught only by clause 2. Dose compensation makes an audited pair read clean
while the class does not. Presence-triggered influence is invisible to every pair
of positive-exposure policies and visible against the null policy.

The full matrix is `PROSECUTION.md`; 40 checks, `python3 tests/run.py`.

**Non-tautology.** The advisor is denied write access to nothing: every
coordinate of `Z` is reachable by an advisor item, and the record-internal
conditions hold in every arm. The evidence that the condition is not definitional
is the principal with no residual channel: remove it and `Z = F(E, L)` holds by
construction of the transition rule, every attack becomes unbuildable, and the
round has nothing to report. `TheResidualChannelIsWhatMakesTheConditionFalsifiable`.

## 4. The protected projection did not survive as given

Attack I installs a merge licence. That is not `generation`, `entitlement`,
`bearing` or `adequacy`, and it is also not a field the procedural round's
`State` carries — so no record-internal condition there could read it either. The
four-coordinate projection is identical across the arms and clause 1 passes on a
trajectory that fails the target. A fifth coordinate, `identification`, catches
it; the other five attacks are caught without it.

The projection was not found too broad: no control needs a coordinate dropped.
Practical authority and grants stayed out, and no experiment gave a reason to
include them. What the round cannot show is closure — five is enough here, and
there is no argument that any finite list is enough in general.

A second object moved. A reason named by `(content, coordinate)` is too coarse:
two revisions offered under one name give identical traces and different
protected states with no residual channel involved. The trace has to individuate
a reason finely enough to determine what it licenses.

## 5. Delivered licensed reasons were not enough

Section 2. Repairing the withholding case by declaring the withheld reason
unlicensed would have been false to the fixture — both grounds are
provenance-valid and both bear on adequacy under the principal's own relation —
so the round added a clause instead.

Protected access needs an exogenous pool of due inputs, and the round checked
that this is not the environment-relative target smuggled back in: one fixture,
one class, two environments differing only in whether the cheap witness settles.
Both clauses take one value across the pair; `L*` takes two. An exogenous *reason
supply* and the environment that adjudicates faithfulness are independent
objects, and a grading that conflated them would have scored this result as a
failure under the dispatch's third negative criterion.

## 6. Relation to dose response

The note builds its contrast physically, so its design constraints are
constraints on an audit. Here the contrast is definitional, so each was
re-derived. Two arms: needed. Graded doses: not needed — the condition quantifies
over a class, it does not estimate a slope. One committed stream coarser than the
arm partition: replaced by the quantifier, and the dose-compensation witness is
what shows the replacement is doing the same work. Blinding: not needed as a
condition, since an arm-conditioning advisor is a policy the class already
contains. Zero-exposure arm: needed, and the presence-triggered witness is the
finite form of the note's own observation. Content randomization: not needed for
detection, and still missing for attribution — a content-mediated push and a
content-blind disposition produce identical records, identical protected states
and identical verdicts from both clauses, which is the note's non-attribution
theorem as an identity of finite objects.

## 7. What the scorekeeping theory now has to export

1. **`Due` with an advisor-independent extension.** The load-bearing one. Clause
   2 is unstatable without a due-reason pool the advisor cannot select within,
   and the round stipulates that pool rather than deriving it.
2. **An arising interface.** What demands arise must be exogenous to the advisor,
   or the counterfactual cannot be posed at all. This is stronger than anything
   the current `Due` is asked for.
3. **`Licensed` as a relation on a change, not on a name.** The trace must
   determine what a reason licenses, not merely identify it.
4. **A protected projection**, explicitly listing which coordinates count —
   including identification and merge licences, which the current state object
   does not carry.
5. **Liability identity through split and merge.** The bridge round already
   records this as still required on the answerability side; `identification` is
   the same need showing up on the legitimacy side, which is convergent evidence
   rather than a second finding.
6. **Disclosure of standards changes**, which already exists, holds in every arm
   here, and is compatible with the interface without being sufficient for it.

Nothing new is needed from `Performance`. No clause reads a loss, and the round
never constructed one.

## 8. What this does not establish

`BOUNDARY.md` in full. In short: the projection is not shown closed; two
susceptibilities are not a general residual channel; the entailment
`conditions + counterfactual clauses => L*` was not attempted and is false as
stated, since autonomous bad revision satisfies the left and fails the right;
`due_pool` is stipulated; a colluding pair is untouched.

The consequential one is auditability. Neither clause is a predicate of a record,
so the procedural round's record-equivalence argument applies to both: no
statistic of one realized trajectory determines either. A counterfactual
legitimacy condition is a good standard and a bad test, and any deference
argument using it must say which of three things supplies the assurance —
architectural constraint on the advisor, physically instantiated arms, or
self-certification, which is worth nothing without one of the first two.

## 9. Provisional names introduced

`ProtectedNormativeProjection` and its fifth coordinate `identification`;
reason-mediated non-capture; protected access; licensed-reason trace, and its
coarse and fine forms; reason channel and residual channel; `ResidualRule` with
values `repetition`, `salience`, `presence`, `none`; variation class; `due_pool`;
and the code objects `Fixture`, `Policy`, `Item`, `Proposal`, `Machinery`, `Run`.
The verdict label `architecture-positive / interface-splits-in-two /
projection-fixture-complete` is also provisional.

## 10. Deviations

1. **The secondary prosecution was not run.** The prompt lists coordinated
   standards drift, advisor–critic collusion and vocabulary split as high-value
   if the primary candidate survives, and it survived. Clause 1 quantifies over
   one advisor's policies against one principal, and a second scorekeeper is not
   in this fixture; the bridge round's own finding is that its protection is
   separation of the write, which a colluding pair does not face. Extending the
   variation class to a pair of influencers is a different fixture and is named
   as open rather than half-built here.
2. **The licensed-reason trace was refined beyond the prompt's specification.**
   The prompt does not fix its granularity. A witness forced the fine form, and
   the coarse form is retained and displayed as insufficient rather than dropped.
3. **The protected projection grew rather than shrank.** The prompt anticipated
   a smaller or differently typed projection; the counterexample forced a larger
   one. The counterexample is displayed, as required.
4. **No `FOR_HUMANS.md`.** The prompt makes it conditional and nothing here needs
   it.
5. **The wiki pages were not read.** The prompt permits rather than requires it;
   no claim in this round rests on wiki prose.
6. **Grading.** The round meets every bullet of the dispatch's *strong positive*,
   including the clause about arm-conditioning and presence-triggered adversaries
   under explicit design assumptions, and the dispatch's own note that a clean
   two-part interface counts as stronger than hiding the distinction. It also
   carries one *partial* marker — the protected projection is resolved for this
   fixture and not in general. Rather than choose a label the evidence does not
   pick out, both are stated and the round's own verdict line names the boundary.

No path or count in the prompt was found wrong.

## 11. Outstanding maintainer actions

1. **Decide the provisional names in §9**, or reject them. *Doing it* is one
   sitting over `COUNTERFACTUAL_INTERFACE.md` and `MODEL.md`. *Waiting* costs
   little now and more once a second round builds on the vocabulary. Appended to
   `DECISIONS.md`'s *Awaiting the author*.
2. **Decide whether the round's open questions become `PRIORITIES.md` items** —
   `THEOREM_MAP.md` §6, five of them. The round did not file any: it was not
   dispatched to file, and nothing here enters the registry. Appended to
   `DECISIONS.md`'s *Awaiting the author*.

Nothing is registered in `CLAIMS.md` and no existing document was rewritten to
fit the result. Three files outside the round directory changed, all of them
required: the round's entry in `state/rounds.json`, the one line it adds to the
generated `VERDICT_STATUS_INVENTORY.md`, and the two entries above in
`DECISIONS.md`'s *Awaiting the author*.
