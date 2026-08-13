# Follow-up dispatch: Press and refine PR #29 before merge

**Date:** 2026-08-13  
**Maintainer:** A. M. Berns  
**Repository:** `A-M-Berns/alignment-workspace`  
**Target PR:** #29 — `Research: relational scorekeeping bridge for learning and corrigibility`  
**Branch:** `round/2026-08-13-relational-scorekeeping-bridge`  
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)  
**Executor:** self-identify accurately in report, commits, and PR metadata  
**End state:** update **PR #29 in place**. Do not open another PR. Do not merge it.

# 0. Purpose

PR #29 has returned a provisionally positive result:

```text
Shared-substrate-positive
```

The representation gamble appears to have paid off:

```text
commitments_i(j) = closure of ack[j] under practice[i]
```

gives a genuine perspectival answerability object; reified applicability fits
naturally; fixed public-status programs appear to avoid the uniform-map comparator
collapse; and scoped practical authority gives the corrigibility line an
authorization coordinate distinct from causal capability.

Before this is merged, perform a **pressing/refinement pass**.

The goal is not to make the PR larger or more impressive.

The goal is to determine whether the current positive verdict survives correction
of the places where the implementation or prose currently outruns the result.

In particular, press on six load-bearing questions:

1. Is the proposed learning loss genuinely resistant to **standards/self-score
   laundering**, rather than merely described that way?
2. Should consequential commitments become learning loss immediately, or only
   once they are **publicly exposed as due burdens**?
3. Are **protocol legality, normative compilation/reasons-responsiveness, and
   comparative performance** still properly separated?
4. Does the model preserve the distinction between **commitment-preserving** and
   **entitlement-preserving** inference?
5. Do semantic learning actions such as `SUSPEND` actually implement the
   normative operation their names claim?
6. Do the public-status comparator programs remain meaningful under a small amount
   of **endogenous state evolution**, rather than only under re-filed copies of one
   state?

A downgrade of the verdict is acceptable.

Do not protect `Shared-substrate-positive`.

---

# I. Procedure

Start by fetching the latest remote head of PR #29 and checking out:

```text
round/2026-08-13-relational-scorekeeping-bridge
```

Read the whole current round, especially:

```text
MODEL.md
THEOREM_MAP.md
PROSECUTION.md
TWO_ARC_INTERFACE.md
FOR_HUMANS.md
BRANDOM_MAP.md

src/scorekeeping.py
src/moves.py
src/learning.py
src/collapse.py
src/corrigibility.py

tests/test_answerability.py
tests/test_learning.py
tests/test_corrigibility.py
tests/test_structure.py
```

Also reread the existing main-branch learning interface and bridge:

```text
projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md
projects/leverage/rounds/2026-08-11-phi-regret-bridge/PHI_REGRET_BRIDGE.md
projects/leverage/rounds/2026-08-11-phi-regret-applicability/
projects/leverage/rounds/2026-08-11-phi-regret-learner/
```

Use PR #27 only as adversarial evidence as before. Do not create a dependency on
it.

Preserve the original dispatch and report as historical artifacts.

Add this follow-up dispatch and a new report under:

```text
prompts/2026-08-13-relational-scorekeeping-refinement/PROMPT.md
prompts/2026-08-13-relational-scorekeeping-refinement/REPORT.md
```

Do not overwrite the original prompt to make history look cleaner.

You may update the round's current synthesis files and code/tests where the
refinement changes the live result.

---

# II. PRESSING ISSUE 1 — audit the loss dependency claim exactly

The current model defines approximately:

```text
defect =
    1/2 * unacknowledged consequences
  + 1   * live challenges
  + 1/2 * defeated commitments
  + 1   * unsupported practical commitments
```

The current prose says in several places that the loss is read from the learner's
public record and a second participant's score, and that the learner cannot erase
it merely by rewriting its own practice.

Audit this statement literally.

In particular, inspect:

```text
unsupported_practical
```

which reads practical authority / grants.

The current fixture gives `H` practical authority over some authority-changing
moves. Therefore the claim that *every input to the loss is only `ack[H]` or
`practice[C]`* appears too strong.

Audit every indirect dependency of every loss component:

```text
ack
practice
grants
challenges
vindications
deferrals
testimony_permitted
vocabulary
performed
```

and every move that can alter each dependency.

Do not try to prove:

```text
the learner cannot change the loss
```

That is false and undesirable.

A recognized answer should be able to reduce the loss.

The desired distinction is:

```text
legitimate response can reduce loss
```

versus:

```text
mere revision of H's own evaluative/inferential standards cannot erase
an externally still-live answerability burden
```

## Required artifact: `LOSS_DEPENDENCY_AUDIT.md`

Create an exact table:

```text
loss component
direct dependencies
indirect dependencies
which agents can modify them
which moves modify them
which modifications are legitimate answers
which modifications are mere standards/self-score revision
whether self-laundering is possible
```

Then choose the smallest principled repair.

Possible dispositions include:

### Option A — split the loss

For example:

```text
RelationalAnswerabilityDefect
PracticalAuthorityDefect
```

and use only the first as the theorem-facing normative-learning loss until the
second has a non-self-launderable semantics.

### Option B — preserve the combined loss but prove the relevant non-laundering

property for a sharply stated class of edits.

### Option C — revise the practical component so that it is assessed against an

authority relation the learner cannot unilaterally rewrite.

Do not select an option for aesthetic symmetry.

If the practical-authority term does not belong in the current theorem-facing
loss, remove it from that loss and update prose/tests accordingly.

## Required regression tests

At minimum distinguish:

```text
self-revision of H's inferential practice
    -> does not erase a still-live relational burden

recognized answer to that burden
    -> may reduce it

unrelated authorized practical edit
    -> does not accidentally count as self-erasure proof
```

Do not call a loss "self-erasure-resistant" without saying exactly **which class
of edits it resists**.

---

# III. PRESSING ISSUE 2 — exposure-gate consequential debt

The current loss penalizes:

```text
commitments_C(H) - ack[H]
```

as unacknowledged consequential commitments.

Press this aggressively.

In a rich inferential system, a critic may attribute a very large set of
consequences to a reasoner. It is not obvious that the reasoner is normatively
defective merely because it has not explicitly acknowledged every consequence.

The current representation risks turning consequential closure into an implicit
logical-omniscience requirement.

Test the alternative hypothesis:

> A consequential commitment becomes chargeable as answerability debt only once
> it has been publicly **exposed** as an issue requiring response.

Possible exposure events include:

```text
challenge
query
explicit attribution
docket/service demand
request for justification
```

Do not build a full inquiry system.

Implement the smallest finite notion that distinguishes:

```text
latent consequence
```

from:

```text
exposed consequential burden
```

A candidate structure is:

```text
ExposedConsequence_C(H,q)
    iff
q is consequentially attributable to H by C
and q has been made the object of a public query/challenge/demand
```

The precise representation is for this pass to decide.

## Required tests

At minimum:

1. `q` follows from `p` for `C`, but `q` has not been raised.

   * `C` may attribute `q`.
   * The theorem-facing learning loss should not automatically require H to
     explicitly acknowledge it unless you can justify that stronger rule.

2. `q` is publicly exposed.

   * The burden becomes chargeable.

3. H changes only `practice[H]`.

   * The exposed burden remains.

4. H gives a recognized disposition.

   * The burden can fall.

5. The burden is not erased simply because H stops locally deriving `q`.

Use this to test the emerging architecture:

```text
inferential closure
    -> latent consequential commitments

inquiry/challenge/service
    -> some commitments become due

answerability loss
    -> measures mishandling of due burdens
```

If you retain the ungated loss, explain precisely why it does not amount to a
logical-omniscience norm.

---

# IV. PRESSING ISSUE 3 — restore the legality / normative compilation / performance separation

The current round says reasons-responsiveness "reduces and thins", and suggests
that on the doxastic side much of its work is relocated into the loss.

Do not accept that conclusion without prosecution.

The previous architecture deliberately separated:

```text
what transformations count as normatively lawful
```

from:

```text
which lawful transformations perform better
```

That separation is load-bearing.

If normative lawfulness is defined by whether a transformation lowers the loss,
the learner can game the normative criterion through optimization.

## Audit three distinct notions

Explicitly distinguish:

```text
1. protocol legality
   can the transition grammar execute this move?

2. normative compilation / reasons-responsiveness
   is this transformation licensed by public reasons, entitlement,
   authority, defeater state, exposure state, etc.?

3. performance
   what answerability loss does the resulting action incur?
```

`apply_move` legality is not automatically substantive reasons-responsiveness.

Likewise, the synthetic `RESPONSIVE` / `TOLERANT` notions in `collapse.py` are
currently loss-defined.

They are acceptable as **collapse diagnostics**.

They are not acceptable as the theorem-facing normative lawfulness predicate.

## Required refinement

Create a minimal explicit compilation layer:

```text
PublicStatus
      |
      v
NormativeCertificate / Compiler
      |
      v
fixed Program induces F_phi^t
      |
      v
loss evaluates the result
```

The compiler may inspect public normative statuses.

It may not inspect:

```text
loss
charge
saving
profit
comparative advantage
regret
future value
horizon
```

But mere blindness to loss is not sufficient.

For each nonidentity comparator intended to count as normatively lawful, state
the **positive public reason** that licenses it.

For example:

```text
acknowledge_exposed
    licensed by an exposed consequential burden

suspend_defeated
    licensed by defeated entitlement to applicability

vindicate_live
    licensed by a live challenge plus available recognized justification

reopen_not_disavow
    licensed by a live unresolved challenge

defer_where_permitted
    licensed by a testimonial/deference entitlement route
```

Implement this as data/checks rather than only prose if possible.

If the model cannot supply such a certificate without recovering arbitrary
state-indexed recertification, report that as a negative result.

## Required conceptual verdict

Update `TWO_ARC_INTERFACE.md` to distinguish:

```text
protocol legality
substantive reasons-responsiveness / normative compilation
answerability loss
```

Do not claim RR has disappeared if what has actually happened is that it has been
compressed into the normative compiler.

A plausible positive verdict would be:

> Reasons-responsiveness is substantially thinned into a public normative
> compilation interface, while loss remains purely comparative performance.

Do not force that verdict.

---

# V. PRESSING ISSUE 4 — preserve commitment vs entitlement correctly

The current model declares a simplification:

> committive rules transmit entitlement as well as commitment.

But the architecture explicitly distinguishes:

```text
commitment-preserving inference
```

from:

```text
entitlement-preserving inference
```

Press whether the current shortcut is doing hidden work.

Try the more faithful representation:

```text
committive rules
    -> consequential commitment only

permissive rules
    -> entitlement inheritance
```

If a particular inferential pattern should preserve both commitment and
entitlement, represent it explicitly in both relations.

For example:

```text
p =>_C q
p =>_E q
```

may both be present.

Do not make every committive rule entitlement-preserving by default.

## Required tests

Show at least one case where:

```text
p =>_C q
```

holds but:

```text
p =>_E q
```

does not.

The target should become committed to `q` without thereby becoming entitled to
`q`.

Also show at least one case where entitlement does transmit because a permissive
rule is explicitly present.

Then rerun:

```text
undercutter behavior
challenge behavior
loss components
reified applicability
vindication
```

to see whether any previous positive result depended on the shortcut.

If the separation breaks a headline result, do not patch around it silently.
Report the dependency.

---

# VI. PRESSING ISSUE 5 — audit semantic action labels

Audit whether the eight semantic learning labels actually perform the normative
operation their names claim.

At minimum inspect:

```text
SUSPEND
REOPEN
VINDICATE
ACKNOWLEDGE
SELF_REVISE
DISAVOW
```

## A. `SUSPEND`

The current decoder maps:

```text
SUSPEND -> disavow
```

But:

```text
suspending reliance on an entitlement
```

is not generally the same as:

```text
retracting the commitment
```

This is especially important for reified applicability, where the intended
structure is:

```text
commitment to A_rho may remain
while entitlement to deploy A_rho is defeated
```

Preferred outcomes:

1. implement a genuinely distinct suspension / non-use status if needed;
2. rename the semantic label if the move really is retraction;
3. show that a separate suspension state is unnecessary and why.

Do not leave a semantic mismatch in theorem-facing code.

## B. `REOPEN`

The current decoder uses `query` as the realization of reopening.

Check whether `query` actually changes anything.

If `query` is a no-op on state, then calling it `REOPEN` may be merely descriptive.

A real reopening should probably change some public burden/status, or else the
learning theorem is comparing labels that are semantically distinct but
transition-identical.

If `query` is intended to be a public event rather than a state change, represent
that event explicitly enough that future loss/status can depend on it.

## C. `VINDICATE`

Check that vindication does not merely write a terminal bit that permanently
suppresses a challenge regardless of later undercutters or changed reasons.

If a later defeater can undermine the displayed justification, determine whether
the challenge should reopen.

Do not build full nonmonotonic adjudication unless needed, but identify the
minimum semantics necessary for the current theorem claims.

## Required output

Add a compact semantic-action table to `MODEL.md` or a new
`ACTION_SEMANTICS.md`:

```text
label
decoded move
state effect
normative interpretation
possible mismatch
final disposition
```

No theorem-facing label should intentionally misdescribe its actual operation.

---

# VII. PRESSING ISSUE 6 — endogenous evolution

The current recurrent-failure witness resets to the same loaded position at each
date.

This makes the comparison additive by construction.

The PR itself correctly identifies **endogenous evolution** as the sharpest
untested hypothesis.

This pass must push on it.

Do not attempt to solve the full general counterfactual-replay problem.

Construct the smallest evolving scorekeeping process in which a repair at time
`t` changes the scorekeeping state seen at `t+1`.

For example:

```text
t:
    an exposed consequential burden exists

learner response:
    acknowledge / vindicate / reopen / hold

t+1:
    the next public status is computed from the actual resulting state
```

Compare actual and transformed trajectories.

## Required questions

For at least one comparator:

```text
phi = acknowledge_exposed
```

or another clean candidate, determine:

1. Does applying `phi` now change future burdens?
2. Does the local loss saving equal the full replay saving?
3. If not, what is the distortion term?
4. Is the cumulative discrepancy:

   * zero,
   * uniformly bounded,
   * sublinear,
   * or potentially linear?

Do this exactly on a finite toy process.

## Required result shape

The useful possibilities are:

### Positive

There exists a nontrivial evolving fixture where:

```text
|local comparator regret - replay comparator regret| <= B
```

for horizon-independent `B`, or another clearly sublinear bound.

### Mixed

Some programs admit bounded/sublinear distortion and others do not.

This would be valuable: it could define the theorem-facing comparator subclass.

### Negative

Even the simplest answerability repairs produce linear replay distortion.

If so, the current additive Φ-regret bridge is not enough for the intended
normative-learning theorem, and the verdict should be downgraded accordingly.

Do not simulate by re-filing the same state in this test.

---

# VIII. Press the fixed-program comparator diagnosis

The current result says the comparator collapse was an artifact of requiring one
state-independent map, while the online-learning theorem permits a fixed rule
inducing state/history-indexed maps.

This is promising and must survive a sharper audit.

## Required test

For every theorem-facing comparator program, verify:

```text
program syntax is fixed
program has no callable
program cannot inspect date merely as date
program cannot inspect loss/profit/future
program may inspect only declared public normative status
same relevant public status -> same induced map
```

But also test the converse pressure:

> Is the six-Boolean `PublicStatus` only avoiding date-indexed certification by
> being too weak?

Construct at least one pair of states with:

```text
same PublicStatus
```

but where a normatively adequate repair should arguably differ because of a
difference the status currently throws away.

Candidate hidden differences:

```text
which content is challenged
which warrant is defeated
who raised the challenge
scope / authority source
provenance / entitlement ancestry
which practical subject is involved
```

If such a pair exists, the public status must either be enriched or the comparator
class admitted to be too weak.

The target is not "no date field."

The target is:

```text
a sufficient public normative statistic for lawful fixed programs
```

without reopening capture.

This may be the real comparator-interface theorem we need.

---

# IX. Press self-certification beyond one-agent write separation

The current positive result explicitly repairs self-certification only for a
reasoner acting alone.

That limitation is acceptable, but prosecute it one step further.

Do not build a full collusion theory.

Construct the smallest test involving:

```text
H
C
```

where both agents revise their practices in coordinated ways.

Ask whether a previously live burden can disappear solely because both parties
change their standards while the public acknowledged history stays fixed.

If yes, state exactly:

```text
relational scorekeeping prevents unilateral self-release
but not coordinated standards drift
```

Then ask whether this is:

1. a genuine defect in the intended theory;
2. acceptable because answerability is always relative to current interlocutors;
3. evidence that a third/world-responsive source is required;
4. evidence that inquiry/noninferential authority must remain a separate layer.

Do not introduce an oracle merely to defeat the witness.

The purpose is to know what the shared substrate really buys.

---

# X. Reassess the corrigibility side conservatively

The current result on corrigibility is useful:

* epistemic authority and practical jurisdiction are operationally distinct;
* the advisor lacks a reserved authority subject;
* protected capability survives every advisor-only run by invariant;
* standing and access are independent.

Preserve those if they survive.

But tighten the interpretation.

The current protection is **arranged, not derived**.

The fixture starts with a favorable authority allocation.

Do not call this a corrigibility theorem.

The strongest warranted statement is closer to:

> Once scoped practical authority is represented as a transition-relevant
> coordinate, advisor-robust preservation of a principal's corrective authority
> becomes a precise invariant/reachability question.

## Required refinement

Update prose so it distinguishes:

```text
authorization representation
```

from:

```text
normative justification of the initial authority allocation
```

from:

```text
causal protection of that allocation under advisor policies
```

Those are three different objects.

Also check whether any learning-side modification introduced in this refinement
accidentally allows the advisor to affect grants or standing.

Rerun all C1–C7 tests after every structural change.

---

# XI. Reassess the disposition of the existing architecture

After the technical refinements, rewrite the relevant part of
`TWO_ARC_INTERFACE.md`.

Do not preserve the current disposition table if the pass changes it.

Explicitly reassess:

```text
constraint statics
warrants
strict consequence
permissive inference
reified applicability
defeaters / undercutters
credal support
multiplicative propagation
LP / dual enforcement
provenance
reasons-responsiveness
inquiry
docket / service
diachronic answerability
settlement
```

A likely architecture to test is:

```text
QUALITATIVE NORMATIVE PRACTICE
    perspectival commitments / entitlements
    inferential roles
    reified applicability
    challenge and practical authority

QUANTITATIVE CONSTRAINT ENRICHMENT
    graded support
    credal sets
    propagation
    LP/dual machinery

ANSWERABILITY GENERATION
    inquiry / exposure / service
    makes latent commitments due

DIACHRONIC TRANSPORT
    needed primarily across vocabulary / ontology change

LEARNING CONSUMER
    bounded due-burden loss
    public lawful repair programs
    online regret
    counterfactual stability

CORRIGIBILITY CONSUMER
    normative standing / jurisdiction
    protected effective access
```

Do not adopt this merely because it is elegant.

State where evidence supports it and where it remains conjectural.

---

# XII. Required new/updated tests

At minimum add tests covering:

1. exact dependency audit for every theorem-facing loss term;
2. self-revision cannot erase an exposed burden;
3. legitimate answer can reduce the burden;
4. latent consequence vs exposed consequence;
5. committive inference without entitlement inheritance;
6. permissive inference with entitlement inheritance;
7. `SUSPEND` semantics;
8. `REOPEN` has a real public effect or is renamed;
9. compiler lawfulness does not inspect loss;
10. every nonidentity theorem-facing program has an explicit normative certificate;
11. same relevant public status gives same comparator map;
12. same current six booleans but normatively different hidden state, if such a
    counterexample exists;
13. at least one genuinely endogenous evolving trajectory;
14. local-vs-replay distortion on that trajectory;
15. coordinated H/C standards drift witness;
16. all existing corrigibility invariants still pass.

Use exact arithmetic.

Prefer exhaustive finite checks where possible.

---

# XIII. Evidence classes and theorem claims

Keep the evidence discipline strict.

Nothing in this refinement becomes a general theorem merely because more tests
pass.

Distinguish:

```text
fixture theorem / exact finite check
finite exhaustive characterization
unbounded invariant
derived source-theorem instantiation
open conjecture
```

If a current prose claim is stronger than the implementation, weaken the prose.

If the implementation can cheaply be strengthened to justify the prose, strengthen
the implementation.

Do not resolve a mismatch by leaving both.

---

# XIV. Verdict reconsideration

Re-grade the PR at the end.

Use `Shared-substrate-positive` only if, after this pass:

1. unilateral self-release remains structurally blocked;
2. the theorem-facing answerability loss has a precise non-laundering guarantee;
3. exposure-gated or otherwise defensible burden semantics avoids a hidden
   logical-omniscience obligation;
4. commitment and entitlement remain genuinely distinct;
5. normative compilation remains separate from loss/performance;
6. at least one nontrivial fixed public comparator remains lawfully certifiable;
7. endogenous evolution does not immediately destroy the learning interface, or
   the surviving boundary is sharply identified;
8. epistemic authority and practical jurisdiction remain operationally distinct;
9. normative standing and protected access remain independent.

Possible downgraded verdicts include:

```text
Shared-representation-positive / learning-interface-open
Learning-positive / corrigibility-interface-positive / replay-blocked
Representation-positive / theorem-neutral
Refuted
```

Invent a sharper label if necessary.

Do not grade generously.

---

# XV. What the updated PR must answer

By the end of this pass, a reader should know:

### 1. What exactly is the theorem-facing learning loss?

Not just a formula: what normative phenomenon does each term represent?

### 2. Which learner edits can and cannot erase it?

State the class exactly.

### 3. When does a latent consequential commitment become a due burden?

### 4. What makes a comparator transformation normatively lawful independently of

its loss?

### 5. Does the fixed-program solution to comparator collapse survive once public

status is made sufficiently expressive?

### 6. Do committive and entitlement-preserving inference remain distinct?

### 7. Does reified applicability still work after that distinction is enforced?

### 8. What survives under endogenous state evolution?

### 9. Is scorekeeping really replacing reasons-responsiveness, or is it supplying

a better normative compiler for it?

### 10. What exactly remains of inquiry and diachronic answerability?

### 11. What does the corrigibility arc get from the shared substrate, and what

still comes only from the execution/control model?

### 12. Is the best project-level architecture still:

```text
answerability practice + online performance
    -> normative learning

answerability practice + protected effective access
    -> legitimate corrigibility
```

If yes, state the remaining missing hypotheses on each arrow.

---

# XVI. Update PR #29 in place

When complete:

1. run the round test suite;
2. run the full repo Python test runner;
3. run checkers;
4. run relevant Lean/CI checks required by the repository;
5. commit the refinement on the existing PR branch;
6. push;
7. update PR #29's body to reflect the new exact verdict and results.

Do **not** open another PR.

Do **not** merge PR #29.

The updated PR body should include a short section:

```text
## Refinement pass
```

covering:

* whether the loss dependency overclaim was confirmed and how it was repaired;
* whether consequential loss is now exposure-gated;
* the final legality / normative compilation / performance separation;
* whether committive vs permissive inference was repaired;
* any semantic action renames or new state;
* the endogenous-evolution result;
* whether the fixed-program comparator diagnosis survived;
* coordinated standards-drift result;
* final verdict;
* what remains blocking before the architecture should be reorganized around this
  substrate.

Follow all repository DCO and attribution rules.

Commit trailers must include:

```text
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Model: <executor's accurate self-identification>
```

Do not sign prose or commits in the maintainer's voice.

The standard for this pass is not:

> Can the current positive story be defended?

It is:

> After attacking the theorem-facing loss, legality boundary, semantic actions,
> comparator interface, and endogenous dynamics, what exact part of the relational
> scorekeeping architecture is still doing real mathematical work?
