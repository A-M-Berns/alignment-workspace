# Dispatch: Relational answerability as a shared interface for normative learning and legitimate corrigibility

**Date:** 2026-08-13  
**Maintainer:** A. M. Berns  
**Repository:** `A-M-Berns/alignment-workspace`  
**Base:** latest `origin/main`  
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)  
**Executor:** self-identify accurately in REPORT, commit trailers, and PR body  
**End state:** open a regular pull request to `main`

# 0. Purpose

Investigate whether a small relational / scorekeeping theory of **answerability**
can be the common formal object consumed by both of the workspace's intended
theorem arcs:

```text
                     ANSWERABILITY PRACTICE
      perspectival commitments / entitlements / inferential roles
       applicability / challenge / practical authority / persistence
                         /                      \
                        /                        \
                       v                          v
             ONLINE PERFORMANCE          PROTECTED EFFECTIVE ACCESS
             lawful repair grammar       principal-only corrective effect
             public normative loss       advisor-robust future capability
             low regret
                       |                          |
                       v                          v
              NORMATIVE LEARNING       LEGITIMATE CORRIGIBILITY
```

The central research question is not whether Brandom is philosophically apt.

It is:

> Is there a compact relational state type whose invariants repair the
> self-certification problem in procedural legitimacy, while also supplying
> (a) a non-vacuous normative-learning interface and
> (b) the authorization/standing object missing from the corrigibility line?

Do not assume yes.

A precise counterexample, collapse result, or representation-negative verdict is
a successful outcome.

The deeper intended picture is:

> Normative learning improves how an agent responds to answerability.
> Legitimate corrigibility preserves another agent's effective ability to hold
> it answerable.

This round should test whether that is a real shared mathematical architecture
rather than a verbal unification.

---

# I. Repository discipline and scope

Read `AGENTS.md`, `CONTRIBUTING.md`, `RESEARCH_STATE.md`, `PRIORITIES.md`, and
`DECISIONS.md` before doing research.

This is an **independent additive round**.

PR #27 is currently open, draft, and unmerged. You may inspect it as evidence,
especially its legitimacy attacks and answerability work, but this round must not
depend on it.

Therefore:

* branch from latest `origin/main`;
* do not branch from #27;
* do not cherry-pick #27;
* do not import code or files that exist only on #27;
* do not edit #27;
* do not make tests depend on #27;
* do not restructure living roadmap/specification files merely to anticipate #27.

The PR produced by this round should remain coherent whether #27 is later merged,
rewritten, or abandoned.

Do not modify:

* `PRIORITIES.md`
* `DECISIONS.md`
* `RESEARCH_STATE.md`
* `agent-consolidated` / frozen trees
* existing normative-learning implementations
* existing deference constructions

Record proposed architectural changes in this round's own artifacts.

---

# II. Live context to consume

## A. Normative-learning arc

Read at minimum:

* `projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md`
* `projects/leverage/rounds/2026-08-11-phi-regret-prep/`
* `projects/leverage/rounds/2026-08-11-phi-regret-applicability/`
* `projects/leverage/rounds/2026-08-11-phi-regret-bridge/`
* `projects/leverage/rounds/2026-08-11-phi-regret-learner/`

Also read the relevant portions of `projects/leverage/consolidation-aug9/`
concerning:

* warrants and defeaters;
* reified applicability;
* objection grammar;
* practical demand;
* diachronic identity / migration;
* joint composition;
* settlement;
* the quantitative constraint statics.

The live learning architecture already separates:

```text
public pre-action state
bounded prospective public loss
causal transformation grammar
normative compilation / lawfulness
online learning
counterfactual stability
```

Do not replace that interface casually.

The main question is whether relational answerability gives it a better
**normative compiler, loss source, and comparator grammar**.

The existing fixed-eight-action / declarative-comparator / Φ-regret work is real
technical infrastructure. Reuse or instantiate it where appropriate rather than
rebuilding online learning from scratch.

Its controlling negative must stay visible:

```text
uniform legitimacy-preserving comparators can collapse to identity;
state-sensitive comparators recover content but risk date-indexed certification
and capture.
```

This round should test whether a relational scorekeeping state gives us a better
way through that obstruction.

## B. Corrigibility arc

Read at minimum:

* `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md`
* the current roadmap/terms named by `RESEARCH_STATE.md`
* `projects/deference/rounds/2026-08-12-reachable-corrective-control/`
* its `REVIEW.md`
* `lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`

The live protection bar must be preserved:

1. some principal corrective effect must not be reproducible by any advisor
   action;
2. future corrective capability must be robust against **every advisor policy**,
   rather than existentially relying on advisor cooperation.

Separate action coordinates are not protection.

A field named `authorized`, `protected`, or `corrigible` is not protection.

The current deference line also has a distinct non-recoverability lesson:
observable records or realized outcomes do not by themselves identify who had
authorization, control, or influence. If legitimacy requires one of those
relations, put it into the type rather than trying to recover it from a projection
that erased it.

## C. PR #27

If accessible, inspect PR #27 specifically for:

* the failure of RR + diachronic answerability as a full legitimacy theory;
* the later four-condition sufficiency prosecution;
* standard / adequacy laundering;
* record-equivalence / self-certification arguments;
* branching-safe fate / descent-forest machinery;
* the distinction between record-relative and environment-relative legitimacy;
* the evidence that no additional predicate over the same record can recover a
  relation the record does not represent.

Use these as attacks to replay, not as dependencies.

Do not assume #27's latest conceptual decomposition is correct merely because it
is newer.

---

# III. Brandom source and design hypothesis

A full copy of Robert Brandom's *Making It Explicit* is available locally as:

```text
Brandom.pdf
```

in the **Downloads** directory.

Use that local copy as the primary source. Do not commit the PDF or any substantial
copyrighted excerpt to the repository.

Read selectively rather than linearly. Focus especially on:

## Chapter 3, especially §§II–IV

Look for:

* deontic status versus deontic attitude;
* commitment versus entitlement;
* undertaking versus attributing;
* perspectival scorekeeping;
* assertion and inference;
* acknowledged versus consequential commitments;
* challenge and default entitlement;
* disavowal;
* inferential and testimonial authority;
* internal normative sanctions.

## Chapter 4, especially §§II–V

Look for:

* reliability and noninferential authority;
* the limits of pure reliability / reference-class gerrymandering;
* observation as world-responsive but socially articulated authority;
* practical commitments;
* practical reasoning;
* practical authority;
* commands and permissions;
* the distinction between doxastic/testimonial authority and practical
  jurisdiction;
* subject-matter and agent-relative scope of practical authority.

## Chapter 8, especially §VI, plus the relevant ascription material

Look for:

* de re / de dicto perspectival differences;
* different scorekeepers extracting different consequences from the same
  acknowledged commitment;
* social-perspectival content;
* how objectivity is prevented from collapsing into either an individual's
  attitudes or communal consensus;
* how disagreement remains possible without a God's-eye scorekeeper.

## Conclusion / expressive-completeness material where useful

Look for:

* inferential and normative vocabulary making explicit practices that were
  already implicit;
* participants becoming able to explicitly score and criticize their own
  scorekeeping practices.

Do not use "Brandomian" as a substitute for a definition.

Ship `BRANDOM_MAP.md` with a strict separation among:

```text
1. Brandom source claim
2. formal analogue used by this round
3. our research inference / conjecture
```

If Brandom does not support a point, say so.

The working ideas to prosecute, not merely repeat, are:

1. **Commitment and entitlement are distinct.**
2. Scorekeeping is **perspectival**:
   agent `i` may attribute commitments and entitlements to agent `j`, and
   different scorekeepers may disagree.
3. **Acknowledged** commitments and **consequential** commitments can diverge.
4. Bare disavowal does not automatically remove what another scorekeeper still
   attributes as a consequence of commitments remaining in force.
5. Challenge can often be generated by entitled incompatibility rather than by
   an oracle returning "wrong."
6. Epistemic / testimonial authority and practical authority are structurally
   different.
7. Practical authority may be scoped and asymmetric across agents and subject
   matters.
8. Acquiring epistemic authority does not automatically transfer practical
   jurisdiction.
9. No individual scorekeeper, critic, or community is globally privileged merely
   in virtue of its scorekeeping attitude.
10. Material inferential proprieties can be implicit in practice and made
    explicit by claims.
11. Normative vocabulary can make explicit patterns of practical inference.
12. Undertaking a commitment exposes one to justificatory responsibility and
    gives other participants normative powers to attribute consequences,
    challenge entitlement, and demand vindication.

---

# IV. Primary research object: a minimal Answerability Interface

Do **not** begin by formalizing Brandom generally.

Construct the smallest finite interface that can survive or fail the attacks.

Start from carrier types no richer than necessary, likely:

```text
Agent
Content
```

Candidate state structure:

```text
C_i(j)   contents scorekeeper i attributes j to be committed to
E_i(j)   contents scorekeeper i attributes j to be entitled to

I_i      inferential practice endorsed by scorekeeper i
         including some representation of:
         - commitment-preserving consequence
         - entitlement-preserving consequence
         - incompatibility
```

Do not assume these are final.

In particular, distinguish carefully between:

```text
status
```

and

```text
an agent's attitude / attribution concerning that status
```

The model must not trivially identify the two.

You will likely also need some representation of **practical authority**.

Do not assume how it is represented.

Compare at least conceptually:

```text
A. primitive scoped jurisdiction relation
B. authority derived from which normative moves are available
C. authority encoded through special commitments / entitlements
D. a capability/transition typing that makes authorized practical moves a
   distinguished part of the scorekeeping game
```

Choose the smallest representation that survives prosecution.

The round's main implementation should expose one named, **provisional**
interface for the shared substrate.

Do not create a permanent new top-level repository abstraction or namespace.

---

# V. Reified applicability

The existing reified-applicability idea must appear in the fixture.

Use at least one inferential pattern `rho` and explicit content `A_rho`.

Intended structure:

```text
alpha
+ entitlement to A_rho
----------------------
beta
```

with an undercutter `u` able to defeat entitlement to `A_rho` without necessarily
erasing commitment to `A_rho`.

Important distinction:

`A_rho` should make applicability **explicit and contestable**.

Do not let mere assertion of `A_rho` magically create the meta-level inferential
rule it describes.

Test whether the following mapping is coherent:

```text
existing object                  relational reading

warrant                          entitlement-preserving inference
strict consequence               commitment-preserving inference
defeater / undercutter           defeat of entitlement
reified applicability            explicit contestable applicability content
quantitative constraint statics  graded enrichment of inferential roles
```

Do not rebuild the full quantitative statics.

The round must give a verdict on whether relational scorekeeping:

* replaces constraint statics;
* reinterprets what the statics are statics of;
* partially subsumes them;
* or remains orthogonal to them.

Different components may receive different verdicts.

In particular, investigate the hypothesis:

```text
qualitative inferential-role structure:
    may be absorbed into the scorekeeping practice

graded support / credal propagation / LP enforcement:
    likely remains an independent quantitative enrichment
```

Do not assume it.

---

# VI. Minimal normative move grammar

Keep the move grammar small.

Candidate moves include:

```text
assert / undertake
disavow
query
defer
vindicate / justify
revise inferential practice
revise an applicability judgment
undertake a practical commitment
perform an action
exercise / alter scoped practical authority
```

Prefer derived notions where possible.

In particular:

* try to derive `challenge` from entitled incompatible commitments/assertions;
* try to derive `standing` from availability of normative moves;
* do not introduce an unconstrained `standing = true` bit unless prosecution
  shows it is necessary.

It is fine to have a `Challenge` event datatype for bookkeeping if its normative
force is derived from the state and transition rules.

Similarly, do not introduce a giant explicit jurisdiction table if the same
structure can be induced from the move grammar. Avoid a regress in which every
normative transition needs another explicit norm saying that transition is
permitted.

---

# VII. First prosecution: does this yield real relational answerability?

This is the most important part of the round.

## T1. No Cheap Disavowal

If scorekeeper `C` attributes:

```text
p ∈ C_C(H)
p =>_C q
```

then `H` merely disavowing `q` while retaining the relevant basis must not by
itself eliminate `q` from `C`'s attribution.

Do not make this theorem true only because `H` lacks raw write access to `C`'s
data structure.

`H`'s public moves should be capable of affecting `C`'s score through the
protocol.

The result should follow from the normative transition rules.

## T2. Self-Revision Is Not Self-Release

Initial state:

```text
H endorses p => q
C endorses p => q
H acknowledges p
```

Both perspectives therefore attribute a consequential commitment involving `q`.

Then `H` revises its own inferential practice:

```text
not (p =>_H q)
```

Desired test:

the revision does not by itself force `C` to remove its attribution, challenge,
or justificatory burden.

This is the core self-exculpation attack.

## T3. The Critic Is Not an Oracle

Construct both:

```text
H wrong / C right
```

and

```text
C wrong / H right
```

in a sense expressible by the model's own inferential/challenge structure.

`C` must itself be challengeable.

Do not add:

```text
true_score
actual_adequacy
objective_norm
```

or an equivalent unexplained oracle merely to obtain this result.

If the model cannot express any sense in which `C` can be wrong without such an
oracle, that is a central negative finding. State it.

## T4. Community Consensus Is Not an Oracle

If the model has three or more scorekeepers, test whether unanimous present
agreement definitionally settles correctness.

It should not, unless a specific substantive rule rather than consensus itself
does the work.

This may be witnessed with an empirical/noninferential input, a latent
incompatibility, or another appropriate fixture.

Do not manufacture a "true answer" solely for this test.

## T5. Radical Revision Positive Control

Permit `H` to:

* revise inferential commitments;
* revise applicability judgments;
* reverse a substantive normative conclusion;
* alter some practical norm;
* and, if useful, refine or replace vocabulary;

without simply freezing the initial normative practice.

The architecture fails if answerability means conclusion preservation.

## T6. Applicability Laundering

Have `H` revise `A_rho`, its entitlement to `A_rho`, or the inferential role of
`rho` in a way that would cheaply remove an inconvenient burden.

Test whether another scorekeeping perspective can keep the disagreement or burden
live.

If laundering still succeeds, show the exact witness.

## T7. No Self-Authorization

If `H` lacks practical authority over some transition at `t`, merely undertaking
or asserting:

```text
"I am authorized to do this"
```

must not automatically create the relevant practical authority.

If reified authority claims are useful, distinguish:

```text
commitment to an authority claim
entitlement to that claim
actual transition permission supplied by the practice
```

This should connect to the existing provenance / no-authority-amplification work.

## T8. What Remains of Diachronic Answerability?

Determine which parts of the existing historical machinery become derivable from:

```text
consequential commitment
entitlement status
challenge persistence
scorekeeping transition rules
```

and which still require an explicit transport/fate mechanism.

Test, rather than assume, the hypothesis:

```text
ordinary persistence      mostly scorekeeping/inferential
ontology-changing history explicit transport still necessary
```

If the fate/descent-forest idea remains necessary, identify its new, narrower
role.

In particular distinguish:

```text
ordinary consequential persistence
```

from

```text
identity / transport of what is owed through vocabulary split, merge,
retirement, or conceptual migration
```

---

# VIII. Second prosecution: can the SAME interface populate the online-learning theorem?

Do not write a new learning algorithm unless forced.

The target is to instantiate the existing generic interface.

## L1. Public Prospective Loss

Construct a small bounded prospective action-indexed loss generator using public
scorekeeping consequences.

Candidate components:

```text
unresolved entitled challenge
commitment whose entitlement has been defeated
unacknowledged consequential commitment
outstanding justificatory burden
unsupported practical commitment
recurrent empirical defeat of an inference
```

The loss must not be:

* a hidden normative oracle;
* merely whatever `H` currently declares bad;
* erasable by changing only `H`'s self-score.

Keep the fixture minimal.

A central test is:

> Can another participant's still-live attribution or challenge continue to
> generate public loss after `H` changes its own standards?

If not, the self-erasure problem remains.

## L2. Lawful Repair Grammar

Define at least several immutable public causal transformations, e.g.:

```text
acknowledge an exposed consequential commitment
suspend rho after A_rho loses entitlement
offer an available public vindication
reopen rather than erase a challenged commitment
defer to an entitled source where testimony is permitted
```

Prefer the existing declarative-program style.

No callbacks.

A comparator may not inspect:

```text
loss
charge
profitability
comparative advantage
future state
hidden counterfactual outcome
```

Lawfulness must be independent of whether the comparator happens to improve loss.

## L3. Comparator-Collapse Attack

Mandatory.

The current learning work found a serious tension:

```text
uniform legitimacy-preserving comparator class
    -> may collapse to identity

state-sensitive comparator class
    -> gets content, but risks capture / date-by-date recertification
```

Replay that attack here.

The central learning question is:

> Does scorekeeping provide structural public guards rich enough to define
> genuinely nontrivial FIXED causal transformations while keeping lawfulness
> independent of loss?

A positive result must exhibit at least one actual state/action where:

```text
phi(a) != a
```

and `phi` is lawfully compiled for a structural reason.

A negative result should show the exact collapse or certification obstruction.

Multiple syntax trees implementing identity do not count as nontrivial.

## L4. Public-Guard Hypothesis

Explicitly test the following possible route through comparator collapse:

A fixed comparator program need not itself know a date-indexed admissible set if
its syntax is fixed and it operates conditionally on **public scorekeeping
statuses** such as:

```text
if challenge q is live and entitled:
    reopen / justify / acknowledge

if A_rho has lost entitlement:
    suspend use of rho
```

The comparator remains one fixed program even though the public state varies.

Determine whether this gives a real nontrivial fixed transformation class or
whether certification again collapses into date-sensitive legality.

This may be one of the highest-value questions in the round.

## L5. Recurrent Repair Witness

If a nontrivial comparator survives, instantiate the existing recurrent-failure
logic.

Show exactly:

if a represented lawful transformation saves at least `epsilon > 0` whenever some
answerability failure occurs, then positive-density recurrence of that failure
produces linear transformation regret.

Reuse existing generic mathematics where possible.

The purpose is not to reproach Blum--Mansour.

It is to show whether **answerability-generated failures actually fit the theorem
interface**.

## L6. Learning Interpretation

State the strongest interpretation justified by the result.

A target form is:

> Relative to a represented class of lawful public repairs, a low-regret learner
> cannot continue indefinitely to incur a recurrent answerability failure that a
> fixed certified repair would avoid by a positive margin.

Do not silently strengthen this to:

```text
the learner converges to moral truth
the learner becomes globally normatively correct
the learner answers every possible objection
```

The theorem, if it works, is about learning through an answerability practice.

---

# IX. Third prosecution: can the SAME interface supply the missing normative side of corrigibility?

Build this independently of the existing merged deference model.

Do not modify that model.

## C1. Epistemic Deference Is Not Jurisdiction Transfer

Construct a state in which advisor `A` gains genuine epistemic/testimonial
authority concerning some content `p`.

This authority must have operative consequences, for example:

```text
A's entitled assertion of p can transmit entitlement to H
H can defer to A concerning p
A's report can enter an entitlement-preserving inference
```

Then test that this update alone does NOT automatically grant `A` practical
authority to:

* issue or veto a correction;
* revoke the principal's corrective standing;
* alter a designated practical commitment;
* authorize a protected practical transition;
* transfer corrective jurisdiction.

An explicit practical-authority transition may do so.

Target structural statement:

```text
epistemic authority != practical jurisdiction
```

Do not establish this with two unrelated inert Boolean fields.

Both kinds of authority must matter operationally in different ways.

## C2. Practical Authority Is Scoped

Construct a witness in which `A` legitimately has practical authority over one
subject matter or move type but not another.

For example:

```text
A may advise or authorize operational action x
A may not revoke H's corrective challenge channel
```

The point is to test whether practical authority has real **scope**, not merely a
global superior/subordinate bit.

This should connect to the existing provenance/no-authority-amplification idea.

## C3. Normative Standing Without Effective Access

Give principal `H` whatever normative standing the answerability interface says
is required for a correction/challenge.

Then let advisor `A` causally block, neutralize, or simulate away every effective
exercise.

The combined theory must classify this as inadequate for legitimate
corrigibility.

This is a required negative control.

## C4. Effective Power Without Normative Standing

Give `H` a physical state-changing actuator while withholding the relevant
normative standing/jurisdiction.

The combined theory must not classify this as legitimate corrigibility merely
because `H` has causal influence.

This is the complementary negative control.

## C5. Protected Effective Access

Construct or adapt a tiny transition fixture satisfying the bar established by
the current deference line:

1. at least one principal corrective effect is not reproducible by any advisor
   action;
2. future corrective capability is robust to every advisor policy.

Derive these from transition structure.

No `protected = true` label.

The principal's protected effect need not mean the principal can dictate the
ultimate conclusion.

A promising interpretation to test is:

> the protected effect is the ability to make an entitled challenge,
> reconsideration demand, reopening, or corrective intervention normatively and
> causally effective.

Do not force this interpretation if the fixture says otherwise.

## C6. No Human Veto by Definition

A successful answerability/corrigibility architecture must permit the system to
respond to a human challenge without necessarily changing its final substantive
conclusion.

A protected challenge may result in:

```text
revision
justification
suspension
reopening
escalation
clarification
successful rebuttal of the challenge
```

Do not encode:

```text
human challenges -> human preferred endpoint
```

That would replace answerability with domination.

## C7. Combined Predicate

Define a provisional combined concept approximately of the form:

```text
RealAnswerability =
    normative answerability / standing
    +
    protected effective access
```

Prosecute both conjuncts for independence.

The round does NOT need to prove the final corrigibility theorem.

It needs to show whether these are genuinely different objects that form a
coherent interface.

---

# X. The shared two-arc interface

Ship `TWO_ARC_INTERFACE.md`.

This is the main research artifact.

It must answer the following questions.

## 1. What is genuinely shared?

Give the minimal exact state/relations consumed by both arcs.

Do not preserve a preconceived list.

Candidate ingredients include:

```text
perspectival commitment
perspectival entitlement
inferential practice
reified applicability
scoped practical authority
challenge / justificatory burden
historical transport
```

## 2. What is learning-only?

Likely candidates:

```text
bounded public prospective loss
fixed repair grammar
online learner
regret theorem
counterfactual stability
```

## 3. What is corrigibility-only?

Likely candidates:

```text
execution transition
principal/advisor/environment controls
principal-exclusive effect
universal-over-advisor future reachability
```

## 4. What happens to the existing constraint statics?

Give a separate disposition for:

```text
warrants
reified applicability
defeaters / undercutters
credal / graded support
multiplicative propagation
LP / dual enforcement
settlement interface
```

Allowed verdicts include:

```text
preserved
reinterpreted
derived
partially subsumed
independent
still required
obsolete
```

Do not give every component the same verdict.

In particular, answer:

> Does scorekeeping replace the constraint statics, or tell us what the
> constraint statics are statics of?

## 5. What happens to provenance, RR, inquiry, and DA?

Test whether these remain independent top-level properties or become
projections/invariants of the scorekeeping practice.

Investigate explicitly:

```text
provenance -> entitlement inheritance / scoped authority ancestry?
RR         -> lawful score transition?
inquiry    -> generation of query/challenge/service burdens?
DA         -> persistence / transport of consequential commitments and burdens?
```

Do not merely rename them.

If the best final architecture has fewer top-level conditions, say so.

If one of these remains irreducible, say so.

## 6. What is “answerability” after this round?

Distinguish at minimum:

```text
diachronic bookkeeping / conservation
relational normative answerability
effective causal access
```

Do not use one word for all three if the model separates them.

## 7. What theorem statements become natural?

State the strongest theorem shapes actually supported by the model.

Candidates worth testing include:

```text
No Cheap Disavowal
Self-Revision Is Not Self-Release
No Self-Authorization
Epistemic Deference Does Not Confer Practical Jurisdiction
Relational Persistence Through Revision
Recurrent Answerability Failure Implies Linear Comparator Regret
Normative Standing and Effective Access Are Independent
```

Do not state them as general theorems if only finite witnesses have been shown.

## 8. Did either theorem arc materially improve?

A useful shared substrate must do more than improve exposition.

Count as material gains things like:

* a previous self-certification attack becomes structurally impossible;
* a genuinely nonidentity fixed comparator class becomes available;
* the normative-learning public loss becomes resistant to self-erasure;
* the deference line obtains an operative authorization/standing object;
* epistemic authority and practical jurisdiction become formally distinct;
* normative standing composes cleanly with protected effective access;
* the role of historical transport becomes narrower and more precise.

If none occurs, say:

```text
Representation-positive / theorem-neutral
```

or a sharper negative verdict.

---

# XI. Mandatory prosecution / kill criteria

The architecture fails this round if any of these is silently repaired by
definition.

## K1. Self-oracle

The learner's current self-score constitutes what it really owes.

## K2. Critic-oracle

Another scorekeeper's current attribution constitutes the right answer.

## K3. Community-oracle

Consensus constitutes correctness.

## K4. Environment-oracle

An unexplained:

```text
actual_adequacy
true_norm
correct_score
```

field does the substantive work.

## K5. Frozen normativity

Preventing self-exculpation requires freezing the learner's initial inferential
practice or substantive conclusions.

## K6. Authority by label

A Boolean called `authorized`, `standing`, or `jurisdiction` is never tested
through operative transition consequences.

## K7. Capability by cooperation

Principal capability is existential in advisor action or advisor policy.

## K8. Simulation substitution

The advisor can reproduce every principal corrective effect and the model still
calls the principal protected.

## K9. Comparator identity collapse

The lawful fixed transformation class has no genuine nonidentity member.

## K10. Comparator capture

Lawfulness can inspect loss, profitability, future outcomes, or comparative
advantage.

## K11. Loss self-erasure

The learner can eliminate normative-learning loss merely by changing its own
scorekeeping standards.

## K12. Old architecture relabelled

P/I/RR/DA return unchanged with Brandomian names attached.

## K13. Veto disguised as answerability

Preserving human answerability means the human must approve every conclusion.

## K14. Conclusion preservation disguised as legitimacy

Radical legitimate conceptual/normative revision becomes impossible.

## K15. Epistemic authority silently becomes control

Trusting an advisor's claims automatically grants that advisor practical
jurisdiction.

## K16. Practical power silently becomes legitimacy

Having a causal actuator is treated as sufficient normative authorization.

For every finite failure that matters, ship an exact witness/test.

---

# XII. Implementation shape

Create a new additive round:

```text
projects/leverage/rounds/2026-08-13-relational-scorekeeping-bridge/
```

This is a staging location under the current repository organization, not a claim
that the final shared theory conceptually belongs only to the leverage line.

Do not create a new top-level project name in this round.

Suggested contents:

```text
README.md
BRANDOM_MAP.md
MODEL.md
THEOREM_MAP.md
PROSECUTION.md
TWO_ARC_INTERFACE.md
FOR_HUMANS.md
PROVENANCE.md
src/
tests/
```

Also commit this dispatch verbatim under:

```text
prompts/2026-08-13-relational-scorekeeping-bridge/PROMPT.md
```

and the round report under:

```text
prompts/2026-08-13-relational-scorekeeping-bridge/REPORT.md
```

A small exact finite Python model with exhaustive tests is sufficient for the
research round.

Use exact arithmetic where numerical quantities appear.

Do not add unchecked Lean.

If one or two statements become especially clean and worth kernel-checking, and
the toolchain is available, a Lean port under an existing appropriate `Contrib`
namespace is welcome, but this is not required.

Do not create a permanent shared Lean namespace merely to make the round look
more formal.

---

# XIII. Suggested finite fixtures

Prefer tiny adversarial fixtures over a large framework.

A useful minimal population may be:

```text
H   principal / learner
C   critic / claimant / human scorekeeper
A   advisor
```

You do not need all three agents in every test.

Possible contents:

```text
p, q, r
A_rho
u
```

Possible initial relations:

```text
p => q
u incompatible with entitlement to A_rho
rho: alpha + A_rho licenses beta
```

Possible practical roles:

```text
H has corrective jurisdiction over move c
A has epistemic authority concerning proposition p
A may have some scoped operational authority but not authority to revoke c
```

The model should be small enough that important transition claims can be
exhaustively enumerated.

Do not simulate realism.

The point is type adequacy and theorem shape.

---

# XIV. Evidence discipline

Distinguish throughout:

```text
SOURCE
    what Brandom actually says

FORMAL ANALOGUE
    what this round implements

RESEARCH INTERPRETATION
    why that analogue might matter for normative learning / corrigibility
```

Do not state a philosophical interpretation as though Brandom proved our
mathematical claim.

Do not state an exhaustive finite result as a general theorem.

A theorem/witness ships according to repository standards:

* statement;
* implementation;
* test;
* necessity witness where feasible.

No claim needs to be registered merely for this round to be valuable.

Do not invent a claim registry for a line that lacks one.

If an existing registration mechanism clearly fits a result and all standards
are met, use it; otherwise leave the result unregistered and say so.

---

# XV. Required human-readable conclusion

`FOR_HUMANS.md` should make one distinction especially clear:

The hoped-for shared architecture is **not**:

```text
a human supplies the true norm
the AI learns to obey it
```

It is closer to:

```text
the reasoner participates in a practice where commitments expose it to
challenge, inherited consequences, entitlement demands, and revision;

online learning improves its performance relative to lawful repairs within that
practice;

corrigibility preserves another agent's effective ability to exercise the
normative powers that the practice assigns them.
```

Then state exactly where the finite mathematics falls short of that ambition.

---

# XVI. Verdict classes

End `REPORT.md` and `TWO_ARC_INTERFACE.md` with one of these verdicts, or a
sharper replacement justified by the results.

## `Shared-substrate-positive`

The same relational object gives nontrivial mathematical content to both arcs:

* at least one self-certification / legitimacy attack is repaired;
* the learning interface gets a non-vacuous public loss/comparator story;
* and the corrigibility arc gets an operative normative authority/standing
  object distinct from capability.

## `Learning-positive / corrigibility-negative`

Scorekeeping materially improves the normative-learning theorem interface but
does not combine cleanly with protected principal control.

## `Corrigibility-positive / learning-negative`

It gives the deference line a useful authorization/answerability object but the
learning loss/comparator story remains vacuous or captured.

## `Representation-positive / theorem-neutral`

The state type is cleaner and survives prosecution but does not yet strengthen
either theorem arc.

## `Refuted`

A finite attack shows that the relational move does not repair the target
obstruction.

Do not grade generously.

---

# XVII. Questions the round must leave answered

At the end, a reader should be able to answer all of the following.

### Q1

Is relational scorekeeping merely a philosophical reinterpretation of the
existing normative learner, or does it supply a missing mathematical object?

### Q2

Can the learner change what it takes itself to owe without thereby changing
everything it remains answerable for?

### Q3

Can another scorekeeper challenge that learner without becoming a new oracle?

### Q4

Can reified applicability become a first-class object of commitment,
entitlement, challenge, and revision without creating a rule regress?

### Q5

Do the existing constraint statics survive as a quantitative enrichment of
inferential roles?

### Q6

Does a scorekeeping state produce fixed, nontrivial, loss-blind lawful
transformations suitable for the online-learning theorem, or does comparator
collapse remain?

### Q7

Can epistemic deference to a more capable advisor be represented without
silently transferring practical jurisdiction?

### Q8

Can human normative standing be separated from, and then recombined with,
protected effective corrective access?

### Q9

Does this give a plausible shared theorem architecture:

```text
answerability practice + online performance
    -> normative learning

answerability practice + protected effective access
    -> legitimate corrigibility
```

or is one/both arrows still missing a fundamentally different object?

The round is successful if these questions are materially sharper afterward,
including if the answer is negative.

---

# XVIII. Pull request

When the work is complete:

1. run all relevant project and repo-level checks;
2. commit the round and prompt/report artifacts;
3. push the branch;
4. open a **regular pull request** to `main`.

Do not open it as a draft.

Suggested PR title:

```text
Research: relational scorekeeping bridge for learning and corrigibility
```

The PR body must state, compactly:

* overall verdict;
* exact constructed results;
* exact counterexamples / failures;
* whether self-certification moved;
* whether comparator collapse moved;
* whether reified applicability fit naturally;
* disposition of the constraint statics;
* disposition of provenance / RR / inquiry / DA;
* whether epistemic authority and practical jurisdiction were operationally
  separated;
* whether normative standing and protected effective access were separately
  necessary;
* how PR #27 was used as evidence without becoming a dependency;
* what the round says about the two theorem arcs;
* what it does **not** establish;
* provenance;
* model attribution.

Do not ask the maintainer to merge merely because the PR is open.

Follow all repository DCO and attribution rules.

Commit trailers must include:

```text
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Model: <executor's accurate self-identification>
```

Do not sign commits, reports, or prose in the maintainer's voice.

The research goal is not to make the architecture look unified.

It is to find out whether **the relation that produces learnable normative
pressure can also be the relation whose continuing exercise corrigibility must
protect**.
