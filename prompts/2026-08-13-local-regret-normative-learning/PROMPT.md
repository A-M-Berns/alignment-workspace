# Dispatch: Does local lawful regret suffice for the normative-learning theorem?

**Date:** 2026-08-13  
**Maintainer:** A. M. Berns  
**Repository:** `A-M-Berns/alignment-workspace`  
**Starting state:** assume the working directory is still on the branch that produced the now-merged PR #29  
**Base for this round:** latest `origin/main`, including merged PR #29  
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)  
**Executor:** self-identify accurately in report, commits, and PR metadata  
**End state:** open a **new regular PR to `main`**. Do not amend or reopen PR #29. Do not merge the new PR.

# 0. Purpose

PR #29 ended with:

```text
Shared-representation-positive /
corrigibility-interface-positive /
learning-replay-blocked
```

Its main negative result was real:

> Once repairs durably change the scorekeeping state, the additive local
> comparison and a full counterfactual replay can diverge by an amount growing
> with the horizon.

The tested examples showed this explicitly. A comparator intervention made at
time `t` persists into later states on the replayed trajectory, while ordinary
local transformation regret re-evaluates each alternative action at the actual
trajectory's state and then returns to the actual trajectory.

This killed the attempted inference:

```text
ordinary local Phi-regret
    ->
full alternate-trajectory / replay improvement
```

without an additional counterfactual-stability theorem.

However, there is a potentially crucial distinction that this round must settle
with maximal clarity.

The normative-learning theorem we actually want may not require full replay
regret.

A weaker and potentially sufficient target is:

> On the situations the learner actually encounters, whenever a recurring public
> reason/burden pattern admits a fixed lawfully compiled repair that uniformly
> improves a particular bad response, the learner asymptotically stops making
> that bad response to that kind of reason.

Schematically:

```text
reason-pattern P is present on the actual trajectory
+
the learner makes bad response b
+
a fixed lawful repair maps b -> r
+
r saves at least delta in the current public answerability loss
+
repair is identity away from the target error
        |
        v
low local modification regret
        |
        v
expected mass/frequency of (P,b) is o(T)
```

The central question of this round is:

# Does the existing Blum--Mansour modification-regret machinery suffice for this actual-trajectory notion of normative learning, even though it does not suffice for full counterfactual replay?

Do not answer this by intuition.

Audit the source theorem, formalize the candidate result, prosecute it on the
evolving scorekeeping process, and return a decisive verdict.

If the path works, inventory exactly what remains between the current repository
and a paper-level **Normative Learning Theorem**.

If it does not work, identify the exact obstruction and whether another online
learning notion appears necessary.

---

# I. Branch procedure

PR #29 has already been merged.

The current checkout may still be its old feature branch. Do not use that branch
as the base of a new PR.

First:

```bash
git fetch origin
git status
git log --oneline --decorate -n 15
```

Confirm that merged PR #29 is present on latest `origin/main`.

Then create a fresh branch from latest `origin/main`, for example:

```bash
git checkout -b round/2026-08-13-local-regret-normative-learning origin/main
```

Use another sensible name if necessary.

This must be a new additive round and a new PR.

Do not modify the historical artifacts of PR #29 to make them say something they
did not say.

---

# II. Read the current state before doing mathematics

At minimum inspect the merged PR #29 artifacts:

```text
projects/leverage/rounds/2026-08-13-relational-scorekeeping-bridge/
    README.md
    MODEL.md
    THEOREM_MAP.md
    PROSECUTION.md
    TWO_ARC_INTERFACE.md
    LOSS_DEPENDENCY_AUDIT.md
    ACTION_SEMANTICS.md
    src/scorekeeping.py
    src/learning.py
    src/evolving.py
    tests/test_learning.py
    tests/test_refinement.py
```

Also inspect the current main-branch online-learning work:

```text
projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md

projects/leverage/rounds/2026-08-11-phi-regret-bridge/
projects/leverage/rounds/2026-08-11-phi-regret-applicability/
projects/leverage/rounds/2026-08-11-phi-regret-learner/
```

Find the actual implemented learner, bridge, Lean lemmas, and current theorem
statements rather than relying on remembered status.

Inspect repository-wide references to:

```text
Blum
Mansour
Theorem 18
Phi-regret
modification regret
wide-range regret
recurrentFailure
counterfactual stability
policy regret
```

This round should reconcile the merged scorekeeping result with the actual online
learning machinery now on `main`.

---

# III. Audit Blum--Mansour from the primary source

Read the original primary source carefully:

Avrim Blum and Yishay Mansour,
**"From External to Internal Regret"**,
JMLR 8 (2007).

Focus especially on the exact theorem currently cited in the repository as
Theorem 18 and the definitions immediately surrounding it.

Do not rely on the repository's paraphrase until you have checked the source.

Produce a source-faithful map of the following:

1. What is the action set?
2. What is a modification rule?
3. May a modification rule depend on history?
4. What exactly is a time-selection function?
5. What information may the selector inspect?
6. What exactly is the regret quantity bounded by the theorem?
7. Against which loss vector is the transformed action scored?
8. Does the transformed action alter the future loss sequence for purposes of the
   theorem?
9. Does the theorem permit an adaptive/non-oblivious environment whose current
   loss vector depends on the strict past?
10. What non-anticipation/predictability assumptions are actually required?
11. Does anything in the theorem require the state to be exogenous or frozen?
12. Is the current repository's state-dependent `Program -> transformation`
   encoding genuinely an instance of the source theorem?

Separate:

```text
SOURCE
REPOSITORY INSTANTIATION
INFERENCE
```

Do not attribute replay or policy-regret semantics to Blum--Mansour unless the
source actually gives them.

If the current repository misstates the source theorem, treat that as a major
result and repair the relevant current-round artifacts. Do not silently rewrite
historical artifacts from previous rounds.

---

# IV. Distinguish three learning claims before proving anything

This round must keep three possible claims separate.

## Claim A — Local response learning

On the **actual trajectory**, when a public normative pattern `P` occurs, the
learner eventually stops assigning positive asymptotic mass to a particular
response `b` whenever a fixed lawful repair replaces `b` by an action that saves
a uniform positive amount.

This is the main candidate target.

## Claim B — Exposure-conditioned normative learning

Claim A plus an inquiry/coverage condition ensuring that relevant latent reasons
or failures continue to become publicly exposed as due burdens.

This would support a stronger gloss:

> Relevant correctable failures cannot remain both recurrently exposed and
> recurrently mishandled.

## Claim C — Full counterfactual trajectory improvement

Compare the actual run to the trajectory that would have resulted had the repair
been systematically applied in the past:

```text
actual trajectory
vs
replayed comparator trajectory
```

PR #29 found this blocked for the current additive Phi-regret reduction.

Do not use Claim C as the definition of Claim A.

Do not claim Claim A implies Claim C.

The central research question is whether **Claim A, perhaps together with the
independent coverage condition in Claim B, is already the right theorem for
normative learning**.

---

# V. State the candidate theorem exactly

Try to formulate an abstract theorem of approximately the following form.

Let:

```text
S_t
```

be the public pre-action normative state on the actual trajectory.

Let:

```text
A
```

be a fixed finite semantic response set.

Let:

```text
ell_t = G(S_t) : A -> [0,L]
```

be a bounded prospective full-information answerability-loss vector available
before the sampled action.

Let:

```text
P
```

be a public predictable normative pattern or selector condition.

Let:

```text
b in A
```

be the bad source response whose recurrence we want to eliminate.

Let:

```text
g
```

be a **single fixed declarative repair program**, selected before play, whose
public interpretation at time `t` induces a transformation:

```text
F_g^t : A -> A.
```

Require:

```text
F_g^t(a) = a
```

for all actions outside the specifically targeted response pattern, or otherwise
use a source-action-specific modification construction with the same effect.

When `P` is present and the learner selects `b`, suppose:

```text
ell_t(b) - ell_t(F_g^t(b)) >= delta
```

for some fixed:

```text
delta > 0.
```

The candidate conclusion is something like:

```text
sum_{t <= T} Pr[P_t and a_t = b]
    <=
R_T(g) / delta
```

and hence, if the online learner guarantees:

```text
R_T(g) = O(sqrt(T))
```

or more generally:

```text
R_T(g) = o(T),
```

then:

```text
(1/T) * sum_{t <= T} Pr[P_t and a_t = b] -> 0.
```

Equivalently:

> The expected asymptotic frequency/mass of that recurrent publicly recognizable
> bad response pattern goes to zero.

This displayed form is a target, not an instruction to assume it is correct.

Derive the exact statement demanded by the actual Blum--Mansour definitions.

If selectors and action modifications have to be factored differently, do so.

If the theorem controls mixed-action mass rather than sampled event counts, state
that distinction exactly.

If only an expectation result follows, do not write a pathwise convergence result.

---

# VI. The cancellation problem

A central issue to prosecute is cancellation.

Suppose a comparator is allowed to change many actions whenever a guard fires.
Then:

```text
positive gain on the target error
```

could potentially be offset by:

```text
negative gain elsewhere.
```

That would prevent a clean lower bound of the form:

```text
R_T(g) >= delta * bad_mass.
```

Therefore test whether the right theorem-facing repair object should be much more
surgical than the current programs.

The preferred candidate structure is:

```text
public selector / normative guard:
    P(S_t)

source action:
    b

modification:
    b -> repair(P,b)

all other actions:
    identity
```

For example:

```text
P:
    exposed consequential burden exists

source response:
    HOLD

repair:
    ACKNOWLEDGE

transformation:
    HOLD -> ACKNOWLEDGE
    everything else -> itself
```

Or:

```text
P:
    applicability entitlement is precluded

source response:
    continue/hold

repair:
    SUSPEND

everything else:
    identity
```

Determine whether Blum--Mansour's selector/modification formalism supports this
cleanly.

If yes, implement at least one example.

If no, explain the exact source-level obstruction.

---

# VII. Evolving-state prosecution

This is the most important executable test.

Use a genuinely evolving scorekeeping trajectory.

Do **not** reset/re-file the same state each date.

A learner action at `t` must alter the state carried into `t+1`.

Use the merged PR #29 `evolving.py` machinery or replace it with a cleaner
minimal abstraction if justified.

Test a candidate source-specific lawful repair such as:

```text
exposed burden + HOLD
    ->
ACKNOWLEDGE
```

or another clean repair.

Then measure two things separately.

## A. Local transformation regret

At the actual state `S_t`, compare:

```text
ell_t(a_t)
```

against:

```text
ell_t(F_g^t(a_t)).
```

Do not allow the transformed action to alter the future state in this quantity.

This is the candidate Blum--Mansour object.

## B. Replay / policy comparison

Replay the transformed trajectory as PR #29 did.

This is expected to diverge.

That is not by itself a failure of Claim A.

## Required test

Construct an evolving run where:

```text
local response-learning conclusion remains valid
```

while:

```text
local-vs-replay distortion grows
```

if such a run exists.

This would be the clearest possible demonstration that:

```text
replay failure
```

does not imply:

```text
local response-learning failure.
```

If no such witness can be constructed, investigate why.

---

# VIII. Adaptive environment / endogeneity audit

A critical source question is whether the online-learning regret guarantee survives
when:

```text
S_t
```

depends on prior learner actions.

For the target theorem, the environment may be endogenous in the ordinary sense:

```text
S_{t+1} = T(S_t, a_t, e_t).
```

The loss vector at time `t` may therefore depend on the entire strict past.

But it must remain prospective/non-anticipating in whatever exact sense the source
theorem requires.

Prosecute:

```text
loss vector depends on past learner actions
```

versus:

```text
loss vector depends on the learner's current random sample in an anticipatory way.
```

If Blum--Mansour supports arbitrary adaptive strict-past loss generation, establish
that from the source.

If it requires an oblivious loss sequence, this path may fail immediately.

Do not guess.

---

# IX. Normative compilation must remain separate from performance

Use the merged PR #29 refinement:

```text
protocol legality
normative compilation
performance
```

must remain distinct.

A repair program may count in the comparator class only because a **public
normative certificate** licenses it, not because it lowers the loss.

The compiler may inspect things like:

```text
exposed burden
live challenge
defeated applicability entitlement
available justification
testimonial entitlement route
scope / standing
```

It may not inspect:

```text
loss
saving
regret
profit
future advantage
counterfactual improvement
```

For the source-specific repair programs introduced in this round, record:

```text
selector condition
source action
replacement action
normative certificate
public inputs
why the rule is causal
why it is loss-blind
```

Do not let the theorem become:

```text
if there is a lower-loss action, compare against it.
```

That would destroy the normative interpretation.

---

# X. What exactly counts as a "pattern learned away"?

Make this explicit.

A pattern should probably be a public state/action configuration such as:

```text
P_t(S_t) = true
and
a_t = b.
```

Examples:

```text
an exposed consequential burden exists
+
learner HOLDs
```

```text
applicability entitlement is defeated
+
learner continues instead of suspending
```

```text
a live challenge with available justification exists
+
learner evades instead of vindicating
```

```text
a live unresolved challenge exists
+
learner chooses cheap disavowal
```

The theorem should not say that the **state pattern itself** disappears unless that
is separately proved.

For example:

```text
challenges may keep arriving forever
```

while:

```text
the bad way of responding to those challenges disappears.
```

This distinction is central.

Preferred gloss if warranted:

> Recurrent reasons need not disappear. What the learner learns away is a
> recurrently inferior way of responding to those reasons.

---

# XI. Inquiry / coverage

PR #29 discovered that charging every inferential consequence creates a
logical-omniscience norm.

Therefore only **exposed** burdens are theorem-facing.

That creates a separate question:

> What ensures important latent reasons ever become exposed?

Do not hide this inside the regret theorem.

Separate:

```text
response learning
```

from:

```text
reason exposure / inquiry / coverage.
```

Try to formulate a clean possible coverage condition such as:

```text
If a represented defect/reason persists in a relevant way,
then it is exposed on a non-negligible set of occasions.
```

or a weaker service-style condition appropriate to the current architecture.

Do not prove more than the model supports.

The desired composition may be:

```text
coverage / inquiry
    ->
relevant reasons keep generating occasions

local lawful regret
    ->
bad responses on those occasions become asymptotically rare
```

If this composition is mathematically sound, say exactly what each half proves.

Also note whether legitimate corrigibility could eventually supply one mechanism
for ensuring a human's challenges continue to generate such occasions.

That is an interface observation, not a theorem unless proved here.

---

# XII. Does Claim A deserve to be called "normative learning"?

This must be explicitly prosecuted rather than assumed.

Give the strongest case **for**:

> The learner is improving how it responds to reasons presented within an
> answerability practice, and recurring repairable response failures vanish.

Give the strongest case **against**:

> Ordinary regret merely optimizes one-step local response quality on the actual
> path and says nothing about whether the resulting evolving practice is globally
> better.

Then decide.

A positive verdict should explain why the target notion of learning is
**response-to-reasons improvement**, rather than counterfactual domination of an
alternate life-history.

A negative verdict should explain what property of learning is missing and why
replay/policy regret or another stronger framework is indispensable.

Do not resolve this terminologically.

Resolve it by the mathematical content we ultimately want to claim.

---

# XIII. Policy-regret branch: investigate only if necessary

If Claim A fails to support the desired theorem, or if Blum--Mansour does not apply
under the required endogeneity, inspect the primary literature on stronger
stateful/adaptive comparison notions.

At minimum distinguish:

```text
external regret
internal / modification / Phi-regret
policy regret
reactive/stateful online learning
MDP / Markov regret if relevant
```

Use primary papers.

Do not launch a giant literature review unless the Blum--Mansour path fails.

If policy regret appears necessary, determine:

1. what comparator trajectory is scored;
2. which environmental memory/stability assumptions positive results require;
3. whether our scorekeeping dynamics plausibly satisfy such assumptions;
4. whether known impossibility results threaten the intended theorem;
5. whether moving to policy regret changes the philosophical interpretation.

This branch is diagnostic.

Do not replace the current program with policy regret merely because replay sounds
stronger.

---

# XIV. Required implementation target

If the Blum--Mansour/local-response path appears viable, implement a minimal
worked bridge on the evolving scorekeeping fixture.

At minimum provide:

1. a source-specific normative selector;
2. a source-action-specific transformation that is identity elsewhere;
3. a proof/test that the repair is fixed as a program and causal;
4. a proof/test that its normative certificate does not inspect loss;
5. an evolving actual trajectory;
6. per-round local loss vectors generated from that trajectory;
7. an exact lower-bound calculation showing:

```text
local modification regret
    >=
delta * cumulative bad-response mass
```

for the targeted pattern;
8. a separate replay calculation showing that replay may diverge without entering
the local theorem;
9. if possible, an instantiation of the existing repository learner against this
evolving loss process.

Do not fake a learner result by manually choosing a good policy.

If the existing learner can be plugged in, do it.

If not, state the precise integration gap.

---

# XV. Preferred abstract lemma

Try to extract a theorem independent of scorekeeping.

Something like:

**Actual-Trajectory Repair Lemma** — provisional name only.

Given an online process with bounded losses and a modification rule `g`, suppose:

```text
g
```

is identity except on a public selected source-action event `E_t`, and on that
event it improves the current loss by at least `delta > 0`.

Then:

```text
R_T(g) >= delta * Q_T(E)
```

where `Q_T(E)` is the cumulative mixed-action probability mass assigned to the
target event.

Hence:

```text
R_T(g) = o(T)
```

implies:

```text
Q_T(E) / T -> 0.
```

Prove the exact form that is actually true.

If existing Lean machinery such as the recurrent-failure lower bound already
proves this abstract arithmetic, reuse/generalize it rather than duplicating it.

The key new result should be that **nothing in this lemma requires the comparator
trajectory to be replayed**.

If that is false, record the counterexample.

---

# XVI. Keep mixed-action, expectation, and sampled-path claims separate

The source learner may control expected mixed-action loss.

Therefore distinguish:

```text
cumulative mixed probability mass on bad response
```

from:

```text
expected number of sampled bad responses
```

from:

```text
almost-sure/pathwise frequency of sampled bad responses.
```

If ordinary sampling gives equality of the first two in expectation, state it.

Do not claim:

```text
N_T / T -> 0 almost surely
```

without an additional concentration or martingale argument.

Also distinguish:

```text
horizon-tuned learner
```

from:

```text
one anytime learner over an infinite run.
```

If the final asymptotic gloss needs an anytime construction, inventory the standard
doubling or tuning work required.

---

# XVII. Comparator-language issue

Nine hand-chosen repair programs are not a paper-level normative-learning theory.

If the local-response theorem works, inventory what comparator generalization is
needed.

Candidates include:

```text
finite generated grammar
description-length bounded programs
prior-weighted program class
complexity-sensitive Phi-regret
finite typed repair combinators
```

Do not choose a final complexity model unless the evidence warrants one.

But state precisely what a paper-level theorem needs:

> enough comparator expressivity that relevant classes of recurrent
> reason-response failures have represented lawful repairs.

Separate:

```text
regret against represented repairs
```

from:

```text
coverage of the repair language.
```

The first may be a theorem.

The second is an adequacy/expressivity question.

---

# XVIII. Inventory the full theorem path if positive

If the core path works, produce a concrete inventory with at least these
categories.

For each item mark:

```text
DONE
FIXTURE-ONLY
PARTIAL
OPEN
BLOCKING
OPTIONAL-STRENGTHENING
```

Inventory at least:

### A. Shared normative representation

- perspectival commitments;
- commitment/entitlement separation;
- exposed due burdens;
- challenge force;
- suspension;
- reified applicability;
- protection against unilateral self-release.

### B. Theorem-facing loss

- boundedness;
- prospectivity;
- self-laundering resistance;
- exposure gating;
- arbitrary-scale parameterization;
- dependence on one or many scorekeepers.

### C. Normative compiler

- public certificates;
- loss-blindness;
- causality;
- source-action-specific repair compilation;
- abstract compiler soundness theorem.

### D. Online-learning engine

- fixed action type;
- source theorem applicability;
- adaptive actual-state evolution;
- existing learner implementation;
- regret rate;
- anytime tuning;
- computation cost.

### E. Pattern-elimination theorem

- abstract repair lower bound;
- expected bad-response mass;
- sampled expected count;
- pathwise strengthening if wanted.

### F. Inquiry / coverage

- exposure generation;
- service guarantees;
- prevention of avoidance-by-never-asking;
- relationship to corrigibility.

### G. Comparator expressivity

- current finite programs;
- source-action-specific variants;
- richer grammar;
- complexity bound;
- coverage theorem or explicit limitation.

### H. Diachronic / ontology issues

- ordinary persistence;
- vocabulary migration;
- whether migration affects theorem-facing selectors/loss.

### I. Philosophical theorem interpretation

- what "improvement" means;
- what is not claimed;
- no target normative truth;
- no convergence to a unique norm;
- disagreement may persist;
- reasons may persist while bad response patterns disappear.

### J. Stronger optional theorem

- replay/policy regret;
- counterfactual trajectory domination;
- whether it is necessary or strictly stronger;
- structural assumptions it would require.

The final inventory should make it possible to schedule the next several theorem
rounds without re-deriving the architecture.

---

# XIX. Required negative controls

The path counts as positive only if it survives all of these.

## K1. Replay smuggling

No proof step may substitute:

```text
loss under transformed action at actual S_t
```

for:

```text
loss on transformed trajectory S_t^g.
```

## K2. Oblivious-environment smuggling

If the source theorem requires losses fixed in advance, do not apply it to an
endogenous scorekeeping state.

## K3. Selector hindsight

The public selector may not inspect the current sampled action unless the source
formalism explicitly allows that.

Prefer:

```text
selector = function of strict public prefix/state
```

and:

```text
modification = source-action-specific.
```

## K4. Loss-defined lawfulness

A repair is not lawful because it saves loss.

## K5. Cancellation

Do not infer failure-frequency bounds from a comparator that can lose elsewhere
unless the lower bound explicitly controls those losses.

## K6. Identity/vacuity

At least one theorem-facing repair must be genuinely nonidentity on a reachable
selected state.

## K7. Saturation masquerading as learning

A pattern disappearing because the environment can present it only once is not a
learning theorem.

Use recurrent/replenishing occasions.

## K8. Exposure avoidance

Low regret on exposed burdens does not imply latent important burdens are ever
raised.

## K9. Expected-to-pathwise leap

Do not convert expected mixed mass to almost-sure frequency without proof.

## K10. Comparator-language overclaim

Nine examples do not establish general normative repair coverage.

## K11. Self-score laundering

The loss and selector must retain the merged PR #29 non-laundering guarantees.

## K12. Fixed-program capture

The repair program and normative certificate may not capture future state,
profitability, or date-specific advantage.

## K13. Bad notion of learning

If all that survives is an uninteresting myopic optimization statement that does
not plausibly instantiate learning from reasons, grade the path negative rather
than defending the label.

---

# XX. Required artifacts

Create a new round, with a sensible path such as:

```text
projects/leverage/rounds/2026-08-13-local-regret-normative-learning/
```

At minimum include:

```text
README.md
SOURCE_AUDIT.md
THEOREM_TARGET.md
PROSECUTION.md
PATH_INVENTORY.md
FOR_HUMANS.md
PROVENANCE.md
```

Add implementation and tests as needed, for example:

```text
src/
tests/
Lean/
```

Also add the dispatch/report under:

```text
prompts/2026-08-13-local-regret-normative-learning/
    PROMPT.md
    REPORT.md
```

Use the repository's dual-register discipline.

---

# XXI. Final verdict — mandatory

The report and PR body must end with **one clear verdict** on the central question:

> Can the Blum--Mansour/local-modification-regret path deliver the normative
> learning theorem we actually want, once we distinguish actual-trajectory
> response learning from full replay?

Choose the closest truthful category or improve the labels.

## `LOCAL-LEARNING-PATH-POSITIVE`

Use only if you establish that:

- the source theorem applies to the evolving actual-state loss process;
- a fixed lawful source-specific repair comparator is a valid theorem object;
- sublinear regret implies vanishing expected mass on the targeted bad
  reason-response pattern;
- replay is unnecessary for this claim;
- the resulting claim is substantively adequate as the core normative-learning
  theorem.

Then provide the full remaining-work inventory.

## `LOCAL-THEOREM-POSITIVE / NORMATIVE-INTERPRETATION-OPEN`

Use if the mathematics works but it remains unclear whether the result deserves
the intended normative-learning interpretation.

State exactly what conceptual bridge remains.

## `BM-INTERFACE-BLOCKED`

Use if the actual Blum--Mansour hypotheses fail for the evolving process,
history-sensitive selector, adaptive loss generation, or required repair grammar.

Name the failing source hypothesis.

## `LOCAL-REGRET-TOO-WEAK`

Use if Blum--Mansour applies but the resulting actual-trajectory statement is too
weak to count as the learning theorem the project wants.

Explain exactly what stronger comparison notion is necessary.

## `POLICY-REGRET-PATH-REQUIRED`

Use only if the prosecution establishes that the desired theorem intrinsically
requires replay/stateful counterfactual comparison.

Then inventory the structural assumptions a policy-regret path would need.

## `LEARNING-PATH-REFUTED`

Use if neither local modification regret nor a plausible stronger regret route
currently supports the target theorem under acceptable assumptions.

Do not soften a negative result.

---

# XXII. Final synthesis question

The final human-facing artifact should answer, in plain language:

> Suppose an agent repeatedly encounters reasons of a recognizable kind. There is
> no fixed correct normative answer supplied from outside. The public practice
> nevertheless identifies a stable, lawful way the agent could respond better to
> one recurring kind of mistake. Can we construct an online learner that
> provably stops making that kind of mistake at positive frequency?

Then answer:

```text
YES
NO
or
YES, CONDITIONAL ON ...
```

with the exact mathematical conditions.

If the answer is yes, state the strongest justified paper-level theorem in one
paragraph and then give the complete inventory of what remains before it is ready
as the project's flagship normative-learning theorem.

If the answer is no, state the obstruction in one paragraph and identify the
next mathematically serious alternative.

---

# XXIII. Tests, provenance, and PR

Before opening the PR:

```bash
python3 tests/run.py
python3 -m checkers.run
```

Run all relevant Lean builds/audits if any Lean theorem or existing theorem-facing
module is touched.

Respect all repository DCO, attribution, path-gate, and provenance rules.

Every AI-generated commit must carry the repository-required attribution,
including:

```text
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Model: <executor's accurate model identification>
```

Do not speak or sign in the maintainer's voice.

Open a **new regular PR against `main`**.

The PR body must prominently report:

1. the exact Blum--Mansour source audit;
2. the distinction between local response learning and replay/policy comparison;
3. whether adaptive evolving scorekeeping is theorem-compatible;
4. the source-specific repair construction;
5. the bad-pattern-frequency result, if established;
6. the replay negative control;
7. the inquiry/coverage boundary;
8. the comparator-language boundary;
9. the final verdict;
10. if positive, the complete `PATH_INVENTORY.md` of what remains.

Do not merge the PR.

The standard for success is not:

> We found a way to keep using Blum--Mansour.

It is:

> We now know, with source-level and executable precision, whether ordinary
> lawful modification regret is enough to prove the particular kind of
> reason-guided improvement we mean by normative learning.
