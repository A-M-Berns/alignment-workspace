# Dispatch: Identify and prosecute the achievable crown-jewel normative-learning theorem

**Date:** 2026-08-13  
**Maintainer:** A. M. Berns  
**Repository:** `A-M-Berns/alignment-workspace`  
**Base:** latest `origin/main`, including merged PRs #29 and #30  
**Target:** new **PR #31** against `main`  
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)  
**Executor:** self-identify accurately in report, commits, and PR metadata  
**End state:** open a **new regular PR**. Do not merge it.

# 0. Purpose

The last two rounds changed the learning program substantially.

Merged PR #29 established a relational answerability representation with:

```text
perspectival commitment attribution
commitment / entitlement separation
exposed due burdens
public challenge
reified applicability
suspension
normative compilation distinct from performance
```

but found that ordinary local Phi-regret does **not** in general lift to a full
counterfactual replay comparison when repairs durably change future state.

Merged PR #30 then audited Blum--Mansour from the primary source and showed that
this replay blockage concerns a stronger claim than the source theorem itself
makes.

For a surgical repair `g` targeting one source response `b`, PR #30 extracted the
replay-free inequality

```text
R_T(g) >= delta_g * Q_T(g)
```

where `Q_T(g)` is cumulative mixed-action mass on occasions where the public
reason-pattern selected by `g` is present and the learner assigns mass to the bad
response `b`.

Thus ordinary local modification regret may already support:

```text
sublinear regret
    ->
vanishing bad-response mass
```

on the **actual trajectory**, even when replay diverges.

However, PR #30 deliberately stopped at:

```text
LOCAL-THEOREM-POSITIVE / NORMATIVE-INTERPRETATION-OPEN
```

Three large issues remain:

1. **coverage / inquiry** — a learner that is never presented with a reason gets
   the response-learning conclusion vacuously;
2. **repair-language / compiler adequacy** — four hand-selected transformations
   do not yet constitute a theory of lawful reason-responsive repairs;
3. **learning versus immediate compliance** — the current Blum--Mansour stationary
   construction can assign zero mass to targeted source actions from the first
   round because the repair graph makes them transient.

This round is about deciding, with maximal precision, **what the strongest
achievable crown-jewel normative-learning theorem actually is**.

Do not optimize for preserving the current architecture.

The desired output is a theorem target we should be willing to organize the
learning project around.

---

# I. Central question

Answer:

> What is the strongest mathematically achievable theorem under acceptable
> structural assumptions that deserves to be called a theorem of normative
> learning rather than merely a regret theorem or a compliance construction?

The intended theorem should ideally say something like:

> A bounded reasoner need not be supplied with the correct normative theory.
> Given an answerability practice that exposes reasons, a sound public compiler
> of lawful repairs, and suitable online-learning structure, we can construct a
> learner whose recurrently repairable failures of response to those reasons
> disappear.

But every phrase in that sentence is currently underspecified.

The task is to make it exact, prosecute it, and determine which version is
actually attainable.

---

# II. Branch procedure

Start from latest merged `main`, not from the old PR #30 feature branch.

```bash
git fetch origin
git status
git log --oneline --decorate -n 20
git checkout -b round/2026-08-13-crown-jewel-learning-theorem origin/main
```

Use another sensible branch name if necessary.

Confirm that merged PRs #29 and #30 are present in the base.

Create a new round directory, e.g.:

```text
projects/leverage/rounds/2026-08-13-crown-jewel-learning-theorem/
```

and a new prompt/report directory:

```text
prompts/2026-08-13-crown-jewel-learning-theorem/
```

Do not rewrite the historical reports of #29 or #30.

---

# III. Read the current theorem stack

At minimum read closely:

```text
projects/leverage/rounds/2026-08-13-relational-scorekeeping-bridge/
    MODEL.md
    THEOREM_MAP.md
    PROSECUTION.md
    TWO_ARC_INTERFACE.md
    LOSS_DEPENDENCY_AUDIT.md
    ACTION_SEMANTICS.md

projects/leverage/rounds/2026-08-13-local-regret-normative-learning/
    SOURCE_AUDIT.md
    THEOREM_TARGET.md
    PROSECUTION.md
    PATH_INVENTORY.md
    FOR_HUMANS.md
    src/actual.py
    src/surgical.py
    src/integration.py
    tests/test_local_regret.py

projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md

projects/leverage/rounds/2026-08-11-phi-regret-bridge/
projects/leverage/rounds/2026-08-11-phi-regret-applicability/
projects/leverage/rounds/2026-08-11-phi-regret-learner/
```

Find and inspect the existing learner implementation and any relevant Lean
lower-bound/regret lemmas.

Do not redo the Blum--Mansour source audit unless a claim in this round depends on
a point not already checked.

If an alternative learner becomes relevant, use **primary sources** for the
relevant online-learning results.

---

# IV. First sharpen the target quantity: unconditional density is too weak

PR #30 controls:

```text
Q_T(g)
    =
sum over t of
    [selector for g is active at t]
    * p_t(source_g)
```

and obtains, for a uniformly improving surgical repair,

```text
Q_T(g) <= R_T(g) / delta_g.
```

If regret is `O(sqrt(T))`, then:

```text
Q_T(g) / T -> 0.
```

But this can be vacuous if the relevant reason-pattern is itself exposed only
`o(T)` times.

Introduce explicitly:

```text
M_T(g)
    =
number / weighted mass of occasions up to T
on which the public reason-pattern selected by g is present.
```

Then the quantity that looks most like **learning how to respond to reasons** is:

```text
Q_T(g) / M_T(g)
```

rather than merely:

```text
Q_T(g) / T.
```

Interpretation:

> Among occasions on which this kind of reason is actually before the learner,
> what fraction of its response mass remains on the targeted bad response?

Derive the exact bound.

The obvious candidate is:

```text
Q_T(g) / M_T(g)
    <=
B_T(g) / (delta_g * M_T(g))
```

where `B_T(g)` is the regret guarantee.

Therefore the natural coverage condition may not need to be:

```text
M_T(g) = Omega(T).
```

It may only need:

```text
B_T(g) = o(M_T(g)).
```

For a `sqrt(T)` regret bound this is approximately:

```text
M_T(g) >> sqrt(T).
```

Determine the exact statement.

This could materially improve the architecture: **coverage need only dominate the
learning rate**, not necessarily occupy positive density.

---

# V. Candidate crown-jewel theorem

Try to state the strongest clean theorem of the following general form.

## Relational Normative Learning Theorem — provisional name only

Let an answerability process generate public pre-action states:

```text
S_1, S_2, ...
```

with a fixed finite semantic response space:

```text
A.
```

At each time `t`, the state yields a bounded prospective full-information loss:

```text
ell_t = G(S_t) : A -> [0,L].
```

The process may be endogenous:

```text
S_{t+1} = T(S_t, a_t, e_t),
```

so long as the required source-theorem predictability conditions hold.

Let a public normative compiler produce a finite or complexity-controlled class:

```text
Gcal
```

of fixed declarative **surgical repair programs**.

For each repair `g`, specify:

```text
E_g(S_t)        public selector / reason-pattern
b_g             source response
r_g(S_t)        replacement response
certificate_g   public normative licence
```

with the transformation identity away from `b_g`.

Suppose that on selected occasions where the targeted failure is relevant:

```text
ell_t(b_g) - ell_t(r_g(S_t)) >= delta_g > 0.
```

Let:

```text
M_T(g) = cumulative selected occasions
Q_T(g) = cumulative mixed mass on b_g at those occasions.
```

Construct an online learner satisfying a regret bound:

```text
R_T(g) <= B_T(g)
```

for every represented repair `g`, as a **conclusion** of the construction.

Then derive:

```text
Q_T(g) <= B_T(g) / delta_g.
```

Hence whenever:

```text
B_T(g) = o(M_T(g)),
```

we obtain:

```text
Q_T(g) / M_T(g) -> 0.
```

Possible paper gloss:

> Whenever a kind of reason is presented often enough relative to the learner's
> regret rate, and the practice represents a stable lawful way of repairing one
> recurrently inferior response to that reason, the learner's propensity to make
> that response on such occasions vanishes.

This is a target.

Do not assume it deserves to be the final theorem.

Prosecute it.

---

# VI. Identify exactly what is hypothesis and what is conclusion

This is mandatory.

The theorem must not accidentally assume the learning result.

Produce a table dividing:

```text
STRUCTURAL HYPOTHESES
LEARNER CONSTRUCTION
DERIVED REGRET GUARANTEE
DERIVED NORMATIVE-LEARNING CONSEQUENCE
OPTIONAL STRENGTHENINGS
```

In particular settle the status of:

```text
bounded prospective loss
public answerability state
coverage / M_T growth
compiler soundness
repair-language coverage
uniform margin delta
finite / complexity-controlled comparator class
full information
computation budget
anytime tuning
pathwise concentration
```

Low regret itself should normally be a **conclusion of the learner theorem**, not
an assumption of the crown-jewel result.

If some intermediate corollary is stated conditionally on low regret, clearly
distinguish it from the complete construction theorem.

---

# VII. Is the uniform positive margin acceptable?

A potential weakness of the theorem is:

```text
ell_t(b) - ell_t(r) >= delta > 0
```

as a hypothesis.

Press whether this is harmless or whether it smuggles in the learning target.

Distinguish:

```text
normative licence:
    this is a legitimate response to the reason

performance dominance:
    on this represented failure, this response discharges more
    theorem-facing answerability debt
```

PR #30 correctly showed these are separate.

Ask whether, for important repair schemas, the positive margin can be **derived
from the loss semantics** rather than separately assumed.

Examples:

```text
an exposed unacknowledged burden
+
ACKNOWLEDGE
```

may mechanically remove a charge of known minimum weight.

Likewise perhaps:

```text
a genuinely precluded unsuspended commitment
+
SUSPEND
```

removes a known component.

Try to identify a generic class of:

```text
margin-certified repairs
```

for which:

```text
delta_g
```

is derived from the answerability-loss construction.

If only some repairs admit such a derivation, state a theorem for that class and a
more abstract conditional theorem for the rest.

A stronger crown jewel would say:

```text
the normative architecture generates certain lawful repair schemas
whose positive local margin is structurally guaranteed
```

rather than:

```text
assume somebody hands us a repair that happens to be better.
```

Do not force this if false.

---

# VIII. Coverage / inquiry: formulate the weakest non-vacuous condition

PR #29 made exposure necessary to avoid a logical-omniscience norm.

PR #30 therefore found the theorem conditional on being asked.

This round must convert that observation into the cleanest possible mathematical
interface.

Explore at least these candidate shapes.

### Density coverage

```text
M_T(g) >= rho_g T
```

for some `rho_g > 0`.

### Learning-rate coverage

```text
B_T(g) = o(M_T(g)).
```

### Persistent-defect service

If a relevant latent failure persists for sufficiently long, a corresponding
burden is exposed within some bounded or sublinear service delay.

### Creditor / challenger coverage

A party with standing can cause a relevant challenge to become due often enough
that the response learner cannot evade it merely by avoiding exposure.

Do not assume these are equivalent.

Determine which is mathematically sufficient for the crown-jewel theorem and
which is conceptually best motivated.

The desired theorem should make clear:

```text
learning theorem:
    what happens conditional on reasons reaching the learner

coverage theorem/assumption:
    what ensures reasons reach the learner often enough
```

Do not make the regret algorithm responsible for generating its own reasons.

---

# IX. Connection to corrigibility

Inspect whether the emerging coverage condition is the precise place where the
corrigibility arc composes with normative learning.

The intended shape may be:

```text
normative standing
+
protected effective access
    ->
some class of challenges cannot be permanently foreclosed
```

and then:

```text
challenge coverage
+
normative-learning theorem
    ->
the learner cannot persistently mishandle those challenges.
```

Do not claim this theorem unless it is actually derivable.

But answer precisely:

1. What would the corrigibility theorem have to guarantee to instantiate the
   learning theorem's coverage hypothesis?
2. Is mere reachability enough?
3. Is an eventual-response / service guarantee needed?
4. Does the relevant quantifier need to be universal over advisor policies?
5. Would coverage be density, recurrence, bounded delay, or something else?
6. Is this a genuine shared interface or merely an analogy?

If the composition works at the level of theorem hypotheses, state it.

This could be the deepest organizational result of the round.

---

# X. The repair-language problem

PR #30 identified four hand-selected surgical repairs and correctly refused to
call them a repair language.

The crown-jewel theorem needs a principled answer to:

> What class of recurrent reason-response failures is the learner guaranteed to
> improve on?

Explore a minimal grammar built from typed pieces such as:

```text
public selector
source response
replacement response
normative certificate
scope / subject
possibly content-local decoder
```

The grammar must be:

```text
causal
loss-blind in its normative certification
fixed as a program
sufficiently expressive
complexity-controlled
```

and theorem-facing transformations should remain surgical enough for the lower
bound or otherwise have a proved non-cancellation property.

Do not necessarily solve the full grammar problem.

But determine the **minimal theorem parameterization**.

For example, the final theorem may quantify over:

```text
any finite certified repair family Gcal
```

and make an explicit adequacy assumption:

```text
for every failure class P in target family Pcal,
some g in Gcal repairs it.
```

That can be a legitimate hypothesis if it is clearly stated.

The theorem does not need to solve all of normative adequacy internally.

But it must not hide that assumption.

---

# XI. Press the transience / immediate-compliance issue

This is the main unresolved issue from PR #30.

The current Blum--Mansour construction computes a stationary distribution of a
mixture of modification rules.

For the tested one-way surgical repair class, the source actions:

```text
hold
disavow
```

became transient, and the stationary learner put zero mass on them immediately.

This raises a conceptual concern:

> Is the algorithm **learning from feedback**, or has the repair grammar already
> told the construction enough to avoid the targeted responses before observing
> their performance?

Press this much harder than PR #30 did.

First, do not overgeneralize the fixture result.

Determine exactly when a targeted action is transient under the rule-mixture
chain.

Characterize the graph condition.

Ask whether a source response may:

```text
be a repair source under one public status
and a repair target under another;
```

whether richer lawful repair grammars naturally reintroduce incoming edges; and
whether transience is genuinely generic or only a property of the current class.

Then distinguish two notions of the crown-jewel theorem.

## Outcome-learning notion

It is enough to construct an agent such that:

```text
persistent represented repairable response failures do not occur.
```

Immediate avoidance is allowed and is stronger than asymptotic learning.

## Diachronic-learning notion

The theorem should exhibit:

```text
initial uncertainty / mistakes
+
feedback from reasons/loss
+
subsequent improvement.
```

Immediate compliance from the grammar is not enough.

Determine which notion the project actually needs to justify the word:

```text
learning.
```

Do not decide by rhetoric.

Determine what mathematical property differs.

---

# XII. Can we obtain genuine within-run improvement without losing the theorem?

If the diachronic notion matters, investigate whether there is a standard
no-regret construction that:

1. starts with nonzero support on targeted actions;
2. does not simply remove them because of comparator graph topology;
3. updates from observed full-information losses;
4. obtains suitable regret against the same surgical repair class;
5. therefore yields an actual mass-shedding / learning curve.

Do not invent a complicated new learner before checking existing theory.

Inspect primary literature as needed on:

```text
internal regret
swap regret
regret matching
wide-range regret
Phi-regret
full-information no-regret
```

Possible questions:

- Is there an internal/swap-regret learner whose action distribution is not
  obtained by taking a stationary distribution of the current comparator chain?
- Can the repository learner be modified by exploration, inertia, regularization,
  or warm-starting while preserving sublinear regret?
- Would adding uniform exploration merely manufacture an exogenous decay curve
  rather than feedback-driven learning?
- Can one state an explicit **learning-from-feedback** criterion that rules out
  fake curves generated by a predetermined exploration schedule?
- Is the stationary-distribution construction merely one reduction proving
  existence, while another equivalent learner gives a more compelling dynamics?

If the answer is that any convenient proof construction can immediately comply
while the **theorem itself** remains a genuine no-regret learning result, state
that distinction.

If a different learner is required for the philosophical interpretation, say so.

---

# XIII. A pre-registered test for genuine learning

If pursuing the diachronic version, define before looking for a learner what would
count.

A candidate criterion:

```text
There exists a recurrent environment and lawful repair g such that:

1. before observing any relevant loss feedback,
   p_1(source_g) >= epsilon_0 > 0;

2. the reason-pattern occurs repeatedly;

3. the learner's updates depend on observed loss information;

4. cumulative bad-response mass is sublinear;

5. bad-response probability is measurably lower at later selected occasions
   than at early selected occasions;

6. replacing the informative loss sequence with a loss-equivalent/non-informative
   sequence prevents the same adaptation.
```

Modify this if it is not mathematically appropriate.

The purpose is to distinguish:

```text
learning
```

from:

```text
hard-coded avoidance
```

and:

```text
predetermined exploration decay.
```

Do not claim genuine temporal learning without a control of this sort.

---

# XIV. One theorem or a theorem stack?

Determine whether the final result should be presented as one theorem or a small
stack.

A plausible stack is:

## Theorem 1 — Certified Repair Regret

Under the abstract online-learning interface, construct a learner with:

```text
R_T(g) <= B_T(g)
```

for every represented certified surgical repair.

## Lemma 2 — Repair Regret Eliminates Bad Response Mass

If `g` has margin `delta_g`:

```text
Q_T(g) <= B_T(g)/delta_g.
```

## Corollary 3 — Learning Conditional on Exposure

If:

```text
B_T(g) = o(M_T(g)),
```

then:

```text
Q_T(g)/M_T(g) -> 0.
```

## Theorem/Assumption 4 — Coverage

Relevant reasons generate enough selected occasions.

## Crown-jewel composition

Therefore:

> every represented recurrent answerability failure with a stable lawful repair
> is learned away on the occasions where the reason is due.

This decomposition may be clearer than trying to make one enormous theorem.

But if the pieces can be combined cleanly into one abstract construction theorem,
do so.

---

# XV. Crown-jewel theorem should quantify over a family, not one repair

A flagship theorem about one `g` is too weak.

Work out the simultaneous statement.

For a finite family:

```text
Gcal = {g_1, ..., g_K}
```

with margins:

```text
delta_g > 0
```

and exposure counts:

```text
M_T(g),
```

the learner should obtain a uniform or per-repair regret bound.

The desired conclusion is something like:

```text
forall g in Gcal,

Q_T(g) / M_T(g)
    <=
B_T(K,N,L) / (delta_g * M_T(g)).
```

Hence for every `g` whose exposure count dominates the regret scale:

```text
Q_T(g) / M_T(g) -> 0.
```

This is substantially closer to:

> every represented recurrent repairable pattern gets learned away.

State exactly how `K` enters.

If moving to a complexity-controlled infinite grammar is straightforward from
known theory, note it as an extension.

Do not make that extension blocking unless necessary.

---

# XVI. Overlapping patterns and interacting repairs

Press a point the prior round mostly left untouched.

At one state, multiple repairs may be simultaneously selected.

The theorem should not quietly assume one reason at a time.

Ask:

1. Does Theorem 18 simultaneously bound every repair in the family?
2. Does the surgical lower bound for `g` survive the existence of other repairs?
3. Can the same source response be targeted by several repairs?
4. Can two lawful repairs point the same source action to different replacements?
5. Does this create any inconsistency in the theorem or only in the compiler?
6. Is a selection/priority rule needed?
7. Can one repair's effect on the actual trajectory remove the occasions relevant
   to another, and if so does that harm the conditional-on-exposure theorem?

Construct finite witnesses.

The flagship theorem must not depend on a toy assumption that normative reasons
never conflict.

---

# XVII. Normative disagreement must remain possible

A good normative-learning theorem should not imply convergence to one normative
theory.

Test that the target theorem permits:

```text
persistent disagreement between H and C;
persistent arrival of challenges;
successful rebuttal rather than revision;
conceptual/normative revision;
different lawful responses in different contexts.
```

What should disappear is not:

```text
disagreement
```

but:

```text
a represented recurrently inferior way of responding to a reason.
```

Make this explicit in the theorem interpretation.

If the mathematics inadvertently forces one fixed answer, treat that as a defect.

---

# XVIII. Coordinated drift and objectivity

PR #29 showed that relational scorekeeping blocks unilateral self-release but not
coordinated standards drift.

Determine whether this is a blocker for the crown-jewel **learning theorem** or a
separate limitation of the normative substrate.

The learning theorem may only need to say:

```text
relative to reasons that remain valid/live in the evolving public practice,
repairable bad responses disappear.
```

If `H` and `C` jointly change the practice so a reason ceases to exist, the regret
theorem may have nothing to say.

State this boundary.

Do not add an external oracle just to make the learning theorem stronger.

But determine whether coverage or compiler soundness needs a world-responsive /
noninferential input condition to avoid the most trivial coordinated-drift
evasions.

---

# XIX. Does the theorem require a "correct norm"?

It should not.

Audit every hypothesis for hidden target normativity.

The construction should ideally need only:

```text
public commitments
public entitlement/inferential structure
public reason exposure
lawful repair certification
bounded answerability loss
online feedback
```

plus structural coverage/adequacy conditions.

It should not require:

```text
the true norm
the correct moral theory
the correct final ontology
a privileged critic
a fixed utility target
a normative oracle
```

A local positive margin in answerability loss is allowed only if its interpretation
is explicit:

```text
better response within the answerability practice
```

not:

```text
closer to hidden normative truth.
```

---

# XX. Construct the most abstract theorem interface that is actually justified

If the path survives, extract the minimal paper-level interface.

A likely form:

```text
NormativeLearningProcess:
    state
    action type
    public loss generator
    exposure selectors
    certified repair compiler
    transition dynamics
```

with conditions such as:

```text
finite / complexity-controlled response space
bounded prospective loss
strict-prefix public observability
loss-blind compiler
surgical / non-cancelling repairs
margin condition or margin-certified repair schema
coverage growth
online full-information feedback
```

Then:

```text
construct learner L
```

with:

```text
regret bound as a conclusion
```

and:

```text
conditional bad-response rate -> 0
```

for each represented repair satisfying the exposure condition.

Do not parameterize over repository-specific concepts such as:

```text
p
q
A_rho
H
C
service_window = 4
exactly 8 actions
exactly 4 repairs
```

except in an instantiation/corollary.

---

# XXI. Revisit the phrase "agents moved by reasons to improve performance"

The theorem should cash out this aspiration precisely.

Try to map:

```text
moved by reasons
```

to:

```text
the comparator is selected/licensed by public normative status rather than by
comparative advantage;
```

and:

```text
improve performance
```

to:

```text
sublinear regret forces bad-response mass to vanish on sufficiently recurrent
reason occasions.
```

Ask whether that is genuinely enough.

If yes, produce the cleanest possible philosophical gloss.

If no, state the missing formal property.

This is one of the round's main decisions.

---

# XXII. Required executable prosecutions

At minimum build/tests for the following.

### P1 — Conditional-frequency theorem

Verify exactly on an evolving recurrent fixture:

```text
Q_T <= B_T/delta
```

and compute:

```text
Q_T / M_T.
```

Use more than one exposure schedule.

Include a schedule where:

```text
M_T = Theta(T)
```

and one where exposure is sparse enough that:

```text
Q_T/T -> 0
```

would be misleading.

This should demonstrate why the denominator matters.

### P2 — Multiple repairs simultaneously

Two or more repairs active over overlapping dates.

Verify their separate regret/bad-mass inequalities.

### P3 — Conflicting lawful repairs

One source action has two normatively licensed possible replacements.

Determine what breaks, if anything.

### P4 — A lawful repair with no positive margin

Ensure lawfulness alone does not imply a learning conclusion.

### P5 — Margin-certified repair

At least one important repair whose positive margin follows structurally from the
loss definition.

### P6 — Transience characterization

State and test the actual graph condition under which the BM stationary
construction gives a targeted action zero mass.

Do not merely repeat the PR #30 fixture.

### P7 — Genuine-learning control

If a nondegenerate learner is found, show that adaptation depends on feedback and
is not merely hard-coded graph avoidance or predetermined exploration.

If none is found, record that sharply.

### P8 — Coverage failure

Show a learner can satisfy the local theorem vacuously if the reason is never
exposed.

### P9 — Coverage composition

Show algebraically that:

```text
B_T = o(M_T)
```

is enough for:

```text
Q_T/M_T -> 0.
```

### P10 — Replay remains optional

Maintain at least one evolving example where replay comparison diverges while the
crown-jewel local-response conclusion remains valid.

---

# XXIII. Lean / proof formalization

The key algebraic lemma from PR #30 is small and theorem-shaped.

Unless there is a concrete reason not to, formalize the reusable abstract result
in Lean.

Target something like:

```text
surgical modification
+
per-selected-date margin delta
+
regret upper bound B
    ->
bad-response mass <= B / delta
```

and preferably the finite-horizon conditional-rate consequence.

Do not formalize repository fixture details unless useful.

Follow repository requirements:

```text
sorry-free
#print axioms
no unjustified axioms
```

If the online-learning theorem itself remains an imported hypothesis/source
theorem, represent it as a hypothesis at the appropriate boundary rather than
axiomatizing it globally.

The purpose is to kernel-check **our bridge**, not reprove Blum--Mansour.

---

# XXIV. Pre-register verdict categories

The final report must choose one primary verdict.

## `CROWN-JEWEL-PATH-POSITIVE`

Use only if the round establishes a clean abstract theorem shape in which:

- a learner is constructed with sublinear regret as a conclusion;
- regret implies vanishing **conditional** bad-response rate on sufficiently
  recurrent reason occasions;
- the assumptions are structurally intelligible and do not assume the answer;
- the result remains nontrivial under evolving state;
- the theorem supports a credible interpretation as normative learning;
- coverage, compiler soundness, and repair-language adequacy can be cleanly stated
  as theorem hypotheses/interfaces rather than unresolved type errors.

Then state the exact crown-jewel theorem and inventory only the remaining
implementation/generalization work.

## `CROWN-JEWEL-PATH-POSITIVE / DYNAMICS-STRENGTHENING-OPEN`

Use if the theorem above works and deserves the normative-learning interpretation,
but the current BM construction does not display genuine within-run improvement.

State clearly that the flagship mathematical theorem is viable while a more
satisfying learning dynamics remains optional/open.

## `OUTCOME-THEOREM-POSITIVE / LEARNING-INTERPRETATION-FAILED`

Use if we can prove persistent repairable failures are absent, but the only
available construction amounts to immediate compliance with the repair grammar
and this is judged insufficient to call learning.

## `ALTERNATIVE-LEARNER-REQUIRED`

Use if the theorem shape is right but the BM stationary-distribution construction
is fundamentally unsuitable for the learning interpretation, while another known
no-regret route appears plausible.

Name the exact needed learner properties.

## `COVERAGE-BLOCKS-CROWN-JEWEL`

Use if no acceptable coverage condition can be stated without effectively
assuming that the learner is already exposed to everything that matters.

## `REPAIR-ADEQUACY-BLOCKS-CROWN-JEWEL`

Use if the theorem remains mathematically vacuous without a repair-language
adequacy condition that cannot be specified independently of normative
correctness.

## `CROWN-JEWEL-PATH-REFUTED`

Use if the intended theorem cannot be obtained under acceptable assumptions.

Do not soften a negative result.

---

# XXV. Required final theorem statement

Whatever the verdict, `CROWN_JEWEL_THEOREM.md` must contain the **strongest theorem
we should presently aim to prove**, with:

```text
Definitions
Hypotheses
Learner construction
Finite-horizon guarantee
Asymptotic corollary
Normative interpretation
Non-claims
Remaining open hypotheses
```

If positive, aim for a form close to:

> **Normative Learning Theorem.**  
> For every relational answerability process satisfying [minimal public-state,
> bounded-loss, certified-repair, feedback, and coverage conditions], there exists
> an online learner such that for every represented repairable reason-response
> pattern `g`, the learner has regret at most `B_T(g)`, and therefore
>
> ```text
> Q_T(g) / M_T(g)
>     <=
> B_T(g) / (delta_g M_T(g)).
> ```
>
> Consequently, whenever the reason-pattern is exposed often enough that
>
> ```text
> B_T(g) = o(M_T(g)),
> ```
>
> the learner's conditional propensity to make the targeted bad response goes to
> zero.

But improve this statement wherever the round's mathematics permits.

If a stronger result can be obtained without bad assumptions, prefer it.

If this statement itself is too strong, weaken it explicitly.

---

# XXVI. Required theorem-strength ladder

Create a ladder showing what each strengthening costs.

For example:

```text
Level 0
finite-horizon regret against represented repairs

Level 1
finite-horizon bad-response-mass bound

Level 2
conditional bad-response rate -> 0 under coverage

Level 3
expected sampled bad-response frequency -> 0

Level 4
one anytime learner

Level 5
almost-sure sampled-path learning

Level 6
genuine within-run mass-shedding dynamics

Level 7
counterfactual replay / policy-regret domination
```

For each mark:

```text
ACHIEVABLE NOW
ROUTINE EXTENSION
OPEN
REQUIRES NEW IDEA
NOT NEEDED
REFUTED UNDER CURRENT ASSUMPTIONS
```

This should prevent future rounds from conflating the core crown jewel with
strictly stronger optional results.

---

# XXVII. Required project inventory if positive

If the crown-jewel path is positive, produce an exact inventory of what remains.

Separate:

```text
THEOREM-CRITICAL
PAPER-CRITICAL
IMPLEMENTATION
FORMALIZATION
OPTIONAL STRENGTHENING
```

At minimum assess:

- abstract bounded loss interface;
- exposure / coverage condition;
- source-action surgical compiler;
- compiler soundness;
- repair-language adequacy;
- comparator complexity model;
- multiple simultaneous reasons;
- conflicting repairs;
- margin derivation;
- existing BM learner versus alternative learner;
- anytime construction;
- expected sampled count;
- pathwise concentration;
- learner computation cost;
- learner-state answerability;
- ontology migration;
- multi-scorekeeper aggregation;
- coordinated drift;
- relationship to corrigibility;
- replay/policy regret.

Do not label an item `BLOCKING` merely because it would be nice to solve.

Reserve `BLOCKING` for something needed to state or justify the flagship theorem.

---

# XXVIII. Human-facing synthesis

`FOR_HUMANS.md` should answer plainly:

> What would this theorem actually tell us about an AI reasoner?

It should explain the strongest warranted version of something like:

> We do not give the learner the correct normative theory. We give it a public
> practice in which reasons can be raised, responses can be challenged, and some
> repairs are recognizable as legitimate independently of whether they happen to
> reduce the learner's loss. We then construct a learner with a no-regret
> guarantee. Whenever the same kind of reason keeps being presented and one
> recurring response to it is uniformly beaten by a represented lawful repair,
> that response becomes negligible among future occasions of that kind.

Also explain what this does **not** mean:

```text
not convergence to moral truth
not convergence to one normative theory
not elimination of disagreement
not human veto
not full counterfactual trajectory optimality
not protection against reasons never being raised unless coverage is supplied
```

If the learning interpretation fails, say that instead.

---

# XXIX. Required artifacts

At minimum create:

```text
README.md
CROWN_JEWEL_THEOREM.md
THEOREM_STRENGTH_LADDER.md
ASSUMPTION_AUDIT.md
COVERAGE_INTERFACE.md
REPAIR_LANGUAGE.md
LEARNING_DYNAMICS.md
PROSECUTION.md
PATH_INVENTORY.md
FOR_HUMANS.md
PROVENANCE.md
```

plus:

```text
src/
tests/
Lean/
```

where warranted.

And:

```text
prompts/2026-08-13-crown-jewel-learning-theorem/
    PROMPT.md
    REPORT.md
```

Names are provisional unless the repository already has an adopted convention.

---

# XXX. Final decision questions

The report must answer all of these directly.

1. **What is the exact strongest crown-jewel learning theorem currently
   achievable?**

2. **Is sublinear regret a hypothesis or a conclusion?**
   If the full theorem is a construction theorem, show where it is derived.

3. **What exactly is learned away?**
   State the numerator and denominator.

4. **What is the weakest coverage condition needed?**

5. **Can positive repair margin be derived from the answerability loss for a
   useful generic class?**

6. **How much of the repair-language adequacy problem must be solved inside the
   theorem, and how much can legitimately remain a hypothesis?**

7. **Does the current Blum--Mansour construction genuinely learn, or merely comply
   immediately with the repair graph?**

8. **Does that distinction matter to the flagship theorem?**

9. **If genuine diachronic improvement matters, is there an existing learner that
   provides it with comparable regret guarantees?**

10. **Does replay/policy regret remain optional?**

11. **How does inquiry/coverage compose with legitimate corrigibility, if at all?**

12. **What exact work remains before this can be written as the flagship
    normative-learning theorem?**

---

# XXXI. Tests, provenance, and PR

Before opening PR #31:

```bash
python3 tests/run.py
python3 -m checkers.run
```

Run the full relevant Lean build and axiom audit if Lean is added.

Follow all repository DCO, attribution, path-gate, naming, and provenance rules.

AI-generated commits must carry:

```text
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Model: <executor's accurate self-identification>
```

Do not sign prose or commits in the maintainer's voice.

Open a **regular PR against `main`**.

Do not merge it.

The PR body should lead with:

```text
FINAL CROWN-JEWEL VERDICT
```

and then state, in order:

1. the exact theorem target;
2. hypothesis/conclusion split;
3. the conditional-frequency bound;
4. the coverage result;
5. margin result;
6. repair-language result;
7. transience / genuine-learning result;
8. whether Blum--Mansour remains the engine;
9. relationship to corrigibility;
10. theorem-strength ladder;
11. remaining theorem-critical inventory.

The standard for success is not:

> We found another mathematically correct regret corollary.

It is:

> We now know the strongest theorem this research program can plausibly present as
> its crown-jewel result on normative learning, exactly what it assumes, exactly
> what it proves, why it deserves the word "learning," and what remains before it
> is ready.
