# Refinement dispatch: Press PR #31 until the crown-jewel theorem is theorem-clean

**Date:** 2026-08-13  
**Maintainer:** A. M. Berns  
**Repository:** `A-M-Berns/alignment-workspace`  
**Target PR:** #31 — `Research: the crown-jewel normative-learning theorem, and what it costs to call it learning`  
**Branch:** `round/2026-08-13-crown-jewel-learning-theorem`  
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)  
**Executor:** self-identify accurately in report, commits, and PR metadata  
**End state:** update **PR #31 in place**. Do not open a new PR. Do not merge it.

# 0. Purpose

PR #31 has found what may be the final theorem shape:

```text
bounded relational answerability process
+
certified surgical repair family
+
online modification-regret learner
+
sufficient reason exposure
    ->
vanishing bad-response rate conditional on occasions of that reason
```

The current central inequality is:

```text
Q_T(g) / M_T(g)
    <=
B_T(g) / (delta_g * M_T(g))
```

with the intended asymptotic conclusion:

```text
Q_T(g) / M_T(g) -> 0
```

when exposure outruns the regret scale.

This looks like a real crown-jewel theorem.

But several details in the current PR are still too loose for the project to
organize around it confidently.

This pass should **not invent a new direction**.

It should press the existing theorem until all of the following are maximally
clear:

1. exactly what is random and what is pathwise;
2. exactly what the learner knows before acting;
3. exactly what the Blum--Mansour construction guarantees;
4. exactly what coverage must say;
5. exactly when stationary-distribution transience creates immediate compliance;
6. whether that transience is generic to normatively coherent repair languages or
   only to one-way repair graphs;
7. exactly which assumptions belong inside the abstract theorem and which are
   external adequacy hypotheses;
8. exactly what result deserves the label **normative learning**;
9. what remains theorem-critical after this clarification.

The standard is:

> Could we now write the flagship theorem statement in a paper without having to
> reinterpret any symbol, repair any quantifier, or discover that one of the
> hypotheses already assumed the substantive result?

A downgrade is acceptable.

---

# I. Procedure

Work on the existing PR #31 branch.

```bash
git fetch origin
git status
git log --oneline --decorate -n 20
git checkout round/2026-08-13-crown-jewel-learning-theorem
git pull --ff-only
```

Read the entire current round again, especially:

```text
CROWN_JEWEL_THEOREM.md
ASSUMPTION_AUDIT.md
COVERAGE_INTERFACE.md
LEARNING_DYNAMICS.md
REPAIR_LANGUAGE.md
THEOREM_STRENGTH_LADDER.md
PROSECUTION.md
PATH_INVENTORY.md
FOR_HUMANS.md

src/
tests/
```

Also reread PR #30's:

```text
SOURCE_AUDIT.md
THEOREM_TARGET.md
```

and inspect the actual repository Blum--Mansour learner rather than relying on
this round's prose.

Do not rewrite the historical PR #29 or #30 artifacts.

Add this refinement dispatch/report under a new prompt subdirectory, e.g.:

```text
prompts/2026-08-13-crown-jewel-learning-theorem-refinement/
    PROMPT.md
    REPORT.md
```

Update PR #31's current-round artifacts/code/tests in place.

---

# II. First rewrite the crown-jewel theorem in fully typed mathematical registers

Before further experimentation, make every random/pathwise object explicit.

The current process is endogenous:

```text
S_{t+1} = T(S_t, a_t, e_t)
```

and `a_t` may be sampled from `p_t`.

Therefore, under genuine sampling:

```text
S_t
p_t
E_g(S_t)
M_T(g)
Q_T(g)
```

may themselves be random variables.

The current prose sometimes treats them as deterministic quantities.

Fix this.

Introduce an explicit probability-space/history register if needed.

For example:

```text
H_t        strict history before round t
S_t        H_t-measurable state
p_t        distribution chosen from H_t
E_t^g      selector, H_t-measurable
ell_t      round loss vector
a_t ~ p_t
```

Then define pathwise:

```text
M_T^g
    =
sum_{t <= T} E_t^g

Q_T^g
    =
sum_{t <= T} E_t^g p_t(b_g)

N_T^g
    =
sum_{t <= T} E_t^g 1[a_t = b_g].
```

Settle exactly which quantities are:

```text
pathwise
in expectation
high probability
almost sure
```

## Mandatory correction

Do not write:

```text
E[N_T] = Q_T
```

unless `Q_T` is deterministic.

In the endogenous sampled process the likely exact statement is:

```text
E[N_T] = E[Q_T].
```

More structurally:

```text
N_T - Q_T
```

should be a martingale sum / compensator difference under ordinary sampling.

Verify this.

If an even sharper conditional-expectation statement is available, state it.

Update:

```text
CROWN_JEWEL_THEOREM.md
THEOREM_STRENGTH_LADDER.md
ASSUMPTION_AUDIT.md
FOR_HUMANS.md
```

accordingly.

---

# III. Separate three timing notions that are currently conflated

The theorem currently says roughly:

```text
ell_t = G(S_t)
```

is fixed before action and is "available in full."

Those are not the same claim.

Distinguish:

### A. Determination

```text
ell_t
```

is mathematically fixed before the current sampled action.

### B. Observability

When does the learner receive the full vector?

```text
before choosing p_t?
after choosing p_t but before sampling?
after sampling / after acting?
```

### C. Computability

Even if `S_t` and `G` are public, can the bounded learner compute the full vector
before choosing?

These differences matter enormously to whether the construction deserves to be
called learning.

If the learner sees the entire current loss vector before choosing `p_t`, then it
can potentially select a current minimizer directly, and the online-learning
interpretation changes.

Audit the actual repository learner and the Blum--Mansour source protocol.

State the strongest theorem with the **correct information order**.

Prefer a protocol diagram such as:

```text
history H_t / public state S_t
        |
        v
learner chooses p_t
        |
        v
loss vector ell_t revealed
        |
        v
sample / execute a_t
        |
        v
update learner
        |
        v
S_{t+1}
```

or whatever exact order is correct.

If the source permits the adversary to choose `ell_t` after `p_t`, while our
scorekeeping `ell_t` is already determined by `S_t`, explain why the learner is
nevertheless not assumed to have access to it prematurely.

If the architecture genuinely wants prospective public loss to be fully known
before action, state that and prosecute whether the result then still deserves to
be presented as learning.

Do not leave "prospective" ambiguous.

---

# IV. Rewrite coverage independently of the derived regret conclusion

Current H6 is:

```text
B_T(g) = o(M_T(g)).
```

This is mathematically fine as a rate condition, but `B_T` is itself the regret
bound produced by the learner construction.

Make the theorem's hypothesis/conclusion structure cleaner.

Once the exact Blum--Mansour scale is settled, prefer something like:

```text
M_T(g)
/
[ L sqrt(T |A| log K_eff) ]
    -> infinity
```

or the exact source-level complexity scale.

Then the logical order becomes:

```text
COVERAGE HYPOTHESIS
    M_T grows faster than known learning-complexity scale

LEARNER CONSTRUCTION
    ->
R_T <= C * learning-complexity scale

SURGICAL LOWER BOUND
    ->
Q_T <= R_T / delta

CONCLUSION
    ->
Q_T / M_T -> 0.
```

This is easier to audit for circularity.

## Exact `K` accounting

Audit whether the relevant rule count is:

```text
K
K + 1
M K
```

or another source-level quantity.

The implementation includes identity plus repairs and may fold selectors into
rules.

Do not write `log K` merely because it is asymptotically harmless.

State exactly what object is counted and then give the simplified asymptotic form.

---

# V. Press the transience claim much harder

The graph theorem appears sound:

> If `b` is transient in the active rule-mixture graph, every stationary
> distribution assigns it zero mass.

Keep that.

The stronger current claim is approximately:

> A normatively coherent repair class always gives a targeted source an outgoing
> edge but no return route, so every targeted bad response is transient whenever
> its reason is due.

This is **not yet established**.

Do not infer normative incoherence merely from the existence of a cycle.

A return route can arise because **another independent reason is simultaneously
active**.

For example, abstractly:

```text
reason R1:
    HOLD -> ACKNOWLEDGE

reason R2:
    ACKNOWLEDGE -> HOLD
```

The second rule need not mean:

```text
"the same exposed burden licenses undoing its answer."
```

It may encode another consideration:

```text
new evidence
scope restriction
privacy
authority conflict
defeater
resource constraint
conflicting obligation
```

The mathematical question is whether a realistic public normative state can
simultaneously certify both.

## Required prosecution

Construct at least three classes:

### A. One-way coherent repair

```text
b -> r
```

with no return route.

Expected:

```text
b transient
p_t(b) = 0
```

under the BM stationary construction.

### B. Artificially incoherent return route

A direct undoing rule licensed by the same reason.

Expected:

```text
b recurrent
```

but poor normative interpretation.

### C. Independently certified competing reasons

A return route generated by a **different public reason/certificate** that is
plausibly legitimate rather than an intentional anti-repair.

Determine whether:

```text
b
```

can be recurrent while every individual rule remains normatively coherent in its
own context.

If yes, the current claim:

```text
coherent repair class -> immediate compliance
```

must be withdrawn.

Replace it with the exact graph condition:

```text
b_g transient in active repair graph
    ->
p_t(b_g) = 0.
```

Then state whether realistic normative grammars are expected to produce transient
or recurrent targeted actions.

Do not infer this philosophically without a construction.

---

# VI. Clarify what "conflicting repairs do not matter" actually means

PR #31 correctly observes that two repairs may share a source and each retain its
own surgical inequality.

But this is only part of the story.

Distinguish:

```text
per-comparator regret theorem
```

from:

```text
global normative compiler coherence
```

and from:

```text
stationary learner dynamics induced by the entire comparator graph.
```

Two conflicting repairs may not interfere with:

```text
R_T(g) >= delta_g Q_T(g)
```

for either `g`.

But they absolutely may affect:

```text
p_t
```

through the stationary distribution of the full rule mixture.

Test this explicitly.

Ask:

> Can adding an otherwise lawful competing repair alter the learner's mass on the
> source action enough to turn a nontrivial learning problem into immediate
> compliance, or vice versa?

If yes, state:

```text
individual theorem guarantees are modular;
learner dynamics are not.
```

This distinction should appear in `REPAIR_LANGUAGE.md`.

---

# VII. Make the "learning vs compliance" fork theorem-clean

PR #31 currently says the crown jewel is viable even though the coherent fixture
satisfies it through immediate compliance.

We need a sharper conceptual decomposition.

Distinguish three properties.

## Property 1 — No Persistent Repairable Failure

For each represented reason-response repair:

```text
Q_T / M_T -> 0.
```

This is the current theorem target.

## Property 2 — Feedback Sensitivity

Changing the observed loss feedback while holding public reasons fixed can change
future `p_t`.

The cyclic control gives some evidence for this.

## Property 3 — Diachronic Improvement

For at least some natural recurrent failure pattern:

```text
early selected bad-response probability > late selected bad-response probability,
```

and the decrease is causally attributable to feedback rather than hard-coded
topology or a predetermined schedule.

Ask:

* Is Property 1 alone sufficient for the crown-jewel theorem?
* Does "normative learning" require 1 + 2?
* Does it require 1 + 2 + 3?
* Is Property 3 best treated as an optional dynamics strengthening?

Do not answer by terminology.

Answer by the motivating research desideratum:

> agents moved by reasons to improve performance.

Produce the most defensible theorem name for each level.

Potential distinctions:

```text
Normative no-persistent-failure theorem
Normative response-learning theorem
Diachronic normative-learning theorem
```

Names are provisional.

If the actual flagship theorem is better described as a **no-persistent-repairable-failure theorem**, say so rather than stretching "learning."

If "normative learning" remains justified, explain mathematically why.

---

# VIII. Investigate whether BM can exhibit genuine learning under a realistic repair graph

Before declaring:

```text
DYNAMICS-STRENGTHENING requires a new learner
```

prosecute whether a sufficiently rich but normatively coherent repair graph already
gives the current BM engine a recurrent target and feedback-driven adaptation.

This is now a concrete question.

Construct a small public state with:

```text
multiple simultaneously active legitimate reasons
```

such that the active repair graph has a recurrent strongly connected component
containing a targeted response.

Then run the current learner.

Pre-register success:

1. `p_1(b) > 0`;
2. the relevant reason recurs;
3. the relevant repair retains positive margin on enough dates;
4. `p_t(b)` decreases materially on selected dates;
5. replacing informative losses by an uninformative control removes or materially
   weakens the adaptation;
6. no rule is inserted merely to create a cycle;
7. every edge has an independently stated public certificate.

Possible verdicts:

```text
BM-DYNAMICS-POSITIVE
BM-DYNAMICS-POSITIVE-BUT-WEAK
BM-DYNAMICS-ONLY-WITH-INCOHERENT-CYCLES
ALTERNATIVE-LEARNER-STILL-REQUIRED
```

Do not require spectacular convergence.

The question is whether the current engine can actually learn under a **non-artificial**
normative repair graph.

---

# IX. Margin assumptions: distinguish four theorem strengths

Current H5 says:

```text
ell_t(b_g) - ell_t(r_g) >= delta_g > 0
```

on selected dates.

This is fine abstractly but can make the theorem read like:

> Assume a lawful response is uniformly better; then regret learns it.

Separate four cases.

### Level A — arbitrary licensed repair

No performance guarantee.

No learning conclusion.

### Level B — margin hypothesis

Assume:

```text
gap >= delta.
```

Gives the abstract theorem.

### Level C — margin-certified schema

The public answerability loss mechanically guarantees the margin under a public
side condition.

This is stronger.

### Level D — generated margin theorem

A general compiler theorem says an entire class of repair schemas is
margin-certified.

This would be strongest and is currently likely open.

Inventory which level the crown-jewel should use in its main statement.

My default expectation is:

```text
main abstract theorem: Level B
important worked corollaries: Level C
future strengthening: Level D
```

but prosecute this.

Do not describe H5 as normative correctness.

It is comparative performance in a publicly defined answerability metric.

---

# X. Compiler soundness: specify exactly what remains unproved

"Certificate" currently risks being a typed label that the model simply trusts.

Define what a **sound compiler theorem** would actually assert.

Possibilities include:

```text
if certificate c is valid in public state S,
then transformation g is:

protocol-legal
scope-correct
reason-connected
defeater-respecting
burden-preserving
non-laundering
causal
```

and perhaps:

```text
normatively licensed
```

if that phrase can be reduced to formal public conditions.

Do not smuggle:

```text
positive loss margin
```

into compiler soundness.

Licence and performance must stay separate.

Ask which parts can already be derived from relational scorekeeping and which are
additional axioms/interfaces.

Produce a minimal formal signature for:

```text
compile : PublicNormativeState -> RepairProgram -> Certificate -> Bool
```

or the more appropriate type.

The theorem may legitimately quantify over a **sound certified repair family** as
a hypothesis.

But `sound` must mean something stronger than:

```text
certificate string exists.
```

---

# XI. Repair-language adequacy is an assumption, not automatically a blocker

Reassess the current project inventory.

There are two distinct questions:

### Mathematical theorem

Can we prove:

> for any finite sound certified repair family satisfying the stated margin and
> coverage conditions, construct a learner with the conditional bad-response
> guarantee?

### Normative adequacy of an application

Does the chosen family actually represent the important ways the agent can fail to
respond to reasons?

The second can legitimately be a theorem hypothesis / application condition.

Do not call it a mathematical blocker merely because the project ultimately wants
a rich grammar.

Rewrite `PATH_INVENTORY.md` using categories like:

```text
BLOCKING THE ABSTRACT THEOREM
BLOCKING A SUBSTANTIVE INSTANTIATION
PAPER-CRITICAL
FORMALIZATION
OPTIONAL STRENGTHENING
```

Apply the same discipline to:

```text
coverage
compiler soundness
repair grammar
multi-scorekeeper aggregation
ontology migration
pathwise sampling
anytime learner
computation cost
```

The goal is to know exactly how much remains before we have:

```text
a theorem
```

versus:

```text
a compelling theorem about a rich normative practice.
```

---

# XII. Pathwise crown jewel versus expected crown jewel

Because Blum--Mansour's mixed regret inequality is pathwise over the realized
sequence, investigate whether the cleanest theorem can be stated:

> For every realized history satisfying the coverage and margin conditions,
>
> ```text
> Q_T(g) <= B_T(g)/delta_g.
> ```

If yes, make this the primary theorem.

Then sampling can be a separate corollary.

This may give a particularly clean structure:

```text
PATHWISE MIXED-ACTION THEOREM
    Q_T/M_T -> 0

EXPECTED SAMPLED-ACTION COROLLARY
    E[N_T] related to E[Q_T]

HIGH-PROBABILITY / ALMOST-SURE COROLLARY
    optional concentration extension
```

Determine the correct relationship when `M_T` is itself random.

Do not write:

```text
E[N_T]/M_T
```

if the denominator is random without saying what is meant.

Potential valid quantities include:

```text
E[N_T] / E[M_T]
E[N_T / M_T ; M_T>0]
high-probability N_T/M_T
```

but do not invent a result.

Keep the mixed-action theorem primary if that is the cleanest exact statement.

---

# XIII. Coverage should be pathwise, expected, or policy-robust — decide

Current coverage says a reason is exposed often enough.

But there are several inequivalent forms.

### Pathwise coverage

For every realized trajectory in the target class:

```text
M_T(g) / learning_scale(T) -> infinity.
```

### Expected coverage

```text
E[M_T(g)] / learning_scale(T) -> infinity.
```

### High-probability coverage

With high probability the realized exposure count dominates the learning scale.

### Adversary/policy-robust coverage

For every advisor/environment policy in some class, a challenge source can force
enough exposures.

Determine which one the crown-jewel theorem actually needs.

The regret theorem likely composes most cleanly with **pathwise realized coverage**.

Then a corrigibility theorem may separately establish a robust sufficient
condition for it.

State this layering clearly.

---

# XIV. Press the corrigibility composition one step further

PR #31 correctly says:

```text
protected capability
!=
exercise rate.
```

Do not try to prove a full composition here.

But specify the exact theorem interface the corrigibility line would need to
supply.

For example:

```text
For each principal-recognizable challenge class g,
for every advisor policy pi_A,
the principal/environment has a strategy sigma_H such that

M_T(g) >= m_g(T)
```

with:

```text
m_g(T) / learning_scale(T) -> infinity.
```

Or perhaps coverage is conditional on the principal actually choosing to exercise
the channel.

Distinguish:

```text
ability to expose
opportunity to expose
actual exercise
mandatory service by the learner once exposed
```

This should make clear whether:

```text
corrigibility + normative learning
```

could eventually yield something like:

> A protected principal can continue supplying reasons which the learner becomes
> asymptotically unable to mishandle in any represented uniformly repairable way.

Do not claim that result yet.

But make the missing quantifiers exact.

---

# XV. Exact theorem stack

At the end of the refinement, prefer a theorem stack rather than one sentence
doing six jobs.

Try to settle something like:

## Theorem A — Certified Surgical-Regret Construction

Given H1–H4 and full-information protocol assumptions, construct one learner such
that simultaneously for every `g`:

```text
R_T(g) <= C * L * sqrt(T |A| log K_eff).
```

This is sourced from Blum--Mansour.

## Lemma B — Surgical Repair Lower Bound

If `g` has positive margin `delta_g`:

```text
R_T(g) >= delta_g Q_T(g).
```

This is our bridge.

## Theorem C — Conditional Response-Learning Bound

Therefore:

```text
Q_T(g) / M_T(g)
    <=
C L sqrt(T |A| log K_eff)
/
(delta_g M_T(g)).
```

## Corollary D — Asymptotic Normative Response Learning

If realized exposure satisfies:

```text
M_T(g) >> sqrt(T |A| log K_eff),
```

then:

```text
Q_T(g)/M_T(g) -> 0.
```

## Corollary E — Margin-Certified Repairs

For schemas whose margin follows from the public answerability-loss semantics, H5
is discharged.

## Optional F — sampled-action consequence

State only at the strength actually proved.

Then explain exactly which of these together deserves the "crown jewel" name.

---

# XVI. Formalization

PR #31 now contains a sufficiently stable algebraic theorem that lack of Lean is
becoming the conspicuous missing verification step.

Try again to formalize the reusable bridge, unless blocked by a concrete
environment/tool issue.

Minimum Lean target:

```text
Given nonnegative selected masses q_t,
repair gaps d_t >= delta > 0,
and

R = sum_t q_t * d_t,

prove:

delta * sum_t q_t <= R.
```

Then finite-horizon consequence:

```text
R <= B
->
Q <= B / delta
```

with appropriate ordered-field assumptions.

If convenient, also formalize:

```text
Q / M <= B / (delta*M)
```

for positive `M`.

Do **not** reprove Blum--Mansour.

Treat its regret upper bound as an explicit theorem hypothesis at the Lean bridge
boundary.

Requirements:

```text
sorry-free
#print axioms
```

If Lean still cannot be completed for a concrete tool/runtime reason, report the
exact failure rather than only "budget."

---

# XVII. Required new negative controls

At minimum add tests/prosecutions for:

### K1 — stochastic register

A genuinely sampled endogenous process where `Q_T` differs between trajectories,
demonstrating why:

```text
E[N_T] = E[Q_T]
```

is the correct register.

### K2 — information timing

Show the learner's choice at `t` does not consume the current loss feedback before
committing `p_t`, unless the theorem deliberately assumes otherwise.

### K3 — independently justified return route

A recurrent target created by multiple legitimate certificates rather than an
explicit anti-repair.

### K4 — full-graph dependence

Add/remove one competing repair and show whether the BM stationary distribution
changes even though the per-repair lower-bound theorem does not.

### K5 — coverage at the exact regret scale

Retain the square-root boundary witness.

### K6 — random coverage

If sampling makes `M_T` random, demonstrate the difference between pathwise and
expected coverage.

### K7 — margin/license separation

Retain the lawful negative-margin witness.

### K8 — immediate-compliance theorem

Demonstrate the exact graph condition under which a targeted response gets zero
mass independent of feedback.

### K9 — feedback-driven recurrent case

If a coherent recurrent repair graph is found, require a no-information control.

### K10 — no hidden correctness

No coverage, certificate, or margin assumption may refer to a hidden true norm.

---

# XVIII. Required final verdict

End with **one primary verdict on the crown-jewel theorem**, plus a separate
dynamics verdict.

Possible primary verdicts:

```text
CROWN-JEWEL-THEOREM-CLEAN
CROWN-JEWEL-THEOREM-POSITIVE-WITH-INTERFACE-HYPOTHESES
CROWN-JEWEL-THEOREM-MATHEMATICALLY-POSITIVE / NORMATIVE-INTERPRETATION-OPEN
CROWN-JEWEL-THEOREM-BLOCKED
```

Separate dynamics verdict:

```text
BM-DYNAMICS-POSITIVE
BM-DYNAMICS-CONDITIONALLY-POSITIVE
BM-IMMEDIATE-COMPLIANCE-ONLY
ALTERNATIVE-LEARNER-REQUIRED
DYNAMICS-NOT-NEEDED-FOR-CROWN-JEWEL
```

Do not make one verdict carry both questions.

---

# XIX. Final report must answer these questions directly

1. What is the **exact strongest theorem** after this refinement?

2. Is its main statement pathwise over mixed actions, in expectation, or both?

3. What are the exact definitions of:

```text
M_T
Q_T
N_T
R_T
```

under endogenous randomized play?

4. What is the correct relationship between `N_T` and `Q_T`?

5. What information does the learner know before choosing `p_t`?

6. What is the exact Blum--Mansour complexity term, including rule/identity/selector
   counting?

7. What is the cleanest non-circular coverage hypothesis?

8. Is `M_T >> sqrt(T)` only schematic, or the exact finite-class condition?

9. Is transience a theorem about **one-way repair graphs** or about
   **normatively coherent repair languages**?

10. Can independently legitimate competing reasons create a return route?

11. Can the current BM learner exhibit genuine feedback-driven adaptation under a
    realistic coherent repair graph?

12. If not, does the crown-jewel theorem actually require such dynamics?

13. Which margins are derived from answerability semantics and which remain
    hypotheses?

14. What exactly would a compiler soundness theorem say?

15. Which current "blockers" are really just abstract theorem interfaces?

16. What must corrigibility eventually prove to instantiate coverage?

17. Does replay/policy regret remain strictly optional?

18. What theorem name is now justified?

19. What is the remaining theorem-critical inventory?

20. Should PR #31 merge after this refinement?

---

# XX. Desired final paper-level shape

If everything survives, the target should look approximately like:

```text
RELATIONAL NORMATIVE PRACTICE
    public commitments / entitlements
    public exposure of reasons
    certified lawful repairs
    bounded answerability loss

            |
            v

ONLINE LEARNING CONSTRUCTION
    one learner
    simultaneous regret bound
    against every represented repair

            |
            v

SURGICAL BRIDGE
    positive repair margin
        ->
    bad-response mass bounded by regret

            |
            v

COVERAGE
    reason occasions outgrow learning scale

            |
            v

NORMATIVE RESPONSE LEARNING
    conditional bad-response rate -> 0
```

The corresponding human theorem should be something like:

> When a kind of reason continues to come before a bounded agent often enough,
> and its public normative practice represents a stable lawful way to repair one
> uniformly inferior response to that reason, we can construct an online learner
> whose propensity to make that response on future occasions of the same kind
> vanishes.

But do not preserve this wording if the mathematics does not support it.

The point of this pass is to make that theorem **exactly as strong as it is true
and exactly as weak as it needs to be**.

---

# XXI. Tests, CI, provenance, PR update

Before declaring completion:

```bash
python3 tests/run.py
python3 -m checkers.run
```

Run all relevant Lean builds and axiom audits if Lean is added.

Update PR #31's body with a clearly labeled:

```text
## Crown-jewel refinement pass
```

that records:

* stochastic-register corrections;
* information-timing result;
* exact coverage condition;
* exact `K`/complexity count;
* transience/coherence verdict;
* dynamics verdict;
* compiler-soundness interface;
* revised blocker inventory;
* Lean status;
* final crown-jewel theorem;
* merge recommendation.

Follow repository attribution and DCO rules.

AI-generated commits must include:

```text
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Model: <executor's accurate model identification>
```

Do not merge PR #31.

The standard for this pass is:

> We no longer merely have a promising theorem schema. We can state exactly what
> the crown-jewel normative-learning theorem is, exactly which mathematical
> objects it controls, exactly what assumptions make it non-vacuous, exactly why
> it does or does not deserve the word "learning," and exactly which remaining
> problems are external interfaces rather than holes in the theorem itself.
