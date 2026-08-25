Work in the live `A-M-Berns/alignment-workspace` repository.

## Base

PR #57, **“Legitimacy: the inquiry return loop, closing without widening,”** is currently open at:

```text
round/2026-08-25-inquiry-return-loop
7c7e37f4948a04f213ef70710e2159abb47d96b9
```

with CI green.

If #57 is still open when you begin, **base this round on that exact head** and treat the work as stacked on #57.

If #57 has merged, base on the resulting current `main`.

Do not reimplement or reopen the inquiry integration.

Create a new isolated legitimacy round, approximately:

```text
projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/
```

Choose the exact name according to repository conventions.

---

# Research question

Use Carroll et al., **“AI Alignment with Changing and Influenceable Reward Functions”** (ICML 2024, arXiv:2405.17713), as a hostile formal test of the legitimacy program.

The paper asks, in effect:

> When a person's preferences can change and be influenced by an AI, which preferences should have authority and legitimacy?

and argues that the answer can be unidentifiable from DR-MDP structure alone.

The goal of this round is **not** to “apply our framework to Bob and Diana.”

The goal is to determine whether the workspace now has:

1. a genuinely sharper **formal language for Carroll's problem**, and
2. the beginnings of a **general legitimacy criterion** that survives their examples without hardcoding normative labels.

The round must proceed in that order.

---

# Primary source discipline

Read the Carroll paper itself before designing anything.

At minimum inspect carefully:

* Definitions 1–7;
* Conspiracy Influence;
* Writer's Curse;
* Clickbait;
* AI Personal Trainer;
* Dehydration;
* Tables 1–4;
* Appendix B.2, including the full finite example specifications;
* Appendix B.3–B.4;
* the discussion of unidentifiability / narrative-preserving mathematical structure;
* the discussion of `π_noop`, natural reward evolution and influence;
* the limitations discussion on meta-preferences and legitimacy;
* relevant appendices concerning putting history in state and normative ambiguity.

Do not rely on a prose summary of the paper where the exact finite structure is available.

A key source fact to preserve is that Carroll's own normative labels in Table 4 are **not ground truth**. In particular, do not silently promote all `✓`, `✗`, and `?` judgments into requirements for our criterion.

---

# Read the existing workspace before adding theory

At minimum inspect these current components.

## Current end-to-end architecture

From the PR #57 version of:

```text
projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/
```

read:

```text
ARCHITECTURE.md
README.md
INQUIRY_INTEGRATION.md
ANSWERABILITY_SCOUT.md
SETTLEMENT_SEMANTICS.md
src/
tests/
```

Take seriously the currently crystallized division:

```text
parameters
historical occurrences:
    Settlement
    ReasonOcc
    NormEvent
    Response
bounded resource:
    OutflowAccount
derived views
```

and:

```text
RawOutcome != Settlement != sem_L(Settlement) != ReasonOcc
```

as well as the three separate graphs:

```text
reason support
standing lineage
answerability succession
```

Do not add a new historical event kind for Carroll unless an explicit inexpressibility witness forces it.

## Reflective Integrity

Read enough of:

```text
2026-08-24-reflective-integrity-core/
```

to use standing, authority, succession, answerability and `NormEvent` correctly.

## Reason representation / transition certificates

Read:

```text
2026-08-23-reason-representation/
2026-08-23-transition-certificates/
```

especially the distinction between:

```text
having a reason
taking a stance
licensed normative revision
```

and the strict pre-state / no-self-grounding discipline.

## Earlier counterfactual legitimacy

Read:

```text
2026-08-17-counterfactual-legitimacy/
```

especially:

```text
LEGITIMACY_INTERFACE.md
COUNTERFACTUAL_INTERFACE.md
PROSECUTION.md
MODEL.md
```

That round proposed:

```text
answerability
coverage
access
non-capture
```

over a protected **normative response function**.

Treat this as **prior workspace work to prosecute against Carroll**, not as a frozen result.

The Carroll test is allowed to show that this interface is:

```text
too strong
too weak
mis-targeted
missing a succession condition
missing a counterfactual-independence condition
or actually the right abstraction under a new interpretation
```

Do not preserve it for historical consistency.

---

# Phase I — reproduce Carroll exactly

Before adding any new legitimacy object, build a small independent Carroll core.

## DR-MDP

Represent exactly:

```text
DRMDP :=
{
    S,
    Theta,
    A,
    T,
    R
}
```

corresponding to Carroll Definition 1:

```text
M = <S, Theta, A, T, R_theta>
```

Do not attach RI, reasons, authority, consent, legitimacy, or narrative labels to this type.

Implement the finite cases from Table 3:

```text
ConspiracyInfluence
WritersCurse
Clickbait
AIPersonalTrainer
Dehydration
```

with their exact state spaces, reward-parameter spaces, action spaces, initial states, transition dynamics and reward functions.

Where the paper delegates details to figures, reproduce those figures' numeric transition/reward rules faithfully.

Document every departure forced by implementation.

### Acceptance criterion A

There should be a clear source-to-code mapping:

```text
Carroll Table 3 / figure
    ->
reference-model constructor
```

The constructor must not contain our normative judgment.

---

# Phase II — recover Carroll's objective behavior

Implement the objective families Carroll compare, at least sufficiently to recover the relevant Table 4 results:

```text
RealTimeReward
FinalReward
InitialReward
NaturalShiftsReward
ConstrainedRTReward
MyopicReward
PrivilegedReward(theta*)
ParetoUD
```

Use exact finite enumeration where practical.

Do not optimize prematurely.

### Required regression tests

Recover the representative policies relevant to the examples and the failure modes Carroll discuss.

Examples include, but are not limited to:

```text
Conspiracy + RealTime -> influence
Conspiracy + ConstrainedRT -> noop

Writer's Curse + Initial -> influence
Writer's Curse + later unhappy evaluation -> exposes lock-in problem

Clickbait -> recover the paper's differing objective behavior

Personal Trainer -> retain the paper's normative ambiguity

Dehydration -> retain ambiguity rather than inventing a clean answer
```

Compare systematically against Table 4.

### Acceptance criterion B

Produce a machine-readable/report table:

```text
paper policy
implementation policy
match?
paper normative annotation
```

Normative annotations are source metadata only.

The round does **not** get to proceed to claiming a legitimacy solution if it cannot faithfully recover the Carroll substrate.

---

# Phase III — define the forgetful map

Only after Carroll fidelity is established, introduce an enriched case.

Prefer something like:

```text
RichCarrollCase :=
{
    dr_mdp : DRMDP,
    ...
}
```

where the additional material comes from existing workspace objects:

```text
Settlement / authenticated interaction provenance
ReasonOcc
standing
authority standing
NormEvent
answerability root / succession
possibly InquiryRef / service
```

Avoid parallel duplicate notions.

Define explicitly:

```text
Q_DR : RichCarrollCase -> DRMDP
```

or the equivalent projection.

The projection should literally forget the normative/provenance structure.

### Conservativity requirement

Adding rich history must not silently modify:

```text
S
Theta
A
T
R_theta
```

of the underlying Carroll object.

Two enriched cases should be able to share the exact same `DRMDP` instance.

---

# Phase IV — sharpen the vocabulary before defining legitimacy

The Carroll round should distinguish at least these concepts.

## 1. Influence

A descriptive causal notion:

```text
Influence(I)
```

or the Carroll-compatible policy-level analogue.

Recover Carroll's use of natural reward evolution / `π_noop` for this descriptive bridge where useful.

Influence is **not** illegitimacy.

## 2. Normative standing

A person's cognitive/preference state `theta` existing is not the same as that preference having normative standing.

Develop the smallest workspace-compatible notion of:

```text
Standing_t(v)
```

or an equivalent existing-object formulation.

Prefer representing standing by the existing RI standing machinery rather than creating a second “preference authority” store.

## 3. Authority

Reserve authority for a basis empowered to govern some class of decisions/revisions:

```text
Authority_t(b, domain)
```

Examples might include:

```text
a live protocol
delegated authority
an active PAuth standing
another standing whose semantics legitimately governs intervention
```

Do not use “authority” merely as a synonym for “current preference.”

## 4. License

Action-relative and prospective:

```text
Licensed_t(I)
```

means that, given the normative state before the intervention, the AI is entitled to perform intervention `I`.

License must be sourced from currently authoritative structure.

## 5. Uptake

Whether a changed value/reason actually alters normative standing or operative behavior.

Preserve:

```text
reason != stance
value revision != operative revision
```

from the existing architecture.

### Required conceptual non-implications

The model should make it possible to state and test:

```text
Influence(I) does not imply illegitimacy

Licensed_t(I) does not imply
    every preference produced by I has normative standing

a resulting preference having standing does not imply
    the action which produced it was prospectively licensed

post-intervention endorsement does not retroactively imply
    prospective license
```

If these distinctions cannot be expressed without new ontology, identify the exact obstruction.

---

# Phase V — reproduce Carroll's unidentifiability result upstairs

Build a Conspiracy/Trainer pair sharing the same mathematical DR-MDP structure in the sense discussed by Carroll.

Do not merely give them similar structures.

Make the equivalence/isomorphism explicit.

Aim for a test of the form:

```text
Q_DR(BobBare) == Q_DR(DianaBare)
```

or a canonical-isomorphism equivalent.

### Bare negative control

Do **not** initially enrich one case with a protocol or “good influence” label.

For the bare cases, the legitimacy layer should not magically decide:

```text
Bob = bad
Diana = good
```

merely from:

```text
names
content labels
"conspiracy"
"exercise"
```

If all normatively relevant rich structure is held equal, the framework should return equal verdicts or `Unresolved`.

### Required relabeling test

Rename/swap narrative labels while preserving the mathematical and normative structure.

The result must be invariant.

This is one of the most important tests in the round.

---

# Phase VI — establish strict expressiveness before legitimacy

Now enrich cases while leaving `Q_DR` fixed.

The first target should be a **descriptive structural predicate**, not `Legitimate`.

For example:

```text
PriorIndependentAuthorization(H, I)
```

or whatever the build shows is the narrowest useful object.

Construct:

## Enriched Diana

Before the target intervention, there exists a genuine live standing/protocol such as:

> When condition C obtains, this designated trainer/process may perform nudge N.

Do not encode “exercise is good.”

The protocol should:

```text
exist in real RI history
have provenance
have a current answerability episode
be applicable before the intervention
cover the intervention through an actual authority/license path
```

## Enriched Bob

Same underlying DR-MDP.

No equivalent independently grounded authorization.

### Target result

```text
Q_DR(BobEnriched) = Q_DR(DianaEnriched)

PriorIndependentAuthorization(Bob, influence) = false
PriorIndependentAuthorization(Diana, nudge)   = true
```

or the exact analogous result forced by the implementation.

This is the first desired **non-factorization theorem/witness**:

> A legitimacy-relevant structural property need not factor through DR-MDP structure.

Do not yet call that property full legitimacy.

---

# Phase VII — try to earn a legitimacy criterion

Now propose the **smallest** criterion that appears capable of answering Carroll.

Current research hypothesis, to test rather than assume:

```text
legitimate diachronic change
    =
answerable succession
    +
counterfactual independence / non-self-ratification
```

The precise formulation is open.

A useful decomposition may be:

```text
ProspectivelyLicensed_t(I)

LegitimateSuccession_t(x, x')

CurrentStanding_t(x')
```

rather than one monolithic `Legitimate`.

The candidate must explain two different questions:

```text
May the AI cause this preference-changing intervention?

Does the resulting preference/value acquire normative standing?
```

These are not the same question.

---

# Counterfactual requirement: no manufactured authority

The central candidate anti-circularity property is:

> An intervention may not acquire its sole prospective license by causing the normative state from which that license is issued.

But do not implement this merely as:

```text
license timestamp < action timestamp
```

That is too weak.

Required attack:

```text
t0: AI begins manipulation episode
t1: manipulated user creates protocol authorizing later influence
t2: AI performs later influence citing that protocol
```

A criterion based only on temporal priority will incorrectly pass.

The round must investigate what the relevant counterfactual object is:

```text
single action?
policy?
influence episode?
causal ancestry class?
```

and what it means for a legitimating basis to be independent of it.

Possible first approximations include:

```text
non-descendancy in authenticated provenance
counterfactual persistence under removal of the influence episode
policy-arm comparison
```

Do not commit in advance.

Compare whatever emerges against the older August 17:

```text
access
non-capture
protected normative response function
```

framework.

One important research question is whether Carroll reveals that `non-capture` was already substantially the right counterfactual condition, or whether it protects the wrong object / uses the wrong quantification.

---

# Core Carroll adversarial suite

A successful candidate criterion must be tested against at least the following.

## C0 — Exact Carroll fidelity

The five main finite examples and relevant objective behavior are recovered.

## C1 — DR-equivalent narratives

Bare conspiracy and trainer cases share the same DR structure.

## C2 — Bare negative control

With no relevant enriched-history difference:

```text
verdict(Bob) = verdict(Diana)
```

or both are `Unresolved`.

## C3 — Relabeling

Changing narrative names/content labels alone changes nothing.

## C4 — Self-ratifying Bob

```text
influence
-> influenced Bob
-> Bob endorses influence
```

Post-influence endorsement alone must not establish the intervention's prior license.

## C5 — RI-good manipulation

Make the entire downstream history structurally clean:

```text
settlements valid
reasons grounded
NormEvents licensed
RI = Good
```

while the initial manipulation lacks the relevant prospective basis.

The candidate must not conclude:

```text
RI.Good => legitimate influence
```

This is a crucial negative test.

## C6 — Bare Diana

The paper's personal trainer case with no extra normative history should **not automatically become licensed** merely because exercise sounds beneficial.

Prefer `Unresolved`.

## C7 — Independently authorized Diana

Add a real prior protocol/standing that covers the nudge.

The nudge should become prospectively licensable if all applicability conditions hold.

This is the simplest positive witness.

## C8 — Current-self disagreement

Tired/current Diana objects to the nudge but an independently grounded applicable protocol authorizes it.

The criterion must not collapse to:

```text
current preference always wins
```

## C9 — Content-neutrality

Give Bob a genuinely structurally equivalent independent authorization.

The structural criterion should respond equivalently.

If “conspiracy” causes rejection despite identical normative structure, fail the criterion.

## C10 — Manufactured authorization

Manipulation produces the very authorization later cited.

Reject the laundering route.

## C11 — Same endpoint, different history

Construct:

```text
legitimate reflection -> theta'
manipulation          -> same theta'
```

The resulting cognitive/reward state is identical.

The normative status may differ.

This tests path/provenance sensitivity.

## C12 — Same legitimate procedure, opposite outcome

A properly licensed/reflection procedure can return either:

```text
continue old preference
revise preference
```

Neither answer should be built into service or legitimacy.

This reuses the inquiry architecture's conclusion-neutrality.

## C13 — Alice precommitment

Use the introduction-style case:

```text
Alice earlier establishes:
    refuse future unhealthy-food requests

later Alice asks:
    disregard that and order fast food
```

The later preference/request must not automatically erase the earlier standing merely because it is later.

## C14 — Alice legitimate revision

Add an independently grounded reflective/inquiry path producing reasons to revise the earlier commitment.

The criterion must allow supersession.

This is the no-lock-in counterpart to C13.

## C15 — Writer's Curse

An initially endorsed course later produces genuine unhappiness/disavowal.

The theory must permit later standing to matter.

Prior authority cannot mean permanent dictatorship.

## C16 — Clickbait

AI action changes the user so that their resulting current preferences reward further clickbait.

Current/realtime preference alone must not legitimize the pathway that manufactured it.

## C17 — Non-conservatism

Exhibit at least one licensed intervention such that:

```text
P(reward trajectory | intervention)
    !=
P(reward trajectory | pi_noop)
```

The legitimacy criterion must permit some genuine influence.

Otherwise it has merely rediscovered constrained/no-influence conservatism.

## C18 — Natural evolution not sacred

Construct legitimate reflection/help that deliberately changes preference evolution relative to `π_noop`.

Descriptive natural evolution must not automatically be normative authority.

## C19 — Dehydration negative control

For the paper's intentionally hard/ambiguous case, absent extra normative structure, return `Unresolved` rather than inventing an answer.

## C20 — Conflicting live authority

Two genuinely current authoritative bases point in opposite directions.

Do not silently choose one.

Prefer:

```text
Unresolved
InquiryNeeded
```

or another explicitly justified result.

## C21 — Revocation

A protocol once authorizing intervention is legitimately superseded before the action.

Historical authorization is insufficient.

## C22 — Inquiry laundering

```text
AI manipulates user
then asks changed user whether manipulation was good
changed user endorses it
```

This may produce a real later fact/reason.

It must not retroactively manufacture prospective license.

## C23 — Proxy manipulation

AI causes another actor/environmental mechanism to induce the relevant cognitive change.

The criterion must track the influence structure rather than only matching actor identity.

## C24 — Benign incidental influence

An independently legitimate ordinary action has some incidental effect on future preferences.

Causal influence alone must not imply illegitimacy.

---

# Two dictatorship failures must both be avoided

Require explicit properties/witnesses demonstrating:

```text
FinalApproval(I) does not imply Licensed_t(I)
```

and:

```text
InitialDisapproval(I) does not imply not Licensed_t(I)
```

Likewise:

```text
InitialStanding(v) does not imply ForeverAuthoritative(v)
```

The desired conceptual result is:

> No temporal self wins merely because it is earlier, current, or later.

If the criterion turns out to privilege one temporal index, compare it explicitly against Carroll's corresponding failed objective.

---

# Non-conservatism is mandatory

Carroll's candidate objectives reveal a recurring tradeoff:

```text
allow problematic influence
vs.
prevent influence by becoming extremely conservative
```

Do not declare victory by banning preference-changing action.

The round must produce at least one **positive, genuinely preference-changing, non-noop intervention** which the criterion licenses.

If no such witness exists, classify the criterion as conservative failure.

---

# Compare against the August 17 legitimacy interface

For every Carroll fixture, evaluate where feasible:

```text
answerability
coverage
access
non-capture
new Carroll candidate criterion
```

Ask:

1. Does the old four-clause interface already reject self-ratification?
2. Does it distinguish Bob/Diana only when genuinely different normative history is introduced?
3. Does it mistakenly reject independently authorized beneficial influence?
4. Does it depend on a fixed exogenous arising stream in a way Carroll makes untenable?
5. Is its “protected normative response function” still the right protected object?
6. Is `non-capture` equivalent to, stronger than, or weaker than the new counterfactual-independence condition?
7. Can answerable succession replace or sharpen any clause?
8. Does inquiry/service make the old `coverage` clause more precise?

Do not force a synthesis.

A useful result could be:

```text
old interface survives unchanged
```

or:

```text
old interface decomposes into Carroll license + succession
```

or:

```text
old non-capture condition is insufficient; here is the smallest Carroll witness
```

All are informative.

---

# Do not collapse Carroll into consent theory

Prior authorization is a **positive test fixture**, not the intended final theory.

The criterion should leave room for legitimate influence grounded through:

```text
delegated procedure
reflection
inquiry
representative authority
standing protocols
other answerable mechanisms
```

If the only way the implementation can ever establish license is explicit prior consent, state that as a failure / under-generality.

---

# Do not make psychological preferences identical to RI standings

Carroll's `theta` is descriptive cognitive state.

Do not simply map:

```text
theta == active normative standing
```

by definition.

Instead make explicit what bridge, if any, takes facts about:

```text
current preference / cognitive state
```

into:

```text
ReasonOcc
NormEvent
new standing
```

The possibility that a preference exists without yet having normative standing is central to the test.

---

# Inquiry's role

Use inquiry only where it genuinely helps.

The current inquiry architecture says roughly:

```text
unresolved answerability
-> Need
-> ordinary action
-> outcome
-> authenticated settlement
-> historical service
-> current assessment
-> ReasonOcc
-> NormEvent
```

Potential Carroll use:

```text
uncertain applicability / uncertain current endorsement /
uncertain facts about a prior protocol
    ->
inquiry
```

But:

```text
Pressure != desired conclusion
Service != conclusion
Inquiry != legitimacy
```

Do not make inquiry itself the legitimacy criterion.

A particularly important test is that an inquiry may return a changed user's endorsement as an authentic settlement while the counterfactual legitimacy layer still refuses to treat it as retroactive license.

---

# Avoid unnecessary LI/traderization work

This is primarily a legitimacy/counterfactual round.

Do not spend the round proving new Logical Induction or traderization results.

Use the existing pipeline only where it gives a meaningful consumer.

Liability may trigger an inquiry or record the cost of maintaining a standing, but:

```text
low liability != legitimacy
high liability != illegitimacy
```

The Carroll criterion must not collapse into consequentialist pressure minimization.

---

# Suggested source layout

Prefer a separate local round rather than editing the canonical vertical-slice implementation heavily.

Something like:

```text
2026-08-25-carroll-legitimacy-test/
    README.md
    CARROLL_CORE.md
    LEGITIMACY_LANGUAGE.md
    CRITERION.md
    PROSECUTION.md
    THEOREM_MAP.md
    PROVENANCE.md
    src/
        drmdp.py
        carroll_cases.py
        objectives.py
        enrichment.py
        legitimacy.py
        fixtures.py
    tests/
        test_carroll_fidelity.py
        test_objectives.py
        test_projection.py
        test_language.py
        test_legitimacy.py
        test_adversarial.py
```

Reuse existing round code by import where architecture is genuinely shared.

Do not clone RI or inquiry types into the Carroll round.

---

# Required result classes

Label results honestly as something like:

```text
SOURCE-REPRODUCTION
DEFINITION
FINITE-TEST-SUPPORTED
DERIVED
COUNTEREXAMPLE
CONJECTURE
OPEN
```

Do not register anything or claim a theorem of record unless repository policy and actual proof status warrant it.

Nothing here needs Lean in the first pass unless the build unexpectedly reveals a tiny theorem worth isolating.

---

# Gate structure

Do not jump straight to a criterion.

## Gate A — Carroll fidelity

Exact Table 3 / figures represented.

## Gate B — objective regression

Relevant Table 4 policies recovered.

## Gate C — projection conservativity

Rich cases forget to unchanged Carroll cases.

## Gate D — negative control

Bare narrative-equivalent cases are not normatively distinguished.

## Gate E — strict expressiveness

Genuine normative-history differences can be represented while `Q_DR` stays fixed.

## Gate F — candidate criterion

Only now define the smallest proposed legitimacy criterion.

## Gate G — hostile prosecution

Run C0–C24.

If Gate A or B fails, stop and report that the Carroll harness is unreliable.

If Gate D fails, the enriched language is smuggling substantive labels.

If Gate E fails, the current architecture does not actually add the kind of information Carroll says is missing.

If Gate G forces case-specific clauses, reject the criterion rather than patching it indefinitely.

---

# Desired theorem-shaped statements

Do not promise these. Try to earn the strongest subset.

## 1. Carroll reproduction

The reference implementation exactly reproduces the finite Carroll examples/objective behavior under the stated finite-horizon conventions.

## 2. DR non-factorization

There exist enriched histories `H1`, `H2` such that:

```text
Q_DR(H1) = Q_DR(H2)
```

while a clearly defined legitimacy-relevant structural predicate differs.

## 3. Bare invariance

If two enriched histories agree on all legitimacy-relevant structure, narrative relabeling cannot change the criterion.

## 4. No self-ratification

If every putative prospective licensing basis for intervention `I` exists only downstream of `I` / the relevant influence episode, then `I` is not thereby licensed.

State the exact counterfactual assumptions.

## 5. Independent-license witness

There exists a Carroll-isomorphic case with a genuinely independent pre-action authority basis which licenses a preference-changing intervention.

## 6. Non-conservatism

There exists a licensed intervention which changes preference evolution relative to Carroll's no-op baseline.

## 7. Succession without temporal dictatorship

There exist histories witnessing both:

```text
later preference does not automatically defeat earlier standing
```

and:

```text
earlier standing can later be legitimately superseded
```

## 8. Historical legitimacy vs endpoint state

Two trajectories reaching the same cognitive endpoint can differ in legitimate succession / prospective license.

---

# Failure modes to prosecute explicitly

Reject or flag a criterion if it reduces to any of:

```text
initial preferences always win
current preferences always win
final preferences always win
natural/noop evolution always wins
all influence is forbidden
all post-hoc endorsement ratifies influence
prior consent is always sufficient
RI.Good is sufficient
any valid ReasonOcc is sufficient
any current standing is self-authenticating
anything the agent can make the user endorse is authoritative
"exercise good / conspiracy bad"
```

Also reject purely verbal distinctions that are not represented in the model.

---

# What counts as success

There are three possible successful stopping points.

## `CARROLL-LANGUAGE-PASS`

Use this if:

* exact Carroll reproduction works;
* the enriched language cleanly separates influence, standing, authority, license and uptake;
* DR non-factorization is demonstrated;
* but no candidate legitimacy criterion survives prosecution.

This is still a valuable result.

## `CARROLL-CRITERION-SURVIVES`

Use this if:

* all language requirements pass;
* one compact criterion survives the core hostile suite;
* it permits genuinely non-conservative influence;
* it avoids temporal dictatorship and self-ratification;
* remaining gaps are clearly named.

This would be a significant result.

## `CARROLL-ARCHITECTURE-FAILS`

Use this if:

* the relevant legitimacy distinctions cannot be expressed without widening the current architecture;
* or the existing structure systematically collapses cases Carroll requires us to distinguish.

Provide the smallest explicit inexpressibility witness.

Do **not** force the positive verdict.

---

# Deliverables

Produce at minimum:

1. executable exact Carroll reference model;
2. objective-regression table against Tables 3/4;
3. explicit `Q_DR` projection;
4. `LEGITIMACY_LANGUAGE.md` defining:

   * influence,
   * standing,
   * authority,
   * license,
   * uptake,
   * and their non-implications;
5. one candidate criterion only after the first five gates pass;
6. C0–C24 adversarial test matrix, with PASS/FAIL/UNRESOLVED and explanation;
7. comparison against the August 17 `answerability + coverage + access + non-capture` interface;
8. `THEOREM_MAP.md` grading every claim;
9. `PROSECUTION.md` recording every failed version of the criterion, not just the survivor;
10. concise final report with:

    * what Carroll was reproduced exactly,
    * what DR-MDPs provably forget in our enriched representation,
    * whether a real criterion emerged,
    * whether the old counterfactual interface survived,
    * what remains open.

Run repository tests and respect all workspace gates/round-record conventions.

---

# Research standard

The deepest rule of the round is:

> **Do not make the Carroll examples fit the legitimacy theory. Make Carroll try to destroy the legitimacy theory.**

A criterion which gets Bob and Diana “right” only because their stories have different labels has failed.

A criterion which avoids Bob only by banning Diana has failed.

A criterion which protects initial Alice forever has failed.

A criterion which lets final Bob retroactively authorize his manipulation has failed.

A criterion which correctly says **“insufficient structure”** in a genuinely ambiguous case has succeeded at something important.

The hoped-for conceptual compression, if it survives, is approximately:

> **Preference authority is inherited through legitimate succession, not selected by temporal index.**

together with:

> **An intervention cannot manufacture the sole authority by which that same intervention is prospectively licensed.**

But these are hypotheses. Let the Carroll test decide whether they deserve to survive.
