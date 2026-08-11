# Leverage / Normative Learning — Φ-Regret Applicability, Lawful Repairs, and Online-Learning Interface

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)

## Mission

Advance **only the leverage / normative-learning research line**.

Do not conduct new deference/corrigibility research in this round.

The current leverage programme has reached a specific transition:

[
\boxed{
\text{answerability + lawful local repair}
\longrightarrow
\text{a real online-learning question}.
}
]

The workspace now contains a finite lawful-edit learning substrate in which:

* candidate local repairs can be represented;
* legality/reasons-responsiveness is separated from profitability;
* historical counterfactual charge can be evaluated;
* the environment is exact-rational and executable;
* fencing alone has been shown **not** to imply bounded lifetime counterfactual influence;
* absence of the relevant solvency coupling gives the useful locality result;
* no Φ-regret theorem has yet been established.

The immediate live priority is item 29:

> **Does a Blum–Mansour-style Φ-regret reduction actually apply to the comparator substrate we have constructed?**

The important complication is that the comparator class is not obviously the textbook fixed-action setting. It contains structure such as:

* guarded lawful edits;
* prefix-dependent legality;
* potentially varying available responses/actions;
* historically indexed counterfactual evaluation;
* reasons-responsiveness constraints that must remain independent of profitability.

This round should answer that applicability question **before** claiming or testing a Φ-regret guarantee.

The research objective is:

[
\boxed{
\text{identify the exact online-learning object we have built and determine which regret theorem, if any, actually applies to it}.
}
]

A negative applicability result is a successful research result.

---

# 0. Start from the actual integrated workspace state

Begin from current `main` after the combined workspace integration.

Do not rely on an older leverage branch.

Inspect at minimum:

* applicable `AGENTS.md`;
* `RESEARCH_STATE.md`;
* `PRIORITIES.md`;
* `DECISIONS.md`;
* `PROVENANCE.md`;
* leverage project landing/index files;
* current leverage consolidation;
* the answerability/docket artifacts;
* reasons-responsiveness materials;
* lawful-edit / learning-substrate artifacts;
* the PR #17 round report and verification artifacts;
* items 29, 30, 31;
* F4;
* existing finite tests/harnesses;
* any φ-regret notes already present;
* relevant citation/reference notes for Blum–Mansour or related online-learning theory.

Establish and report:

1. HEAD;
2. active branch/worktree;
3. dirty/clean state;
4. current relevant tests;
5. current live leverage frontier.

Use a worktree or otherwise safe isolated branch so parallel research cannot be disturbed.

Do not edit deference research artifacts except where a shared workspace-wide state surface must be reconciled at the end.

---

# 1. Frozen leverage conclusions

Treat these as standing unless you find a concrete defect.

## 1.1 Answerability is necessary but not the learning theorem

The system can preserve obligations, history, reasons, and answerability without thereby satisfying a meaningful online-learning guarantee.

Do not identify answerability with learning.

---

## 1.2 Reasons-responsiveness is local legitimacy

The lawful-edit machinery is intended to certify that an individual transition is legitimate by the learner's reasons/process constraints.

It must not certify an edit merely because the edit is profitable.

Preserve the separation:

[
\boxed{
\text{lawfulness}
\neq
\text{profitability}.
}
]

If the current implementation enforces this through a declared read footprint excluding the charge/profit table, preserve and verify that separation.

---

## 1.3 Φ-regret is the global learning question

The intended online-learning aspiration is not merely:

> eventually stop making one recurring mistake.

It is closer to:

[
\boxed{
\text{no historically lawful local edit continues to outperform the actual learner at positive asymptotic rate}.
}
]

The comparator class should encode **lawful local repairs**, not arbitrary hindsight policies.

---

## 1.4 No Φ-regret theorem exists yet

The existing environment makes a regret question executable.

It does not establish low regret.

Do not write as though item 30 has been achieved.

---

## 1.5 Fencing alone does not buy locality

The previous learning-substrate round found that a fenced account can still produce divergence growing with horizon because exhausting an account may remove later merits service.

Therefore do not assume:

[
\text{fenced}
\Rightarrow
\text{bounded lifetime counterfactual influence}.
]

The useful locality condition instead depends on eliminating the relevant solvency coupling or an equivalent bounded-lifetime mechanism.

Preserve this correction.

---

# 2. Primary question: what is the comparator class mathematically?

Before invoking any theorem, write the current comparator class in explicit mathematical form.

Let the actual learner generate a sequence:

[
a_1,a_2,\ldots
]

or the repository-native equivalent.

A lawful local repair (\phi) should be represented precisely.

Determine whether the comparator is best understood as:

* an action transformation;
* a swap map;
* a state/history-dependent map;
* a partial function;
* a guarded map;
* a contextual policy;
* a family of transformations indexed by prefix;
* something else.

Do not force Blum–Mansour notation if the actual object is different.

The first deliverable is:

[
\boxed{
\text{the exact type signature of a lawful comparator.}
}
]

---

# 3. Reconstruct Blum–Mansour precisely

Use the actual relevant primary source(s), not a remembered slogan.

Determine exactly which Φ-regret theorem/reduction is being considered.

Record:

1. action-set assumptions;
2. whether the action set is fixed;
3. comparator-map domain/codomain;
4. whether maps are time-independent;
5. whether contextual/history-dependent maps are allowed;
6. feedback assumptions;
7. loss assumptions;
8. boundedness assumptions;
9. adversarial/adaptive environment assumptions;
10. whether the reduction requires one external-regret learner per action or equivalent machinery;
11. what probability distributions are mixed;
12. how stationary distributions/fixed points enter if applicable;
13. exact asymptotic/finite-time bound;
14. computational requirements.

Do not cite a theorem merely because the phrase “Φ-regret” appears in the paper.

Identify the exact theorem or reduction that could instantiate here.

---

# 4. Map the workspace substrate to the theorem hypothesis-by-hypothesis

Build an applicability table.

For every Blum–Mansour hypothesis classify:

* **satisfied directly**;
* **satisfied after harmless encoding**;
* **requires a lemma**;
* **requires substantive model change**;
* **false in the current substrate**;
* **unclear**.

Pay particular attention to:

[
\boxed{
\text{fixed action set vs varying action availability}
}
]

and:

[
\boxed{
\text{fixed comparator map vs prefix-dependent guard}.
}
]

These are expected pressure points.

Do not wave them away.

---

# 5. Guarded lawful edits

A lawful repair may only be permitted on prefixes satisfying a reasons-responsiveness certificate.

A likely schematic form is:

[
\phi(h_t,a_t)
=============

\begin{cases}
a_t' & G_\phi(h_t)=1,\
a_t & G_\phi(h_t)=0.
\end{cases}
]

Investigate whether this can be represented as an ordinary Φ-map without changing the theorem.

Questions:

1. Can history/context be incorporated into the action state?
2. Does that cause the action set to explode?
3. Does the theorem permit a comparator to inspect the prefix?
4. Can the guard be compiled into an enlarged contextual action?
5. Would such compilation make the comparator class hindsight-dependent in an illegal way?
6. Does the legality certificate depend only on information available at the relevant time?
7. Is the resulting comparator fixed ex ante even though its behavior is prefix-dependent?
8. Is the comparator class finite/computable enough for the theorem?

Prove the encoding or reject it.

---

# 6. Varying action/response sets

The existing environment may present different lawful responses at different occasions.

Study this directly.

Suppose:

[
A_t
]

varies with (t) or with the prefix.

Does the reduction require a common fixed (A)?

If so, consider candidate encodings such as:

[
A=\bigcup_t A_t
]

with illegal/unavailable actions masked or assigned special loss.

Red-team this aggressively.

Potential problems:

* unavailable actions create artificial regret;
* masking changes stationary-distribution structure;
* comparator maps cease to be closed on (A);
* the reduction selects impossible actions;
* adding null actions changes swap structure;
* legality and availability become conflated.

Do not accept union-padding unless the resulting regret quantity is exactly the desired one.

---

# 7. Partial/guarded swaps

The normative comparator is probably not:

[
\phi:A\to A
]

applied everywhere.

It may instead be:

[
\phi:
(h,a)
\mapsto
a'
]

only on a lawful support set.

Ask whether the right formal object is:

* Φ-regret;
* swap regret;
* internal regret;
* contextual swap regret;
* sleeping-expert regret;
* specialists;
* adaptive comparator regret;
* policy regret;
* another known online-learning class.

Do not remain attached to the name Φ-regret if the actual comparator substrate belongs to a better-developed neighboring theory.

The scientific goal is the correct theorem class, not terminological loyalty.

---

# 8. Historical lawfulness

A comparator should be judged lawful relative to the learner's **historical state**, not by current hindsight rewriting of what the learner was allowed to do.

Formalize the distinction.

The counterfactual repair should satisfy something like:

[
\operatorname{Lawful}*t(\phi;h*{<t})
]

using the state/obligations/reasons available at (t).

It should not be licensed because later information makes the alternative attractive.

Audit:

* what the legality oracle reads;
* whether it has future leakage;
* whether replay changes the legality judgment;
* whether the comparator can modify the state that later legality checks depend on;
* whether a one-step repair has downstream effects on future lawfulness.

This may be crucial for the regret notion.

---

# 9. Comparator intervention semantics

A local repair can mean at least two different things.

## One-step substitution

Change action at (t), then return to the actual trajectory.

## Replay intervention

Change action at (t), then replay the learner/environment forward under the changed state.

These are not equivalent.

Determine which one the current substrate implements.

If regret is defined using replay:

[
L(\phi(\text{history}))
]

then the comparator can change later:

* obligations;
* solvency;
* docket state;
* permissible actions;
* charges.

That makes ordinary Φ-regret applicability significantly less obvious.

State the semantics exactly.

---

# 10. Locality and lifetime influence

Use the fencing/locality correction from the previous round.

For each candidate comparator determine whether one edit can affect:

* only the current loss;
* a bounded window;
* the whole future trajectory.

If a repair has unbounded downstream effect, standard additive online-learning reductions may not apply directly.

Investigate whether the no-solvency-coupling condition gives a finite influence radius or a bounded influence norm.

Possible desired lemma:

[
\left|
L_{1:T}(\phi\text{-replay})
---------------------------

L_{1:T}(\text{actual})
\right|
\le
C_\phi
+
\sum_{t\in S_\phi} \Delta_t
]

with (C_\phi) independent of (T), or a repository-native equivalent.

Do not invent such a lemma if false.

---

# 11. Loss definition

The regret theorem is only meaningful if the charge/loss is well-defined.

Audit exactly what counts as loss.

Possible ingredients:

* answerability charge;
* violation debt;
* unresolved objection cost;
* sanction/payment;
* replay charge;
* missed merits service;
* other workspace-native quantities.

Ask:

1. Is loss bounded?
2. Is it per-round?
3. Is it observable at decision time?
4. Is full-information feedback available?
5. Is loss adversarially adaptive?
6. Can a lawful repair alter the loss function itself?
7. Are we comparing monetary/accounting charges or normative quality?
8. What philosophical claim is licensed by low regret on this loss?

Keep:

[
\boxed{
\text{low charge regret}
}
]

distinct from:

[
\boxed{
\text{moral truth or normative correctness}.
}
]

---

# 12. Counterfactual evaluability

A regret comparator requires evaluating:

[
L_t(\phi(a_t))
]

or its replay analogue even when the actual learner did not choose that response.

Verify where those counterfactual losses come from.

Possible sources:

* deterministic simulation;
* replay;
* stored environment state;
* explicit charge table;
* oracle.

Determine whether:

* all comparator actions are evaluable;
* feedback is full-information or bandit;
* the current theorem assumes more feedback than the substrate provides.

Do not silently assume counterfactual feedback.

---

# 13. Independence of legality from profitability

This is load-bearing.

Construct or preserve a formal/read-footprint statement showing:

[
\boxed{
\operatorname{Lawful}(\phi)
\text{ cannot read the regret/profit advantage that }\phi\text{ later receives}.
}
]

Attempt a cheap adversarial witness:

* two environments with identical reasons/legality state;
* different charge/profit tables;
* same legality verdict.

If this currently exists, verify it rather than duplicating it.

If it does not, add the cheapest serious check.

The point is to block:

> “the edit is legitimate because it would have reduced loss.”

---

# 14. Comparator richness

The global theorem becomes meaningless if the lawful comparator class is too weak.

Audit whether the current class can express the kinds of self-corrections the research actually cares about.

Examples:

* answering an unresolved objection;
* choosing a lawful alternative response;
* correcting a repeated local failure;
* responding differently under a recognized defeater;
* repairing an answerability violation.

Construct small inhabited examples.

At the same time, ensure the class is not so broad that:

[
\text{low regret}
]

essentially requires solving the whole normative problem by hindsight.

---

# 15. Main applicability verdict

After the previous audits, give exactly one of these verdicts:

### A. Direct applicability

The chosen Blum–Mansour theorem applies essentially as stated.

### B. Applicability via proved encoding

The substrate can be transformed into the required setting without changing the intended regret quantity.

State and verify the encoding.

### C. Near miss

One or two explicit missing lemmas block applicability.

State them.

### D. Wrong theorem class

A neighboring regret framework is a better fit.

Identify it.

### E. Structural failure

The current comparator/replay dynamics do not fit standard Φ-regret machinery without substantive redesign.

Explain why.

Do not blur these categories.

---

# 16. If Blum–Mansour does not fit, search the neighboring literature

Only if needed, investigate the closest relevant online-learning classes.

Potential areas:

* swap/internal regret;
* contextual regret;
* sleeping experts;
* specialists;
* adaptive regret;
* policy regret;
* stateful online learning;
* online learning with changing action sets;
* regret with endogenous state transitions.

Use primary sources for technical claims.

The question is not:

> what regret theory sounds similar?

It is:

> what theorem has hypotheses matching the lawful-edit/replay object we actually have?

Do not launch a broad literature review if Blum–Mansour already fits cleanly.

---

# 17. Do not run item 30 prematurely

Item 30 is the actual Φ-regret experiment/theorem test.

Do not run it until this round produces a valid applicability bridge.

If verdict A or B obtains and implementation is cheap, you may prepare the exact interface needed by item 30.

But stop before claiming the empirical/global regret result unless the current round explicitly and honestly expands into it after the theorem bridge is proven.

Default:

[
\boxed{
\text{Stage ends with item 29, not item 30}.
}
]

---

# 18. Item 31 interaction

Use item 31 only where it helps clarify the comparator class.

Ask whether a recurring remediable failure can already be represented using the existing typed objection/filing machinery.

Do not redesign the docket.

If the current ontology already supports the needed filing, demonstrate that briefly.

If not, record the exact interface debt.

Item 31 should not distract from item 29.

---

# 19. F4

Do not resolve F4 unless a maintainer decision already exists.

The underlying issue is that executable answerability/docket structures live in a disposable/non-evidential forward tree while authoritative consolidation describes them.

This round may need to consume those structures.

If so:

* follow current repository policy;
* record exactly which implementation was used;
* do not silently promote disposable artifacts into canonical evidence.

If F4 materially blocks the learning round, report that.

Do not invent a repository-wide fix as side work.

---

# 20. Philosophical target

Keep the deep goal visible.

The learning programme is trying to establish something stronger than constrained motion.

The learner should be:

1. **answerable** — unable to erase its own historical obligations;
2. **reasons-responsive** — individual revisions require legitimate local reason;
3. **learning** — lawful alternative local revisions do not keep outperforming it indefinitely.

Schematic target:

[
\boxed{
\text{historically answerable}
+
\text{locally legitimate}
+
\text{globally no-regret against lawful repair}.
}
]

This is the normative-learning architecture under investigation.

Do not claim the third component until earned.

---

# 21. What success would mean

If item 29 succeeds, the important result is not simply:

> Blum–Mansour applies.

It is:

> the workspace's locally certified, historically lawful repairs form a comparator class compatible with a genuine online-learning theorem.

That would convert the current learning frontier from:

[
\text{theorem-applicability debt}
]

to:

[
\text{theorem/empirical-test debt}.
]

That is a substantive research-state transition.

---

# 22. Possible negative result

A particularly valuable negative result would be:

[
\boxed{
\text{stateful historically lawful replay comparators are not ordinary Φ-comparators}.
}
]

If so, characterize the exact obstruction.

For example:

* prefix dependence;
* changing action sets;
* downstream state effects;
* endogenous legality;
* lack of counterfactual feedback.

That may tell us what a genuinely new **normative learning theory** needs to generalize.

Do not regard that as failure.

---

# 23. Formalization / executable artifacts

Use the cheapest appropriate verification.

This round is likely more theorem-interface/math than Lean-heavy.

Possible useful artifacts:

* finite exact-rational comparator harness;
* type-checked comparator definitions;
* exhaustive small counterexamples;
* theorem-hypothesis matching tests;
* formal mathematical note;
* Lean only where it materially clarifies a stable theorem.

Do not formalize literature transcription for its own sake.

If a clean generic reduction/encoding theorem stabilizes and fits the existing Lean substrate, formalization is welcome.

---

# 24. Independent red team

Before closure, give the proposed applicability result to an independent adversarial agent without the constructing agent's reasoning.

Ask:

1. Is this really the Blum–Mansour comparator class?
2. Is the action set fixed where required?
3. Are changing action sets hidden by invalid padding?
4. Is the comparator fixed ex ante?
5. Does a prefix-dependent guard violate the theorem?
6. Does the comparator read future information?
7. Is lawfulness independent of profitability?
8. Is replay changing future state in a way the theorem does not model?
9. Is lifetime influence actually bounded?
10. Is counterfactual feedback available?
11. Is the loss bounded?
12. Is the claimed encoding regret-preserving?
13. Is the comparator class inhabited/nontrivial?
14. Would an easier neighboring regret theorem fit better?
15. What is the cheapest counterexample?
16. Has item 30 been smuggled into item 29?
17. Does the philosophical gloss overstate what low charge regret would establish?

Persist the verdict.

Do not silently patch major failures.

---

# 25. Consolidation

Before closure, compress the round.

Persist a concise leverage learning note, e.g.:

`projects/leverage/.../PHI_REGRET_APPLICABILITY.md`

or the repository-conformant equivalent.

It should state:

1. actual learner/action object;
2. loss;
3. lawful comparator type;
4. replay semantics;
5. feedback model;
6. action-set structure;
7. guard structure;
8. exact Blum–Mansour theorem considered;
9. applicability mapping;
10. verdict;
11. missing lemmas if any;
12. next theorem/test;
13. philosophical interpretation;
14. debt update.

Do not create multiple overlapping "final" notes.

---

# 26. Update `PRIORITIES.md`

At closure update the leverage items honestly.

## Item 29

Mark:

* closed-positive;
* closed-negative;
* partially closed;
* or blocked

with the exact result.

If a theorem/encoding applies, state which.

If a neighboring regret framework replaces Blum–Mansour, record the replacement.

---

## Item 30

Only promote/unblock it if item 29 genuinely supplies the applicability bridge.

Do not mark it achieved.

The next task should then specify exactly what regret quantity to compute/prove.

---

## Item 31

Update only if this round actually resolves part of it.

---

## New item

If item 29 fails for one precise repairable reason, create a new numbered item only if the missing statement now has a clear acceptance shape.

Otherwise put it in the ingenuity section.

Do not multiply priorities unnecessarily.

---

# 27. Update `RESEARCH_STATE.md`

Reconcile the leverage section.

Preserve the deference section unchanged except for mechanical merge compatibility.

The leverage section should accurately state:

### Aspirational mathematical claim

A genuine online-learning guarantee against historically lawful repairs.

### Constructed mathematical state

Whatever this round actually establishes about theorem applicability.

### Explicit non-result

Low Φ-regret itself remains unproved unless this round unexpectedly and legitimately proves it.

### Aspirational philosophical gloss

A reason-responsive answerable agent can improve without an externally supplied fixed normative target.

### Constructed philosophical gloss

Use only what the current substrate + applicability result supports.

### Controlling debt

Update from applicability debt to the correct next type.

---

# 28. Update `DECISIONS.md`

Do not manufacture maintainer decisions.

Add only genuinely consequential pending judgments.

Examples might include:

* adopt a replacement regret framework as the programme's named target;
* approve a substantive comparator-definition change;
* resolve F4 if it became blocking.

Pure theorem applicability does not necessarily need a maintainer decision.

If no new human decision is required, do not add one.

Preserve all unrelated deference decisions/status exactly.

---

# 29. Update `PROVENANCE.md` and project indices

Record:

* this round;
* executor/model;
* formal/executable artifacts;
* report;
* research status.

Update leverage landing/index files so a fresh agent can find the learning line.

Do not rewrite historical prompts.

Do not touch root README unless repository policy requires a purely mechanical pointer update; default is no edit.

---

# 30. Workspace-wide reconciliation

Although this is a **leverage-only research round**, the repository should remain globally coherent.

Before PR:

* verify `RESEARCH_STATE.md` still preserves current deference Stage V state;
* verify `PRIORITIES.md` does not regress deference items;
* verify `DECISIONS.md` does not lose unrelated pending decisions;
* verify no stale branch version overwrote shared state.

Research only leverage.

Reconcile shared surfaces safely.

---

# 31. Verification

Run all applicable repository checks.

At minimum:

* exact-rational leverage harnesses;
* new applicability/counterexample tests;
* path gate;
* provenance checks;
* living-document checks;
* `git diff --check`;
* house suite;
* Lean/build checks if shared policy requires them;
* any new Lean theorem checks if formalization was added;
* sorry/axiom audit where applicable.

Record exact verification results in the round report.

Avoid putting volatile counts into stable front-door prose.

---

# 32. Final verdict taxonomy

The final report must classify item 29 as exactly one of:

[
\boxed{
\begin{array}{ll}
\textbf{Direct} & \text{Blum–Mansour applies directly}\
\textbf{Encoded} & \text{applies through a proved regret-preserving encoding}\
\textbf{Near miss} & \text{specific lemma(s) remain}\
\textbf{Replacement} & \text{another regret framework is the correct one}\
\textbf{Structural failure} & \text{current lawful-repair object lies outside the standard framework}
\end{array}}
]

No vague "promising."

---

# 33. PR endpoint

This round must end in a **leverage research-state PR to current `main`**.

Before opening:

1. consolidate the science;
2. reconcile `PRIORITIES.md`;
3. reconcile `RESEARCH_STATE.md`;
4. reconcile `DECISIONS.md`;
5. update provenance/indexes;
6. run verification;
7. commit;
8. push;
9. open the PR.

Do not merge manually unless live repo policy/maintainer authorization says to.

The PR description must distinguish:

* source-theorem facts;
* proved applicability/encoding results;
* finite/exhaustive findings;
* counterexamples;
* implementation artifacts;
* conjectures;
* philosophical interpretation;
* open debt.

Prominently state:

[
\boxed{
\text{whether item 29 succeeded and whether item 30 is now legitimately ready.}
}
]

---

# 34. Final maintainer memo

End with:

1. What exact Φ-regret theorem/reduction was audited?
2. What is the lawful comparator type?
3. Is it fixed or history-dependent?
4. How are guards represented?
5. Are action sets fixed or varying?
6. What is the replay semantics?
7. What loss is being minimized?
8. Is counterfactual feedback actually available?
9. Does legality remain independent of profitability?
10. Does one edit have bounded lifetime influence?
11. What role does no-solvency-coupling play?
12. Does Blum–Mansour apply directly?
13. If not, is there a valid encoding?
14. If not, what framework fits better?
15. What did the red team kill?
16. What is item 29's final status?
17. Is item 30 now ready?
18. What is item 31's status?
19. Did F4 matter?
20. What is now constructed mathematically?
21. What remains aspirational?
22. What is the strongest justified philosophical gloss?
23. What research debt changed type?
24. What is the exact next leverage task?
25. Were `RESEARCH_STATE`, `PRIORITIES`, and `DECISIONS` fully reconciled?
26. Was current deference state preserved untouched?
27. What maintainer decisions, if any, remain?
28. What are the human review surfaces?
29. PR URL.

The governing question is:

[
\boxed{
\text{Do historically lawful local repairs form a comparator class to which a real online-learning theorem applies?}
}
]

And the deeper research objective is:

[
\boxed{
\text{answerability}
+
\text{reasons-responsiveness}
+
\text{genuine online learning}.
}
]

Do not claim that synthesis until the theorem machinery actually supports it.

**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
