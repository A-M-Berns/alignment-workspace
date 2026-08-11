# Workspace Ethos Pass — Consolidation Layers, Aspirational/Constructed Status, and Research Debt

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)

## Mission

Refine the workspace’s research-state architecture so that it remains legible under substantial AI-assisted research without becoming procedurally bloated.

The guiding problem is:

> How do we let agents explore aggressively while keeping it cheap to tell what the research program currently aspires to, what it has actually constructed, what remains unresolved, and what has received human judgment?

This is primarily a **workspace framing / information-architecture pass**, not an object-level research round.

It may run in parallel with active deference/corrigibility research.

Accordingly:

[
\boxed{
\text{do not redesign active research objects underneath ongoing work.}
}
]

Prefer small, additive, repo-conformant changes. Do not impose elaborate workflow or mandatory ceremony.

---

# 0. First inspect the live workspace

Do not assume this prompt knows the exact current repository structure.

Read the live repository, including as applicable:

* root and nested `AGENTS.md`;
* `README`;
* `DECISIONS.md`;
* `PROVENANCE`;
* `PRIORITIES.md`;
* project roadmaps and ledgers;
* current consolidation reports;
* research-track reports;
* canonical specification documents;
* current treatment of archived/frozen/superseded work;
* any existing review, registration, status, or provenance conventions.

Use the deference/corrigibility project as the main case study because it has undergone several research/consolidation rounds, but design the resulting conventions to be usable across the workspace, including leverage/normative-learning work and future projects.

Before implementing anything, identify what the repository **already does well** and reuse it.

Do not create parallel machinery for distinctions that are already represented adequately.

---

# 1. Governing design principle: discipline without procedural bloat

The workspace is a research lab first.

Adopt this principle:

[
\boxed{
\text{structure should reduce ambiguity and cognitive load, not create ceremony.}
}
]

Avoid a system where ordinary research requires:

* formal amendment objects;
* multi-step approvals;
* mandatory status metadata on every note;
* redundant registries;
* constant manual synchronization;
* extensive form-filling before an agent can investigate an idea.

Heavyweight treatment is justified only where coordination cost is actually high—for example:

* changing a shared formal skeleton;
* changing canonical ontology;
* altering trust/build/governance machinery;
* registering a major result;
* changing something on which many active artifacts depend.

Ordinary research should remain ordinary Git research.

Prefer conventions over mechanisms where conventions suffice.

Prefer one useful file over three registries.

Prefer a compact human-readable table over a schema unless machine structure provides clear immediate value.

---

# 2. Establish three research-state layers

The workspace should clearly distinguish:

[
\boxed{
\text{Research Lab}
\longrightarrow
\text{Agent-Consolidated State}
\longrightarrow
\text{Human-Canonical State}
}
]

Implement this distinction in the lightest useful way.

## 2.1 Research Lab

Purpose:

> maximize exploration.

This includes:

* raw research tracks;
* speculative theorem shapes;
* negative attempts;
* finite harnesses;
* agent reports;
* alternative models;
* prompts;
* provisional vocabulary;
* failed approaches.

The lab may be messy.

Lab artifacts are evidence/history, not automatically the current research position.

---

## 2.2 Agent-Consolidated State

Purpose:

> maximize coherence, compression, and recoverability.

An agent-consolidated artifact represents:

> the best current machine-produced synthesis of the research evidence available in the workspace.

It may:

* reconcile several tracks;
* identify the current best object;
* mark superseded approaches;
* compress duplicated terminology;
* classify open debts;
* distinguish aspiration from construction;
* propose canonical changes;
* identify the controlling next question.

It is **not automatically what the maintainer endorses**.

Make this status explicit.

Do not call agent consolidation “canonical.”

---

## 2.3 Human-Canonical State

Purpose:

> maximize clarity, judgment, and stability.

This layer should remain deliberately small.

It represents the research position that has received human/maintainer judgment.

It may contain:

* current core questions;
* current definitions;
* constructed mathematical results that matter;
* current philosophical interpretation;
* important impossibility/fence results;
* accepted assumptions;
* acknowledged debts;
* controlling research direction.

Important:

[
\boxed{
\text{agents may propose changes to the canonical state but may not silently confer canonical status.}
}
]

Do not infer maintainer endorsement merely because:

* a theorem is Lean-verified;
* several agents agree;
* a parent report recommends it;
* it is newer than the existing canonical statement.

If existing repository conventions already have a suitable mechanism for maintainer adoption, use them.

Do not invent an elaborate new approval process.

---

# 3. Define precedence for interpreting the workspace

The intended epistemic precedence should be clear enough for both fresh agents and a future public chatbot.

Default current-state interpretation should approximately be:

[
\boxed{
\text{Human-Canonical}

>

\text{Agent-Consolidated}

>

\text{Research Lab}
}
]

But this is a **precedence for representing the current program**, not a truth hierarchy.

A lower-level artifact can challenge a higher-level claim.

For example, the workspace must be able to represent:

> “The canonical view currently says C, but a new unresolved research result purports to refute C and has not yet been consolidated or reviewed.”

Do not hide conflicts merely because they have not reached the canonical layer.

Historical artifacts should remain retrievable without having equal authority to current artifacts.

---

# 4. Introduce the Aspirational / Constructed / Gap distinction

This should become one of the central lightweight framing conventions.

For an important research object, distinguish:

[
\boxed{
\text{Aspirational}
\qquad
\text{Constructed}
\qquad
\text{Gap}
}
]

Do this on **two registers**.

## 4.1 Mathematical register

### Aspirational mathematical state

What theorem, object, mechanism, or construction would constitute the hoped-for technical result?

### Constructed mathematical state

What has actually been defined, proved, implemented, verified, or formally built?

### Mathematical gap

What precisely prevents the constructed state from reaching the aspiration?

---

## 4.2 Philosophical register

### Aspirational philosophical gloss

What conceptual claim would the intended result vindicate if the full technical program succeeded?

### Constructed philosophical gloss

What does the existing mathematics actually warrant saying now?

### Interpretive gap

What further mathematics or argument would be required before the aspirational gloss is justified?

---

This distinction should make it difficult for an agent or reader to confuse:

[
\text{“this is the theorem we want”}
]

with:

[
\text{“this is a theorem we have.”}
]

Likewise:

[
\text{“this is the conceptual picture motivating the work”}
]

with:

[
\text{“the current mathematics establishes this conceptual picture.”}
]

---

# 5. Prefer a lightweight recurring research-state format

Do not migrate every existing file mechanically.

Instead, propose and where useful implement a compact convention for canonical and agent-consolidated project summaries.

A good default shape is:

## Question

What are we trying to understand?

## Aspirational mathematical picture

What would technical success look like?

## Constructed mathematical state

What exists now?

## Aspirational philosophical gloss

What would the hoped-for result mean?

## Constructed philosophical gloss

What does the current work genuinely support?

## Fences / negative knowledge

What attractive approaches or stronger claims have been ruled out?

## Research debt

What kinds of unresolved work remain?

## Controlling gap

What currently blocks the next major advance?

## Next question

What should the research attack next?

Do not require every small research note to use this structure.

It is principally for consolidation/frontier/canonical views.

---

# 6. Research debt accounting

“Open problem” is too coarse.

Introduce a lightweight vocabulary for different kinds of research debt.

Use only categories that prove useful; do not force every project to populate every category.

Candidate categories:

### Model debt

The right mathematical object is not yet adequately defined.

Example shape:

> the comparator itself is not yet well-posed.

### Theorem debt

The object and statement are sufficiently clear, but the proof is missing.

### Assumption debt

A positive result depends on an antecedent whose strength, necessity, or interpretation remains unresolved.

### Interface debt

Two coherent components do not yet compose cleanly.

### Formalization debt

A mathematical argument exists but has not been promoted into the desired formal substrate.

### Verification debt

An artifact exists but lacks the intended independent checking/audit.

### Interpretation debt

The mathematics is reasonably clear but its correct philosophical or research significance remains unsettled.

### Scope debt

An important omitted phenomenon has been identified, but it is not yet clear whether it should be solved, modeled, or explicitly fenced out.

### Compression debt

The live research state has become too complicated to recover cheaply from the canonical/consolidated layer.

This last category is particularly important.

Do **not** assign numeric debt scores unless the repository already has a useful reason to do so.

The point is classification, not pseudo-precision.

---

# 7. Debt can change type

Make explicit that reclassifying debt can itself be genuine research progress.

For example:

[
\text{apparent theorem debt}
\rightarrow
\text{assumption debt}
]

or:

[
\text{“prove theorem X”}
\rightarrow
\text{model/interface debt first}.
]

A failed proof round that reveals the target is ill-posed is not merely “no progress.”

The consolidated state should make such transitions visible.

---

# 8. Consolidation discipline

The workspace should encourage:

[
\boxed{
\text{explore freely for a bounded interval, then compress aggressively.}
}
]

Do not impose a rigid clock.

Instead identify **soft consolidation triggers**.

A consolidation pass is probably due when:

* several agents introduce competing names for the same object;
* a result changes the interpretation of multiple earlier artifacts;
* live conceptual forks are becoming difficult to enumerate;
* fresh agents require large amounts of historical material to understand the present;
* agents begin treating superseded reports as current;
* the initialization prompt required to state the live research state becomes very large;
* the roadmap accumulates layers of exceptions and caveats;
* active priorities contain dead or already-resolved routes;
* the distinction between aspiration and construction has become blurry.

A strong consolidation success criterion is:

> Can a fresh strong agent recover the live research state from the agent-consolidated/canonical layer without reading the full history?

If not, there is compression debt.

---

# 9. Consolidation should include garbage collection

A consolidation pass should not merely create one more summary.

It should reduce the **live conceptual working set**.

Where safe and repository-conformant, consolidation should:

* mark superseded definitions clearly;
* retire dead routes from active priorities;
* collapse duplicate terminology;
* identify the current definition owner;
* distinguish active from historical questions;
* remove stale claims from default current-state views;
* compress several exploratory distinctions into the few that survived;
* preserve the historical artifacts rather than deleting evidence.

Desired principle:

[
\boxed{
\text{history may remain lossless; the canonical layer should be aggressively compressed.}
}
]

Do not rewrite old reports to pretend the research always had its current form.

---

# 10. Cheap deprecation

Implement or document a lightweight convention for superseded material.

A minimal form may be enough:

* `SUPERSEDED BY: ...`
* `STATUS: historical`
* `REASON: ...`

or whatever fits existing repo style.

The aim is that a future agent or chatbot can retrieve old ideas without treating them as equally current.

Do not build an elaborate deprecation registry unless the repository clearly needs one.

---

# 11. Definition and symbol stability

Consider a very small current-definition/symbol surface for research lines that need it.

Its purpose is to prevent conceptual drift in objects such as:

* agents/processes;
* policy classes;
* execution objects;
* quantities;
* grades;
* settlement;
* jurisdiction;
* specialized project notation.

The useful information is:

* current symbol/name;
* current meaning;
* where the definition is owned;
* whether it is canonical, agent-consolidated, or provisional.

Keep this compact.

Do not create an ontology-management bureaucracy.

---

# 12. Module interfaces

Where the repo already has genuinely modular research components, make their **interfaces** easier to see.

An interface description should answer:

> What does this module supply downstream?

and:

> What does it explicitly not supply?

For example, a module might supply:

* calibration;
* a competence condition;
* protected execution semantics;
* an uncertainty quantity;

without being allowed to silently supply:

* moral legitimacy;
* jurisdiction;
* prediction accuracy;
* choice optimality.

Use the deference project to determine whether such interface descriptions would materially reduce confusion.

If yes, add them in the lightest appropriate place.

Do not force every project into formal module contracts.

---

# 13. Human review surfaces

Agent consolidation should reduce the amount of material a human must inspect.

At the end of a substantial phase, the consolidated report should be able to identify a short list such as:

## Human review surfaces

* new shared definition;
* important theorem statement;
* substantive assumption;
* major negative result;
* philosophical reinterpretation;
* proposed canonical delta.

The goal is:

[
\boxed{
\text{human judgment over compressed consequential changes, not exhaustive rereading of agent output.}
}
]

Where possible, distinguish:

> **Proposed canonical delta**

from the full consolidation report.

This can simply be a small section, not a new workflow system.

---

# 14. Lab → Consolidation → Brief

Evaluate whether the current repo would benefit from making this architecture more legible:

[
\boxed{
\text{LAB}
\longrightarrow
\text{AGENT-CONSOLIDATED STATE}
\longrightarrow
\text{HUMAN-CANONICAL / BRIEF}
}
]

The lab preserves detailed research evidence.

Agent consolidation compresses it.

The canonical/brief layer exposes the current human-legible research state.

A future website/chatbot should normally answer from the upper two layers and descend into lab artifacts when:

* challenged;
* asked for evidence;
* asked for history;
* asked for a counterexample;
* asked how the current state was reached.

Do not build the website/chatbot in this pass.

Just make the workspace structure compatible with that future use.

---

# 15. Challenge before canonization

Preserve the workspace’s successful adversarial norm without turning it into ceremony.

For claims that are becoming load-bearing, encourage questions like:

* What is the cheapest model in which this fails?
* What assumption secretly carries the conclusion?
* Does this theorem become uninteresting under its antecedents?
* Is the philosophical gloss stronger than the mathematics?
* Has a previous witness already killed this route?

Do not require a formal adversarial report for every theorem.

The principle is:

[
\boxed{
\text{important claims should meet serious challenge before becoming canonical.}
}
]

---

# 16. Do not overbuild a claim graph yet

There are attractive future ideas such as:

* machine-readable claim graphs;
* theorem-to-paper dependency maps;
* objection edges;
* formal amendment objects;
* public challenge interfaces.

Evaluate them briefly.

But unless the existing workspace has an immediate concrete need, **do not implement heavy graph/schema infrastructure in this pass**.

Record them as aspirational workspace capabilities if useful.

The present objective is to improve the working research environment cheaply.

---

# 17. Parallel-safety constraint

This pass may occur while active object-level research is ongoing.

Therefore, while that research remains active:

### Safe / preferred

* documentation;
* additive conventions;
* small new ethos/frontier files;
* clarification of layer semantics;
* debt taxonomy;
* templates or examples;
* non-invasive status annotations;
* identifying future cleanup;
* documenting consolidation triggers.

### Avoid unless clearly safe

* renaming active research objects;
* moving files used by active agents;
* changing formal skeleton semantics;
* changing theorem statements;
* changing Lean APIs;
* changing path gates;
* redesigning `PRIORITIES.md` incompatibly;
* introducing mandatory metadata that breaks existing workflow;
* reorganizing active project directories.

If an apparently desirable framing change would disrupt active research, record it as a recommendation for the next consolidation boundary instead of performing it now.

---

# 18. Use the current deference work as a stress test

Inspect the current deference/corrigibility project and ask:

1. Can a fresh agent tell what is aspirational versus constructed?
2. Can it distinguish the mathematical aspiration from the philosophical aspiration?
3. Can it identify the current human-canonical position?
4. Can it tell what is merely an agent synthesis?
5. Can it locate historical failed routes without mistaking them for current ones?
6. Can it identify the dominant debt types?
7. Can it tell what the next controlling question is?
8. Can it tell which results are formal, finite-verified, report-level, architectural, or assumed?
9. Can it identify the major human review surfaces without reading every track?
10. Can it reconstruct why the program changed its mind on major concepts?

Use the answers to determine what implementation is actually needed.

Do not merely instantiate every idea in this prompt.

---

# 19. Likely implementation shape

The exact repository-conformant solution is yours to determine after inspection.

A good outcome might be surprisingly small—for example:

* one concise workspace ethos/research-state document;
* one lightweight consolidation template or convention;
* clarification in agent instructions about lab / agent-consolidated / human-canonical status;
* debt vocabulary incorporated into consolidation reports;
* a small current-state/frontier convention;
* one example application to the deference project;
* minor deprecation/status cleanup where obviously safe.

This is preferable to creating seven new registries.

If the repository already has documents that can absorb these functions, update those instead of multiplying files.

---

# 20. Human-canonical safety rule

This is load-bearing:

[
\boxed{
\text{do not mark new substantive research claims as human-canonical merely because this pass recommends them.}
}
]

You may:

* define what human-canonical means;
* identify which existing artifacts already have clear maintainer adoption;
* propose canonical changes;
* create a section listing proposed canonical deltas.

You may not manufacture maintainer review.

When status is unclear, say so.

---

# 21. Deliverables

Produce:

## A. Implemented framing changes

Make the smallest set of repo changes that materially improves the architecture.

## B. Workspace ethos / architecture explanation

Persist a concise description of:

[
\text{Lab}
\to
\text{Agent Consolidation}
\to
\text{Human Canonical}
]

plus:

[
\text{Aspirational}
/
\text{Constructed}
/
\text{Gap}
]

and research-debt vocabulary.

## C. Deference case-study audit

Briefly demonstrate how the distinctions apply to the live deference/corrigibility work.

Do not redo the deference research.

## D. Proposed canonical delta

List any changes that would require maintainer judgment.

Keep this short.

## E. Deferred structural ideas

Record promising but currently unnecessary infrastructure rather than implementing it.

## F. Procedural-bloat audit

Explicitly answer:

> What process did you consider adding but decline because the coordination benefit did not justify the ceremony?

This is an important deliverable.

---

# 22. Final evaluation

Conclude with answers to:

1. What was structurally confusing before this pass?
2. What did you change?
3. What remained intentionally lightweight?
4. How is agent-consolidated now distinguished from human-canonical?
5. How is aspirational now distinguished from constructed?
6. How are mathematical and philosophical versions separated?
7. What research-debt categories survived implementation?
8. What triggers consolidation?
9. How does consolidation reduce rather than add artifacts?
10. What is the intended precedence for a future chatbot?
11. What still creates compression debt?
12. What proposed changes require maintainer review?
13. What did you deliberately refuse to proceduralize?
14. Did any change interfere with active research?
15. Is the resulting setup simpler to reason inside than the prior setup?

The success criterion is not “more structure.”

It is:

[
\boxed{
\text{a fresh human or agent can recover the live research state more cheaply and with less risk of category error.}
}
]

And the central ethos is:

[
\boxed{
\begin{array}{c}
\textbf{Lab: explore freely}\
\downarrow\
\textbf{Agent-consolidated: compress aggressively}\
\downarrow\
\textbf{Human-canonical: exercise judgment sparingly}
\end{array}
}
]

with every serious research line making it easy to distinguish:

[
\boxed{
\text{what we hope to show}
\quad
\text{from}
\quad
\text{what we have actually shown}.
}
]

**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
