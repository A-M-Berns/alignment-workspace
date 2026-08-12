# Alignment Workspace Research Prompt — Reframe the Learning Track Around a General Normative-Learning Interface

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
**Target repository:** `A-M-Berns/alignment-workspace`
**Date:** 2026-08-11

## Mission

Reorganize the leverage / normative-learning track around its emerging general theorem ambition.

This is **not a deep new-science round**. Do not attempt to prove a new regret theorem, solve comparator coverage, redesign the reasons architecture, or close the current learner-integration obstruction.

The goal is to make the repository clearly express the research direction now visible after PRs #20 and #21:

> The eight-action, nine-program, docket-charge construction should be treated as a worked instantiation of a more general normative-learning interface, not as the final theorem statement.

The intended eventual theorem shape is approximately:

> Given a suitable bounded prospective loss process and a suitable causal rule grammar compiling public reasons into admissible action transformations, an online learner obtains low regret against the transformations expressible by that grammar; additional conditions may allow that local guarantee to lift to genuine counterfactual self-correction.

Do **not** claim that theorem has been proved.

Your task is to reorganize the research surfaces so that:

1. the current result is stated accurately as a concrete finite instantiation;
2. the general abstraction is clearly identified as the next theorem program;
3. architecture-specific machinery is separated from theorem-generic machinery;
4. future rounds can attack the generalization without first reverse-engineering what in the current construction is essential.

---

# I. Controlling current state

Treat the merged repository as authoritative.

PR #20 established the repaired theorem interface in the frozen environment:

* fixed semantic response alphabet with `N = 8`;
* nine fixed declarative lawful programs;
* causal actual-prefix transformations;
* non-capture for the exact comparator class;
* charge/regret preservation;
* recurrent-failure lower bound.

PR #21 constructed the Blum–Mansour learner:

* eight source-action rows;
* nine program weights per row;
* 72 learner weights;
* transformation-weighted stochastic matrix;
* stationary mixed-action selection;
* row-conditioned update;
* numerical experiments consistent with the source theorem.

The present verdict is:

> **Learning-positive, integration-blocked.**

The expected mixed-action low-regret result is available for the frozen nine-program class. Positive asymptotic expected mass on represented uniformly saving repairs is thereby retired.

The remaining item-30 integration debt is that:

* learner computation is not priced in the declared bounded service model;
* learner policy state is not historically recorded as an answerable artifact.

Also preserve the explicit limitations:

* no exact-real executable identity;
* no sampled-path/high-probability theorem;
* no anytime theorem;
* no rich comparator-coverage theorem;
* low charge regret is not normative correctness.

Do not weaken or strengthen those conclusions.

---

# II. The research ambition to encode

The repository should now distinguish three levels.

## Level A — Generic online-learning interface

Abstract away from the current warrant, docket, tolling, and interval vocabulary.

The eventual generic theorem should be expected to involve objects of roughly the following form:

### Semantic action space

A finite action/response set

[
A
]

with fixed cardinality independent of horizon.

### Public pre-action state

A public causal state

[
s_t
]

computed from information available before the current action.

### Loss generator

A bounded prospective loss vector

[
G(s_t)=\ell_t\in[0,L]^A.
]

The eventual theory should not be conceptually tied to docket liability specifically.

The current docket charge should be recorded as **one constructed admissible candidate loss process**, notable because it is internally derived from the practical-demand layer and does not scalarize unrelated quantities using invented exchange rates.

### Rule grammar / comparator compiler

A rule language or grammar

[
\mathcal G
]

whose programs compile to causal action transformations of the form

[
\llbracket g\rrbracket(s_t,a)\in A.
]

The eventual theorem should ideally speak about a general class of such transformations rather than nine hand-written programs.

Do not decide in this round whether the right complexity measure is finite cardinality, description length, prior mass, VC-like complexity, or something else.

Record that as open theorem design.

---

## Level B — Normative compilation interface

The online learner need not understand warrants, defeaters, commitments, or objections.

Those belong to a separate question:

> Under what conditions does a normative architecture soundly compile its public reasons into admissible causal transformations?

The current reasons-responsiveness interface suggests candidate conditions such as:

* historical availability;
* causal/public information access;
* reason connection;
* defeater discipline;
* scope;
* magnitude discipline;
* burden/history preservation;
* replacement support;
* independence of lawfulness from comparative advantage.

Treat these as **candidate interface conditions extracted from the current instantiation**, not as a proved complete axiomatization of normative rule grammars.

The desired architectural decomposition is:

```text
normative architecture
        |
        | compile reasons
        v
lawful transformation grammar
        |
        | online learning
        v
regret / self-correction guarantee
```

Make this decomposition visible in the repository.

---

## Level C — Counterfactual stability

The current theorem works in a deliberately frozen additive environment.

A richer architecture may allow an edit today to change:

* future obligations;
* future reasons;
* future losses;
* service availability;
* accounting state;
* ontology or procedure.

The repo has already established that one local edit can have horizon-sized downstream effects when solvency coupling is restored.

Therefore record a distinct future theorem problem:

> When does low regret against local causal transformations lift to regret against the full replayed counterfactual world?

A likely abstract object is a counterfactual-distortion term

[
B_T(g)
]

measuring the discrepancy between local fixed-loss comparison and full counterfactual replay.

The attractive target condition is something like

[
B_T(g)=o(T),
]

but this round must not claim that this is sufficient under the final intended semantics unless that result is already formally available.

The purpose here is only to identify **counterfactual stability as its own theorem layer**, rather than hiding the frozen-environment assumptions inside the main learning theorem.

---

# III. Concrete repository work

Perform a documentation and organization pass that makes this architecture legible.

Prefer small, durable edits over a new large speculative document tree.

## A. Create one general-interface research note

Create a note under an appropriate leverage research path, with a name such as:

`projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md`

or another concise name consistent with repository conventions.

It should contain:

1. the motivation for abstraction;
2. the three-level decomposition above;
3. a table distinguishing:

   * theorem-generic objects;
   * architecture-specific objects;
   * current concrete instantiation;
4. candidate eventual theorem shapes, explicitly marked **ASPIRATIONAL / OPEN**;
5. a list of assumptions presently needed only because of the current fixture;
6. a section titled approximately **“What the current result already establishes”**;
7. a section titled approximately **“What must be generalized before this becomes the paper-level theorem.”**

Do not reproduce entire existing round documents.

This should be a routing document, not another consolidation.

---

## B. Extract a minimal interface table

Somewhere in that note, include a compact table like:

| generic role                | current instantiation                          | status                          |
| --------------------------- | ---------------------------------------------- | ------------------------------- |
| semantic action set `A`     | eight semantic labels                          | constructed                     |
| public state `s_t`          | restricted actual-prefix reason context        | constructed                     |
| loss generator `G`          | docket liability / charge vector               | constructed                     |
| rule grammar `𝒢`           | nine declarative lawful programs               | constructed, weak               |
| compiler soundness          | reasons-responsiveness checks + decoder bridge | partial / architecture-specific |
| learner                     | Blum–Mansour Theorem 18 construction           | constructed                     |
| counterfactual stability    | frozen filings/reasons, no suspension/solvency | assumption, not generalized     |
| learner-state answerability | none                                           | blocking                        |
| computation budget          | none                                           | blocking                        |

Use exact repository terminology where appropriate.

The point is to make it immediately obvious which parts are accidental features of the fixture.

---

## C. Reframe the learning-track landing surfaces

Update `projects/leverage/README.md` and `RESEARCH_STATE.md` minimally so that the current learning track is described as:

> a successful finite instantiation and proof-of-concept for a broader normative-learning interface theorem.

Preserve the current “Learning-positive, integration-blocked” verdict.

Do not turn aspiration into accomplishment.

The current research state should make clear that there are now **two different next directions**:

1. **integration:** make the current learner itself bounded and answerable;
2. **generalization:** extract an architecture-neutral theorem over loss generators and rule grammars.

Neither should silently supersede the other.

---

## D. Reconcile `PRIORITIES.md`

Without renumbering existing items, update the learning-track section so future work does not read as though item 31 is automatically the only next research move.

If repository governance permits filing new items within this dispatched scope, file narrowly scoped items corresponding to execution-ready generalization work.

Good candidates are:

### General loss interface

> Determine which properties of docket charge are actually used by the lawful-regret theorem, and parameterize the learner/bridge over that minimal bounded prospective loss interface.

This should **not** ask the next agent to invent the final class of normative losses.

It should ask for interface extraction.

### Rule-grammar interface

> Extract the minimal causal transformation interface satisfied by the nine declarative programs, separating BM-required structure from reasons-responsiveness structure.

Again, this is interface work, not the final infinite-grammar theorem.

### Counterfactual-stability formulation

Only file this if it can be made execution-ready without doing new science. Otherwise put it in the general-interface note as a theorem-design question.

Do not create a work order whose acceptance check is “solve counterfactual regret.”

If the correct statement is not yet known, leave it as an explicitly named research direction rather than manufacturing a numbered item.

---

# IV. Distinguish generic theorem requirements from normative requirements

This is an important conceptual cleanup.

Create a clear split between:

## Requirements imposed by the online-learning theorem

Examples:

* finite/fixed action representation;
* causal transformation;
* bounded loss;
* appropriate feedback availability;
* finite comparator family in the current theorem;
* stationary-distribution construction.

and:

## Requirements imposed by the normative interpretation

Examples:

* lawfulness independent of profitability;
* grounds available historically;
* defeaters respected;
* obligations not erased;
* replacement supported;
* appropriate authority/scope.

The current repository sometimes necessarily discusses both in the same round because it was building the bridge.

The new organizational layer should make the distinction explicit.

A future reader should be able to ask independently:

> Does this grammar compile to a legal Φ-comparator?

and:

> Is this comparator normatively licensed by the architecture?

Those are different questions.

---

# V. Clarify the role of the current loss

Do not redesign the loss.

Do not add penalties for merits errors, incoherence, resource use, or other quantities.

Instead record the present status accurately:

> Docket liability is the first constructed loss because it is bounded, public, derived from the record, and already prices practical disposition without introducing an unsupported scalarization.

Then make explicit the generalization ambition:

> The intended paper-level theorem should depend only on structural properties of the loss process, not on the substantive interpretation “docket liability.”

Record as future targets, not established results:

* arbitrary bounded prospective public loss generators;
* invariance under harmless transformations such as positive scaling and action-independent shifts;
* possibly broader notions of loss-equivalence;
* possibly vector-valued/non-scalar evaluation in later work.

Do not pursue Blackwell approachability or vector-valued regret in this round.

---

# VI. Clarify the role of the nine programs

The nine-program class is a **test fixture and finite theorem instantiation**.

Do not describe it as an adequate normative repair language.

Preserve the existing witness that zero Φ-regret against this class can coexist with substantially higher total charge than action Hedge.

Use that result constructively:

> It demonstrates why comparator-language generalization is not optional if the project is to support a strong normative-learning claim.

The eventual ambition may involve:

* a grammar generating many repairs;
* complexity-sensitive regret;
* prior-weighted comparator classes;
* description-length bounds.

Do not choose among these in this round.

Simply record them as candidate theorem directions.

---

# VII. Preserve the current paper-level theorem arc

The repository should make the emerging paper arc easy to see:

1. **Alignment problem:** agents may need to revise normative judgments after deployment without a fixed normative target.
2. **Lawful revision:** reasons determine which counterfactual changes count as admissible corrections.
3. **Generic learning interface:** admissible corrections compile to causal transformation comparators.
4. **Online-learning theorem:** low regret against the resulting comparator class.
5. **Self-correction consequence:** uniformly beneficial represented repairs cannot remain relevant at positive asymptotic rate.
6. **Current instantiation:** docket liability + finite reasons interface + eight actions + nine programs.
7. **Limits:** comparator coverage, endogenous/counterfactual loss dynamics, learner-state answerability, computation cost, inquiry.

This section can live in the new interface note.

Do not draft the actual paper.

---

# VIII. Avoid these mistakes

Do not:

* claim a general normative-learning theorem already exists;
* rewrite Blum–Mansour as though it were a new theorem;
* claim the current nine rules form a “universal” grammar;
* call docket charge a measure of normative correctness;
* conflate rule lawfulness with low loss;
* conflate actual-action admissibility with comparator admissibility;
* solve the learner-state/service obstruction by declaring computation free;
* redesign ontology;
* broaden the action set;
* change the current experiment suite;
* change theorem statuses;
* register speculative claims;
* turn every future idea into a numbered priority;
* produce another large consolidation duplicating existing files.

---

# IX. A useful conceptual vocabulary

Use restrained terminology.

Preferred distinctions:

* **loss process / loss generator**
* **semantic response space**
* **public pre-action state**
* **rule grammar**
* **compiled transformation**
* **lawful comparator**
* **normative compilation**
* **counterfactual stability**
* **worked instantiation**
* **general interface theorem** or **normative-learning interface theorem** as an aspirational label

Avoid proliferating new branded names.

Any new permanent term remains provisional pending maintainer review.

---

# X. Success criterion

This round succeeds if, after it lands, a new researcher can answer all of the following without reconstructing the history of PRs #17–21:

1. What part of the current result comes directly from generic online-learning theory?
2. What part is supplied by the normative architecture?
3. Why is docket liability only one possible loss process?
4. Why are the nine comparator programs only a finite instantiation?
5. What is the intended general theorem interface?
6. Why is counterfactual stability a separate issue?
7. What remains blocking for the current learner to count as a fully bounded answerable process?
8. What concrete next rounds could generalize the result without redesigning the entire architecture?

If those answers are clear, stop.

Do not use this organizational round as an excuse to do the theorem work itself.

---

# XI. Deliverables

At minimum:

* one concise general-interface note;
* minimal updates to `RESEARCH_STATE.md`;
* minimal updates to `projects/leverage/README.md`;
* a careful reconciliation of the learning-track portion of `PRIORITIES.md`;
* provenance entry for the new organizational artifact;
* round report stating explicitly that no new scientific result was claimed.

If new priorities are filed, record that they were filed under this maintainer-dispatched scope and give each a genuinely executable acceptance criterion.

No changes to the deference line.

No changes to the authoritative leverage consolidation except a very small routing pointer if one is clearly necessary and repository conventions permit it.

---

# XII. Final report

End with:

### What changed in the research architecture

Explain how the learning track is now organized.

### What did not change scientifically

State that the finite BM result, recurrent-failure consequence, comparator weakness, and integration obstruction retain their prior statuses.

### The intended theorem program

State, explicitly as aspiration:

> Generalize from one docket-loss/nine-rule instance to a theorem over a class of bounded prospective loss processes and a class of causal normatively compiled rule grammars, with counterfactual stability treated separately.

### Recommended next executable round

Recommend one small generalization round that requires little or no new conceptual invention—for example, extracting and parameterizing the loss interface—rather than attempting the whole theorem at once.

---

**Prompt provenance:** GPT-5.6 Sol (OpenAI)
**Maintainer:** A. M. Berns
