# Deference / Corrigibility Stage IV — Future-Agent Semantics and Comparator Reconstruction

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)

*Kept verbatim as sent, per `AGENTS.md` standard 12. The mathematical notation arrived
partly mangled in transmission and is preserved as received rather than repaired.*

---

## Mission

Stage III is closed and shipped as PR #10 with a negative result.

Do **not** treat that as a failed proof attempt to be patched locally.

Stage III established that the proposed FUD comparator did not contain the object it purported to contain.

The transferred arm was defined using the present evaluator's own conditional optimizer:

[
\phi(C)
=======

\arg\max_{\pi}
E_{P_n}[X_{n,\pi}\mid C].
]

Because (A_n) knew the objective, credence, and conditioning structure, this was not a genuinely later agent. It was the present agent's own contingent optimum written out as a future policy.

The resulting dominance theorem was therefore an envelope result:

[
\sum \max(\cdot)
\ge
\sum \text{anything},
]

not a theorem about epistemic improvement, deference, or jurisdiction.

The namespace has correctly been renamed from `JurisdictionTransfer` to `EnvelopeDominance`.

Stage III also showed that the attempted comparator erased the execution layer—including (\bot) and the protection structure where Stage II located the valuation content of jurisdiction—and then unsurprisingly found no jurisdictional term.

The next phase is therefore:

[
\boxed{
\textbf{construct a genuine future-agent comparator before attempting any FUD theorem.}
}
]

This is primarily a **research / semantics / model-construction phase**.

It may produce formal artifacts where statements stabilize, but do not optimize for theorem count.

A negative result is acceptable.

---

# 0. Inspect the live repository first

Do not trust this prompt for exact current file locations or commit state.

Inspect the live branch and PR history.

Read at minimum, where repository-conformant:

* applicable `AGENTS.md`;
* `DECISIONS.md`;
* `PRIORITIES.md`;
* `RESEARCH_STATE.md` if present;
* `CORRIGIBILITY_ROADMAP.md`;
* `CORRIGIBILITY_PAPER_LEDGER.md`;
* `FINITE_MODEL_SKELETON.md`;
* Stage II parent report;
* Stage III parent report;
* Stage III comparator specification;
* Stage III red-team report;
* Track I competence results;
* Tracks K/L jurisdiction/execution results;
* Track H calibration/magnitude results;
* relevant Lean modules including `EnvelopeDominance`;
* Item 25 and Item 27.

Verify the actual current build/test state before modifying anything.

Do not reopen Stage III's negative verdict unless you find a concrete verification defect.

---

# 1. Frozen Stage III conclusion

Treat the following as settled research constraints unless contradicted by a genuine defect.

## 1.1 Present contingent optimization is not a future agent

Do not define future (A_{g(n)}) as:

[
\arg\max E_{P_n}[X\mid C].
]

Do not use any equivalent construction where the present evaluator already knows all inputs needed to compute the future policy exactly.

A future agent suitable for FUD must not collapse to:

[
\boxed{
\text{present agent's own optimal contingent plan}.
}
]

---

## 1.2 Better-informed must remain compatible with fallibility

A genuine future-agent object must permit:

[
A_{g(n)}
\text{ has epistemic access unavailable to }A_n
]

while also permitting:

[
A_{g(n)}
\text{ selects an action that is not optimal by the relevant }X\text{-evaluation}.
]

If "better informed" is defined so that the later agent cannot be wrong, the model is not suitable for FUD.

This is a **required nontriviality property**.

---

## 1.3 Execution cannot be quotiented away

Stage II located jurisdiction in the execution/capability layer.

Therefore a genuine comparator must retain the distinction among:

* proposals;
* authorization;
* executable realization;
* blocked/non-executed realization (\bot);
* protected/non-bypass structure.

A comparator over proposal values alone cannot establish a theorem about jurisdiction merely by interpretive gloss.

---

## 1.4 Competence remains a separate hurdle

Stage III showed that the value gap reduces to a delegation deficit against a later-measurable class.

Track I already established that choice/regret-level competence assumptions collapse into the desired conclusion.

Therefore do not solve comparator semantics and then quietly assume:

[
\text{continuing principal performs nearly as well as the later agent}.
]

The competence problem survives a successful comparator reconstruction.

---

# 2. Core Stage IV research question

Construct the smallest coherent model in which all of the following are simultaneously true:

1. (A_n) and (A_{g(n)}) are genuinely distinct epistemic states/processes.
2. (A_{g(n)}) may receive information unavailable at time (n).
3. (A_{g(n)}) may nevertheless be wrong.
4. (A_n) can evaluate the **policy of using (A_{g(n)})** without knowing the future realized recommendation/action.
5. The delegated and transferred arms receive comparable future evidence and cognitive resources.
6. Their final authorization source differs.
7. The execution layer, including (\bot), is live.
8. Jurisdiction/protection remains architectural rather than behaviorally inferred.
9. No competence assumption already contains the D-vs-FU conclusion.
10. No theorem follows merely because one arm is defined as a maximizer of the evaluation functional.

If this combination is impossible or incoherent, establish that sharply.

---

# 3. Required nontriviality witness before theorem search

Before attempting any general FUD theorem, construct a finite model witnessing:

[
\boxed{
\text{future epistemic improvement}
+
\text{future fallibility}
+
\text{present evaluability}.
}
]

The witness should contain at least:

* a finite world space (\Omega);
* present credence (P_n);
* later information/event or signal structure;
* a genuinely later decision process (A_{g(n)});
* an (X)-register over realizations;
* at least two proposals;
* at least one state/history where later information improves expected decision quality;
* at least one state/history where the later agent still chooses suboptimally relative to (X);
* a well-defined present-time value for the policy "use later (A)";
* no present-time computability collapse into the exact future action.

This witness is a **gate**.

If it cannot be built, stop and explain why.

Do not proceed to FUD theorem work by assumption.

---

# 4. Track A — future-agent semantics

Research candidate semantics for a genuinely later agent.

Possible families include, but are not limited to:

### A.1 Signal-conditioned later policy

Present (A_n) knows a stochastic policy/kernel:

[
K(\pi\mid s),
]

but does not know the future signal (s).

Later (A_{g(n)}) observes (s) and acts according to (K).

This is allowed only if (K) is not defined as the present evaluator's exact conditional argmax.

### A.2 Distinct later credence process

Let:

[
P_n
\quad\text{and}\quad
P_{g(n)}
]

be related by an explicit epistemic-update process, but do not assume (P_{g(n)}) is identical to the true conditional distribution or makes the later action infallible.

### A.3 Noisy / bounded later optimizer

The later agent may process richer evidence while remaining computationally bounded, approximate, stochastic, or otherwise fallible.

### A.4 LI-like time-indexed process

Investigate whether actual Logical Induction semantics naturally provides:

[
A_n \neq A_{g(n)}
]

in the needed sense.

If using LI/FAF machinery, work against actual pinned definitions and their admissibility/computability conditions.

Questions to answer:

1. What is known at (n)?
2. What becomes known only later?
3. What policy object can (A_n) price/evaluate now?
4. What remains genuinely unresolved at (n)?
5. Why can the later agent be epistemically improved yet fallible?
6. What prevents reduction to present contingent optimization?
7. Which pieces are ordinary probability theory and which genuinely require LI?

---

# 5. Track B — present evaluation of a future process

FUD requires the present agent to compare:

[
D_{n,g}
]

and:

[
FU_{n,g}
]

without already knowing the future action.

Formalize a present-time valuation of a **future decision procedure**, not a known action.

Candidate abstract form:

[
V_n(\mathcal P)
===============

E_{P_n}
\left[
X_{n,\operatorname{Exec}(\mathcal P,\omega)}
\right].
]

But do not assume this exact form is correct.

The crucial distinction is:

[
\boxed{
A_n\text{ knows the future decision rule/process}
\neq
A_n\text{ knows its eventual output}.
}
]

Audit carefully whether the policy is:

* extensional over future signals;
* computable now;
* merely described now;
* internally dependent on later computation;
* dependent on future market prices;
* dependent on information not measurable at (n).

A present policy description may be known without its later output being known.

Make this distinction explicit.

---

# 6. Track C — reinstate execution and jurisdiction

Stage IV must reintroduce the execution layer from the beginning.

Use the Stage II skeleton-v2 distinction between proposal and realization.

At minimum, make explicit:

[
\pi \in \Pi_n
]

versus:

[
r \in \Pi_n\sqcup{\bot}.
]

Specify:

* proposal generation;
* recommendation;
* authorization;
* execution;
* protection;
* (\bot);
* the authorization source.

The comparator should contain a parameter or object such as:

[
J_n
\in
{\text{principal},\text{future-A}}
]

or a repository-conformant equivalent.

Do not treat this symbol as moral legitimacy.

It means operational jurisdiction:

> which authorization source is constitutively required for the intervention to become executable.

Required property:

Two architectures may produce the exact same object-level action while differing in jurisdiction.

The formal model must preserve that distinction.

---

# 7. Track D — reconstruct the comparator pair

Only after Tracks A–C stabilize should you define candidate arms.

The intended conceptual structure is:

## Delegated cognition

At time (n), continuing principal jurisdiction is retained.

At (g(n)):

* future evidence is available;
* future (A) performs its later cognition;
* advice is transmitted through the specified interface;
* (H^+) authorizes;
* execution occurs through the protected interface.

Schematically:

[
D_{n,g}:
\quad
A_{g(n)}
\to
\text{advice}
\to
H^+
\to
\text{authorization}
\to
\text{execution}.
]

## Future-A jurisdiction

At time (n), the authorization source for the later decision is assigned to future (A_{g(n)}).

At (g(n)):

* the same future evidence is available;
* the same future-A cognitive process runs;
* (A_{g(n)}) directly supplies the operative authorization;
* execution occurs.

Schematically:

[
FU_{n,g}:
\quad
A_{g(n)}
\to
\text{authorization}
\to
\text{execution}.
]

The assignment at (n) is jurisdictional.

The object-level action remains later and contingent.

---

# 8. Comparator fairness audit

For every candidate pair, produce a table of variables held fixed versus variables changed.

At minimum inspect:

* world;
* menu;
* future external information;
* future-A computational resources;
* future-A decision process;
* advice content;
* advice bandwidth;
* human interpretation/use of advice;
* timing;
* value target;
* evaluator;
* authorization source;
* protection;
* execution outcome;
* (\bot) handling.

The intended experimental intervention is:

[
\boxed{
\text{change final authorization source while preserving future cognition as far as possible}.
}
]

If something else changes, state it explicitly.

Do not call the comparator "fair" merely because it has many symmetry predicates.

Each fairness predicate must have an actual operational interpretation and, where practical, a one-variable confound witness.

---

# 9. Information symmetry without lossless cognition

Do not require:

[
H^+
]

to reproduce the entire internal state of (A_{g(n)}).

That would risk trivializing the intended distinction.

Instead define an explicit advice interface:

[
m_{n,g}
=======

\operatorname{Advice}(A_{g(n)},s).
]

Possible interfaces to test:

* action recommendation;
* recommendation + value estimates;
* uncertainty estimates;
* reasons/proofs/certificates;
* bounded generic message.

The central question is:

> How much of the value of future cognition can be transmitted through advice without transferring final authorization?

Do not solve this by assuming a lossless interface.

Advice loss should become an explicit term, assumption, or obstruction.

---

# 10. Better-informed but fallible

This phrase must become mathematically explicit.

Do not leave it as philosophical prose.

Investigate candidate notions such as:

* Blackwell-more-informative signals combined with non-Bayes-optimal downstream choice;
* lower expected predictive loss without zero loss;
* improved calibration without perfect accuracy;
* refinement of information partitions without perfect decision rule;
* better expected (X)-performance over a reference class while retaining error probability;
* LI-specific improvement notion if available.

The notion must permit both:

[
\text{epistemic improvement}
]

and:

[
\text{mistake}.
]

Provide both positive and negative finite witnesses.

---

# 11. Competence remains fenced

Do not attempt to solve the full competence problem unless the comparator forces a specific tractable subproblem.

Any competence slot should apply to the **advised continuation**:

[
H^+(s,m_A).
]

Do not call an assumption "principal competence" if it materially includes:

* the evaluator's credence;
* future-A optimality;
* the D-vs-FU value gap;
* a direct comparison against later choice quality.

If the condition mixes grade and credence registers, label it honestly as a joint condition.

Track I's result remains active:

[
\boxed{
\text{choice-level near-optimality assumptions are not an explanation}.
}
]

If Stage IV reveals that a genuine comparator makes this obstruction even stronger, record that as a major result.

---

# 12. Separate comparator existence from positive FUD

This phase should maintain two different questions:

## Q1 — Comparator existence

Can we construct a genuine, fair, nontrivial D/FU pair?

## Q2 — Positive FUD

Under what non-circular assumptions, if any, is:

[
V_n(D_{n,g})
\ge
V_n(FU_{n,g})-\epsilon?
]

Stage IV is primarily about Q1.

Do not allow a positive answer to Q1 to be described as evidence that Q2 is true.

Likewise, a counterexample to Q2 does not automatically show Q1 is ill-posed.

---

# 13. Required anti-collapse tests

Every candidate comparator must pass explicit tests against at least these failure modes.

## Collapse 1 — present argmax

Can (A_n) compute the exact future action because the later policy is defined using only known present inputs?

If yes: reject.

## Collapse 2 — infallible conditionalization

Does "better informed" guarantee the later choice is conditionally optimal by definition?

If yes: reject as FUD model.

## Collapse 3 — proposal-only semantics

Has the execution/protection layer disappeared?

If yes: reject as jurisdiction comparator.

## Collapse 4 — menu asymmetry

Does one arm have access to proposals the other does not?

If yes: identify as agenda/information confound.

## Collapse 5 — competence conclusion smuggling

Does an antecedent already imply:

[
V(D)\approx V(FU)?
]

If yes: reject.

## Collapse 6 — unavailable FU

Is FU assigned value only after being architecturally removed from the counterfactual space?

If so, distinguish counterfactual evaluation from actual capability.

## Collapse 7 — advice identity

Is advice defined as the final executable authorization itself?

If yes, the arms may be extensionally/constitutionally collapsed.

## Collapse 8 — value drift

Does (A_{g(n)}) differ from (A_n) in evaluative target as well as epistemic state?

If yes, separate this from FUD or explain why it is essential.

---

# 14. Track E — cheap impossibility search

Run a dedicated adversarial search after a candidate future-agent semantics exists.

Ask:

> Is there any theorem stating that preserving jurisdiction loses little that does not merely restate a competence assumption?

Try to construct countermodels where:

* future (A) is modestly better informed;
* future (A) is fallible;
* advice is informative but lossy;
* principal retains genuine jurisdiction;
* all comparator fairness conditions hold;
* yet FU strongly beats D.

If such models exist, identify exactly what positive assumption excludes them.

The result may be:

[
\boxed{
\text{a fair comparator exists, but strong FUD is false without substantive competence}.
}
]

That would be a successful Stage IV result.

---

# 15. Track F — relation to Logical Induction

Once the finite semantics are clear, ask what LI genuinely contributes.

Possible contributions:

* time-indexed credences (A_t);
* calibration;
* self-measured uncertainty;
* market-computable policies;
* reflection/deference structure;
* admissible pricing of future-process value;
* faithful acceleration from (H) to (A).

Do not force LI relevance into a finite result that is really ordinary decision theory.

Conversely, where LI is claimed to do work, formalize against actual FAF machinery.

Explicitly distinguish:

[
\boxed{
\text{finite decision-theoretic comparator semantics}
}
]

from:

[
\boxed{
\text{LI theorem about an agent inhabiting that comparator}.
}
]

---

# 16. What not to do

Do not:

* dispatch a FUD proof swarm;
* rename an envelope theorem back into jurisdiction language;
* define future (A) by present conditional argmax;
* make future (A) infallible by definition;
* erase (\bot);
* erase execution/protection;
* assume lossless advice;
* use underwriting as the main positive engine;
* solve refusal;
* solve agenda sovereignty;
* solve arbitrary value drift;
* solve legitimacy;
* add unnecessary general architecture.

The phase should remain focused on:

[
\boxed{
\text{future-agent semantics}
+
\text{fair comparator reconstruction}.
}
]

---

# 17. Deliverable: `FUTURE_AGENT_SPEC`

Persist a versioned specification in the repository-conformant location.

It should answer:

1. What is (A_n)?
2. What is (A_{g(n)})?
3. What changes between them?
4. What does not change?
5. What is known at (n)?
6. What is revealed later?
7. What makes the later process better informed?
8. What makes it still fallible?
9. What future process does (A_n) evaluate?
10. Why can (A_n) value it without knowing its eventual action?
11. What is the advice interface?
12. What is (H^+)?
13. What is the proposal space?
14. What is the realization space?
15. What is (\bot)?
16. What is the jurisdiction assignment?
17. What is protected?
18. What is the delegated arm?
19. What is the transferred arm?
20. What exactly differs between the arms?

The last question is mandatory.

---

# 18. Deliverable: nontriviality harness

Create a small finite harness or equivalent checked artifact demonstrating that the candidate semantics permits:

[
\text{later information improvement}
]

without:

[
\text{later infallibility}.
]

The harness should include at least:

* one case where later information helps;
* one case where later (A) still makes an error;
* one case where present (A_n) cannot know the realized future action;
* both jurisdiction assignments;
* live execution semantics including (\bot) where applicable.

Prefer exhaustive finite checking if cheap.

Do not promote a general theorem merely because the witness works.

---

# 19. Deliverable: comparator audit

Persist a concise audit answering:

> Has the FUD comparator finally been constructed?

Possible verdicts:

* **yes, nontrivial and fair enough for theorem research;**
* **yes, but with one named confound;**
* **semantically coherent but competence dominates the remaining problem;**
* **future-agent model still collapses;**
* **jurisdiction cannot yet be isolated;**
* **intended comparator is impossible under current architecture.**

Use the strongest honest verdict.

---

# 20. Research debt update

Reclassify the project debt after the phase.

At minimum assess:

* model debt;
* interface debt;
* assumption debt;
* theorem debt;
* formalization debt;
* interpretation debt;
* scope debt;
* compression debt.

A key question is whether Stage IV converts:

[
\text{model debt}
]

into:

[
\text{assumption/theorem debt}.
]

If not, say why.

---

# 21. Aspirational vs constructed update

For the deference/corrigibility project, explicitly state:

## Aspirational mathematical claim

What FUD would ideally prove.

## Constructed mathematical state

What objects/theorems actually exist after Stage IV.

## Mathematical gap

What remains.

## Aspirational philosophical gloss

For example:

> future cognitive superiority need not justify transfer of final jurisdiction.

## Constructed philosophical gloss

State only what the current mathematics actually supports.

Do not let a successful comparator construction inherit the full aspirational philosophical gloss automatically.

---

# 22. Formalization

Formalize stabilized finite results where doing so materially improves confidence.

Do not formalize speculative interfaces merely to increase theorem counts.

Any promoted result must have:

* non-vacuity witness where required by repository policy;
* correct assumptions;
* honest theorem/docstring correspondence;
* no hidden float/numerical approximation issues;
* permitted axioms only;
* normal build inclusion.

If an interpretation changes, rename the theorem/namespace rather than retaining misleading terminology.

Stage III's `EnvelopeDominance` correction is the model.

---

# 23. Independent red team

Before closure, give the candidate comparator specification and artifacts to an independent adversarial agent with no access to the constructing agent's chain of reasoning.

Ask it specifically:

1. Where is the future agent?
2. Can the present agent compute its realized action already?
3. Can the future agent be wrong?
4. Where does jurisdiction enter mathematically?
5. Is (\bot) live?
6. What variables differ between D and FU?
7. Is any fairness condition vacuous?
8. Is any competence condition the conclusion in disguise?
9. Does any theorem's docstring claim more than its hypotheses/conclusion?
10. What is the cheapest countermodel?

Do not repair the red-team output silently.

Record material failures.

If the comparator fails again, that is the Stage IV result.

---

# 24. Stop conditions

Stop rather than forcing a positive construction if:

* every candidate future agent collapses to present contingent optimization;
* "better informed" cannot be made compatible with fallibility;
* present evaluation of a genuinely later process is incoherent in the chosen framework;
* the execution layer makes the comparator ill-typed;
* advice symmetry requires lossless cognition;
* the only positive FUD result uses a competence assumption equivalent to the conclusion;
* the only value difference arises from agenda asymmetry;
* future-A evaluation requires value drift;
* LI machinery cannot represent the needed future process without future leakage;
* the red team finds a conceptual collapse with no cheap repair.

A sharp negative result is preferable to another falsely labelled positive theorem.

---

# 25. Parent report

Produce a Stage IV parent report answering:

1. Did we construct a genuine future agent?
2. In what precise sense is it later?
3. In what precise sense is it better informed?
4. Can it be wrong?
5. Can (A_n) evaluate the future process without knowing its action?
6. Is the execution layer live?
7. Is (\bot) live?
8. How is jurisdiction represented?
9. What exactly differs between D and FU?
10. Is future cognition held fixed across arms?
11. Is advice loss explicit?
12. Does the comparator pass the anti-collapse tests?
13. What did the independent red team find?
14. What competence debt remains?
15. Does Track I's collapse still apply?
16. What, if anything, does LI contribute yet?
17. Is underwriting absent from the main engine?
18. Is FUD now ready for theorem research?
19. If not, what single obstruction controls the next phase?
20. What should the paper claim after Stage IV?

Include:

## Does the FUD program survive Stage IV?

Allowed verdicts include:

* comparator constructed; proof research ready;
* comparator constructed; competence is now the controlling obstruction;
* only a weaker FUD survives;
* comparator still not coherent;
* strong FUD false in the fair model;
* research direction should be reframed.

---

# 26. PR endpoint

If Stage IV reaches a coherent research-state endpoint:

* commit the phase;
* push the branch;
* open a research-state PR for maintainer review.

A negative result is PR-worthy.

The PR description must distinguish:

* newly constructed semantics;
* finite witnesses;
* formal theorems;
* negative results;
* architectural assumptions;
* open competence assumptions;
* unresolved research debt;
* aspirational claims not yet established.

Do not merge.

Do not describe the comparator as successful unless the independent red team agrees that it contains:

[
\boxed{
\text{a genuinely later, better-informed, fallible process}
}
]

and:

[
\boxed{
\text{a live execution-level jurisdiction difference}.
}
]

---

# 27. Final maintainer memo

End with a compact memo:

1. What future-agent object did you construct?
2. Why is it not the Stage III envelope construction?
3. Can it be better informed and wrong?
4. How does present (A_n) evaluate it?
5. Where does jurisdiction enter?
6. What role does (\bot) play?
7. Is the comparator now fair?
8. What is still confounded?
9. What competence assumption remains?
10. Does Track I threaten the positive theorem?
11. What did the red team attack successfully?
12. Is FUD ready for a proof phase?
13. If yes, state the theorem target.
14. If no, state the controlling obstruction.
15. What changed in the aspirational/constructed research state?
16. PR URL and human review surfaces.

The central discipline for this phase is:

[
\boxed{
\text{do not prove a theorem about a future agent until there is actually a future agent in the model.}
}
]

And the desired object is one where:

[
\boxed{
\text{future cognition can improve without becoming infallible,}
}
]

while:

[
\boxed{
\text{the marginal effect of changing final jurisdiction remains separately representable.}
}
]

Only after that exists should the project attempt the crown-jewel FUD theorem.

**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
