Here’s the prompt I’d send. I’ve written it to make the agent **consolidate aggressively but claim conservatively**: the conceptual architecture should become legible and durable in the wiki, while every mathematical addition to the repo has to survive prosecution before being presented as a result.

---

# Prompt: consolidate the afoundational normative-learning / inquiry architecture

Work in the live `A-M-Berns/alignment-workspace` repository. This is a substantial research/consolidation task. **End in a PR.**

The goal is to consolidate the current normativity/legitimacy architecture, especially the newly developed **left side of the pipeline**—afoundational initialization, empirical interaction, normative-record dynamics, inquiry generation, bounded question selection, coverage, and answerability—and to connect it cleanly to the existing answerability kernel and downstream normative-realization pipeline.

There are two distinct deliverables:

1. **Conceptual consolidation in the GitHub wiki.** The wiki should contain the human-facing conceptual architecture, philosophical interpretation, diagrams, literature orientation, and relationship among the pieces.
2. **Mathematical integration in the repository.** Create a new research round that formalizes and adversarially tests the candidate interfaces and results. Do **not** register, advertise, or silently treat conjectural mathematics as established without verification.

Do not merely summarize existing artifacts. The purpose is to test whether the ideas below form a coherent formal interface, repair them when they do not, and leave the workspace in a better organized research state.

## 0. Start by orienting against the live workspace

Before changing anything, inspect the current repository and wiki. In particular locate and read the current versions of the relevant artifacts, including at minimum:

* `projects/normativity/legitimacy/README.md`
* the legitimacy architecture round
* the procedural-legitimacy round
* `rounds/2026-08-21-internal-answerability/`, especially `MEMO.md`
* `rounds/2026-08-22-role-parametric-answerability/`, especially `MEMO.md`
* relevant relational-scorekeeping / diachronic-identity artifacts
* relevant counterfactual-legitimacy interfaces
* the current normativity/traderized-enforcement semantics and force interfaces
* anything describing the open `R -> O -> C -> K -> E` pipeline
* current `PRIORITIES.md` / structured state / theorem registries
* the current Legitimacy wiki page and neighboring normativity pages

Treat the live workspace as authoritative over path/name assumptions in this prompt.

Preserve the existing repository/wiki division: **dry technical facts, artifacts, tests, theorem status, and research rounds belong in the repo; conceptual interpretation, philosophical narrative, alignment relevance, and high-level architecture belong primarily in the wiki.** Do not gratuitously rewrite unrelated existing repo prose.

The current internal-answerability work already appears to have isolated a small record-internal kernel involving immutable undertaken certificates, proof-relevant liability/account lineage, semantic transport, and basis-loss review. **Build around that kernel rather than replacing it with a parallel theory.**

---

# 1. Core architecture to investigate

The candidate architecture is no longer a simple linear

[
\text{normative environment}\to R_n.
]

The strongest current picture is:

### One-time initialization

[
\boxed{
S_0
\xrightarrow{\text{pre-licensed induction}}
R_0
}
]

where (S_0) is a small **afoundational seed**: an initial induction into a normative practice.

The seed is the one place where the formalism is allowed to receive normativity without an internal prior justification. But seed contents are **not immutable foundations or eternal truths**. They are initially pre-licensed and thereafter revisable through the same normative practice.

The intended distinction is:

[
S_0 \not\models R_n
]

in general. Instead we want something like

[
S_0\leadsto_{\mathrm{answerable}}R_n.
]

The invariant should concern **genealogical continuity of normative authority/accountability, not preservation of substantive content**.

After initialization, no fresh ungrounded normative roots should simply appear.

### Recurrent learning/inquiry loop

The left side should be approximately:

[
\boxed{
(R_n,L_n)
\xrightarrow{\text{inquiry}}
\mathcal W
\xrightarrow{\text{receipts}}
L_{n+1}
\xrightarrow[;R_n;]{\text{reasoned uptake}}
R_{n+1}.
}
]

Here:

* (\mathcal W) is an ordinary interactive world/environment, kept as normatively thin as possible.
* (L_n) is a monotone empirical/logical ledger: roughly logic plus eternalized interaction history.
* (R_n) is the auditable, evolving normative practice.

The world should provide things such as actions, utterances, measurements, testimony, consequences, query responses, etc. Avoid building predicates such as “really normatively relevant,” “really due,” or “true authority” into the preferred positive model.

For example, (L_n) may permanently record something like

[
\mathsf{Received}(o,n)
]

or

[
\mathsf{Did}(a,n),
]

while an interpretation such as

[
\mathsf{Interprets}(o,\phi)
]

belongs to the normative/reason machinery in (R) and may later be defeated or revised.

Then the right side remains approximately:

[
\boxed{
R_n
\xrightarrow{\text{authorization}}
O_n
\xrightarrow{\text{credal interpretation}}
C_n
\xrightarrow{\text{price realization}}
K_n
\xrightarrow{\text{traderization}}
E_n.
}
]

So the overall architecture is:

[
\boxed{
\text{afoundational learning loop}
\quad\longrightarrow\quad
\text{normative realization/compiler pipeline}.
}
]

Test this architecture rather than merely installing it.

---

# 2. Avoid quietly reintroducing normative realism

A previous approach used an external structure containing facts like

[
\mathsf{Due}^{*}(h)
]

for the demands that “really” deserve confrontation. That is useful as an **external evaluator/test fixture** for separation results, but it risks baking a time-indexed oracle of true normative facts into the positive theory.

The preferred positive architecture should instead derive inquiry responsibilities from the **currently inherited normative practice**.

Do not delete old starred/evaluator machinery if existing impossibility, sufficiency, or separation results use it. Instead clarify the distinction:

* external normative evaluator as a **meta-theoretic benchmark/test harness**;
* seed-descended internal practice as the preferred **positive model of legitimacy/normative learning**.

The project is explicitly afoundationalist. We are allowed to “spend” a small amount of primitive normativity in (S_0), but should be extremely careful not to replenish it invisibly later.

---

# 3. Candidate type theory for the normative record

Aggressively test whether the existing answerability kernel can be extended using a **small narrow waist**.

A promising compression is that many apparent types may be species of one common identity-bearing normative object.

Consider something like:

```text
Commitment
  Hold(Judgment)
  Do(Task)
```

Examples of `Hold` contents:

* interpretation of a receipt;
* applicability of a warrant;
* standing relation;
* activation of a rule;
* authorization of some effect.

Examples of `Do` contents:

* consider an issue;
* investigate a question;
* review an old commitment;
* respond;
* maintain some substantive normative constraint.

Under this proposal:

* an **issue** is a commitment to consider something;
* an **inquiry task** is a commitment to investigate;
* a **review debt** is a commitment to review;
* ordinary identity-bearing normative liabilities are other commitments with corresponding contents.

Test whether this collapse is actually sufficient. If counterexamples require separate primitive types, preserve the distinction and explain exactly why.

A candidate minimal append-only event language is something like:

```text
Root(c)
Undertake(c, certificate)
Account(parents, disposition, successors, certificate)
```

Do not assume these constructors are sufficient. Prosecute them.

The intended principle is:

> (R_n) is primarily an immutable history of normative acts; the mutable-looking “current normative state” is a derived view.

So try to distinguish:

[
R_n=\text{append-only historical record}
]

from

[
V_n=\operatorname{View}(R_n,L_n),
]

where current standing, live commitments, open issues, active rules, etc. are derived.

Integrate this with the existing internal-answerability representation instead of inventing a wholly new ledger if the current kernel already has the needed objects.

---

# 4. Separate grounds, normative license, and account lineage

One of the strongest candidate refinements is that a normative move has several different proof-relevant relationships that must not be conflated.

For a normative act (e), investigate a certificate/interface containing conceptually distinct roles such as:

[
\boxed{
\text{grounds}
\qquad
\text{licenses / authority}
\qquad
\text{account incidence / lineage}.
}
]

### Grounds

Answer:

> Why this content?

These may include empirical receipts from (L) and prior normative judgments.

### Normative licenses

Answer:

> What entitled the practice to make a normative move of this kind?

These should trace through standing normative authority already in the practice.

The intended anti-Humean / anti-realist discipline is:

[
\boxed{
\text{empirical receipts may ground normative moves,
but do not themselves create normative authority.}
}
]

### Account incidence

Answers:

> Which previous identity-bearing commitments is this act accounting for?

This is the existing diachronic-answerability/account structure: split, merge, succession, closure, suspension, etc. must remain proof-relevant.

Determine whether the existing certificate/dependency interface already supports these distinctions, and extend it minimally if necessary.

---

# 5. Afoundational authority genealogy

Formalize and attack a candidate **No New Normative Roots** property.

Only seed initialization may introduce a normatively authoritative root without an incoming normative-license ancestry.

After initialization, authority edges should point backward in the historical record.

Candidate theorem shape:

> For every post-seed normative act admitted by the transition system, every maximal backward path through its normative-authorization ancestry terminates in a seed occurrence.

Be extremely careful about what this establishes.

It should **not** establish:

[
S_0\models \text{current substantive norm}.
]

The substantive grounds for a current commitment may be overwhelmingly empirical and may have changed completely since initialization.

The intended interpretation is closer to:

> the current act belongs to the same evolving normative practice because its authority to enter the practice has an accountable genealogy.

Check for circularity, self-licensing, mutual instantaneous licensing, checker-level hidden authority, and rule-version loopholes.

In particular, preserve the existing pre-state checking discipline: a move should not install the very authority that licenses itself.

Also examine what belongs in the fixed checker. The fixed kernel should ideally enforce the **grammar of authority/accountability**, not contain hidden substantive norms. If the checker itself contains substantive normative facts, identify this explicitly as an additional primitive normative expenditure.

---

# 6. First-class normative rules: `May` and `Must`

Test a rule interface with at least two modes:

[
\boxed{
\mathsf{May}
\quad\text{and}\quad
\mathsf{Must}.
}
]

A `May` rule licenses some normative act when its conditions hold.

A `Must` rule generates an owed commitment/task when its trigger holds.

The rule's executable/code-like content can be an ordinary finite object, while **its authority to operate** comes from a standing commitment in (R).

This may organize several previously separate notions:

* reasons-responsiveness / licensing mainly concerns `May`;
* coverage / inquiry-generation mainly concerns `Must`;
* both rule families are themselves normatively revisable objects in (R).

Rules need to be boundedly usable. Avoid defining coverage as closure under every semantic implication of an open-ended normative theory, thereby silently demanding logical omniscience.

Look for a minimal finite trigger/checking interface.

---

# 7. Due tokens and event-time accrual

A particularly promising anti-evasion mechanism is to distinguish a historically generated **due token** from the rule that generated it.

Suppose rule (r) stands immediately before event (z), and its trigger fires. Let the event generate something like

[
\delta=(r,z,\tau),
]

where (\tau) is the required task/commitment.

This is not “the objectively true demand.” It means:

> the normative practice actually standing at the time of event (z) generated this requirement.

Prosecute the candidate principle:

[
\boxed{
\textbf{Event-time accrual: }
normative demands accrue under the practice standing when their trigger occurs.
}
]

Once (\delta) exists historically, later repeal or modification of (r) should not rewrite the past so that (\delta) never existed.

A later rule change may affect future triggers. Existing due tokens / docketed obligations must instead receive an ordinary explicit account.

Try to prove a **No Retroactive Evasion** result under minimal hypotheses.

Test edge cases:

* rule is revised immediately before the trigger;
* trigger occurs while rule stands but bounded processor has not yet docketed it;
* trigger and repeal occur “in the same step”;
* rule interpretation itself changes;
* delayed empirical recognition of an earlier-world event;
* new evidence changes whether the old trigger was believed to hold;
* mistake discovered in the original interpretation;
* explicit retroactivity is itself authorized by the practice;
* settlement/incorrigible events versus defeasible normative acts.

Do not bake the desired answer in. The temporal semantics here may require repair.

---

# 8. Inquiry liabilities and coverage

Test whether inquiry obligations can reuse the existing identity-bearing liability/account calculus.

The candidate picture:

[
\mathsf{InquiryDue}(\tau)
\quad\Rightarrow\quad
\ell_\tau:\mathsf{Do}(\tau).
]

Then inquiry tasks are not a parallel ontology; they are a typed species of liability.

This would let existing machinery handle:

* stable identity;
* split/merge;
* delegation;
* suspension;
* explicit release/cancellation;
* basis-loss review;
* successor obligations;
* terminal dispositions;
* no silent disappearance.

However, inquiry introduces liveness/resource questions beyond ordinary account conservation. Distinguish at least the following notions.

### Docket coverage

Every due token generated by the standing practice becomes an actual identity-bearing commitment, or a visible coverage violation/debt remains.

Schematic:

[
\delta\in D_n
\Rightarrow
\exists m\le n+s(\delta),\ell:
\operatorname{Origin}(\ell)=\delta.
]

Do not assume a bounded deadline exists universally; test bounded and eventual formulations separately.

### Service coverage

A live inquiry liability should not be starved indefinitely when it is persistently feasible/serviceable, unless the practice explicitly permits another terminal disposition.

Schematic:

[
\mathsf{Live}_n(\ell)
\land
\mathsf{PersistentlyServiceable}(\ell)
\Rightarrow
\Diamond\mathsf{Serviced}(\ell).
]

This needs explicit resource/load assumptions for a bounded reasoner.

### Service certification

Do not count an inquiry liability as adequately serviced merely because it happened, from an external God's-eye perspective, to obtain enough information.

Explore a proof-relevant condition:

[
\mathsf{Serviced}*n(\ell)
\iff
\exists p:
p\vdash*{\sigma_\ell}
\mathsf{AdequatelyInvestigated}(\ell).
]

Here (\sigma_\ell) is the **versioned service specification** that says what counts as satisfying this inquiry liability.

Changing (\sigma_\ell) should itself be an explicit normative move; the process must not redefine adequacy retrospectively so that an inconvenient old task becomes automatically discharged.

This idea is strongly suggested by Golovin–Krause's notion of adaptive coverage/self-certification: in their model, actual target achievement alone is not enough for termination; the observations must certify coverage across all realizations still consistent with the history.

Determine which of these notions can be defined entirely record-internally and which require an external environment/model assumption.

---

# 9. Quantitative service semantics and bounded question selection

Do not make optimal question selection part of the legitimacy definition.

Separate:

[
\boxed{
\text{what inquiry is owed}
}
]

from

[
\boxed{
\text{how a bounded reasoner allocates scarce inquiry resources}.
}
]

The normative record generates a live docket. A downstream scheduler consumes a finite **inquiry-state snapshot**.

Explore an interface approximately like:

[
\mathcal I_n
============

(A_n,\Sigma_n,F_n,D_n,C_n,\ldots)
]

where for each live inquiry liability (\ell):

* (\sigma_\ell): versioned service specification;
* (f_\ell): progress/service function;
* (d_\ell): delay/urgency/answerability-charge semantics;
* perhaps priority/weight if not already encoded in (d_\ell).

An inquiry action (q) has some resource cost and may affect multiple liabilities.

A promising quantitative representation is

[
f_\ell(\psi)\in[0,1],
]

where (1-f_\ell(\psi)) is residual inquiry/answerability debt and (f_\ell=1) indicates complete service, subject to certification.

This allows partial investigation to count without conflating partial progress with discharge.

---

# 10. Verify exact bridges to existing bounded-inquiry mathematics

Do literature-backed mathematical work here. Do not merely write analogies.

At minimum investigate these papers closely:

1. Yossi Azar, Ashish Chiplunkar, Shay Kutten, Noam Touitou, **“Set Cover with Delay – Clairvoyance is not Required.”**
2. Daniel Golovin and Andreas Krause, **“Adaptive Submodularity: Theory and Applications in Active Learning and Stochastic Optimization.”**
3. Sungjin Im, Viswanath Nagarajan, Ruben van der Zwaan, **“Minimum Latency Submodular Cover.”**
4. Andrew Guillory and Jeff Bilmes, **“Interactive Submodular Set Cover.”**
5. Follow references only where they materially bear on the interface.

Use primary papers.

Try to establish precise special-case embeddings.

## Candidate bridge A: Set Cover with Delay

Can a finite dynamic inquiry instance with:

* arriving inquiry liabilities;
* deterministic overlapping inquiry actions;
* action costs;
* liability delay functions;

compile exactly into SCD?

If yes, state and verify an actual translation preserving the objective.

Be attentive to the fact that SCD can permit requests to remain permanently unserved if the terminal delay is finite; eventual service only follows under suitable divergent/infinite-delay or other conditions.

A useful candidate corollary is:

> competitive servicing + a serviceable persistent liability with divergent delay penalty prevents permanent starvation.

Prove only with the exact assumptions needed.

## Candidate bridge B: submodular ranking / MLSC

Can a fixed docket with deterministic partial progress functions

[
f_1,\ldots,f_m
]

compile into submodular ranking / minimum-latency submodular cover?

The key idea is that individual inquiry liabilities naturally correspond to **multiple service objectives**, not necessarily one global coverage function.

If switching/context costs are present, MLSC's metric structure may be relevant.

Again: exact translation where possible; explicit mismatch where not.

## Candidate bridge C: adaptive stochastic inquiry

Investigate when uncertain query outcomes plus service functions fit Golovin–Krause adaptive stochastic min-cost or min-sum coverage.

Do **not** make adaptive submodularity an axiom of legitimate inquiry.

Treat it as a tractable special class. The paper itself emphasizes that adaptive submodularity is a diminishing-returns condition and fails in the presence of important conditional synergies or when actions alter the underlying realization.

If the bridge requires:

* a fixed realization space;
* a known Bayesian prior;
* immutable service objectives;
* monotonicity/submodularity assumptions;

say so prominently.

Also inspect Guillory–Bilmes because its worst-case interactive query/response setting may provide a more suitable non-Bayesian scheduler class.

---

# 11. Resource feasibility and boundedness

Coverage cannot simply demand that every generated task be serviced within a fixed time if demands can arrive faster than a bounded reasoner can process them.

Make resource assumptions explicit.

Explore distinctions such as:

* merely live;
* feasible at some time;
* continuously/persistently serviceable;
* globally feasible under the scheduler's capacity;
* overload cases where no policy can meet all service commitments.

Possible theorem shapes include conditional liveness:

[
\mathsf{PersistentLive}(\ell)
\land
\mathsf{PersistentServiceable}(\ell)
\Rightarrow
\Diamond\mathsf{ServiceOrAuthorizedDisposition}(\ell),
]

or competitive/online performance relative to a feasible comparator.

Do not hide infeasible load behind “coverage.”

---

# 12. Basis loss and inquiry review

Integrate inquiry with the existing undertaken-basis / review machinery.

A past normative act that was valid when undertaken should not become retroactively nonexistent when its basis is later undercut.

Instead test rules of the form

[
\mathsf{BasisUndercut}(c)
\rightsquigarrow_{\mathsf{Must}}
\mathsf{Review}(c).
]

Whether the original commitment remains active, becomes suspended, etc. during review should be a substantive revisable rule of the practice, not hardcoded unless the existing kernel forces it.

Likewise, a different currently available proof should not erase the historical fact that the undertaken basis was lost; it may instead provide an easy way to discharge the review debt.

Preserve existing distinctions around settlement/incorrigible historical facts.

---

# 13. Relation to actual-run and counterfactual legitimacy

Keep this pass focused on the actual-run/process architecture.

A plausible high-level decomposition remains:

[
\boxed{
\text{Legitimacy}
\approx
\text{actual-run/process legitimacy}
+
\text{counterfactual non-capture/corrective-control properties}.
}
]

This pass should make the first term more precise.

Do not claim that impeccable internal genealogy, inquiry, and answerability prove non-manipulation. The existing counterfactual-legitimacy work should remain a separate hyperproperty over coupled runs.

In the wiki, explain the failure mode:

> A process can follow every internal rule, docket every generated obligation, and maintain flawless accounts while another agent has strategically shaped the evolution of the rules themselves.

That is why counterfactual legitimacy is still needed.

Do not attempt to solve the entire counterfactual side in this round.

---

# 14. Relation to the downstream normative compiler

Keep the right side visible:

[
R_n
\to
O_n
\to
C_n
\to
K_n
\to
E_n.
]

The new left-side work should clarify what kind of `NormativeRecord` is handed to (R\to O).

Do not silently solve the open normative-record-to-operative/credal compiler unless you actually do.

A likely interface remains that the current view of (R_n) determines which liabilities are standing/applicable/authorized to exert a particular type of force. Then only the typed credal-bearing fragment proceeds downstream.

Explicitly mark the `R -> O` compiler as open if it remains open.

---

# 15. Wiki deliverables

Update the wiki substantially.

At minimum, create or substantially revise a page along the lines of:

**Normative Record and Inquiry**

Use whatever wiki naming scheme fits the live wiki.

This page should be human-readable and should explain:

* the afoundational seed;
* why the external world is normatively thin;
* (L_n) as immutable empirical/interaction transcript;
* (R_n) as the evolving auditable normative practice;
* genealogical authority rather than foundational derivability;
* grounds vs normative licenses vs account lineage;
* commitment/liability narrow waist;
* May/Must rules;
* due tokens and event-time accrual;
* docket coverage vs service coverage vs service certification;
* bounded inquiry as a downstream scheduling problem;
* how Set Cover with Delay, submodular ranking/MLSC, adaptive submodularity, and interactive submodular cover relate;
* why adaptive submodularity is only a tractability condition;
* relation to actual-run legitimacy and counterfactual legitimacy;
* relationship to the downstream (R\to O\to C\to K\to E) compiler;
* important open questions.

Use the **self-amending court with an immutable transcript** analogy if it still survives scrutiny:

* (S_0): initial charter/induction;
* (L): permanent court reporter / transcript;
* (R): evolving rules, commitments, cases, reasons, and accounts;
* May-rules: what the court is empowered to do;
* Must-rules: what cases/tasks the court incurs;
* due token: a case incurred while the relevant rule stood;
* amendment cannot simply erase already incurred cases;
* service must leave an auditable record.

Be careful not to imply that the seed is normatively true or metaphysically privileged. It is simply the one pre-licensed starting point allowed by the model.

Update the main Legitimacy wiki page to situate and link this architecture without duplicating the whole page.

Add literature references with short explanations of exactly what is borrowed and what is not.

---

# 16. Repo deliverables

Create a new research round under the legitimacy project with an appropriate date/name, e.g. conceptually:

```text
rounds/2026-08-23-afoundational-inquiry/
```

but follow existing naming conventions.

The round should contain, as appropriate:

* `README.md`
* `MEMO.md`
* executable finite witnesses / model code
* adversarial tests
* `PROVENANCE.md`
* perhaps a `THEOREM_MAP.md` or interface file if consistent with neighboring rounds

The round should state a verdict, not just exposition.

Possible verdicts include:

* candidate kernel survives;
* survives after repairs;
* partial unification;
* May/Must abstraction fails;
* due-token semantics needs stronger temporal structure;
* etc.

Tests should attack the actual proposed invariants.

Suggested adversarial witnesses include:

* post-seed unlicensed normative root;
* self-licensing rule installation;
* two rules mutually licensing each other in one transition;
* empirical receipt illicitly treated as normative authority;
* rule repeal used to erase an already generated due token;
* trigger/repeal same-step ordering ambiguity;
* service criterion rewritten to fake discharge;
* inquiry obligation dropped without account edge;
* two identical-content inquiry obligations improperly contracted;
* merged investigation used to discharge two obligations without two adequacy/account edges;
* basis loss hidden by an unrecorded alternate proof;
* overloaded docket where naive coverage is impossible;
* submodular scheduler assumptions violated by complementarity;
* adaptive-scheduler bridge attempting to use mutable service semantics;
* old external evaluator and new internal generation disagree, demonstrating they are distinct notions rather than interchangeable definitions.

Reuse and extend existing kernels/tests when possible.

---

# 17. Theorems / propositions to prosecute

Do not assume these are true. Try to prove, falsify, or repair them.

### A. No New Normative Roots

Every admitted post-seed normative act has finite authorization ancestry terminating in seed roots.

### B. No Retroactive Evasion

A due token generated under the then-standing practice cannot disappear merely because its generating rule is subsequently revised.

### C. Docket Completeness

Under clearly stated processor/fairness assumptions, generated due tokens acquire identity-bearing liabilities or remain explicit unresolved coverage debts.

### D. No Forgotten Inquiry

An incurred inquiry liability always retains an ancestry-linked live/suspended frontier or explicit terminal account.

Determine how much follows directly from the existing No Forgotten Liability machinery.

### E. Service-Specification Integrity

An inquiry liability's service criterion cannot silently change. Revision requires an explicit licensed/accountable transition.

### F. Certified Service

Discharge requires a certificate against the applicable version of the service specification.

### G. SCD Embedding

Identify a precise restricted inquiry model that is isomorphic/reducible to Set Cover with Delay and prove objective preservation.

### H. Coverage-from-competitive-service

Under an appropriate divergent-delay / feasible-service hypothesis, derive eventual service from a finite competitive bound.

### I. Submodular-docket embedding

Identify a restricted fixed-docket model corresponding to submodular ranking / MLSC or explicitly establish why the mapping fails.

### J. Afoundational provenance/conservation

Clarify the strongest theorem actually supported by the authority graph. It should concern ancestry/authorization and not falsely imply substantive correctness or justification by the seed.

For every result, report:

* exact statement;
* hypotheses;
* proof status;
* smallest counterexample if false;
* repaired statement if possible;
* whether Lean/formal registration is warranted now.

---

# 18. Do not overclaim

Especially do not conflate any of the following:

* authorization ancestry with normative truth;
* genealogy with philosophical justification;
* empirical grounds with normative authority;
* current support with historical validity;
* docketing with servicing;
* servicing with certified discharge;
* internal legitimacy with non-manipulation;
* competitive scheduling with normative adequacy;
* adaptive submodularity with legitimate inquiry;
* external evaluator-relative adequacy with the preferred afoundational positive definition;
* account conservation with normative progress;
* actual-run legitimacy with corrigibility.

If a distinction turns out not to survive formal scrutiny, say so and explain.

---

# 19. Status map

Leave a compact status map somewhere appropriate, covering at least:

| Component                            | Status                             |
| ------------------------------------ | ---------------------------------- |
| afoundational seed semantics         |                                    |
| no-new-root property                 |                                    |
| (L_n) empirical transcript           |                                    |
| minimal `NormativeRecord` event type |                                    |
| grounds/license/account separation   |                                    |
| commitment/liability narrow waist    |                                    |
| May/Must rule interface              |                                    |
| due-token semantics                  |                                    |
| event-time accrual                   |                                    |
| docket coverage                      |                                    |
| service coverage                     |                                    |
| service certification                |                                    |
| versioned service specifications     |                                    |
| Set Cover with Delay bridge          |                                    |
| submodular ranking / MLSC bridge     |                                    |
| adaptive stochastic inquiry          |                                    |
| external evaluator role              |                                    |
| counterfactual non-capture           | out of scope / separate            |
| (R\to O) compiler                    |                                    |
| downstream (O\to C\to K\to E)        | existing / unchanged unless needed |

Use status labels consistent with the workspace: proved, finite witness only, single derivation, conjecture, interface, false, repaired, unregistered, registered, etc.

---

# 20. PR requirements

Work on a dedicated branch.

Before opening the PR:

* run all relevant existing tests;
* run new tests;
* ensure no existing registered claims were silently changed;
* inspect diff for accidental conceptual rewrites;
* verify links among repo and wiki pages;
* verify literature claims against primary sources;
* distinguish clearly between theorem, finite witness, proposed definition, and philosophical interpretation.

The PR description should explain:

1. the new architecture;
2. what was actually verified;
3. what failed or required repair;
4. which pieces remain conceptual/wiki-only;
5. how the new round relates to the existing internal-answerability and role-parametric kernels;
6. what changed about the status of “coverage” and external normative evaluators;
7. the most important next research questions.

**End by opening the PR. Do not merge it.**

The standard is not “make these ideas look coherent.” The standard is:

> **Find the smallest afoundational, proof-relevant inquiry/answerability interface that survives adversarial scrutiny; put the conceptual picture in the wiki, put only verified mathematical structure in the repo, and leave every remaining uncertainty visible.**
