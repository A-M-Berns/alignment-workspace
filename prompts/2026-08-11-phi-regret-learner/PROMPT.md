# Alignment Workspace Research Prompt — Item 30: Construct the Lawful Φ-Regret Learner

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
**Target repository:** `A-M-Berns/alignment-workspace`
**Date:** 2026-08-11

## Mission

Execute `PRIORITIES.md` item 30.

The theorem-interface question is no longer open. PR #20 repairs the two defects found by the item-29 audit:

1. theorem-facing actions now form a fixed eight-element semantic alphabet rather than a horizon-growing set of occasion-indexed repository responses; and
2. the comparator class is now nine fixed declarative lawful programs interpreted through a restricted public reason context rather than arbitrary Python callbacks capable of capturing profitability information.

Within the frozen environment, Blum–Mansour (2007), Theorem 18 therefore applies with

[
N=8,\qquad M=1,\qquad K=9,
]

yielding a horizon-tuned learner with expected mixed-action charge regret

[
O!\left(\ell_{\max}\sqrt{8T\log 9}\right).
]

Do **not** spend this round re-auditing whether Φ-regret is conceptually applicable. Item 29 has already answered that question positively within the frozen boundary.

The task now is to **construct the learner that the theorem calls for, run it on the repository-native lawful-edit environment, and determine whether it can satisfy the learning guarantee while remaining answerable and within its declared service constraints.**

The scientific target is the conjunction:

> A learner whose individual revisions are historically licensed and whose record remains answerable nevertheless achieves genuine sublinear online regret against the fixed class of lawful repairs.

This conjunction, not merely another regret calculation, is the point of the round.

---

# I. Current research state

## A. Leverage / normative-learning architecture

The leverage line is developing a theory of reason-guided deliberation without a fixed external normative ground truth.

Its relevant components are now:

* **answerability:** the system cannot erase, merge away, or silently evade obligations created by its own history;
* **reasons-responsiveness:** individual revisions must be licensed by live reasons rather than selected because they happen to reduce charge;
* **practical demand / docket pressure:** cases generate obligations to rule rather than permitting the empty-book solution;
* **lawful-edit certificates:** local counterfactual repairs are independently certified without access to their profitability;
* **online learning:** the learner should not continue making a recurrent class of historically repairable mistakes at positive asymptotic rate.

The hoped-for synthesis is not “learn the true morality.” It is:

> among revisions that the system's own public reason structure licenses, persistent correctable failure should become dynamically unsustainable.

PR #20 established the theorem bridge needed to make that statement mathematically meaningful.

## B. Item 29 result

Treat the following as controlling unless you find a genuine contradiction.

The theorem-facing action alphabet is the fixed set

[
\Lambda =
{
\text{merits-positive},
\text{merits-negative},
\text{default},
\text{decline-0},
\dots,
\text{decline-4}
}.
]

Occasion-local decoding introduces obligation and ledger identity only after the semantic choice is made.

The audited comparator class contains exactly nine programs:

1. `identity`
2. `repair_declines`
3. `repair_declines_even`
4. `repair_declines_odd`
5. `toll_declines_1`
6. `toll_declines_2`
7. `toll_declines_4`
8. `default_declines`
9. `withdraw_merits`

These are immutable data records, not arbitrary callbacks.

The bridge establishes, within the frozen environment:

* fixed `N = 8`;
* `K = 9`;
* always-on selector `M = 1`;
* closure of every induced transformation on `Lambda`;
* commutation of transformation with occasion-local decoding;
* preservation of pointwise, mixed, cumulative, counterfactual, and regret quantities;
* a finite non-capture audit for the exact nine-program/default-policy class;
* a Lean-proved generic finite-horizon regret-preservation lemma;
* a Lean-proved recurrent-failure lower bound.

The Blum–Mansour guarantee is an **expected mixed-action loss guarantee**. It is not yet a sampled-path or high-probability theorem.

## C. Frozen theorem boundary

Do not silently generalize past these assumptions:

* one occasion per date;
* `service_window = 4`;
* canonical responses only;
* frozen arrivals, schedules, filings, and relevant reasons;
* guards evaluate from the actual strict pre-action prefix;
* full bounded charge vectors are available;
* no suspension;
* no solvency coupling;
* no post-hoc affordability deletion;
* no comparator filtering after play based on profitability;
* charge bounded by the declared `ell_max`;
* comparator class fixed ex ante to the nine audited programs.

A result outside this boundary requires a separately identified theorem or experiment.

---

# II. Primary task

Construct the Blum–Mansour Theorem 18 learner on the repaired lawful-action interface.

Do not substitute a generic multiplicative-weights learner over nine comparators.

The source reduction matters.

The implementation must contain the theorem's essential structure:

* weights conditioned on **source action and modification rule**;
* eight source-action rows;
* nine comparator programs;
* the corresponding transformation-weighted stochastic matrix;
* computation of a stationary distribution used as the learner's mixed action;
* update of the row-conditioned weights from the revealed full-information charge vector.

For `M=1`, the natural theorem-facing state therefore contains 72 action/program weights before any harmless implementation simplification.

The implementation should make it possible to identify the exact mathematical object corresponding to each term in the source construction.

---

# III. Real-valued parameter and stationary-distribution issue

This is a required part of the round, not an implementation footnote.

The repository has strongly preferred exact-rational executable evidence. Blum–Mansour's optimized learning parameter and stationary-distribution computation are naturally real-valued.

Handle this honestly.

Acceptable outcomes include:

### Outcome A — faithful real-valued implementation

Implement the source semantics numerically and clearly separate:

* source-theorem guarantee;
* numerical solver accuracy;
* empirical observations.

Do not call floating-point agreement an exact proof.

### Outcome B — exact-rational variant

Give a justified exact-rational choice of learning parameter and an exact method for selecting an appropriate stationary distribution, together with the resulting regret bound.

If the asymptotic bound worsens, report the actual bound.

### Outcome C — explicit implementation obstruction

If exact-rational execution cannot faithfully realize the source algorithm without additional mathematics, say exactly why and implement the smallest faithful approximate version needed to test the scientific question.

Do **not** silently round a theoretically optimized parameter and continue reporting the unmodified theorem bound.

---

# IV. Experiments

Use at least the declared horizons

[
T\in{12,24,48,96}.
]

Report the entire comparator class alongside every regret result.

For each horizon, compute at minimum:

1. learner expected cumulative mixed-action charge;
2. counterfactual cumulative charge under each of the nine lawful programs;
3. regret against each program;
4. maximum Φ-law regret;
5. regret divided by `T`;
6. regret divided by the theorem-scale quantity

[
\ell_{\max}\sqrt{8T\log 9}.
]

The purpose is not to “verify big-O” from four data points. The purpose is to make sure the implemented dynamics behave like the theorem-facing object and to expose any interaction with the repository architecture.

Include deliberately adversarial fixtures in which at least one lawful program repeatedly produces a uniform positive saving.

The learner should face a setting where failure to learn is visible, not merely benign random examples.

---

# V. Recurrent-failure consequence

Connect the learner result to the already established lower bound.

For a fixed lawful program `phi`, suppose the learner assigns total mixed-action mass at least `rho*T` to source labels on which:

* the program is admitted; and
* it saves at least `delta > 0`.

Then, up to the declared bounded distortion term `B`,

[
R_T(\phi)\ge \rho\delta T-B.
]

Use this to state precisely what the learner result retires.

The permitted conclusion is approximately:

> A learner with `o(T)` expected Φ-law regret cannot continue assigning positive asymptotic expected mass to a recurrent uniformly remediable failure represented by one of the fixed lawful programs.

Do not strengthen this into:

* eventual correctness;
* moral correctness;
* convergence to a unique normative state;
* elimination of failures outside the comparator class;
* a claim about realized-path frequency without an additional sampling theorem.

If convenient, add a sampled-action experiment, but label it empirical unless you separately prove a concentration/pathwise result.

---

# VI. The important test: answerability and service

This should receive substantial attention.

A learner that achieves low regret only by stepping outside the answerability architecture does not complete the intended synthesis.

Determine whether the actual learner's operation can be integrated with the current repository interfaces while preserving the relevant invariants.

At minimum inspect:

### 1. Answerability

Does the learner's mixed choice and subsequent sampled or selected response still produce the ordinary repository artifacts required for historical answerability?

Can obligations created by earlier actions still be tracked through the existing ledger/docket machinery?

Does the learner ever require retroactively rewriting its own record rather than making a new licensed response?

### 2. Reasons-responsiveness

The learner is allowed to put probability mass on actions for ordinary online-learning reasons.

But the **comparators** defining what counts as a repair must remain reasons-responsive independently of profitability.

Check carefully that construction of the learner does not reintroduce charge information into the legality interface.

Do not prove “the learner is reasons-responsive” merely because it has low regret.

These are different predicates.

### 3. Service / work constraints

Check the S4-style operational question already anticipated by item 30:

* Does computing the learner's distribution fit within the declared work model?
* Does every chosen response remain within per-date service capacity?
* Does the update mechanism create hidden service obligations?
* Is stationary-distribution computation being treated as free meta-computation when the intended architecture would have to pay for it?

Distinguish clearly between:

* theorem-level computation treated abstractly;
* executable implementation cost;
* repository-native service work.

If the current service model cannot meaningfully account for the learning computation, record that as interface debt rather than pretending the condition has passed.

---

# VII. Baselines

Compare the theorem-faithful learner against useful controls.

At minimum include:

1. a fixed or uniform policy;
2. a simple external-regret / Hedge-style baseline if already available or cheap to implement;
3. the theorem-faithful Φ-regret learner.

The purpose of the external-regret baseline is conceptual.

It should help demonstrate why ordinary regret over the eight actions is not equivalent to regret against history-dependent lawful repair programs.

Do not spend the round optimizing baseline performance.

---

# VIII. What would count as success

The strongest desired outcome is:

### Result 30-A — constructed lawful Φ-regret learner

A faithful implementation of the Blum–Mansour learner exists on the fixed eight-action, nine-program interface.

### Result 30-B — empirical/theorem consistency

Its expected mixed losses and comparator regrets behave consistently with the source guarantee on the declared environments, with no hidden horizon-growing action set or comparator capture.

### Result 30-C — recurrent-failure retirement

The existing recurrent-failure lemma combines with the learner guarantee to rule out positive asymptotic expected mass on represented uniformly remediable failures.

### Result 30-D — answerability compatibility

The learner's actual operation can be embedded into the answerability/service architecture without requiring record erasure, post-hoc comparator deletion, profit-sensitive certification, or undeclared service work.

If 30-A through 30-C hold but 30-D fails, that is still an important result:

> Φ-regret supplies the right learning theorem, but the present answerability architecture cannot yet host the learner faithfully.

Do not hide this outcome.

It would identify the next research problem much more sharply than another successful regret curve.

---

# IX. Likely failure modes to actively probe

Try to break the construction.

In particular test or reason about:

1. non-unique stationary distributions;
2. reducible transformation matrices;
3. zero-weight or degenerate rows;
4. numerical stationary-distribution instability;
5. learning-rate choices that depend on a declared horizon;
6. whether a doubling trick preserves the comparator semantics;
7. hidden dependence on future information;
8. accidental use of replay-prefix rather than actual-prefix guards;
9. comparator maps that cease to close after learner-generated actions;
10. legality becoming dependent on charge through implementation glue;
11. service-accounting assumptions that make learner computation effectively free;
12. the difference between mixed expected loss and sampled realized loss.

Necessity witnesses are preferred wherever practical.

---

# X. Anytime status

The theorem bridge currently gives a horizon-tuned existence result.

Do not imply that one infinite-run learner has already been proved to satisfy the same asymptotic guarantee.

Choose one of:

* remain explicitly horizon-tuned;
* prove a doubling/restart construction;
* give another justified anytime schedule.

If you implement doubling, check that restart boundaries do not change the comparator semantics or invalidate answerability claims.

An empirical doubling implementation without proof should be labeled empirical.

---

# XI. Comparator coverage

Do not widen `Φ_law` in this round unless a tiny extension is required to fix a discovered implementation defect.

Nine programs is deliberately weak.

Report that weakness prominently.

The next conceptual question after a successful item 30 is likely not “can we reduce regret further?” but:

> How rich must the lawful comparator language become before low regret means robust normative self-correction rather than success against nine hand-selected repairs?

That is future work.

Do not solve it here.

---

# XII. Repository deliverables

Create a new round directory, preferably something like:

`projects/leverage/rounds/2026-08-11-phi-regret-learner/`

Ship at minimum:

* `README.md`
* `FOR_HUMANS.md`
* `PHI_REGRET_LEARNER.md`
* implementation source
* exact or numerically controlled tests
* experiment output/table
* answerability/service audit
* `THEOREM_LEDGER.md`
* `PROVENANCE.md`

If a Lean theorem is added, place it under the appropriate `Workspace.Leverage.Contrib` namespace and keep it unregistered unless the repository's evidence rules justify promotion.

Update:

* `PRIORITIES.md`
* `RESEARCH_STATE.md`
* `PROVENANCE.md`

only insofar as the round's actual results warrant.

Do not modify the deference line.

Do not rewrite the authoritative consolidation wholesale.

---

# XIII. Evidence discipline

For every significant statement, label it as one of:

* source-theorem fact;
* Lean-proved;
* exact-test-supported;
* numerical experiment;
* finite audit;
* derived consequence;
* conjecture;
* open.

In particular keep separate:

1. Blum–Mansour's theorem;
2. the repaired representation bridge;
3. the concrete learner implementation;
4. empirical regret measurements;
5. answerability compatibility;
6. sampled-path behavior.

Do not allow a successful numerical run to migrate upward into a theorem claim.

---

# XIV. Decision rule

At the end of the round give one of the following top-level verdicts:

### **Closed-positive**

A faithful Φ-law learner has been constructed and its integration passes the declared answerability/service tests.

### **Learning-positive, integration-blocked**

The learner and regret result work, but the answerability/service architecture cannot yet host them without an additional interface or theorem.

### **Implementation-blocked**

The theorem bridge remains valid, but faithfully realizing the source learner exposes unresolved stationary-distribution, arithmetic, horizon, or computation-model debt.

### **Bridge reopened**

Only use this if the actual learner construction uncovers a genuine error in the PR #20 theorem-interface claim.

Do not call an ordinary engineering difficulty a theorem failure.

---

# XV. Research interpretation

If successful, state the result conservatively but clearly.

The intended claim is not:

> the learner discovers normative truth.

It is:

> given a fixed public language of historically licensed repairs, an answerable bounded reasoner can be placed under an online-learning discipline that prevents it from indefinitely repeating represented, uniformly correctable failures.

That would be the first real synthesis in this line of:

* answerability to one's history;
* local legitimacy of revision;
* and global online self-correction.

Determine whether the present architecture actually earns that statement.

---

**Prompt provenance:** GPT-5.6 Sol (OpenAI)
**Maintainer:** A. M. Berns
