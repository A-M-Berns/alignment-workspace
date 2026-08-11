# Alignment Workspace — Prepare the Leverage Program for a φ-Regret Test

**Maintainer:** A. M. Berns
**Research program:** Leverage / Normative Learning
**Task:** φ-regret preparation round
**Model provenance:** GPT-5.6 Sol
**Date:** 2026-08-11

## Objective

Prepare the Alignment Workspace so that the **next research round can perform a mathematically meaningful finite φ-regret test** for the normative learner.

Do **not** try to solve the full φ-regret problem in this round, and do **not** force a complete theory of reasons-responsiveness before the test can begin.

The goal is narrower and more concrete:

> Build, document, test, and audit the smallest finite-era substrate on which it is well-defined to ask whether the learner has low regret relative to a class of historically lawful, reasons-responsive local edits.

At the end of this round, a new agent should be able to enter the repo and immediately attempt the first φ-regret theorem/experiment without having to make hidden choices about:

* what a comparator is;
* when an edit is admissible;
* what history is replayed;
* which consequences are counterfactually recomputed;
* what loss/charge is compared;
* how movement/capacity is kept distinct from loss;
* what counts as recurrence;
* what the test is supposed to establish;
* or which results would falsify the proposed direction.

Reasons-responsiveness may remain **parametric or schematic** where substantive normative judgment is genuinely unresolved. What may *not* remain schematic are the interfaces needed to determine whether a proposed edit belongs to the comparator class.

---

# 0. Worktree and parallel-work safety — mandatory

This task may be running concurrently with other Alignment Workspace work. **Do not modify the primary checkout or another agent's worktree.**

Before editing anything:

1. Locate the repository root with Git.
2. Record:

   * repository root;
   * current branch;
   * current commit SHA;
   * `git status --short`;
   * existing linked worktrees.
3. Determine whether the current directory is already a dedicated worktree suitable for this task.
4. If it is already a dedicated task worktree, remain there.
5. Otherwise create a **new sibling worktree** from the exact current `HEAD`, on a uniquely named branch such as:

   * `research/phi-regret-prep-20260811`
   * with a sibling path such as `../alignment-workspace-phi-regret-prep-20260811`.
6. Perform **all mutations only inside that worktree**.

Hard safety rules:

* Do not `git stash` the primary checkout.
* Do not `git reset`, `git clean`, force checkout, rebase, or otherwise rewrite another checkout.
* Do not delete or move another worktree.
* Do not switch the primary checkout's branch.
* Do not commit changes belonging to another concurrent task.
* Do not merge into `main`/`master` or another shared branch.
* Do not remove the worktree when finished; leave it available for review.
* If the source checkout has uncommitted work, do not alter it. Record that fact in the handoff. Work from the committed `HEAD` unless this task is already executing inside a dedicated worktree containing those changes.
* Treat frozen/canonical consolidation artifacts as read-only unless the repository explicitly designates a living roadmap/status file for updates.

Create a small `WORKTREE_RECORD.md` in this round's output directory recording the source SHA, task branch, worktree path, initial cleanliness state, and files modified by this round.

---

# 1. First reconstruct the current program state

Do not begin from this prompt alone.

Inspect the current Alignment Workspace and identify the authoritative/latest materials for at least:

* the leverage consolidation;
* answerability;
* the answerability/challenge docket;
* the newer decision/practical-demand or inquiry/docket work;
* reasons-responsive / earlier-authorized correction material;
* the normative learner experiments;
* settlement/inquiry interfaces;
* current roadmap/open-problem/theorem-ledger files;
* any existing discussion of:

  * φ-regret;
  * self-correction;
  * lawful edits;
  * replay;
  * counterfactual influence;
  * remediable failure patterns;
  * HistOK / ReasonOK or equivalent notions;
  * coverage/inquiry;
  * fenced vs pooled accounting.

Do not privilege chronological notes over later consolidation/audit documents merely because they are more detailed. Determine authority from the repo's own status conventions.

Write a concise `CURRENT_STATE.md` for this round that says what is:

* proved;
* architected;
* merely proposed;
* assumed/parametric;
* and open.

The relevant high-level architecture should be preserved:

1. **Leverage/statics:** represented reasons constrain unsettled judgment.
2. **Operative force:** those constraints affect an online process under explicit liability/movement control.
3. **Answerability:** recognized objections cannot simply be ignored or erased.
4. **Reasons-responsiveness:** changes must be licensed by reasons/history rather than merely advantageous.
5. **Self-correction / φ-regret:** recurrent remediable mistakes should not persist.
6. **Coverage/inquiry:** important remediable failures must eventually enter view.

The task of this round is primarily the interface between **4 and 5**.

---

# 2. Preserve the conceptual target

The intended learning theorem is **not** ordinary best-fixed-policy regret over complete normative theories.

The target comparator primitive is a class of **local lawful edits**.

A future theorem should be able to say approximately:

> Conditional on a represented failure entering view, no historically lawful local repair can continue to outperform the learner at positive asymptotic rate.

And from this derive a consequence of the form:

> A recurrent failure with a uniformly beneficial lawful repair cannot persist at positive rate.

Do not claim this theorem in the present round unless it genuinely falls out unexpectedly. The required success condition is that the repo becomes precise enough to test it.

The fundamental separation must remain:

* **Lawfulness / reasons-responsiveness determines which edits count as comparators.**
* **Charge or performance differential determines whether a lawful comparator would have done better.**

Never define an edit as lawful merely because it lowers loss, saves charges, preserves solvency, or performs better in hindsight.

That would collapse normative legitimacy into optimization and invalidate the project.

---

# 3. Define a minimal reasons-responsiveness interface

Create a dedicated document, preferably named something like:

`REASONS_RESPONSIVENESS_INTERFACE.md`

Do not attempt a complete substantive theory of reasons.

Instead specify the weakest explicit interface needed for φ-regret.

The interface should take an actual historical prefix (h_t), an actual local response/action (a_t), and a proposed replacement (b_t), and return either:

* a checkable `LawfulEditCertificate`; or
* rejection / unresolved status.

A v1 certificate should contain enough information to check, at minimum:

### A. Historical availability

The reasons, warrants, routes, permissions, or other grounds used to license the edit were available at the relevant historical prefix.

No later fact may be silently imported as though it had already been available.

### B. Reason connection

The cited grounds actually bear on the component being edited.

A live reason somewhere in the book cannot license arbitrary unrelated motion.

### C. Defeater discipline

The grounds relied on by the edit were not defeated, suspended, undercut, out of scope, or otherwise inactive according to the actual-prefix record.

### D. Scope discipline

The edit changes only the coordinates, response components, schema instances, dispositions, or other objects that its cited grounds license it to change.

### E. Magnitude discipline

Where applicable, distinguish:

* a reason for moving in a direction;
* from a reason for moving all the way to a particular endpoint.

Do not assume that directional support licenses arbitrary magnitude.

If magnitude remains substantively unresolved, expose a parameter/predicate such as `MagnitudeOK(...)` rather than inventing a canonical rule.

### F. Burden/history preservation

The edit cannot achieve apparent improvement by deleting, renaming away, retroactively discharging, or otherwise laundering outstanding objections, obligations, dependencies, targets, or lineage.

### G. No successor ratification

Later endorsement of the replacement is not sufficient evidence that it was lawful at the earlier prefix.

### H. No cost laundering

Lower charge, lower regret, lower reserve use, or improved solvency is evidence that an edit may be *advantageous*; it is not evidence that the edit was *licensed*.

### I. Explicit parametric residue

Anything still genuinely normative may remain an explicit predicate, oracle, warrant family, or policy parameter.

Good examples:

* `BearsOn(reason, issue)`
* `MagnitudeOK(reason_state, old, new)`
* `AddressOK(defect, edit)`
* `AuthorityOK(source, scope)`
* `ReasonCompatible(...)`

Bad examples:

* an opaque `IsLawful(edit)` predicate with no decomposition;
* defining lawfulness from low loss;
* smuggling the future replay result into the certificate.

The point is to make reasons-responsiveness **typed and auditable without pretending it is substantively complete**.

State clearly which certificate fields are mechanically checkable and which remain supplied policy relations.

---

# 4. Define the v1 comparator class (\Phi_{\mathrm{law}})

Create:

`LAWFUL_EDIT_GRAMMAR.md`

Define a finite/effectively enumerable v1 comparator class suitable for an initial experiment.

For this round prefer **conservative, issue-local edits**.

A comparator (\phi) should be a conditional edit rule of roughly the form:

[
\phi:
(\text{actual prefix},\text{occasion})
\mapsto
\begin{cases}
b_t & \text{if guard fires and a lawful-edit certificate exists},\
a_t & \text{otherwise.}
\end{cases}
]

Pin down:

* what information the guard may inspect;
* whether the guard is evaluated on the actual or replayed history;
* what objects the replacement may change;
* how occurrence identity is preserved;
* whether a comparator may fire once or repeatedly;
* how overlapping edit rules compose;
* what happens if two edits conflict;
* whether the edit is local-response, schema-local, case-local, or another explicitly chosen v1 granularity.

For the first test, strongly prefer:

* guards evaluated on the **actual prefix**;
* filings/questions/occasions frozen to those occurring on the **actual history**;
* local replacements only;
* no endogenous creation of new objections during replay;
* no ontology creation;
* no retroactive rewriting;
* no arbitrary changes to funding/capacity;
* no comparator whose applicability depends on seeing its own counterfactual consequences.

Explain why these restrictions are methodological scaffolding for the first theorem rather than claims about the final theory.

Include positive and negative examples.

At minimum include witnesses showing:

[
\text{profitable} \not\Rightarrow \text{lawful},
]

[
\text{successor-endorsed} \not\Rightarrow \text{lawful},
]

[
\text{reason exists} \not\Rightarrow \text{arbitrary edit lawful},
]

and at least one nontrivial edit that *is* certified lawful.

---

# 5. Specify replay semantics completely

Create:

`REPLAY_SEMANTICS.md`

This is load-bearing.

For an actual run (H) and comparator (\phi), define exactly what the replay (H^\phi) means.

The first version should be deliberately conservative.

Unless the current repo provides a better already-justified convention, use the following starting hypothesis:

### Frozen exogenous/event surface

Keep fixed from the actual run:

* case/question arrival;
* objection/filing arrival;
* empirical reports/pins;
* externally supplied messages;
* identities and timestamps;
* challenge grounds not themselves generated by the edited response;
* other declared exogenous events.

### Actual-prefix guards

Whether (\phi) fires at occasion (t) is evaluated from the actual prefix, not from the counterfactual prefix.

### Local endogenous recomputation

Recompute only consequences declared endogenous to the response being replaced, such as the local response status, charges on affected streams, disposition, or other explicitly listed downstream fields.

Do not casually recompute the entire future institutional history.

### No counterfactual authority laundering

The replay cannot generate new reasons that are then used to justify the edit that generated them.

### Identity preservation

The actual and replayed occurrence must remain pairable, so loss differences are interpretable occasion-by-occasion.

Produce a field-level table with columns like:

| field/event | frozen from actual history | recomputed | ignored in v1 | justification |

There should be no important history field whose replay treatment is implicit.

---

# 6. Define loss and keep resource use separate

Create:

`PHI_REGRET_OBJECTIVE.md`

The first φ-regret test should use **one interpretable loss/charge quantity**, not a kitchen-sink scalarization of every desideratum.

Inspect the existing answerability mechanism and identify the best existing charge/rent/liability notion to use.

Define actual cumulative loss and replay cumulative loss, for example:

[
L_T(H),
\qquad
L_T(H^\phi),
]

and

[
R_T(\phi)
=========

L_T(H)-L_T(H^\phi).
]

Set sign conventions once and test them.

If the existing theory makes another convention more natural, use it, but make it impossible to confuse “positive regret” with “the comparator was worse.”

Keep **movement, reserve, force-admission, and other operative-resource constraints separate** unless there is already a proved reason to combine them into loss.

A comparator that reduces charges while violating operative safety is not an admissible successful comparator; encode this through comparator admissibility/resource feasibility, not by inventing arbitrary exchange rates between normative charge and financial movement.

Specify:

* per-occasion loss;
* cumulative loss;
* comparator advantage;
* normalized regret;
* positive-rate outperformance;
* any boundedness assumptions needed by the intended online-learning algorithm.

---

# 7. Define the remediable-pattern consequence before proving regret

Create:

`REMEDIABLE_FAILURES.md`

Define a v1 **remediable failure pattern**.

It should contain roughly:

1. a recognizable guard/pattern;
2. a recurring actual response;
3. a lawful replacement;
4. a lawful-edit certificate schema;
5. an expected or realized charge advantage when the edit fires;
6. an occurrence count/frequency notion.

State the desired future consequence theorem in explicit conditional form.

For example:

> If a represented pattern occurs on (\Omega(T)) occasions, a fixed lawful edit applies on those occasions, and applying it saves at least (\delta>0) charge per occurrence up to bounded counterfactual distortion, then any learner with (o(T)) regret against that edit cannot continue exhibiting the pattern at positive rate.

Do **not** silently assume coverage.

Separate:

* **Self-correction:** conditional on a remediable pattern being represented in (\Phi_{\mathrm{law}}), it does not persist.
* **Coverage:** important/recurrent remediable patterns eventually enter the represented challenge/comparator class.

Coverage may remain a separate assumption/module in this round.

---

# 8. Investigate bounded counterfactual influence

Create:

`COUNTERFACTUAL_CHARGE_INFLUENCE.md`

This is the main mathematical preparatory investigation.

Determine whether, under the conservative replay semantics, one local lawful edit has bounded influence on future charge accounting.

Investigate at least two regimes:

## A. Fenced/localized accounting

Use whatever account separation/firewall machinery already exists.

Try to establish a finite statement of the form:

> The total difference between actual-history and replayed charge consequences attributable to one local edit is bounded by a quantity depending only on the finitely many streams/accounts the edit can touch and their admitted lifetime liability.

Be precise about assumptions.

If the bound is essentially an accounting lemma, say so.

## B. Pooled/shared solvency

Construct the smallest exact witness you can in which:

* one local edit changes a pooled solvency/suspension/insolvency date;
* that changes later service or charge outcomes globally;
* and counterfactual divergence grows with horizon.

If this works, record it as a sharpness/necessity witness showing why fencing or another locality condition is necessary for the simple replay-based φ-regret reduction.

If it does *not* work, explain why the prediction failed.

Do not force the expected conclusion.

---

# 9. Build an executable finite φ-regret test harness

The repo should not leave this at prose.

Following existing repository conventions, create the minimal reference implementation needed to instantiate:

* finite actual histories;
* occasions/cases/questions;
* reason states;
* lawful-edit certificates;
* comparator guards;
* local edits;
* replay;
* per-stream charges/losses;
* fenced and pooled accounting;
* regret computation.

Reuse existing code and record types where doing so does not damage frozen modules.

Prefer adapters over invasive refactors.

The harness should support at least the following exact experiments:

### E1 — Profitable but unlawful

An edit would reduce charge but fails the reasons-responsiveness interface.

Expected: excluded from (\Phi_{\mathrm{law}}).

### E2 — Successor ratification

A later state endorses an edit for which no earlier licensing grounds existed.

Expected: excluded.

### E3 — Lawful one-shot repair

One certified local edit lowers the relevant charge.

Expected: admitted; replay difference computed correctly.

### E4 — Recurrent remediable failure

The same certified edit applies on repeated recognizable occasions and saves a fixed positive amount.

Expected: cumulative comparator advantage grows linearly if the learner never adopts the lesson.

This is the canonical positive-regret witness.

### E5 — Non-recurrent improvement

A lawful edit helps only finitely/often-sublinearly.

Expected: does not by itself witness positive-rate failure.

### E6 — Magnitude overreach

A reason licenses movement in a direction but not the full proposed endpoint.

Expected: rejected or marked unresolved via the parametric magnitude predicate.

### E7 — Defeated reason

The same edit is lawful before an undercutter/defeater and unlawful afterward.

Expected: comparator applicability changes according to actual-prefix reason status.

### E8 — Burden laundering

An edit lowers apparent charges only by deleting/relabeling an inherited obligation.

Expected: rejected.

### E9 — Fenced locality

One edit affects only its declared account/streams.

Expected: bounded counterfactual influence.

### E10 — Pooled divergence

One edit changes a shared solvency/suspension point and causes large downstream divergence.

Expected: demonstrate the failure of the naive locality lemma if the predicted witness exists.

### E11 — Guard-on-actual vs guard-on-replay

Construct an example where the two conventions differ.

Expected: v1 deliberately uses actual-prefix guards, and the test makes the reason for that choice visible.

### E12 — Frozen filings

Construct a case where allowing the replay to generate new filings changes the comparison drastically.

Expected: v1 freezes filings, and this limitation is documented rather than hidden.

All arithmetic should be exact where practical.

Tests must distinguish:

* legality/certificate status;
* replay semantics;
* loss computation;
* resource feasibility;
* regret.

Do not collapse these into one boolean “better.”

---

# 10. Produce the exact φ-regret test specification for the next round

Create:

`PHI_REGRET_TEST_SPEC.md`

This should be the main handoff artifact.

It must make the next research task almost mechanical.

Specify:

## The finite test environment

* horizon;
* action/response set;
* occasion structure;
* finite comparator class;
* loss range;
* legality predicates;
* replay semantics;
* bounded-influence/locality assumptions;
* resource constraints.

## Baselines

At minimum compare:

1. the current/default learner or a simple answerable policy;
2. a standard finite online-learning baseline if applicable;
3. a learner augmented with lawful-edit tracking.

Do not yet assume which algorithm wins.

## Quantity measured

For every (\phi\in\Phi_{\mathrm{law}}), compute:

[
R_T(\phi)
=========

L_T(H)-L_T(H^\phi)
]

or the chosen equivalent convention.

Also compute:

[
\sup_{\phi\in\Phi_{\mathrm{law}}} R_T(\phi)
]

and normalized regret.

If the comparator class is conditional/internal-regret-like rather than ordinary external regret, say exactly which standard notion it is closest to and where it differs.

## Success outcomes

Distinguish at least:

* **S0 — semantics success:** all quantities are well-defined and replay is deterministic;
* **S1 — witness success:** persistent remediable failure produces linear lawful-edit regret;
* **S2 — algorithmic success:** a candidate learner obtains sublinear regret on the finite class;
* **S3 — consequence success:** sublinear lawful-edit regret implies no positive-rate recurrent remediable failure under stated assumptions;
* **S4 — integration success:** the successful learner remains answerable, reasons-responsive by the declared interface, and within operative-resource constraints.

The next round need not reach all four.

## Failure outcomes worth learning from

Pre-register serious negative results:

* no satisfactory replay semantics even under conservative restrictions;
* counterfactual influence unbounded even with fencing;
* lawful edit class too weak and self-correction becomes vacuous;
* lawful edit class too broad and admits cost-driven normative rewriting;
* charge loss fails to correspond to the remediable-failure intuition;
* standard φ/internal/swap-regret machinery does not apply because losses/comparators are too history-dependent;
* low regret is compatible with an intuitively important recurrent failure;
* resource feasibility destroys the comparator reduction.

Treat these as informative results, not reasons to hide counterexamples.

---

# 11. Map the construction to standard online-learning language

Create a short technical note:

`ONLINE_LEARNING_MAP.md`

Without claiming equivalence prematurely, identify the closest standard concepts:

* external regret;
* internal regret;
* swap regret;
* (\Phi)-regret / transformation regret;
* contextual or sleeping-expert variants if relevant;
* policy regret / history-dependent loss if relevant;
* approachability if genuinely useful.

The purpose is to tell the next mathematician which theorem machinery is plausibly reusable.

Explicitly answer:

1. What is the action space?
2. What is a transformation (\phi)?
3. Is (\phi) action-only, context-conditional, or history-conditional?
4. Are losses exogenous, adaptive, or policy-dependent?
5. Does replay make comparator loss well-defined from the actual history?
6. What bounded-influence assumption is required to reduce policy/history-dependent regret to ordinary φ-regret?
7. Is the first test genuinely φ-regret, or only φ-regret-shaped?

Do not rename a nonstandard problem “standard φ-regret” for rhetorical convenience.

---

# 12. Self-hosting interface: prepare, do not overbuild

The emerging research hypothesis is that a `LawfulEditCertificate` plus:

* recurrence evidence;
* and a positive charge differential

can itself serve as the grounds of a public **remediable-pattern objection**.

Prepare this interface if it can be done cleanly.

The desired conceptual identity is:

> the online learner's private deviation ledger and the public answerability system's remediable-pattern docket are two representations of the same detected lesson.

But do not redesign the entire docket merely to force this result.

If the existing objection ontology can represent it with a generic typed filing, use that.

If a new primitive is genuinely required, justify it by an ontology audit.

---

# 13. Keep the following things out of scope

Unless a dependency proves unavoidable, do **not** solve:

* open-ended ontology formation;
* unrestricted language migration;
* full natural-language interpretation;
* the complete substantive theory of reasons;
* universal adequacy of correction routes;
* full inquiry/attention allocation;
* multi-agent bargaining;
* full Logical Induction construction;
* the corrigibility/deference program;
* a universal scalar normative loss;
* convergence to moral truth;
* a latent true utility function.

Do not let those problems block a clean finite φ-regret test.

Where they matter, expose them as parameters or explicit future interfaces.

---

# 14. Protect existing results and architecture

Do not casually modify or reinterpret established leverage results.

In particular preserve the distinctions among:

* leverage;
* authority;
* answerability;
* reasons-responsiveness;
* operative force;
* solvency/capacity;
* loss/charge;
* learning/self-correction;
* coverage/inquiry.

Do not make:

* profitability imply legitimacy;
* feasibility imply priority;
* successor endorsement imply lawful change;
* recognition imply liveness;
* public provenance imply causal independence;
* low regret imply moral correctness.

Reuse the existing public-history, burden, lineage, warrant, challenge, settlement, and force-admission machinery when possible.

Prefer a thin adapter around stable modules to invasive changes.

---

# 15. Required output package

Use the repo's existing naming/location conventions where possible. If no suitable location exists, create a clearly scoped directory under the leverage/normative-learning research area for this round.

The final package should contain the equivalents of:

1. `README.md`
2. `WORKTREE_RECORD.md`
3. `CURRENT_STATE.md`
4. `REASONS_RESPONSIVENESS_INTERFACE.md`
5. `LAWFUL_EDIT_GRAMMAR.md`
6. `REPLAY_SEMANTICS.md`
7. `PHI_REGRET_OBJECTIVE.md`
8. `REMEDIABLE_FAILURES.md`
9. `COUNTERFACTUAL_CHARGE_INFLUENCE.md`
10. `ONLINE_LEARNING_MAP.md`
11. `PHI_REGRET_TEST_SPEC.md`
12. `THEOREM_LEDGER.md`
13. `OPEN_PROBLEMS.md`
14. executable source/adapters;
15. focused tests and an experiment runner;
16. `TEST_RESULTS.md`
17. `COMPLETION_AUDIT.md`

If some of these concepts fit better as sections of fewer files under existing repo conventions, consolidate them. Do not create bureaucracy for its own sake. But every substantive item above must be easy to locate.

Update the relevant living roadmap/context document so that a future agent sees the **full current project architecture and status**, not merely this local task. Do not rewrite frozen historical artifacts.

---

# 16. Evidence/status discipline

Every mathematical or architectural claim must be labeled using the repo's established evidence-status convention, or a clearly defined equivalent such as:

* **PROVED**
* **MACHINE-CHECKED**
* **EXECUTABLE FINITE WITNESS**
* **CONDITIONAL**
* **ARCHITECTED**
* **CONJECTURED**
* **OPEN**
* **REFUTED**

In particular, do not upgrade executable tests into proofs.

The theorem ledger must explicitly distinguish:

* definition/interface completion;
* finite witnesses;
* bounded-influence lemmas;
* assumptions about reasons-responsiveness;
* actual regret theorems.

A repo being “ready for a φ-regret test” is **not** evidence that φ-regret has been achieved.

---

# 17. Acceptance criteria

This round succeeds only if all of the following are true.

### A. Worktree isolation

All changes are confined to the dedicated task worktree/branch, with source SHA and modified files recorded.

### B. Comparator legibility

Given an actual finite history and a proposed edit, a reader can determine exactly what additional predicates/certificates are needed before the edit enters (\Phi_{\mathrm{law}}).

### C. Parametric honesty

Unresolved reasons-responsiveness questions are explicit parameters, not hidden inside prose or silently resolved by charge minimization.

### D. Replay determinacy

Given an actual history and admitted comparator, the v1 replay has an unambiguous output.

### E. Loss determinacy

Actual and comparator cumulative losses/regrets have fixed sign conventions and are mechanically computable.

### F. Resource separation

Movement/capacity/solvency constraints remain explicit and are not silently scalarized into normative loss.

### G. Positive witness

There is an executable recurrent-remediable-failure example producing linear lawful-edit regret for a learner that refuses to learn.

### H. Negative witnesses

The suite contains profitable-but-unlawful, successor-ratification, magnitude-overreach, defeated-reason, and burden-laundering examples.

### I. Counterfactual-locality verdict

The round gives a clear answer—positive, negative, or sharply conditional—about bounded counterfactual influence in the fenced finite setting, plus a pooled stress test.

### J. Next-round readiness

`PHI_REGRET_TEST_SPEC.md` is sufficient for another agent to begin the actual φ-regret investigation without redesigning the ontology.

---

# 18. Completion behavior

Run all focused tests and experiment scripts.

Inspect the final Git diff carefully.

Do not merge the branch.

Do not delete the worktree.

End with a concise `COMPLETION_AUDIT.md` containing:

* branch and source SHA;
* exact files added/modified;
* tests run and results;
* what is now fully specified;
* what remains parametric;
* which expected conjectures survived;
* which failed;
* the strongest theorem actually established;
* the strongest theorem **not** established;
* and the exact recommended next prompt/task for the first φ-regret theorem/experiment.

The recommended next task should be narrow. Ideally it should be possible to state it in one sentence of the form:

> Given the frozen finite comparator/replay environment prepared here, determine whether [specified online learner/construction] achieves sublinear (\Phi_{\mathrm{law}})-regret, and whether that guarantee implies retirement of every positive-rate uniformly remediable failure pattern.

Do not broaden the next task unless this round proves that formulation is ill-posed.

---

# Research standard

The aim is not to make φ-regret fit the project by definition.

The aim is to expose the exact mathematical question:

> Can a learner whose revisions remain answerable to its history and licensed by its live reasons nevertheless satisfy a genuine online self-correction guarantee—without a fixed external normative target?

Build the smallest rigorous environment in which that question can now be tested.

**Model provenance/sign-off:** GPT-5.6 Sol

---

## Addendum, sent mid-round by the maintainer

Verbatim:

> Is there anything in the leverage repo that's status human consolidated? If not, there should be some version of the deck (most recent version you can find in tex in downloads) with a timestamp and a notation that this might be superseded by further updates. also make sure at the end of your work you PR
