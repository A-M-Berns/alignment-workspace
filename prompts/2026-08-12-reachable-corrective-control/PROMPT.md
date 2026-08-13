Alignment Workspace Research Prompt — Foreclosure as Loss of Reachable Corrective Control

Maintainer: A. M. Berns
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Repository: A-M-Berns/alignment-workspace
Research line: Deference / corrigibility
Date: 2026-08-12
Mode: Dispatched exploratory representation round
Required endpoint: Reviewable pull request. Do not merge without maintainer authorization.

⸻

I. Mission

Build the smallest dynamic model in which foreclosure is genuinely expressible.

The target phenomenon is:

An AI can take an action now that leaves the principal unable to perform some corrective intervention later, even though the immediate realized behavior may look the same as under a non-foreclosing action.

Do not attempt a full corrigibility theorem.

Do not use sealed-sibling constructions.

Do not import dose-response or endpoint-preservation machinery.

Do not make Cartesian Frames foundational unless the construction actually needs them.

The core question is:

\boxed{
\text{Can foreclosure be represented as loss of future reachable principal-controlled correction?}
}

A positive round should give us a representation over which a later corrigibility theorem can be stated.

⸻

II. Why this round exists

The deference line has accumulated several exact negative results.

Static realization is too coarse

Earlier attempts collapsed distinct authority/control architectures whenever they induced the same realized action map.

Adding downstream valuation parameters or hidden jurisdiction fields did not repair this.

Cartesian Frames helped, but did not solve the problem

The CF round established that realized behavior can erase meaningful counterfactual control structure.

It also showed:

* CF represents control, not authorization;
* accurate simulation can collapse with delegation under CF;
* CF has no intrinsic temporal transition structure;
* Commit / External provide useful representation examples but do not by themselves express present foreclosure of later correction.

PR #26 attempted a cut-time capability family and failed

The time-indexed corrective-capability round tried to combine CF control with a cut-time counterfactual family.

The red team proved the construction collapsed because the system had no dynamics without the advisor:

\operatorname{cutRun}(\pi,n,k,s)
=
\operatorname{run}(\pi,\min(n,k),s).

So cutting A off merely froze the trajectory.

Its foreclosure predicate therefore reduced to a one-step property on a single run rather than a property of genuine alternative continuations.

The same review also showed:

* constructing a frame around a state field does not certify that the field represents a genuine capability;
* the accurate-simulation gate was disconnected from the transition dynamics;
* an Actor tag became the very sort of authorization label the round was trying to avoid.

Preserve these negatives.

Do not repair them by renaming fields.

⸻

III. New strategy

Use an ordinary multi-source transition system.

A schematic target is:

S_{t+1}
=
F(S_t,h_t,a_t,e_t),

where:

* S_t is the system state;
* h_t is the principal/human action;
* a_t is the AI/advisor action;
* e_t is autonomous/environmental evolution.

The key change from PR #26 is:

The system continues evolving when the AI does nothing.

There is no sealed sibling and no cut-time baseline.

Time comes from repeated application of the actual transition relation.

⸻

IV. Reachability

Define a finite-horizon or finite-state reachability relation such as

\operatorname{Reach}(S)

or

S \leadsto^* S'.

Prefer the smallest exact finite definition.

It should represent genuine future continuations under later principal/environment/AI choices.

Do not build an elaborate temporal logic.

A plain transition relation plus reflexive-transitive reachability is enough if it works.

⸻

V. Corrective capability must come from the dynamics

Define a designated corrective role for the principal.

The critical requirement is:

CanCorrect must be derived from actual transition variation, not from a Boolean state label and not from a frame fabricated to read one.

A schematic form is:

\operatorname{CanCorrect}_H(S)

iff there exist principal actions h_0,h_1 and appropriate fixed context such that varying only the principal coordinate changes some relevant outcome or reachable continuation:

F(S,h_0,a,e)\not\sim F(S,h_1,a,e).

The equivalence / observation relation \sim should be minimal and explicit.

If correction is intrinsically multi-step, it is acceptable instead to define:

\operatorname{CanCorrect}_H(S)
\iff
\exists h,\;S'
\text{ such that a principal-controlled path reaches a designated corrected region}.

Choose whichever form makes the intended corrective capability non-vacuous with least machinery.

⸻

VI. Foreclosure target

Define foreclosure dynamically.

A present AI action a should count as foreclosing a corrective capability only if it removes a future principal-controlled correction that otherwise remains reachable.

A schematic target is:

\operatorname{Forecloses}(S,a)

iff:

1. correction remains reachable under an appropriate non-foreclosing baseline, but
2. after taking a, every relevant future continuation lacks that correction capability.

For example:

\operatorname{CanCorrectFuture}_H(S)

and

S' = F(S,h,a,e)

with

\forall T\in \operatorname{Reach}(S'),
\qquad
\neg \operatorname{CanCorrect}_H(T).

Do not mechanically use this exact formula if it has bad quantifiers.

The round should derive the cleanest finite definition.

The semantic content must be:

A acts now, and afterward the principal has lost a future correction branch that previously existed.

⸻

VII. Mandatory tests

A positive verdict requires all of the following in substance.

T1. Genuine autonomous continuation

Show that the system can evolve nontrivially with A absent or idle.

PR #26’s collapse must be impossible:

A=\text{idle}
\not\Rightarrow
S_{t+1}=S_t

in general.

A trivial clock-bit update is not enough.

The post-A dynamics should include some genuinely relevant principal or environmental continuation.

⸻

T2. Dynamics-first corrective capability

Construct a state where H genuinely has an effective corrective capability and a state where H does not.

The distinction must be witnessed through the actual transition/reachability structure.

Negative controls:

* duplicate principal actions with identical effects must not count;
* adding an inert state label must not create capability;
* merely changing action-set cardinality must not create capability.

⸻

T3. Same immediate effect, different future reachability

Construct two AI actions a and b such that:

\operatorname{ImmediateObs}(S,a)
=
\operatorname{ImmediateObs}(S,b),

but:

a:
\quad
\exists T\in\operatorname{Reach}(S_a)
\text{ with }
\operatorname{CanCorrect}_H(T),

while:

b:
\quad
\forall T\in\operatorname{Reach}(S_b),
\neg\operatorname{CanCorrect}_H(T).

This is the central witness.

It should demonstrate exactly:

same-looking present behavior, different future ability to correct.

⸻

T4. Genuine temporal foreclosure

Show that the capability loss is not merely immediate relabeling.

There should be at least two stages:

S_t
\to
S_{t+1}
\to
S_{t+2}

such that an action at t changes what the principal can do at a later stage.

Prefer a witness where the immediate world-level realization at t is unchanged and the difference appears in later reachability.

⸻

T5. Non-foreclosing comparison

Construct a nearby action/system where:

* the immediate realization is the same;
* the system still evolves;
* the future corrective branch remains reachable.

This should rule out definitions under which every transition is “foreclosure.”

⸻

T6. Simulation non-substitution

Give A a perfect predictor of H’s relevant corrective choice.

The model must still distinguish:

\text{A predicts }h

from

\text{H supplies input }h

to the protected causal coordinate.

Do not add a disconnected Actor label.

Ideally the separation should follow because the real transition has distinct input channels:

F:S\times HAct\times AAct\times Env\to S.

Varying the A-coordinate alone should not substitute for varying the protected H-coordinate.

If this cannot be proved without an extra capability/provenance primitive, say exactly where it fails.

⸻

T7. No hidden-label cheat

Add an explicit inert field or fake jurisdiction bit and verify that:

* transition/reachability is invariant under it;
* CanCorrect is invariant under it;
* foreclosure is invariant under it.

The positive result must survive this adversary.

⸻

VIII. Cartesian Frames: optional, not assumed

Do not begin by encoding the model in Cartesian Frames.

First construct the transition/reachability result.

Afterward ask:

Does the transition-derived effective-control structure naturally instantiate a Cartesian frame in a useful way?

If yes, it is acceptable to define a frame from the actual transition function and prove something like:

\operatorname{CanCorrect}_H(S)
\iff
\neg\operatorname{AgentInert}(C_S).

This correspondence is useful only if the frame is derived from the real dynamics.

Do not manufacture a frame around an arbitrary state field.

If no CF-specific machinery does mathematical work beyond that correspondence, say:

Cartesian Frames are a semantic model of the effective-control interface, not a theorem dependency.

That is an acceptable and potentially preferable result.

⸻

IX. Explicitly out of scope

Do not work on:

* sealed siblings;
* endpoint preservation;
* dose-response;
* legitimacy theory;
* normative learning;
* Hohfeldian power;
* authorization logic;
* speaks-for;
* DCL-PC;
* deontic permission;
* proof-carrying authorization;
* resource-separated computational futurity;
* LI competence;
* near-indifference leakage;
* grade-to-quantity;
* value of commitment;
* a final corrigibility inequality.

The point of this round is to isolate the dynamic control representation.

⸻

X. Relationship to dose-response

Record explicitly:

\boxed{
\text{dose-response asks how A changes H's deliberation}
}

while

\boxed{
\text{foreclosure asks what H can still do after A acts}
}

Do not synthesize these in this round.

A result on one axis must not be treated as evidence on the other.

⸻

XI. What success looks like

The strongest intended result is something like:

There exists a finite autonomous transition system with separate principal and advisor inputs in which two advisor actions have identical immediate realization but induce different future principal-controlled reachable sets; one preserves a genuine corrective path and the other eliminates it. Perfect prediction of the principal’s corrective action by the advisor does not itself provide access to the principal’s causal input channel.

If machine-checked, this is enough to say:

Foreclosure is expressible at the representation level in a dynamic reachability model.

Do not claim more.

⸻

XII. What failure looks like

A negative result is valuable.

Especially valuable failure modes include:

* reachability does not add anything beyond adjacent-state comparison;
* CanCorrect collapses to a hidden label;
* distinct H/A channels are only syntactic and not causally load-bearing;
* perfect simulation still substitutes for H;
* foreclosure requires an explicit capability/provenance type;
* the definition quantifies away every nontrivial example;
* every preservation/foreclosure witness differs already in immediate realization.

If one occurs, isolate the smallest missing primitive.

Do not respond by adding a large formalism in the same round.

⸻

XIII. Verdict classes

Use exactly one.

Representation-positive

Use only if T1–T7 substantially pass.

Meaning:

A genuinely temporal loss of future reachable corrective control is now expressible.

⸻

Dynamics-positive, protection-incomplete

Time and foreclosure work, but simulation/protected-channel separation fails.

⸻

Protection-positive, foreclosure-incomplete

Separate causal channels work, but future capability loss does not become a genuine dynamic reachability distinction.

⸻

Mixed

Important successes and failures coexist.

⸻

Insufficient

The model does not improve materially on PR #26.

⸻

XIV. Existing-obstruction table

End with:

Existing obstruction	repaired?	evidence
static realization collapses control distinctions		
CF lacks intrinsic time		
PR #26 cut freezes instead of continuing		
fabricated frame can certify spurious field		
same immediate behavior / different future capability		
simulation substitutes for protected exercise		
foreclosure not expressible		
authorization/capability relation absent		
computational futurity	untouched	
competence / near-indifference	untouched	
dose-response / legitimacy	separate	

Do not mark anything repaired merely because it has a name.

⸻

XV. Lean strategy

Prefer a tiny finite construction.

A reasonable core might contain:

* finite State;
* finite HAct;
* finite AAct;
* finite EnvAct;
* step;
* finite-horizon or closure-based Reach;
* CanCorrect;
* Forecloses;
* explicit positive and negative-control systems.

Machine-check the acceptance witnesses if practical.

No sorry.

No new axioms.

Audit all new declarations under repository policy.

Keep names provisional unless already canonical.

⸻

XVI. Adversarial review

Run a separate adversarial review.

It should specifically attack:

1. Does the system meaningfully evolve without A?
2. Is autonomous evolution relevant or just a clock tick?
3. Is CanCorrect derived from the actual dynamics?
4. Can an inert state bit fake correction?
5. Do duplicate actions fake correction?
6. Is “future” genuinely multi-step?
7. Are the two key actions really immediately observationally identical?
8. Does the non-foreclosing arm genuinely retain a future corrective branch?
9. Does the foreclosing arm eliminate it from all relevant continuations?
10. Can A simulate H and thereby acquire the protected effect?
11. Are H/A action types merely labels on extensionally interchangeable inputs?
12. Does the theorem secretly assume foreclosure in the transition definition?
13. Is CF doing real work, or should it be abstracted away?
14. Has the round accidentally reintroduced sealed-sibling or endpoint machinery?

Accept substantive corrections.

Prefer machine-checked refutations over prose responses when possible.

⸻

XVII. Deliverables

Suggested directory:

projects/deference/rounds/2026-08-12-reachable-corrective-control/

Produce:

1. REACHABLE_CORRECTIVE_CONTROL.md
    Technical verification register.
2. REACHABLE_CORRECTIVE_CONTROL_FOR_HUMANS.md
    Concise conceptual explanation.
3. Lean/executable finite construction.
4. Adversarial review and disposition record.
5. Obstruction table.
6. Minimal updates to:
    * PRIORITIES.md;
    * RESEARCH_STATE.md;
    * deference roadmap/ledger if warranted;
    * provenance surfaces.
7. No new DECISIONS.md item unless there is a genuine maintainer choice not already represented.

⸻

XVIII. Stopping rule

Stop once you can answer these:

1. Does the system evolve meaningfully without A?
2. Is corrective capability derived from actual transition dynamics?
3. Can two identical-present actions differ in future corrective reachability?
4. Is that difference genuinely temporal?
5. Does a nearby non-foreclosing control preserve the branch?
6. Does perfect prediction fail to substitute for principal exercise?
7. Does the result survive hidden-label adversaries?
8. Is CF actually needed?

If these are answered, do not continue into value theory.

⸻

XIX. Git and PR workflow

This round must normally terminate in a reviewable pull request.

Before beginning, inspect the current repository state and existing open deference PRs. In particular, do not accidentally lose or duplicate PR #26’s negative results.

Work on a dedicated branch from the appropriate current base.

Then:

* make scoped changes;
* run repository tests;
* run Lean builds/audits where applicable;
* run adversarial review;
* incorporate accepted corrections;
* update research-state surfaces conservatively;
* commit with required DCO/sign-off;
* record model provenance;
* push the branch;
* open a pull request.

A negative or Mixed result still gets a PR.

Do not merge.

If a PR cannot be opened, leave a clean pushed/committed branch and report the precise blocker.

⸻

PR body requirements

Include:

* final verdict;
* exact state/transition interface;
* definition of reachability;
* definition of corrective capability;
* definition of foreclosure;
* T1–T7 results;
* strongest positive witness;
* strongest negative result;
* simulation result;
* hidden-label result;
* whether CF was used and whether it was essential;
* which previous negatives moved;
* which did not;
* computational-futurity status;
* competence status;
* dose-response/legitimacy status;
* evidence classes;
* test/build/audit status;
* adversarial-review outcome;
* provenance;
* explicit “does not establish” section.

⸻

Final success criterion

The round succeeds if it can honestly say:

We now have a genuine dynamic model in which an AI action can remove a future principal-controlled corrective path without changing the immediate realized action, and that loss is defined through the actual transition/reachability structure rather than through a hidden authority label.

That is the target.

No more.

Prompt provenance: GPT-5.6 Sol (OpenAI).
