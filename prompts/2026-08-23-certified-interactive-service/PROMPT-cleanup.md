You are running a focused follow-up prosecution and cleanup pass on PR #51:

    “Certified interactive service: the waist survives revision”

Repository:
    A-M-Berns/alignment-workspace

Work on the existing PR #51 branch:

    round/2026-08-23-certified-interactive-service

Do not start a new research thread. Do not broaden into full inquiry theory.

The current PR verdict is:

    REQUIRES-REVISION — the service waist survives as a revised interface

with the surviving object approximately

    I = (A, Y, Gamma, Sigma)

where liabilities are supplied externally, Gamma is an observable-history response relation, ServiceSpecs provide finite record-visible certificates, and algorithmic content lives in structural capability assumptions rather than the bare interface.

This follow-up should assume that broad result provisionally stands.

Your job is to press hard on the remaining semantic seams, repair any genuine inconsistencies, rerun the adversarial suite, and leave PR #51 in a state suitable for conceptual closeout.

Do not merge the PR.

# 1. Central issue: certification semantics

There is a likely inconsistency in the current interface.

The PR currently says, in effect:

    L_sigma = { h : exists c, Check_sigma(h,c) }

and also requires:

    Check_sigma reads only the immutable receipts cited by c.

Since the transcript is append-only, if

    Check_sigma(h,c)

holds, the same cited receipts still exist unchanged in every extension hh'. Therefore:

    Check_sigma(hh',c)

should still hold.

Hence existential certifiability appears automatically extension-closed:

    h in L_sigma  =>  hh' in L_sigma.

But the current memo rejects this as a general law using a “recency-bounded” ServiceSpec where `make_cert` stops returning a certificate after another interaction occurs.

That test appears to distinguish:

    “the current prover emits a certificate”

from

    “there exists a valid certificate”.

Those are not the same predicate.

Prosecute this carefully.

## Required questions

Determine whether the current interface should distinguish at least:

    ValidCert_sigma(L, c)

from

    MayClose(d, L, n, c)

or equivalent notions.

Candidate interpretation:

- `ValidCert` says that c remains a valid historical certificate that the specified service event occurred.
- `MayClose` says that this certificate is presently admissible for discharging the still-open liability.

Then a freshness condition could live in `MayClose`:

    current_time - receipt_time <= k

without making an earlier valid historical certificate become false.

Do not assume these are the final names or types.

Try to find the minimum distinction that resolves the tension.

## Required cleanup

Audit and repair as needed:

- `INTERACTIVE_SERVICE_INTERFACE.md`
- `HANDOFF.md`
- `SERVICEABILITY.md`
- `README.md`
- `src/service_core.py`
- all tests referring to `Certified`, `MonotoneEvidence`, freshness, or persistence.

Pay special attention to:

    ServiceSpec.certified(...)
    ServiceSpec.make_cert(...)
    ServiceSpec.check(...)

The current implementation may be conflating:

    existential validity
    certificate discovery/proving
    current admissibility for closure.

Separate them if the mathematics demands it.

## Required adversarial cases

Add explicit tests for:

1. A certificate valid at t remains valid as a historical certificate at t+10.
2. The same certificate may nevertheless become unusable to close an open liability after a freshness deadline.
3. A prover failing to rediscover an existing certificate does not imply no valid certificate exists.
4. A later contradictory receipt does not rewrite the historical service event.
5. A later contradictory receipt may generate upstream review or a new inquiry, without invalidating the old service certificate.
6. A ServiceSpec whose actual acceptance semantics genuinely depends on future/current context is either:
   - represented through a separate closure-admissibility condition, or
   - shown to violate citation locality.

State exactly which.

# 2. Reassess `MonotoneEvidence`

The current PR treats extension-closure of

    Certified_sigma(h)

as an optional capability `MonotoneEvidence`.

This may be wrong under the intended citation-local existential semantics.

Determine whether:

A. `MonotoneEvidence` is actually a theorem of the core and should be removed from the capability lattice;

B. there are two different predicates, one necessarily monotone and another legitimately non-monotone;

or

C. citation locality itself needs weakening.

Strong default: do NOT weaken citation locality merely to preserve the existing taxonomy.

If two predicates are needed, name and define them cleanly.

Do not leave two uses of “certified” with different semantics.

# 3. Press on what exactly a ServiceSpec is

The current PR says extensionally:

    ServiceSpec = accepting language of finite traces

with finite-state monitors as implementations.

But proof-relevant certification is also retained.

Clarify the exact relationship among:

    ServiceSpec
    certificate type C_sigma
    checker
    accepted/certifiable histories
    prover / make_cert
    monitor implementation
    closure admissibility

Questions to settle:

- Is `make_cert` part of ServiceSpec at all?
- Or is it an algorithm/policy for discovering witnesses?
- Is `Check` the only constitutive semantic component?
- Is the extensional trace language induced by `exists c, Check`?
- If present closure conditions differ from historical validity, which object owns them?
- Does a finite-state monitor represent:
    historical certifiability,
    present closure eligibility,
    or both?

Prefer a type structure in which semantic predicates are not accidentally defined by an incomplete prover.

# 4. Online timing / exogenous arrivals

The current interface collapses each action to one response event:

    Gamma : H x A -> P+(Y)

and says exogenous events such as SCD request arrivals can “ride in the response component of whatever step is current.”

Press this harder.

The issue is not expressivity alone; it is online information order.

These protocols are potentially distinct:

    arrivals -> controller chooses action -> response

versus

    controller chooses action -> arrivals/response

versus

    autonomous environment event -> controller reacts.

For an online algorithm, these may induce different policy classes.

## Required task

Specify the temporal convention of CIS clearly.

Options might include:

1. one fixed turn-based convention, with embeddings required to preserve source-model observation/action order;

2. an explicit environment/tick/no-op action to expose autonomous arrivals before the next decision;

3. a slightly richer step type distinguishing environment events from action responses.

Do not add structure unless needed.

Prove or counterexample the claim that the current one-response-per-action interface can preserve the relevant SCD online information structure.

At minimum, do not claim a coding equivalence merely because objective values on fixed schedules agree.

Add a finite counterexample if differing arrival/action order can change the online optimal policy.

If a no-op/tick encoding repairs this exactly, demonstrate it.

# 5. Environment semantics

The current public environment is:

    Gamma : H x A -> P+(Y)

and hidden state is demoted to representation.

Recheck this decision after the timing pass.

In particular:

- Does every finite-state game/environment used by the serviceability solver induce an observational Gamma cleanly?
- Can two hidden states with the same observable history but different future possibilities be represented without losing information?
- If not, does Gamma already encode the union of possibilities and therefore exactly capture the adversarial observable semantics?
- Does that change strategy semantics relative to a fixed hidden-state environment?

The prior ISSC analysis already uses a “consistency adversary” construction. Generalize the lesson if appropriate.

State explicitly whether `Gamma` represents:

    epistemically possible responses from the current public history

rather than:

    the true hidden transition dynamics.

This distinction may be conceptually important.

# 6. Serviceability definitions

Audit:

    Servable(d,h)
    JointlyServable(D,h)
    Schedulable(...)

against the cleaned certification semantics.

If serviceability currently targets `Monitor.accepting`, determine whether that means:

    eventual historical valid certificate

or

    eventual valid present closure.

For perishable/freshness-sensitive obligations, these differ.

This may change the overload discussion.

In particular, revisit the current claim:

    overload refutes eventual service for perishable specs.

Under the historical-validity / current-closure distinction, formulate precisely whether overload causes failure of:

    historical service,
    timely service,
    closure admissibility,
    deadline satisfaction,
    eventual account.

Do not use “service” ambiguously.

Try to produce a clean lattice of notions, perhaps:

    ever-certifiable
    forceably certifiable
    timely closable
    eventually closed
    bounded-latency serviced

but keep only distinctions that survive actual examples.

# 7. Reason-representation compatibility pass

PR #51 was developed independently of the reason-state branch, so now perform a conceptual compatibility audit without consuming or depending on any concurrent unmerged branch.

Use only the following stipulated frozen reason interface:

    reason sources are V ⊔ L

    occurrence:
        e = (id, sources, target, applied_as)

    sources may cite immutable transcript receipts in L.

The intended composition is:

    InquiryLiability
        -> CIS interaction
        -> receipts E ⊆ L + procedural ServiceCertificate
        -> assessment
        -> new reason occurrences whose sources may cite E.

Press on whether PR #51's handoff supports this exactly.

## Core question

Should a reason ever need to cite the ServiceCertificate itself?

Strong hypothesis:

    no.

The certificate answers:

    “Was the owed investigation adequately performed?”

The reason occurrence answers:

    “What bears on proposition v?”

Those are different provenance relations.

Test cases:

1. Service certificate is valid but evidence supports neither p nor not-p.
2. Same receipt set supports different conclusions under different `App` judgments.
3. A ServiceOutcome is procedurally valid but assessment returns `NoBearing`.
4. Two inquiry liabilities share evidence but assessment mints only one reason occurrence.
5. A claim like “this experiment followed protocol P” is epistemically relevant.

For case 5, determine whether it can be represented as an ordinary content in V supported by receipts, rather than extending reason sources to include record/certificate objects.

The cleanup should explicitly state one of:

    V ⊔ L remains sufficient for the reason waist

or

    concrete counterexample requires another source sort.

Do not alter the reason representation in this PR.

If you find an expressivity failure, document it as a blocking interface issue.

# 8. Three provenance relations

See whether the cleaned architecture supports the distinction:

    evidential grounds
    procedural service adequacy
    normative/accounting license

These should normally live in:

    reason occurrence sources
    ServiceCertificate
    normative record / account graph

respectively.

Construct one microhistory in which all three differ.

Example shape:

- normative record requires investigation d;
- controller performs actions;
- certificate k shows d was adequately serviced;
- receipts l1,l2 are passed to assessment;
- assessment mints e : {l1,l2,v} -> p;
- record closes/accounts d using k;
- e itself does not cite k as an epistemic ground.

If this works, make it the canonical composition fixture.

# 9. Recheck prior-art claims after semantic cleanup

Do not redo the entire literature review.

Audit only whether the certification/timing corrections alter the current claims for:

- Set Cover with Delay
- Submodular Ranking / MLSC
- Adaptive Submodularity
- Interactive Submodular Set Cover
- Request-Response games.

Questions:

- Does SCD embedding require a specific event-order convention?
- Is Golovin–Krause coverage genuinely existential learner-visible certification, or should the memo use more careful terminology?
- Does ISSC's semantic/certified distinction still hold under the cleaned types?
- Does RR correspond to historical service, timely closure, or just eventual response?

Update claims conservatively.

# 10. Check the capability lattice for accidental semantics

Audit each current capability:

    ResponseIrrelevant
    OrderIrrelevant
    RepetitionIrrelevant
    FixedIncidence
    MonotoneProgress
    SubmodularProgress
    FiniteStateEnvironment
    FiniteStateServiceMonitor
    FixedRealization
    KnownPrior
    AdaptiveMonotone
    AdaptiveSubmodular
    SelfCertifying
    ConsistentAdversarialResponses
    CoalescingRequests
    MonotoneEvidence

For each:

- is it genuinely a property of the service/environment object?
- is it instead a property of a particular objective annotation?
- is it a property of the prover?
- is it a property of closure/account policy?
- does it unlock the stated theorem?

Demote/move/delete anything typed at the wrong layer.

The goal is not to maximize the number of capabilities.

# 11. Inspect implementation for semantic-vs-testing artifacts

The current reference implementation contains several conveniences that may accidentally be presented as semantics.

Audit especially:

    ServiceSpec.make_cert
    ServiceSpec.certified
    Monitor with absorbing acceptance
    transcript indexing
    FiniteStateEnv.state_after
    forced_reach
    order_irrelevant
    repetition_irrelevant
    fixed_realization_family

Distinguish:

- semantic definition;
- decision procedure;
- finite testing helper;
- implementation convenience.

Do not let finite implementations define the abstract notion unless intentionally justified.

For example, an absorbing monitor may encode “historical certification has occurred” even if the live freshness predicate later fails. That may actually be the right implementation after cleanup.

# 12. Required final artifact

Add a focused follow-up note, e.g.

    CERTIFICATION_CLEANUP.md

or integrate the results cleanly into existing round documents.

The closeout must state:

## A. Certification verdict

Choose one:

    ORIGINAL-CERTIFICATION-SEMANTICS-SOUND
    SPLIT-VALIDITY-AND-CLOSURE
    CITATION-LOCALITY-REVISED
    OTHER

Explain exactly why.

## B. Environment timing verdict

Choose one:

    CURRENT-TURN-MODEL-SUFFICIENT
    CURRENT-TURN-MODEL-SUFFICIENT-WITH-CONVENTION
    REQUIRES-EXPLICIT-EXOGENOUS-EVENTS

## C. Reason-waist compatibility verdict

Choose one:

    CLEAN-COMPOSITION
    CLEAN-WITH-OPAQUE-HANDOFF-REVISION
    SOURCE-TYPE-MISMATCH

## D. CIS overall verdict

Does PR #51 remain:

    REQUIRES-REVISION — SURVIVES

or does this pass force a stronger change?

# 13. Tests

Add/update tests covering at minimum:

- historical certificate persistence;
- prover incompleteness vs existential certificate validity;
- freshness/current closure;
- contradictory later evidence;
- online arrival/action ordering;
- canonical three-provenance composition fixture;
- reason-waist source-type compatibility;
- all previously green microcases.

Run:

    python3 tests/run.py

for the round and repo-level tests required by governance.

If CI exists for the branch, ensure it is green.

# 14. Scope discipline

Do NOT:

- redesign the full inquiry loop;
- build assessment theory;
- modify the frozen reason representation;
- build action selection / decision theory;
- add EU securities;
- alter legitimacy/counterfactual theory;
- pursue scheduler optimality beyond what is needed to clarify semantics;
- register new claims unless repo governance explicitly requires it.

This is a semantic prosecution and cleanup pass.

# 15. Stop rule

Stop when:

1. certification semantics are unambiguous;
2. event timing is explicitly typed;
3. the reason-state handoff has survived or failed a concrete compatibility test;
4. the capability lattice has been cleaned of type errors;
5. the prior-art claims have been minimally audited;
6. all tests pass;
7. PR #51 contains a crisp revised closeout.

Do not continue to the next inquiry research problem.
