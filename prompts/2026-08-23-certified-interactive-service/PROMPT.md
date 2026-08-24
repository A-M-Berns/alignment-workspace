You are running a self-contained research round in the alignment-workspace repo.

Your task is to prosecute a candidate mathematical abstraction for bounded inquiry:

    CERTIFIED INTERACTIVE SERVICE

The central question is:

Does there exist a minimal, non-vacuous interactive-service interface that

1. exactly embeds the important set-cover/submodular/adaptive inquiry models;
2. handles interactive, non-submodular, interventionist, and multiplicity-bearing inquiry cases needed by a bounded normative learner;
3. supports meaningful notions of serviceability, joint serviceability, liveness, scheduling, and certification;
4. composes cleanly between an upstream normative-record layer that generates inquiry liabilities and a downstream assessment layer that turns serviced evidence into reasons?

Do not assume the answer is yes. The round may conclude that the abstraction is too general, incorrectly typed, or at the wrong architectural boundary.

## Independence / concurrency constraint

Other research threads are running concurrently.

This round MUST be independent of them.

- Create a fresh branch for this round.
- Do not depend on any unmerged branch, PR, or result from another current agent.
- Do not edit shared high-level architecture/wiki files unless absolutely required.
- Prefer a new isolated round directory and self-contained implementation/tests/notes.
- Do not merge, rebase onto, or otherwise consume concurrent work.
- Treat the interface summary below as the complete upstream/downstream contract needed for this investigation.
- If the live default branch lacks some object described below, model the minimum local stub needed inside this round rather than reaching into another branch.
- End in a PR containing only this round's work.
- Do not proceed into the next research problem after finishing this one.

The point is that this PR should remain intelligible and useful even if every other current research thread is abandoned.

# I. Architectural boundary supplied to this round

The larger learner has approximately these conceptual layers:

    normative record
        ↓
    inquiry liability
        ↓
    [THIS ROUND: interactive service]
        ↓
    certified evidence / interaction receipts
        ↓
    assessment
        ↓
    reason occurrences
        ↓
    accountable stance review

This round ONLY owns the middle service layer.

An inquiry-service object must NOT decide:

- why an inquiry is normatively owed;
- whether some issue should become Due;
- what observed evidence means;
- which propositions should be believed;
- whether a stance should change;
- whether a reason is normatively decisive.

Those belong upstream or downstream.

The intended slogan is:

    The record says what investigation is owed.
    Interactive service determines how that investigation can be carried out and certified.
    Assessment says what the resulting evidence bears on.

The service abstraction should be able to consume inquiry liabilities from multiple sources — e.g. answerability-generated inquiries and decision-relevance-generated inquiries — without caring why they were generated.

# II. Frozen assumptions about surrounding learner

You may treat the following as axiomatic for this round.

There is an append-only transcript L of identity-bearing interaction receipts.

There is an append-only reason ledger R, but the service layer should ideally not need to know its internal structure.

There is a current stance B and normative record N, but again the service layer should see at most opaque identifiers / liability data supplied by N.

A record-side inquiry liability is identity-bearing and pins the service specification under which it was undertaken.

Distinct liability occurrences with extensionally identical task content remain distinct historical objects.

Evidence may be shared between liabilities, but shared evidence does not by itself collapse their identities or accounting.

Once a historical service event is validly certified against its pinned specification, subsequent cognitive revision does not make that service event historically unperformed. Later evidence may generate review, but not rewrite history.

Do not redesign the reason representation, stance semantics, authority genealogy, or general legitimacy theory.

# III. Candidate generic object — treat as conjectural

Start from, but do not blindly preserve, something like:

    I = (A, Y, Γ, Σ, Check, cost)

where:

- A is an action space;
- Y is an observable response/output space;
- H is the type of finite observable interaction histories;
- Γ is an environment response interface, tentatively

      Γ : H × A → P₊(Y*)

  so that after history h and action a, the environment may return any permitted observable response y ∈ Γ(h,a);

- Σ is a space of pinned ServiceSpecs;
- for σ ∈ Σ, C_σ is a certificate type and

      Check_σ : H × C_σ → Bool

  determines whether the observable interaction trace plus certificate establishes that σ has been adequately serviced;

- costs/resources may optionally be represented by something like

      cost : H × A → R_≥0.

Dynamic identity-bearing liabilities are tentatively supplied EXTERNALLY by the normative record rather than built into I:

    d = (id, accruedAt, σ_d, ...).

Do not assume this is the correct minimal interface.

Try to delete, weaken, factor, or replace every component.

In particular investigate:

1. Should Γ be history-dependent, state-based, stochastic, relational, or some combination?
2. Is hidden world state part of the public interface, or merely a representation of Γ?
3. Do we need Y* per action or only one response event Y?
4. Is cost core structure or structure on optimization problems over the core?
5. Is ServiceSpec extensionally an accepting trace language?
6. Is a finite-state monitor merely an implementation of ServiceSpec?
7. Is proof-relevant certification actually necessary?
8. Should certification be distinguished from hidden/semantic goal achievement?
9. Which interface laws are required to stop the object from becoming “arbitrary games with arbitrary acceptance predicates”?

# IV. Important distinction: semantic success vs certification

Press very hard on:

    semantic success
    ≠
    learner-visible certified service
    ≠
    efficient service.

For some prior-art models, an omniscient evaluator may know an objective has been achieved under the true hidden realization while the observation history does not establish this to the learner.

Our normative record can only close an inquiry on an appropriate finite record-visible certificate.

Investigate whether the generic object should contain a hidden semantic objective at all.

Current suspicion:

- observable certification belongs in the core;
- hidden semantic success is optional analytical structure attached to some models, not primitive service structure.

If appropriate, formulate soundness relations such as:

    Check_σ(h,c)
      ⇒ Goal_σ(h,w)

for every hidden state/realization compatible with h.

But do not force every ServiceSpec to have a hidden-world Goal. Purely procedural service specs are allowed.

# V. Search/review mathematical prior art

The round should inspect and accurately compare at least:

1. Set Cover with Delay
   Yossi Azar, Ashish Chiplunkar, Shay Kutten, Noam Touitou,
   “Set Cover with Delay—Clairvoyance Is Not Required.”

2. Submodular Ranking / Minimum Latency Submodular Cover
   Sungjin Im, Viswanath Nagarajan, Ruben van der Zwaan,
   “Minimum Latency Submodular Cover.”
   Also inspect the directly relevant submodular-ranking formulation if useful.

3. Adaptive Submodularity
   Daniel Golovin, Andreas Krause,
   “Adaptive Submodularity: Theory and Applications in Active Learning and Stochastic Optimization.”

4. Interactive Submodular Set Cover
   Andrew Guillory, Jeff Bilmes,
   “Interactive Submodular Set Cover.”

5. Request-Response games
   Florian Horn, Wolfgang Thomas, Nico Wallmeier, Martin Zimmermann,
   “Optimal Strategy Synthesis for Request-Response Games.”
   A copy may be available in the conversation/workspace. Inspect the actual paper, especially:
   - definition of request-response conditions;
   - treatment of repeated requests while one request of the same type is open;
   - waiting-time state;
   - finite-state memory reduction;
   - relation to Büchi;
   - quantitative waiting-time objective.

Use primary sources.

Do not assume that request-response games occupy exactly the same abstraction relation as the submodular models. Determine it.

# VI. Exact embedding program

The strongest desired result of the round is not “these models feel similar.”

For each prior object, try to define an explicit translation into the proposed generic service interface and state/prove an objective-preservation result.

## A. Set Cover with Delay

Given task kinds E, purchasable sets/actions, costs, request arrivals, and delay functions, construct an interactive-service instance.

Try to establish exact preservation of:

- request identity;
- service time;
- action/purchase cost;
- delay cost;
- total objective.

Determine precisely which restrictions on the generic object characterize this subclass.

Expected rough shape:

    response irrelevance
    + fixed action→covered-task incidence
    + dynamic arrivals
    + action costs
    + per-request delay.

Do not assume past actions service future arrivals unless the source model does.

## B. Submodular Ranking / MLSC

Given normalized monotone submodular functions

    f_i : 2^A → [0,1],

construct ServiceSpecs satisfying

    Certified_i(h) ↔ f_i(S(h)) = 1

where S(h) is the relevant set/order/path of actions.

Prove equality of cover/service times in the restricted model.

Be exact about the distinction between:

- unit-cost ordering;
- metric path length;
- intrinsic action costs;
- repeated actions.

Identify which assumptions are needed to get submodular ranking versus MLSC.

## C. Adaptive Submodularity

Embed:

- finite item set;
- fixed realization φ;
- known prior;
- partial realization ψ;
- observation of item state after selection;
- adaptive utility/coverage objective.

Show how partial realizations correspond to observable interaction histories.

Then identify as EXTRA CAPABILITIES, not generic assumptions:

    FixedRealization
    Prior
    AdaptiveMonotonicity
    AdaptiveSubmodularity
    SelfCertification (where appropriate).

Test carefully the distinction between actual goal achievement and observation-visible certification.

## D. Interactive Submodular Set Cover

Embed:

- finite hidden hypothesis class H;
- query set;
- known query→valid-response relation;
- adversarial response consistent with hidden target;
- pointwise submodular progress/objective.

Try to express this directly through Γ.

Again isolate all extra assumptions:
- fixed target;
- known hypothesis class;
- noiseless consistency;
- fixed response relation;
- pointwise submodularity.

## E. Request-Response games

Do NOT assume this is simply another nested subclass in exactly the same sense.

Determine whether:

1. RR games embed into the generic interactive-service game;
2. some finite-state fragment of our object compiles into RR;
3. the two are merely overlapping abstractions.

Pay special attention to the paper's feature that while a request of type j is already open, additional requests of type j are ignored / coalesced.

Our target learner has identity-bearing liability occurrences, so this may be a genuine expressive mismatch.

Try to state an exact restricted theorem of roughly this form if correct:

    finite environment
    + finitely many service types
    + finite-state service monitors
    + coalescing/idempotent outstanding requests per type
      ⇒ compilation to finite RR game.

And determine what breaks this compilation:
- multiple simultaneously outstanding same-type liability identities;
- per-occurrence pinned specifications;
- unbounded certificate/monitor state;
- dynamic heterogeneous liabilities;
- richer cost/resource objectives.

Also examine whether generalized reachability or request-response games give a cleaner qualitative liveness characterization for fixed finite dockets / recurrent task types.

# VII. Search for the non-vacuous middle abstraction

A completely arbitrary history-dependent acceptance predicate is too weak scientifically.

Identify candidate CORE LAWS that:

- are broad enough for our inquiry use cases;
- are satisfied by the important prior embeddings;
- give the abstraction real content.

Investigate at least:

### Finite-witness certification

Successful service admits a finite, record-visible certificate.

### Prefix persistence

If a historical inquiry is certified at h, extending the trace does not make that historical service event uncertified:

    Certified_σ(h)
      ⇒
    Certified_σ(hh').

If this needs qualification, formulate the correct occurrence-relative property.

### Observation locality

The service checker cannot inspect hidden world state unavailable to the learner.

### Pinned service specification

Liability d is checked against σ_d, the service specification bound at undertaking/accrual, unless an explicit upstream record action migrates it.

### Interpretation separation

The service checker certifies adequacy of investigation/evidence collection; it does not directly mutate B or assert object-language claims by fiat.

Attack each candidate law with counterexamples.

Do not retain a law merely because it sounds philosophically desirable.

# VIII. Core mathematical predicates

Try to define the following cleanly.

## Individual serviceability

For liability d at observable history h:

    Servable(d,h)

should roughly mean that there exists an inquiry policy which forces eventual certified service against every allowed environment response sequence.

Something like:

    ∃π ∀ρ ∈ Runs(Γ,π,h)
        ∃t,c
            Check_{σ_d}(ρ≤t,c).

Be precise about fairness assumptions, infinite branching, nontermination, randomized policies, etc. Keep the base version as simple as possible.

## Joint serviceability

Define:

    JointlyServable(D,h)

for a finite set/multiset of identity-bearing liabilities.

Construct a finite witness showing:

    (∀d∈D Servable(d,h))
        ⇏
    JointlyServable(D,h)

if this is indeed true under bounded resources.

## Dynamic schedulability

Separate the above from an arrival-stream notion such as

    Schedulable(A_class, Γ, resources).

The previous inquiry work found that unconditional eventual service is false under arbitrary overload: even individually serviceable jobs can arrive faster than capacity.

Reproduce or improve this kind of counterexample in the new formalism.

Do not conflate:
- individual feasibility;
- finite-docket joint feasibility;
- recurrent/dynamic schedulability;
- low cost;
- low latency;
- no starvation.

# IX. Mandatory adversarial microcases

The proposed interface must express all of these cleanly without importing new normative primitives.

Implement/test each.

1. COMPLEMENTARITY

Neither action alone services the inquiry:

    a insufficient
    b insufficient
    {a,b} sufficient.

Show why this lies outside a submodular-progress subclass if appropriate but remains valid generic service.

2. RESPONSE-DEPENDENT BRANCHING

Run action a.
If response y1, next useful action is b.
If response y2, next useful action is c.

3. INTERVENTION / NON-FIXED REALIZATION

An inquiry action changes what a later action will observe.

This should remain expressible while falling outside ordinary fixed-realization adaptive-submodular modeling.

4. SHARED EVIDENCE

One interaction receipt can appear in service certificates for d1 and d2, but d1 ≠ d2 remain distinct liabilities requiring separate account closure upstream.

5. SAME-TYPE MULTIPLICITY

Two simultaneously open occurrences carry the same ServiceSpec.

Test whether one service trace:
- can certify both;
- can certify one but not the other;
depending on the specs/account assumptions.

Do not silently coalesce them.

6. HIDDEN SUCCESS WITHOUT CERTIFICATION

The true hidden environment happens to satisfy some semantic goal, but no learner-visible certificate establishes it.

The service layer must not certify closure solely from inaccessible truth.

7. OVERLOAD

Every arriving liability is individually serviceable, but arrivals exceed available service capacity.

Show failure of unconditional dynamic liveness.

8. ORDER SENSITIVITY

a;b services a liability but b;a does not.

This should be expressible even though ordinary set-function models forget order.

9. REPETITION SENSITIVITY

Performing action a twice can matter differently from performing it once.

This tests whether service histories can be reduced to sets of visited actions.

10. ADVERSARIAL RESPONSE

Environment can choose among multiple permitted outputs, and the service controller needs a strategy, not a static action set.

# X. Structural capability taxonomy

If the generic object survives, define properties/capabilities rather than forcing instances into a rigid disjoint subtype tree.

Candidates:

    ResponseIrrelevant
    OrderIrrelevant
    RepetitionIrrelevant
    FixedIncidence
    SetFactorizing
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
    FiniteRequestTypes
    CoalescingRequests

For each useful capability, say:

- exact definition;
- which prior model assumes it;
- which theorem/algorithm it potentially unlocks;
- which mandatory microcases violate it.

Avoid capability proliferation if several notions can be cleanly compressed.

# XI. Composition test with normative learner

Without implementing the surrounding theory, create one minimal end-to-end fixture demonstrating the boundary:

    upstream Due/InquiryLiability
        ↓
    service controller
        ↓
    action
        ↓
    environment response
        ↓
    immutable receipt(s)
        ↓
    ServiceCert
        ↓
    downstream opaque Assess handoff.

The service layer must not need to inspect or mutate:
- stance B;
- reason ledger internals;
- authority genealogy.

Conversely, the downstream assessment stub must not need:
- Γ internals;
- scheduling policy internals;
- submodularity assumptions.

Also create two origin cases:

1. an answerability-generated inquiry;
2. a decision-relevance-generated inquiry.

They should become indistinguishable to the service layer after both are converted upstream into InquiryLiability objects.

This is an important architecture test.

# XII. Theorem targets

Do not overclaim. Seek the strongest correct versions of things like:

### Embedding theorems
Each selected prior object maps exactly into the generic interface with objective/service-time preservation.

### Finite-monitor game theorem
Under finite environment + finite service monitor hypotheses, serviceability is reducible to a finite game objective.

Determine whether the correct target is reachability, generalized reachability, request-response, Büchi, or something else.

### Restricted RR compilation
Under explicit coalescing finite-type assumptions, recurrent certified service compiles to an RR game.

### No-silent-loss / certificate persistence
A valid service certificate against a pinned historical service spec remains a valid record of that historical service under trace extension.

### Feasibility separation
Individual serviceability does not imply dynamic schedulability.

If stronger results fail, provide minimal counterexamples.

# XIII. Implementation / evidence discipline

Build a small executable reference model sufficient to test the interfaces and adversarial examples.

Prefer:
- tiny finite instances;
- explicit exhaustive enumeration where feasible;
- exact arithmetic;
- transparent traces and certificates.

Do not confuse finite test evidence with a mathematical proof.

For every important claim, label it as one of:

- DEFINITION
- DERIVED / proved on paper
- FINITE-TEST-SUPPORTED
- COUNTEREXAMPLE
- CONJECTURE
- OPEN.

If there is an existing claim-registration or evidence discipline in the default branch, follow it without modifying unrelated infrastructure.

# XIV. Deliverables

Create an isolated round directory containing at least:

1. `README.md`
   - round question;
   - final verdict;
   - concise object/interface;
   - map of results.

2. `INTERACTIVE_SERVICE_INTERFACE.md`
   - exact types;
   - core laws;
   - what is intentionally excluded;
   - minimality/subtraction analysis.

3. `PRIOR_ART_EMBEDDINGS.md`
   - Set Cover with Delay;
   - submodular ranking / MLSC;
   - adaptive submodularity;
   - interactive submodular set cover;
   - request-response games;
   - explicit translations;
   - exact preservation claims;
   - mismatches.

4. `SERVICEABILITY.md`
   - Servable;
   - JointlyServable;
   - dynamic schedulability;
   - liveness/fairness/load distinctions;
   - theorem/counterexample results.

5. executable model/tests
   - all mandatory adversarial microcases;
   - embedding sanity tests where finite examples suffice.

6. `HANDOFF.md`
   State exactly what an upstream record layer must provide and what a downstream assessment layer receives.

7. `OPEN_QUESTIONS.md`
   Only genuine remaining questions; do not turn this into a new speculative agenda.

# XV. Required final verdict

Choose exactly one headline verdict:

    SURVIVES
    TOO-GENERAL
    WRONG-WAIST
    REQUIRES-REVISION

If `SURVIVES`, state the smallest surviving interface.

If `REQUIRES-REVISION`, state exactly what was changed and why.

If `TOO-GENERAL`, identify where mathematical content disappears.

If `WRONG-WAIST`, identify which necessary information crosses the proposed architectural boundary.

Also answer explicitly:

1. Can we honestly say this object generalizes Set Cover with Delay?
2. Can we honestly say it generalizes submodular ranking / MLSC?
3. Can we honestly say it generalizes adaptive submodular coverage?
4. Can we honestly say it generalizes Interactive Submodular Set Cover?
5. What is its exact relationship to Request-Response games?
6. Is certification genuinely load-bearing?
7. Is hidden environment state part of the public interface?
8. What is the weakest useful set of core laws?
9. What structural capability is actually responsible for each imported algorithmic guarantee?
10. Does the service abstraction compose cleanly with the stipulated normative-learner boundary?

# XVI. Stop rule

Once you have:

- prosecuted the candidate interface by subtraction;
- checked the primary prior art;
- constructed the exact embeddings or found their failures;
- run the adversarial microcases;
- stated the serviceability/liveness distinctions;
- made the final verdict;
- opened the PR;

STOP.

Do not start building the full inquiry/coverage theory.
Do not redesign the normative record.
Do not redesign reason representation.
Do not develop decision theory or expected-utility securities.
Do not pursue traderization.
Do not consume or alter concurrent research threads.

The purpose of this round is only to determine whether Certified Interactive Service is a real mathematical narrow waist for the service portion of inquiry.
