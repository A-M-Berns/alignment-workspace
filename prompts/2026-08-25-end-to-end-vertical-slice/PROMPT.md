You are working inside the alignment-workspace repository.

Your task is to build and adversarially test the FIRST END-TO-END VERTICAL SLICE
of the legitimacy / normative-learning architecture, while treating the current
VALUE WAIST and OPERATIVE WAIST as serious but still somewhat untested
hypotheses.

This is not merely an implementation task.

The purpose of the end-to-end work is to force the architecture into one running
formal object and use the resulting pressure to determine whether the current
value/operative waists are actually the right narrow interfaces.

Do not prematurely freeze them.
Do not redesign them casually either.

The target is:

    upstream normative practice
      -> settlement / reasons / normative standing
      -> value exposure + operative injunctions
      -> LI-facing quantitative cognition
      -> normative price-region K^N
      -> composition with deductive region K^D
      -> traderized enforcement
      -> resulting LI cognitive state

and, if feasible in this pass, begin exposing the return path from resulting
cognitive state / conflict / outcomes back toward pressure and inquiry.

# Governing research posture

We are now CLOSE TO END-TO-END.

Reflective Integrity is comparatively mature and should be treated as
stable/frozen unless a genuine incompatibility is discovered.

By contrast, the VALUE WAIST and OPERATIVE WAIST are promising but still
under-tested.

Current hypotheses:

    VALUES EXPOSE CERTIFIED LUVS.

    INJUNCTIONS CONSTRAIN PROBABILITIES AND LUV EXPECTATIONS.

    THOSE CONSTRAINTS COMPILE BACK TO ORDINARY LI PRICE GEOMETRY.

    TRADERIZATION REALIZES THE RESULT WHEN ITS ACTUAL MATHEMATICAL
    HYPOTHESES ARE SATISFIED.

The goal of this pass is to see whether one exact end-to-end dynamics can be
built using these interfaces without hidden semantic cheats, ad hoc glue, or
unnecessary new ontology.

The long-run benchmark remains:

    same formal core
      + exact synthetic toy dynamics
      + genuinely rich real normative practice
      + positive learning theorem

This pass is primarily about the first two terms needed to make that benchmark
credible:
- one exact synthetic dynamics;
- enough architectural confidence that the SAME waists are worth taking to real
  normative practice.

# 0. First inspect the live repository

Before designing or coding:

1. Read the current Reflective Integrity implementation/spec/tests.
2. Read the current V / reason-expression / object-language machinery.
3. Read the current Logical Induction / FAF formalization relevant to:
   - language/signature;
   - sentence pricing;
   - LUVs;
   - LUV expectations;
   - threshold formulas;
   - future-price/self-reference machinery if present.
4. Read the current traderization / constraint / liability work.
5. Identify current representations of:
   - deductive region K^D;
   - market price spaces/signatures;
   - affine constraints;
   - effective separation;
   - tolerance / liability / enforceability assumptions.
6. Produce a short internal dependency map before changing anything.

Prefer reuse over parallel abstractions.

# 1. Stable upstream architecture

Treat the persistent normative state conceptually as:

    S_t = (L_t, R_t, N_t)

with the following distinctions preserved:

    settlement
      !=
    reason occurrence
      !=
    normative uptake / standing
      !=
    operative force

Normative standing changes through explicit valid NormEvents.

Historical reference must remain rigid.

Do not reopen RI merely because a downstream API would be easier with a
different design.

If the downstream layer really exposes an RI defect, isolate the counterexample
precisely.

# 2. Relationship between upstream V and LI language L

There is a rich upstream reason/object language V and a formal Logical Induction
language L.

Do NOT assume:

    V = L

and do NOT treat them as unrelated free parameters.

Current hypothesis:

    L ∈ Ext(L_min(V))

i.e. fixing V / the RI signature determines a minimum representation package
that the LI language must be able to encode, while L may additionally contain
arbitrary mathematical, empirical, application, reflective, etc. vocabulary.

Important distinction:

    ability to quote / code / reason ABOUT r ∈ V
      !=
    existence of an LI sentence whose propositional meaning IS r.

A rich or open-textured reason may remain an opaque historical/normative object
while still being rigidly represented inside L.

Please make this relationship as formal as the existing code permits.

Questions to test:

- What exactly must L_min(V) contain?
- Is ordinary effective coding enough?
- Which RI relations need internal representation?
- Does V-extension induce a natural conservative extension of L_min?
- Which of these facts belong to the object theory Γ versus metatheory?

Do not overengineer this unless end-to-end execution demands more.

# 3. Candidate value waist — still provisional

Candidate standing extension:

    PValue(v)

where v is a frozen historical value specification.

The candidate narrow waist is:

    compileValue :
      ValueSpecCode × QueryCode
        ⇀ CertifiedLUV

with CertifiedLUV grounded as directly as possible in the ACTUAL Logical
Induction definition of a bounded LUV.

Do not invent new generalized securities unless LUVs fail.

Interpretation:

A rich value specification need not itself be a utility function or a scalar
object.

It may expose particular bounded evaluative observables as LUVs.

Examples to test with the SAME interface:

- scalar policy value;
- stakeholder-specific value;
- several dimensions of plural value;
- lower/upper value estimates for incomplete value specification;
- value of information;
- surrogate-goal value;
- future endorsement;
- references to a superseded historical value specification;
- if supported by LI, reflective/future-price-defined quantities.

Important principle:

    rich value may outrun quantification.

If a query cannot yet be compiled to a legitimate LUV, that should be a
representable non-exposure state, not a failure of the architecture.

Historical rigidity:

If:

    v0 -> v1

then any already-defined X_{v0,q} retains its meaning.

Do NOT silently reinterpret historical value quantities through v1.

Multiple active value specifications should be allowed unless concrete dynamics
reveal a reason not to.

# 4. Candidate LI-facing cognitive waist — still provisional

Current candidate:

    CognitiveQuantity :=
      Prob(phi)
      | Expect(X)

where:

    phi ∈ Sent(L)

and X is a certified bounded LUV.

Semantics at day n:

    [[Prob(phi)]]_n = P_n(phi)

    [[Expect(X)]]_n = E_n(X)

Use the exact existing LI definition of E_n(X).

The point is that Expect(X) is a DERIVED cognitive coordinate, not necessarily a
primitive new asset.

Test whether this is actually sufficient as the first common quantitative
language.

The operative layer should not care where X came from.

A value-generated X and an ordinary LI LUV should be interchangeable downstream
if both satisfy the same LUV interface.

# 5. Candidate operative waist — still provisional

Candidate standing extension:

    PInjunction(J)

An injunction is operational-only.

It should have exact market-facing semantics.

It is not merely:
- a commitment;
- principle;
- reason;
- aspiration;
- recommendation.

Its payload should contain frozen operative terms only.

Why it was issued should be recovered through:

    injunction id
      -> issuing NormEvent
      -> authority / certificate / reasons / derivation

Do not redundantly encode justification into the injunction unless required by
an invariant.

Do not use diachronic predecessor links as justificatory links.

Changing:
- active values;
- reasons;
- schemas;
- commitments;
- interpretations

must not silently rewrite an existing injunction.

If operative force should change, require an explicit new normative event.

# 6. First injunction language to test

Start with:

    InjunctionTerms =
      finite rational affine inequalities over CognitiveQuantity

For example:

    2 Expect(X) - Prob(phi) + Expect(Y) <= 0.7

At day n, compile:

    kappa_n :
      InjunctionTerms
        -> rational affine constraints over ordinary LI sentence prices

using the standard finite-day LUV expectation representation.

This is a key pressure point.

The injunction syntax is frozen, but the low-level threshold realization of
E_n(X) may vary with n.

Determine whether this gives a coherent notion of semantic rigidity.

Do not just assert that it does.

Build an explicit multi-day example and inspect the generated constraints.

# 7. Operative projection

The intended N -> O projection should remain intentionally boring:

    O_n =
      {(i,J_i) :
         i is active standing carrying PInjunction(J_i)}

Then:

    K_{i,n} = [[kappa_n(J_i)]]

and:

    K_n^N = intersection_i K_{i,n}

Do not:
- reinterpret reasons;
- substitute current values for historical references;
- optimize away an injunction;
- weaken constraints to preserve feasibility;
- prioritize conflicts silently.

The output is just the region currently demanded by operative normative
standing.

# 8. Conflict

Make at least these states explicit:

A. malformed / internally inconsistent single injunction;

B. individually consistent active injunctions whose intersection is empty:

       K_n^N = empty

C. normatively consistent region incompatible with deduction:

       K_n^N != empty
       K_n^D != empty
       K_n^N ∩ K_n^D = empty

The first implementation should detect/certify these states, not solve the
jurisprudence of conflict.

For affine/polyhedral constraints, investigate whether finite infeasibility
certificates can carry provenance back to the specific active injunction terms.

# 9. Deductive composition

Keep the two channels independent:

    deduction -> K_n^D

    operative normativity -> K_n^N

and compose only at:

    K_n = K_n^D ∩ K_n^N

Do not contaminate the deductive semantics with normative concepts.

Do not embed logical consistency rules inside PInjunction.

# 10. Traderization

This is the execution boundary.

The operative layer chooses WHAT region is in force.

Traderization determines WHETHER/HOW the requested region can be imposed while
preserving the relevant LI guarantees.

Do not put into injunction semantics:
- funding;
- enforcement budget;
- intensity;
- tolerance;
- liability;
- risk capital.

Inspect the existing traderization mathematics and replace vague language such
as:

    Traderizable(K)

with the strongest exact interface currently supported.

In particular test the actual end-to-end generated K_n schedule against:
- effectiveness;
- changing dimension/signature;
- convexity/closedness;
- separation;
- nonemptiness;
- margin/interior conditions if required;
- tolerance schedules;
- oscillation / diachronic liability;
- interaction with LUV expectation compilation.

This is one of the most important outputs.

# 11. Build ONE narrative end-to-end toy

If possible, build a single exact toy trajectory where every important
distinction is visible.

Do NOT merely connect types.

The toy should be hand-inspectable and should contain at least the following
narrative.

## Stage A: initial state

Start from a thin seed.

Introduce:

    PValue(v0)

and:

    PInjunction(J0)

where v0 exposes a LUV:

    (v0,q) -> X0

and J0 constrains:

    Expect(X0)

possibly along with one ordinary proposition probability.

Compile J0 to:

    K_0^N

compose with a tiny:

    K_0^D

and pass the resulting region through the existing traderization/enforcement
interface.

Record the resulting relevant price/cognitive state.

## Stage B: feedback and value revision

Produce an explicit world/inquiry settlement.

Route it through:

    L -> R -> NormEvent

so that:

    v0 is superseded by v1

and:

    PValue(v1)

becomes active.

Have:

    (v1,q) -> X1

Crucially, DO NOT revise J0 automatically.

J0 should still refer rigidly to X0.

Demonstrate:

    value revision
      !=
    operative revision

as an actual state-transition fact, not only prose.

## Stage C: explicit operative revision

Use a later explicit normative event to supersede / replace J0 with:

    J1

which refers to X1.

Only then should the operative region change for that reason.

Show the complete provenance:

    new reason
      -> NormEvent
      -> new injunction standing
      -> O_n
      -> compiled K_n^N
      -> enforcement effect

This should be the canonical first full-stack trajectory.

# 12. Add adversarial variants of the toy

After the happy path works, mutate the same setup to test:

- two active value specs;
- an old active injunction referencing superseded v0;
- failed ValueQuery -> no LUV exposure;
- several LUVs representing plural values;
- affine tradeoff between value dimensions;
- mixed Prob(phi)/Expect(X) injunction;
- two active injunctions with empty intersection;
- K^N incompatible with K^D;
- same frozen injunction at several days with changing E_n threshold resolution;
- unrelated extension of LI language/signature;
- future-price / reflective LUV if supported;
- constraint that satisfies syntax but violates traderization / LI-preservation
  assumptions.

The desired result is not "everything works."

The desired result is to locate exactly which boundary rejects each bad case.

# 13. Pressure-test whether the waists are really narrow enough

Do not widen them reflexively.

Try these richer normative forms:

- conditional obligation;
- disjunction;
- lexicographic priority;
- defeasible priority;
- nonconvex permissibility;
- value incomparability;
- dynamic ontology revision.

For each, classify:

1. Can this remain entirely upstream and produce simple LUV exposure /
   injunction issuance?

2. Can it be represented through multiple LUVs / multiple affine injunctions?

3. Does it genuinely require widening the VALUE waist?

4. Does it genuinely require widening the OPERATIVE waist?

5. Is it actually not supposed to have direct market-level semantics at all?

We particularly want to know whether rich normative complexity can stay upstream
while the waist remains simple.

# 14. Begin closing the loop if the vertical slice is stable

Do NOT attempt a complete positive-learning theory.

But once the forward pipeline runs, investigate what the return interface
naturally needs.

Candidate sources of internal pressure:

- K_n^N = empty;
- K_n^N ∩ K_n^D = empty;
- large change in E_n(X);
- an old injunction referring to superseded value standing;
- repeated costly enforcement;
- failed formal exposure of a value query;
- predictive or action outcome failure.

Important:

None of these should automatically mutate N.

Try to identify the minimal generic structure:

    cognitive / operative condition
      -> pressure or concern
      -> inquiry / assessment
      -> reason occurrence
      -> possible NormEvent

Preserve:

    pressure != reason != normative revision

The goal here is NOT to finish inquiry.

The goal is to let the running toy reveal what the inquiry interface must
consume and emit.

# 15. Desired theorem / invariant package

Where supported, formulate exact versions of:

VALUE LAYER

1. Value semantic stability.
2. Historical value-reference rigidity.
3. Failed exposure is explicit/non-destructive.
4. Value revision does not imply operative revision.

LANGUAGE LAYER

5. Representation compatibility between V and L.
6. Conservative extension / unrelated-signature invariance.

OPERATIVE LAYER

7. Injunction projection exactness.
8. Issuance provenance.
9. Compilation exactness.
10. No invisible force.
11. No invisible weakening.
12. Conflict visibility.

EXECUTION LAYER

13. Deduction/normativity composition correctness.
14. Enforcement provenance:
       trade/action
         <- separator
         <- K_n
         <- compiled injunction
         <- active injunction standing
         <- issuing NormEvent
         <- reasons/authority
15. Strongest actual traderization / LI-preservation result supported by current
    math.

END-TO-END

16. Value revision / operative persistence theorem in the toy.
17. Explicit operative revision theorem.
18. Deterministic replay / inspectability of the toy trajectory if feasible.

Do not invent theorem statements stronger than the repository supports.

# 16. What counts as a successful pass

A successful pass does NOT require proving the whole normative learner.

It should tell us whether we are ready to treat the architecture as one running
machine.

Use one of these final verdicts:

    END-TO-END-READY

Meaning:
- the current value/operative waists survive the vertical slice and adversarial
  tests well enough;
- remaining issues are localized proof/implementation obligations;
- the next main research step should be closing inquiry and expanding the exact
  toy.

    END-TO-END-WITH-LOCAL-REPAIRS

Meaning:
- the overall architecture works;
- end-to-end construction exposed specific corrections to the value or operative
  waist;
- those corrections are local and clearly specified.

    WAIST-REVISION-REQUIRED

Meaning:
- the end-to-end dynamics expose a structural defect in ValueSpec -> LUV,
  CognitiveQuantity, PInjunction, or the K^N compilation interface.

    UPSTREAM-INCOMPATIBILITY

Meaning:
- a genuine conflict with frozen RI or the V/L relationship requires revisiting
  upstream assumptions.

    TRADERIZATION-MISMATCH

Meaning:
- the semantic architecture is coherent, but the generated constraint schedule
  falls outside the current traderization theorem in a way requiring new
  mathematics.

Multiple labels may be used if needed, but designate one primary verdict.

# 17. Deliverables

Produce:

1. A research report with:
   - repo map;
   - exact interfaces reused/added;
   - what original LI/LUV machinery buys us;
   - exact V/L relationship used;
   - exact value waist;
   - exact operative waist;
   - exact K^N compiler;
   - actual traderization assumptions;
   - adversarial failures;
   - implications for inquiry.

2. A formal/spec document for the refined end-to-end architecture.

3. The smallest executable narrative vertical slice.

4. Tests covering the adversarial variants above.

5. A trace/output representation allowing a human to inspect the toy trajectory
   end-to-end.

6. A table classifying each rich expressiveness case as:
   - fits current waist;
   - stays upstream;
   - local extension;
   - genuine waist failure.

7. A concise list titled:
      "WHAT THE END-TO-END BUILD TAUGHT US"
   containing only discoveries that were not already assumed at the start.

8. Final verdict.

If the work is coherent enough to preserve:
- make a focused branch;
- commit relevant changes only;
- open a PR;
- state clearly in the PR whether the value and operative waists are now
  canonical, provisional-but-usable, or locally repaired.

# 18. Strong prohibitions

Do NOT:

- reopen RI merely for convenience;
- build an entirely new generalized security market before LUVs fail;
- identify V with the LI language;
- require every V-object to have propositional truth conditions;
- treat all values as one utility function;
- collapse plural/incomparable value into fake scalar utility;
- silently replace old value references with current ones;
- let value revision automatically revise injunctions;
- let conflict automatically weaken force;
- put budgets/liability inside normative semantics;
- solve rich defeasible normative logic inside the operative waist unless forced;
- attempt the positive-learning/regret theorem in this pass;
- build a Supreme Court replay yet;
- declare success merely because unit tests pass.

# 19. Research standard

The architectural pattern we are testing is:

    rich upstream semantics
      -> small formal/proof-carrying waist
      -> bounded cognitive execution

Specifically:

    rich value standing
      -> certified LUVs

    operative normative standing
      -> simple constraints over Prob(phi), Expect(X)

    simple constraints
      -> ordinary LI price geometry

    price geometry
      -> traderized enforcement

The strongest reason to trust this architecture would be that the FULL TOY runs
without introducing semantic glue that belongs nowhere, and that the rich
adversarial cases mostly stay upstream rather than forcing the waist to grow.

The strongest reason to reject it would be a concrete end-to-end counterexample
where a necessary normative operation cannot pass through these interfaces
without either semantic distortion or breaking the LI/traderization guarantees.

Use the end-to-end build as a scientific instrument.

Try to break the waists by making the machine run.

---

# ADDENDUM 1 — SETTLEMENT LEDGER AND LI-COMPATIBLE WORLDS

*(sent mid-round, while the repository audit was in progress)*

One additional architectural point has become salient while this run is in
progress. Please incorporate it into the audit and end-to-end design.

We suspect that the Settlement Ledger L_n should be much more tightly coupled to
the LI formal language than the rich reason/object language V is.

The intended distinction is:

    V:
      rich language of reasons / normative objects;
      may contain open-textured content;
      need not have total propositional market semantics.

    L_n:
      provenance-bearing record of what has actually been settled;
      if it is to constrain the LI's live possible/completion worlds, its
      epistemically operative content should have exact semantics in the LI
      formal substrate.

The current candidate picture is:

    L_n
      -> Sem_L(L_n) ⊆ Sent(L)
      -> compatible LI completions

with something like:

    Sigma_n = D_n ∪ Sem_L(L_n)

    W_n = PC(Sigma_n)

or equivalently:

    W_n = PC(D_n) ∩ Compat(L_n)

where the exact formulation should follow the actual LI definitions in the
repository/paper.

The idea is that original LI is recovered when the only settled theory is the
deductive process D_n, while the interactive normative learner additionally
acquires irreversible empirical/interactive settlements through L_n.

IMPORTANT: DO NOT simply assume this formulation is correct. Audit it against
the actual Logical Induction setup and the existing RI settlement semantics.

Please investigate the following.

1. LEDGER VS THEORY

Do not identify L_n itself with a deductively closed theory.

Prefer a distinction like:

    L_n = append-only provenance-bearing settlement history

    Sem_L(L_n) = formal epistemic content induced by that history

so that different settlement histories may induce the same present compatible
world set while remaining historically distinct.

We want, if coherent:

    history/provenance lives in L_n;
    current epistemic restriction lives in Sem_L(L_n) / PC(...).

2. TOTALITY OF SETTLEMENT SEMANTICS

Determine whether every object admitted as a genuine Settlement Ledger entry
should carry a rigid LI-facing denotation, for example:

    sem_L :
      Settlement -> finite theory / sentence constraint in L

such that its effect on compatible worlds is exact.

This should be contrasted with V, whose formal exposure may remain partial.

Potential principle:

    every genuine settlement has exact world-compatibility semantics,
    but not every reason/normative expression does.

Test whether this is too strong.

3. RAW OUTCOME VS FORMAL SETTLEMENT

If the environment produces messy/open-textured observations, investigate
whether the architecture should distinguish:

    RawOutcome
      -> certified/formally interpreted Settlement
      -> L_n

rather than placing arbitrary natural-language observations directly into the
world-constraining ledger.

For example, an ambiguous observation should not eliminate LI worlds until there
is some exact account of what was settled.

Preserve:

    settlement != assessment != reason.

Do not smuggle normative interpretation into sem_L.

4. GENERALIZATION OF PC(D_n)

Audit the hypothesis that the natural generalized epistemic substrate is:

    Sigma_n = D_n ∪ Sem_L(L_n)

    W_n = PC(Sigma_n)

where:
- D_n supplies deductive/logical settlement;
- L_n supplies empirical/interactive settlement.

Determine:
- whether PC is still exactly the right construction;
- whether the existing LI theory Γ / deductive process needs to absorb
  Sem_L(L_n) instead;
- whether there are monotonicity/consistency requirements;
- whether this interacts with the definition of LUVs;
- whether changing environment observations require any departure from ordinary
  LI possible-world semantics.

5. CONSISTENCY / FAILURE CASES

Explicitly test:
- two settlement entries whose formal contents conflict;
- settlement content conflicting with D_n;
- a raw observation that cannot yet be given exact LI-facing semantics;
- conservative extension of the LI language after old settlements;
- whether old settlement denotations remain rigid.

Do not silently repair contradictions.

If a "settlement" can later turn out false, ask whether it was really a
settlement in the intended sense, or whether we need a separate
fallible observation/evidence layer upstream of formal settlement.

6. RELATION TO V AND VALUE LUVS

The emerging compatibility picture is asymmetric:

    V -> L
      mostly through rigid quotation/coding plus selective formal exposure;

    Settlement -> L
      potentially through total exact world-constraining semantics.

Please determine whether that asymmetry is principled.

Also check that value-generated LUVs, ordinary proposition prices, and
environmental settlements all inhabit one coherent LI semantic substrate, rather
than accidentally creating separate notions of "world".

7. END-TO-END TOY

If the candidate survives, the narrative toy should make this explicit:

    environment outcome
      -> formal settlement ell
      -> append ell to L_n
      -> update Sem_L(L_n)
      -> update the currently compatible LI completions / deductive substrate
      -> affect P_n(phi), E_n(X)
      -> assessment / reason occurrence
      -> possible NormEvent

The exact causal/order structure should respect the repository's LI dynamics; do
not force this sequence if the actual machinery requires another one.

The architectural hypothesis to test is:

    THE SETTLEMENT LEDGER IS THE PROVENANCE-BEARING INTERACTIVE
    GENERALIZATION OF THE EPISTEMIC ROLE PLAYED BY THE DEDUCTIVE PROCESS,
    WHILE PC(...) / COMPATIBLE COMPLETIONS PROVIDE THE WORLD SEMANTICS.

In the final report, explicitly say whether this is:
- correct as stated;
- correct after a local reformulation;
- too strong;
- or incompatible with LI/RI as currently formalized.

---

# ADDENDUM 2 — RETAIN CORE PRIOR ART

*(sent mid-round, while the test suite was being written)*

Before finishing, add a small dry prior-art note to the normativity project,
preferably:

    projects/normativity/notes/PRIOR_ART.md

Do not develop new theory or alter the architecture. This is preservation only.

Record the prior art we have already identified as materially relevant to the
current normative-learning / legitimacy program:

1. Inquiry/service optimization:
   - Golovin & Krause on adaptive submodularity
   - Guillory & Bilmes on interactive submodular set cover
   - Azar & Gamzu on submodular ranking
   - set cover with delay / online covering

   Preserve the architectural conclusion:
       Service semantics are general;
       submodularity/adaptive submodularity are optional tractable subclasses,
       not definitions of legitimate inquiry.

2. Reason representation:
   - Doyle TMS
   - de Kleer ATMS
   - Horty on reasons/defaults
   - Pollock on defeaters
   - Prakken / ASPIC+

   Preserve:
       support/provenance/defeat machinery is relevant prior art,
       but reason representation != normative force.

3. Answerability / normative practice:
   - Brandom on commitments, entitlements, and scorekeeping
   - Pettit on reasons-responsiveness / answerability

4. Credal/normative statics:
   - Walley, Williams, Levi
   - Łukasiewicz / probabilistic logic

   Preserve:
       credal/convex statics do not themselves provide learning,
       legitimacy, or normative authority.

5. Main external comparison targets:
   - Demski, Learning Normativity
   - Carroll et al. (2024), changing/influenceable reward
   - Inductive Coherence
   - Nostalgebraist's Logical Induction criticism

For each item give:
- exact citation/link if confidently verifiable;
- 1–3 sentences on what we take from it;
- when useful, one sentence on what we explicitly do NOT take from it.

Keep the note factual and compact. Do not promote these references into claims
or imply that the current architecture has already subsumed them.

---

# ADDENDUM 3 — PRESS AND CLOSE THE END-TO-END VERTICAL SLICE

*(sent after the first pass reported, as a follow-up dispatch)*

Continue directly on PR #56 / branch:

    round/2026-08-25-end-to-end-vertical-slice

Do not open a new PR. Do not merge it. You may take several internal passes and
multiple commits if useful.

The goal is no longer exploration. The goal is to leave PR56 as the strongest
honest end-to-end reference demonstration we can currently support:

    Gamma / settlement
      -> Sigma / PC worlds
      -> reasons / normative standing
      -> value exposures and LUVs
      -> operative force
      -> K^N, K^D, K
      -> exact traderization interface
      -> resulting prices/readings

with every boundary explicit, every quantitative claim using the canonical
quantity from the underlying theorem/API, and every remaining gap sharply
isolated.

Do NOT expand into a general inquiry theory, decision theory, Carroll et al.,
real-practice replay, or a new architectural layer. Preserve sockets for those
consumers, but finish this slice first.

## 0. Start with a hostile re-read

Before changing code, reread at least the PR56 body, `VERTICAL_SLICE.md`,
`FINDINGS.md`, `SETTLEMENT_SEMANTICS.md`, `EXPRESSIVENESS.md`, `TRACE.txt`,
`src/pipeline.py`, `tests/test_composition.py`, `tests/test_toy.py`, and the
canonical traderization/safety sources actually being consumed —
`FUNDING_AND_SAFETY.md`, `src/outflow.py`, `src/force_api.py`, and the relevant
Lean declarations for the unconditional theorem / constraint schedule.

Treat the existing PR's prose as hypotheses under audit, not as facts.

## 1. Repair the liability / exclusion quantity first

The current vertical slice appears to define `exclusion_depth` differently from
the quantity the safety API actually charges.

The safety layer's sharp live-world deficit is of the form

    D_t = max_{omega in Omega_t^live} sum_j d_{t,j}(omega)

for the exact force request / row presentation / support / assessment state.

The current slice appears instead to compute something like

    sum_omega max_j d_{t,j}(omega)

over distinct fragment patterns.

These are not interchangeable.

Audit this exactly against `LiveDeficitCertificate.by_enumeration`,
`compile_safe_force`, and the theorem statements they implement.

Then: make the vertical slice use the canonical safety-layer quantity; preferably
reuse the canonical implementation directly where dependency direction permits,
rather than maintaining a subtly different clone; if reuse would violate the
round's dependency discipline, reproduce it with a test that proves equality to
the canonical implementation on the same inputs; keep any other useful geometric
quantity only under a distinct name; and repair every claim, test, trace line,
PRIORITIES item, and documentation passage that currently identifies the wrong
quantity with the safety charge.

The final slice must have ONE unambiguous answer to:

    "What exact quantity is charged for this normative force request?"

and a reader must be able to walk from that number to the existing safety theorem.

## 2. Press the "settlement makes force cheaper" claim

Separate three claims that are currently too easy to conflate.

**A. Fixed request monotonicity.** For one fixed row presentation/support, if the
live-world set shrinks, `Omega' subset Omega`, then prove/test the exact
monotonicity that follows for the canonical deficit: `D(Omega') <= D(Omega)`.
State this narrowly and cleanly.

**B. Day-indexed compilation.** A frozen semantic injunction containing
`Expect(X)` compiles differently at different days because the LI expectation
mesh changes: `kappa_n(J) != kappa_{n+1}(J)` at the low level. Therefore
shrinking live-world sets alone does NOT establish `D_{n+1} <= D_n` for the
actual day-indexed force requests.

Construct adversarial multi-day examples and determine what is true. Try hard to
find: a case where settlement shrinks the live worlds and D falls; a case where
the changing compilation prevents a naive monotonicity proof; ideally a case
where D actually rises despite additional settlement, if one exists; or a
theorem/structural reason ruling that out for the current LUV compilation, if
that is genuinely provable.

Do not infer cross-day monotonicity from finite examples.

**C. Actual charge.** The safety charge is `q_t = (eps_t + M_t) * D_t / delta_t`.
Even if `D_t` falls, `q_t` need not fall. Every final statement about "cheaper",
"cost", or "affordability" must distinguish `D_t` from `q_t`.

The preferred conceptual phrasing, if the math supports it, is something like:
force is charged for the live-world gap between what is demanded and what is
epistemically settled — but only at the exact level justified by the theorem.

## 3. Turn item 61 into the right mathematical question

Rewrite PRIORITIES item 61 if necessary so it asks for the actual missing
condition, not a quantity accidentally invented by the slice.

The central question should be approximately: can a plausible normative source +
settlement trajectory satisfy `sum_t (eps_t + M_t) * D_t / delta_t < infinity`
where `D_t` is computed for the exact day-t compiled force request over the exact
live-world assessment state?

Then go one step further INSIDE THIS ROUND. Do not solve general normative
inquiry. But construct the smallest serious trajectory you can which exercises
the condition. Try at least: a safely summable trajectory; a divergent
trajectory; a trajectory where settlement is doing genuine work in reducing
liability; and if possible, a trajectory where some other factor rather than
settlement makes the charge summable, to preserve the existing theorem's
three-factor interpretation.

These may be synthetic. The point is to demonstrate that the end-to-end slice can
actually feed the charged traderization branch correctly.

If no plausible normative source can yet be shown summable, say so. Do not fake
one. But the mechanics from normative standing -> compiled request -> exact D_t
-> q_t -> cumulative account should run.

## 4. Make the charged branch part of the actual end-to-end demonstration

The current slice diagnoses that every contentful injunction falls outside the
zero-liability/world-inclusive theorem. Good. Now make the positive branch
concrete.

The final demonstration should visibly contain at least one contentful operative
injunction for which: `hadm` / zero-liability admissibility fails; the injunction
genuinely changes K relative to K^D; the exact live-world deficit certificate is
computed; the exact charge is computed; the charge is paid through the existing
safety-bearing force interface or an exact adapter to it; the resulting force is
therefore safety-certified conditional on the account bound; and prices/readings
are produced only after the correct safety boundary succeeds.

If the current pipeline merely computes a projected target without passing
through the canonical charged-force API, close that gap or state precisely why
the reference model stops short.

I want the slice to demonstrate not merely "this is the region normativity wants"
but "this is the actual theorem-facing route by which a contentful normative
region is allowed to influence the LI market."

## 5. Retest the inertness dichotomy

The paper derivation appears sound: `hadm` -> every deductive world vertex lies
in K^N -> by convexity K^D subset K^N -> K^D intersect K^N = K^D.

Press it rather than merely preserving it. Check the exact hypotheses: finite
fragment, projection, convexity, duplicated coordinates, settlement-augmented
Sigma, etc. Make sure "admissibility iff inertness" is stated only in the precise
setting where the converse holds. Search for edge cases involving empty stages,
empty demand, dimension 0, redundant rows, and repeated coordinates. The
stage-unsatisfiable case must remain blocked before vacuous admissibility can
masquerade as success.

If cheap and natural, add a small Lean theorem for this observation against the
existing region types. Do not let Lean formalization block completion of the
round; if it remains a paper derivation, label it honestly.

## 6. Press the settlement semantics

Keep the good local reformulation: `Sigma_n = D_n union Sem_L(L_n)` is itself the
LI `DeductiveProcess`, provided monotonicity/effectivity hold.

But pressure these claims: total `sem_L : SettleId -> Finset Sentence` with `{}`
as non-exposure; rigidity of old settlement readings; append-only settlement
required by `DeductiveProcess.mono`; RawOutcome vs certified SettlementReading;
contradiction detection before LI/traderization guarantees are consumed; and two
different histories inducing the same Sigma while retaining distinct provenance
upstream.

Add any missing adversarial tests. Do not silently turn ambiguous observations
into settled propositions.

## 7. Press the value / operative waists one last time

Do not widen them unless a concrete failure forces it.

Retest specifically: old value spec v0 superseded by v1 while old injunction J0
still names X[v0,q]; J0 changes only after an explicit normative event supersedes
it; several active PValue standings; failed query -> NonExposure; mixed Prob /
Expect inequality; two LUVs sharing threshold sentences; unrelated language
growth; reflective/future-state LUV; an old quantity that later becomes
hard/impossible to settle; conflict between two individually valid injunctions;
and normative/deductive incompatibility.

The key historical invariant should remain machine-visible: value revision !=
operative revision. Do not add automatic reconciliation.

## 8. Improve the canonical trace

TRACE.txt should become the thing a human can read to understand the whole
architecture. Prefer one compact but rich trajectory over many toy fragments.

It should visibly show, with exact rationals: initial settlement/deductive state;
active PValue(v0); compileValue(v0,q) -> certified LUV X0; active PForce/J0
referring to X0; day-n compilation of Prob/Expect terms; K^D_n; K^N_n; K_n;
zero-liability admissibility failing because J0 is contentful; exact live-world
deficit D_n; exact charge q_n and safety-account effect; resulting
price/readings; raw outcome -> certified settlement -> Sigma growth; reason
occurrence; normative event superseding v0 -> v1; X1 exposed; J0 STILL
constraining X0; later explicit normative event superseding J0 -> J1; changed
operative region; and at least one point where settlement changes the liability
calculation.

If the full charged branch cannot honestly be executed, TRACE must display the
exact undischarged obligation where execution stops rather than pretending the
market update happened.

## 9. Keep the inquiry socket small but sharp

Do not implement inquiry. The final round may expose computed pressure objects
such as: conflict/Farkas certificate; inconsistent-stage source set; exact
live-world deficit certificate; persistent/non-summable charge history; active
injunction over a superseded or no-longer-settleable quantity.

But preserve: pressure != inquiry != reason != NormEvent. Do not let a deficit or
conflict automatically become a reason or mutate N. At most document the return
interface that a future inquiry/service layer can consume.

## 10. Fix the repository / CI failures

PR56 currently has mechanical failures that must be resolved before closeout. In
particular inspect current CI rather than trusting this prompt, but known
failures include: the prompt round missing its required top-level PROVENANCE.md
row; and commit attribution — the PR body names Claude Opus 5 while the commit
lacks the required `Model:` trailer.

Repair these according to repository policy. Then run all relevant gates locally
and push until GitHub CI is green. Do not merely report "tests green locally"
while CI exits before reaching the project runner.

## 11. Final documentation discipline

At the end, rewrite the PR body / FINDINGS summary around what survived the
audit. Distinguish clearly: machine-checked finite behavior; paper derivations;
imported Lean theorems and their exact hypotheses; declared
computability/effectivity assumptions; and open mathematical obligations.

In particular avoid these overclaims unless newly proved: "a fixed semantic
injunction always gets cheaper over time"; "settlement alone makes cumulative
liability summable"; "the end-to-end normative source is unconditionally safe";
"submodularity/inquiry solves the liability condition"; "the waists are
canonical".

A strong final result is allowed to say: the architecture runs end to end; every
contentful injunction uses the charged branch; the exact charge is now wired to
the canonical safety theorem; several synthetic trajectories discharge the
condition and several do not; the general normative-source theorem remains open.
That is a success.

## 12. Closeout verdict

At the end give one primary verdict:

    END-TO-END-DEMONSTRATION-CLOSED
    END-TO-END-DEMONSTRATION-CLOSED-WITH-OPEN-SAFETY-THEOREM
    LOCAL-REPAIR-STILL-REQUIRED
    WAIST-REVISION-REQUIRED
    TRADERIZATION-INTEGRATION-FAILED

and separately answer: are the value/cognitive/operative waists still
provisional-but-usable? Is the exact charged traderization path now exercised end
to end? What is the exact remaining theorem, if any, between this slice and a
general normative-learning architecture? What should the next research pass be —
inquiry/service core, summable-liability/source theorem, Carroll benchmark, or
something discovered here?

Do not answer the last from project-management intuition. Answer it from what the
repaired end-to-end run actually reveals.

Push all repairs to PR56 and leave it reviewable, CI-green, and unmerged.

---

# ADDENDUM 4 — CRYSTALLIZE THE ARCHITECTURE OF PR56

*(sent after the pressing pass reported)*

Continue on the existing PR #56 branch. Do not open a new PR. Do not merge.
Multiple internal passes and commits are fine.

The previous passes have now done the hard empirical work: the end-to-end forward
slice runs, the charged branch uses the canonical traderized-enforcement safety
quantity, the false cross-day monotonicity claim has been withdrawn, and the
current verdict is `END-TO-END-DEMONSTRATION-CLOSED-WITH-OPEN-SAFETY-THEOREM`.

This pass is primarily a mathematical compression, architecture audit, and
cleanup pass. The goal is to leave this round in a state where the architecture
it has crystallized is stated canonically, minimally, and compositionally enough
that the next round can build the learning loop against it without rediscovering
what the types mean.

Do not expand into inquiry/service, Carroll, decision theory, or a
normative-learning theorem. You may identify sockets for them, but this pass
should finish the forward architecture.

## 0. Start from the live branch, not from this prompt's reconstruction

Re-read the current PR body, `VERTICAL_SLICE.md`, `FINDINGS.md`,
`SETTLEMENT_SEMANTICS.md`, `EXPRESSIVENESS.md`, the current `TRACE.txt`,
`src/waist.py`, `src/epistemic.py`, `src/pipeline.py`, `src/safety.py`, the
Reflective Integrity core imported by this round, the earlier
reason-representation round, and the canonical traderized-enforcement safety
sources actually imported by this round.

Treat the current executable behavior and the underlying imported theorem
interfaces as evidence. Do not preserve prose merely because an earlier pass
wrote it.

## 1. Recover the architecture from the types

Before editing prose, reconstruct the smallest compositional type-level account
of the system. Separate rigorously: primitive/parameter types; append-only
historical occurrences; rigid interpreters/semantics; derived current views;
compiled/effective representations; and certificates and safety/resource state.

Ask of every named object: does this actually need to be state, or is it a
derived view? Does this actually need to be primitive, or is it a construction
over more basic types? Is this a semantic object, a historical occurrence, an
effective presentation, or a certificate about one?

The final architecture should have substantially fewer peer-level boxes than the
accumulated documentation currently suggests.

A candidate compression to test, not assume:

    persistent mutable state
        = append-only historical record + LI price history + enforcement account

    fixed / meta-stable semantics
        = reason/schema machinery + demand semantics + settlement semantics
          + value exposure semantics + LI substrate

    everything else = derived or compiled.

If this is wrong, find the counterexample.

## 2. Put the directed multihypergraph back at the center of reason representation

The recent compression discussion recovered an important picture that the current
vertical-slice prose may understate: the reason substrate should be understood as
a growing directed multihypergraph.

Audit the earlier reason-representation work and the actual RI types and state
this exactly. Current candidate: `ReasonOcc e = (id, s_V : Finset V, s_L : Finset
SettleId, target : V, tau)` induces an identity-bearing directed hyperedge
`e : s_V(e) + s_L(e) -> target(e)` over a vertex universe roughly `U = V +
SettleId`. Because distinct `ReasonOcc`s may have the same sources and target,
the structure is a multihypergraph, not merely a hypergraph.

But do not merely copy that statement. Press it against the exact semantics:
`s_V` contains reason expressions, not `ReasonId`s; `s_L` contains settlement
identities; a `Derivation` later cites actual `ReasonOcc` identities; `Enabled`
has its exact current meaning; stance-bearing standing and the reason graph must
not be conflated; and historical occurrence-level provenance and content-level
support are different.

State precisely what the multihypergraph does and does not represent. In
particular, determine whether the clean formulation is: reason graph with
vertices `V + SettleId` and hyperedges `ReasonOcc`; normative derivation as
selected occurrence-level provenance through that graph plus licensed
inference/schema steps — or whether the exact implementation forces a refinement.

## 3. Make revisable schemas an explicit part of that picture

Preserve the core reflective idea: schemas structure reasoning, while reasoning
can justify revision of the active schemas.

Audit the relation among `SchemaCode`; the occurrences of schema/application/
instance structure in `V`; `PAuth(schema)` standing; `Derivation.steps`; G3/G4;
the practical-schema interpreter `[[.]]_S`; and supersession of standing.

Distinguish rigorously rigid historical schema meaning from revisable standing
toward / authorization of schemas. A likely good formulation is `PAuth(sigma_0)
~> PAuth(sigma_1)` rather than changing the semantics of `sigma_0` in place.
Check that this is genuinely what the current architecture says. Do not add a new
schema-revision mechanism if ordinary standing supersession already supplies it.

Make the recursive structure visible in the canonical architecture: active schema
standing structures/licences reasoning, which produces the reason
multihypergraph / derivation, which produces a NormEvent, which may supersede
active schema standing. This should be presented as one of the central
mathematical structures, not buried as an implementation detail under
`SchemaCode`.

## 4. Clarify the settlement ledger / LI Sentence connection completely

Preserve the distinction: settlement history != LI Sentence set. `L_n` is the
provenance-bearing append-only settlement ledger. There is a rigid finite
LI-facing semantics `sem_L : SettleId -> Finset(Sentence)`, or whatever exact
type survives audit. Then `Sem_L(L_n) = union over l in L_n of sem_L(id(l))` and
`Sigma_n = D_n union Sem_L(L_n)`, and finally `W_n = PC(Sigma_n)`.

The architectural interpretation should be explicit: the ledger remembers what
settled and its provenance; `sem_L` gives a rigid formal projection of that
settlement into the LI language; `Sigma_n` is the actual monotone sentence
process consumed by LI; and `PC(Sigma_n)` forgets provenance and retains only the
induced epistemic restriction. Two different settlement histories may therefore
induce the same `Sigma_n` / same live-world set.

Also press the exact type-level seam around `SettlementReading`. The current
round uses a write-once settlement-semantics object. Decide whether the canonical
architecture should describe `Settlement + external rigid sem_L` or an
application-level certified/read settlement wrapper which RI then forgets down to
its thin `Settlement`.

Do not modify Reflective Integrity merely to make the diagram prettier. The
criterion is compositional correctness: can a reader see exactly how an
environmental/raw observation becomes an admitted historical settlement and how
that settlement contributes formal `Sentence`s to `Sigma_n`, without implying
that natural-language interpretation or normative interpretation is silently
performed inside LI?

Preserve `RawOutcome != Settlement != sem_L(Settlement) != ReasonOcc`. Preserve
the empty reading `sem_L(l) = {}` as a genuine non-exposure state. Also preserve
the contradiction guard: an unsatisfiable `Sigma_n` must be caught before vacuous
LI guarantees are consumed.

## 5. Re-express the entire forward architecture compositionally

Produce one canonical type/signature presentation whose pieces compose. Press
every arrow. In particular identify what is a function; what is a
relation/refinement type; what is a fold over history; what is a projection; what
is a compiler; what is a certificate; and what is a theorem assumption. Do not
let prose arrows hide an untyped semantic jump.

## 6. Compress the value/cognitive/operative waists to their real mathematical cores

Retest whether the cleanest formulations are `valueSem : ValueSpecCode x
QueryCode -> CertifiedLUV + NonExposure`; `CognitiveQuantity ::= Prob(Sentence) |
Expect(CertifiedLUV)`; `Affine(A)` as finite rational affine expressions over
`A`; `Injunction` as a finite nonempty family of affine inequalities over
`CognitiveQuantity`; and `kappa_n : active operative standing -> finite Sentence
coordinates x rational rows`.

Prefer generic mathematical constructions such as `Affine(A)` over accidental
implementation record shapes when they say the same thing.

Retain all distinctions the running code showed to matter: `Expect(X)` is derived
through existing LI `expectAffine`, not a new security; duplicate sentence
coordinates must be merged; standing identity must survive the operative
projection; frozen high-level semantic force does not mean frozen day-level row
presentation; multiple value specifications need not be aggregated; and
`NonExposure` is non-destructive.

## 7. Incorporate the repaired charged-branch lessons into the type story

The architecture must now reflect the second pass, not the obsolete first-pass
intuitions. The canonical live-world deficit is `D_t = max over omega in
Omega_t^live of sum_j d_{t,j}(omega)`, and the charge is `q_t = (eps_t + M_t)
D_t / delta_t`.

Do not restore any stronger slogan such as "a fixed injunction gets cheaper as
settlement accumulates." State separately: fixed presentation + support +
assessment, narrowing the live-world set cannot increase `D`; across days,
`kappa_n(J)` changes, fragments change, and `D_n` can rise; and even falling
`D_n` need not imply falling `q_n`.

Also elevate the new presentation dependence result: equivalent semantic regions
can have different charged row presentations. Ask whether the true theorem-facing
enforcement object is therefore something like `ForceRequest = date + support +
exact row presentation + live-world assessment + tolerance/slack/volume` rather
than merely a semantic region.

Do not solve presentation invariance in this pass unless a very small
canonicalization falls out for free. Record it as a genuine mathematical frontier
if not.

Preserve the central dichotomy `hadm <=> K_t^D subset K_t^N <=> K_t = K_t^D` on
the exact nonblocking domain where the equivalence is valid. Interpret this as:
the unconditional branch is the deductively inert / zero-liability calibration
branch; genuinely region-changing normativity uses charged enforcement. Do not
say "traderization fails for normativity."

## 8. Identify the truly persistent state

Press hard on whether the entire forward machine can now be presented as
approximately `MachineState_t = History_t x PriceHistory_<t x OutflowAccount_t`
where `History_t` is append-only and contains the RI occurrence types, and
essentially everything else is derived.

If a settlement-semantics or value registry really must be dynamic state, explain
why. If it can instead be understood as rigid admitted meaning / conservative
extension, remove it from the conceptual persistent-state list.

The final presentation should distinguish historical state, rigid semantics,
bounded resource state, and derived current views rather than putting all of them
in one undifferentiated "system state."

## 9. Keep the three graph structures separate

If the audit supports it, explicitly distinguish the reason multihypergraph
(support/undercutting/schema-applicability structure); the standing lineage graph
(`pred` under supersession); and the answerability/custody succession graph
(`AnsRoot` succession). Explain in one concise place what question each graph
answers. Do not merge them into one mega-graph just because they all contain
edges.

## 10. Clean the documentation around one canonical architecture

The round currently contains several overlapping narratives accumulated over
multiple passes. Create or designate one canonical architectural document inside
this round; a name such as `ARCHITECTURE.md` is fine if no existing document is
clearly the right canonical surface.

It should be readable by a mathematically sophisticated person who has not
followed the chat history. Recommended structure: irreducible/parameter types;
reason multihypergraph; settlement and LI epistemic projection; normative event /
revisable-schema loop; standing and answerability as derived views;
value/cognitive/operative waists; independent construction of `K^D_n` and
`K^N_n`; intersection and conflict; charged traderization boundary; minimal
persistent state; explicit open sockets for learning/inquiry; and open
mathematical obligations.

Include one compact compositional diagram and one compact signature block. Avoid
fifteen pages of parallel terminology. Favor equations and types.

Then harmonize `README.md`, `VERTICAL_SLICE.md`, `FINDINGS.md`,
`SETTLEMENT_SEMANTICS.md`, and `EXPRESSIVENESS.md` around that account. Do not
delete useful adversarial findings, but move repeated architectural prose toward
the canonical document or cross-reference it.

Search the whole round for now-withdrawn claims, especially: cross-day
settlement/deficit monotonicity; "force is priced at the gap between demand and
settlement" without the fixed-day qualification; any old noncanonical
exclusion-depth statistic; any suggestion that `V` must translate wholesale into
the LI language; and any accidental implication that schemas mutate in place.

## 11. Press the compressed architecture adversarially

Before declaring success, try to break the canonical type story with small cases.
At minimum ask: two `ReasonOcc`s with identical tail/head but different IDs; same
reason content arising through different historical occurrences; a reason for
`not App(sigma,c,n)`; superseding `PAuth(sigma_0)` with `PAuth(sigma_1)` while an
old derivation remains historically interpretable; two different settlement
histories inducing identical `Sigma_n`; a settlement with empty `sem_L`;
contradictory settlements; a settlement conflicting with ordinary deduction;
equal `PForce` payloads at two distinct standing IDs; value supersession while
old LUV meaning remains fixed; same semantic normative region under redundant row
presentations with different charge; a frozen `Expect(X)` injunction whose
compilation changes across days; and account exhaustion leaving normative
standing intact but withholding operative force.

If the compressed architecture cannot explain one of these without adding an ad
hoc box, revise the architecture.

## 12. Scope discipline for the next learning loop

End with an explicit return-interface socket, not an implementation. The forward
run now exposes candidate pressure/certificate objects: Farkas conflict
certificates; contradictory-stage source sets; live-deficit certificates; charge
history / partial sums; account state; and withheld-force events.

Preserve `pressure != inquiry != service != assessment != reason != NormEvent`.
State the exact forward-side output types the next inquiry/learning round should
be allowed to consume.

Do not yet decide the full `Inquiry` ontology; whether inquiry lives as standing;
an action-selection theory; submodularity; Carroll; or a regret theorem. The
point of this pass is to hand the next round a stable typed forward machine.

## 13. Verification and repository hygiene

Make only architecture-driven code changes. Do not refactor working code for
style unless the type audit finds an actual mismatch. If documentation claims a
function has a given type or dependency direction, verify against the
code/imported source.

Run the round test suite; repository checks required by the workspace; any
relevant provenance/naming checks; and CI. Leave PR56 CI-green. Preserve exact
arithmetic. Do not register or claim Lean theorems that have not been proved.

## 14. Final report

At the end, report: A. the canonical mathematical architecture, in no more than
about 2 pages of dense prose/equations. B. the truly primitive/parameter types.
C. the truly persistent state. D. everything that is derived. E. the exact role
of the directed multihypergraph. F. the exact relation `L_n -> Sem_L(L_n) ->
Sigma_n -> PC(Sigma_n)`. G. the exact reflective schema loop. H. the exact
theorem-facing charged-force interface. I. any architecture change the audit
actually forced. J. the smallest unresolved type-level questions that must be
answered by the learning-loop round.

Give one of these verdicts: `ARCHITECTURE-CRYSTALLIZED`;
`ARCHITECTURE-CRYSTALLIZED-WITH-LOCAL-SEAMS`; `TYPE-LEVEL-REPAIR-REQUIRED`; or
`FORWARD-ARCHITECTURE-NOT-YET-STABLE`.

The bar for `ARCHITECTURE-CRYSTALLIZED` is not that the safety theorem is solved.
It is: the forward normative reasoner has one compact, compositional, internally
consistent type-level account; the running vertical slice implements that
account; the remaining safety theorem and learning loop are identifiable
consumers/extensions rather than symptoms of unresolved architecture.

Push all cleanup and repairs to PR #56, leave it reviewable and CI-green, and do
not merge.

---

# ADDENDUM 5 — SHORT THEOREM SCOUT: QUANTITATIVE ANSWERABILITY ⇒ PERPETUAL TRADERIZABILITY

*(sent as an insert to the crystallization pass, after the architecture audit and
before the final report)*

Once the architecture has been compressed and the types are stable, spend one
tightly scoped pass testing a mathematical connection that the crystallized
architecture now makes possible.

Do not turn this into a new research round, and do not block completion of PR56
on solving a mature liability theory. The goal is to determine whether there is
already a clean first theorem connecting the existing answerability structure to
the charged traderization interface.

The motivating eventual result is: appropriate diachronic answerability
conditions imply the normative trajectory is traderizable forever. Here
"traderizable forever" should initially mean something precise and modest:
`sum_{t=0}^{infinity} c_t < infinity`, where `c_t` is the canonical certified
charged-branch liability generated by PR56's actual `LiveDeficitCertificate` /
`compile_safe_force` path.

This scout should ask whether the theorem can be obtained as an
amortized/conservation theorem over the existing answerability or
standing-succession structure, rather than by proving that per-date deficit
decreases. PR56 has already shown that the latter route is unavailable: a frozen
semantic injunction can compile differently across dates, so `D_t` may rise even
under increasing settlement. Do not assume or seek cross-day monotonicity of
`D_t`.

## A. Find the correct carrier of quantitative answerability

Inspect the actual RI structures and determine where a liability
allowance/potential most naturally belongs. Candidate carriers include
force-bearing `StandingId`s; live `AnsRoot` / custody episodes; a pairing of a
standing with its current answerability episode; or some other already-existing
succession object.

Do not add a new carrier merely because it makes the proof easy. Ask: which
existing identity is supposed to remain answerable for the downside of exercising
this normative force through supersession, transfer, and succession? The answer
should make liability laundering impossible in the obvious bad cases.

In particular test: superseding one expensive force by an equivalent successor;
splitting one force-bearing standing into several successors; merging several
predecessors; transferring custody; terminating a standing; and retaining
normative standing while enforcement is withheld for lack of funds.

## B. Test the potential-function theorem shape

Suppose each currently responsible episode/object `e` carries a nonnegative
remaining allowance `B_t(e) >= 0`. Define total outstanding allowance `Phi_t =
sum over e in E_t of B_t(e)`.

Investigate whether natural local transition laws on the existing RI operations
can imply an inequality of the form `c_t + Phi_{t+1} <= Phi_t + eta_t`, where
`c_t` is the actual canonical traderization charge incurred at date `t` and
`eta_t >= 0` is explicitly accounted newly granted liability allowance.

If so, derive the telescoping consequence `sum_{t<T} c_t + Phi_T <= Phi_0 +
sum_{t<T} eta_t`, and therefore `Phi_0 < infinity` and `sum_t eta_t < infinity`
imply `sum_t c_t < infinity`. This is the candidate first perpetual-traderizability
theorem.

The proof itself may be trivial once the correct local laws are chosen. The
research question is whether those local laws are a natural quantitative
strengthening of answerability rather than the conclusion disguised as an
assumption.

## C. Search for local laws that deserve the name "answerability"

At minimum press the following candidate principles.

1. **Charge coverage.** Every actually exercised normative force must be charged
   to the currently answerable object(s) responsible for that force. No force can
   appear with certified charge > 0 while being owned by no answerability episode.

2. **No liability laundering through succession.** When a responsible object is
   superseded, transferred, split, merged, or otherwise succeeded, its remaining
   allowance cannot simply disappear and then reappear as fresh unencumbered
   authority. Candidate shape: `sum over e' in succ(e) of B_{t+1}(e') <= B_t(e) -
   charge allocated to e + explicit grant`. Generalize carefully to many-to-many
   succession if the actual RI graph requires it.

3. **No silent creation of liability capacity.** New allowance must enter through
   an explicit typed channel `eta_t`, attributable to whatever authority licenses
   new liability-bearing force. Creation, `MINT`, `Supersede`, and `Transfer`
   should not manufacture free budget merely by changing identities.

4. **Conservation under mere relabeling / transfer.** A purely custodial or
   nominal transition should not increase total liability allowance.

5. **Explicit discharge.** If outstanding liability disappears, identify the event
   that discharged it. Possible discharge modes may eventually include settlement,
   force withdrawal, supersession to a weaker demand, or other explicit normative
   disposition — but do not invent inquiry semantics in this pass. The accounting
   layer only needs to know that discharge occurred through a named allowed
   transition.

## D. Distinguish three theorem levels

Level I — accounting theorem: quantitative answerability invariants imply `sum_t
c_t < infinity`. This is the theorem this scout may plausibly formulate or prove
now.

Level II — responsiveness theorem: answerability + inquiry/revision dynamics
imply the quantitative answerability invariants. This likely requires the future
inquiry/service/learning loop. Do not attempt it here.

Level III — legitimacy theorem: legitimate normative learning implies perpetual
safe enforceability. This is an eventual synthesis target, not a PR56 deliverable.

The purpose of the current scout is to see whether Level I is already real enough
to give Level II a clear target.

## E. Do not smuggle summability into the hypotheses

Reject formulations equivalent to: every source is assigned enough finite budget
to cover all of its future charges. That simply assumes what is to be proved.

Prefer local transition invariants that can be checked one normative event at a
time and whose global cumulative implication follows by conservation/telescoping.
A good result should explain why locally answerable succession prevents globally
unbounded unaccounted liability.

## F. Press the presentation-dependence obstruction

PR56 shows that the current charge is a function of the exact row presentation,
not only of the semantic region: a duplicate equivalent row gives the same `K^N`,
a larger `D_t`, and a larger charge.

Therefore determine which of these the first theorem should use:
presentation-level liability, where the actual compiled force request is what
answerability owns; canonicalized presentation liability, where the normative
compiler is required to emit a canonical/nonredundant presentation; or
semantic/source-level liability, defined by a presentation-invariant
construction, perhaps a minimum over equivalent implementations.

Do not solve this issue by fiat. It is acceptable for the first theorem to be
explicitly presentation-level if that is the clean theorem supported by current
machinery. But record exactly what a stronger theorem would require.

## G. Connect the theorem scout back to the multihypergraph / RI architecture

The theorem should not float separately from the architectural compression. Ask
how the quantitative structure composes with: reason multihypergraph ->
Derivation -> NormEvent -> standing succession -> PForce -> kappa_t -> c_t.

The reason multihypergraph itself probably should not carry monetary/liability
weights merely because it is central to reasoning. More plausibly: reasons
justify normative events; normative events create/supersede force-bearing
standing; answerability attaches responsibility to those normative transitions;
and traderization produces the quantitative downside of exercising the resulting
force.

The theorem should therefore clarify exactly where qualitative
provenance/answerability acquires quantitative liability conservation.

## H. Use the result to sharpen, not implement, the next learning-loop interface

If a natural potential/allowance object emerges, note what the future inquiry
layer would be able to observe as pressure — for example low remaining allowance;
rapidly accumulating charge; a successor inheriting substantial outstanding
liability; or an attempted force that was withheld for lack of allowance/funding.

But preserve: liability pressure != inquiry != reason != NormEvent. Do not build
inquiry here. The benefit of doing this scout before inquiry is precisely that
the inquiry round may receive a principled typed signal rather than inventing an
arbitrary "something seems wrong" score.

## I. Deliverable and stopping rule

Keep this scout short. It should end with one of:
`QUANTITATIVE-ANSWERABILITY-THEOREM-SHAPED`;
`ACCOUNTING-THEOREM-PROVED-LOCALLY`;
`PRESENTATION-LIABILITY-SEAM-BLOCKS-CLEAN-THEOREM`;
`WRONG-CARRIER-NEEDS-LEARNING-LOOP`; or
`ANSWERABILITY-CONNECTION-CURRENTLY-ONLY-ANALOGICAL`.

Report: the proposed carrier of liability allowance; the local conservation laws;
the resulting one-step potential inequality; the global telescoping theorem, if
valid; necessity/counterexamples for obvious omitted laws; how
succession/splitting/merging/transfer behave; whether the result genuinely
deserves to be called quantitative answerability; and the exact gap between this
Level-I theorem and a future inquiry-driven responsiveness theorem.

If the theorem is clean and extremely cheap, a small executable model or Lean
statement is welcome.

Do not let this theorem scout prevent PR56 from closing as an
architecture-crystallization round. The desired final state is: crystallized
forward architecture + precise open safety frontier + first tested mathematical
bridge from answerability to traderizability.

---

# ADDENDUM 6 — THE INQUIRY RETURN LOOP

*(sent after the crystallization pass and theorem scout reported, and after PR
#56 merged)*

Work in the live `A-M-Berns/alignment-workspace` repository. Focus on
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/`
and, as needed, the immediately preceding rounds: `2026-08-24-reflective-
integrity-core`, `2026-08-23-certified-interactive-service`,
`2026-08-23-reason-representation`, `2026-08-16-traderized-enforcement`.

**Goal:** extend the existing end-to-end vertical slice with the missing inquiry
return loop, without reopening the architecture unnecessarily.

The current slice is essentially one-way. The missing loop is:

    existing normative standing -> operative force -> liability pressure /
    unresolved need -> inquiry -> ordinary world interaction -> settlement ->
    historical service -> defeasible assessment -> ReasonOcc -> ordinary
    NormEvent -> revised/continued normative standing

The target is not to develop a freestanding theory of inquiry. The target is to
make this exact loop run through the waists already earned.

## First: inspect before editing

Read at minimum `README.md`, `ARCHITECTURE.md`, `FINDINGS.md`,
`ANSWERABILITY_SCOUT.md`, `SETTLEMENT_SEMANTICS.md`, `src/toy.py`,
`src/pipeline.py`, `src/safety.py`, `src/epistemic.py`, `tests/test_toy.py`,
`tests/test_composition.py`, `tests/test_answerability.py`. Then inspect the
certified-interactive-service round, especially `CLOSEOUT.md`,
`INTERACTIVE_SERVICE_INTERFACE.md`, `src/service_core.py`, `src/composition.py`.
Also inspect the RI core and reason-representation round enough to understand why
the existing durable historical types should remain: `Settlement`, `ReasonOcc`,
`NormEvent`, `Response`.

Do not assume the August 23 service integration boundary is still canonical. In
particular, the old `ServiceEvent` design predates the later RI/settlement
crystallization.

## Architectural hypothesis to test

Inquiry completes the loop without becoming a second reasoner. Concretely: no new
inquiry historical event is needed; no new service historical event is needed; no
assessment historical event is needed; inquiry/service/assessment should be
derived interfaces or predicates over the existing state; the only durable
epistemic return from inquiry should be an ordinary `ReasonOcc`; and only an
ordinary licensed `NormEvent` may change normative standing.

Treat this as a hypothesis to prosecute through implementation. If it genuinely
fails, identify the exact type-level reason; do not widen the architecture for
convenience.

## The canonical toy should be extended, not replaced

Do not build a separate inquiry demo if the existing canonical trajectory can be
extended. Preserve the key theorem demonstrated by B/C: value revision !=
operative revision. Inquiry should explain why/how the trial was performed and
returned into Stage B. Ideally, once `l:trial` has been admitted, the downstream
objects/states should agree with the old canonical trajectory as exactly as
practical.

## Desired new trajectory

Refine Stage A/B into approximately: A0, `v0` and `J0` active with `J0`
contentful and incurring positive traderized liability. A1, the actual charged
pipeline result gives a typed pressure signal, and a current answerability
episode already exists for the relevant force-bearing standing. A2, from
`CurrentEpisode(q)`, `subject(q)` the relevant standing, and
positive/persistent liability pressure, derive an `InquiryNeed` for a diagnostic
service problem — with pressure != obligation != reason != desired conclusion !=
NormEvent, and Need read-only. I0, a policy/controller sees the Need and chooses
an ordinary action `Probe`. I1, `Probe` goes through an ordinary
history-relational environment `Gamma : H x Action -> P+(RawOutcome)`, no query
oracle. I2, the raw outcome is converted through the existing certified reading
seam: `Probe -> RawOutcome("o:trial", ...) -> SettlementReading ->
Settle("l:trial")`, reusing the existing canonical ids where possible. I3, at
this point `Sigma` / `PC(Sigma)` have changed, historical inquiry service is
certifiable, no new `ReasonOcc` exists yet, and no normative standing has
changed. I4, an assessment checker admits a proposed ordinary `ReasonOcc`,
ideally the existing `e:revalue`; after the append, reason history has changed
and standing still has not. B, the existing `a:revalue` fires in the ordinary RI
way, `v0 -> v1`, `J0` untouched. C, existing `a:reforce`, `J0 -> J1`.

Make the intermediate states visible in tests and preferably in `TRACE.txt`.

## Inquiry identity / Need

Do not automatically mint a new normative `Investigate(...)` standing. The
current preferred interpretation is that inquiry is a way of servicing an
already-live unresolved answerability problem, not necessarily another obligation
layered on top of it.

A provisional inquiry reference might look like `InquiryRef = (subject :
StandingId, key : InquiryKey, spec : ServiceSpecId)` with a derived
`Need(machine_view, current_root, inquiry_ref)`. However, leave one question open
to implementation pressure: should stable inquiry identity be keyed by
`(StandingId, InquiryKey)` or `(AnsRootId, InquiryKey)`? Current prior: use
`StandingId` for the persistent unresolved subject and let the current `AnsRoot`
supply episode/custody information. But test this rather than forcing it. Do not
let `Need` mutate anything.

## Pressure source

Use the real current traderization output, not a fake pressure flag. Start with a
deliberately simple application-level trigger such as positive sharp deficit or
positive charge on the relevant live force-bearing standing. This first round
does not need a universal theory of when pressure rationally/normatively requires
investigation. What matters is that the types demonstrate liability pressure !=
inquiry need != reason != normative update.

## Minimal action theory

Keep action theory minimal: `Action`, `RawOutcome`, `InteractionHistory`,
`Gamma`, `Policy`. For the canonical fixture use something trivial like `Action =
{Wait, Probe}` and two policies, `probe_policy` and `wait_policy`. Do not build
an MDP, utility theory, Bellman machinery, causal formalism, etc. Inquiry should
be action-theory-parametric. If the old CIS `Env` machinery reuses cleanly, use
it; do not preserve old code reuse at the expense of the new settlement seam.

## Service semantics

The key conceptual object is `ValidCert(sigma, L, kappa)`, meaning the actual
historical interaction/settlement record contains enough of the right kind of
work to count as adequate service. It must not mean the answer is yes / revoke /
loosen / grant / update. A service specification should be conclusion-neutral,
and the diagnostic spec should accept both legitimate branches of the experiment
if both constitute adequate investigation. Think of service as a
terminal/reachability condition on histories. Decision theory chooses how to
reach `G_sigma`; inquiry does not rank policies.

## Settlement-backed service

This is one of the main seams to resolve. The old CIS reference model has
`ServiceCertificate` cite interaction receipts directly. The post-August-25
architecture strongly suggests the normative-facing service predicate should be
settlement-backed, because settlement is now the public epistemic boundary. But
service still needs to be able to distinguish "¬C was settled" from "¬C was
settled as the result of the designated Probe".

Do not solve this by smuggling action-theory state into LI semantics. Find the
narrowest provenance seam that permits something like `SettleId -> frozen
SettlementReading -> RawOutcomeId -> frozen interaction receipt / action
provenance` while preserving `RawOutcome != Settlement != sem_L(Settlement) !=
ReasonOcc` and keeping `sem_L : SettleId -> Finset Sentence` blind to normative
interpretation. This is a genuine design question for the round. Document what
the implementation forces.

## Historical service vs present assessability

Preserve the crucial distinction: historical service is persistent; current
assessability may be defeasible / lapse. Aim for `ValidCert(sigma, L, kappa) =>
ValidCert(sigma, L ++ L', kappa)` under the appropriate citation-local/frozen-
provenance conditions. Do not add a durable `ServiceEvent` merely to remember
that this once happened. If freshness/current applicability matters, represent it
separately, e.g. `Assessable_t(iota, kappa)`, which may become false later while
historical service remains true.

## Assessment

Keep assessment extremely thin. Preferred architecture: `ReasonProposal = (s_V,
s_L, target)` and `AdmissibleAssessment(assessment_code, inquiry_ref,
service_certificate, current_state, reason_proposal)`. In other words, assessment
is checker-shaped, not a constitutive conclusion generator. An arbitrary
algorithm may propose a reason; the architecture checks whether the proposed
reason is an admissible interpretation of the serviced history. Do not define the
core as `assess : certificate -> correct conclusion` unless such a function
exists only as a toy proposal generator and is explicitly non-semantic. A
successful assessment returns into the architecture only by appending an ordinary
`ReasonOcc`. No new source sort is desired.

## Exact expressiveness test

Add a fixture showing the inquiry/service layer is strictly richer than the LI
epistemic quotient. Construct histories `L_good`, `L_bad` such that
`sem_L(L_good)` and `sem_L(L_bad)` induce the same `Sigma` and `PC(Sigma_good) ==
PC(Sigma_bad)`, but diagnostic service succeeds on `L_good` and fails on `L_bad`,
because `L_good` contains the designated diagnostic procedure/provenance and
`L_bad` obtained the same proposition some other way. This should make executable
the non-factorization statement: service need not factor through `PC(Sigma)`.
This is a core acceptance criterion, not optional polish.

## Policy parametricity test

Run the exact same `Gamma`, `InquiryNeed`, `ServiceSpec`, settlement semantics,
assessment checker and normative machinery under at least `probe_policy` and
`wait_policy`. Demonstrate different Policy -> different trajectory while the
same `ServiceSpec` semantics holds, and ideally `probe_policy -> serviced`,
`wait_policy -> not serviced`. If the prior CIS finite-game `forced_reach`
machinery imports cleanly, it is useful to additionally demonstrate
`Servable(iota)` for the finite toy, but do not let the round become a
scheduling/game-solving project.

## Absolutely no grants in this round

The current `ANSWERABILITY_SCOUT.md` leaves the future grant channel `eta` as the
important Level-II seam. Do not solve grant semantics here. In fact, establish
the stronger negative result: `InquiryNeed`, `Action`, `Settlement`, `ValidCert`,
`Assessment`, `ReasonOcc` have no operation that can increase enforcement
allowance. If a future theory allows reasons -> licensed NormEvent -> explicit
Grant, that should be an explicit later normative/accounting extension. Add a
test demonstrating no inquiry/service/assessment operation can increase the
existing account.

## Preserve these architecture boundaries

Do not modify the underlying meaning/types of `Settlement`, `ReasonOcc`,
`NormEvent`, `Response` merely for integration convenience. Do not add
`InquiryEvent`, `ServiceEvent`, `AssessmentEvent`, `PressureEvent` unless you
find a genuine impossibility result showing the existing ontology cannot express
the required distinction. If so, document the minimal counterexample before
widening anything. Likewise, do not reopen Reflective Integrity or the
traderization layer unless an exact incompatibility is found. The current
four-history-type/event-sourced architecture is an acceptance constraint.

## Suggested implementation shape

Prefer a local module such as `src/inquiry.py` containing only the new
integration waist. Reuse the old CIS environment/policy/service code where
semantically appropriate. Update `src/toy.py` so the canonical Stage B is reached
through inquiry. Add `tests/test_inquiry.py`. Keep old tests intact wherever
possible. Update the canonical trace so the human-readable run shows the new
intermediate states.

## Required test/invariant package

At minimum establish executable tests for: (1) a real Stage-A charged result
derives the inquiry need; (2) deriving Need mutates no ledger, standing, or
allowance/account; (3) `Probe` goes through ordinary `Gamma`, not an oracle; (4)
raw outcome alone does not change `Sigma` / eliminate worlds; (5) settlement
changes the epistemic stage before any reason exists; (6) the canonical
settlement supports a valid diagnostic service certificate; (7) historical
service persists under extension; (8) service does not append a reason; (9)
assessment admits the proposal corresponding to the existing `e:revalue`; (10)
appending that `ReasonOcc` alone does not alter standing; (11) existing
`a:revalue` then produces the intended old Stage-B result; (12) `J0` remains
untouched after revaluation; (13) only the later existing Stage C moves `J0 ->
J1`; (14) Probe and Wait policies produce different trajectories under identical
service semantics; (15) same `PC(Sigma)` with different procedural provenance can
produce different service verdicts; (16) inquiry/service/assessment cannot mint
or increase allowance; (17) RI remains `Good` at every historical state; (18)
existing repository tests remain green except for intentional canonical-trace
updates.

Also make visible, preferably through distinct testable snapshots: `T0` Need
live, no interaction; `T1` raw Probe outcome, no settlement; `T2` settlement
admitted, epistemics moved, service certifiable, no `ReasonOcc`, standing
unchanged; `T3` `ReasonOcc` appended, standing unchanged; `T4` NormEvent revalues
`v0 -> v1`, `J0` unchanged; `T5` later NormEvent `J0 -> J1`.

## Research questions to resolve through the build

Do not spend the whole round abstractly debating these. Build the simplest
candidate, test it, and report what breaks.

Q1. Inquiry identity. Is `(StandingId, InquiryKey)` sufficient, with `AnsRoot`
supplying current custody, or is episode identity genuinely needed in the request?

Q2. Settlement provenance. What is the narrowest frozen provenance bridge that
lets `ValidCert` verify the designated action/procedure without widening `sem_L`
or the reason-source sorts?

Q3. CIS reuse. Can the August-23 `ServiceSpec`/`Env` machinery survive behind a
small adapter, or does the post-settlement architecture force a cleaner
settlement-backed service type?

Q4. Assessment thinness. Can `AdmissibleAssessment` remain a checker over
proposed `ReasonOcc`s without needing hidden inference/update machinery?

If one of these forces a change, identify the exact smallest failing example.

## What not to do

Do not build a general MDP/POMDP/action theory; design a substantive decision
theory; solve optimal inquiry scheduling; solve the `eta`/grant problem; make
pressure itself normative authority; let service encode the desired conclusion;
let assessment directly mutate standing; let inquiry directly revise
beliefs/norms; add new historical object kinds just because they make
implementation easier; rewrite RI, reason representation, or traderization
wholesale; or duplicate existing liability formulas or existing service results
when an adapter suffices.

## Deliverables

1. A running extension of the end-to-end toy. 2. Tests implementing the invariant
package above. 3. Updated deterministic `TRACE.txt` showing the inquiry loop. 4. A
concise `INQUIRY_INTEGRATION.md` explaining the final types/interfaces; the exact
trajectory; what was reused; what had to change; answers to Q1–Q4; any failed
designs/counterexamples; and which claims are implementation facts vs theorem
candidates. 5. Update `ARCHITECTURE.md` / README only where the integration
actually crystallizes something; do not rewrite narrative gratuitously.

End with a verdict in one of these forms:
`INQUIRY-LOOP-CLOSES-WITHOUT-WIDENING` if the four historical types and existing
waists suffice; or `INQUIRY-LOOP-FORCES-WIDENING` with the smallest explicit
type-level counterexample showing why.

The standard is not "the demo works." The standard is: the agent/world return
loop works while every layer continues to own exactly one job.

In particular, try to make the final executable architecture visibly realize:
normative standing -> traderized force -> liability pressure -> derived inquiry
need -> ordinary action -> raw outcome -> settlement -> historical service
certificate -> defeasible assessment -> ReasonOcc -> licensed NormEvent ->
accountable normative succession, and prosecute any shortcut that collapses
adjacent arrows.
