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
