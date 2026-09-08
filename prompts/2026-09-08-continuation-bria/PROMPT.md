# Dispatch — 2026-09-08 continuation BRIA

Five messages, all verbatim as sent.  The second is the pressure pass dispatched
against the first's result; the third the final correctness pass dispatched against the
second's; the fourth the allowance-timing audit dispatched against the third's; the fifth
the closing pass with merge authorization and two mid-dispatch additions.

## Message 1

You are working in `A-M-Berns/alignment-workspace`.

This is a focused research round on the dynamic-competence gap in the corrigibility
program:

    can BRIA-style bounded inductive rationality be lifted from one-step choices
    to long-running continuation plans, while retaining the features that made
    BRIA attractive in embedded/self-referential settings?

The intended downstream consumer is PRIORITIES item 86:

    bounded competence against legitimate continuation policies under
    endogenous admissibility.

Do NOT try to solve corrigibility as a whole.
Do NOT redesign Legitimate Evolution.
Do NOT assume ordinary policy regret is the correct primitive rationality criterion.
Do NOT force the final result to be positive.

The main research question is:

    What is the weakest mathematically clean non-myopic extension of BRIA
    that (a) is actually constructible by a bounded agent,
    (b) tests long-run advice using realized outcomes rather than a table of
        counterfactual rewards,
    (c) composes with the existing constitutional gate,
    and (d) can serve as one input to a later policy-regret theorem?

The round should distinguish sharply:

    BRIA criterion
    BRIA auction construction
    finite-horizon continuation competence
    growing-horizon continuation competence
    full policy regret.

These are not the same claim.

======================================================================
0. PRIMARY SOURCE AND REPOSITORY CONTEXT
======================================================================

Read the source paper closely:

    Caspar Oesterheld, Abram Demski, Vincent Conitzer
    “A Theory of Bounded Inductive Rationality”
    TARK 2023
    arXiv:2307.05068

Use the paper itself as the authority for BRIA.

At minimum inspect carefully:

- §2 Setting
- §4 Rationality criterion
- §5 / Appendix A.2 construction and proof
- §6 guaranteed-option / lower-bound theorems
- §8 comparison with regret learning
- Appendix C discussion of regret / policy-style learning / biased testing
- the footnote in the construction mentioning combinatorial auctions and
  “cross-decision optimization”, but do NOT read more into that sentence than it says.

Important source facts to preserve:

1. `DP_t` is finite.
2. Only the actually received reward `r_t` is primitive.
   Counterfactual rewards of unchosen options are deliberately not defined.
3. Future `DP_t` may depend on the agent’s previous choices.
4. The theory nevertheless explicitly targets MYOPIC optimality:
   current reward is optimized regardless of effects on future decision problems.
5. A hypothesis has the same basic type as an estimating agent:
       recommendation + promise.
6. Testing a hypothesis means actually following its recommendation.
7. Coverage says, roughly:
       a hypothesis that keeps outpromising the agent may not be rejected forever
       without accumulating arbitrarily bad empirical record on actual tests.
8. The auction/wealth construction is one implementation of the criterion.
9. Theorem 3-style guarantees work by supplying a hypothesis whose promise is a
   genuine lower bound when its recommendation is followed.
10. The paper is explicitly skeptical of making ordinary counterfactual regret the
    primitive rationality criterion in its fully embedded setting.

Repository context to inspect:

- PRIORITIES.md item 86
- projects/deference/rounds/2026-09-06-decision-theory-bill/
  especially:
    CANDIDATE_DECISION_THEORIES.md
    NORMATIVE_CHOICE_THEOREM.md
    CORRIGIBILITY_CONNECTION.md
    tests implementing the endogenous-admissibility / amendment-investment failure
- the current Corrigibility wiki
- the current Deference wiki
- the static gated-choice Lean work
- the legitimate-deference work currently landing, only insofar as it constrains
  the eventual value interface
- the interactive-factorization / continuation-policy definitions already present
  in the workspace, if any

Do not import a generic RL framework before checking whether the BRIA structure itself
already gives the right first theorem.

======================================================================
1. FIRST QUESTION: IS FIXED-HORIZON NON-MYOPIA JUST ORDINARY BRIA?
======================================================================

Pressure this claim first:

    For a FIXED horizon m, non-myopic BRIA may require no new rationality criterion.

At a macro-time k, starting from primitive history H_t, let an option be an m-step
CONTINGENT CONTROLLER

    q : future histories during the lease -> primitive actions

rather than an open-loop action sequence.

Define an execution wrapper

    Exec_m(H_t, q)

which runs q for m primitive steps while:

- exposing it to actual subsequent observations/history;
- applying the existing constitutional/admissibility gate at every primitive step;
- allowing authorized changes to the admissibility structure;
- leaving the protected principal / exterior response process live;
- preserving correction/inquiry mechanisms;
- recording the actual realized primitive rewards.

Define one macro reward, e.g.

    G^m_k(q)
      := (1/m) Σ_{j < m} r_{t+j}

or a more general bounded declared block-return functional.

Only the return of the ACTUALLY EXECUTED controller should be primitive.

Now ask whether the macro-process

    DP'_k = finite menu of available m-step controllers
    c'_k  = chosen controller
    r'_k  = G^m_k(chosen controller)

is literally an instance of the original BRIA setting.

Important:

    original BRIA already allows DP'_{k+1} to depend on earlier chosen controllers.

So endogenous future admissibility by itself may NOT be the missing structure.

Prove or refute:

    FIXED-HORIZON REDUCTION THEOREM

    Every ordinary BRIA over the induced macro-decision process is a bounded
    inductive learner over m-step continuations, with exactly the original
    no-overestimation and coverage guarantees.

Be precise about:

- finiteness of macro menus;
- encoding/computability of controllers;
- what information a controller sees;
- whether the environment or gate can interrupt execution;
- whether the macro process still satisfies the source theorem’s assumptions;
- computational overhead.

If this is basically definitional, say so. Do not inflate it into a new theorem.

======================================================================
2. USE THE EXISTING ENDOGENOUS-ADMISSIBILITY FAILURE AS THE FIRST FIXTURE
======================================================================

Take the exact current fixture where the myopic gated learner is legitimate but loses
linearly to a legitimate continuation that:

    pays a short-term cost
      -> makes an authorized amendment
      -> obtains a persistent later benefit.

Show the following distinctions explicitly.

A. Ordinary one-step gated BRIA can rationally remain myopic.

B. For sufficiently large fixed m, an m-step continuation option can expose the
   investment benefit inside ONE macro reward.

C. Determine the minimal m required in the exact fixture.

D. If the benefit lies strictly beyond m, the fixed-horizon learner can still fail.

This should establish:

    endogenous admissibility is not, by itself, the hard problem;
    temporal credit assignment at the testing granularity is.

======================================================================
3. WHAT EXACTLY IS A CONTINUATION HYPOTHESIS?
======================================================================

Do not identify a BRIA hypothesis with a bare policy.

Original BRIA hypotheses supply:

    recommendation h^c_t
    promise        h^e_t.

The non-myopic analogue should retain this structure.

Candidate:

    h(H_t) = (q_{h,t}, e_{h,t})

where

    q_{h,t}
        is a contingent continuation controller from the CURRENT history;

    e_{h,t}
        is a contextual promise about the bounded return obtained if q_{h,t}
        receives the declared execution treatment from THIS history.

Pressure whether this should instead be:

- a policy plus value estimate;
- a stateful decision procedure;
- a policy generator;
- a controller + continuation message/state;
- something else.

The promise must remain context-sensitive.

Use the BRIA paper’s biased-testing discussion as a central test:
raw average historical performance of policy π is generally not enough, because π may be
tested on systematically different decision problems.

Construct the corresponding dynamic fixture in our setting:

    Policy A is genuinely pointwise better than policy B,
    but the testing scheduler gives A hard states and B easy states,
    so raw observed policy averages rank B above A.

Show how contextual promises can avoid this failure in the BRIA manner.

This should answer:

    Why continuation-BRIA should be a theory of
        “plans + accountable contextual promises”
    rather than an ordinary bandit over named policies.

======================================================================
4. TESTING A CONTINUATION: DEFINE THE LEASE SEMANTICS
======================================================================

Original BRIA:

    testing h at t
      := choose h^c_t at t.

This is no longer sufficient.

Construct a delayed-benefit fixture:

    h recommends:
        pay cost now;
        continue according to plan for m steps;
        receive large benefit at the end.

If the learner:

    takes only h’s first action
    then switches to another hypothesis
    then scores h on the resulting low return,

it falsely “refutes” a genuinely good plan.

Use this to establish a necessity result:

    some notion of CONTINUATION EXECUTION RIGHTS is required to test
    temporally extended promises.

Provisional name:

    execution lease.

Define the weakest useful lease semantics.

Important: the lease should control only the advisor/learner-side continuation relevant
to the test. It must NOT freeze:

- the protected principal;
- exterior responses;
- constitutional correction;
- authorized amendments;
- inquiry;
- settlement arrivals.

Try to express this using the existing interactive factorization:

    q = tested advisor-side continuation
    z = still-live exterior/principal response policy.

A lease should be:

    enough commitment to make the hypothesis empirically testable,
    but not enough commitment to defeat corrigibility.

Produce exact fixtures separating:

1. one-step pseudo-test — invalid evidence against delayed plan;
2. full hard commitment that blocks correction — competence at cost of corrigibility;
3. advisor-side lease with live principal/exterior — intended middle object.

======================================================================
5. GATING AND TESTING MUST COMPOSE CLEANLY
======================================================================

The BRIA layer should NOT have to know the substance of legitimacy.

Define an abstract execution wrapper such as

    Exec^G_m(H, q)

where G is the existing gate / admissibility mechanism.

At each primitive step:

    proposed action
      -> gate
      -> actual action / inquiry / refusal
      -> next state.

Ask which comparator object is correct:

A. “legitimate controller”
   q whose own proposals are always admitted on its induced trajectory;

B. arbitrary q, evaluated by its GATED/TRUNCATED execution;

C. both, with A as the meaningful comparator class and B as the safe operational domain.

Strong candidate:

    every hypothesis may be tested operationally through the gate;
    the competence theorem’s clean comparators are controllers for which the gate
    is transparent.

Prove a transparency lemma of the form:

    q legitimate along Exec(q)
      -> Exec^G(q) = Exec(q)

under the exact existing gate semantics.

Do NOT re-prove constitutional safety inside BRIA.

======================================================================
6. FIXED-HORIZON COMPETENCE THEOREM
======================================================================

Try to obtain a theorem almost directly from original BRIA Theorem 3.

Suppose for every macro-round k there is an efficiently identifiable m-step controller

    q_k ∈ DP'_k

and an efficiently computable lower bound L_k such that whenever q_k is actually
executed under the macro test,

    G^m_k(q_k) ≥ L_k.

Then ordinary BRIA on the macro sequence should imply something like:

    liminf_K
      (1/K) Σ_{k≤K} G^m_k(α_k)
        ≥
    liminf_K
      (1/K) Σ_{k≤K} L_k.

For equal m, translate this exactly into primitive-time average reward.

Check all quantifiers and source assumptions.

Call this, provisionally:

    Fixed-Horizon Continuation Competence.

Classify carefully:

- SOURCE/PAPER: original BRIA theorem;
- DERIVED: macro reduction;
- LEAN/FIX if formalized here;
- EXT: any environmental interpretation.

If the reduction is genuinely trivial, do not register a grand claim.
But make the theorem chain explicit enough that later work can consume it.

======================================================================
7. FIND THE PRECISE POINT WHERE FIXED m FAILS
======================================================================

Construct several delayed-benefit families:

- benefit at m+1;
- benefit at 2m;
- benefit after an environment-dependent finite delay;
- benefit after a growing delay;
- irreversible amendment whose value appears only much later.

Characterize exactly what fixed-horizon continuation competence does and does not imply.

A useful concept may be:

    horizon-m detectable advantage.

For example:

    continuation q has an m-detectable advantage δ at H

if its superiority is already visible in the declared m-block return from H.

Do not canonize this term unless useful.

The purpose is to isolate why m must eventually grow.

======================================================================
8. VARIABLE HORIZONS: THE FIRST GENUINELY NEW MATHEMATICS
======================================================================

Now let macro-block k have primitive duration

    m_k,

possibly with

    m_k -> ∞.

Let

    G_k ∈ [0,1]

be the average primitive reward over block k.

Original BRIA controls averages over MACRO ROUNDS:

    (1/K) Σ G_k.

But primitive-time performance is

    [Σ m_k G_k] / [Σ m_k].

These differ when block lengths vary.

This suggests a WEIGHTED BRIA criterion.

Investigate the exact weighted analogue.

Candidate weighted no-overestimation:

    limsup_K
      [Σ_{k≤K} m_k (α^e_k - G_k)]
      /
      [Σ_{k≤K} m_k]
      ≤ 0.

Candidate record for h:

    ℓ^h_K
      =
    Σ_{k∈M_h, k≤K}
      m_k (G_k - h^e_k).

Candidate coverage:

    if h outpromises α infinitely often,
    either rejection eventually stops,
    or its weighted record along rejection/test occasions tends to -∞
    in the appropriate sense.

Pressure all of this.

Questions:

1. Is multiplying by m_k the correct weight when G_k is a per-time average?
2. What if the declared return is discounted rather than average?
3. Is the natural primitive a general positive test weight w_k rather than duration?
4. Which original BRIA lemmas port syntactically?
5. Which fail?
6. Does weighted coverage still give a useful guaranteed-option theorem?
7. Can the original criterion simply be applied to a time-expanded sequence instead?
   If yes, compare the two formulations and take the simpler one.

Do not assume weighted BRIA is necessary until alternatives are ruled out.

======================================================================
9. GENERALIZE OR BREAK THE AUCTION/WEALTH CONSTRUCTION
======================================================================

This is the highest-value technical part.

Audit the original construction line by line.

Original qualitative structure:

    allowance
      +
    wealth-limited bid
      +
    winner’s realized reward
      -
    winner’s bid

and the wealth identity yields both:

    no systematic overestimation
    hypothesis coverage.

For weighted tests, one candidate is to measure wealth in TOTAL primitive reward units.

If block k has weight w_k (= m_k in the first model), and hypothesis h promises
per-unit reward e_{h,k}, then a full test exposes h to liability of order

    w_k e_{h,k}.

Candidate bidding rule:

    per-unit bid
      =
    min(e_{h,k}, W_h / w_k)

or equivalently bid total promised return subject to wealth.

Candidate winner update:

    W_h'
      =
    W_h
      + allowance
      + w_k (G_k - charged_estimate).

DO NOT accept this formula without reproducing the source proof carefully.

Establish:

A. exact weighted wealth identity;

B. weighted no-overestimation from nonnegative wealth plus sublinear total allowance;

C. coverage:
   a persistently outpromising hypothesis that is not tested infinitely often
   must eventually become unconstrained enough to win;

D. computability:
   only finitely many hypotheses need active simulation per macro-round.

The new issue is capital adequacy for long tests.

A hypothesis wanting an m_k-step lease may need O(m_k) wealth before its promise can bid
unconstrained.

Original “infinite cumulative allowance per hypothesis” may no longer suffice if m_k
grows too quickly.

Find the SHARP or at least clean sufficient relationship among:

    horizon growth m_k
    per-hypothesis cumulative allowance A_i(K)
    total allowance
    total primitive time S_K = Σ_{k≤K} m_k.

Strong candidate conditions:

    A_i(K) / m_K -> ∞        for every fixed i

and

    [Σ_i A_i(K)] / S_K -> 0.

But pressure whether these are:
- sufficient;
- necessary;
- stronger than needed;
- compatible with finite-support / efficient allowance schedules.

Construct an explicit inhabiting schedule.

For example, investigate schedules in the family:

    m_k ≍ log k
    A(k,i) ≍ i^{-2} k^{-a}

for suitable a∈(0,1),

with finite-support modifications if necessary.

Prove exact asymptotics rather than handwave.

This may be the central NEW theorem:

    existence of a computable weighted-BRIA auction supporting unboundedly growing
    test horizons while total exploration subsidy is negligible per primitive time.

If false, produce the obstruction.

======================================================================
10. LONG TESTS AS LIABILITY / EXPERIMENTAL ATTENTION
======================================================================

Pressure the conceptual interpretation exposed by the weighted construction.

A one-step hypothesis risks one unit of realized payoff.

An m-step continuation hypothesis consumes m units of execution opportunity and may expose
the learner to m units of downside.

So perhaps:

    long plans SHOULD require more wealth to test.

Investigate whether the right interpretation is:

    hypothesis wealth = claim on experimental attention / execution time.

This has a potentially strong connection to the workspace’s liability/traderization work,
but DO NOT force the analogy.

Only keep it if there is an actual mathematical identity:
e.g. a lower bound showing that allowing arbitrarily long leases without corresponding
capital lets a bad hypothesis monopolize a non-negligible fraction of primitive time.

Construct an exact monopoly counterexample if possible.

======================================================================
11. GROWING-HORIZON CONTINUATION COMPETENCE
======================================================================

Assuming the weighted construction works, shoot for a theorem of roughly this form.

Let:

    m_k -> ∞
    max_{j≤K} m_j / Σ_{j≤K} m_j -> 0

or the exact non-dominance condition actually needed.

Let α be a weighted continuation-BRIA covering a declared computable class H_cont.

Suppose h∈H_cont makes sound contextual promises L_k on its tests:

    whenever h is granted its m_k-step constitutional lease at H_k,
    its realized block-average reward is at least L_k.

Then α cannot asymptotically achieve primitive-time reward below the relevant weighted
average of L_k.

Find the exact correct statement.

Then prove useful corollaries:

A. every fixed finite planning horizon is eventually subsumed;

B. delayed-investment fixture with any fixed finite payoff delay is eventually learned;

C. if a continuation’s advantage is detectable at some finite horizon uniformly often,
   α eventually captures it in the relevant average sense.

Be very precise about what is NOT obtained:
- no full own-trajectory policy comparison yet;
- no arbitrary irreversible hidden value;
- no future-principal value semantics yet.

======================================================================
12. PROMISE COMPLEXITY VS POLICY COMPLEXITY
======================================================================

This is conceptually important.

Original BRIA’s guaranteed-option theorem needs more than an easy-to-execute option:
it uses an efficiently computable hypothesis with a computable promise/lower bound.

So distinguish:

    policy/controller complexity
    promise/value-estimation complexity.

A policy may be easy to execute while its value is computationally opaque.

The bounded-rational comparator class may therefore naturally be:

    H_cont
      =
    efficiently computable
      (continuation recommendation + contextual promise)

rather than:

    all efficiently computable policies.

Pressure whether this is:
- an unavoidable feature;
- too weak;
- exactly analogous to source BRIA;
- broadenable because a hypothesis can LEARN its own promise from past tests.

Construct examples:

1. easy policy, hard-to-compute value;
2. hypothesis whose value estimate improves from empirical lease outcomes;
3. good plan with no computationally accessible way to recognize its goodness.

State honestly which one a bounded learner should be required to compete with.

======================================================================
13. DO NOT CONFLATE CONTINUATION COMPETENCE WITH POLICY REGRET
======================================================================

Define the distinction explicitly.

At actual learner history H_t^α, continuation testing observes something like

    G_m(π | H_t^α).

Full external policy regret compares against the history that would have occurred if π
had been followed:

    H_t^π.

These may differ arbitrarily.

Construct a sharp irreversible-history counterexample:

- At t=0 there are two legitimate irreversible branches A and B.
- The environment hides which is good until after commitment.
- Once α enters A, testing B “from the current history” cannot reproduce the world in
  which B was chosen at t=0.
- Both policies are legitimate.
- No learner can get sublinear regret against the hindsight-best own-trajectory policy
  in the unrestricted class.

Use this to prove or strongly establish:

    continuation-BRIA does NOT by itself imply policy regret.

Then define a decomposition/bill for a later theorem.

Candidate conceptual decomposition:

    policy-regret gap
      ≤
    continuation-learning error
      +
    finite-horizon truncation error
      +
    history-shift / counterfactual-stability error
      +
    block-boundary / exploration error.

Do not assert this exact inequality unless you can type it cleanly.

But isolate the HISTORY-SHIFT term mathematically.

This may connect to the existing workspace idea of counterfactual stability / replay distortion.
Search the workspace before inventing a duplicate concept.

======================================================================
14. WHAT ADDITIONAL ENVIRONMENTAL CONDITION WOULD RECOVER POLICY REGRET?
======================================================================

This is exploratory but important.

Test several candidate classes:

- episodic reset;
- exact reset to a common state;
- bounded-memory environments;
- mixing/ergodic systems;
- recoverable endogenous admissibility;
- reversible amendments;
- eventually stable admissibility;
- bounded influence of a finite prefix;
- policy-value continuity under bounded history perturbation.

For each, ask:

    Does testing π for growing leases from α’s actual histories approximate
    π’s own full-policy performance closely enough for a policy-regret corollary?

Prefer one abstract condition over six special cases if it becomes clear.

Candidate abstract quantity:

    B_T(π)
      :=
    discrepancy between
      evaluating π from α-reached histories
    and
      evaluating π on π’s own induced history.

Then:

    B_T(π)=o(T)

might be the exact additional consumer assumption.

But do not canonize this unless it survives fixtures.

This section can legitimately end OPEN.

======================================================================
15. RELATION TO THE ULTIMATE CORRIGIBILITY THEOREM
======================================================================

At the end, give an exact interface to the existing architecture.

The desired composition should look like:

A. CONSTITUTION

    Legitimate Evolution
      + Robust Openness
      + authorization semantics
      + static gate

    -> safe primitive execution wrapper Exec^G.

B. DYNAMIC BOUNDED COMPETENCE

    continuation-BRIA over Exec^G

    -> cannot systematically underperform
       sound efficiently computable legitimate continuation hypotheses
       under actual growing-horizon tests.

C. TESTABILITY / RECOVERABILITY

    actual-history continuation tests
       approximate
    own-induced-policy performance.

D. OPTIONAL EXTERNAL PERFORMANCE COROLLARY

    B + C
      ->
    low policy regret against an appropriate legitimate policy class.

Keep deference separate:

    authoritative future-principal value may later be one source of bounded return /
    evaluation for continuation hypotheses,

but this round should first establish the dynamic learning theorem for a generic bounded
realized return.

Do not entangle authorship/value semantics with the BRIA extension.

======================================================================
16. ADVERSARIAL FIXTURES
======================================================================

At minimum build exact fixtures for:

A. myopic amendment failure:
   one-step BRIA loses to legitimate investment continuation.

B. fixed-horizon rescue:
   sufficiently large m makes investment superior as a macro-option.

C. horizon-too-short:
   benefit lies at m+1 and fixed-m BRIA still misses it.

D. invalid one-step “test”:
   delayed plan falsely appears bad if control is removed after first action.

E. anti-corrigible hard commitment:
   a lease that freezes principal correction makes the plan testable but violates
   constitutional requirements.

F. gated lease:
   advisor continuation is stable while principal/exterior correction remains live.

G. biased policy testing:
   raw empirical averages reverse two policies because they are tested on different
   state distributions.

H. contextual-promise repair:
   BRIA-style promises correctly normalize the same fixture.

I. long-test monopoly:
   if lease duration is not charged in wealth/attention, one bad hypothesis can consume
   a non-negligible or dominant share of primitive time.

J. allowance-too-slow:
   horizon growth outruns a hypothesis’s ability to finance a test, so a persistently
   outpromising hypothesis can be starved.

K. feasible horizon/allowance schedule:
   exact schedule satisfying all weighted-construction requirements.

L. history-shift impossibility:
   local continuation testing cannot recover the value of an irreversible policy branch
   that had to be selected earlier.

M. recoverable environment:
   reset/mixing fixture where local tests DO recover policy performance.

N. easy-policy/hard-value:
   computable controller whose good value has no comparably easy promise.

O. learning hypothesis:
   hypothesis learns an increasingly accurate promise about a fixed controller from
   its own lease outcomes.

======================================================================
17. FORMALIZATION TARGETS
======================================================================

Lean is useful only for small exact algebraic cores.

High-value possible Lean targets:

- macro-block average identity for equal block lengths;
- weighted primitive-time / block-time accounting identities;
- weighted wealth telescoping identity;
- sufficient conditions implying weighted no-overestimation;
- transparent-gate execution lemma, if current types make it small;
- exact finite counterexamples A–L where appropriate;
- horizon/allowance asymptotic lemmas if cleanly expressible.

Do NOT formalize:
- a giant MDP library;
- generic causal semantics;
- the whole original BRIA paper;
- policy regret in full generality

unless a very small reusable theorem genuinely requires it.

Executable exact-rational fixtures are acceptable for exploratory/negative results.

======================================================================
18. EVIDENCE DISCIPLINE
======================================================================

Use:

PAPER
    statement actually established by Oesterheld–Demski–Conitzer.

DERIVED
    direct mathematical consequence / reduction from the PAPER theorem,
    with derivation supplied.

LEAN
    kernel-checked new theorem in the workspace.

FIX
    exact finite/executable witness.

EXT
    external semantics such as “this gate corresponds to actual corrigible execution”.

OPEN
    unresolved.

Be especially careful:

- “BRIA permits endogenous future decision problems” = PAPER.
- “BRIA handles non-myopic planning” = FALSE.
- “fixed-m macro-BRIA is an ordinary BRIA instance” = DERIVED only after exact typing.
- “growing-horizon weighted auction exists” = NEW, prove it.
- “continuation-BRIA gives policy regret” = do NOT say this without a testability theorem.
- “all computable good policies are covered” = likely too strong unless promise complexity
  is addressed.
- “combinatorial auctions solve cross-decision optimization” = NOT in the paper;
  the paper contains only a suggestive footnote.

======================================================================
19. DELIVERABLES
======================================================================

Create a new round, suggested name:

    projects/deference/rounds/2026-09-08-nonmyopic-bria/

or, if the resulting concept is clearer,

    .../continuation-bria/

At minimum write:

1. REPORT.md
   - one verdict
   - what ports from BRIA unchanged
   - what is genuinely new
   - strongest theorem established
   - strongest impossibility established
   - exact downstream implication for item 86

2. BRIA_SOURCE_AUDIT.md
   - source-paper definitions/theorems actually used
   - theorem numbers / sections
   - what the paper explicitly does NOT claim
   - mapping source object -> our object

3. FIXED_HORIZON.md
   - macro-option reduction
   - exact theorem
   - amendment fixture
   - computational/typing conditions

4. CONTINUATION_HYPOTHESES.md
   - controller + contextual promise
   - test/lease semantics
   - biased-testing analysis
   - policy vs hypothesis distinction

5. WEIGHTED_BRIA.md
   - proposed weighted criterion
   - construction
   - wealth algebra
   - horizon/allowance conditions
   - computability
   - theorem or exact obstruction

6. GROWING_HORIZON.md
   - theorem statement
   - what delayed plans become learnable
   - remaining horizon error

7. POLICY_REGRET_FRONTIER.md
   - actual-history tests vs own-policy history
   - impossibility witness
   - candidate history-shift distortion term
   - recoverability/testability conditions
   - exact boundary between BRIA result and later policy-regret theorem

8. CORRIGIBILITY_COMPOSITION.md
   - existing constitutional gate as execution wrapper
   - no duplication of legitimacy
   - exact interface into item 86
   - what a future corrigibility theorem would consume

9. COUNTERMODELS.md
   - fixtures A–O

10. FOR_HUMANS.md
   - explain the core idea without jargon:
       “BRIA knows how to test advice that pays off immediately.
        We want to test advice like ‘take a cost now because this plan pays later’
        without handing that plan irreversible control and without pretending we know
        what untried policies would have done.”

If the result is strong enough, refine PRIORITIES item 86 in place.
Do not mark it answered unless the theorem actually supplies bounded competence at the
strength the item asks for.

Do not update the canonical wiki unless the round establishes a stable theorem-level
correction. If it does, keep the wiki edit narrow.

======================================================================
20. DECISION TREE / STOP CONDITIONS
======================================================================

The round should be willing to stop at any of these outcomes.

OUTCOME A — STRONG POSITIVE

    Fixed-horizon reduction is exact;
    weighted/growing-horizon BRIA is constructible;
    growing-horizon continuation competence is proved;
    policy-regret bridge remains a separately typed recoverability assumption.

Possible verdict:

    GROWING-HORIZON-CONTINUATION-BRIA-SURVIVES

OUTCOME B — PARTIAL POSITIVE

    Fixed-horizon reduction works;
    variable horizons expose a genuine construction obstruction.

Verdict:

    FIXED-HORIZON-PORTS-WEIGHTED-BRIA-BLOCKED-BY-X

OUTCOME C — CRITERION FAILURE

    There is a counterexample showing that the natural continuation-BRIA criterion
    itself is incoherent or rewards pathological behavior.

Verdict:

    CONTINUATION-BRIA-CRITERION-FAILS-BECAUSE-X

OUTCOME D — POLICY-REGRET SEPARATION

    Continuation-BRIA works but cannot imply policy regret without an additional
    history-shift / recoverability condition.

This is EXPECTED and counts as success.

Verdict:

    CONTINUATION-COMPETENCE-SURVIVES-POLICY-REGRET-NEEDS-RECOVERABILITY

Do not choose the strongest verdict just because the fixtures pass.

======================================================================
21. THE QUESTION I MOST WANT ANSWERED
======================================================================

At the end I want a mathematically precise answer to:

    If an efficiently computable hypothesis says,

        “from the state you are actually in,
         give me control of the advisor-side continuation for long enough,
         subject throughout to the constitution,
         and I can deliver at least L,”

    what does bounded inductive rationality require the learner to do with that claim?

And then:

    under what additional assumptions does successfully answering THAT question imply
    the stronger external statement

        “the learner performs nearly as well as the best legitimate continuation
         policy on that policy’s own induced trajectory”?

The first is the non-myopic BRIA problem.

The second is the policy-regret problem.

Do not collapse them.

---

## Message 2

You are working in `A-M-Berns/alignment-workspace`, on the current open PR #95:

    Continuation BRIA: leases, the weighted auction, and the policy-regret frontier

Branch:

    round/2026-09-08-continuation-bria

This is a PRESSURE + REFINEMENT pass on PR95 before merge.

Do NOT start a new broad research direction.
Do NOT redesign BRIA.
Do NOT redesign the corrigibility architecture.
Do NOT merge.

The goal is to determine the strongest version of the current result that is actually
true, correctly typed, and useful downstream — and to repair PR95 in place.

The round has found a promising spine:

    fixed-horizon continuation options
        -> ordinary BRIA
        -> variable horizons
        -> weighted BRIA / execution-time accounting
        -> growing-horizon competence against continuation hypotheses
        -> promise slack + history shift
        -> conditional policy-regret corollary under recoverability.

That spine should survive if possible.

But several claims need hard pressure before they are ready for main.

======================================================================
0. READ FIRST
======================================================================

Read the current PR95 branch, not only the PR description.

At minimum:

- projects/deference/rounds/2026-09-08-continuation-bria/
  - REPORT.md
  - BRIA_SOURCE_AUDIT.md
  - FIXED_HORIZON.md
  - CONTINUATION_HYPOTHESES.md
  - WEIGHTED_BRIA.md
  - GROWING_HORIZON.md
  - POLICY_REGRET_FRONTIER.md
  - CORRIGIBILITY_COMPOSITION.md
  - COUNTERMODELS.md
  - FOR_HUMANS.md

- lean/Workspace/Deference/Contrib/ContinuationBRIA.lean

- tests and `src/`

- PRIORITIES.md item 86 as modified by PR95

Also re-read the source paper sections actually used:

    Oesterheld, Demski, Conitzer
    “A Theory of Bounded Inductive Rationality”

especially:
- setting;
- BRIA criterion;
- construction / allowance proof;
- guaranteed-option theorem;
- biased-testing discussion;
- regret discussion.

The source paper is the authority on what is PAPER.

======================================================================
1. FIRST PRESSURE POINT: THE EXISTENCE THEOREM HAS AN EFFECTIVITY ISSUE
======================================================================

PR95 currently claims, roughly:

    a computable weighted BRIA covering the e.c. class exists
    iff
    m_K / S_K -> 0.

The sufficiency proof currently chooses a computable decreasing upper envelope

    ρ̄_K >= ρ_K
    ρ̄_K -> 0

for

    ρ_K := (M_K + 1 + log K) / S_K,

and defines the active support from ρ̄.

This is NOT automatic for an arbitrary computable sequence ρ_K -> 0.

A computable convergent sequence need not have a computable modulus of convergence.
A computable monotone majorant tending effectively to zero would itself provide such
information.

So audit the theorem from scratch.

Distinguish at least these claims:

A. Mathematical non-dominance:

       m_K / S_K -> 0.

B. Effective non-dominance:

       the schedule comes with enough computable tail information / a computable
       majorant / modulus to construct the support and allowances.

C. Uniform construction:

       one algorithm takes a code for any computable non-dominant schedule and
       produces the weighted BRIA.

D. Nonuniform existence:

       for each computable non-dominant schedule, some computable weighted BRIA exists,
       without necessarily being uniformly obtainable from the schedule code.

These are different.

Determine exactly which are true.

Do not settle for “the current construction uses a modulus” if a better construction avoids it.

Try hard to answer:

    Is there a computable allowance/support construction depending only on the
    OBSERVED prefix of a computable non-dominant schedule that always achieves

        A_i(K) - m_K -> ∞       for every fixed i

    and

        totalAllowance(K) / S_K -> 0

    without assuming an effective convergence rate?

If YES:
- construct it;
- prove it;
- replace the current ρ̄ argument.

If NO:
- give a precise impossibility/diagonal argument;
- weaken the existence theorem accordingly.

At minimum preserve the explicit usable case:

    m_k = floor(log_2 k) + 1

or another clean declared schedule with fully proved computable allowance.

For our downstream corrigibility application we choose the schedule, so

    explicit effective schedules

may be all that is actually needed.

But do not call the theorem “sharp iff non-dominance” unless the computability quantifiers
really support that statement.

======================================================================
2. AUDIT THE NECESSITY DIRECTION WITH THE SAME EFFECTIVITY DISCIPLINE
======================================================================

The dominant-block impossibility uses

    c := limsup m_K / S_K > 0

and an infinite set

    D = { K : m_K >= (c/2) S_K }.

For the adversarial hypothesis to belong to the e.c. class, the set on which it promises 1
must be effectively recognizable at the required complexity.

Do not casually call D computable if c is an arbitrary noncomputable real.

Repair the proof using the strongest true form, probably:

    if limsup m_K/S_K > 0,
    then there EXISTS a positive rational q such that

        D_q := {K : m_K/S_K >= q}

    is infinite,

and for a computable rational-valued schedule D_q is computable.

Check all quantifiers carefully.

State whether the impossibility is:

- for every computable dominant schedule;
- uniform in the schedule;
- merely existential;
- or something else.

Keep the criterion-level impossibility separate from failure of the particular auction.

======================================================================
3. SECOND PRESSURE POINT: TYPE THE POLICY-REGRET DECOMPOSITION CORRECTLY
======================================================================

Current `POLICY_REGRET_FRONTIER.md` says both:

    G_k(π | H^α)

is observed when π is tested and undefined otherwise,

and later sums

    G_k(π | H^α)

over every block in an exact regret identity.

Those cannot be the same object.

Repair the ontology.

There should probably be TWO layers.

A. BRIA-INTERNAL / REALIZED FEEDBACK

For block k only the executed controller has an observed return:

    G_k^obs ∈ [0,1].

This is all the BRIA criterion and wealth construction see.

No counterfactual reward vector is supplied.

B. EXTERNAL THEOREM SEMANTICS

The theorist may declare an interactive environment giving a counterfactual block evaluator

    Ĝ_k(π ; H)

or equivalently a rollout semantics

    β(H, π, z)

from which such a return can be computed.

This object may be used to STATE external policy regret and history shift.

It is not observed by the learner unless π is actually tested.

Then type the exact decomposition using Ĝ:

    V_T(π) - V_T(α)
      =
    Σ m_k [ Ĝ_k(π ; H^π_k) - Ĝ_k(π ; H^α_k) ]
      +
    Σ m_k [ Ĝ_k(π ; H^α_k) - L_k ]
      +
    Σ m_k [ L_k - G_k^obs(α) ]
      + boundary.

Call the terms whatever survives:

    history shift
    promise slack
    learning error
    boundary.

Prove the finite identity in Lean if useful.

The important conceptual statement is:

    continuation-BRIA never consumes counterfactual rewards;
    the policy-regret theorem does.

Make that distinction impossible to miss.

======================================================================
4. THIRD PRESSURE POINT: THE MAIN CONTINUATION theorem IS ABOUT PROMISES,
NOT ACTUAL POLICY PERFORMANCE
======================================================================

PR95 sometimes says things like:

    “the learner cannot asymptotically underperform any continuation hypothesis
     whose promises are sound”

or

    “its average is at least that of the continuation hypothesis.”

Pressure this.

The theorem currently proves, roughly:

    learner reward >= L_k

in weighted average,

where L_k is the hypothesis’s accountable promise.

It does NOT give

    learner reward >= actual block value of q_h

unless the promise is tight enough.

An excellent controller with a vacuous promise

    L_k = 0

does not force competence against its actual value 1.

So split the notions explicitly.

A continuation hypothesis is:

    h = (q, e)

where e is an ACCOUNTABLE CONTEXTUAL CLAIM.

It may be wrong.
It may start optimistic.
It may learn.
It may be refuted.

A SOUND comparator hypothesis satisfies, eventually or on the relevant tests,

    e_k <= Ĝ_k(q ; H^α_k).

A TIGHT / VANISHING-SLACK comparator additionally satisfies

    Σ m_k [Ĝ_k(q ; H^α_k) - e_k] = o(S_K).

Then:

THEOREM 1 — Continuation-promise competence

    learning error <= o(S_K)

against every sound covered hypothesis.

THEOREM 2 — Actual-history continuation competence

    if promise slack is o(S_K),

    Σ m_k [
      Ĝ_k(q ; H^α_k) - G_k^obs(α)
    ] <= o(S_K).

THEOREM 3 — Own-trajectory policy competence

    add history shift o(S_K).

This three-level hierarchy may be the mature theorem stack.

Repair every sentence in:
- PR description;
- REPORT;
- GROWING_HORIZON;
- PRIORITIES item 86

that skips the promise-slack term.

======================================================================
5. DO NOT DEFINE A BRIA PROMISE AS A LOWER BOUND
======================================================================

Current prose sometimes says that an “estimate” which is not a lower bound buys nothing.

That is too strong.

Original BRIA hypotheses are allowed to be wrong.
Their promise is what creates empirical accountability.

The learner discovers overpromising through losses.

This is essential to:
- the source construction;
- the learning-hypothesis fixture;
- the entire point of hypothesis wealth.

Use:

    continuation hypothesis
      = controller + contextual promise/estimate/claim.

Then define special classes:

    sound-on-tests
    eventually sound
    bounded-record
    tight
    vanishing-slack

as theorem hypotheses.

Do not bake “lower bound” into the generic hypothesis type.

Ask whether Theorem-3-style competence really needs pointwise soundness,
or whether the weakest useful condition is something like

    cumulative promise slack on test occasions is o(S_K)

or merely bounded below empirical record.

Find the weakest clean condition the proof actually consumes.

This could materially improve the theorem.

======================================================================
6. PRESS THE LEASE: WHAT IS REALLY NECESSARY?
======================================================================

The round currently calls a whole-block exclusive execution lease “the weakest useful lease.”

That may overstate the necessity result.

The true logical requirement seems closer to:

    the empirical treatment used to test h must match the treatment that h's promise
    is about.

If h promises:

    “if q receives uninterrupted advisor-side control for m steps, return >= L,”

then executing only a prefix of q and completing with another controller is not a test.

But there may be OTHER valid promise types, e.g.

    “if q is run under the declared interruption/exploration protocol τ, return >= L.”

Then an interrupted run could be a legitimate test of THAT claim.

So consider parameterizing the hypothesis by a declared execution treatment:

    τ_k

and interpret

    e_h,k

as a promise about

    Exec_{τ_k}(H_k, q_h,k).

Then:

    TestValidity:
       data counts against h only if generated by the same declared treatment.

A whole-block selection lease is one especially clean treatment.

It may remain the preferred realization because it gives temporally extended plans enough
causal continuity to exhibit their benefits while leaving the principal/exterior live.

But do not claim uniqueness unless proved.

Try to end with:

    semantic primitive:
        promise-treatment alignment;

    canonical realization:
        advisor-side execution lease through the constitutional gate.

This would make the theory more general and more precise.

======================================================================
7. KEEP CORRIGIBILITY LIVE DURING A TEST
======================================================================

Re-audit the execution-lease interpretation.

The lease may commit:

    which advisor-side continuation controller is being tested.

It must not commit:

- principal response policy;
- protected correction;
- gate behavior;
- authenticated settlement arrivals;
- authorized amendment;
- inquiry.

The clean interactive picture is still:

    q fixed for the test window,
    z live.

But check a deeper issue:

Suppose principal correction changes the state in such a way that q’s original promise
becomes impossible.

That should not be called an unjustified refutation if the original promise was explicitly
conditional on no such correction.

Conversely, if the promise was about the actual gated/exterior-live treatment, then the
correction IS part of the test outcome.

So force hypotheses to say what treatment they are promising under.

Do not smuggle counterfactual “absent intervention” assumptions into the score.

======================================================================
8. AUDIT THE DISCOUNTED-RETURN REMARK
======================================================================

WEIGHTED_BRIA currently suggests that discounted returns are essentially a bounded-weight
case because

    Σ_{j<m} γ^j <= 1/(1-γ).

Separate algebra from execution semantics.

For a FINITE truncated discounted lease, yes: its total weight is uniformly bounded.

For a genuinely infinite-horizon discounted return, the payoff is not available at a
finite atomic test time unless another settlement mechanism is supplied.

So do not claim:

    infinite discounted non-myopic BRIA reduces to ordinary BRIA

merely because discount mass is finite.

State exactly what is proved:

    uniformly bounded FINITE test weight
       -> rescaling to ordinary BRIA.

If you want to discuss infinite discounted promises, label the required deferred-settlement
mechanism OPEN.

======================================================================
9. AUDIT “EASY POLICY, HARD VALUE”
======================================================================

The current fixture uses a simple controller and a digit sequence such as sqrt(2) to argue
that policy complexity and value/promise complexity differ.

That does not establish the desired separation merely because the value is nontrivial.

The BRIA source uses explicit computational classes.

A sequence can be computable and still be “easy” in the only complexity class currently
named unless a resource separation is proved.

So either:

A. state the example only as conceptual:
       controller code and promise code are distinct computational objects;

or

B. build an actual complexity separation relative to a declared g(t):
       q computable in O(g)
       but no promise of the desired strength belongs to the covered hypothesis class;

or

C. use a diagonal / source-paper-style example that genuinely establishes the
   recognizability limitation.

Do not overclaim a complexity separation from “digit computation looks hard.”

======================================================================
10. CRITERION VS CONSTRUCTION VS FIXTURE
======================================================================

The current round discovered an important correction to item 86:

the old “myopic gated learner” was not a BRIA.

But there is still some slippage between:

    every BRIA satisfying the criterion

and

    the published auction construction.

Audit every fixture.

In particular, for the d=1 persistent amendment:

- a BRIA need not “invest infinitely often” once it enters an absorbing expanded state;
- the correct statement is conditional on revisiting base;
- the published auction may invest once and then remain expanded;
- the BRIA criterion itself can permit sparse experiments and later return to base,
  if its coverage/no-overestimation obligations remain satisfied.

State separately:

PAPER/CRITERION:
    what EVERY BRIA must do.

CONSTRUCTION:
    what the particular wealth auction does.

FIX:
    what the exact simulated ecology does.

Do not transfer behavior from the auction to the criterion.

Repair the sentence:

    “every one-step BRIA invests infinitely often”

to its actual quantified form.

======================================================================
11. RECHECK THE “SHARP” NON-DOMINANCE BOUNDARY
======================================================================

Assuming the effectivity repair in §§1–2, pressure whether non-dominance is really the
right criterion boundary.

The intuitive conflict is:

    coverage demands a test,
    but one test may consume a fixed fraction of all primitive time,
    and no-overestimation forbids paying that cost infinitely often.

This is elegant.

Try to state the strongest clean theorem in three layers:

I. Criterion impossibility:
   dominant blocks make weighted coverage + weighted no-overestimation jointly impossible
   for some tiny e.c. hypothesis class.

II. Auction sufficiency:
   under capital adequacy + negligible total allowance, the weighted auction is a weighted BRIA.

III. Schedule existence:
   characterize when allowances satisfying II exist, with the correct COMPUTABILITY qualifier.

Do not compress all three into one “iff” unless all quantifiers line up.

======================================================================
12. TRY TO STRENGTHEN THE GUARANTEED-CONTINUATION THEOREM
======================================================================

Current theorem assumes sound promises on tests.

Find the weakest useful empirical condition.

Original BRIA coverage only needs that an outpromising hypothesis cannot be rejected while
its record fails to diverge negatively.

So perhaps the continuation theorem can use:

    the hypothesis's weighted empirical record on its valid tests is bounded below,

rather than:

    every test satisfies G_k >= L_k.

Or an asymptotic condition:

    [Σ_{tests} m_k (L_k - G_k)]_+ = o(S_K).

Work out the exact theorem.

This matters for hypotheses that LEARN:
- they may overpromise finitely;
- they may have bounded calibration error;
- they may converge to a sound claim.

A mature theorem should not require perfect soundness from birth if the BRIA criterion does
not.

Try to derive a hierarchy:

    pointwise sound             => easiest corollary;
    finite total overpromise    => same asymptotic result;
    sublinear overpromise       => quantitative degraded result.

If this works, it may be more valuable than several of the current fixtures.

======================================================================
13. POLICY REGRET SHOULD BECOME A CLEAN THREE-BRIDGE COROLLARY
======================================================================

After repairs, shoot for one exact composition theorem.

For a legitimate continuation policy π with external block evaluator Ĝ:

Define

    LEARN_T(π)
      :=
    Σ_k m_k [L_k - G_k^obs(α)]

    SLACK_T(π)
      :=
    Σ_k m_k [Ĝ_k(π ; H^α_k) - L_k]

    SHIFT_T(π)
      :=
    Σ_k m_k [Ĝ_k(π ; H^π_k) - Ĝ_k(π ; H^α_k)].

Then at block boundaries:

    Regret_T(α,π)
      =
    SHIFT_T(π)
      +
    SLACK_T(π)
      +
    LEARN_T(π).

And off boundaries add the exact boundary term.

Then the ultimate consumer theorem is simply:

if

    LEARN_T(π) = o(T)      [continuation-BRIA]
    SLACK_T(π) = o(T)      [promise recognizability]
    SHIFT_T(π) = o(T)      [recoverability]

then

    Regret_T(α,π) = o(T).

This should become the canonical frontier statement.

It is much better than saying “BRIA plus recoverability gives policy regret,” because it
makes the PROMISE gap equally explicit.

Then determine how to quantify over a class:

    Π_rec,prom
      :=
    legitimate policies with
      - a covered continuation hypothesis,
      - vanishing promise slack,
      - vanishing history shift.

The strongest legitimate-policy regret statement should quantify only over this class.

======================================================================
14. DO NOT ASK THE CONSTITUTION TO PRODUCE TASK-VALUE PROMISES
======================================================================

Current item 86 asks how a promise is produced “from the constitution’s own certificates.”

Pressure this.

The constitution certifies things like:

- admissibility;
- authorization;
- protected correction structure;
- legitimate transition;
- maybe some certified safety/lower-bound properties if explicitly supplied.

It does not generically certify task reward or future-principal value.

So separate:

    LEGITIMACY CERTIFICATE
       -> q is an allowed comparator / gate-transparent continuation.

from:

    PERFORMANCE/PROMISE CERTIFICATE
       -> L is a computationally accessible claim about q's return.

These may compose.
They are not the same interface.

Repair item 86 so that it asks for:

1. recoverability of legitimate slow-lane continuations;
2. a promise-recognizability interface for task/value performance;
3. composition.

Do not make task-value recognition a duty of legitimacy itself.

======================================================================
15. PRESS THE RECOVERABILITY CONDITION
======================================================================

Current “uniform block recovery” is:

    m * |Ĝ_m(π ; H) - Ĝ_m(π ; H^π)| <= φ(m)
    with φ(m)/m -> 0.

This is promising, but ask whether it is too strong.

The policy-regret decomposition only needs the weighted aggregate:

    SHIFT_T(π) = o(T).

Potentially weaker sufficient forms include:

- average recovery along learner-reached block starts;
- one-sided recovery, because regret only needs an upper bound;
- policy-class-uniform versus per-policy recovery;
- recovery in expectation rather than pathwise;
- amortized repair cost.

Try to characterize:

    weakest condition consumed by the theorem:
        SHIFT_T(π) = o(T).

Then present uniform block recovery as one CHECKABLE SUFFICIENT schema, not as the
definition unless that is truly useful.

For corrigibility, pay special attention to authorized amendment.

Perhaps a legitimate policy can differ from the learner because it requested an amendment
earlier, but the learner can later request the same amendment at bounded cost d.

Then history shift may satisfy an amortized bound of exactly “cost to catch up.”

If this gives a theorem-shaped notion of recoverable admissibility state, develop it.

But do not claim irreversible amendment is bad per se:
irreversible choices may simply fall outside the comparator class for which policy regret
is achievable.

======================================================================
16. WHAT THIS SHOULD MEAN FOR CORRIGIBILITY
======================================================================

At the end, restate the dynamic competence interface without overselling.

The mature picture should be approximately:

    Constitution / legitimacy
        -> safe execution wrapper
        -> class of legitimate continuations

    Continuation BRIA
        -> learning error controlled
           against accountable continuation promises

    Performance recognizability
        -> promise slack controlled

    Recoverability
        -> history shift controlled

    therefore
        -> low external regret
           against legitimate, recognizable, recoverable continuation policies.

This is probably a better corrigibility competence theorem than regret against all
`Π_leg`.

Do not change the canonical Corrigibility wiki unless this pass produces a theorem-level
statement worth landing.

======================================================================
17. REQUIRED COUNTERMODELS / TESTS
======================================================================

Add or repair exact fixtures for at least:

A. EFFECTIVITY GAP
   A computable non-dominant schedule with very poor apparent convergence behavior.
   Test candidate allowance constructors against it.
   If proving a uniform-construction impossibility, make the diagonal explicit.

B. EXPLICIT EFFECTIVE SCHEDULE
   `m_k = floor(log_2 k)+1` or equivalent, with all allowance properties exact.

C. CRITERION VS CONSTRUCTION
   Persistent one-step amendment:
   auction invests and stays expanded;
   criterion-level statement says only what coverage actually forces.

D. PROMISE VS VALUE
   Controller has block value 1, promise 0.
   Continuation-promise theorem gives no competence against actual value.

E. VANISHING SLACK
   Same controller with promise `1 - ε_k`, weighted ε-average -> 0.
   Actual-history continuation competence follows.

F. FINITE OVERPROMISE
   Hypothesis is wrong on finitely many early tests, then sound.
   The asymptotic theorem should survive.

G. SUBLINEAR OVERPROMISE
   If the strengthened theorem permits it, exact schedule showing degraded but vanishing
   error.

H. COUNTERFACTUAL TYPING
   Policy not tested on most blocks:
   observed return absent,
   external evaluator defined,
   regret identity still typed externally.

I. TREATMENT MISMATCH
   Whole-lease promise falsely refuted by prefix execution.

J. ALTERNATIVE TREATMENT
   Hypothesis explicitly promises performance under a known interruption protocol;
   interrupted execution is now a valid test.
   Shows “full lease” is realization-specific, treatment matching is abstract.

K. DISCOUNTED FINITE BLOCK
   bounded discount mass rescaling works.

L. INFINITE DISCOUNTED CLAIM
   cannot settle in one finite test without extra semantics.
   Keep OPEN rather than fake-resolve.

M. RECOVERABLE AMENDMENT
   learner can enter π's admissibility state after bounded catch-up cost;
   history shift sublinear with growing blocks.

N. IRREVERSIBLE BRANCH
   unchanged impossibility.

======================================================================
18. LEAN TARGETS
======================================================================

Keep Lean small.

Useful possible additions:

- corrected external regret decomposition with separately typed:
    learner-observed return,
    external actual-history comparator return,
    external own-history comparator return;

- theorem:
    learning + slack + shift bounds
      -> regret bound;

- finite-overpromise / cumulative-slack algebra;

- any exact allowance inequality needed for the repaired existence theorem;

- rational-threshold form of the dominance impossibility.

Do NOT formalize:
- computability theory broadly;
- a general modulus-of-convergence library;
- an MDP framework.

If the effectivity question needs recursion/diagonal mathematics that is not worth Lean
yet, prove it carefully on paper and keep the Lean algebra beneath it.

======================================================================
19. DOCUMENT REPAIR
======================================================================

Audit and repair at least:

REPORT.md
- verdict;
- “iff non-dominance” if needed;
- promise vs actual performance;
- criterion vs construction.

WEIGHTED_BRIA.md
- effectivity quantifiers;
- sufficiency construction;
- necessity computability;
- discounted-return wording.

GROWING_HORIZON.md
- theorem conclusion should name promises, not actual controller value unless slack is
  controlled;
- strengthen to eventual/sublinear soundness if possible.

CONTINUATION_HYPOTHESES.md
- generic promise is not by definition a lower bound;
- treatment semantics / lease abstraction.

FIXED_HORIZON.md
- repair “every BRIA invests infinitely often”;
- criterion vs auction.

POLICY_REGRET_FRONTIER.md
- observed vs counterfactual evaluator typing;
- exact three-term theorem;
- recoverability weakest consumer condition.

CORRIGIBILITY_COMPOSITION.md
- constitution supplies admissibility, not generic task-value promises.

PRIORITIES.md item 86
- recoverability + performance-recognizability + composition;
- no false claim of unrestricted `Π_leg` regret.

PR description
- no headline theorem stronger than the repaired result.

======================================================================
20. FINAL DELIVERABLE
======================================================================

Add a short follow-up document, e.g.

    projects/deference/rounds/2026-09-08-continuation-bria/PRESSURE_PASS.md

or amend REPORT.md with a clearly marked pressure-pass section.

It should state:

1. strongest true existence theorem;
2. exact effectivity assumptions;
3. strongest continuation-BRIA theorem;
4. exact promise condition it consumes;
5. exact external policy-regret decomposition;
6. weakest policy-regret consumer assumptions;
7. what the constitution supplies;
8. what it does NOT supply;
9. remaining open problem.

======================================================================
21. FINAL VERDICT
======================================================================

Choose exactly one verdict.

Examples:

    CONTINUATION-BRIA-READY-EFFECTIVE-NONDOMINANCE-REQUIRED

    CONTINUATION-BRIA-READY-NONDOMINANCE-IFF-REPAIRED

    FIXED-AND-WEIGHTED-CORE-SURVIVE-EXISTENCE-THEOREM-WEAKENED

    NOT-READY-BLOCKED-BY-EFFECTIVITY

Do not choose READY because tests pass.

READY requires:

- the effectivity gap in the existence theorem resolved honestly;
- observed and counterfactual returns separately typed;
- promise competence not misstated as actual-policy competence;
- criterion vs auction behavior separated;
- the one-step amendment quantifier repaired;
- generic promises allowed to be wrong;
- lease necessity stated at the correct abstraction level;
- item 86 no longer asks legitimacy to certify generic task value;
- the final policy-regret theorem has explicit learning/slack/history-shift terms.

The question this pass should leave answered is:

    Exactly what has continuation-BRIA solved?

The desired mature answer is something like:

    It solves bounded learning against empirically accountable,
    temporally extended continuation claims on the histories the learner actually reaches.

And:

    Exactly what remains before corrigible policy regret?

The desired answer is:

    A policy must additionally have a computationally accessible near-tight promise
    and its own induced history must be recoverable, in value, from the histories on
    which the learner can actually test it.

Pressure until those two sentences are literally true.

---

## Message 3

You are working in `A-M-Berns/alignment-workspace`, on open PR #95:

    Continuation BRIA: leases, the weighted auction, and the policy-regret frontier

Branch:

    round/2026-09-08-continuation-bria

This is a FINAL CORRECTNESS PASS before merge consideration.

Do NOT start a new research round.
Do NOT broaden the agenda.
Do NOT redesign the weighted-BRIA construction unless one of the four issues below
forces it.
Do NOT merge.

The current core result is promising and should be preserved if correct:

    fixed-horizon continuation options
        -> ordinary BRIA

    unbounded horizons
        -> duration-weighted BRIA

    non-dominant schedules
        -> computable online weighted auction

    continuation-promise competence
        + promise recognizability
        + history recoverability
        -> external policy-level competence.

But there are four residual issues which must be resolved exactly.

======================================================================
1. REPAIR CONDITION (R): THE CURRENT STATEMENT IS VACUOUS
======================================================================

Current `GROWING_HORIZON.md` defines:

    (R) for some C,
        ℓ^h_K ≥ -C
        for infinitely many rounds K at which α rejects h.

Coverage says:

    either B_h is finite,
    or ℓ^h_K -> -∞ along K ∈ B_h.

The document then uses (R) to rule out the divergence case and concludes B_h is finite.

But (R), as currently written, already asserts infinitely many rejection rounds.
So coverage + (R) implies both:

    B_h finite
    and
    B_h infinite.

That makes the theorem vacuous.

Repair this from first principles.

The proof only needs a condition which rules out

    ℓ^h_K -> -∞ along rejection rounds.

Possible clean theorem-facing conditions:

A. GLOBAL BOUNDED-RECORD CONDITION

    inf_K ℓ^h_K > -∞.

This is strong, simple, and nonvacuous.

B. REJECTION-CONDITIONAL FORM

    if B_h is infinite, then ℓ^h_K does not tend to -∞ along K ∈ B_h.

This is logically weakest but uglier.

C. AN EQUIVALENT FORM YOU FIND CLEANER.

Pressure which should be canonical.

Strong preference:
- use a simple sufficient theorem hypothesis if the maximally weak form adds little;
- do not call something "the weakest exact condition" unless it really is.

Rebuild the implication hierarchy correctly:

    sound on every test
      ->
    eventually sound / finite total tested overpromise
      ->
    record bounded below
      ->
    continuation-promise competence.

Check carefully whether:
- finitely many wrong tests is enough;
- finite total weighted overpromise is enough;
- bounded-below record is enough;
- sublinear but divergent overpromise is still insufficient.

Preserve the existing negative fixture if correct.

Repair everywhere:
- GROWING_HORIZON.md
- WEIGHTED_BRIA.md
- PRESSURE_PASS.md
- REPORT.md
- PR body
- PRIORITIES item 86
- COUNTERMODELS.md
- FOR_HUMANS.md if affected.

The final theorem should be nonvacuous and literally true.

======================================================================
2. REPAIR THE ONE-STEP PERSISTENT-AMENDMENT CLAIM:
   CRITERION VS CONSTRUCTION VS FIXTURE
======================================================================

The current pressure pass says:

    a BRIA cannot remain at `base` on a set of positive density.

But elsewhere the same branch says the BRIA criterion still permits a myopic learner
which:
- stays at `base` almost all the time;
- rejects the request hypothesis almost all the time;
- tests it on a sparse infinite set;
- accumulates record -> -∞ on those tests;
- returns to `base` after each excursion.

These appear incompatible.

Re-analyze the d=1 persistent fixture from the BRIA criterion itself.

Let:

    h = (request, 1)

at base, with request producing an immediate low reward and moving to a persistent
benefit state.

Ask exactly what coverage requires.

Important possibility:

    h may be rejected on a positive-density set
    while being tested only on a sparse infinite set,
    provided the record on those sparse tests tends to -∞.

If that is true, then the criterion does NOT force:
- positive-density investment;
- permanent adoption of the benefit state;
- eventual departure from base.

It only rules out NEVER testing the outpromising hypothesis.

Separate three registers cleanly:

A. BRIA CRITERION

What every BRIA must do.

B. PUBLISHED AUCTION CONSTRUCTION

What the specific wealth auction does.

C. EXACT FIXTURE

What the current simulation does for the chosen ecology and allowance.

Strong candidate correction:

    - the old greedy argmax is not a BRIA because it never tests the outpromising
      request hypothesis;
    - the BRIA criterion nevertheless permits asymptotically myopic behavior via
      sparse losing tests;
    - the published auction happens to invest and keep the persistent benefit on
      the one-step fixture;
    - multi-step / renewable fixtures show failure of the particular auction's
      temporal credit assignment more robustly.

If this is right, repair every sentence that currently says:

    "the genuine failure needs a multi-step or renewable investment"

to distinguish:

    criterion-level insufficiency
    from
    construction-level insufficiency.

Add an exact fixture implementing the sparse-test myopic BRIA if practical.
If not, prove its existence carefully enough that it is not merely asserted.

This correction matters a lot conceptually:
the one-step BRIA criterion itself may already be too weak for dynamic competence,
even though the published auction behaves well on one persistent fixture.

======================================================================
3. REPAIR COMPUTABILITY OF THE PREFIX CONSTRUCTOR:
   ALLOWANCE SUPPORT IS NOT THE ACTIVE BIDDER SET
======================================================================

Current online constructor:

    s(k) = floor sqrt(S_k / M_k)

and allowance is given to:

    i <= s(k).

The document says monotonicity of s is unnecessary and therefore only s(k)
hypotheses need to be simulated at round k.

But s(k) need not be monotone.

A hypothesis i may:
- receive allowance earlier when i <= s(j);
- retain positive wealth;
- later have i > s(k).

It is still a bidder. It cannot be dropped from the auction merely because it receives
zero current allowance.

Repair this by separating:

    current allowance support:
        s(k)

from

    ever-activated bidder frontier:
        s*(k) := max_{j<=k} s(j).

Then:
- allocate allowance only to i <= s(k);
- simulate/bid every previously activated hypothesis i <= s*(k);
- keep their wealth even when outside current allowance support.

Check whether this is sufficient.

Then repair:
- the computability theorem;
- runtime bound;
- Python implementation if it currently drops previously active hypotheses;
- any fixture depending on current support;
- PR prose.

Expected runtime shape:

    O(s*(k) g(k) + m_k * execution_cost)

or the exact version implied by the source paper's enumeration model.

The subsidy proof should remain based on s(k), not s*(k), because only current
allowance support costs subsidy.

Pressure whether s*(k) remains finite and computable at each k:
it obviously should, but state the proof.

Also inspect the Python implementation of `prefix_allowance` and the auction driver.
The current test implementation appears to receive a fixed finite list of hypotheses,
which may conceal this issue.

The theorem is about the c.e. infinite class, so the proof must explicitly explain
how activation and simulation work there.

======================================================================
4. REPAIR RECOVERABILITY LANGUAGE:
   THE REAL DISTINCTION IS NOT REVERSIBLE VS IRREVERSIBLE
======================================================================

Current corrigibility prose sometimes says:

    an irreversible amendment has no finite catch-up cost.

But the round's own persistent amendment can be irreversible in the sense that:

    base -> expanded

has no path back,

while still having finite catch-up cost:
if π amended earlier and α did not, α can later make the SAME amendment and reach
the same/equivalent expanded state at cost d.

So "irreversible" is not the obstruction.

The genuine obstruction in the branch example is closer to:

    mutually exclusive / foreclosing branch choices

where after α chooses A, the state reachable by π choosing B cannot later be reached
or matched in value.

Find the right theorem-facing concept.

Candidates:
- bounded catch-up;
- joinability;
- recoverable divergence;
- bounded synchronization cost;
- value-equivalent catch-up.

Try to define the weakest object actually consumed by SHIFT.

For example:

    CatchUp_d(H^α, H^π)

if from the learner's history there exists a legitimate continuation which, within
cost d, reaches a state whose future π-value differs from π's own state by at most ε.

Or a simpler direct value statement if that is all the theorem needs.

The key conceptual distinction should become:

    irreversible but joinable / catch-up-able:
        fine for regret;

    foreclosing / mutually exclusive:
        history shift may remain linear.

Repair:
- POLICY_REGRET_FRONTIER.md
- CORRIGIBILITY_COMPOSITION.md
- PRESSURE_PASS.md
- PRIORITIES item 86
- PR body.

Do not overbuild a new theory here.
The main point is to stop canonizing the wrong binary distinction.

======================================================================
5. RECHECK THE THREE-BRIDGE THEOREM AFTER THESE REPAIRS
======================================================================

The desired mature decomposition remains:

    Regret
      =
    LEARN
      +
    SLACK
      +
    SHIFT.

Where:

    LEARN
        is controlled by continuation-BRIA under the corrected nonvacuous
        record condition;

    SLACK
        is performance recognizability / near-tight claim;

    SHIFT
        is history recoverability / bounded catch-up / joinability.

Re-state the theorem after all repairs.

The clean class should look roughly like:

    Π_rec,prom
      =
    {
      legitimate π :
        there is a covered continuation hypothesis h_π
        whose test record satisfies the nonvacuous competence condition,
        SLACK_π <= o(T),
        SHIFT_π <= o(T)
    }.

Do not quantify over all Π_leg.

The irreversible-branch / foreclosure fixture should remain the negative boundary.

======================================================================
6. RECHECK THE NON-DOMINANCE EXISTENCE THEOREM, BUT DO NOT REOPEN IT
   WITHOUT CAUSE
======================================================================

The pressure pass replaced the broken modulus argument with the online prefix
constructor:

    s(k) = floor sqrt(S_k / M_k)
    a_k = ΔM_k + 1/k.

The current claimed subsidy bound is:

    𝒜_K
      <=
    2 sqrt(S_K M_K)
      +
    sqrt(S_K)(1 + log K).

Under M_K/S_K -> 0 this is o(S_K).

This appears to repair the previous effectivity gap.

Do one final audit only for interactions with §3's active-set correction.

Check:

- allowance existence still iff non-dominance;
- activation frontier does not increase subsidy;
- capital adequacy still holds for each fixed hypothesis;
- a previously activated hypothesis that stops receiving allowance temporarily
  does not break the coverage proof;
- eventual activation of every fixed index follows from s(k) -> infinity;
- the necessity theorem's rational threshold argument remains correctly typed.

Do not redesign this theorem if these checks pass.

======================================================================
7. TESTS / EXACT WITNESSES
======================================================================

Add or repair exact tests for:

A. CONDITION-R VACUITY
   Construct a covered hypothesis that is eventually never rejected.
   Verify the old (R) fails despite soundness.
   Verify the repaired condition succeeds.

B. SPARSE-TEST MYOPIC BRIA
   On the d=1 persistent amendment, demonstrate or formally specify a BRIA which:
   - is at base on density tending to 1;
   - rejects request on most base rounds;
   - tests request on sparse infinite rounds;
   - its request-hypothesis record tends to -∞;
   - satisfies no overestimation;
   - remains asymptotically myopic.
   This is the key criterion-level witness.

C. AUCTION CONTRAST
   Published auction on the same fixture invests and keeps the benefit.
   Show criterion != construction behavior.

D. NONMONOTONE SUPPORT
   Give a schedule where s(k) decreases.
   Activate some hypothesis i at an earlier round with i <= s(j),
   later have i > s(k),
   give it positive remaining wealth,
   verify it still participates under the corrected active-frontier implementation.

E. CATCH-UP WITHOUT REVERSIBILITY
   base -> expanded is irreversible,
   but α can later take the same amendment and synchronize with π at bounded cost.
   SHIFT per block is bounded.

F. FORECLOSURE
   A/B irreversible mutually exclusive branch.
   No bounded catch-up; SHIFT linear.

======================================================================
8. LEAN TARGETS
======================================================================

Keep Lean small.

Useful only if natural:

- corrected regret theorem unchanged;
- any finite algebra needed for the record-condition implication;
- monotone ever-active frontier fact, if useful;
- no need to formalize BRIA criterion itself;
- no need to formalize density-zero sparse testing unless trivial.

The main work here is correctness of theorem statements and quantifiers.

======================================================================
9. DOCUMENT / PR AUDIT
======================================================================

Repair at minimum:

- PRESSURE_PASS.md
- REPORT.md
- FIXED_HORIZON.md
- GROWING_HORIZON.md
- WEIGHTED_BRIA.md
- POLICY_REGRET_FRONTIER.md
- CORRIGIBILITY_COMPOSITION.md
- COUNTERMODELS.md
- FOR_HUMANS.md
- PRIORITIES.md item 86
- PR body
- src/bria.py if active-set logic is implicated
- tests.

Search the whole PR for phrases like:

    "positive density"
    "infinitely often"
    "(R)"
    "irreversible amendment"
    "reversible"
    "only s(k) hypotheses"
    "genuine failure needs"
    "every BRIA"

and audit each occurrence.

======================================================================
10. FINAL VERDICT
======================================================================

Choose exactly one.

Preferred if all four repairs succeed:

    CONTINUATION-BRIA-READY-AFTER-FINAL-CORRECTNESS-PASS

Other examples:

    CORE-SURVIVES-CRITERION-WEAKNESS-RECHARACTERIZED

    NOT-READY-RECORD-CONDITION-BLOCKS-COMPETENCE-THEOREM

    NOT-READY-ACTIVE-SET-BREAKS-COMPUTABLE-CONSTRUCTION

READY requires all four issues to be explicitly repaired.

======================================================================
11. FINAL QUESTIONS TO ANSWER
======================================================================

At the end, answer these literally:

1. What does the BRIA CRITERION itself force about long-term plans?

2. What additional behavior comes only from the WEALTH AUCTION construction?

3. What exactly is the theorem hypothesis replacing the broken condition (R)?

4. For which schedules does the computable weighted learner exist, with the
   corrected active-set semantics?

5. What exactly does continuation-BRIA control?

6. What exactly does promise recognizability add?

7. What exactly does history recoverability add?

8. What structural property distinguishes:
       "I did not amend yet but can still catch up"
   from
       "I chose a branch that permanently foreclosed the comparator's branch"?

The final conceptual picture should be:

    continuation-BRIA
        = bounded learning against empirically accountable continuation claims
          on histories actually reached;

    performance recognizability
        = those claims are close enough to actual continuation value;

    recoverability / joinability
        = the learner can still compare meaningfully with the policy's own
          counterfactual history;

    policy competence
        = all three.

Do not collapse these.

---

## Message 4

You are working in `A-M-Berns/alignment-workspace`, on open PR #95:

    Continuation BRIA: leases, the weighted auction, and the policy-regret frontier

Branch:

    round/2026-09-08-continuation-bria

Current head before this dispatch:

    c75e05ce475fdc00f73636257e01188015c4ad51

This is a FOURTH AND FINAL TECHNICAL PASS.

Do NOT open a new research direction.
Do NOT broaden into LI integration, normative induction, or corrigibility beyond fixing
downstream wording if the theorem changes.
Do NOT merge.

There is one central unresolved issue:

    the weighted prefix-constructor theorem currently mixes two different
    allowance timings.

Resolve that exactly.

======================================================================
0. READ FIRST
======================================================================

Read the current PR95 branch, especially:

- BRIA_SOURCE_AUDIT.md
- WEIGHTED_BRIA.md
- REPORT.md
- PRESSURE_PASS.md
- GROWING_HORIZON.md
- FIXED_HORIZON.md
- src/bria.py
- tests/test_weighted.py
- tests/test_pressure.py
- tests/test_final.py
- lean/Workspace/Deference/Contrib/ContinuationBRIA.lean
- PR body

Re-read the source paper's Theorem 1 construction directly if needed.

Do not trust the current prose about timing until you have reconstructed the round order
yourself.

======================================================================
1. THE TIMING MISMATCH
======================================================================

The current source audit says the paper construction has:

    winner at t bids from w_t(i)

then after the round:

    w_{t+1}(i)
      =
    w_t(i)
      +
    A(t,i)
      +
    winner payoff.

The current Lean model matches this:

    W k = wealth entering round k

    Feasible:
        w_k b_k <= W_k(winner)

    W_{k+1}
      =
    W_k + A_k + winner payoff.

The current Python implementation does something different:

    reveal m_k
    add A(k,i) to h.wealth
    THEN compute bids.

So the current Python weighted auction is PREFUNDED for the current round.

This distinction is harmless-ish for constant unit weights but is load-bearing for the
prefix constructor:

    A(k,i)
      =
    ΔM_k + 1/k.

The ΔM_k term is designed to capitalize hypotheses against a newly revealed large block
m_k.

If ΔM_k arrives only AFTER the auction on block k, it cannot finance a bid on that block.

This matters on non-dominant but highly spiky schedules.

======================================================================
2. FIRST DECIDE THE OPERATIONAL TIMELINE
======================================================================

Write down the exact timeline of one weighted macro-round.

At minimum distinguish:

    1. block length / weight w_k becomes known
    2. hypotheses are activated
    3. allowance is credited or not
    4. hypotheses emit (q, treatment, claim)
    5. bids are computed
    6. winner selected
    7. block executed
    8. realized return observed
    9. wealth settled

There are two serious candidate constructions.

----------------------------------------------------------------------
A. PRE-BID / OPENING ALLOWANCE
----------------------------------------------------------------------

At round k:

    opening wealth from the past:
        W_k

    current subsidy:
        A(k,i)

    bid capital:
        B_k(i) := W_k(i) + A(k,i)

    bid:
        b_{i,k} = min(e_{i,k}, B_k(i)/w_k)

    settlement:
        W_{k+1}(i)
          =
        B_k(i)
          +
        1[i=winner] w_k(G_k - b_k).

This matches the existing Python implementation and lets ΔM_k finance the current spike.

It is NOT literally the paper's timing.

If this is the right weighted construction, say so clearly:

    fixed-horizon criterion reduction = PAPER VERBATIM;
    weighted prefunded auction = DERIVED MODIFICATION OF THE PAPER'S CONSTRUCTION.

Do not call the weighted construction "the paper's construction verbatim."

----------------------------------------------------------------------
B. END-OF-ROUND / SOURCE-PAPER TIMING
----------------------------------------------------------------------

At round k:

    bid from W_k

then:

    W_{k+1}
      =
    W_k + A(k) + payoff.

This matches the source audit and current Lean model.

If retaining this timing, determine whether the claimed prefix theorem survives.

In particular, can an online rule depending only on the prefix through k finance a
surprise spike at k when the current ΔM_k is unavailable until k+1?

Do not assume yes.

If it requires:
- one-block lookahead;
- a predictable schedule;
- an allowance based on m_{k+1};
- or a weaker schedule condition,

state that exactly.

======================================================================
3. PRESS THE END-OF-ROUND VERSION WITH A SPIKY COUNTERMODEL
======================================================================

Construct a non-dominant schedule with sparse surprise spikes:

    m_k = 1 most rounds,

and at spike times k_j:

    m_{k_j} << S_{k_j}
    but
    m_{k_j} >> M_{k_j-1},

with

    m_{k_j}/S_{k_j} -> 0.

Choose gaps large enough that each new spike dwarfs all previous maximum block lengths.

Now use a hypothesis which:
- promises 0 off the spikes;
- promises 1 on the spikes;
- has a controller returning 0.

Ask:

    under end-of-round timing with the current prefix allowance,
    does it have enough PRE-SPIKE wealth to bid meaningfully on infinitely many spikes?

If not:
- make this an exact fixture;
- state that the current prefix theorem is false under source timing.

This is the core diagnostic.

The fixture should distinguish:

    current-round ΔM_k available before bidding

from

    current-round ΔM_k arriving only after the test opportunity has passed.

======================================================================
4. IF USING PRE-BID ALLOWANCE, REPROVE THE WEIGHTED AUCTION FROM SCRATCH
======================================================================

Do not merely reindex the old Lean statements.

Define the exact pre-bid capital object.

Suggested notation:

    W_k(i)      wealth carried into round k from prior settlements
    B_k(i)      opening bid capital after current subsidy
                = W_k(i) + A(k,i)

Then prove exact finite statements for:

A. nonnegativity;

B. total wealth identity;

C. weighted overestimation bound;

D. per-hypothesis wealth / record identity;

E. rejection-record bound;

F. stopped-winning accumulation;

G. attention bound.

Be especially careful about the rejection round itself.

At a rejection K, h_i may itself be the winner while wealth-constrained:

    b_{i,K} < e_{i,K}.

Coverage's record includes test outcomes according to the criterion's indexing.

So derive the exact inequality rather than assuming the old one:

    ℓ_K < w_K - A_i(K)

may or may not survive unchanged.

Possibilities include a constant-factor condition such as:

    cumulativeAllowance_i(K) - c w_K -> ∞

for c = 1, 2, or another exact constant.

Find the SHARPEST CLEAN condition the proof really needs.

Do not preserve:

    A_i(K) - m_K -> ∞

by inertia if the prefunded timing changes the proof.

======================================================================
5. RECHECK THE NON-DOMINANCE IFF AFTER THE EXACT COVERAGE CONDITION
======================================================================

Suppose the corrected prefunded auction needs:

    A_i(K) - c m_K -> ∞

for some fixed c > 0.

Determine whether the schedule-level theorem remains:

    m_K / S_K -> 0
        iff
    suitable negligible allowances exist.

It probably does for any fixed constant c, but prove it.

If the prefix rule needs a coefficient:

    A(k,i)
      =
    C (M_k - M_{k-1}) + 1/k

with C > c,

then:
- choose the cleanest C;
- redo the subsidy bound;
- show it is still o(S_K);
- state the exact constant.

Do not care about optimizing C unless the sharp value is easy.

The important theorem is the schedule-level boundary.

======================================================================
6. LEAN SHOULD MODEL THE ACTUAL WEIGHTED CONSTRUCTION
======================================================================

Right now Lean proves the end-of-round auction while Python executes the prefunded one.

That is unacceptable for the headline weighted construction.

Preferred repair:

OPTION 1:
    retain the current `Auction` as the PAPER-TIMED / end-of-round algebra,
    and add a distinct `PrefundedAuction` (or better name) for the weighted construction.

This has the virtue of keeping source fidelity explicit.

OPTION 2:
    refactor `Auction` to the actual prefunded weighted construction,
    but then make very clear that it is DERIVED rather than literally the paper's auction.

I weakly prefer OPTION 1 because it preserves the distinction:

    original BRIA auction
    vs
    weighted continuation-BRIA auction.

But choose whichever produces the cleanest theory.

At minimum Lean should kernel-check:
- the actual wealth identity used by Python;
- the actual overestimation bound;
- the actual rejection / coverage inequality;
- the actual attention bound or its finite algebraic core.

The prefix sum lemma can remain unchanged if its combinatorics are unchanged.

======================================================================
7. SOURCE FIDELITY AUDIT
======================================================================

Audit every phrase:

    "the paper's construction"
    "verbatim"
    "same auction"
    "m = 1 is the paper's construction"
    "allowance is paid"
    "wealth entering the round"

Separate:

A. PAPER CRITERION:
   fixed-horizon macro reduction really is verbatim at the level of Definitions 1–7 and
   Theorems 1–4.

B. PAPER CONSTRUCTION:
   exact Theorem-1 wealth timing.

C. WEIGHTED CONSTRUCTION:
   whatever timing this pass settles on.

If pre-bid funding is adopted, say explicitly that the weighted auction is a small but
important modification necessitated by online variable liabilities.

For m ≡ 1, determine whether prefunding is:
- literally identical after reindexing;
- only asymptotically equivalent;
- or genuinely a slightly different BRIA construction.

State the truth, not the convenient slogan.

======================================================================
8. ONLINE INFORMATION MODEL
======================================================================

The current branch mixes:

    "schedule declared in advance"

and

    "one online rule reading only the revealed prefix."

Clarify exactly what is known when.

For the strongest theorem, I suggest:

    before bidding on block k, m_k is revealed;
    no information about m_{k+1}, m_{k+2}, ... is required.

Then the prefunded constructor may use:

    S_k, M_k, m_k

to set current opening subsidy.

If instead the proof requires the entire schedule in advance, say so.

The headline "uniform online" theorem should mean something precise.

======================================================================
9. PYTHON FIXTURE: SURPRISE SPIKE
======================================================================

Add a test that directly demonstrates the timing issue.

Run the SAME non-dominant spiky schedule under:

A. prefunded timing;

B. end-of-round timing with the same prefix allowance.

Use a spike-only outpromising hypothesis.

Expected diagnostic if the concern is real:

    prefunded:
        current ΔM spike capital is available;
        hypothesis can eventually meet coverage obligations;

    end-of-round:
        hypothesis repeatedly arrives at surprise spikes undercapitalized;
        current ΔM arrives too late.

Do not merely test wealth identities.

Test the causal thing the theorem needs:
ability to bid on the current large block.

======================================================================
10. ATTENTION BOUND
======================================================================

Re-derive the attention bound under the settled timing.

The desired interpretation remains:

    wealth is a claim on experimental execution time.

But make sure the algebra uses the correct notion of:
- subsidy through K;
- opening capital;
- settled wealth.

If a prefunded auction gives a bad hypothesis current subsidy before its test, that subsidy
must be counted in the attention budget.

No free current-round experimental capital should disappear from the accounting.

======================================================================
11. COMPETENCE THEOREMS SHOULD NOT CHANGE UNLESS NECESSARY
======================================================================

The criterion-level theorems:

    (BR) -> LEARN <= o(T)
    + SLACK -> actual-history competence
    + SHIFT -> own-trajectory competence

do not depend on the auction's allowance timing once a weighted BRIA exists.

Preserve them.

This pass is about the EXISTENCE CONSTRUCTION, not the criterion.

Likewise preserve:
- promise-treatment alignment;
- criterion vs construction distinction;
- joinability vs foreclosure;
- external typing of Gobs and Ĝ.

Do not reopen those.

======================================================================
12. DOWNSTREAM WORDING
======================================================================

If the existence theorem changes, repair:

- WEIGHTED_BRIA.md
- REPORT.md
- PRESSURE_PASS.md
- BRIA_SOURCE_AUDIT.md
- FOR_HUMANS.md
- PRIORITIES item 86
- PR body
- Lean module header
- src/bria.py comments
- tests.

Also clean the two stale items already visible:
- any remaining reference to condition `(R)` should be `(BR)`;
- REPORT should not say the sparse-test witness is "stated, not implemented" now that
  `test_final.B` exists, except insofar as full BRIA-ness is a prose theorem rather than
  mechanically checked.

======================================================================
13. FINAL THEOREM SHAPE
======================================================================

The desired result, if prefunding works, is something like:

WEIGHTED CONTINUATION-BRIA EXISTENCE.

At the start of block k, after its weight w_k is revealed, a negligible opening subsidy
is distributed. Hypotheses bid in total-reward units against that opening capital.
For every non-dominant schedule

    w_K / S_K -> 0,

there is one prefix-online finite-support subsidy rule such that the resulting auction is
a weighted BRIA for every c.e. e.c. hypothesis class.

Conversely, if

    limsup w_K / S_K > 0,

the weighted BRIA criterion itself is unsatisfiable for a two-hypothesis e.c. class.

Do NOT use this wording unless the exact proof supports every quantifier.

======================================================================
14. DELIVERABLE
======================================================================

Add a final section to PRESSURE_PASS.md, e.g.

    §13 Allowance-timing audit

which states:

1. the source paper's timing;
2. the old Lean timing;
3. the old Python timing;
4. why the difference matters for spikes;
5. the chosen weighted timing;
6. the exact new wealth recursion;
7. the exact capital-adequacy condition;
8. the corrected prefix theorem;
9. whether non-dominance remains iff;
10. source-fidelity consequences.

======================================================================
15. FINAL VERDICT
======================================================================

Choose exactly one:

    CONTINUATION-BRIA-READY-TIMING-ALIGNED

    CORE-SURVIVES-PREFUNDED-WEIGHTED-AUCTION

    EXISTENCE-THEOREM-WEAKENED-TO-PREDICTABLE-SCHEDULES

    NOT-READY-PREFIX-CONSTRUCTOR-FAILS-UNDER-CORRECT-TIMING

Do not choose READY merely because tests pass.

READY requires:

- one operational round timeline everywhere;
- Lean and Python modeling the same weighted construction;
- the spike test;
- coverage reproved under that timing;
- exact capital adequacy;
- source-paper timing distinguished from weighted timing;
- non-dominance theorem re-audited.

======================================================================
16. FINAL QUESTIONS
======================================================================

Answer these literally:

1. Is the weighted auction the paper's auction, or a modified auction?

2. Exactly when does a hypothesis receive A(k,i)?

3. Does current ΔM_k capital finance block k?

4. What wealth is used to form the bid?

5. What exact cumulative-capital condition proves coverage?

6. Does the prefix constructor still work for every non-dominant schedule?

7. Is one-step lookahead needed?

8. Does non-dominance remain the sharp criterion-level schedule boundary?

9. Which parts of the round remain PAPER, DERIVED, LEAN, and FIX after this repair?

The pass is done only when there is no remaining ambiguity between:

    capital available before a test

and

    capital credited after the test.

---

## Message 5

You are working in `A-M-Berns/alignment-workspace`, on PR #95:

    Continuation BRIA: leases, the weighted auction, and the policy-regret frontier

Branch:

    round/2026-09-08-continuation-bria

Last inspected head:

    17507972bb9dc9b7daf3a1434b72a964c3aa44ee

This is the CLOSING PASS.

The maintainer explicitly authorizes you to MERGE PR #95 once the acceptance criteria
below are satisfied.

Do not start another research round.
Do not broaden into a new LI/BRIA unification project.
Do not add speculative machinery.
Do not preserve old abstractions merely because they are already written.

The goals are:

1. repair the last theorem-hygiene issue in opening-timed coverage;
2. compress the continuation-hypothesis type to its mature formulation;
3. make the round documents internally consistent;
4. promote the settled results into the canonical wiki;
5. run the full repository checks;
6. merge PR #95 if and only if all checks and audits pass.

======================================================================
0. READ CURRENT STATE FIRST
======================================================================

Before changing anything, inspect the CURRENT branch and PR, not merely this prompt.

Read at minimum:

- PR #95 body
- projects/deference/rounds/2026-09-08-continuation-bria/
  - REPORT.md
  - PRESSURE_PASS.md
  - BRIA_SOURCE_AUDIT.md
  - FIXED_HORIZON.md
  - CONTINUATION_HYPOTHESES.md
  - WEIGHTED_BRIA.md
  - GROWING_HORIZON.md
  - POLICY_REGRET_FRONTIER.md
  - CORRIGIBILITY_COMPOSITION.md
  - COUNTERMODELS.md
  - FOR_HUMANS.md
- src/bria.py
- all tests, especially test_timing.py
- lean/Workspace/Deference/Contrib/ContinuationBRIA.lean
- PRIORITIES.md
- DECISIONS.md
- PROVENANCE.md
- wiki/Architecture.md
- wiki/Corrigibility.md
- wiki/Deference.md
- wiki/Normative-Induction.md
- wiki/Normative-Inductor.md
- wiki/Logical-Induction-and-Deference.md
- wiki/Glossary.md
- wiki/Home.md
- wiki/CONVENTIONS.md

Check repo rules for canonical wiki status labels, registration, provenance, and merge
workflow.

======================================================================
1. SHARPEN THE OPENING-TIMING COVERAGE BOUND
======================================================================

The current fourth pass claims that because BRIA Definition 5 uses the inclusive record,

    ℓ_K = Σ_{tests t ≤ K} w_t (G_t - e_t),

opening-timed coverage requires

    A_i(K) - 2 w_K -> ∞,

and hence the prefix subsidy has coefficient 2:

    A(k,i) = 2 ΔM_k + 1/k.

This appears unnecessarily loose.

Re-derive the inclusive rejection inequality carefully.

At a rejection round K, opening capital satisfies

    B_K(i) = W_K(i) + A(K,i)

and because i's wealth-bounded bid is below the winning estimate while

    α^e_K < e_{i,K},

we have

    B_K(i) < w_K e_{i,K}.

Using

    B_K(i)
      =
    A_i(K) + chargedRecord_i(<K),

and paid bid ≤ promise, derive

    ℓ^i_{<K}
      <
    w_K e_{i,K} - A_i(K).

Now split on whether i is the winner at K.

CASE 1: i does not win.

Then

    ℓ^i_K = ℓ^i_{<K},

so

    ℓ^i_K < w_K - A_i(K).

CASE 2: i wins while wealth-constrained.

Then the inclusive record adds exactly

    w_K (G_K - e_{i,K}),

not an arbitrary +w_K.

Therefore

    ℓ^i_K
      <
    w_K e_{i,K} - A_i(K)
      + w_K(G_K - e_{i,K})
      =
    w_K G_K - A_i(K)
      ≤
    w_K - A_i(K).

So the expected sharp uniform inequality is:

    BOX:
        ℓ^i_K < w_K - A_i(K)

at every rejection K.

If this derivation is correct, replace the current factor-2 condition by:

    capital adequacy:
        A_i(K) - w_K -> ∞.

Then restore the prefix subsidy to:

    A(k,i) = ΔM_k + 1/k

on the support

    s(k) = floor sqrt(S_k / M_k).

The subsidy bound should return to:

    𝒜_K
      ≤
    2 sqrt(S_K M_K)
      +
    sqrt(S_K)(1 + ln K)
      =
    o(S_K).

Do not assume this prompt is right:
kernel-check the finite inequality and try to break it.

If there is a hidden indexing issue, identify it exactly.
But do not retain coefficient 2 merely because a finite fixture with coefficient 1 fails
to test every early spike: BRIA coverage does NOT require every rejection to be tested.

======================================================================
2. LEAN THE SHARP OPENING-TIMING ARGUMENT
======================================================================

Update the Lean algebra to prove the ACTUAL bound used by the theorem.

Preferred theorem shape:

    record_succ_lt_of_rejected_opening
      ...
      :
      record e i (K+1)
        <
      w K - allowanceOf i (K+1)

under the correct bounded-return / bounded-promise assumptions.

The proof should exploit cancellation of `e_K` when i wins, not separately bound the
current record increment by `w_K`.

Also fix the current no-win accumulation gap.

The existing:

    wealth_ge_of_no_win

assumes source-paper `Feasible`.

The opening-timed construction has only:

    FeasibleOpening.

Add either:

    wealth_ge_of_no_win_opening

or generalize the lemma so it only consumes the nonnegativity fact it actually needs.

Then ensure the opening-timing coverage proof has a completely coherent Lean-supported
finite spine:

- opening wealth nonnegative;
- no-win subsidy accumulation;
- rejection record bound;
- inclusive rejection record bound;
- overestimation bound;
- attention bound.

Do not formalize the whole BRIA criterion unless this becomes unexpectedly necessary.

======================================================================
3. RETUNE THE PREFIX CONSTRUCTOR AND TIMING FIXTURES
======================================================================

If coefficient 1 is restored:

    prefix subsidy:
        A(k,i) = ΔM_k + 1/k

and:

    A_i(K) - m_K -> ∞.

Retune:

- src/bria.py
- test_timing.py
- test_pressure.py
- test_weighted.py
- all prose.

The surprise-spike test should test the ACTUAL distinction:

SOURCE / SETTLEMENT TIMING:
    current ΔM_k cannot finance the surprise spike;
    there exists a non-dominant adversarial schedule on which a spike-only hypothesis
    remains uncovered.

OPENING TIMING:
    current ΔM_k is available;
    the theorem's asymptotic capital-adequacy and coverage argument succeeds.

Do NOT require:

    "the liar wins every spike"

or even:

    "the liar wins all sufficiently large spikes"

unless actually proved.

Coverage is about:

    finite rejection
    OR
    record -> -∞ along rejection rounds.

Use fixtures as finite diagnostics, not as substitutes for the asymptotic theorem.

Keep the settlement-timing impossibility theorem if it survives the sharpened audit.

======================================================================
4. COMPRESS THE CONTINUATION-HYPOTHESIS TYPE
======================================================================

The current canonical type is approximately:

    h(H_k) = (q_k, τ_k, e_k)

where q is a controller and τ an advisor-side execution treatment.

This was useful scaffolding for discovering the pseudo-test / treatment-mismatch issue,
but it is not needed as the mature primitive.

Canonicalize the theory around ONE executable continuation object.

The new core type should be:

    h(H_k) = (c_{h,k}, e_{h,k})

where

    c_{h,k} ∈ C_{m_k}(H_k)

is a finite-horizon CAUSAL ADVISOR CONTINUATION for the next block.

Preferred abstract type:

    c :
      ObsHist_{H_k,<m_k}
        ->
      Proposal

or an equivalent typed causal strategy.

The existing implementation type

    (state, within-block step, absolute time) -> action/proposal

is acceptable as a concrete sufficient representation when state is history-sufficient.

Be explicit:

- c is NOT an open-loop action list;
- c may react to gate refusals, external observations, amendments, principal actions, etc.;
- c controls only the advisor/proposal side;
- the gate and exterior remain live;
- c is finite-horizon because the surrounding block contract fixes m_k.

The SYSTEM, not the bidder, supplies the block contract:

    χ_k =
      (
        actual start history H_k,
        block duration m_k,
        constitutional execution wrapper Exec^G,
        bounded score functional R_k
      ).

Then:

    h(χ_k) = (c_{h,k}, e_{h,k})

and if h wins:

    ω_k = Exec^G_{m_k}(H_k, c_{h,k})
    G_k = R_k(ω_k).

The hypothesis's claim e is accountable against this realized G_k.

======================================================================
5. REMOVE τ AS A CANONICAL PRIMITIVE, BUT PRESERVE THE LESSON
======================================================================

Do not erase the important treatment-alignment insight.

Instead demote `(q, τ)` to an explanatory FACTORIZATION of a continuation:

    c = τ(q).

For example:

    "q for three steps, then baseline"

is simply a different continuation c from:

    "q for the whole block."

The mature test-validity principle becomes:

    BOX:
      Data is evidence about a continuation claim only when it is generated by executing
      the continuation named by that claim under the standard block semantics.

So:

    c ≠ c'
        =>
    an observation from c' is not a test of a claim about c.

This is the direct continuation analogue of ordinary BRIA:

    ordinary hypothesis:
        (action, promise)

    continuation hypothesis:
        (continuation, claim).

Testing is NOT a third object supplied by the bidder.

A TEST is the derived event:

    Test(h,k)
      iff
    h is selected at k and c_{h,k} is actually executed under χ_k.

Keep `q/τ` only:
- in the historical explanation of how the pseudo-test problem was found;
- as an optional representation lemma / explanatory note;
- in fixtures if convenient internally.

Do not make readers carry τ through the headline theorem.

======================================================================
6. BE EXACT ABOUT WHO CHOOSES THE HORIZON
======================================================================

Current continuation-BRIA does NOT let bidders request arbitrary lease lengths.

The global schedule supplies:

    m_k.

Every bidder at block k competes for the SAME next block of length m_k.

So the mature object is:

    system parcels the future into blocks m_k;
    hypotheses bid for which continuation occupies the next block.

The headline non-dominance theorem concerns the system schedule:

    m_k / S_k -> 0.

Do not write language suggesting each bidder currently chooses how much lifetime to buy.

Hypothesis-requested horizons / combinatorial bids for duration remain OPEN.

This distinction belongs prominently in the wiki.

======================================================================
7. REWRITE THE ROUND DOCUMENTS AROUND THE MATURE TYPE
======================================================================

Update at minimum:

- CONTINUATION_HYPOTHESES.md
- FIXED_HORIZON.md
- WEIGHTED_BRIA.md
- GROWING_HORIZON.md
- POLICY_REGRET_FRONTIER.md
- CORRIGIBILITY_COMPOSITION.md
- PRESSURE_PASS.md
- REPORT.md
- FOR_HUMANS.md
- BRIA_SOURCE_AUDIT.md
- PR body.

Use terminology consistently:

Preferred:
    continuation
    continuation hypothesis
    accountable contextual claim
    block contract
    execution wrapper
    realized test
    opening subsidy
    weighted BRIA
    non-dominance
    continuation-promise competence
    promise recognizability
    history shift
    joinability / bounded catch-up
    foreclosure

Avoid making these canonical unless needed:
    protocol
    treatment
    lease object
    policy

"Execution lease" may remain as an intuitive description of what winning a block means,
but should not be a separate component of the hypothesis type.

======================================================================
8. STATE THE HEADLINE THEOREM CLEANLY
======================================================================

The canonical theorem should have a human-readable form close to:

CONTINUATION-BRIA EXISTENCE / NON-DOMINANCE THEOREM.

Let block k have duration m_k ≥ 1 and

    S_K = Σ_{k≤K} m_k.

At each block start, after m_k is revealed, hypotheses from a c.e. class emit a causal
continuation for that block and an accountable claim about its realized bounded block
score.

Then:

    m_K / S_K -> 0

iff suitable negligible opening subsidies exist for the weighted auction; under this
condition there is a single prefix-online computable weighted-BRIA learner covering every
c.e. class of e.c. continuation hypotheses.

If

    limsup m_K / S_K > 0,

there is a computable environment and a two-hypothesis e.c. class for which NO estimating
agent satisfies the weighted BRIA criterion.

Keep the exact quantifiers correct.

The converse is criterion-level.
The positive result uses the opening-timed weighted auction.

Do not call the weighted auction literally the paper's construction:
- fixed-horizon BRIA criterion reduction: PAPER verbatim;
- source paper auction: settlement-timed;
- weighted auction: DERIVED opening-subsidy modification.

======================================================================
9. STATE THE COMPETENCE RESULT CLEANLY
======================================================================

For a covered continuation hypothesis h with bounded-below test record:

    (BR)
      inf_K ℓ^h_K > -∞,

continuation BRIA controls:

    LEARN_K(h)
      =
    Σ_{k≤K} m_k (e_{h,k} - G^obs_k)
      ≤
    o(S_K).

Interpretation:

    the learner cannot asymptotically underperform the accountable claims of a continuation
    that survives its actual tests.

Then preserve the clean external decomposition:

    Regret
      =
    LEARN
      +
    SLACK
      +
    SHIFT.

Where:

    LEARN:
      continuation BRIA;

    SLACK:
      the claim is near-tight for the continuation's value from the learner's actual
      history;

    SHIFT:
      the comparator's own-history value is recoverable from / joinable with the learner's
      actual history.

Do not imply BRIA itself supplies counterfactual policy values.

======================================================================
10. PROMOTE THE RESULT TO THE WIKI
======================================================================

This round is mature enough to stop living only in `projects/deference/rounds/...`.

Create a canonical wiki page, preferably:

    wiki/Continuation-BRIA.md

unless repo conventions strongly prefer another name.

This page should be concise and theorem-oriented, not a dump of the round.

Suggested structure:

# Continuation BRIA

## Status
Clearly label:
- source BRIA facts: PAPER;
- fixed-horizon reduction: DERIVED;
- weighted algebra: LEAN-backed DERIVED;
- non-dominance theorem: DERIVED, finite algebra Lean-backed;
- policy-regret bridges: DERIVED / EXT as appropriate;
- remaining open questions.

## 1. Problem
Original BRIA is one-step/myopic.
We need empirically accountable temporally extended choice without counterfactual reward
tables.

## 2. Canonical type
System block contract χ_k.
Hypothesis:

    h(χ_k) = (c_{h,k}, e_{h,k})

with causal advisor continuation

    c : ObsHist_{<m_k} -> Proposal.

Test is realized execution, not another primitive.

Mention `c = τ(q)` only as an optional factorization explaining treatment mismatch.

## 3. Fixed horizon
Macro-reduction to original BRIA.

## 4. Variable horizon / weighted BRIA
Primitive-time weighting.
Opening-subsidy auction.
Attention interpretation.

## 5. Headline theorem
Non-dominance:

    m_K / S_K -> 0

is the sharp schedule-level boundary.

State positive and negative sides carefully.

## 6. Competence theorem
(BR) -> LEARN = o(S).

## 7. Policy frontier
LEARN + SLACK + SHIFT.

## 8. Corrigibility interface
Constitution supplies:
- execution gate;
- legitimate/gate-transparent continuation class;
- possibly joinability/catch-up structure.

It does NOT supply task-value claims.

## 9. Open
At least:
- promise/value recognizability;
- recovery/joinability certificates;
- weighted analogue of BRIA Theorem 4 if still open;
- hypothesis-requested horizons / combinatorial duration allocation;
- infinite-horizon discounted settlement;
- deeper LI/BRIA coupling (do not solve here).

======================================================================
11. UPDATE EXISTING WIKI PAGES, BUT KEEP LAYER BOUNDARIES
======================================================================

Update only where the new result materially changes the canonical architecture.

At minimum inspect and likely update:

### wiki/Architecture.md
Add continuation BRIA as the bounded dynamic-competence layer:

    Legitimate Evolution / normative state
      ->
    traderized LI / bounded epistemic enforcement
      ->
    constitutional execution interface
      ->
    continuation BRIA
      ->
    temporally extended behavior.

Do not say BRIA is part of legitimacy.

### wiki/Corrigibility.md
Update the positive theorem target to distinguish:

    constitutional preservation
      +
    continuation learning
      +
    promise recognizability
      +
    joinability/recoverability.

Use:

    Regret = LEARN + SLACK + SHIFT.

Make clear that unrestricted Π_leg regret remains false.

### wiki/Normative-Inductor.md
Explain that continuation BRIA is a candidate dynamic response-selection/competence layer
AFTER normative constraints determine the execution envelope.

Traderized LI and BRIA remain separate layers:
- LI: bounded beliefs / normative enforcement;
- BRIA: allocation of actual execution among temporally extended continuations.

Do not claim the concrete Normative Inductor realization is complete.

### wiki/Normative-Induction.md
Only add the interface if helpful:
the Progress theorem is agnostic about how responses are selected; continuation BRIA is one
candidate learner supplying good dynamic responses.

### wiki/Deference.md and/or wiki/Logical-Induction-and-Deference.md
Add the precise bridge:
future authoritative evaluation / LI can potentially supply accountable continuation-value
claims, which would discharge SLACK.
Mark this as an interface/open realization unless actually proved.

### wiki/Glossary.md
Add concise entries for:
- continuation
- continuation BRIA
- non-dominance
- opening subsidy
- continuation-promise competence
- promise recognizability
- history shift
- joinability / bounded catch-up
- foreclosure

Do not add obsolete `τ` as a canonical glossary primitive.

### wiki/Home.md
Add the new page to navigation / current theory map if conventions call for it.

======================================================================
12. KEEP LI AND BRIA MODULAR
======================================================================

Do not turn this closing pass into a deeper synthesis.

Canonical current picture:

    Logical Induction / traderization:
      bounded epistemics, prediction, normative enforcement.

    Continuation BRIA:
      bounded experimental selection among actual executable continuations.

Potential bridge:

    LI-derived / deferential value prediction
      ->
    accountable continuation claim e
      ->
    BRIA empirical testing.

But this bridge is not yet a theorem unless the repo already has one.

In particular:

    LI predicts;
    BRIA allocates realized experiments.

Keep the wealth accounts semantically distinct.

======================================================================
13. PRIORITIES / DECISIONS / PROVENANCE
======================================================================

Update PRIORITIES item 86 to reflect the result now established.

Do NOT close item 86 if its remaining substance is still:

- promise recognizability;
- joinability/recoverability realization;
- composition into corrigible policy competence.

But remove work that PR95 has genuinely discharged.

Update DECISIONS.md if the repo records architectural decisions there. Candidate decisions:

- canonical continuation hypothesis is `(continuation, claim)`, not `(q, τ, claim)`;
- test is derived realized execution;
- horizon is system-scheduled, not bidder-requested;
- opening subsidy is the weighted construction's timing;
- non-dominance is the sharp schedule-level boundary;
- LEARN / SLACK / SHIFT are separate interfaces.

Update provenance everywhere required.

======================================================================
14. REGISTRATION DECISION
======================================================================

Inspect repo conventions for "statement of record."

Do NOT register a theorem merely to make the PR look stronger.

But if the repository's canonicalization rules imply that a theorem promoted to the wiki
should receive a registered statement, make the minimal appropriate registration.

Be explicit about levels:

PAPER:
    source BRIA theorem.

DERIVED:
    continuation reduction / weighted criterion / existence theorem / policy decomposition.

LEAN:
    exact finite algebra supporting the derived theorem.

EXT:
    constitutional meaning of gate, rollout semantics, task/principal value semantics.

OPEN:
    the unresolved interfaces.

If no registration is appropriate, say why in the final report.

======================================================================
15. FULL CONSISTENCY SEARCH
======================================================================

Search the branch for stale language and repair every meaningful occurrence:

    "(q, τ, e)"
    "treatment"
    "protocol"
    "weakest useful lease"
    "test is"
    "coefficient 2"
    "2 ΔM"
    "A_i(K) − 2"
    "4√"
    "every spike"
    "declared in advance"
    "known to hypotheses"
    "reversible"
    "condition (R)"
    "paper's construction verbatim"
    "policy"

For "policy", do not mechanically replace every occurrence.
Use:
- continuation/controller for the BRIA object;
- policy only for the external own-trajectory comparator where that is genuinely the type.

======================================================================
16. TESTS
======================================================================

Run and repair:

- round-local tests;
- root `python3 tests/run.py`;
- Lean build for ContinuationBRIA;
- full Lean audit required by repo convention;
- round_records;
- lean_scope;
- DCO;
- any wiki/link consistency checks;
- any registry/checker suite if registration changed.

All exact fixtures should remain meaningful after the semantic compression.

Add one small test or specification fixture if useful showing:

    c_full
      !=
    c_prefix_then_baseline

and that an outcome from the latter does not count as a test of a claim about the former.

This can replace τ-level language.

======================================================================
17. FINAL HUMAN AUDIT BEFORE MERGE
======================================================================

Before merging, answer these exactly:

1. What is the canonical type of a continuation hypothesis?

2. Who chooses the block duration m_k?

3. What exactly does a continuation control?

4. What remains live outside the continuation?

5. What event constitutes a test?

6. Is τ still a primitive?
   Expected mature answer: no; `(q,τ)` is at most an explanatory factorization of one
   executable continuation.

7. What is the sharp opening-timing capital-adequacy condition?

8. What is the prefix subsidy rule?

9. What is the headline schedule condition?

10. What is the positive existence theorem?

11. What is the criterion-level impossibility theorem?

12. What exactly does continuation-promise competence guarantee?

13. What do SLACK and SHIFT add?

14. What does this solve for corrigibility?

15. What remains open?

If any answer is still ambiguous across the docs/wiki/code, do not merge yet.

======================================================================
18. MERGE CRITERIA
======================================================================

You are authorized to merge PR #95 when ALL of the following hold:

- the opening-timing coverage inequality is correct and Lean-backed;
- the coefficient is sharp enough that no known avoidable factor remains in the canonical
  theorem;
- Python and Lean implement/model the same weighted construction;
- the prefix theorem is still valid;
- the settlement-timing negative is correctly scoped;
- canonical type is `(continuation, claim)`;
- τ is demoted from primitive to optional explanatory factorization;
- block duration is clearly system-scheduled;
- round docs are consistent;
- wiki/Continuation-BRIA.md exists and is canonical;
- relevant architecture/corrigibility/normative-inductor/deference wiki pages are updated;
- PRIORITIES / DECISIONS / PROVENANCE are consistent;
- all tests and audits pass;
- PR body reflects the final result;
- branch is mergeable against current main.

If main moved and causes conflicts, rebase/update safely, rerun all checks, and re-audit
the changed interfaces.

Then MERGE PR #95 using the repository's normal merge strategy.

Do not leave it open merely because previous round prompts said "maintainer decides":
the maintainer has now explicitly decided that this closing dispatch should merge once
the above criteria pass.

======================================================================
19. FINAL VERDICT
======================================================================

If merged, final verdict:

    CONTINUATION-BRIA-CANONICALIZED-AND-MERGED

If not merged, choose one precise blocker, e.g.:

    NOT-MERGED-SHARP-COVERAGE-BOUND-FAILS

    NOT-MERGED-NONDOMINANCE-THEOREM-CHANGED

    NOT-MERGED-WIKI-AND-ROUND-DISAGREE

    NOT-MERGED-CI-FAILURE

Do not say READY if you did not actually merge.

======================================================================
20. FINAL REPORT
======================================================================

The final response/report should be compact and answer:

- final PR head and merge commit;
- exact headline theorem;
- final continuation-hypothesis type;
- final subsidy/capital condition;
- what was changed from the fourth pass;
- wiki pages created/updated;
- what remains in item 86;
- whether anything was registered;
- all tests/audits run;
- final verdict.

The desired conceptual compression is:

    system chooses a vanishing-share block;
    hypothesis proposes a causal advisor continuation plus an accountable claim;
    winning means that continuation is actually executed through the live constitutional
    wrapper;
    realized score settles the claim;
    weighted BRIA guarantees accountable long-horizon experimentation exactly on
    non-dominant schedules.

And the downstream frontier remains:

    policy regret
      =
    LEARN
      +
    SLACK
      +
    SHIFT.

Do not collapse those three terms.

---

Mid-dispatch additions from the maintainer, verbatim:

> Can you also remove stuff about how the deference line is "paused"?

> Please also try to incorporate the most important mathematical results presented in
> their most mature form into the wiki. you can use the most recent pdf (might be in
> downloads, legitimate evo and etc) as a guide to some extent, and any agent
> consolidated/agent canonicalized results from the repo
