# Dispatch — 2026-09-08 continuation BRIA

Two messages, both verbatim as sent.  The second is the pressure pass dispatched
against the first's result.

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
