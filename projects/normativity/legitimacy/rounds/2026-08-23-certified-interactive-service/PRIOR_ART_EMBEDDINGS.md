# Prior-art embeddings

Status: **research memo; unregistered**. Translations are exact where
stated; every preservation claim names its restriction. Sources are the
primary PDFs listed in `PROVENANCE.md`; finite tests are in
`tests/test_embeddings.py` and `tests/test_rr_compilation.py`.

## A. Set Cover with Delay

Source model (arXiv 1807.08543v3 Section 2): sets `S_i` with prices
`c(S_i) >= 1`; requests `q_j` arrive on elements at `r_j` with momentary
delay `d_j(t)`; buying a set serves all then-pending requests on its
elements and never future arrivals; requests may go permanently
unserved (their footnote 2); cost = buying cost + accumulated delay.

Translation (`SCDInstance`, `scd_spec`): a step is one time unit; the
action is a purchase or wait; the response carries that step's arrivals
(the environment's channel, irrelevant to any liability's progress);
one liability per request occurrence; the pinned spec accepts a
certificate citing one purchase receipt of a covering set at a time
`>= r_j`.

Preservation. DERIVED and FINITE-TEST-SUPPORTED
(`TestSetCoverWithDelay`): request identity (one liability per
arrival), service time (first covering purchase at or after arrival,
on both sides by the same formula), purchase cost, delay cost, total
objective — term by term on every tested schedule, including the empty
one. Past purchases do not serve future arrivals, matching the paper.

Restrictions defining the subclass: `ResponseIrrelevant` progress +
`FixedIncidence` (action -> covered elements is static) + dynamic
arrivals + action costs + per-occurrence delay. Declared deviation from
the source: the paper's time is continuous; the executable model is
discrete-event with per-step momentary delays, and unserved requests
are accounted to a finite horizon where the paper takes `tau =
infinity`. The translation itself does not depend on the discretization
— both sides' objectives are functions of arrival and purchase times
only.

**Event-order convention (required for online fidelity).** The
fixed-schedule preservation above does not by itself preserve the
online problem: SCD lets the decision at time `t` see arrivals up to
and including `t`, and the naive one-step encoding (act, then receive
the step's arrivals in the response) provably changes the achievable
online cost profiles (`test_naive_encoding_changes_the_online_problem`,
a finite counterexample). The embedding therefore uses the TICK
convention — one source time step is an observation action whose
response carries that step's arrivals, followed by the decision —
which restores the source protocol's policy class exactly
(`test_tick_convention_restores_the_source_protocol`). See
`CERTIFICATION_CLEANUP.md`, verdict B.

**Verdict: honest generalization** under the tick convention. Every
SCD instance is an instance of the generic object; the generic object
does not transfer any SCD competitive guarantee outside these
restrictions.

## B. Submodular Ranking / Minimum Latency Submodular Cover

Source model (arXiv 1110.2207v3 Sections 1-1.1): metric `(V, d)`, root
`r`, normalized monotone submodular `f_1..f_m : 2^V -> [0,1]`; cover
time of `f_i` on path `pi` = `min { t : f_i({v within distance t on
pi}) = 1 }`; objective = sum of cover times. Uniform metric =
Submodular Ranking, where cover time is the covering prefix's length.

Translation (`MLSCInstance`, `mlsc_spec`): actions are vertices,
response space a singleton, per-step cost `d(prev, v)`; spec `i`
certifies by citing a prefix whose visited set reaches `f_i = 1`; cover
time = accumulated cost at first certification.

Preservation. FINITE-TEST-SUPPORTED over all permutations of the
tested instance and DERIVED in general (both sides compute `min` over
prefixes of the same monotone quantity): per-liability cover times and
their sum are equal; uniform metric reproduces the ranking objective
exactly (`TestSubmodularRankingMLSC`).

Exactness notes. Unit-cost ordering (SR) and metric path length (MLSC)
differ only in the per-step cost annotation. Intrinsic action costs are
NOT MLSC — a vertex's cost in MLSC depends on its predecessor; encoding
intrinsic costs as a metric needs a valid metric and is not always
possible. Repeated actions are harmless exactly because the specs
factor through the visited set (`test_repetition_harmless...`);
repetition-sensitive specs (microcase 9) leave the subclass.

Assumptions yielding the subclass: `OrderIrrelevant` +
`RepetitionIrrelevant` (jointly: set-factorizing) + `MonotoneProgress`
+ `SubmodularProgress` + normalization `f_i(V) = 1` + fixed docket +
degenerate `Gamma`. Complementarity (microcase 1) violates
`SubmodularProgress` while remaining a valid spec.

**Verdict: honest generalization**, same caveat on guarantees.

## C. Adaptive Submodularity

Source model (arXiv 1003.3967v5 Sections 2-3, 5.2): items `E`, states
`O`, realization `phi : E -> O`, known prior `p(phi)`; selecting an
item reveals its state; partial realization `psi`; adaptive
monotonicity/submodularity (Definitions 1-3); coverage (Definition 7):
after `psi`, the quota holds under EVERY realization consistent with
`psi`; self-certifying instances (Definition 8).

Translation (`GKInstance`, `gk_env`, `gk_certified`): histories are
partial realizations with order and (idempotent) repetition forgotten;
`Gamma(h, e) = { phi(e) : phi consistent with psi(h) }`; the generic
certificate is exactly Definition 7 — quota under every consistent
realization, a finite record-visible check. In the cleaned
vocabulary: Definition 7 is the existential learner-visible predicate
`Certifiable` (monotone, per the core theorem, under monotone `f` with
the quota objective), and GK instances pair with `LapseFree`
discharge — no record-side window ever refuses a valid certificate.
The paper's own remark that
"it is not enough that a policy achieves value Q for the true
realization; in order to terminate it also requires a proof of this
fact" (their Section 5.2) is precisely the core's L1.

Extra capabilities, none assumed generically: `FixedRealization`
(Gamma presented by a family of response functions; checkable on
finite instances, `fixed_realization_family`), `KnownPrior`,
`AdaptiveMonotone`, `AdaptiveSubmodular` (`gk_adaptive_submodular`,
exact `Fraction` check of Definition 3), `SelfCertifying`
(`gk_self_certifying`, Definition 8). The synergy instance fails
adaptive submodularity; the intervention microcase fails
`FixedRealization` itself — GK's Section 3.4 names both boundaries
(treasure-hunting synergies; POMDP-style realization alteration).

Semantic success vs certification: `gk_semantic` (quota at the true
realization) is analytic; microcase 6 exhibits semantic success with
no certificate on a non-self-certifying instance.

**Verdict: honest generalization** of the coverage/certification
side; the prior-relative expected-cost objectives transfer only under
`KnownPrior` and are annotations, not core.

## D. Interactive Submodular Set Cover

Source model (arXiv 1002.3345v2 Sections 2-3): finite hypothesis class
`H` with unknown target `h*`; questions `q` with known nonempty valid
response sets `q(h)`; responses adversarial but consistent with `h*`;
monotone submodular `F_h` over question-response pairs; goal `F_{h*}
(S) >= alpha`; minimize modular question cost.

Translation (`ISSCInstance`, `issc_env`): `Gamma(h, q) = union of
q(h')` over the current version space — the consistency-relational
environment, expressed directly through `Gamma` with no hidden state
in the interface.

Fixed target vs consistency adversary. DERIVED and finite-tested
(`test_consistency_adversary_equals_fixed_target`): every finite run
of the consistency-relational environment is a run of the fixed-target
environment for every member of its final version space, which is
never empty; so for certified (observation-decided) objectives the two
semantics coincide, and the fixed target is analytic structure. For
the paper's *stated* termination — `F_{h*}(S) >= alpha`, referencing
the true target — they do not coincide: that condition is semantic,
and the learner-visible stopping rule that soundly implies it is the
version-space-uniform certificate `F_h(S) >= alpha` for every
consistent `h` (`issc_certified`), which the tests show can fail while
the semantic condition holds
(`test_semantic_without_certificate_blocks_sound_stopping`). This is
the certification distinction doing real work inside a prior model,
not a philosophical addition to it.

Extra capabilities: `FixedRealization` (hypothesis = realization; this
round compresses ISSC's hypothesis class and GK's realization set into
one capability), `ConsistentAdversarialResponses` (noiseless
consistency), known fixed response relation, `PointwiseSubmodular`
objectives.

**Verdict: honest generalization** of the interaction and
certification structure; the `ln`-factor greedy guarantee transfers
only under the full capability conjunction.

## E. Request-Response games

Source model (arXiv 1406.4648v1 Sections 2-3): arena `(V, V0, V1, E)`;
conditions `(Q_j, P_j)`; Player 0 wins if every `Q_j` visit is followed
by a `P_j` visit; waiting time `wt_j` by the paper's inductive
definition — and, explicitly, "while a request of condition j is open,
additional requests are ignored" (coalescing); play value = limsup of
mean accumulated penalties; optimal finite-state winning strategies
exist via a mean-payoff reduction; RR games reduce to Buechi games
with exponential memory.

This is NOT another nested subclass. Findings:

1. **RR games embed into the generic object** as instances: alternation
   padding turns the arena into act/response steps; each coalesced
   opening mints a liability; the type's spec is "a later `P_j`
   receipt". The embedding is faithful to the paper's accounting:
   `rr_wt_vector` implements the paper's `wt` exactly, and the round
   reproduces Example 2's value `56/10` exactly from the Figure 1
   arena with the alternating strategy
   (`test_paper_example_value_56_over_10`). FINITE-TEST-SUPPORTED.

2. **A restricted fragment compiles to RR.** Finite environment +
   finitely many service types + finite-state recurrent monitors +
   coalescing (a type open mints nothing) => product arena whose RR
   pairs are the monitor-open and monitor-accept vertex sets
   (`compile_to_rr`). Play-level correspondence — RR condition
   satisfied iff every coalesced occurrence is eventually certifiable —
   checked on every simple lasso of the compiled arena, with both
   verdicts realized (`test_play_level_correspondence...`).
   FINITE-TEST-SUPPORTED; the general statement is CONJECTURE at the
   level of full strategy synthesis (this round did not implement RR
   solving; the paper's Buechi reduction covers it).

3. **What breaks the compilation.** COUNTEREXAMPLE
   (`test_identity_bearing_multiplicity_breaks_coalescing`): two
   same-type identity-bearing accruals coalesce to one RR occurrence
   closed by one response; under a per-occurrence exclusive-evidence
   account rule, one liability remains open while the RR verdict is
   satisfied. The paper itself flags the boundary — its [18] is cited
   for the extension where waiting times track the number of open
   requests. Also outside the fragment: per-occurrence pinned specs
   (unboundedly many types), unbounded certificate or monitor state,
   and SCD-style purchase-cost objectives (the paper's quantitative
   theory is waiting-time penalties, a different objective family).

4. **For fixed finite dockets, the right game is reachability, not
   RR.** Individual serviceability is forced reachability in the
   environment x monitor product; joint serviceability of a finite
   docket is generalized reachability, which absorbing accepting
   states reduce to plain reachability (`forced_reach`). RR/Buechi
   enter only for recurrent liability generation. DERIVED;
   `TestServiceabilityGames`.

In the cleaned vocabulary, the RR condition corresponds to EVENTUAL
HISTORICAL SERVICE per coalesced occurrence (every opening eventually
answered) — not record-side discharge; the paper's waiting-time value
is a latency annotation on the same historical notion, and discharge
policy has no RR counterpart.

**Verdict: overlapping abstractions.** RR games are the finite-state,
recurrent, qualitative, *coalescing* fragment; identity-bearing
multiplicity is a genuine expressive mismatch in both directions of
fit, and the quantitative theories differ.
