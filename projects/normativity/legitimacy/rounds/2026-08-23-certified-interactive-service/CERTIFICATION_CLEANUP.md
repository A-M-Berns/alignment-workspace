# Certification semantics cleanup

Status: **research memo; unregistered**. Follow-up prosecution of the
round's certification, timing, and boundary semantics. Labels as in
the other round documents.

Governing types: `CLOSEOUT.md`. This memo's `Admit_sigma` component,
introduced here inside the spec, was factored out by the closeout
pass to the record-side account layer (`MayClose` over `(N, L, o, c,
now)`); the prosecution below, and everything it establishes about
validity, monotonicity, and lapse, is unchanged by that move.

## A. Certification verdict: `SPLIT-VALIDITY-AND-CLOSURE`

The original memo conflated three predicates and drew one wrong
conclusion from the conflation.

DEFINITION. For a pinned spec `sigma = (C_sigma, Check_sigma,
Admit_sigma)` over transcript `L`:

```text
ValidCert(sigma, L, c)     Check_sigma judges c against the receipts
                           it cites; citation-local by type.
Certifiable(sigma, L)      exists c, ValidCert(sigma, L, c) — the
                           extensional acceptance predicate.
MayClose(d, L, n, c)       ValidCert holds AND Admit_sigma(n, c,
                           cited) holds now: c is presently
                           admissible for discharging open d.
ProverFinds(sigma, L)      an attached discovery algorithm returns a
                           certificate the judge accepts. Not a
                           semantic predicate at all.
```

DERIVED (the monotonicity theorem). `Certifiable` is extension-closed:
if `ValidCert(sigma, L, c)` then `ValidCert(sigma, LL', c)`, because
`Check` reads only cited receipts, receipts are immutable, and
indices are stable under append; so the existential persists.
`test_certifiable_is_extension_closed` exercises it, including on the
spec previously offered as a counterexample.

COUNTEREXAMPLE, RETRACTED. The earlier "recency-bounded spec"
counterexample to prefix persistence distinguished nothing but the
prover: its `Check` was citation-local (hence monotone existentially);
only `make_cert` stopped returning a certificate after an extension.
"The current prover emits a certificate" and "there exists a valid
certificate" are different predicates, and the old
`ServiceSpec.certified` computed the first while the memo read it as
the second. The claim "the Certified predicate need not be
extension-closed" is withdrawn.

What the retracted example was reaching for is real and lands in
`MayClose`: a freshness condition (`now - receipt index <= k`) makes a
certificate lapse as a closure instrument without falsifying the
historical record (`test_lapsed_certificate_remains_valid`).

Required adversarial cases (all in `tests/test_interface.py` and
`tests/test_composition.py`):

1. valid at `t` stays valid at `t+10` — `test_certificate_persists_under_extension`;
2. same certificate lapses for closure after a freshness deadline —
   `test_lapsed_certificate_remains_valid`;
3. prover incompleteness does not witness nonexistence —
   `test_prover_incompleteness_is_not_nonexistence` (lazy prover
   fails; exhaustive `certifiable` succeeds);
4. a contradictory later receipt does not rewrite the historical
   service event — `test_contradictory_receipt_does_not_rewrite_history`;
5. it may mint an upstream review liability instead —
   `test_contradictory_receipt_yields_review_not_invalidation`;
6. genuinely context-dependent acceptance ("the probe is the current
   last step") is INEXPRESSIBLE as a citation-local `Check`: the
   judge never sees the present transcript length, and prover-supplied
   data claiming nowness is unverifiable, so the existential stays
   monotone. Such semantics is represented as closure admissibility —
   `test_context_dependent_acceptance_is_inexpressible_in_check`.
   Citation locality is NOT weakened.

## `MonotoneEvidence` resolved

Answer A-and-B of the dispatch's options: `Certifiable` is necessarily
monotone (theorem of the core — removed from the capability lattice),
and `MayClose` is a second, legitimately non-monotone predicate. No
two uses of "certified" remain: round documents now say *certifiable*
(historical, monotone) or *admissible/closable* (present, lapsable).
The lattice gains `LapseFree` — `Admit_sigma` trivially true — which
is a closure-policy property, not a spec-language property; every
embedded prior model is lapse-free.

## What a ServiceSpec is

Constitutive: `(C_sigma, Check_sigma, Admit_sigma)`. `Check` alone
induces the extensional acceptance language `{ L : Certifiable }`,
which is what a finite-state `Monitor` implements — absorbing
acceptance is now justified by the monotonicity theorem rather than
by stipulation. `Admit` owns present closure conditions; a live
admissibility monitor would be a separate object (not built).
`make_cert`/`prove` is an attached prover: an algorithm for
discovering witnesses, never part of the spec's semantics; the
reference model exposes `certifiable(...)` (bounded exhaustive
search) as the decision procedure for the semantic predicate, and
`prover_certified(...)` as the explicitly prover-relative statement.

## B. Environment timing verdict: `CURRENT-TURN-MODEL-SUFFICIENT-WITH-CONVENTION`

The claim that SCD arrivals can "ride in the response component" was
too quick as stated: objective equality on fixed schedules does not
give protocol equivalence online. COUNTEREXAMPLE
(`test_naive_encoding_changes_the_online_problem`): one element, one
unit-cost set, delay 10/step, arrival-or-not at time 0. The SCD
protocol (decide at `t` seeing arrivals `<= t`) achieves cost profile
`(1, 0)`; under the naive one-step encoding (act before seeing the
step's arrivals) every deterministic policy has strictly larger total
cost across the two scenarios.

REPAIR, exact (`test_tick_convention_restores_the_source_protocol`):
encode one source time step as two generic steps — an observation
action (`tick`) whose response carries that step's arrivals, then the
decision. The achievable profile sets coincide exactly with the
source protocol's. No new step type and no exogenous event channel is
added to the core; the convention is a requirement ON EMBEDDINGS:
preserve the source model's observation/action order, using
observation actions where the source reveals before deciding. The
SCD embedding text now carries this convention.

## Environment semantics statement

`Gamma(h, a)` denotes the EPISTEMICALLY POSSIBLE responses given the
public history — what the record can rule out — not the true hidden
transition dynamics. Consequences, generalizing the ISSC lesson:

- A hidden-state family induces its relational `Gamma` by
  whole-history consistency (`{y : some configuration consistent with
  h permits y}`), and defining it this way — rather than memorylessly
  from currently-reachable states — is what preserves cross-time
  correlations (the tested GK/ISSC envs are built exactly so).
- Under that construction, every finite `Gamma`-run maintains a
  nonempty consistent set whose members each generate the whole run,
  so adversarial (worst-case) strategy semantics against `Gamma`
  coincide with adversarial semantics against a fixed hidden
  configuration — DERIVED for fixed-configuration families;
  finite-tested via `test_consistency_adversary_equals_fixed_target`.
- The solver's `FiniteStateEnv` is an observation-deterministic
  compression (its replay is unambiguous by construction); it is a
  presentation choice, and nothing in the public interface names
  states.

## Serviceability notions after the split

The lattice that survives examples (all separations witnessed in
`tests/`):

```text
ever-certifiable(d, h)      some continuation reaches Certifiable
forceable(d, h)             = Servable: a policy forces Certifiable
                            against every permitted response
timely-closable(d, h)       a policy forces reaching a moment where
                            some certificate is valid AND admissible
eventually-closed(d, rho)   on the actual run, the record performed
                            the closure account (upstream act)
bounded-latency             quantitative annotation on any of these
```

- ever vs forceable: the evasion arena
  (`test_unservable_when_adversary_can_evade` — some run certifies,
  none is forced).
- forceable vs timely-closable: deadline-in-`Admit` overload
  (`test_deadline_in_discharge_defeats_timely_closure_only` — every
  occurrence eventually certifiable, later ones never admissible).
- The solver's `Monitor.accepting` targets HISTORICAL certifiability
  (correct after the split; absorbing = the monotonicity theorem).
  Timely closability would need admissibility-aware monitors — noted,
  not built.

Overload, restated without the ambiguous word "service":

- deadline in `Check` (an index-window constraint — citation-local,
  monotone, but time-barred): overload defeats forceable
  certifiability itself (`test_deadline_in_check_defeats_certifiability`);
- deadline in `Admit`: overload defeats timely closure while late
  historical certification survives;
- no deadline: overload defeats only bounded latency
  (`test_fifo_eventual_service_with_diverging_wait`).

## C. Reason-waist compatibility verdict: `CLEAN-COMPOSITION`

Against the stipulated frozen interface (sources `V ⊔ L`, occurrence
`e = (id, sources, target, applied_as)`): the strong hypothesis holds
on every tested case — a reason never cites the ServiceCertificate.
The certificate answers "was the owed investigation adequately
performed" and is consumed by the record's closure account; reasons
cite receipts (and contents). `tests/test_composition.py::
TestThreeProvenance` is now the canonical composition fixture:

- canonical microhistory where evidential grounds (receipts cited by
  `e`), procedural adequacy (certificate `k` citing the same
  receipts), and accounting license (record closes `d` using `k`)
  all differ, and `e` does not cite `k`;
- valid certificate with `NoBearing` assessment (nothing minted,
  closure unaffected) — dispatch cases 1 and 3;
- same receipts, different `applied_as`, different conclusions —
  case 2;
- shared evidence, two closures, one reason occurrence — case 4;
- "this experiment followed protocol P" as an ordinary content in
  `V` supported by receipts — case 5; no new source sort.

`V ⊔ L` remains sufficient for the reason waist on all tested cases;
no blocking interface issue found. The reason representation is
untouched; the stubs live in the test file because the service
sources must not import downstream vocabulary (the scan enforces it).

## Capability lattice audit (layer typing)

Moved or re-typed:

- `MonotoneEvidence`: DELETED — theorem of the core (above).
- `LapseFree`: ADDED — closure-policy property (`Admit` trivial).
- `CoalescingRequests`: re-typed as a property of the UPSTREAM
  MINTING POLICY (open same-type accruals mint nothing), not of the
  service object; the RR compilation consumes it from the record
  side.
- `KnownPrior`: environment-annotation property unlocking
  expected-cost OBJECTIVES; the qualitative core never reads it.
- `ResponseIrrelevant`, `FixedIncidence`, `OrderIrrelevant`,
  `RepetitionIrrelevant`, `MonotoneProgress`, `SubmodularProgress`:
  properties of the spec family (their subjects are `Check`-induced
  languages or progress annotations), confirmed correctly typed.
- `FiniteStateEnvironment`, `FixedRealization`,
  `ConsistentAdversarialResponses`: environment-presentation
  properties, confirmed.
- `FiniteStateServiceMonitor`: property of the acceptance language
  (regularity), confirmed.
- `AdaptiveMonotone`/`AdaptiveSubmodular`, `SelfCertifying`:
  instance-analytic properties relating hidden structure, objectives,
  and `Certifiable`, confirmed with that label.

No capability is a property of the prover; prover structure never
carries a theorem in this round.

## Prior-art claim deltas (conservative)

- SCD: embedding claims now name the tick convention as the required
  event-order convention for ONLINE fidelity; fixed-schedule
  objective preservation is unchanged.
- Golovin-Krause: "coverage (Definition 7) is the generic
  certificate" is retained with sharpened wording: it is the
  existential learner-visible predicate `Certifiable`, monotone (their
  Definition 7 under monotone `f` with the quota objective), and
  their instances are lapse-free.
- ISSC: the semantic/certified distinction survives unchanged under
  the cleaned types; the repaired stopping rule is the
  version-space-uniform `Certifiable`.
- RR games: the correspondence is to EVENTUAL HISTORICAL SERVICE
  under coalescing (every opening eventually certifiable/answered) —
  not timely closure; the paper's waiting-time value adds a latency
  annotation, still not admissibility.
- MLSC/SR: no timing or closure content; unchanged.

## Implementation artifacts sorted

| object | status after cleanup |
|---|---|
| `ServiceSpec.check` | semantic definition (ValidCert) |
| `ServiceSpec.admissible` | semantic definition (MayClose component) |
| `ServiceSpec.prove` | attached algorithm, non-constitutive |
| `certifiable(...)` | decision procedure for the existential predicate, complete on this round's certificate spaces |
| `prover_certified(...)` | explicitly prover-relative testing helper |
| `Monitor` (absorbing) | implementation of historical certifiability, justified by the monotonicity theorem |
| `forced_reach`, `servable`, `jointly_servable` | decision procedures for forceable certifiability on finite presentations |
| `FiniteStateEnv.state_after` | implementation convenience (observation-deterministic replay), documented as presentation scope |
| `order_irrelevant`, `repetition_irrelevant` | finite testing helpers; probe via prover, documented complete-prover caveat |
| `fixed_realization_family` | finite testing helper (capability decision on tiny instances) |

## D. Overall verdict

PR #51 remains `REQUIRES-REVISION — SURVIVES`, with the revision now
including the validity/closure split. The split strengthens the
original result: one candidate law (certificate persistence) was
upgraded from stipulation to theorem, one alleged counterexample was
retracted as a prover artifact, and the freshness phenomenon it
gestured at found its correct home in closure admissibility. No
change to the surviving object's arity: `Sigma`'s elements were
always pinned specifications; they are now typed as
`(C_sigma, Check_sigma, Admit_sigma)`.
