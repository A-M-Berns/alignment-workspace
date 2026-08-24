# The certified interactive service interface

Status: **research memo; unregistered**. All names are provisional.
Claim labels: DEFINITION, DERIVED (paper derivation), FINITE-TEST-SUPPORTED
(executable witness only), COUNTEREXAMPLE, CONJECTURE, OPEN.

## The surviving object

DEFINITION. A certified interactive service interface is

```text
I = (A, Y, Gamma, Sigma)

A            action space
Y            response space
H            = (A x Y)*, finite observable histories; the transcript
             is the append-only sequence of identity-bearing receipts
             (index, action, response)
Gamma        : H x A -> P+(Y), the permitted-response relation
Sigma        a family of pinned service specifications; each sigma
             carries a certificate type C_sigma and a judge
             Check_sigma : Receipts* x C_sigma -> Bool that reads only
             the receipts the certificate cites
```

Liability occurrences `d = (id, accruedAt, sigma_d, origin...)` are
supplied externally by the normative record and are opaque data to the
service layer. Costs are annotations on optimization problems stated
over `I`, not components of `I`.

Reference model: `src/service_core.py`. Boundary fixture:
`src/composition.py`, `tests/test_composition.py`.

## Subtraction analysis of the conjectured object

The candidate was `I = (A, Y, Gamma : H x A -> P+(Y*), Sigma, Check,
cost)` with optional hidden world state. Each component was attacked.

1. **`Y*` per action deletes to one response event.** A finite response
   sequence is one response in the space `Y' = Y*`; nothing in
   serviceability, certification, or any embedding distinguishes the
   two typings. DERIVED (coding argument);
   `test_response_sequences_collapse_to_one_event`. Environment events
   not triggered by the controller (SCD arrivals) ride in the response
   component of whatever step is current, so no separate event channel
   is needed either.

2. **Hidden world state is deleted from the public interface.** A
   state-based environment `(S, s0, delta)` presents a relational
   `Gamma` by replay (`FiniteStateEnv`), and every relational `Gamma`
   is presented by the state space `H` itself, so state adds no
   expressive power. DERIVED. What hidden state is genuinely needed for
   is defining *semantic success* — quota under the true realization —
   and that notion is deliberately excluded from the core (below). An
   instance that carries realizations (Golovin-Krause,
   Guillory-Bilmes) uses them as analytic structure to state soundness
   relations `Check_sigma(h, c) => Goal_sigma(h, w)` for every `w`
   compatible with `h`; purely procedural specs have no `Goal` and are
   legitimate. FINITE-TEST-SUPPORTED:
   `test_certificate_sound_for_every_consistent_realization`,
   `test_certificate_sound_for_true_target`.

3. **`cost` demotes to objective structure.** `Servable`,
   `JointlyServable`, certification, and the boundary contract never
   read it; the SCD and MLSC objectives are computed from the trace and
   instance annotations alone (`scd_generic_objective`,
   `mlsc_generic_cover_times`). Keeping cost in the core would force
   every qualitative statement to carry a vacuous component.

4. **Proof-relevant certification stays, for one reason only.**
   Extensionally, `sigma` induces the certified-history set
   `L_sigma = { h : exists c, Check_sigma(h, c) }`, an arbitrary
   predicate on `H` — so certificates add nothing to expressive power.
   They are retained because the *record* needs a finite, storable,
   re-checkable object: the certificate is what the upstream record
   files against the liability, and re-checking it later must not
   require re-running inquiry. A `ServiceSpec` is extensionally an
   accepting language of finite traces; a finite-state monitor is one
   implementation (`Monitor`), not interface structure.

5. **Liabilities stay external.** Confirmed by the multiplicity
   microcase: two occurrences with extensionally identical specs must
   remain distinct, which is exactly what identity-bearing external
   supply provides and what any internalization into `I` would have to
   re-invent. `test_one_receipt_two_liabilities`,
   `test_exclusive_rule_closes_only_one`.

## Core laws

- **L1 (finite witness).** DEFINITION. Service closes only on a finite
  certificate over record-visible receipts. No law of the form
  "truth suffices": microcase 6 exhibits hidden semantic success with
  no certificate, and the layer refuses closure
  (`test_semantic_true_certificate_false`).

- **L2 (citation persistence).** DERIVED. `Check` reads only cited
  receipts; the transcript is append-only; therefore a valid
  certificate remains a valid record of its historical service event
  under every trace extension
  (`test_certificate_persists_under_extension`).

- **L2' is rejected as a law.** COUNTEREXAMPLE. Blanket prefix
  persistence of the *predicate* `Certified_sigma` — `Certified(h) =>
  Certified(hh')` — fails for legitimate recency-bounded specs
  ("the probe is current"), while the occurrence-relative record from
  L2 stands (`test_certified_predicate_need_not_be_extension_closed`).
  Extension-closure of `L_sigma` is the capability `MonotoneEvidence`,
  not a law.

- **L3 (observation locality).** DEFINITION, enforced by typing:
  `Check` has no hidden-state parameter to consult. An "omniscient
  checker" is ill-typed rather than illegal.

- **L4 (pinned specification).** Boundary rule: `d` is judged against
  `sigma_d` bound at accrual; migration is an upstream record act. The
  service layer cannot express rebinding
  (`Liability` is frozen; `run_service` looks up `d.spec_id` only).

- **L5 (interpretation separation).** Boundary rule, enforced by
  typing: the service layer's output is a `ServiceOutcome` (liability
  id, certificate, cited receipts); there is no channel through which
  it could assert object-language claims or mutate a stance. The
  vocabulary scan in `test_service_sources_do_not_touch_upstream_or_downstream`
  checks the reference implementation honors this.

Attacks tried and survived: L1 against self-certifying instances
(where truth does imply a certificate — that is a capability, and the
law asks for the certificate, which exists); L2 against certificate
reuse across occurrences (persistence is per-certificate and does not
collapse identities); L4 against spec migration (expressible upstream,
inexpressible in-layer, as intended).

## What the laws do and do not buy

Honest statement: L1-L5 are typing and boundary disciplines. They
prevent category errors — closure on inaccessible truth, history
rewriting, in-layer reinterpretation — and they make the object
auditable; they prove no theorems. The mathematical content of the
abstraction lives in the capability lattice below: each prior model is
a conjunction of capabilities, and each imported guarantee is unlocked
by named capabilities, not by the core. A bare `(A, Y, Gamma, Sigma)`
with no capabilities is exactly "arbitrary games with prefix-decided
acceptance," and no more. The round therefore rejects the reading of
the object as a contentful mathematical theory on its own, and retains
it as the narrow waist those theories restrict.

## Capability taxonomy

Properties of instances, not subtypes. Compressions performed:
GK realizations and ISSC hypothesis classes are one capability
(`FixedRealization`); order- and repetition-irrelevance conjoin to
set-factorization; "coalescing" covers the RR waiting-time semantics.

| capability | definition | assumed by | unlocks | violated by microcase |
|---|---|---|---|---|
| `ResponseIrrelevant` | spec progress independent of responses | SCD, SR/MLSC | offline analysis of schedules | 2, 10 |
| `OrderIrrelevant` | `L_sigma` closed under permuting steps | SR/MLSC, GK, ISSC | set-function methods | 8 |
| `RepetitionIrrelevant` | `L_sigma` factors through step sets | SR/MLSC, GK | ground-set arguments | 9 |
| `FixedIncidence` | static action -> covered-task relation | SCD | covering LPs, delay analysis | 3 |
| `MonotoneProgress` | progress function nondecreasing | SR/MLSC, GK, ISSC | greedy well-defined | — (`MonotoneEvidence` analog fails for recency specs) |
| `SubmodularProgress` | progress submodular | SR/MLSC | ln-factor greedy, SR/MLSC algorithms | 1 |
| `FiniteStateEnvironment` | `Gamma` presented by finite `(S, s0, delta)` | RR | game solving, decidability | — (analysis limit, not a microcase) |
| `FiniteStateServiceMonitor` | `L_sigma` regular, monitor-presented | RR fragment | reachability/RR compilation | unbounded-certificate specs |
| `FixedRealization` | `Gamma` presented by a response-function family | GK, ISSC | posterior/version-space reasoning | 3 |
| `KnownPrior` | distribution over the family | GK | expected-cost objectives, adaptive greedy | 10 (adversarial) |
| `AdaptiveMonotone` / `AdaptiveSubmodular` | GK Definitions 2-3 | GK | adaptive greedy guarantees | 1 (synergy) |
| `SelfCertifying` | GK Definition 8: semantic success implies certificate | GK instances, exact learning | stop-on-success | 6 |
| `ConsistentAdversarialResponses` | responses consistent with some fixed member | ISSC | worst-case greedy guarantee | 3 |
| `CoalescingRequests` | open same-type accruals mint nothing | RR | finite waiting-time state, RR compilation | 5 |
| `MonotoneEvidence` | `Certified_sigma` extension-closed | SCD, SR/MLSC, GK, ISSC | close-once semantics | recency-bounded specs |

## Intentionally excluded

Why an inquiry is owed; when an issue becomes due; what evidence
means; stance revision; decisiveness of reasons; hidden semantic
success; reward or delay semantics as normative importance. The first
five are upstream or downstream by the round's charter; the last two
were excluded by the analysis above.
