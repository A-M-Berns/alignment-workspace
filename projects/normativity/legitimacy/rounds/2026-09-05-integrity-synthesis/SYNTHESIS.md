# Synthesis

All names introduced here are provisional.

## 1. Integrity and Answerability

The best current type is a proof-relevant segment package, not the six-field lattice
predicate alone:

```text
IntegritySegment(H,m,n) :=
  record : RecordIntegrity(H,m,n)
  slices : declared authenticated anchored slice family
  initial : initial account for every declared slice
  lifecycle : every transition carries ContentLifecycle
  boundary : endpoint data needed to compose certificates
```

`RecordIntegrity` supplies append-only event identity, immutable anchors and cited
bases, strict-prefix provenance and authority, and replayability. `ContentLifecycle`
supplies adequate-answer receipts, settlement availability plus an immutable internal
closure certificate, and faithful carry preserving anchored meaning, occurrence
multiplicity, standing requirements, and split/merge jointness.

Generic record Integrity does **not** imply Diachronic Answerability. Exact and Lean
countermodels preserve strong structural conditions while accepting an unchecked
answer, unrelated settlement, self-grounded full carry, minted standing, or a hollow
ledger. The minimal extra normative clause is content lifecycle conservation: each
incurred anchored obligation occurrence has exactly one of three content fates — an
adequate answer, a valid settlement-backed discharge, or certified live carry. The
constructive lattice theorem proves account conservation once that clause, authenticated
slices, and initial accounts are hypotheses. It does not derive those hypotheses.

The proof-relevant primitive is `IntegritySegment`. A downstream endpoint relation may
be defined by existence of such a package:

```text
H_m <=leg H_n := exists C : IntegritySegment(H,m,n), True.
```

Reflexivity and concatenation are Lean-proved for one fixed ledger and `Closes`
interpretation. Transitivity of the public relation additionally requires the endpoint
state to package the slice universe, certificate identities, and boundary equality or
an authenticated transport between them. Antisymmetry and witness uniqueness are not
expected.

## 2. Settlement and closure

An external settlement item is an item available through a declared authenticated
boundary. The generic interface assumes provenance/interface authenticity. Epistemic
trustworthiness is a separate domain assumption. Append-only availability is required
when later theorems read past settlement; the stronger nesting/monotonicity assumption
is required by the landed affordability comparison. Resistance to delay or suppression
is a Non-Capture clause only when the declared intervention class and route adequacy
make access timing relevant.

```text
Closes(H_n,s,alpha)
```

is an internal certificate under the rule, interpretation, grounds, and licence in
force at prefix `n`. A discharge requires authenticated availability of `s`, the stored
`Closes` certificate, and authorized transition provenance. Authentication of `s`
does not establish `Closes`; `Closes` does not establish truth of `s`.

Later rejection does not change whether the historical discharge carried its required
certificate. It appends `Reconsiders(new,old,certificate)` and a fresh obligation whose
anchored load states what is owed now. The old settlement item, closure event, and
terminal token remain immutable. Whether reconsideration is mandatory for every
successful challenge is open application-level normative content.

## 3. External bills

For declared scope `Gamma`, interventions `J`, semantics `I`, and protected principal
or relation `P`, the minimal Non-Capture bill surviving its necessity attacks is:

```text
CoverageActual
+ S  : a concern becoming live only counterfactually has an adequate route
+ R+ : an actually and counterfactually live concern retains every adequate route,
       or gains an adequate replacement
+ P  : P retains standing on each counterfactually relevant concern
=> RobustOpen.
```

The theorem is Lean-proved. Concern/target identity, applicability transport, branch
coupling, and the exterior policy held fixed are typing supplied by the intervention
semantics. Settlement delivery and evaluator fidelity remain separately typed.

The minimal public practical bill is edge-local:

```text
PracticalCert(e,s,Pi_s;M_es,epsilon_es) :=
  Lambda_es(Pi_s) <= M_es * d_s + epsilon_es.
```

`Pi_s` is the single response distribution actually realized at service occurrence
`s`. Joint compatibility requires this inequality for every supported exposure edge
against that same `Pi_s`. Value correspondence and a non-scalar adequate-set route are
distinct sufficient factorizations, not the definition.

The E-to-D type-check exposed one adapter, now Lean-proved:

```text
T(e,s) > 0 -> ell(e) <= Lambda_es(Pi_s)
0 <= ell(e) <= D.
```

This `HeadlineToEdgeDominance` belongs to the evaluation/transport adapter, not inside
`PracticalCert`: it connects the exposure-level Progress statistic to edge response
loss while retaining residual accounting.

## 4. Remaining Normative Inductor obligations

Agent-sized integration work:

- implement one authenticated event history and prove its export into the qualitative
  obligation process;
- bind anchored specifications, closure/answer/carry certificates, and event-time
  authority to that export;
- connect a declared compiler's provenance-bearing rows to the existing effective
  rows-to-vertices/projection path;
- instantiate projection work, bounded liability, and declared-workload scheduling
  connectors;
- implement the transport checker binding every supported edge to one response receipt;
- instantiate `HeadlineToEdgeDominance` and package the already Lean-proved conditional
  composition theorem.

Genuine research:

- useful convex-representable obligation classes and compiler completeness within them;
- adversarial online or closed-loop affordable scheduling;
- generation of quantitative semantic-transport certificates through ontology change;
- substantive authorization rules for closure, answer, defeat, and reconsideration;
- a concrete jointly compatible practical-response ecology.

Intentionally external contracts:

- settlement source trust and boundary authenticity for the selected domain;
- intervention-relative Non-Capture, including the coupling and protected party;
- causal/counterfactual identification and response-evaluator adequacy;
- the application-declared normative scope and evaluation protocol.

These contracts should cease appearing as promises for the generic internal theory to
derive. The generic theorem names them and composes their outputs.
