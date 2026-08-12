# Normative-learning interface

Status: **ASPIRATIONAL / OPEN routing note.** “Normative-learning interface” is
provisional terminology pending maintainer review. This note adds no theorem and
changes no existing result status.

## Motivation

The current eight-action, nine-program construction is a worked instantiation.
It identifies a reusable boundary between generic online learning and the
normative architecture that determines which repairs count as lawful. Docket
liability, tolling, warrants, and obligations instantiate that boundary; they
are not intended as parameters of the eventual paper-level theorem.

## Three levels

### A. Generic online-learning interface

The theorem-facing objects are a horizon-independent finite semantic response
space `A`, a public pre-action state `s_t`, a bounded prospective loss generator
`G(s_t) = ell_t in [0,L]^A`, and a rule grammar `Gcal` whose programs compile to
causal transformations

`interpret(g)(s_t, a) in A`.

For the current finite family, Blum--Mansour (2007), Theorem 18 supplies the
online-learning reduction once the transformations and full bounded loss vector
are available. The intended general theorem may require a different complexity
measure when the grammar is enlarged. Finite cardinality, description length,
prior mass, and statistical complexity remain open design choices.

### B. Normative compilation interface

The learner consumes transformations; it need not interpret warrants,
defeaters, commitments, or objections. A normative architecture must separately
justify compiling its public reasons into admissible transformations.

```text
normative architecture
        |
        | compile public reasons
        v
lawful transformation grammar
        |
        | online learning
        v
regret / self-correction guarantee
```

Candidate compilation conditions extracted from the worked instantiation are:
historical availability, causal public access, reason connection, defeater
discipline, authority and scope, magnitude discipline, burden/history
preservation, replacement support, and independence of lawfulness from
comparative advantage. This list is **candidate and incomplete**, not an
axiomatization theorem.

### C. Counterfactual stability

The current result compares additive local losses while filings, reasons, and
arrivals are frozen and suspension and solvency coupling are absent. A richer
edit can change future obligations, reasons, losses, service availability,
accounting, ontology, or procedure. The existing solvency-coupling witness shows
that one edit can then have horizon-sized downstream effect.

A future layer should measure the difference between local fixed-loss comparison
and full replay, provisionally by a distortion term `B_T(g)`. The target
`B_T(g) = o(T)` is **ASPIRATIONAL / OPEN**. This note does not assert that it is
sufficient for the final counterfactual semantics.

## Interface map

| generic role | current instantiation | status |
|---|---|---|
| semantic response space `A` | eight semantic labels | constructed |
| public pre-action state `s_t` | restricted actual-prefix public reason context | constructed |
| loss generator `G` | docket liability / charge vector | constructed |
| rule grammar `Gcal` | nine declarative lawful programs | constructed, weak |
| compiler soundness | reasons-responsiveness checks plus decoder bridge | partial, architecture-specific |
| learner | Blum--Mansour Theorem 18 construction | constructed |
| counterfactual stability | frozen filings/reasons; no suspension or solvency coupling | assumption, not generalized |
| learner-state answerability | no repository-native policy-state record | blocking |
| computation budget | no service cost for updates or stationary solve | blocking |

The fixed action type, bounded full-information losses, causal transformations,
finite comparator family, and stationary construction belong to the current
online-learning theorem interface. Historical grounds, defeaters, authority,
scope, burden preservation, replacement support, and profit-independent
lawfulness belong to the normative interpretation. A transformation can be a
legal Phi-comparator without thereby being normatively licensed; normative
licensing is an additional compilation judgment.

## The role of docket liability

Docket liability is the first constructed loss process because it is bounded,
public, derived from the record, and prices practical disposition without an
unsupported exchange rate between unrelated quantities. It is a loss for the
learning theorem, not a measure of normative correctness.

The paper-level ambition is to depend on structural properties of a loss process
rather than the interpretation “docket liability.” Candidate future targets are
arbitrary bounded prospective public loss generators, invariance under positive
scaling and action-independent shifts, broader loss-equivalence, and eventually
non-scalar evaluation. None is established here; vector-valued learning is
outside this program stage.

## The role of the nine programs

The nine programs are a finite theorem instantiation and test fixture. The
existing witness in the item-30 round has zero Phi-regret against all nine while
paying substantially more charge than action Hedge. Comparator-language
generalization is therefore necessary for any stronger normative-learning
interpretation.

A larger language might use a generative grammar, complexity-sensitive regret,
prior-weighted comparators, or description-length bounds. This note selects none
of them.

## What the current result already establishes

- A fixed eight-element semantic response space and nine immutable declarative
  programs compile to closed causal transformations in the frozen environment.
- The lawfulness adapter for that exact class cannot inspect charge or
  profitability through its public context.
- Pointwise, mixed, cumulative, counterfactual, and regret quantities are
  preserved by the semantic-action bridge.
- Blum--Mansour Theorem 18 gives the horizon-tuned ideal learner expected mixed-
  action regret `O(ell_max sqrt(8 T log 9))` against that class.
- The implemented learner realizes the theorem's row-conditioned structure with
  controlled numerical real arithmetic and exact stationarity for represented
  weights.
- Sublinear expected regret retires positive asymptotic expected mass on a
  represented uniformly saving admitted repair.
- Sampled canonical responses preserve the tested answerability record and
  response-service limits.

The controlling verdict remains **Learning-positive, integration-blocked**.

## Aspirational theorem shapes

**ASPIRATIONAL / OPEN — generic interface theorem.** Given a suitable bounded
prospective public loss process and a suitable finite or complexity-controlled
causal transformation grammar, construct an online learner with low expected
regret against the grammar's compiled transformations.

**ASPIRATIONAL / OPEN — normative compilation theorem.** State conditions under
which a reasons architecture soundly compiles its public historical reasons to
admissible causal transformations independently of comparative advantage.

**ASPIRATIONAL / OPEN — counterfactual lift.** Under a suitable stability bound
relating local loss comparison to full replay, lift local transformation regret
to a counterfactual self-correction statement.

## Fixture-specific assumptions to discharge or parameterize

- eight canonical response labels and occasion-local decoding;
- exactly nine programs and the finite non-capture audit;
- one occasion per date and `service_window = 4`;
- frozen arrivals, schedules, filings, and relevant reasons;
- actual strict-prefix guards;
- full charge-vector feedback and `ell_max = 2`;
- no suspension, solvency coupling, or post-hoc affordability deletion;
- horizon-tuned learning and controlled numerical real arithmetic.

Some conditions may remain legitimate hypotheses. Interface extraction must
identify which are mathematically used rather than remove them by default.

## What must be generalized before this becomes the paper-level theorem

1. Parameterize the bridge and learner over a minimal bounded prospective loss
   interface, with docket charge as one instance.
2. Separate the minimal causal transformation API required by online learning
   from the normative certificate that licenses a compiled rule.
3. Choose and analyze a comparator-language complexity model richer than nine
   hand-selected programs.
4. State a counterfactual-stability condition that controls endogenous future
   effects without hiding the frozen assumptions.
5. Give the learner's computation and policy state a declared bounded,
   historically answerable repository interface.
6. Separately address sampled-path and anytime guarantees where needed.

## Paper arc

1. Agents may need to revise normative judgments after deployment without a
   fixed normative target.
2. Public reasons determine which counterfactual changes qualify as admissible
   repairs.
3. Normative compilation produces causal transformation comparators.
4. Online learning controls regret against those transformations.
5. Uniformly beneficial represented repairs cannot remain relevant at positive
   asymptotic expected rate.
6. Docket liability, the finite reason interface, eight actions, and nine
   programs supply the worked instantiation.
7. Comparator coverage, endogenous replay, learner-state answerability,
   computation cost, and inquiry bound the current claim.

The next low-invention round is loss-interface extraction: parameterize only the
properties already used by the bridge and learner, re-instantiate docket charge,
and add one synthetic bounded prospective generator to demonstrate that the API
is not docket-specific.
