# Architecture

The program studies two ways a reasoner can remain responsive while changing.
Normativity concerns learning from reasons inside a practice. Deference concerns
trusting another process without surrendering correction. Legitimacy names the
trajectory conditions both need.

```text
        Normativity
 reasons → responses → learning
             |
         Legitimacy
  standing, records, write access
             |
          Deference
 trust → delegation → corrigibility
```

The current mathematical center is a conditional response-learning result. A
normative layer says when a burden is due and which responses are licensed. A
separate performance layer assigns bounded loss. A loss-blind compiler turns the
normative inputs into surgical response maps, and an online-learning engine
learns against those maps.

```text
Due + Licensed + Performance
             ↓
       lawful compiler
             ↓
   surgical response maps
             ↓
     learning dynamics
```

This separation prevents two shortcuts. A response is not licensed merely
because it lowers loss, and a licensed response need not improve loss. Coverage
is also separate: a theorem about responding on due occasions cannot make those
occasions occur.

## Current mathematical shape

Let `S` be public pre-action states, `D` public burdens, and `A` a finite response
space. The three primitive interfaces are:

```text
Due      : S → D → Prop
Licensed : S → D → A → Prop
Loss     : S → A → [0, L]
```

`Due` and `Licensed` feed the compiler. `Loss` feeds the learning engine, not the
compiler. For a targeted bad response `b` and licensed alternative `r`, a
positive margin `Loss(S,b) - Loss(S,r) ≥ δ_g > 0` is an additional performance
hypothesis. Coverage measures how often the relevant `Due` occasions appear
relative to the learning scale.

> **Current status — Open / unregistered.** The abstract theorem and dynamics
> witness are current research results with exact round verdicts, but
> <!--historical-->PR #31 registered no workspace claim<!--/historical-->.
> `Due` has no satisfactory substantive instantiation; `Licensed` has interface
> discipline but not substantive soundness; performance is successful only for
> the fixtures; coverage remains a hypothesis.

## Hypothesis ledger

The following table is the machine-significant projection of
`normativity.learning.current`. It mirrors the repository ledger rather than
serving as an independent source of interface state.

<!-- theorem-interface-ledger: normativity.learning.current -->
| ID | notation | kind | producers | consumers | write access | excluded from loss | presentation requirements | registered status | soundness claim IDs |
|---|---|---|---|---|---|---|---|---|---|
| `due` | `Due : S → D → Prop` | `primitive-normative-interface` | `substrate.relational-answerability`; `interface.normative` | `compiler.surgical`; `interface.coverage` | `public-pre-action-record` | — | — | `null` | — |
| `licensed` | `Licensed : S → D → A → Prop` | `primitive-normative-interface` | `interface.normative` | `compiler.surgical` | `public-pre-action-record`; `normative-practice` | — | — | `null` | — |
| `performance-loss` | `Loss : S → A → [0, L]` | `primitive-performance-interface` | `interface.normative` | `engine.blum-mansour`; `theorem.response-learning`; `witness.learning-dynamics` | `learner-acknowledgments`; `ecology-challenges`; `scorekeeper-practice` | `standing`; `grants` | — | `null` | — |
| `response-space` | `A` | `finite-theorem-interface` | `interface.normative` | `compiler.surgical`; `engine.blum-mansour`; `theorem.response-learning` | `specification` | — | — | `null` | — |
| `due-selector-compilation` | `Due → selector` | `compiler-interface` | `interface.normative`; `compiler.surgical` | `engine.blum-mansour` | `public-pre-action-record`; `normative-compiler` | — | `decidable`; `record-computable`; `prospective` | `null` | — |
| `compiled-surgical-repairs` | `CertifiedSurgicalRepair` | `compiler-output` | `compiler.surgical` | `engine.blum-mansour`; `theorem.response-learning` | `normative-compiler` | — | — | `null` | — |
| `blum-mansour-engine` | `Blum–Mansour engine` | `learning-engine` | `engine.blum-mansour` | `theorem.response-learning`; `witness.learning-dynamics` | `learner-policy` | — | — | `null` | — |
| `positive-margin` | `δ_g > 0` | `joint-performance-hypothesis` | `interface.normative` | `theorem.response-learning` | `joint-licensed-response-and-performance` | — | — | `null` | — |
| `coverage` | `coverage(Due)` | `quantitative-property-of-due` | `interface.coverage` | `theorem.response-learning` | `ecology-trajectory` | — | — | `null` | — |
| `compiler-loss-blindness` | `compiler ⟂ Loss` | `compiler-discipline` | `audit.compiler-soundness`; `compiler.surgical` | `theorem.response-learning` | `compiler-input-boundary` | — | — | `null` | — |

## Write access and legitimacy

The learner writes its own acknowledgments and policy. It does not get to decide
whether a burden is due, and the compiler does not read current loss advantage.
In the relational fixture, challenges, exposures, and the scorekeeper's practice
come from other parts of the ecology. Standing and grants may gate what is due,
but they are excluded from theorem-facing loss because a learner-controlled grant
created a laundering route.

Answerability is owing an answer; auditability is the record knowing what became
of every debt; efficacy is the answer-demand actually reaching you. Response
learning uses the first two. Corrigibility uses the first and the third.
[Legitimacy](Legitimacy) is where their write and trajectory conditions meet, framed
there as legitimate cognitive evolution: [Integrity](Integrity) and
[answerability](Diachronic-Answerability) on the history side,
[robust openness](Openness-Coverage-and-Non-Capture) on the intake side, and
[normative induction](Normative-Induction) as the quantitative consequence.

## What the theorem does—and does not—cover

The current accounting compares surgical responses against losses on the actual
trajectory. With a positive margin, low modification regret bounds bad-response
mass on due occasions. A separate coverage hypothesis turns that bound into a
vanishing conditional rate. It does not establish that the counterfactual world
in which the repair was always applied would have improved.

Nor does the abstract theorem solve normative content. It exposes typed sockets
for `Due`, `Licensed`, and performance. Supplying those sockets soundly is the
next substantive problem.

## Evidence and verification

- [Crown-jewel final report — `NORMATIVE-RESPONSE-LEARNING-THEOREM-SETTLED`; `BM-FEEDBACK-DYNAMICS-WITNESSED`](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/prompts/2026-08-13-crown-jewel-learning-theorem-final/REPORT.md)
- [Three-interface boundary](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/rounds/2026-08-13-crown-jewel-learning-theorem/INTERFACES.md)
- [Compiler soundness and loss-blindness](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/rounds/2026-08-13-crown-jewel-learning-theorem/COMPILER_SOUNDNESS.md)
- [Coverage interface](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/rounds/2026-08-13-crown-jewel-learning-theorem/COVERAGE_INTERFACE.md)
- [Machine-readable interface ledger](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/state/theorem_interface.json)
- [Legitimacy loss-dependency audit](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/LOSS_DEPENDENCY_AUDIT.md)
