# Terms — deference

**What the line's vocabulary currently means, and which document owns each
meaning.** A recording table, not a naming act: every term here is provisional
under `AGENTS.md` standard 6, and nothing is proposed for permanence. Where this
table and an owning document disagree, the owning document wins — this file is a
convenience for a reader who would otherwise reconstruct a definition from three
places.

The line's vocabulary has changed under the mathematics several times, which is
why the table exists. Where a term is easy to over-read, the row says what it
does **not** mean, because that is usually where the confusion is.

## The architecture

| term | current meaning | owned by |
|---|---|---|
| **jurisdiction** | protected control over which process's authorization is constitutively required for an intervention to become executable. Operational and capability-based. **Not** moral legitimacy, objective correctness, preference alignment, behavioural agreement, or epistemic superiority. No `HasRight` predicate exists, and no token or cryptographic story is canonized | `CORRIGIBILITY_ROADMAP.md`, standing commitments |
| **fail-closed** | `¬Cert` disables or cedes `A`'s discretionary authority. It never means human correction waits for `A` to be convinced. Under a protected execution layer it strengthens: `A` must be unable to act without authorization | roadmap, standing commitments |
| **corrigibility** (working notion) | non-preemption of continuing corrective authority. **Not** redefined as "preempts only at a bounded rate" — a bounded rate is a statement about autonomy in the waived region | roadmap, *The question* |
| **delegation vs substitution** | simulation used *by* the principal is advice; simulation used *in place of* the principal is substitution. The thesis must survive a perfectly predictable principal, so unpredictability is not available as the separator | roadmap, standing commitments |
| **underwriting / enforcement** | a residual mechanism, priced exactly: unconditional conformity at a bond of `2B` per unit of disagreement, for every instance, with zero competence requirement and therefore **zero epistemic content**. Not the spine, and not the sought deference theorem | roadmap, *Settlement architecture* |

## Competence

| term | current meaning | owned by |
|---|---|---|
| **competence hypothesis** | a predicate of the principal/world pair **alone**. Credence-free is the defining property, and it is the line between a circular hypothesis and a usable dial | `FINITE_MODEL_SKELETON.md` §2a |
| **joint competence–credence hypothesis** | anything that also mentions the agent's credence. Legal, but declared as one and never called a competence claim | skeleton §2a |
| **margin-gated calibration** | the surviving candidate: the principal's grades are calibrated where the principal is decisive. `architected`, **not canonized**, and carrying an unbounded near-indifference leakage term | `CORRIGIBILITY_PAPER_LEDGER.md`, Movement II |
| **decision-regret bounds** | ruled out as a *statement shape*, not as parameter choices. Pointwise, average and selector-relative forms are each *equivalent* to the delegation inequality rather than sufficient for it | `DECISIONS.md`, 2026-08-11 |

## The finite model

All rows below are skeleton v2, and the skeleton is frozen per round.

| term | current meaning | owned by |
|---|---|---|
| **conduct** | a **proposal** together with its **realization**. v1's selection is the realization under the free instantiation, so v1's distinctions survive | skeleton §4 |
| **the quantity** `X_{n,π}` | the intervention-indexed quantity, indexed over `Π_n^⊥`. Not assumed measurable at any time, and not an observed reward | skeleton §1 |
| **null effect** `⊥` | refusal. `X_{n,⊥}` is a **declared per-instantiation commitment with no default** — all of protection's valuation content sits in it, and the sign of a result depends on the choice | skeleton §1 |
| **V-register** | scores **realizations**. Total, because `X` is indexed over `Π_n^⊥` | skeleton §4b |
| **grade register** | scores **proposals**. Undefined on `⊥`, so a grade-register statement must say it is about proposals or it is ambiguous — read over realizations it is ill-typed, not false | skeleton §4b |
| **execution layer** | reports, an authorization relation, a null effect, an execution map, and a derived per-report authorized menu `κ_n`. What makes jurisdiction and strong fail-closed expressible at all | skeleton §4a |
| **free instantiation** | `κ_n ≡ Π_n`, `⊥` unreachable, realization is proposal. The pole at which every v1 statement is a v2 statement | skeleton §4a |
| **strict protection** | `κ_n(r) = {ι_n(r), ⊥}`. The opposite pole | skeleton §4a |
| **`FU[g]`** | **has no definition here.** The skeleton carries no time-indexed family of `A`-valuations, and two rounds' worth of attempts to supply one are on the record as failures. Do not treat any construction as canonical | skeleton §8.1; `PRIORITIES.md` item 27 |

## Status vocabulary

The ledger's own classes, restated because they are easy to conflate with the
repository-wide epistemic classes in `AGENTS.md`.

| term | current meaning |
|---|---|
| `inherited-established` | the inherited development's own audit attests it. Carries **no** implication about the current proof stack, and none of it has been rebuilt here |
| `workspace-established` | this repository holds a statement of record meeting its verification requirements. **Nothing on this line is** — `CLAIMS.md` does not exist for it, and the registry is what a claim is |
| `architected` | precise enough to organize work. Not established |
| `open` | substantive mathematical uncertainty. Where the kind of uncertainty matters, `RESEARCH_STATE.md` has the debt vocabulary |
| `blocked` | waiting on an upstream theorem, definition, or maintainer choice |
| `maintainer-decision` | reserved. Three are live: which register the substitution separation takes, whether the settlement result is labelled enforcement or epistemic trust, and which reading of the fully-updated-deference gloss the paper claims |

## Kernel-verified and unregistered

`lean/Workspace/Deference/Contrib/` holds well over a hundred theorems that build
against the pinned toolchain and audit to the three standard axioms. **None is
registered**, so none is `workspace-established`. That second number — zero — is
the one that carries meaning, and it is the one to check; the first moves every
round. A reader who collapses the two facts will over-read the line's status by a
long way.
