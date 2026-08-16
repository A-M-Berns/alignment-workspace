# Path inventory

Everything between the repository and a paper-level normative-learning theorem,
with a status per item. Statuses: `DONE`, `FIXTURE-ONLY`, `PARTIAL`, `OPEN`,
`BLOCKING`, `OPTIONAL-STRENGTHENING`.

`BLOCKING` means the flagship theorem cannot be stated without it.

---

## A. Shared normative representation

| item | status | note |
|---|---|---|
| perspectival commitment attribution | `DONE` | merged round; `commitments_i(j)` |
| commitment / entitlement separation | `DONE` | merged refinement; separate relations |
| exposed due burdens | `DONE` | `exposures`; what makes a consequence chargeable |
| challenge force derived from entitled incompatibility | `DONE` | |
| suspension distinct from retraction | `DONE` | merged refinement |
| reified applicability | `DONE` | a content, no machinery |
| protection against unilateral self-release | `DONE` | enumerated edit class |
| protection against coordinated drift | `OPEN` | two scorekeepers revising together dissolve a burden |

## B. Theorem-facing loss

| item | status | note |
|---|---|---|
| boundedness | `DONE` | `2·\|contents\|` |
| prospectivity — `ell_t` fixed before the action | `DONE` | tested directly |
| self-laundering resistance | `DONE` | exact edit class |
| exposure gating | `DONE` | avoids logical omniscience |
| parameterization over an arbitrary bounded generator | `OPEN` | the loss is one concrete defect count; the interface note already asks for this |
| dependence on one scorekeeper vs many | `OPEN` | the loss reads a single critic `C` |

## C. Normative compiler

| item | status | note |
|---|---|---|
| public certificates as data | `DONE` | strings, evaluated against status |
| loss-blindness | `DONE` | one lawful repair worsens the loss |
| causality — strict-prefix inputs only | `DONE` | |
| source-action-specific repair compilation | `DONE` | this round |
| compiler soundness theorem | `OPEN` | no statement that a certificate's presence *implies* the repair is normatively right |

## D. Online-learning engine

| item | status | note |
|---|---|---|
| fixed finite action type | `DONE` | eight labels |
| source theorem applies to a **history-dependent** rule | `DONE` | source definition, quoted |
| source theorem applies to a **history-dependent selector** | `DONE` | source footnote 1 |
| source theorem applies to an **endogenous, adaptive** loss process | `DONE` | pathwise proof; corrects a prior reading |
| existing learner runs on that process | `DONE` | `run_learner` |
| learner exhibits mass-shedding dynamics | `OPEN`, and structurally so | the targeted actions are transient under any class of genuine repairs, so the stationary construction gives them zero mass at every date; `PROSECUTION.md` §1 |
| regret measured against the `O(√(TN log K))` bound | `OPEN` | never measured |
| anytime tuning / doubling | `OPEN` | source tunes `β` from `T` |
| computation cost of the learner priced | `OPEN` | carried from the interface note |

## E. Pattern-elimination theorem

| item | status | note |
|---|---|---|
| abstract repair lower bound `R_T(g) ≥ δ·Q_T` | `DONE` | derived, replay-free |
| surgical shape shown necessary | `FIXTURE-ONLY` | cancellation witness |
| exact instantiation at four horizons | `FIXTURE-ONLY` | equality throughout |
| `E[N_T] = Q_T` | `DONE` | one line |
| pathwise `N_T/T → 0` | `OPEN` | needs concentration |
| Lean port of the lower bound derivation | `OPEN` | existing lemma assumes the bound; this would derive it |

## F. Inquiry / coverage

| item | status | note |
|---|---|---|
| exposure as a state coordinate | `DONE` | |
| a coverage condition | `BLOCKING` | nothing forces relevant reasons to be raised |
| prevention of avoidance-by-never-asking | `BLOCKING` | a learner never asked has `Q_T = 0` free |
| service / deadline structure | `OPEN` | `exposures` has no ordering or deadlines |
| corrigibility as a coverage mechanism | `OPEN` | shape match only; no theorem |

## G. Comparator expressivity

| item | status | note |
|---|---|---|
| finite declarative programs | `DONE` | nine broad, four surgical |
| source-action-specific variants | `DONE` | this round |
| richer generated grammar | `BLOCKING` | four hand-chosen rules are not a repair language |
| complexity model for the class | `OPEN` | cardinality, description length, prior — unchosen |
| coverage theorem for the language | `OPEN` | or an explicit stated limitation |
| **recurrence adequacy** | `OPEN`, newly identified | a repair class whose rules all point away from mistakes makes every targeted action transient, so the pattern-elimination conclusion is vacuous for exactly the patterns the class was built to address. Any generated grammar has to be checked against this, and a naive "collect the repairs" construction fails it |

## H. Diachronic / ontology

| item | status | note |
|---|---|---|
| ordinary persistence derived | `DONE` | |
| vocabulary migration needs transport | `OPEN` | merged round |
| whether migration disturbs theorem-facing selectors | `OPEN` | a selector names a status; what it refers to across migration is unexamined |

## I. Interpretation

| item | status | note |
|---|---|---|
| what "improvement" means | `PARTIAL` | response-to-reasons; contested in `PROSECUTION.md` §4 |
| no target normative truth | `DONE` | no oracle field |
| no convergence to a unique norm | `DONE` | |
| disagreement may persist | `DONE` | two-way entitled challenges |
| reasons persist while bad responses vanish | `DONE` | the selector fires at every date while `Q_T` is controlled |

## J. The stronger optional theorem

| item | status | note |
|---|---|---|
| replay / policy regret | `OPTIONAL-STRENGTHENING` | **not** required for Claim A |
| counterfactual trajectory domination | `OPTIONAL-STRENGTHENING` | strictly stronger; blocked for the additive reduction |
| structural assumptions a policy-regret route would need | `OPEN` | not investigated — §XIII of the dispatch is diagnostic and the primary branch did not fail |

---

## The three blocking items

Everything else is work. These three stand between the current state and a
flagship theorem:

1. **A coverage condition** (F). Without it the theorem is conditional on being
   asked, and a learner can satisfy it by arranging to be asked nothing.
2. **A repair language** (G), and it now carries a second constraint nobody had
   articulated. Beyond covering the repairs a practice needs, a class must not
   make its own targets transient, or its conclusions are vacuous for precisely
   the patterns it addresses.
3. **A compiler soundness statement** (C). Certificates are currently a discipline
   the round imposes, with no statement connecting a certificate's presence to the
   repair being normatively appropriate.

The first two are what stop the current mathematics from being a normative-learning
theorem as opposed to a correct regret instantiation. The third is what would make
the word "lawful" carry weight rather than name a convention.

## Suggested sequencing

Coverage first: it is `BLOCKING`, it is where the merged corrigibility work may
compose, and it decides whether the exposure gate is a repair or a hole. Then the
repair language, since its shape depends on what coverage turns out to demand. The
Lean port of §E is short, independent, and can happen at any point.
