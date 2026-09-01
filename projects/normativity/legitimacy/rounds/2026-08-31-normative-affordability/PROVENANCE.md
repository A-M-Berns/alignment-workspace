# Provenance

| file or glob | generator | review status | date |
|---|---|---|---|
| `*.md`, `src/**`, `tests/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-31 |

`FOLLOWUP_REPORT.md`, `CORRECTED_STACK.md`, `src/li_account.py` and
`tests/test_li_account.py` are the second dispatch's; the corrections it applied to
the first dispatch's documents are listed in `FOLLOWUP_REPORT.md`.
`SERVICE_FORCE_TYPING.md`, `LI_PROGRESS_FROM_SERVICE.md`, `END_TO_END_LEARNER.md`,
`src/service.py` and `tests/test_service.py` are the third dispatch's, which
withdraws the second's identification of the service variable with the realized
position magnitude and corrects it in place. `REASONWISE_ACCOUNTING.md`,
`CAPACITY_VS_SAFETY.md`, `FIXED_ERA_THEOREM.md`, `AFFORDABLE_SCHEDULING.md`,
`src/reasonwise.py` and `tests/test_reasonwise.py` are the fourth dispatch's, which
repairs the third's reason-indexed statement and its convexity claim about the
per-date capacity region. `PERSISTENT_AFFORDABILITY.md`, `CAUSAL_CAPACITY.md`,
`SIGNED_VS_CONSERVATIVE.md`, `ONLINE_EXISTENCE.md`, `OVERLOAD_TARGET.md`,
`src/persistence.py` and `tests/test_persistence.py` are the fifth dispatch's, which
withdraws the fourth's sustainable authority-rate region and its convexity, and
freezes the fixed-era composition. `SHARP_PERSISTENCE.md`,
`SERVICE_ADMISSIBLE_EXISTENCE.md`, `CLOSED_LOOP_EXISTENCE.md`, `src/sharp_cost.py`
and `tests/test_sharp_cost.py` are the sixth dispatch's, which withdraws the fifth's
claim that the sharp charge leaves the criterion unchanged and its online
competitive-ratio claim, and narrows its rate-region non-convexity to the
finite-horizon frontier. `BOUNDED_DELAY_TRANSPORT.md`,
`BOUNDED_DELAY_AFFORDABILITY.md`, `SERVICEABILITY_FRONTIER.md`,
`MULTIREASON_SERVICEABILITY.md`, `ONLINE_SERVICEABILITY.md`,
`src/bounded_delay.py` and `tests/test_bounded_delay.py` are the seventh
dispatch's, which supersedes the sixth's disjoint-window service condition and its
depth-only reading of the sharp criterion. `SHARP_SERVICEABILITY.md`,
`EVENTUAL_VS_UNIFORM_SERVICE.md`, `JOINT_SERVICEABILITY.md`, `src/joint_service.py`
and `tests/test_joint_service.py` are the eighth dispatch's, which corrects the
seventh's batching hypotheses and its reading of the unbounded-delay limit, and
shows the settlement-friction residual is paid for by the liability budget on the
sharp charge's linear branch. `SHARP_TIMELY_SERVICE.md`, `DEADLINE_INSOLVENCY.md`,
`CONSISTENCY_AUDIT.md`, `src/timely.py` and `tests/test_timely.py` are the ninth
dispatch's, which withdraws the eighth's separation between persistence and eventual
full service and its bounded-gap shortcut, normalizes the transport residual by claim
mass, supplies the nested-assessment hypothesis the friction-free theorem needs, and
assembles the round's canonical Sharp Timely Service theorem.

The round starts from `main` at
`292bb2731b0df09aa034ca4abc5ce64a20a41785`. It reads and does not modify:

- `projects/normativity/legitimacy/rounds/2026-08-30-progress-consolidation/`,
  for the merged Progress schematic, Surface Fairness and the four Persistent
  Relevance interfaces;
- `projects/normativity/legitimacy/rounds/2026-08-30-liability-theory/`, for the
  Common-Mixture bound, the liability regimes and covered-compatibility duality;
- `projects/normativity/legitimacy/rounds/2026-08-30-progress-liability-hard-pass/`,
  for the authority portfolio and the preservation obligation;
- `projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`, for the compiled
  position, the conformance guarantee, the deficit and support liability routes,
  the preservation theorem and the conformance/liability trade equation;
- `projects/normativity/rounds/2026-08-16-traderized-enforcement/CORE_CONDITION.md`,
  for the depth condition and its compiled row; `MODEL.md` for the priced fragment,
  the compiled position, its legality audit and the statement that the enforcement
  trader is exempt from the criterion's quantifier; `FUNDING_AND_SAFETY.md` for the
  liability identity, the world-inclusive corollary, the preservation theorem and
  its market-maker step, the corrected declared-quantity ceiling, and the
  safe-without-world-inclusiveness trajectory; `NORMATIVE_SAFETY.md` §9 and §13 for
  the affordability relation, the withdrawn depth-only impossibility theorem and
  the conservatism of the per-date certificate; `ENFORCEMENT.md` §§1-3 for the
  extremal pinning lemma, the enforcement inequality, the per-date modulus
  `sum_j beta_j g_j^2 <= eps_n + M_n` and the statement that intensities are fixed
  before the market maker picks a price;
- `projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md`, an
  `agent-consolidated` tree, for no-claw-back, the two polytopes, clauses `J3`,
  `P1`, `P2`, `P4` and the assumed residues.

Every external statement is cited by content read in this tree, not by remembered
label. No claim is registered, no Lean is written, no settled definition is
changed, and no prior round's artifact is edited.

The mathematics is this round's own: the transfer and transport theorems, the
contiguity characterizations, the interference and vanishing-share countermodels,
the common-region composition, the non-revocation theorem, the drift sketch, the
overload certificate, and the score and misfit identities are derived here rather
than imported. The score identity and the friction inequality reproduce, from the
projection geometry, a bound the traderized force interface already records as its
deficit route; that agreement is a check, not a citation.

No originating chat bundle exists.
