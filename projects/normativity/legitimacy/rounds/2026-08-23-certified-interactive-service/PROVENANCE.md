# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `INTERACTIVE_SERVICE_INTERFACE.md`, `PRIOR_ART_EMBEDDINGS.md`, `SERVICEABILITY.md`, `HANDOFF.md`, `OPEN_QUESTIONS.md` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-certified-interactive-service/` | — |
| `src/`, `tests/` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-certified-interactive-service/` | — |
| `CERTIFICATION_CLEANUP.md`, cleanup revisions to the above files, `tests/test_timing.py` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-certified-interactive-service/PROMPT-cleanup.md` | — |
| `CLOSEOUT.md`, closeout revisions to the above files | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-certified-interactive-service/PROMPT-closeout.md` | — |

The executor worked from live `origin/main` at
`299fbd1` (merge of the transition-certificates round), in an isolated
worktree, independent of all concurrently running branches.

## External sources inspected

- Yossi Azar, Ashish Chiplunkar, Shay Kutten, and Noam Touitou, "Set
  Cover with Delay — Clairvoyance Is Not Required," ESA 2020; primary
  PDF arXiv `1807.08543v3`, Sections 1.3-3 inspected for the request,
  delay, repeated-purchase, and optional-nonservice definitions.
- Sungjin Im, Viswanath Nagarajan, and Ruben van der Zwaan, "Minimum
  Latency Submodular Cover," ACM Transactions on Algorithms 13(1);
  primary PDF arXiv `1110.2207v3`, Sections 1-1.2 inspected for the
  metric-path, cover-time, and Submodular Ranking definitions.
- Daniel Golovin and Andreas Krause, "Adaptive Submodularity: Theory
  and Applications in Active Learning and Stochastic Optimization,"
  JAIR 42 (2011); primary PDF arXiv `1003.3967v5`, Sections 2-5
  inspected for Definitions 1-3 (conditional expected marginal
  benefit, adaptive monotonicity/submodularity), Definition 7
  (coverage), Definition 8 (self-certifying), the item-cost extension,
  and the Section 3.4 boundary remarks (synergies; realization-
  altering selection).
- Andrew Guillory and Jeff Bilmes, "Interactive Submodular Set
  Cover," ICML 2010; primary PDF arXiv `1002.3345v2`, Sections 2-3.2
  inspected for the hypothesis-class, valid-response, adversarial-
  consistency, and objective/termination definitions.
- Florian Horn, Wolfgang Thomas, Nico Wallmeier, and Martin
  Zimmermann, "Optimal Strategy Synthesis for Request-Response
  Games"; primary PDF arXiv `1406.4648v1`, Sections 1-3 inspected for
  the arena and RR-condition definitions, the inductive waiting-time
  definition and its coalescing remark, the Buechi-reduction and
  memory-bound citations, and Examples 1-2 (whose value 56/10 the test
  suite reproduces exactly).

The translations, subtraction analysis, capability taxonomy, and
counterexamples are this round's derivations, not claims attributed to
those papers. The predecessor round
`projects/normativity/legitimacy/rounds/2026-08-23-afoundational-inquiry/`
(merged to `main`) is consumed only as merged history: its upstream
`DueToken` shape and its overload deadline note, which this round's
`SERVICEABILITY.md` sharpens.
