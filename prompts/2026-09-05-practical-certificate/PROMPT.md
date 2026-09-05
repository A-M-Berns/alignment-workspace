# Common brief for every worker in the 2026-09-05 integrity research batch

You are one of five isolated research workers dispatched by an orchestrator against
`A-M-Berns/alignment-workspace` at `main` = `5ff9539b44debc464128e6a1921ef1690f7b6487`.
You are running in your own git worktree (the Agent tool created it from that `main`);
verify with `git log --oneline -1` and record any difference in your report rather than
forcing it. Work only inside your worktree directory. Never `cd` into the main checkout
or another worktree.

## Read first, in this order

1. `AGENTS.md` — binding. Exact `fractions.Fraction` arithmetic; a theorem ships as
   statement + implementation + test + necessity witnesses where feasible; Lean is
   sorry-free with `#print axioms` on everything, auditing to
   `[propext, Classical.choice, Quot.sound]` and nothing else; **external theory enters as
   named hypotheses of the statement that uses it, never as `axiom` declarations**; names
   you coin are provisional and listed; deviations from this prompt are declared in your
   REPORT with reasons; the REPORT states what was NOT shown; slop discipline (every
   sentence does work; no summary of a summary; no compliance narration); no negative
   ontologies in living documents (your round directory is a completed-round record, so it
   may narrate its own history, but do not write "formerly X" prose into any file outside
   it).
2. `python3 -m checkers.workspace_state --json` — orientation; do not infer current status
   from completed-round prose.
3. `DECISIONS.md` (the *Awaiting the author* queue and the entries dated 2026-09-01 through
   2026-09-05), `PRIORITIES.md` items 74–77, `RESEARCH_STATE.md`.
4. The wiki pages `wiki/Legitimacy.md`, `wiki/Integrity.md`, `wiki/Settlement-Interface.md`,
   `wiki/Diachronic-Answerability.md`, `wiki/Openness-Coverage-and-Non-Capture.md`,
   `wiki/Normative-Induction.md`, `wiki/Normative-Inductor.md`, `wiki/Roadmap.md`. The
   wiki is permitted as conceptual orientation for this dispatch. **It is not proof
   evidence, and you must not edit it.**
5. The landed rounds relevant to your lane, cited by path below. Their `THEOREMS.md`,
   `README.md`, `REPORT.md` and Lean are evidence; their epistemic class is what their
   own ledgers say (almost everything is paper-derived + exact fixtures = at best
   `test-supported`; kernel-checked declarations are named where they occur).

Key paths:

- Lean spine of the history/defeat theory: `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`
  (§4 settlement, §5 unified grounds / answerable defeat / standing / witnesses).
- Realization bridge lemmas: `lean/Workspace/Normativity/Contrib/NormativeInductor.lean`.
- Rounds under `projects/normativity/legitimacy/rounds/`:
  `2026-08-29-normative-continuity-concordance`, `2026-08-30-normative-continuity-settlement`
  (`SETTLEMENT.md`, `THEOREM_MAP.md`, the `.tex`), `2026-08-30-answerability-carriers`
  (`ANSWERABILITY_CONSERVATION.md`, `TERMINAL_EXITS.md`, `TRANSFER_SEMANTICS.md`),
  `2026-08-30-anchored-slices-auth-transfer` (`ANCHORED_SLICES.md`,
  `SEMANTIC_AUTHENTICATION.md`, `TRANSFER_COMPOSITION.md`),
  `2026-08-31-faithful-semantic-preservation` (`NO_SEMANTIC_LAUNDERING.md`,
  `FAITHFUL_AUTHENTICATION.md`, `REPAIRED_CONSERVATION.md`),
  `2026-08-23-transition-certificates` (`MEMO.md`), `2026-08-30-proper-exercise-calculus`,
  `2026-08-30-cf-coverage-continuity-interface` (`COVERAGE_CONTRACTS.md`,
  `INTERACTION_INTERFACE.md`, `SELF_SEALING.md`), `2026-08-25-carroll-legitimacy-test`
  (`CRITERION.md`), `2026-09-02-unified-grounds-answerable-defeat` (`GROUNDS.md`,
  `DEFEAT.md`, `THEOREMS.md`), `2026-09-03-defeat-landing-horty-standing`
  (`STANDING_REPAIR.md`, `WITNESS.md`, `HORTY.md`),
  `2026-09-04-normative-inductor-realization` (`NORMATIVE_INDUCTOR_REALIZATION.md`,
  `PRESENTATION_AND_VALUE_SEMANTICS.md`, `THEOREMS.md`),
  `2026-08-31-normative-affordability` (`SHARP_TIMELY_SERVICE.md`, `SERVICE_TRANSFER.md`,
  `SERVICE_FORCE_TYPING.md`), and the checkpoint
  `projects/normativity/legitimacy/checkpoint-2026-09-01/` (`CURRENT_THEORY.md`,
  `STATUS_LEDGER.md`, `OPEN_PROBLEMS.md`) which is `agent-consolidated` and must not be
  edited.
- Program prior art: `projects/normativity/notes/PRIOR_ART.md`.

## Shared orientation (hold with the stated status)

Fairly settled: legitimacy is a property of cognitive *evolution*, not certification of a
state. The proof-relevant object is a history segment `H_{m:n}`; the consumer-facing
object is likely an endpoint relation `H_m ⪯_leg H_n` witnessed by a legitimate segment.
Declared normative scope is application-relative. Integrity (did the trajectory
faithfully preserve and account for what entered it?) is distinct from Non-Capture (could
the process improperly determine what was able to enter, challenge, or evaluate it?).
Non-Capture and counterfactual practical/value semantics are billed to external theories:
the generic theory specifies the certificate and proves what follows.

Working hypothesis to TEST, not doctrine: **Trajectory Integrity ⇒ Diachronic
Answerability.** Do not assume it by definition.

Settlement distinction to test: an external settlement item `s ∈ SetView(H_n)` is an
authenticated input through the declared trusted settlement boundary. The internal
reasoner separately judges `Closes(H_n, s, α)` — by the rules/reasons legitimately in
force at `H_n`, `s` suffices to close obligation `α`. A discharge is backed by (1)
authenticated availability of `s`, (2) an internally valid `Closes` certificate, (3)
whatever authority/provenance Integrity requires. Settlement items do not arrive typed as
"settles α"; they may stay immutable while their judged relevance changes; a later
reasoner may find an earlier `Closes` defective, and the response is probably a new
reopening/reconsideration obligation, not retroactive rewriting. The settlement trust
boundary is domain-relative; do not force one universal settlement ontology.

## Isolation

You do not know what the other four workers are doing beyond their one-line lane names
(A: constructive Integrity theory; B: Integrity adversary / laundering audit; C:
Non-Capture certificate minimization; D: practical-semantics certificate minimization;
E: end-to-end Normative Inductor gap audit). Do not coordinate with them, do not read
other worktrees, and do not adopt definitions you have not derived or cited from `main`.

## What you may and may not touch

You MAY create, in your worktree only:

- `projects/normativity/legitimacy/rounds/2026-09-05-<your-round-name>/` with
  `README.md` (verdict, one paragraph), `REPORT.md` (concise; verdict line verbatim as in
  README; a *Deviations* section; a *What this does not establish* section; a
  *Proposed filings* section listing anything that would need `PRIORITIES.md`,
  `DECISIONS.md`, `state/`, or vocabulary changes — you do NOT make those changes; an
  *Attribution* block: prompt author = the orchestrator (Claude Fable 5.1, Anthropic,
  relaying a maintainer dispatch), executor = your model name), `PROVENANCE.md` (one row
  per file/glob: generator, review status `ci-only`, date 2026-09-05, originating round
  `prompts/2026-09-05-<your-round-name>/`), theorem/countermodel ledgers, `src/` and
  `tests/run.py` (self-contained runner; `python3 tests/run.py` must exit 0; exact
  `Fraction` arithmetic), and Lean under `lean/Workspace/Normativity/Contrib/` in a NEW
  file with a NEW namespace (do not edit existing Lean files; if a result needs a
  definition from an existing file, import it).
- `prompts/2026-09-05-<your-round-name>/PROMPT.md` — the prompt you were given, verbatim
  (this whole brief plus your lane section), and `REPORT.md` as a copy or pointer.

You may NOT edit: `wiki/**`, `DECISIONS.md`, `PRIORITIES.md`, `PROVENANCE.md` at root,
`state/**`, `checkers/**`, `tests/**` at root, `.github/**`, any `agent-consolidated`
tree (`projects/normativity/legitimacy/checkpoint-2026-09-01/`,
`projects/normativity/consolidation-aug9/`), any existing round directory, or any
existing Lean file. The orchestrator makes shared-register changes centrally. If your
work needs one, write it under *Proposed filings* in your REPORT.

## Machine discipline (several agents share one 24 GB, 10-core Mac)

- Before any Lean build or other long job run `~/.claude/scripts/resource-guard.sh check`;
  if it exits non-zero run `~/.claude/scripts/resource-guard.sh wait 900` and try again.
- **Never call `lake` directly.** Use `~/.claude/scripts/safe-lake.sh build <Module.Name>`
  from the `lean/` directory of YOUR worktree. Build only your own module and the ones it
  imports; never a bare `lake build` of everything.
- Before the first Lean build, make the shared Mathlib cache available with
  `ln -s /Users/anson/Projects/alignment-workspace/lean/.lake lean/.lake` (run from your
  worktree root). That path is git-ignored; confirm `git status --short` does not list
  `lean/.lake` afterwards. Do not copy the cache and do not run `lake exe cache get`.
- Python is cheap; run only your own `tests/run.py` plus `python3 tests/name_lint.py`,
  `python3 tests/dead_pointers.py`, and `python3 tests/untracked_pointers.py` at the end.
  Do not run the repository-wide `python3 tests/run.py` more than once, at the end.
- If the guard keeps reporting LOADED, wait rather than pushing through, and say so in the
  report.

## Evidence discipline

Label every result exactly one of: `lean-proved` (kernel-checked, axioms audited),
`exact-witness` (a finite instance computed in exact rationals, which is NOT a proof of a
general statement), `paper-derived`, `proposed definition/interface`, `ambient
assumption`, `open`. A finite fixture pins an instance; never write "verified" for a
general theorem it only instantiates. Necessity witnesses for hypotheses where feasible;
where not feasible, say so.

## Prose discipline

Dry, exact, short. Definitions, statements, proofs or proof sketches, countermodels,
what is not shown. No roadmap prose, no philosophical positioning beyond what the result
means for the question under test, no praise of your own care. Your REPORT should be the
length the content needs, typically 100–250 lines. The `README.md` verdict is one
`UPPER-CASE-HYPHENATED-VERDICT — one-sentence gloss` line followed by a reading order.

## Finish

1. `python3 tests/run.py` in your round directory exits 0; each Lean file you added builds
   via safe-lake and every declaration's `#print axioms` line shows only the three
   allowed axioms; `python3 tests/name_lint.py`, `python3 tests/dead_pointers.py`,
   `python3 tests/untracked_pointers.py` pass from the worktree root (the last one will
   complain that your new paths are uncommitted until you commit — commit first).
2. Rename your branch in place to `round/2026-09-05-<your-round-name>` with
   `git branch -m` (do not create a second branch), commit with `git commit -s` and a
   message ending in the trailer line `Model: <your model family and version> (<provider>)`
   — no other trailers, no co-author lines — and push with
   `git push -u origin round/2026-09-05-<your-round-name>`. Do NOT open a pull request and
   do NOT merge anything.
3. Your final message to the orchestrator: the branch name and head SHA; the round
   directory path; the verdict line; then a compact structured summary (at most ~60 lines)
   of your definitions, theorems with evidence labels, countermodels, and open questions —
   written so a reader who has not opened your files can cross-examine it. Include verbatim
   the two or three definitions another worker would need in order to attack them.

# Your lane: Agent D — practical / counterfactual semantics certificate minimization

Round name: `2026-09-05-practical-certificate`. Branch: `round/2026-09-05-practical-certificate`.

You are an interface-minimization worker. Do not solve general counterfactual
identification.

Problem: **determine the weakest practical-semantics certificate the abstract Normative
Induction theorem needs, and which factorizations are merely convenient realizations.**

The public endpoint is, schematically,
`PracticalCert(e, s) : E[ℓ_e(Y_s)] ≤ M_es · d_s + ε_es`
— the anchored loss of exposure `e` under the response realized at service occurrence `s`
is controlled by the public operative defect `d_s` with per-edge constants. Do not assume
scalar counterfactual value vectors are the definition of practical semantics.

The Normative Inductor round's value-correspondence path is one sufficient factorization:
authenticated counterfactual semantics → value calibration/ambiguity `(V_es, v*_es, ζ_es)`
→ randomized `η`-approximate decision rule → decision regret `≤ 2d_s + 2ζ_es + η_s` →
anchored response adequacy `(L_es, ε^resp_es)` → `M_es = 2L_es`,
`ε_es = L_es(2ζ_es + η_s) + ε^resp_es`. Read that round's `PRESENTATION_AND_VALUE_SEMANTICS.md`
§§4–8, `NORMATIVE_INDUCTOR_REALIZATION.md` §6 and §13, and the Lean lemmas
`approximate_argmax_transfer`, `randomized_approximate_argmax_transfer`,
`calibration_through_value_correspondence`, `practical_response_compose` in
`lean/Workspace/Normativity/Contrib/NormativeInductor.lean`.

Test whether that factorization is minimal; unnecessarily strong; appropriate only for
utility-like domains. Find other direct sufficient routes if natural — especially for
procedural, constraint-like, rights-like, or non-scalar obligations (e.g. an obligation
whose adequate response is "produce a receipt of kind X within H steps", or "do not take
actions in a forbidden set", where no value vector is the natural object). For each route
state the certificate it needs from an external theory and prove (paper, plus Lean where the
step is algebra) that it yields `PracticalCert`.

Press on **joint practical-response compatibility**: one service occurrence `s` produces
one realized response distribution `Π_s`; if several exposures `e` are matched to `s`,
each edge certificate must hold against that same `Π_s`. Characterize the weakest useful
bundle-level or edge-level condition ensuring this. Exhibit, as an exact fixture, two
exposures inside one jointly feasible region `K_s` with no common adequate response.
Classify the legitimate outcomes of incompatibility — distinct service contexts;
upstream licensed adjudication/aggregation; a common adequate response; residual mass —
and state, for each, exactly what the transport plan / admissible-edge relation must
record so the Progress bound's accounting stays honest. Do not let joint price-space
feasibility stand in for practical compatibility.

Deliverables: `CERTIFICATE.md` (the minimal public certificate and what it quantifies
over), `FACTORIZATIONS.md` (the value-correspondence route and at least one non-scalar
route, each with its external bill), `NECESSITY.md` (counterexamples showing each retained
clause is needed and which strengthenings are unnecessary), `JOINT_COMPATIBILITY.md`,
`THEOREMS.md` with evidence labels, exact fixtures under `src/` + `tests/run.py`, Lean
algebra in a new file / namespace if any step is naturally algebraic (import
`NormativeInductor` rather than restating its lemmas), `REPORT.md`. Relate every constant
to the existing `M_es`, `ε_es` of the realization round.
