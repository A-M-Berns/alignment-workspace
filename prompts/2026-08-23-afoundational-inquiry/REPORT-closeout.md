# Closeout report

**Attribution.** Prompt author: user, model not stated. Executor: GPT-5.6 Sol
(OpenAI). Dispatched and executed 2026-08-23 against PR #47.

## Scope and result

This was a closeout pass on the existing afoundational-inquiry round, not a new
research round. It repaired the finite authority witness, made the scheduler
bridge checks independent finite comparisons, and aligned the repository and
wiki calibration. No registered claim, theorem-facing interface, priority, or
counterfactual-legitimacy artifact changed.

## Repairs

1. `authority_roots` now validates the strict pre-state record first and uses an
   expanded-node set only to avoid repeated traversal. Shared ancestors and
   diamond DAGs are accepted; repeated roots are deduplicated. Same-index mutual
   ancestry fails closed under the pre-state validator.
2. Inquiry-side and translated Set Cover with Delay objectives are implemented
   separately and compared on overlapping, repeated-purchase, delayed-arrival
   examples. Inquiry latency and unit-metric MLSC objectives are likewise
   implemented separately and compared on multiple orderings.
3. The current `Root`/`Undertake`/`Account` typing is described as insufficient
   for the information used by this implementation. The stronger question of a
   semantics-preserving smaller event calculus remains open. Due-token
   distinctness is operational under the tested representation, not an
   impossibility theorem about all representations.
4. `S_0` is explicitly only the positive model's initialization interface. A
   possible factorization `I_0 --Uptake--> R_0` and the normative content of
   uptake remain open. The checker-boundary primitive-expenditure warning is
   preserved.
5. Incorrect expanded links for the base commit were corrected to
   `e5de4b9c03730961154eec555153a59ec3e7462a`.

## Verification

- The afoundational-inquiry suite passes 26 tests.
- All seven relevant legitimacy suites pass, 381 tests in total.
- `python3 tests/run.py` passes all repository gates and 17 project runners.
- Structured workspace state, wiki links, wiki state bindings, and diff
  whitespace checks pass.
- No registered claim file changed relative to `origin/main`.

## Deviations

No stronger research result was attempted. In accordance with `AGENTS.md`, this
closeout prompt is preserved verbatim beside the original round prompt and this
report is added beside the original report. No Lean artifact or new round was
created because the dispatch expressly excluded both and no claim was promoted.

## What was not shown

Independent finite objective computations are sanity witnesses for the paper
translations, not general machine-checked reduction theorems. The pass does not
prove event-calculus minimality, explain normative bootstrapping beneath `S_0`,
construct `R -> O`, establish non-capture, or alter downstream enforcement.

## Outstanding maintainer actions

None. PR description update, CI observation, and merge are executor closeout
actions rather than reserved research decisions.
