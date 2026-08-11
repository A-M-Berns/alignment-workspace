# Report — Φ-regret applicability

**Prompt author:** GPT-5.6 Sol (OpenAI) · **Executor:** GPT-5 Codex (OpenAI) ·
**Dispatched and executed:** 2026-08-11 · **Branch:**
`agent/phi-regret-applicability` from `fd844d8`

Start state: clean worktree at `fd844d8` on current `origin/main`, after PR #18's
combined integration. The prior leverage runner had 25 passing exact-rational
tests. Item 29 was the live frontier; items 30 and 31 and friction F4 were open.

## Result

**Item 29: Near miss.** Blum and Mansour (2007) Theorem 18 is the right source
theorem. Its modification rules may be fixed programs whose date-`t` maps depend
on pre-action history. That matches guarded lawful edits after a causal adapter,
under frozen filings, actual-prefix guards, no suspension, full-information
bounded charge, and a comparator class fixed before play.

The action encoding fails. Repository `Response` equality includes the
occasion-specific ledger effect, so the union of nominally eight local actions
has `N_T=3T+5`: 41, 77, 149, and 293 at horizons 12, 24, 48, and 96. Theorem
18's `O(ell_max sqrt(T N log K))` bound is then linear in `T`. A uniform
eight-label type and occasion-local decoder are missing.

The round also found that the preparation footprint did not enforce its claimed
profit separation. Guards receive schedules containing tariffs and retain a
complete history through the reader object. The theorem-facing adapter removes
future rows, accounts, service costs, and tariffs from callback arguments, but
arbitrary Python callbacks can capture the original data. The default finite
programs can be audited as profit-independent; the callback type does not enforce
it.

No learner was run. Item 30 remains blocked. Item 31 and F4 are unchanged.

## Source facts and constructed findings

**Source facts.** Blum--Mansour Theorem 18 assumes fixed finite `N`, finite rule
and selector sets, bounded full-information loss vectors, row-conditioned
weights, and a stationary distribution; it permits history-dependent
modification rules and gives `O(sqrt(T N log(MK)))`. Theorem 5 is the narrower
swap result. Gordon--Greenwald--Marks Theorem 1 uses fixed transformations on a
fixed convex compact action region and is not the better guard theorem.

**Derived interface facts.** Under frozen/no-suspension replay, the comparator
loss is additive. Finite-union/retraction padding preserves actual and transformed
loss when the union is fixed. A stationary distribution of rows landing in
`A_t` has support in `A_t`.

**Exact findings.** Ten tests check the causal argument seal, replay/additive
agreement, tariff invariance of the canonical repair, tariff capture through a
closure, raw-padding failure, retraction preservation, stationary support, and
the `3T+5` action-union counterexample.

**Conjectures.** A fixed eight-label encode/decode interface should make the
source theorem applicable to the frozen nine-program class. This has not been
implemented or proved. Whether the finite programs suffice for meaningful
coverage remains open.

## What was not shown

No fixed-`N` applicability bridge, low-regret learner, finite-time workspace
bound, asymptotic result, sampled-trajectory bound, self-correction theorem,
coverage result, or normative-correctness claim was established. The abstract
padding proof is not registered or Lean-formalized. Two of the nine specified
programs remain unimplemented. Theorem 18 controls expected mixed loss; sampled
loss would need an additional argument.

## Independent red team

The independent agent received the artifacts and audit questions without the
constructing transcript. It rejected the initial **Encoded** verdict, found
`N_T=3T+5`, and exhibited the closure-capture bypass. Both findings were added
as tests and persisted in `RED_TEAM.md`; the shared-state status was changed to
**Near miss**. No learner work from item 30 was added.

## Deviations

1. The initial positive encoding was withdrawn after red team. The final result
   is the required negative applicability result.
2. Item 29's ledger acceptance shape offered Lean proof or a house-checked
   obstruction. This round supplies an exact executable counterexample in a
   proof-layer round runner and does not register it; the report and priority row
   state that weaker evidence class explicitly.
3. The requested “independence witness” exposed a defect rather than confirming
   the preparation claim. The theorem-facing argument seal is retained with its
   callback-capture limit stated.

## Verification

- `python3 tests/run.py`: green; all four project runners pass, including the
  preparation suite and the new 10-test applicability suite.
- Gate self-tests, name lint, contributor hygiene, conservativity, sorry scan,
  axiom-discipline scan, path-pattern coverage, and checker self-test: green in
  the house runner.
- `lake build`: green, 2,641 jobs; existing deprecation and unused-argument
  warnings only.
- `python3 tests/audit_axioms.py`: green; 175 results across 12 files, all
  within `Classical.choice`, `Quot.sound`, and `propext`.
- `git diff --check`: green.

## Maintainer memo

1. **Theorem audited:** Blum--Mansour (2007) Theorem 18, with Theorem 5 and
   Gordon--Greenwald--Marks (2008) Theorem 1 as rejected alternatives.
2. **Comparator type:** fixed causal program inducing
   `F^t_phi(x_t):A_t->A_t` by guarded, per-firing certified replacement.
3. **Fixed/history-dependent:** program fixed ex ante; induced map
   history-dependent.
4. **Guards:** identity when false or uncertified; causal pre-action arguments.
5. **Action sets:** eight locally, but `3T+5` repository values globally.
6. **Replay:** frozen arrivals, actual-prefix guard, local substitutions, actual
   responses elsewhere; no-suspension is required for additivity.
7. **Loss:** exact docket charge in `[0,2]` in the frozen test.
8. **Feedback:** full counterfactual charge vector computable from schedule.
9. **Legality/profit:** defaults are invariant in the witness; arbitrary callback
   non-capture is not enforced.
10. **Lifetime influence:** bounded per firing only without the coupling or with
    bounded-lifetime fences.
11. **No-solvency-coupling:** converts replay totals to additive round losses.
12. **Direct applicability:** no.
13. **Valid encoding:** abstract padding yes; fixed-`N` repository encoding no.
14. **Best framework:** BM Theorem 18 remains closest; no replacement adopted.
15. **Red-team kills:** fixed-eight claim and callback capability claim.
16. **Item 29:** partially closed, **Near miss**.
17. **Item 30:** not ready.
18. **Item 31:** unchanged/open.
19. **F4:** consumed only through the ci-only preparation adapter; not blocking.
20. **Constructed mathematics:** exact comparator type, source mapping, additive
    boundary, abstract padding lemma, and two counterexamples.
21. **Aspirational:** sublinear regret against historically lawful repairs.
22. **Strongest philosophy:** the repairs have the right causal comparator
    shape; the online-learning synthesis is not established.
23. **Debt change:** broad applicability debt narrowed to fixed-action interface
    and callback-capability debt.
24. **Next task:** fixed eight-label action type; local decode; preservation of
    action maps, charge, and regret; full nine-program non-capture audit.
25. **Shared documents:** `RESEARCH_STATE.md` and `PRIORITIES.md` reconciled;
    `DECISIONS.md` unchanged because no human decision arose.
26. **Deference:** Stage V text and all deference artifacts untouched.
27. **Maintainer decisions:** none added; existing queue preserved.
28. **Human review surfaces:** the taxonomy verdict, the choice to accept a
    finite program audit versus require a declarative rule language, and the
    unregistered evidence strength.
29. **PR:** recorded after creation.

## Outstanding maintainer actions

None created by this round.
