# Report — crown-jewel refinement pass

**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Dates:** dispatched and executed 2026-08-13
**Primary verdict:** `CROWN-JEWEL-THEOREM-POSITIVE-WITH-INTERFACE-HYPOTHESES`
**Dynamics verdict:** `BM-DYNAMICS-CONDITIONALLY-POSITIVE`

The round's documents carry the results. This answers §XIX's twenty questions and
records what belongs to the pass.

## The correction that matters

**A claim from the first pass is withdrawn.** It said a normatively coherent
repair class always leaves its targets transient, so the construction always
complies immediately. The argument was that a return route would have to say
"there is an exposed burden, so having acknowledged, stop acknowledging".

That inference was invalid: a return route need not be licensed by the *same*
reason. `src/competing.py` builds one from `defeated_applicability` — ordinary
caution about not compounding an outstanding incoherence — which holds
simultaneously with `exposed_consequential_burden` in a single public state. Both
certificates already existed in the merged model. There `hold` is recurrent.

Decisively, `INCOHERENT` and `COMPETING` produce the same graph, so **recurrence
is no evidence of incoherence** and the inference cannot be run in either
direction. What survives is the graph condition alone.

## §XIX, answered

**1.** In `CROWN_JEWEL_THEOREM.md`, now with registers, information order, and
exact counts.

**2. Pathwise over mixed actions, primarily.** Theorem 18's proof and the surgical
lemma are both pathwise in the realized `(p^t, ell_t)` sequence, so
`Q_T <= B_T/delta` holds on each history. Sampling is a separate, weaker corollary.

**3.** `M_T`, `Q_T`, `N_T` are `H_t`-measurable sums, all **random** under
sampling; `R_T` is the mixed-action regret against the same date's loss vector.
Definitions displayed in the theorem document.

**4.** `E[N_T] = E[Q_T]`. The first pass wrote `E[N_T] = Q_T`, which is ill-typed
because `Q_T` is random. `N_T - Q_T` is a sum of martingale differences with
conditional mean zero; checked empirically over 200 sampled trajectories.

**5.** The history, and its own weights. `prepare` receives the maps only;
`ell_t` enters at `update`. So `ell_t` is *determined* when the date opens
(prospectivity) and *not read* when `p^t` is chosen — two claims the first pass
ran together.

**6.** `O(L sqrt(T |A| log (M K_eff)))` with `M = 1` and **`K_eff = K + 1`**: the
repairs plus the identity, which the implementation passes as its first map.
`log K` undercounts by one rule.

**7.** State coverage against the **learning scale** rather than against `B_T`, so
the hypothesis does not mention the learner's output and non-circularity is
checkable by inspection.

**8.** `M_T >> sqrt(T)` is the simplified reading. The exact condition carries
`|A|` and `K_eff`.

**9. One-way repair graphs.** Not coherent repair languages — that is the
withdrawal.

**10. Yes.** Constructed, from two pre-existing certificates.

**11. Undecided, and not for the reason first given.** Under `COMPETING` the
learner *does* start with mass on the target (`p_1 = 1/8`), passing clause (1)
which the first pass called unreachable. Clause (5) fails: the fixture's finite
content set exhausts, the margin is positive on only 4–5 of 48 dates, and the
reason stops recurring. The blocker is the fixture, not the learner.

**12. No.** Levels 0–2 are indifferent to it.

**13.** Derived for the acknowledge schema under a public side condition;
hypothesis for the rest, with a lawful margin `-2` repair kept to keep licence and
performance apart.

**14.** `COMPILER_SOUNDNESS.md`: seven clauses, four already delivered by the
substrate, three genuine interfaces — reason-connection, scope-correctness,
defeater-respect. Reason-connection is the hard one and is where the difference
between normative learning and tidy loss reduction lives.

**15. Two of the three.** Coverage and repair-language adequacy are legitimate
theorem hypotheses, not holes; only compiler soundness blocks the *abstract*
statement, because H4 quantifies over a *certified* family and `certified` must
mean more than "a string is present". `PATH_INVENTORY.md` is recategorised.

**16.** The exact quantifier interface is displayed in `COVERAGE_INTERFACE.md`:
for every advisor policy, a principal strategy forcing `M_T(g) >= m_g(T)` on every
trajectory, with `m_g` outgrowing the learning scale. Four distinct notions are
separated — ability, opportunity, exercise, service — and only the first is
established.

**17. Yes**, strictly optional and refuted as a target.

**18.** `Normative response-learning theorem` for levels 0–2. Not
`diachronic normative-learning theorem`, which needs level 6.

**19.** In `PATH_INVENTORY.md` under the sharpened categories.

**20. Not yet.** One item blocks the abstract theorem, and it is small and
well-specified. Merging before it is settled would put a theorem in the record
whose central hypothesis quantifies over a label.

## What this pass added

- The stochastic register, with a sampled learner and 200-trajectory checks.
- The information-order audit, checked against the implementation.
- `K_eff = K + 1`, stated exactly.
- Coverage restated against the learning scale, and layered into pathwise /
  expected / high-probability / policy-robust.
- The competing-reasons construction and the withdrawal.
- Full-graph dependence: bounds are modular, dynamics are not.
- `COMPILER_SOUNDNESS.md`.
- **Lean.** `SurgicalRepairBound.lean` kernel-checks the bridge.

## Lean status

Done, after two concrete failures worth recording. `Mathlib.Algebra.BigOperators.Order`
does not exist at the pinned revision — the module is
`Mathlib.Algebra.Order.BigOperators.Group.Finset`, with `Finset.mul_sum` in
`Mathlib.Algebra.BigOperators.Ring.Finset`. And `div_le_div_iff` is not available
under that name; `gcongr` after a `field_simp` split avoids the lemma-name
question entirely.

A third failure was mine rather than the toolchain's: the necessity witness had
`B = -1` with `delta = -1`, making `B/delta = 1` and the conclusion *true*, so the
negation could not be proved. `B = 0` gives the intended failure.

Full build green, `audit_axioms` reports 327 results across 16 files all within
`[propext, Classical.choice, Quot.sound]`.

## Deviations from the dispatch

1. **§VIII's pre-registered dynamics run reaches clause (1) and stops.** Clauses
   (4) and (5) could not be evaluated because the fixture cannot sustain a
   positive margin. Recorded as undecided rather than as a negative, since a
   negative would attribute a fixture limit to the engine.
2. **§XII's `E[N_T/M_T ; M_T>0]` and high-probability variants were not
   constructed.** The pass establishes `E[N_T] = E[Q_T]` and the martingale
   structure, and declines the conditional-expectation forms rather than
   inventing one.
3. **No alternative learner was sought.** §XII conditions it on the diachronic
   notion mattering *and* the current engine failing; the engine's failure is now
   attributed to the fixture, so the antecedent is not met.

## What this pass does not establish

- Compiler soundness: the signature and clause list, not a theorem.
- Coverage: an interface with an exact quantifier structure, not a proof, and the
  corrigibility composition remains a shape match missing an exercise rate.
- The dynamics question, per §XIX.11.
- Repair-language adequacy, and the recurrence check a grammar would need.
- Concentration, anytime tuning, computation cost, multi-scorekeeper aggregation,
  ontology migration.
- The reducible-chain observation remains about this implementation's stationary
  solver rather than about Theorem 18.

## New names introduced

All **provisional**, new in this pass: `competing certified reasons`,
`return route`, `learning scale`, `compiler soundness`, `reason-connection`.
Retained from the first pass: `answerability process`, `certified surgical
repair`, `conditional bad-response rate`, `margin-certified repair`,
`recurrence adequacy`. Lean declarations are named provisionally per standard 6.

## Structural defects found

None.

## Outstanding maintainer actions

Nothing is reserved. No `PRIORITIES.md` item filed, nothing appended to
`DECISIONS.md`, no claim registered. PR #31 is updated in place and not merged.

**Merge recommendation: not yet**, per §XIX.20. The next target is compiler
soundness, which is the one item blocking the abstract theorem and is small.
