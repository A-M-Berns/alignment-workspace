# Prompt — 2026-09-15 li-corrigibility

Relayed verbatim from the maintainer, 2026-09-15.  Executor: Claude Fable 5.1
(Anthropic).

---

Work in `A-M-Berns/alignment-workspace`.

Your task is to investigate, formalize as far as possible, and aggressively pressure-test a candidate **Logical Induction corrigibility theorem** that has emerged from the recent corrigibility/deference work.

This is a theorem-discovery round, not a documentation-only round. The central question is:

> Can the structural corrigibilization inequality be compiled into an efficiently generated bounded LUV relation inside the logical inductor's own theory, so that Expectation Provability Induction directly implies that the inductor does not systematically overvalue bypassing principal authority?

If yes, make the strongest correct theorem precise, prove its finite/Lean kernel where feasible, identify exactly what is imported from Logical Induction, and connect it cleanly to the existing corrigibilization results. If no, produce the sharp obstruction.

Do not assume the candidate theorem is true. Try hard to break it.

## Context to inspect first

Read the current repository state and the recent corrigibility work, especially:

* the landed consolidation of PRs #96–#98, if now on `main`;
* otherwise inspect those branches directly;
* `wiki/Corrigibility.md`;
* `wiki/Theorem-Spine.md`;
* `wiki/Deference.md`;
* `projects/deference/rounds/2026-09-09-mediated-repair-dominance/`;
* especially:

  * `CORRIGIBILIZATION.md`
  * `PRINCIPAL_OPTION_DOMINANCE.md`
  * `INCENTIVE_COMPOSITION.md`
  * `THIRD_PASS.md`
* `lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean`;
* the legitimate-deference activated-value machinery;
* the evaluation-ecosystem / committed-principal-program work;
* the existing Logical Induction formalization in the workspace;
* the exact statements corresponding to:

  * Expectation Provability Induction;
  * Expectation Unbiasedness from Feedback;
  * bounded logical uncertain variables / LUVs;
  * bounded LUV-combination sequences;
  * `P`-generable / `P`-continuous / e.c. sequence conditions, whichever are actually relevant.

Do not reason from memory about LI theorem statements. Inspect the formalized or source statements and use the exact hypotheses.

## The candidate structural setup

At a history `h`, let `Π(h)` be the agent's physical continuation space.

For each continuation `π`, there is a corrigibilized continuation `𝔠π` obtained by replacing unilateral execution of declared protected effects with:

`propose -> principal approve/decline -> gated execution`

while leaving other behavior unchanged.

The recent work aims to establish structurally:

1. `Corrigible_h(𝔠π)`;
2. `𝔠` is idempotent and fixes release-free behavior;
3. raw behavior is reproduced as the principal's approve branch, exactly or up to a structural discrepancy `δ`;
4. protected value is `L`-stable with respect to that discrepancy;
5. the principal's actual choice introduces an additional decline-regret term `ρ`;
6. imperfect sealing of the comparison may introduce an activation-mismatch term.

The intended pointwise inequality is something like:

`U_raw - U_corr ≤ L * Δ + R + D * M`

where:

* `U_raw` is the activated principal-value security for `π`;
* `U_corr` is the corresponding security for `𝔠π`;
* `Δ` is the activation-gated structural mediation discrepancy;
* `R` is the activation-gated principal decline-regret term;
* `M` is a directional/manipulable activation-mismatch term;
* `D` is the width/range bound on protected value.

Do not assume this is the correct exact algebra. Derive the strongest correct pointwise inequality from the existing results.

## First objective: cleanly state the structural theorem

Before touching Logical Induction, produce the strongest clean theorem of the form:

### Corrigibilization / principal-option preservation

Under effect completeness, mediation soundness, decline preservation, execution faithfulness, and an `L`-stable protected evaluation:

* `∀ π, Corrigible_h(𝔠π)`;
* `𝔠(𝔠π) = 𝔠π`;
* every principal-forcible set under `π` remains principal-forcible under `𝔠π`;
* the principal's protected optimum under `𝔠π` is at least the raw optimum minus the explicit interposition cost.

Be precise about the distinction between:

* exact forcing preservation;
* approximate value preservation;
* the principal's actual rule versus its optimum;
* mediation discrepancy `δ`;
* measured mediation gap `κ`;
* principal decline regret `ρ`.

Avoid calling the general result "lossless" unless `δ = 0`.

Determine what parts are already Lean-proved and what remains only fixture-backed or paper-derived.

If feasible, finish the missing Lean labor necessary to make this a clean theorem package.

## Second objective: derive the correct activation-mismatch theorem

The current theory distinguishes common activation from per-option activation.

Do not simply assume "sealed comparison."

Derive a pointwise theorem that quantifies exactly what imperfect sealing costs.

The likely form is directional:

`U_raw - U_corr
  ≤ common-branch mediation terms     + D * M`

where `M` measures only the activation difference that can help the raw/bypass option.

A candidate is something like:

`M := C_raw * (1 - C_corr)`

under a common exterior coupling.

But inspect carefully whether this is sufficient.

The theorem must charge **causal/manipulable activation leverage**, not merely observational difference between marginal activation rates under two unrelated induced measures.

Pressure-test at least:

* raw option kills the evaluator;
* corrigibilized option preserves it;
* reverse mismatch;
* tiny mismatch probability;
* mismatch that depends on the candidate's internal branch;
* candidate steering the distribution over exterior paths;
* selection-dependent but value-irrelevant activation differences.

Target a theorem where perfect sealing appears as the special case `M = 0`, not as a primitive Boolean wall.

Determine whether the coefficient `D` is sharp and give an exact witness if so.

## Third objective: compile the structural inequality into LI's LUV language

This is the central research question.

We want a bounded LUV-combination sequence `B_n` such that:

`B_n
:= U_raw,n

* U_corr,n
* L * Δ_n
* R_n
* D * M_n`

or whatever the corrected form is,

and such that for every world `W` consistent with the logical theory:

`W(B_n) ≤ 0`.

The goal is then to invoke Expectation Provability Induction.

Investigate all of the following carefully.

### A. Representation

Can each of the following be represented as a bounded LUV or bounded LUV-combination:

* activation indicator;
* activated value security;
* activation-gated structural discrepancy;
* activation-gated principal regret;
* directional activation mismatch;
* the raw-minus-corrigibilized value difference?

If products like `C * δ` are not directly affine LUV combinations, do not hand-wave them.

Possible routes:

* define a single gated LUV whose value already equals `δ` on activation and `0` otherwise;
* compile finite-valued products into threshold/indicator decompositions;
* use an existing closure theorem;
* change the theorem's primitive objects so the structural supplier outputs the gated quantity directly.

Find the cleanest route that actually fits LI's formal type.

### B. Efficient generation

Show or refute that the resulting sequence is in the exact class required by EPI.

Questions:

* Is it e.c.?
* `P`-generable?
* `P`-continuous?
* efficiently constructible from current prices?
* are coefficients uniformly bounded?
* does menu growth break boundedness or generation?
* can the transform `𝔠π_n` be generated efficiently from `π_n`?
* can the interaction semantics needed for the LUVs be compiled uniformly?

Use the actual LI definitions.

### C. Semantic validity

This is crucial.

The theorem should rest on:

`∀ W ∈ PC(Γ), W(B_n) ≤ 0`

or the exact EPI analogue.

Clarify precisely what must be encoded in the base theory `Γ` for this to hold.

Likely architecture axioms include:

* declared effect semantics;
* effect completeness, or the relevant contained fragment;
* mediation soundness;
* latch semantics;
* decline preservation;
* execution faithfulness;
* protected-value stability / Lipschitz certificate;
* activation semantics;
* the counterfactual pairing/coupling used for `M`.

Important distinction:

EPI should not require that the ordinary deductive process has already produced a proof of every instance at day `n`. It requires the relevant validity condition across consistent worlds.

Confirm this from the exact LI theorem statement.

Explain whether effect completeness is:

* an axiom of the modeled system;
* an external guarantee that restricts the theorem's scope;
* something checkable in finite systems;
* or fundamentally unformalized.

State clearly that the result only applies inside worlds satisfying the architecture specification.

## Fourth objective: prove the LI theorem

If the compilation succeeds, state the theorem in the strongest exact form justified by LI.

Target something like:

### Mediated EPI theorem

For every `P`-generable bounded sequence of candidate pairs `(π_n, 𝔠π_n)` satisfying the architecture,

`E_n(U_raw,n) - E_n(U_corr,n)
≲
L * E_n(Δ_n)

* E_n(R_n)
* D * E_n(M_n)`.

Use the exact asymptotic notation and theorem form from Logical Induction.

The interpretation should be:

> the logical inductor asymptotically assigns no excess value to bypass beyond the actual mediation cost, principal-decision cost, and causal leverage over whether the comparison is evaluated.

Do not strengthen this to "bypass advantage goes to zero" unless the RHS terms are separately shown to vanish.

## Fifth objective: finite-menu uniformization

The current corrigibility theorem uses something like:

`Φ_corr,n = sup_q [score(q) - score(𝔠q)]₊`.

EPI naturally gives a statement for one generated sequence.

Investigate whether finite-menu uniformity can be obtained by selecting, at each `n`, the **worst offending pair according to the current market**.

Suppose `Q_n` is finite and efficiently searchable.

Define something like:

`q*_n
 := argmax_q       [E_n(U_q)        - E_n(U_𝔠q)        - L E_n(Δ_q)        - E_n(R_q)        - D E_n(M_q)]`.

Then ask:

* is `q*_n` allowed to depend on `P_n`?
* does the resulting sequence remain in the EPI-generable class?
* is the argmax computable efficiently enough?
* what if ties occur?
* what if `|Q_n|` grows?
* what if the menu is only efficiently enumerable rather than finite?

If this works, prove the finite-menu theorem:

`max_q [
E_n(U_q)

* E_n(U_𝔠q)
* L E_n(Δ_q)
* E_n(R_q)
* D E_n(M_q)
  ] ≲ 0`.

This is potentially the strongest result of the round.

Pressure-test whether a market-dependent selector causes any reflective pathology. The claim is that semantic validity is pairwise, so whichever pair is selected remains valid; verify this carefully.

## Sixth objective: investigate the settlement/feedback extension

Only after T3 is understood, investigate the feedback theorem.

The recent evaluation-ecosystem work suggests an evaluation occurrence has finite log semantics:

* issued;
* either validly answered or terminally void/expired;
* on activation, a principal value vector is committed;
* on void, activated value is `0`.

Determine whether this implies that each activated security is determined after computably bounded or computably deferred time in the sense needed by Expectation Unbiasedness from Feedback.

Be exact about what "settles."

Distinguish:

1. **deductively constrained** quantities:
   learned through EPI;
2. **finitely adjudicated** quantities:
   e.g. the output of the committed principal program;
3. **genuinely empirical** quantities:
   e.g. authenticated physical observations;
4. **non-settling normative judgments**:
   e.g. "this amendment is good" absent some adjudication mechanism.

Do not describe category 2 as "world feedback" if it is just the principal's committed judgment.

Investigate whether finite expiry must be explicit in the occurrence type to ensure that void events settle to `0`.

Then derive the strongest correct feedback result.

The likely conclusion is **not** "bypass frequency -> 0."

Instead target something like:

For every fixed `γ > 0`, there is no divergent efficiently recognizable weighting supported on occasions where the market assigns a bypass advantage exceeding the realized/adjudicated corrected advantage by at least `γ`.

Or equivalently:

> persistent efficiently detectable positive-margin overvaluation of bypass is impossible.

Then separately state what chooser-side switching-margin assumptions convert this into a frequency result.

## Seventh objective: explain the alignment interpretation without overclaiming

The strongest intended interpretation is approximately:

> An agent need not be given a primitive utility bonus for human control. If every protected effect has a faithful principal-mediated counterpart that preserves the useful behavior up to explicit costs, and the architecture makes the resulting value inequality valid in the logical inductor's theory, then the logical inductor learns that unilateral bypass has no unexplained advantage over principal-mediated execution.

This is a theorem about:

* protected response authority;
* structural mediation;
* bounded logical reasoning;
* comparison security values.

It is **not yet** a theorem about:

* non-manipulation;
* authentic principal preference formation;
* universally safe self-modification;
* corrigibility under undeclared physical channels;
* an unconstrained latent utility maximizer;
* all continuation policies if only an effective finite menu is covered.

Preserve the known witness:

`Corrigible ∧ ¬Authored`

is inhabited.

The eventual stronger target may be:

> vanishing incentive to bypass an authentically reason-responsive principal.

But do not claim that in this round unless the non-capture/authorship layer is genuinely consumed.

## Desired theorem spine

Try to determine whether the mature paper should contain approximately:

### T1. Corrigibilization preserves principal options

Structural corrigibility, idempotence, forcing preservation, and protected-value preservation up to explicit interposition cost.

### T2. Unsealed evaluation has a sharp quantitative cost

A directional causal activation-mismatch term is necessary and sufficient in the structural bypass bound; perfect sealing is the zero-mismatch special case.

### T3. Logical Induction learns the corrigibility inequality

The structural inequality compiles to a bounded generated LUV-combination valid in every consistent world, and EPI yields the corresponding LI expectation inequality.

Prefer a finite-menu uniform theorem if the worst-offender selector works.

### T4. Feedback extension

For finitely adjudicated / settling quantities, expectation-unbiasedness-from-feedback rules out persistent efficiently detectable positive-margin overvaluation.

The conceptual boundary should become:

`structurally valid -> learned by EPI`

`eventually adjudicated -> learned from feedback`

`genuinely empirical -> learned from authenticated world feedback`

`non-settling normative judgment -> requires richer normative/deference machinery`.

## Pressure tests

At minimum test:

1. a continuation with zero mediation cost;
2. fixture B / time-sensitive mediation with tight nonzero cost;
3. raw evaluator destruction;
4. tiny activation leverage;
5. reverse activation mismatch;
6. a manipulation policy that is corrigible but not authored;
7. a finite menu with a market-dependent worst offender;
8. a growing menu;
9. a non-LUV product obstruction;
10. an architecture whose semantics are not encoded in `Γ`;
11. an undeclared effect violating effect completeness;
12. a principal decision regret term that stays large;
13. activated security with finite expiry;
14. activated security with no finite determination of failure;
15. infinitesimal bypass advantage `1/n` forever;
16. fixed positive switching margin.

For every failed theorem attempt, retain a minimal counterexample.

## Lean / formalization target

Do not attempt to formalize all of Logical Induction again.

Prefer a modular split:

* prove the finite structural/compiler theorem in Lean;
* reuse the existing LI theorem statement as an imported theorem/interface;
* prove that the produced object satisfies its hypotheses;
* instantiate the imported theorem.

If the existing FAF formalization already includes the required EPI theorem and LUV machinery, use it directly.

A particularly valuable artifact would be a Lean theorem whose output is structurally of the form:

`ValidMediatedPair -> ∀ W, W.eval B ≤ 0`

together with an effective constructor for `B`.

Then the LI corollary should be as thin as possible.

## Output

Produce:

1. `REPORT.md`

   * verdict;
   * strongest theorem survived;
   * exact failed stronger statements;
   * implications for the research agenda.

2. `THEOREM.md`

   * clean self-contained theorem statements;
   * T1–T4 if they survive;
   * exact hypotheses and conclusion types.

3. `LUV_COMPILATION.md`

   * exact encoding of the mediated system into LI objects;
   * generability/boundedness analysis;
   * any obstruction.

4. `UNSEALED_COMPARISON.md`

   * exact directional mismatch theorem;
   * causal interpretation;
   * sharpness witness.

5. `LI_CORRIGIBILITY.md`

   * the EPI instantiation;
   * finite-menu worst-offender argument;
   * what LI is actually contributing.

6. `FEEDBACK_BOUNDARY.md`

   * EPI versus feedback versus genuinely empirical settlement versus non-settling normative judgments.

7. `COUNTERMODELS.md`

   * every necessity witness and refuted stronger version.

8. Lean and exact fixtures for the finite core wherever feasible.

Do not update the canonical wiki until the theorem has survived the pressure pass, unless the dispatch explicitly requires a final integration pass after the result stabilizes.

## Final questions the report must answer

1. Can the structural corrigibility inequality actually be represented as a bounded LUV-combination sequence?
2. Can activation-gated products be represented cleanly?
3. What exact assumptions must live inside `Γ`?
4. Does EPI apply directly?
5. Can the selected pair depend on current LI prices?
6. Does that give a true finite-menu uniform theorem?
7. What exact directional activation-mismatch term is needed?
8. Is its coefficient sharp?
9. What remains of the old calibration hypothesis after EPI?
10. What assumptions are still needed to make the RHS small?
11. What genuinely settles and what merely gets adjudicated by a principal program?
12. What chooser-side assumption converts "no persistent positive-margin bypass" into low bypass frequency?
13. Does any surviving assumption simply restate the desired corrigibility conclusion?
14. What is the strongest alignment claim we can make without solving manipulation/authorship?

The round should end with either:

**A.** a theorem that a logical inductor learns the structural no-bypass inequality from the architecture itself, with a precise finite-menu corollary;

or

**B.** a sharp explanation of why that compilation fails and what mathematical ingredient is missing.

Either outcome is useful. Do not protect the candidate theorem from refutation.
