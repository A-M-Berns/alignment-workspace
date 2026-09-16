# Prompt — 2026-09-16 seed-statics

Relayed verbatim from the maintainer, 2026-09-16.  Executor: (fill in).

---

Work in `A-M-Berns/alignment-workspace`, on a new branch `round/2026-09-16-seed-statics`.

Your task is to build the first piece of **seed theory** for the normativity line: the statics of what a small set of basic normative premises forces, what it leaves open, which basic premises cannot jointly be held, and whether two reasoners starting from different humble seeds are confined to the same forced region — all *conditional on the settled facts*, with no inductor run anywhere in the round.

This is a theorem-discovery round, not a documentation-only round.  The central question is:

> Given a seed (a typed object defined in this round) and a settled fragment `F`, is the region of normative content the seed forces a well-defined, computable object; is the disagreement between two reasoners with the same constitutive layer and different humble substantive seeds confined to the complement of the common forced region; and does the forced region stabilize as `F` grows and defeaters land?

If yes, make the strongest correct statements precise, prove the finite kernel in Lean on the existing compiler and Farkas machinery, and exhibit the moral and legal fixtures.  If no, produce the sharp obstruction with an exact countermodel.

Do not assume any of the candidate theorems is true.  Try hard to break each of them.  A round that lands one exact countermodel to the confinement theorem is a successful round.

## Separation from the parallel deference round

PR #101 (`round/2026-09-16-noncapture-compilation`) is in flight on the deference side.  This round is separate from it:

* do not edit `wiki/Roadmap.md`, `wiki/Theorem-Spine.md`, `wiki/Corrigibility.md`, `wiki/Deference.md`, or anything under `projects/deference/` or `lean/Workspace/Deference/`;
* do not touch priority items 87–92 or the registry entries PR #101 creates;
* file new priority items at the next free number *after* PR #101's items, and say in the report which numbers you assumed — the maintainer renumbers at merge if needed;
* if a result here bears on the deference side (it will — see "The alignment reading" below), record the connection in this round's `REPORT.md` as a pointer for the maintainer, and do not cross-edit.

## Context to inspect first

Read the current repository state on `main`, especially:

* `wiki/Normativity.md`, `wiki/Legitimacy.md`, `wiki/Normative-Induction.md`, `wiki/Normative-Inductor.md`, `wiki/Diachronic-Answerability.md`, `wiki/Glossary.md`;
* `wiki/Progress.md`, in particular the recorded withdrawal: uptake does not fall out of the learning criterion, because the enforcement position is not efficiently computable and the criterion never quantifies over it;
* the leverage statics as canonically stated in the deck (`projects/normativity/` — locate the "Getting Leverage on Normativity" formulation: endorsed gambles `g_P, g_A, g_S`, the leverage lemma `μ(β_n) ≥ c_P·c_A·c_S`, the LP/dual reading, the sure-loss criterion `𝒞_t = ∅`);
* `lean/Workspace/Normativity/Contrib/NormativeInductorComposition.lean` — `Row`, `CitedRow`, `Bundle`, `Bundle.Region`, `checkCompiled`, `FarkasCert`, `farkas_sound`, `conflict_sound`, `compile_sound`, `failure_conserves`;
* `lean/Workspace/Normativity/Contrib/FourierMotzkin.lean`, `PolyhedralProjection.lean`, `ProjectionCompiler.lean` — reuse before rebuilding;
* the defeat landing (`projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/`) and the unified-grounds round (`2026-09-02-unified-grounds-answerable-defeat/`) for the defeat calculus and standing;
* `DECISIONS.md` — in particular the 2026-08-08 rulings: (1) mechanically-filed past-self charges BURN; (6) seam ordering "reasons constraining → revising reasons → both"; and the 2026-08-09 position that warrant strength is learnable by selection among nearby live candidate bounds;
* `PRIORITIES.md` item 79 (convex representability and compiler completeness) — this round supplies the class that item asks for, as a by-product; say so in the report and do not close the item yourself;
* `AGENTS.md`, all standards, especially 3 (a theorem ships as four things), 8 (deviations declared), 9 (what was not shown), 15 (epistemic promotion is explicit).

Do not reason from memory about the defeat calculus, the compiler, or the leverage statics.  Inspect the formalized statements and use the exact definitions.

## The setting

Fix a language `𝒧` with finite date-fragments `𝒧_t`, canonical security identities for sentences, and rational prices in `[0,1]^d` over a fragment of dimension `d`.  Fix a **settled fragment** `F ⊆ 𝒧_t` with a valuation `F → {0,1}`: the empirical and logical sentences the world has settled by date `t`.  Nothing in this round asks how `F` was produced.

An **endorsement** is a desirable gamble `g` with rational coefficients over securities in `𝒧_t`, constraint `μ(g) ≥ 0`.  The three leverage forms `g_P = 1_X − c_P`, `g_A = 1_{X∧A} − c_A·1_X`, `g_S = 1_{X∧A∧Y} − c_S·1_{X∧A}` are endorsements; so is any rational row.  Under `F`, an endorsement **specializes**: settled coordinates are substituted, and the row becomes a row over the unsettled coordinates only.

A **warrant** `ρ : α ⇝ β` with applicability `A_ρ` compiles to its endorsement triple.  A **defeater** is as in the defeat landing: rebuttal (against `β`) or undercut (against `A_ρ`), with standing.

## The seed as a typed object (first objective)

Define, in Lean, a **seed** with three layers and a transport rule:

* **substantive layer** `S_sub`: a finite list of warrants and endorsements with rational strengths in `(0,1)`, each *defeasible* (each carries a docket port; each may be undercut or rebutted);
* **structural layer** `S_str`: a finite list of endorsements of strength exactly `1` — candidates: dominance (Pareto), impartiality (like cases alike: `P(x) − P(y) = 0` on declared pairs), and any coherence rows the fragment needs — which are *not* defeasible by price but are **revisable by counterexample**: a structural item can be withdrawn only through an explicit surface-change occurrence, never through the docket's ordinary defeat;
* **constitutive layer** `S_con`: the practice — answerability to a declared standing set, coverage of a declared protected class, and **non-dogmatism** (no substantive item of strength `1`; no structural item that is a substantive claim in disguise — give a checkable criterion for this, or record that you could not);
* **transport rule** `τ`: when a predicate `p` in `𝒧_t` is refined into `p₁, …, p_k` in `𝒧_{t'}`, `τ` says what endorsements mentioning `p` become.  Give at least the *conservative* transport (the endorsement is carried to the disjunction, never silently narrowed) as a definition, and show by fixture that its absence splits a seed.

State **humility** as a predicate on seeds: `S_sub` all defeasible, `S_str` all revisable-by-counterexample, `S_con` non-dogmatic.

Keep the five properties of item 79 apart throughout: representability of the class, soundness, completeness within the class, joint feasibility of a serviced bundle, affordable enforceability.  This round addresses the first three for the class "finitely many rational-coefficient endorsements over a fragment" and says nothing about the last two.

## Forced-region statics and seed leverage (second objective)

For a seed `S` and settled fragment `F`:

* the **forced region** `K(S, F)`: the set of price vectors over the unsettled coordinates satisfying every live specialized endorsement of `S`.  Show it is `Bundle.Region` of a computable bundle, and that `checkCompiled` decides membership;
* the **forced interval** `I_φ(S, F) = [inf_{K} P(φ), sup_{K} P(φ)]` for every unsettled `φ`, computed by two LPs (or by Fourier–Motzkin elimination where the existing file makes that cheaper);
* **seed leverage** `Lev(S, F) := Σ_φ (1 − |I_φ(S, F)|)` over the unsettled fragment, or a better normalization you defend — the total content the seed forces.  This is the revival of "leverage" as a measure; name it provisionally and keep it distinct from the technical quantity `wiki/Normativity.md` reserves the word for;
* **seed feasibility**: `K(S, F) = ∅` is a sure loss; produce the `FarkasCert` and the **minimal infeasible subset** of the seed it names.  A seed that is feasible on `F` and infeasible on `F' ⊇ F` is *empirically refuted*; record that this is a definition, not a theorem;
* **monotonicity under settlement**: for `F ⊆ F'` with compatible valuations and no change to the live docket, `I_φ(S, F') ⊆ I_φ(S, F)`.  Prove it or break it.  (Expected: true, by specialization of rows.)
* **non-monotonicity under defeat**: exhibit a defeater whose landing strictly widens some `I_φ`.  (Expected: trivial; the point is to have the witness on file.)

Lean target: `lean/Workspace/Normativity/Contrib/SeedStatics.lean`, built on `Row`/`Bundle`/`FarkasCert`; no new polyhedral machinery unless the existing files cannot express the interval computation.

## The two-reasoner confinement theorem (third objective)

Two reasoners `R¹, R²` with the **same** constitutive and structural layers, **different** humble substantive seeds `S¹_sub, S²_sub`, the same `F`, and the same live warrant set `W` (exchange has already happened).

**Candidate Theorem C1 (confinement).**  For every unsettled `φ`, if `P¹(φ) ∈ K(S¹ ∪ W, F)` and `P²(φ) ∈ K(S² ∪ W, F)`, then

    |P¹(φ) − P²(φ)|  ≤  |I_φ(S¹ ∪ W, F) ∪ I_φ(S² ∪ W, F)|,

and on the **common forced region** `K(S¹ ∪ W, F) ∩ K(S² ∪ W, F)` the bound is the width of the common interval.  Disagreement is confined to the unforced part.

This should be nearly immediate from the definitions.  If it is, say so and spend the effort on what follows.

**Candidate Theorem C2 (grounded convergence under exhaustive exchange).**  Let the exchange be exhaustive: every warrant either reasoner holds is on the shared docket, and every defeater either can raise has been raised.  Then the live warrant sets converge to the **grounded extension** of the shared argumentation framework, and any residual disagreement in warrants is a choice among **preferred extensions**.  Use the defeat calculus as landed; do not import a Dung semantics by paraphrase — state exactly which extension notion the landed calculus supports and prove against that.  If the landed calculus does not determine a unique grounded set, that is a result: record what it does determine.

**Candidate Theorem C3 (seed-independence on the forced fragment).**  Under C2's hypotheses and humility, `K(S¹ ∪ W_∞, F)` and `K(S² ∪ W_∞, F)` have the same forced intervals on every `φ` whose interval is a point in either.  The substantive seed leaves no trace on what is forced; it leaves a trace only on the unforced part.

**Pressure tests for the confinement theorems** — each needs an exact fixture:

1. **Dogmatic item.**  One substantive item of strength `1` in `S¹` only.  C3 must fail; exhibit the permanent trace.
2. **Hysteresis through strength selection.**  Strengths learned by selection among candidate bounds (2026-08-09).  Two reasoners with the same seed and the same `W` but different *orders* of exchange select different candidates and end in different forced regions.  Show whether this happens.  If it does, state the minimal reopening condition that kills it — and note explicitly that this bears on the 2026-08-08 ruling that past-self charges burn: the ruling may need a narrow exception for strength selections.  Do **not** amend the ruling; file it as an outstanding maintainer action.
3. **Refinement without transport.**  `p` refined into `p₁, p₂`; `R¹` transports conservatively, `R²` narrows.  C3 must fail.  Then show C3 holds when both use `τ`.
4. **Price convergence without reason convergence.**  Two reasoners with identical forced intervals everywhere but disjoint live warrant sets (different reasons, same conclusions).  Confinement is satisfied and nothing about *why* has converged.  Record this as the analogue of the deference side's `Corrigible ∧ ¬Authored`: the theorem is about prices, and reason-convergence is a separate claim.
5. **Structural item that is substantive in disguise.**  Encode a contestable claim as an impartiality row on a chosen pair.  Your non-dogmatism criterion should catch it; if it cannot, say so.

## Single-run stabilization (fourth objective)

As `F` grows along a chain `F_0 ⊆ F_1 ⊆ …` and defeaters land from a declared **discovery class** `𝒟` (a finite or efficiently enumerable set of warrants and defeaters that can be raised), does `K(S ∪ W_t, F_t)` converge?

**Candidate Theorem S1 (conditional stabilization).**  If `𝒟` is finite, every element of `𝒟` is eventually raised, and settlement is monotone, then the forced intervals converge (each `I_φ` is eventually constant).

**Expected failure.**  With `𝒟` infinite and defeaters that reopen previously closed intervals, exhibit a seed and a schedule under which some `I_φ` oscillates forever.  State what condition on `𝒟` (summability of reopenings? bounded reopening depth? finite defeat chains?) restores convergence, prove the restored version if it is cheap, and otherwise file it.

This objective does not run an inductor.  It is a statement about the sequence of forced regions.  It is the theorem the program needs *before* any claim of the form "start from `S`, end up at `L`" is meaningful, and no such claim may appear in the report without the discovery class and the settlement chain named.

## The criterion: state it, and prove or obstruct (fifth objective — bounded)

Spend no more than a small fraction of the round here.  The purpose is to put an exact statement on file, not to resolve it.

The three criteria the repository has are stacked: the assessment-relative Logical-Induction criterion (`li.assessment.criterion`), the legitimacy predicate on record evolutions, and continuation BRIA on the decision layer.  Normative content enters the market only through the enforcement trader, which the LI criterion never quantifies over (`wiki/Progress.md`, the withdrawn uptake claim).  Consequently two reasoners satisfying all three can have arbitrary prices on the unsettled normative fragment; limit behaviour is currently a fact about the enforcer, not about any criterion.

State exactly the **fused candidate**:

* an objection is a security paying its holder per period while unanswered, settled by the answer receipt or closure — a finitely adjudicated log event;
* the docket is folded into the assessment process (the assessment assesses objection securities by receipts), so a challenger is a trader;
* the response adapter is held to the BRIA criterion with charges as its loss, so that a reasoner whose market prices an objection as "will be answered" and does not answer is overestimating.

Then either (a) prove, under stated conditions, that any reasoner satisfying the fused criterion has forced region `K(S ∪ W, F)` from the second objective — limit behaviour is criterion-determined — or (b) produce the sharp obstruction: the exact place where the withdrawn uptake argument recurs or a new one appears.  No Lean is required for this objective.  A clean statement plus one obstruction is the expected deliverable.  If the obstruction is decisive, say in the report that limit behaviour is **construction-relative** and what that means for the seed program.

## Fixtures

Both small on purpose.  Every number exact; every fixture in `tests/` with `python3 tests/run.py` green.

**Moral fixture.**  Two individuals, two or three outcomes, a valence predicate per individual per outcome, welfare levels as settled empirical sentences.  Seed: valence ordering (substantive, strength `c < 1`), dominance (structural), impartiality on the declared pair (structural), conservative transport.  Show: (i) the forced intervals on the outcome-ranking sentences; (ii) whether dominance plus impartiality plus coherence forces additive aggregation on the toy (a Harsanyi-style check — do not import Harsanyi; compute); (iii) the leak: interpersonal comparability as an unforced axis, exhibited as a non-point interval that no item in the seed narrows.  Then **add** a population variant with three basic population axioms of your choosing that are individually plausible; obtain the `FarkasCert` and the minimal infeasible subset.  The point of (iii) and the population variant is that the residue has two kinds — *open* and *infeasible* — and the fixture must show both.

**Legal fixture.**  A five-clause constitution: supremacy and *lex specialis* as structural items, one substantive right (strength `c < 1`), one enumerated power, one amendment clause modelled as a surface-change occurrence.  A statute that conflicts with the right.  Show: the forced interval on "the statute is valid"; the effect of the amendment clause as a structural revision (not a docket defeat); and one question the constitution leaves genuinely open.  The purpose is to test that the seed type and the forced-region statics are not moral-specific.  **The legal fixture is allowed to fail.**  If the seed type cannot express something a constitution needs (standing, hierarchy of courts, precedent as strength selection), record exactly what, as a structural defect per `AGENTS.md` standard 14.

## The alignment reading (do not overclaim)

Write one short section connecting the results to the deference side without editing it:

* the constitutive layer `S_con` is the thing a reasoner must not be able to unilaterally change — i.e. it is a protected concern in the response-authority sense; say this in one sentence and point at `wiki/Corrigibility.md` without modifying it;
* the discovery class `𝒟` is, on the deference side, the reason-supply channel; the stabilization condition of the fourth objective and the reason-supply liveness residual are plausibly the same object seen from two sides — record the conjecture, prove nothing about it here;
* the residue (open axes, infeasible clusters) is what a principal community decides; the theory names it and does not decide it.

No sentence in this section may claim that a seed forces a limit absolutely.  Every such claim is relative to `F`, `W`, and `𝒟`.

## What this round is told not to do

* No architecture pass over the generic legitimacy theory.
* No rebuilding of the enforcer, the compiler, the projection machinery, or Progress.
* No inductor run; no oracle-relativized construction; no claim that depends on one.
* No import of Logical-Induction theorems by paraphrase; if an LI theorem is used, cite its exact formalized statement.
* No editing of the files reserved to PR #101 (listed above).
* No "where the seed ends up" claim without `F`, `W`, `𝒟` named.
* Names ship provisional (standard 6).  Candidate names to use and mark provisional: *seed*, *substantive/structural/constitutive layer*, *transport rule*, *humility*, *forced region*, *forced interval*, *seed leverage*, *confinement*, *seed-independence*, *discovery class*, *reopening*.

## Lean / formalization target

`lean/Workspace/Normativity/Contrib/SeedStatics.lean`, sorry-free, auditing to `[propext, Classical.choice, Quot.sound]`:

* the seed structure and the humility predicate;
* `forcedRegion` as a `Bundle` and its membership decision via `checkCompiled`;
* `forcedInterval` (LP endpoints; you may state the interval via the existing Fourier–Motzkin elimination if that is what the file supports, and take the LP optimum as a hypothesis otherwise — say which);
* monotonicity under settlement (second objective);
* C1, and C3 if the landed defeat calculus supports the grounded notion; otherwise the exact statement of what it supports;
* the feasibility/minimal-infeasible-subset extraction on top of `FarkasCert`;
* nothing for the fifth objective.

Register nothing.  List every declaration in `PROVENANCE.md` with its status.  The maintainer registers at merge.

## Output

Directory: `projects/normativity/seed/rounds/2026-09-16-seed-statics/` (a new `seed/` subproject; if the maintainer prefers it under `legitimacy/`, moving it is a rename).  Contents:

* `README.md` — the verdict in one line, in the repository's verdict style;
* `SEED.md` — the typed object, the humility predicate, the transport rule;
* `STATICS.md` — forced region, intervals, leverage, feasibility, monotonicity;
* `CONFINEMENT.md` — C1–C3 with proofs or obstructions, and the five pressure tests;
* `STABILIZATION.md` — S1, the oscillation witness, the restoring condition;
* `CRITERION.md` — the fused candidate stated exactly, and (a) or (b);
* `COUNTERMODELS.md` — every fixture that breaks something, numbered as here;
* `FIXTURES.md` — the moral and legal fixtures with exact arithmetic;
* `ALIGNMENT_READING.md` — the short section above;
* `REPORT.md` — per `AGENTS.md`: what was shown, what was not, deviations, proposed priority changes, outstanding maintainer actions;
* `PROVENANCE.md`, `src/`, `tests/run.py`.

Mirror the prompt at `prompts/2026-09-16-seed-statics/PROMPT.md` and the report pointer at `prompts/2026-09-16-seed-statics/REPORT.md`.  Add the round to `state/rounds.json`.  Do not merge.

## Final questions the report must answer

1. Is the seed a well-typed object with a checkable humility predicate, and did the non-dogmatism criterion catch the disguised-substantive structural item?
2. Is the forced region computable on the existing compiler, and does monotonicity under settlement hold?
3. Does confinement (C1) hold, and is it as trivial as expected?
4. Does the landed defeat calculus determine a grounded extension?  If not, what does it determine, and what does C2 become?
5. Does seed-independence (C3) hold under humility, and which of the five pressure tests break it?
6. Does hysteresis through strength selection occur, and what minimal reopening condition kills it?  What does this imply for the past-self-burn ruling?  (Outstanding action; do not amend.)
7. Does the forced region stabilize along a settlement chain with a finite discovery class?  What is the oscillation witness for an infinite one, and what condition restores convergence?
8. On the moral fixture: what is forced, what is open, and what is infeasible — and are the open and the infeasible residues cleanly distinguished?
9. Did the legal fixture instantiate the interface, and if not, exactly which structural defect blocked it?
10. Is the fused criterion stated exactly, and is limit behaviour criterion-determined or construction-relative under it?
11. What does this round supply toward item 79, and what of item 79 remains?
12. Which of this round's objects coincide with deference-side objects (constitutive layer / protected concern; discovery class / reason-supply), as conjectures only?
13. Which names introduced here are provisional, and which existing names were reused with their existing meanings?
14. What would you have wanted to prove and could not, and where exactly did it stop?
