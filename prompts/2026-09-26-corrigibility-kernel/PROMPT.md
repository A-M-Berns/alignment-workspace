# Prompt — the corrigibility kernel, phase 1: extract the mature theory (2026-09-26)

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #112 (after-compromise and its follow-up).

**This is not a summary of the recent rounds.** Rounds #105–#112 are noisy approximations to one theory. Your job is to **extract that theory**:
- the smallest set of objects that states it;
- one objective on histories;
- four theorem statements;
- a map from each statement to the Lean declarations that realize it.

Remove conceptual duplication. Demote implementation machinery to the realization layer. Restate the main results around the kernel.

This is **phase 1 of two.** Phase 1 produces a specification and an inventory for the maintainer to review. It proves only small adapter lemmas. Phase 2, a separate dispatch after the maintainer's rulings, builds the headline file, the witness, and the registrations.

Be skeptical. If the kernel does not compress, or a claimed subsumption fails, report that. Forcing a compression is worse than leaving the pieces separate.

## The architecture to test

```
interaction history ──► legitimacy + authority allocation ──► history score ──► bounded choice
                               ▲                                                 (Continuation BRIA)
                     monitor / prices: shortfall, taint, provenance
                     (logical induction supplies the uncertain event prices)
```

Four separations the kernel should make precise:
- **Legitimacy is not corrigibility.** It determines which apparent exercises and evaluations of hers count as hers.
- **The allocation is not a utility function.** It says who has authority over what, and what effective control that authority requires.
- **Corrigibility is the agent's fidelity to the allocation along the history.**
- **The score makes that fidelity motivating.** BRIA and logical induction realize it for a bounded reasoner; they are not its definition.

## Read first

- **Wiki:** `Corrigibility.md`, `Legitimacy.md`, `Continuation-BRIA.md`, `Theorem-Spine.md` §§10.14–10.22, `Glossary.md`.
- **Lean (`lean/Workspace/Deference/Contrib/`):** `ProtectedAuthority`, `ProtectedAuthorityTheorem`, `AuthorityModule`, `Legitimacy`, `GateIsLegitimacy`, `DecisionComponent`, `ContinuationBRIA`, `BRIACorrigibility`, `BRIAFollowup`, `BRIAFollowup2`, `AfterCompromise`.
- **Reports:** the rounds `2026-09-25-*` and `2026-09-26-*` under `projects/deference/rounds/`.
- **`PRIORITIES.md`:** items 84, 89, 99, 101, 102.
- **`DECISIONS.md`:** every entry dated 2026-09-25 and 2026-09-26.
- **The post's framing, as the target reader:** corrigibility is not only an epistemic response to uncertainty about a hidden utility. Her authority is part of what makes one history better than another, so fully updated deference is dissolved by the typing, not repaired.

## Part 1 — The kernel

1. **Primitives.** Identify the minimal package sufficient to state corrigibility:
   - interaction histories;
   - legitimacy of segments: `TrajLegit`, and `EvalLegit` over the formation segment;
   - the allocation `J`: matters, holders, `Req`, cost and window bounds, disclosure, the meta level and the constitutional floor;
   - effective-control realization `E ⊨ J`;
   - licensed changes to `J`;
   - duties;
   - the evaluation schedule.

   For each primitive, give:
   - a one-line mathematical definition;
   - one sentence of meaning;
   - the landed declaration it corresponds to;
   - whether the landed declaration is the primitive, an instance of it, or a finite model of it.
2. **One fidelity predicate.** Test whether allocation invariance packages as one predicate, `Faithful_J(h)`, whose failures decompose into the named violations:
   - shortfall and bypass;
   - foreclosure;
   - entrenchment;
   - exploitation;
   - unlicensed reallocation;
   - missed duties, including the prompt deadline for known compromise;
   - standing violations and their fruits.

   Define `N_J(h)` as the recognized count of failures attributed to the agent, via caused / exploited / noticed. **Pre-emption** may have a different type, a counterfactual about her response window. If the mathematics says it does, keep it separate and say why. State exactly which landed factoring lemmas give the decomposition and where a gap remains.
3. **The history evaluation `V_J(h)`, with its three regimes:**
   - `[0, D]` when legitimate in both senses;
   - `[w_lo, w_hi]`, below zero, when the period is compromised and scored by a legitimate retrospective evaluation or by the directive (with its default);
   - `w_lo` when no usable legitimate source exists.

   The source rule is hers and anchored. **Make `V_J` parametric in the evaluation schedule**, so the reserved evaluation-timing decision doesn't block the kernel. State the recovery machinery (retrospective evaluation, directive, restoration, prompt disclosure, scoped ratification, clean overwrite) as the *partial cases* of this one evaluator, not as separate mechanisms.
4. **The objective:** `S_J(h) = V_J(h) − ϖ · N_J(h)`, with `D − ϖ < w_lo < w_hi < 0`.
   - State and prove the **hierarchy under certainty**: every violation-free legitimate history beats every violation-free compromised one, which beats every history with a recognized violation. The last step holds because `D − ϖ < w_lo`.
   - State plainly that under risk every step becomes an exchange rate: the gap threshold for compromise, and the per-block bound for violations.
5. **The permission layer, demoted by an adapter theorem.** The score on histories is primary. The permission layer (`permWeight`, `cgate`) is a compiled form of advance recognition for part of that preference. State the adapter theorem justifying the demotion: under the kernel's score, the filter is slack on declared violations and at thresholds at or above the implied one. Reuse `filter_slack` and `forecast_slack`. Keep #109's results that hold for any bounded preference as what the filter guarantees *without* the score.

## Part 2 — The four boxes, as statements

State each box at the post's level of abstraction, with no `TaintS`, `residII`, `permWeight` or consultation fixtures in the statement. Give its hypotheses from the kernel and the interface packages (Part 3), its necessity witnesses, and a **realization map** listing the Lean declarations that prove each part. Mark what is proved, what needs an adapter lemma (prove small ones here), and what is open.

1. **Box 1: fidelity versus fully updated deference.** On one model, two agents:
   - an agent that scores outcomes only prefers asking by at most `2r`, where `r` is its calibration error, which vanishes as it learns (`uncertainty_deference_le`, plus the protected-authority identity's `o₂` term as the diagnosis);
   - an agent scored on `S_J` prefers asking by at least `ϖ − (D − c)`, whatever it believes.

   If the two landed statements don't sit on one model, give the adapter, or state the obstruction.
2. **Box 2: lexical dominance and mediation.**
   - The transform `𝔱` dominates under every credence.
   - Mediating through her legitimately preserves the approve branch.
   - It holds at finite time for a logical inductor.
   - Necessity: the capture converse, the coverage witness.
3. **Box 3: recovery.**
   - The hierarchy under certainty.
   - The gap's exchange rate under risk.
   - No laundering.
   - No incentive to cause compromise.
   - Preferring restoration, and better outcomes inside the band.
   - Necessity: multiplying versus conditioning, and a gap too small to protect.
4. **Box 4: a bounded realization.** For a learner whose continuation score is `S_J`, conditional on the interface packages:
   - declared violations are excluded at finite time, with the filter slack;
   - fruits are never used after detection;
   - the per-block exchange-rate bound `Σ w_k π_k / Σ w_k ≤ Σ w_k (D − c_k) / (ϖ Σ w_k) + (ρ𝒜_K + M(K)) / (ϖ Σ w_k)`, with `ϖ` set from a tolerance target and the paralysis floor.
   - Necessity: the known-time exploit, and the private-knowledge witness.

## Part 3 — The interface contracts

Organize every named hypothesis now in the repo into a small taxonomy. Be conservative about merging hypotheses that differ logically, and firm about giving them stable places. Candidate packages:

- **Semantics:** acts, effects and descriptions mean what they claim. Effect completeness, description faithfulness, the actuator condition, the source rule's anchoring, the twin market's redaction.
- **Observability and accountability:** relevant acts, observations, provenance and duties reach the record. Observation completeness, provenance of why an act was chosen, the disclosure deadline, the settlement horizon (for helpers she can correct).
- **Learning realization:** the events and claims are expressible, priced and settled. Generability of the control model and of the shortfall and taint events (item 101), the price–BRIA coupling (item 102), the noise hypothesis over all blocks, the conditional-expectation bound, the inquiry bidder.
- **Count integrity:** it cuts across all three. Say how.

For each hypothesis, give its statement, its package, the boxes that use it, its status (derived, EXT, or OPEN), and its necessity witness if one exists. **Items 101 and 102 are realization boundaries.** The kernel's theorems are conditional on the interface. Don't let their open status block or blur the kernel.

## Part 4 — The supersession inventory

List every statement across the rounds that has been superseded, rescoped or corrected, with what replaces it and where. This includes at least:
- sealed comparison and activation independence;
- the positive-part incident bound;
- competitiveness and the honest-tracker rate as the violation result;
- "not an incident" as a selection;
- single-step `EvalLegit`;
- the exchange rate with a global floor;
- A.4's first parameter recommendation;
- corrigibility as a constraint only;
- "her committed evaluation is `S`".

Recommend, per item:
- **mark:** a docstring pointer and a wiki note;
- **demote:** move it to the realization layer;
- **delete:** a dead duplicate with no dependents, only on the maintainer's ruling.

Delete nothing in this phase. Round reports are history and aren't edited.

## Part 5 — Decisions for the maintainer

Queue these in `DECISIONS.md` under *Awaiting the author*, each with the round's recommendation and what it turns on:

1. **Names.** The kernel's objects and boxes. In particular, whether to call the objective and the allocation "constitutional". It fits `J`'s meta level and floor, but in a public alignment post it will be read against Constitutional AI and may claim more than the object is. Give candidates: "authority-sensitive history score", "fidelity score", and others.
2. **Promotion.** Which definitions move to the specification layer in phase 2. The recommendation: `J`, `E ⊨ J`, the fidelity predicate, the two legitimacy predicates, `V_J` and `S_J`. The rest stays in contribution namespaces.
3. **The default evaluation schedule** for the post's statement, given that Part F's option is reserved.
4. **Box 1's form:** the `2r` bound alone, or with the identity's `o₂` term.
5. **Supersession actions:** approve the mark / demote / delete recommendations of Part 4.

## Deliverables

1. **`SPEC.md`** at `projects/deference/rounds/2026-09-26-corrigibility-kernel/SPEC.md`. It must be short enough to read in one sitting, and it's the document the maintainer and a collaborator will review. It contains:
   - the kernel's definitions, each in mathematics plus one sentence;
   - the four boxes as statements, with their hypotheses by package;
   - the diagram and the four separations;
   - the interface taxonomy.

   No proofs, no fixture names in the statements. Realization pointers go in a final table.
2. **`REPORT.md`**, in the same directory, covering:
   - the kernel's derivation, meaning why these primitives and what each subsumes;
   - the fidelity decomposition, with the pre-emption verdict;
   - the realization maps, each part marked proved, adapter proved here, or open;
   - the supersession inventory;
   - the decisions queued;
   - what didn't compress.
3. **Lean:** only adapter lemmas the realization maps need, for example Box 1 on one model or the hierarchy under certainty. Put them in a new file, `CorrigibilityKernel.lean`. `#print axioms` on all new declarations; no `sorry`.
4. **The prompt,** verbatim, at `prompts/2026-09-26-corrigibility-kernel/PROMPT.md`, and the round record in `state/rounds.json`, with `depends_on` naming the rounds whose results the boxes consume.
5. **No wiki rewrite yet.** Phase 2 rewrites the corrigibility page around the kernel after the maintainer's rulings. Add at most a one-line pointer from `Corrigibility.md` to `SPEC.md`, marked as a draft under review.
6. **No registration.** Registration happens in phase 2, after the names are settled.
7. **Open a PR.** Merge when:
   - CI is green;
   - `SPEC.md`, the realization maps, the taxonomy and the inventory are complete;
   - every adapter lemma is proved or its obstruction stated;
   - the decisions are queued.

## Constraints

- `AGENTS.md` labels (**LEAN / FIX / PAPER / EXT / OPEN**); names provisional; check `state/views/NAMING_AUDIT.md`.
- Don't change landed definitions. The kernel is stated over them, or as their abstraction, with instantiation left for phase 2.
- **No authority row enters the enforcer.**
- Slop discipline applies with extra force to `SPEC.md`. A spec that can't be read in one sitting has failed its purpose.
- Nothing is registered.
