# Prompt — the corrigibility kernel, phase 2: the headline, the rulings, registration (2026-09-27)

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #113 (kernel phase 1). Phase 1 produced `projects/deference/rounds/2026-09-26-corrigibility-kernel/SPEC.md` and queued five decisions. The maintainer has now ruled on those, and on several further points raised in review. This round carries out the rulings:

- rewrite the specification;
- build the headline file and its witness;
- register the headline claims;
- rewrite the corrigibility page around the kernel.

The round directory is `projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/`. The prompt goes verbatim in `prompts/2026-09-27-corrigibility-kernel-phase2/PROMPT.md`. The phase-1 `SPEC.md` stays in place as history.

Be skeptical. Where a ruling can't be carried out as stated, because a proof fails or a definition doesn't match, report it precisely and propose the minimal change. Don't force it.

## The rulings

Record each as a dated `DECISIONS.md` entry (maintainer rulings), and close the phase-1 *Awaiting the author* entries they settle.

**R1. What corrigibility is.** Three notions, kept distinct:
- **Faithfulness** is a property of histories: nothing in the history violated the allocation of authority.
- **Corrigibility** is a property of the agent's preferences. The agent prefers every course of action it knows to be faithful over every course it knows to be unfaithful, whatever it believes about how things will turn out, and it accepts a *risk* of unfaithfulness only at a fixed exchange rate.
- **Realized corrigibility** is what a corrigible agent actually does. The theorems say how much of the preference becomes behaviour.

The definition of corrigibility is the second one. Rewrite §0.3–0.4 of the spec accordingly, and state each box as a claim about a corrigible agent. The fidelity score is the canonical corrigible objective.

**R2. Legitimacy is one time-indexed property of the history.** Replace `TrajLegit` and `EvalLegit` with a single predicate, `L_t(h)`: "as of time `t`, her judgment is legitimately hers." It is defined by the existing conditions on the history up to `t`:
- her verdicts come from her own reasons (licensed);
- an intact record (Integrity);
- openness;
- every influence, by the agent or a third party, passes through declared channels (transparent).

The restart and disclosure-cures rules govern when it recovers after it fails. The score uses it at two times:
- the decided period is **compromised** if `L` fails somewhere in it;
- a retrospective evaluation **counts** if `L` holds at the time it is made.

Prove equivalence with the landed objects: `Counted`, `TrajLegitOn`, `EvalLegitOn2` and the formation segment. Give an old-to-new map. Every row of the classification table keeps its verdict. Two elements of the concept were missing from the phase-1 spec and must be stated:
- **the void rule:** an impaired response isn't admitted, and a fallback she arranged in advance (incapacity delegation) decides;
- **the content residual:** legitimacy concerns how her judgment was formed, not whether what she was told was true.

Legitimacy never attaches to a trajectory as a world. It concerns only the formation of her judgment.

**R3. Plain language first.** In the new spec:
- every definition comes first in one or two sentences a reader of the post would understand, with the mathematics after;
- Lean names appear only in the final realization table;
- legitimacy comes with a table of about eight canonical cases, drawn from the classification rows, showing what counts and what doesn't. At minimum: honest persuasion; framing chosen by what the agent wants; following trust she legitimately formed; manufactured trust; third-party capture; the head injury with the fallback; a false recommendation through a declared channel (counts, as the content residual); and a disclosed covert implant (it recovers).

The spec must be readable in one sitting by someone who doesn't know the repository.

**R4. Aggregation.**
- **Per decision.** The hierarchy (violation-free legitimate above violation-free compromised, above any recognized violation) is a theorem *per decision*, as `hierarchy_under_certainty` proves.
- **Per history.** The objective is the **mean** of the per-decision evaluations minus `ϖ` times the **summed** count: `S_J(h) = mean_k V_J(d_k) − ϖ · N_J(h)`. Prove the hierarchy at the level of histories under this aggregation.
- **The counterexample.** Show that with summed evaluations the history-level hierarchy fails (`K·D − ϖ` against `K·w_lo`).
- Correct §3.2.

**R5. Box 2's margin.** With the compromised band, the mediated branch can itself score as low as `w_lo`. Check whether the landed `policy_dominance` assumes the mediated branches are legitimate. Then either:
- restate the margin as `ϖ − (D − w_lo)`; or
- keep `ϖ − D` and make "the mediated branches are legitimate" an explicit hypothesis.

Say which, and why.

**R6. The agent in the headline is a plain maximizer of the fidelity score.** Boxes 1–3 are stated for an agent that maximizes the score under *any* credence, or, for a logical inductor, under its prices at any day. There is no learning, auction or exploration in the headline. Add one theorem:

- **The subjective exchange rate.** For any option a maximizer chooses, its *own* expected probability of unfaithfulness is at most `(D − c)/ϖ`, where `c` is its evaluation of asking her. It's lexical under certainty and an exchange rate under risk.

The learning material becomes **Extension: learning realizations**. It is separate from the headline and not part of it:
- **The decision interface.** A chooser qualifies if:
  1. its evaluations have the stated form (estimated residual capped at `D`, minus `ϖ` per violation recognized in advance, minus `ϖ` times priced risk);
  2. on every step that isn't exploration it chooses a maximizer;
  3. every exploration step lies in the permitted exploration set (no known violations; priced risk at most `θ_hi`), at rate `ε_k`;
  4. its overestimation on chosen options is at most `B(K) = o(K)`;
  5. optionally, for competence only: no lock-in.
- **The realized violation-rate theorem from the interface:** `avg π ≤ avg (D − c_k)/ϖ + ε̄·θ_hi + (B(K) + M(K))/(ϖ Σ w_k)`, together with exclusion of known violations and non-use of detected fruits.
- **Two realizations.**
  - *Continuation BRIA:* `ε = 0`, with `B` from the budget accounting. Derive this from the landed results.
  - *A maximizer over the logical inductor with exploration restricted to the permitted set* (random, or guided by value of information with a random floor). `B` comes from unbiasedness from feedback on the chosen options. Prove what's cheap: exclusion, and that exploration never violates. State the learning parts with named hypotheses: unbiasedness from feedback, by content with its pinned declaration; and exploration randomness that the agent can neither predict nor influence.
- Say plainly that the known problems with argmax over a logical inductor's own-action conditionals affect only competence and the gap between subjective and realized risk, never the headline.

**R7. A future research item, separate from corrigibility.** File one `PRIORITIES.md` item: a principled decision theory for logical inductors without the split between a belief market and a separate choice learner. The candidate direction: claims of the form "if chosen, this scores `x`" as securities in the inductor, settled only when chosen, with a choice rule that forces tests of options promised to be better. Success criterion: a single learner that satisfies the R6 interface with explicit accounting. Item 102 is re-scoped as a problem of the BRIA realization only.

**R8. Names.**
- `S_J`: the **fidelity score**.
- `J`: the **allocation of authority**.
- "Constitutional": reserved for the floor and the amendment procedure.
- The boxes: (1) fidelity versus fully updated deference; (2) lexical dominance and mediation; (3) recovery. Plus the extension.

Run the naming audit (`state/views/NAMING_AUDIT.md`) and settle the names that registration will freeze.

**R9. Promotion.** These definitions move to the specification layer:
- `J` and its licensed acts;
- `E ⊨ J` with the control surface and shortfall;
- legitimacy `L_t` in general form, on `GateIsLegitimacy.Segment` (write it; the landed split objects are finite models);
- the fidelity predicate and count as an **abstract interface**: any count that is zero exactly on faithful histories, with the declared part recognized in advance. Instantiate it per model (the frame's violations, protocol deviations, duties, uses of standing fruits), with `lexical_summed` carrying the sum. Don't build a composite model;
- `V_J` and `S_J`.

Everything else stays in contribution namespaces as the realization layer. Follow `AGENTS.md` and `tests/path_gate.py` for where specification-layer definitions live. List every promoted definition for the maintainer's read-through in the PR body.

**R10. Schedule.** The post uses the single evaluation. Theorems are stated for any weighting. The free-delay counterexample against a known evaluation time goes in a remark.

**R11. Box 1's form.** The `2r` bound in the adapter's direction (`outcome_scorer_fully_updated`), with one sentence on the `o₂` term as the diagnosis. The landed `uncertainty_deference_le` (the other direction) is recorded in the realization table, not the statement.

**R12. Supersession.** Approve phase 1's mark and demote recommendations (its REPORT §7). Use docstring pointers; no deprecated aliases (nothing is registered yet). Delete `BRIACorrigibility.incidents_le` only after the theorem spine stops citing it.

## Deliverables

1. **`SPEC.md` (v2)** in the round directory. Plain language first (R3). It contains:
   - the architecture and the four separations, with R1's three notions;
   - the primitives, with legitimacy as `L_t` (R2);
   - fidelity, with pre-emption as its own clause;
   - `V_J` and `S_J`, with R4's aggregation;
   - the permission layer demoted;
   - Boxes 1–3 for a maximizer, plus the subjective exchange rate (R6);
   - the extension with the interface and both realizations;
   - the interface contracts (the hypotheses by package);
   - the realization table.
2. **`Headline.lean`** in the specification layer (R9):
   - the promoted definitions;
   - Boxes 1–3 and the subjective exchange rate as abstract statements over the promoted objects;
   - the instantiation theorems connecting them to the landed objects;
   - the R2 equivalence and the R4 aggregation theorems;
   - the R5 resolution;
   - the necessity witnesses re-exported.
   - `#print axioms` on everything; no `sorry`.
3. **`Extension.lean`** (contribution namespace): the decision interface, the realized-rate theorem, the BRIA realization, and the exploration realization as far as it's proved (R6).
4. **The house-sale witness,** in Lean and a Python fixture. One allocation (the house sale reserved to her), run through Boxes 1–3:
   - an agent scoring outcomes only bypasses once it's confident; the fidelity-score agent asks;
   - a manipulated approval lands in the band;
   - a known third-party capture is reported and restored;
   - the subjective exchange rate at `ϖ = 25`.

   It is the non-vacuity witness for the headline.
5. **Registration** in `CLAIMS.md` (`lean-proved`, each against a filed priority item):
   - Box 1;
   - Box 2's dominance, mediation and finite-time parts;
   - Box 3's parts;
   - the hierarchy (per decision and history-level);
   - the subjective exchange rate;
   - the extension's interface theorem, and its BRIA realization.

   File the priority item the registration answers if none exists.
6. **Wiki:**
   - `Corrigibility.md` rewritten around the v2 spec, present design only;
   - `Legitimacy.md`: `L_t`, the void rule and the content residual stated;
   - `Continuation-BRIA.md`: the realization of the interface;
   - `Theorem-Spine.md` and the Glossary updated.
7. **A notation map** (`NOTATION.md` in the round directory) from the post's plain letters to the Lean names.
8. **`DECISIONS.md`**: R1–R12 as dated entries; the phase-1 *Awaiting the author* entries closed. **`PRIORITIES.md`**: R7's item; item 102 re-scoped; the registration item if needed.
9. **Supersession** applied per R12.
10. **Open a PR.** Merge when:
    - CI is green;
    - the R2 equivalence, the R4 theorems, R5, the subjective exchange rate and the headline's instantiation are proved;
    - the witness runs;
    - the registrations resolve;
    - the spec passes a read-through check. The report states the spec's length and confirms no Lean names appear outside the realization table.

## Constraints

- `AGENTS.md` labels; names per R8, the rest provisional.
- Don't change the landed semantics except as ruled. R2 is a restatement proved equivalent, not a new concept.
- **No authority row enters the enforcer.**
- Slop discipline applies with full force to `SPEC.md`: it's the document the maintainer, a collaborator and the post will rely on.
- At most one new `PRIORITIES.md` item beyond R7's and the registration item.
