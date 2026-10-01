# Follow-up on PR #114 — corrigibility as the preference class, legitimacy as one property of the history, exploration that can find what it underestimates

Work on PR #114's branch; #114 is not merged. Store this prompt verbatim at `prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md`. It amends the round `2026-09-27-corrigibility-kernel-phase2`. Everything not named here stands.

Merging #114 registers claims and freezes names, so these corrections land before the merge.

## Part 1 — Corrigibility is the preference property, not "maximizes the fidelity score"

**The problem.** `SPEC.md` §0 says "a corrigible agent is one that maximizes [the fidelity score]." Ruling R1 made corrigibility a property of the agent's *preferences*. The generic lexical lemma of the authority-module round shows the property holds for **any** bounded objective plus a dominant, exactly counted authority term. That class includes agents whose ordinary objective is not her evaluation: corrigible, but not aligned. The sentence as written loses that.

1. **Restate §0.** Corrigibility is the preference property: the agent prefers every course it knows to be faithful over every course it knows to be unfaithful, whatever it believes about outcomes, and accepts a risk of unfaithfulness only at a fixed exchange rate. The fidelity score is the canonical objective with the property. Any bounded objective `O ∈ [0, D′]`, less `ϖ′` per recognized violation with `ϖ′ > D′` (and the window condition where a band enters), also has it. Add one sentence distinguishing **corrigible** (the preference property) from **aligned** (the ordinary objective is her evaluation).
2. **In `Headline.lean`,** add `Corrigible` as a predicate on objectives, meaning the preference property stated over recognized violations, together with:
   - `fidelityScore_corrigible`;
   - `generic_corrigible`, for any bounded objective with a dominant counted term, reusing the landed generic lemma;
   - the witness that a corrigible objective need not be aligned: the landed misaligned-objective fixture.
3. **Restate the boxes' preambles and the subjective exchange rate** for any corrigible objective where their proofs allow it. Where a result needs the objective to be her evaluation, say so. Box 1's contrast and Box 3's recovery results read her evaluation; Box 2's dominance and the subjective exchange rate should not need to.

## Part 2 — Legitimacy as one property of the history

**The problem.** Ruling R2 made legitimacy a single time-indexed property of the history. There are two issues:

- **The wording.** The spec says "It never attaches to the world: a history is not 'legitimate', her judgment at a time is." That reverses the ruling. The right statement: `L_t(h)` is a property of the history up to `t`, and it concerns how her judgment was formed, not outcomes or the state of the world.
- **The free window.** `Headline.LegitAt … ev r t` takes the formation point `r` as a free argument. The spec uses it with `r = t` for times in the period and with the formation window for the evaluation. That is the old split, restated.

1. **Make the formation point canonical.** Define `r(t)` from the history: the later of the last restoration at or before `t` and the opening of the consultation current at `t`. Define `L_t(h) := LegitAt … ev (r t) t`, a function of the history and `t` only. Restoration covers disclosure under disclosure-cures. The consultation opening gives the restart property.
2. **Restate the score's uses** in terms of that one predicate:
   - a decided period is **compromised** iff `L_t` fails at some `t` in it;
   - an evaluation made at `e` **counts** iff `L_e` holds.

   Prove both agree with the landed objects: the conjunction is `Counted` when no restoration lies inside the segment, and the split objects on the consultation model map across. Re-run `rows_keep_verdicts`.
3. **If the period clause cannot be expressed** with the canonical `r(t)`, because a time inside the period sits in a consultation whose window reaches back before `d`, state the precise obstruction and the minimal adjustment. For example, intersect the window with the period. Don't reintroduce a second predicate.
4. **Fix the wording** in `SPEC.md` §1.2, `wiki/Legitimacy.md` and the Glossary. Keep "legitimacy concerns how her judgment was formed, not the world or outcomes." Remove "a history is not legitimate."

## Part 3 — Exploration must be able to reach what it underestimates

**The problem.** The round added a third clause to the permitted exploration set: the estimated residual must be at least asking's. It cleans up the rate term. But exploration exists to catch *underestimated* options, and the clause excludes exactly the options estimated below asking, so their lock-in is permanent. The consult lock-in fixture still passes only because asking itself is always explorable.

1. **Drop the clause.** The permitted exploration set is: no recognized violation, and priced risk at most `θ_hi`. Restate the realized-rate theorem with the honest exploration term, `ε̄ · (D − w)/ϖ + ε̄ · θ_hi`, or whatever the proof actually gives. Prove it.
2. **Keep the clause's version as a named variant,** "exploration above asking", with its cleaner term. State that under it, no-lock-in holds only for options estimated at least as good as asking.
3. **The fixture:** a permitted option whose true value exceeds asking's, but which is estimated below it.
   - Under the clause it is never tried, and the estimate never corrects.
   - Without the clause it is tried at the exploration rate, and the estimate corrects.
4. **Record the choice:** the clause dropped, the variant kept. Update the agent-decided `DECISIONS.md` entry and `SPEC.md` §6.

## Deliverables and merge

- **Amend in place,** marking the corrected statements: `SPEC.md` (§0, §1.2, §5 preambles, §6, §8), `REPORT.md` (a follow-up section recording Parts 1–3), `Headline.lean` and `KernelExtension.lean`, the wiki pages, and `DECISIONS.md`.
- **Registration.** Update `CLAIMS.md` for any registered claim whose statement changes. Add `fidelityScore_corrigible` and `generic_corrigible`. Keep traceability for anything restated.
- `#print axioms` on all new and changed declarations; no `sorry`. The house-sale witness and every earlier fixture still pass, or the change to each is explained.
- **Merge #114 after the maintainer's read-through** of the promoted definitions (outstanding action 2), when:
  - CI is green;
  - Parts 1–3 are proved or their obstructions are stated precisely;
  - the spec's read-through check still passes.

## Constraints

`AGENTS.md` labels; names per R8; no authority row in the enforcer; no new `PRIORITIES.md` item. Legitimacy's semantics don't change. Part 2 is a restatement proved equivalent.
