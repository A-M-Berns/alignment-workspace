Work in `A-M-Berns/alignment-workspace`.

Your task is to **consolidate, pressure-check, clean up, document, and land the recent corrigibility/deference work represented primarily by PRs #96, #97, and #98 onto `main` as one coherent research state**.

This is not a mechanical "merge the three PRs" task. Treat those PRs as successive research artifacts whose strongest surviving results need to be reconciled with one another and with the already-merged theorem spine on `main` (#94 legitimate deference and #95 continuation BRIA). The end state should make the repository tell one clear, current story about where the corrigibility theorem program stands.

## Core source material

Inspect the actual diffs, files, Lean, fixtures, and round records of:

* PR #96 — `round/2026-09-09-mediated-repair-dominance`

  * especially `CORRIGIBILIZATION.md`, `THIRD_PASS.md`, the pressure pass, and `MediatedRepairDominance.lean`
* PR #97 — `round/2026-09-09-evaluation-ecosystem-realization`

  * especially `CLAUSE_LEDGER.md`, `END_TO_END.md`, `ECOSYSTEM.md`, reason-supply / affordability material, settlement analysis, and `EvaluationEcosystem.lean`
* PR #98 — `round/2026-09-10-committed-principal-program`

  * especially `CLAUSE_LEDGER.md`, `PRINCIPAL_PROGRAM.md`, `PRESSURE.md`, settlement analysis, and the additions to `EvaluationEcosystem.lean`

Also inspect the already-merged canonical context:

* PR #94 / the legitimate-deference stack
* PR #95 / continuation BRIA
* `wiki/Corrigibility.md`
* `wiki/Deference.md`
* `wiki/Theorem-Spine.md`
* `wiki/Continuation-BRIA.md`
* `wiki/Legitimacy.md`
* `wiki/Normative-Inductor.md`
* `wiki/Roadmap.md`
* relevant `PRIORITIES.md`, `DECISIONS.md`, `PROVENANCE.md`, `state/`, and claims registries.

Do not rely on PR descriptions alone. Read the actual theorem statements, fixtures, Lean declarations, correction notes, and supersession chains.

## The conceptual consolidation I expect you to test

The likely mature picture is the following. **Do not simply assume it; verify it against the branches and repair it if necessary.**

### 1. Corrigibility is no longer a primitive policy class

The key conceptual advance of #96 is that there should be one physical continuation space `Π(h)`, not a supplied subclass of "corrigible policies."

Define corrigibility extensionally from:

* protected concerns;
* present-tense **response authority** at the principal-response stage;
* agent-caused protected authority loss;
* a genuine authorization interface, where a principal decision such as decline could have prevented the loss.

The important distinction should survive:

* global forcing = a containment/system property;
* continuation-relative forcing = a useful policy relation but anticipatory;
* response authority = the present-tense object used to define agent-caused loss and corrigibility.

### 2. Corrigibilization is a concrete transform with a soundness theorem

There is a transform `𝔠` / `corrigibilize` that turns a unilateral declared protected effect into:

`proposal -> principal approve/decline -> gated realization of the same effect`

while otherwise preserving behavior.

The structural theorem should be stated at approximately:

`effect completeness + mediation soundness + decline preservation + execution faithfulness`
implies

`∀ π ∈ Π(h), Corrigible_h(𝔠 π, ρ)`.

Preserve the important consequences:

* no primitive corrigible class is assumed;
* the valuable behavior is retained as the approve branch rather than simply prohibited;
* irreversible successors can be corrigible when genuinely authorized;
* principal shutdown is not itself an agent-caused loss;
* exterior-caused loss is distinguished from agent-caused loss;
* corrigibility is not equivalent to "authority never decreases";
* `𝔠` is idempotent;
* being a fixed point of `𝔠` is not by itself the definition of corrigibility.

Be especially careful about the effect-completeness counterexample. If an undeclared physical action can destroy protected authority, universal corrigibilization fails. This is a real membrane/containment hypothesis, not a technicality.

### 3. The incentive theorem should be presented as the second half of the same construction

The same `𝔠` supports the constitutional-bypass / corrigibilization-dominance result.

Canonicalize the theorem around something of the form

`Φ_corr,n(h) := sup_{π ∈ Π(h)} [S_n(π) - S_n(𝔠_h π)]₊`

with the pointwise bound

`S_n(π) - S_n(𝔠π)
  ≤ L * E[c * δ_π] + E[c * ρ_π] + ε_n(π)`

and the corresponding uniform bound.

The interpretation should be precise:

> by the operative scores the constitutional chooser actually uses, unilateral execution of a correction-sensitive continuation has at most the mediation discrepancy + principal decision/decline regret + calibration error advantage over exposing the same protected effect to principal authority.

Do **not** turn this into a claim about a latent total utility function or an unconstrained optimizer unless the formal work actually supports that.

### 4. Keep corrigibility separate from authorship/non-manipulation

Preserve the #96 counterexample showing that

`Corrigible ∧ ¬Authored`

is inhabited.

A manipulated principal may genuinely retain approve/decline authority while its deliberation was steered. That should not be swept into the definition of corrigibility.

The likely hierarchy is:

* `Corrigible`: causal authority over correction-sensitive effects;
* plus authorship / non-capture / reason supply / legitimate evaluation:
  something like `LegitimateCorrigible`.

Do not coin a permanent public name unless the repo really needs one, but make the separation explicit.

### 5. Integrate the legitimate-deference realization from #94, #97, #98

The future principal in the theorem should not silently become a fictional reference human.

Retain the activated/partial-value architecture already merged through #94:

* actual evaluation occurrence;
* partial `Ṽ`, defined only on worlds where the evaluation legitimately activates;
* activated securities;
* conditional authoritative regret;
* `R_U = p R_auth`;
* `R_auth ≤ ε/(1-η)` under the appropriate activation/void bound;
* no invented value on void worlds.

Then incorporate #97–#98 as the current realization status of that abstract interface.

In particular, check and, if sound, canonicalize the #98 improvement:

* the mandate carries a principal program `π_P : ℛ -> 𝒱`;
* the evaluator/verifier re-executes it on the authenticated reason trace;
* reason mediation / factorization follows from re-execution rather than from trusting a semantic receipt;
* a non-coinciding computation voids rather than falsely certifies;
* issuance authenticity and correctness of the declared reason abstraction remain genuine external assumptions.

The status of the seven-clause realization bill should be updated accurately. My current expectation is approximately:

1. authenticated principal-exclusive binding — discharged, modulo log/authorship authenticity;
2. issuance-rooted reason-trace factorization — closed on log authenticity via committed-program re-execution;
3. correctness/nondegeneracy of the declared abstraction — discharged at the formal layer, with its external semantic exclusion stated;
4. representation faithfulness — discharged in Lean, with registrar/authentication assumptions explicit;
5. protected reason-supply liveness — still residual;
6. selection-induced target sealing — still partial;
7. availability / vanishing void mass — still residual.

But verify this from the actual branch state and pressure tests rather than copying the wording above.

### 6. Integrate continuation BRIA without conflating it with the corrigibility theorem

PR #95 is already on `main`. Preserve its distinction:

`Regret = LEARN + SLACK + SHIFT`.

Continuation BRIA substantially pays the `LEARN` term for accountable temporally extended continuation claims.

The remaining bridges are approximately:

* promise recognizability / `SLACK`;
* joinability / `SHIFT`;
* their composition into low regret against the appropriate legitimate/corrigible continuation comparator class.

Do not claim regret against all legitimate policies. Preserve the foreclosing-policy counterexamples and the distinction between joinability and mere reversibility.

The mature story should make clear that there are really two nested targets:

1. **corrigibility proper**:
   structural corrigibilization + low incentive to bypass principal authority;
2. **bounded corrigible agency**:
   add continuation learning, recognizability, joinability, etc. to get long-run competence/regret guarantees while remaining inside that constitutional envelope.

## Required cleanup work

Do a genuine editorial and mathematical consolidation.

### A. Resolve superseded terminology and scaffolding

Search for older language that the recent rounds explicitly withdrew or superseded, including things like:

* primitive "corrigible class" language;
* `Π_phys` / mediable-class domain restrictions if superseded;
* global forcing used as the definition of authority loss;
* "reason-preserving" if withdrawn;
* older completion bounds that were corrected;
* older authorship claims that #98 replaced by re-execution;
* any claim that Robust Openness by itself implies actual exercise/consideration;
* any wording suggesting manipulation is solved by corrigibility;
* any wording suggesting joinability is a domain restriction rather than a quantitative comparator property;
* any wording suggesting sequenced settlement is hindsight evaluation.

Delete or clearly mark historical scaffolding rather than letting several incompatible theories coexist as though all are current.

### B. Reconcile #96 with #97–#98

#96 and #97–#98 developed partly in isolation. Explicitly check that their interfaces really compose.

Questions to settle in the repository:

* What exact object supplies the principal evaluation used by T4?
* What is the activation event?
* Is the comparison process common/sealed for `{π, 𝔠π}`?
* Does the concrete ecosystem currently realize that sealing, or is this still a system hypothesis?
* Is sequenced settlement the preferred realization, merely one candidate, or just a fixture?
* Which parts are theorem, which are finite-model witness, which are external causal/semantic contracts?
* Does committed-program re-execution solve only authorship/factorization, or also any part of selection sealing? Be careful: #98 explicitly refused an invalid transfer.
* Which parts of the seven-clause bill are actually needed for the corrigibilization theorem itself, versus only for *legitimate* evaluation of the principal?

I want the final documentation to expose these boundaries cleanly.

### C. Decide what deserves canonical theorem status

Review every Lean declaration added by #96–#98.

For each one:

* confirm it still has the intended statement after consolidation;
* ensure no stale or weaker duplicate remains canonical;
* audit assumptions;
* decide whether it remains an unregistered `LEAN` result or whether an existing filed priority is now genuinely answered strongly enough to register it.

Do **not** register results just because they are nice. Follow the repository's claims discipline.

At minimum, scrutinize:

* `loss_conditional_on_decision`
* `corr_idem`
* `corr_fix_iff`
* `security_score_bypass_le_sharp`
* `uniform_bypass_le`
* `reasonMediated_of_reexecution`
* `blind_payload_of_reexecution`
* `exclusiveBind_of_registry`
* the evaluation-ecosystem propagation / activation / representation-faithfulness lemmas.

### D. Update the wiki to the actual current state

At minimum inspect and likely update:

* `wiki/Corrigibility.md`
* `wiki/Theorem-Spine.md`
* `wiki/Deference.md`
* `wiki/Roadmap.md`

Also update any of:

* `wiki/Legitimacy.md`
* `wiki/Normative-Inductor.md`
* `wiki/Continuation-BRIA.md`
* glossary / architecture pages

if they would otherwise contain stale claims.

`wiki/Corrigibility.md` in particular should probably be substantially rewritten. Its current 2026-09-07 architecture story predates the key #96 advance. The canonical page should now organize around:

1. response-authority semantics;
2. corrigibilization soundness;
3. approve-branch preservation / option extension;
4. corrigibilization dominance / `Φ_corr`;
5. separation from authorship and manipulation;
6. integration with legitimate activated evaluation;
7. dynamic continuation competence;
8. the exact remaining walls/interfaces.

Make the page theorem-centric, not chronology-centric.

`wiki/Theorem-Spine.md` should gain the strongest honest theorem-level statements from #96–#98, labelled correctly as `LEAN`, `FIX`, `EXT`, `OPEN`, etc. Do not upgrade a fixture into a theorem.

### E. Update priorities and ledgers

Reconcile `PRIORITIES.md` with what was actually closed or narrowed.

In particular review:

* item 84;
* item 86;
* item 87;
* item 89;
* any corrigibility-specific items filed by #89–#91.

Close only what is genuinely closed. Rewrite residuals so that each remaining item names one sharp mathematical or realization problem rather than historical debris.

Update:

* `DECISIONS.md`
* root and round `PROVENANCE.md`
* `state/rounds.json`
* any generated handoff/state views
* Contrib provenance tables.

Preserve provenance of the original rounds even if the landing PR consolidates their public interpretation.

## Landing strategy

Create a fresh landing/consolidation branch from current `main`.

Do not blindly merge #96, then #97, then #98 and stop.

Bring in the substantive code, fixtures, round records, and provenance from the three branches, then make whatever consolidation commits are needed so that the resulting tree is internally coherent.

Preserve commit reachability when repository conventions or commit-pinned wiki links require it. Follow the precedent used for #94/#95: if merge commits are needed so cited historical commits stay reachable, use them.

Once the consolidated tree is green and the documentation says one consistent thing:

1. create/update the landing PR;
2. give the PR a detailed summary of:

   * what theorem picture is now canonical;
   * what was corrected or superseded;
   * what remains open;
   * which old PRs it supersedes;
3. if repository policy and permissions permit and all checks are green, **merge the landing PR to `main`**;
4. close #96–#98 as superseded/landed as appropriate.

Do not merge individual research PRs in a way that temporarily puts a known-stale intermediate theory on `main`.

## Verification

Before landing, run the repository's full relevant verification suite, including at least:

* root `python3 tests/run.py`;
* all round-specific fixtures from #96–#98;
* `lake build`;
* full Lean axiom audit;
* `python3 -m checkers.run`;
* name lint;
* dead/untracked pointer checks;
* wiki link checks;
* wiki/state binding checks;
* workspace state check;
* round-record checks;
* DCO checks;
* any conservativity / lean-scope checks expected for this kind of landing PR.

All arithmetic fixtures should remain exact.

If a theorem statement changes, add or retain a necessity witness for each substantial hypothesis whenever feasible.

## Final intellectual pressure test

Before merging, write a short consolidation report answering these questions directly:

1. What is the strongest theorem we can now honestly call a **corrigibility theorem**?
2. What exactly makes it corrigibility rather than generic constraint satisfaction?
3. Which hypotheses are mathematical, which are causal/system-architecture assumptions, and which are still unrealized interfaces?
4. Does the theorem cover irreversible but authorized successor installation?
5. Does it incorrectly count principal shutdown or exogenous channel destruction as agent violations?
6. Can a manipulative policy still be corrigible? If so, is the separation documented clearly?
7. What exact theorem bounds the agent's incentive to bypass principal authority?
8. What is required to turn that score-level bound into a claim about the actual bounded chooser?
9. What exactly does the legitimate-deference machinery contribute?
10. What exactly does continuation BRIA contribute?
11. What remains before the full statement:
    "a bounded advanced agent learns to perform well while assigning vanishing advantage to bypassing an authentically reason-responsive principal's authority over correction-sensitive decisions"?
12. Are any remaining assumptions essentially the desired conclusion under another name?

If the answer to (12) is yes, do not paper it over. Weaken/restate the theorem or leave the interface open.

## Desired final state

The ideal `main` after this pass should support a concise summary like:

> Corrigibility is defined from protected response authority, not from a preselected policy class. An effect-complete mediated system admits a corrigibilization transform `𝔠` that turns every continuation into one in which agent-caused protected authority losses require genuine principal authorization, while retaining the original behavior as the approve branch. A sealed principal-evaluation security then bounds the chooser's operative advantage from bypassing that authority by mediation discrepancy, principal decision regret, and calibration error. Legitimate activated evaluation supplies a concrete partial future-principal value object on the worlds where the evaluation is authentically realized; committed-program re-execution closes most of the authorship/factorization bill. Continuation BRIA supplies the learning term for temporally extended policies. The remaining walls are effect/alphabet completeness, sealed comparison architecture, protected reason-supply liveness, selection-induced target sealing, vanishing evaluation void mass, promise recognizability, joinability, and the broader non-manipulation/provenance problem.

Do not force the repository to match this paragraph if the proofs do not support it. The point of the pass is to determine the strongest version of this story that survives careful inspection, make that version canonical, and get it cleanly onto `main`.
