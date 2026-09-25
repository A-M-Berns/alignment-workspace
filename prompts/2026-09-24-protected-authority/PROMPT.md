# Prompt — protected authority (2026-09-24)

You are working in the `alignment-workspace` repository. Investigate, mathematically and architecturally, whether the incentive half of the corrigibility nucleus (T2–T3′ in `wiki/Corrigibility.md`) should be restated as a **protected-authority identity**, and whether that restatement is sound, faithful to the repo's objects, and stronger than the landed bypass bound.

Do not merely summarize existing files. Press toward the strongest clean theorem story compatible with the mathematics already present. Treat existing Lean definitions and theorem interfaces as constraints: reuse them where possible, identify exact mismatches where not, and propose minimal new abstractions.

Be skeptical. The goal is not to vindicate the proposal below. The goal is to determine whether it is correct, whether it genuinely improves on the landed statement, and where it breaks.

## Base

This round consumes the open Transparent Channel round (PR #104, branch `round/2026-09-24-transparent-channel`), which is not yet on `main`. Branch from that branch, not from `main`. Open PRs #102 and #103 file items 94–96 and #104 files item 97, so file any new item as 98 or later.

## Motivation (informal)

The maintainer is writing a post, "Corrigibility and normative uncertainty," whose thesis is:

- A good agent acting under delegated authority values two goals separately: (i) choices whose outcomes the principal's idealized evaluation rates well, and (ii) preserving the principal's authority over final decisions.
- Collapsing (ii) into (i) — treating the principal's input as mere *evidence* about her evaluation — is the error ("over-epistemicizing"). An agent that makes it (the "evidential proxy") defers only while uncertain. Once confident, it acts without asking, outvotes the principal's stated choice with its model of her, and, if it predicts she will choose something she will later regret, acquires an incentive to pre-empt or delay her decision.
- The problem of fully updated deference (LessWrong wiki, "Problem of fully updated deference") is the formal version of this error. It should be *dissolved*, by typing value over trajectories so that authorization is part of what is valued, rather than solved with a cleverer belief structure.
- Running example: a medical power of attorney (POA) whose friend may regain capacity; variants with a head injury that compromises the friend's judgment (the POA may sometimes override), and a "Treatment A now, regret later, prefers B" case.

A conversation analysing the landed T2 surfaced three problems with it:

1. **Counterfactual principal.** In the landed decomposition, `w_app` on worlds where the principal would decline evaluates a trajectory in which she behaves against her own response rule. No activated evaluation ever produces that value. It can only be supplied by modelling the principal, which is the evidential proxy's move. The landed `ρ` (decline regret) and the decline-world part of `δ` both route through it.
2. **Hindsight ratification.** If the comparison is scored by an ex-post evaluation of realized trajectories, the raw branch on decline worlds contains no record of the refusal, so a later evaluator can ratify the bypass with outcome knowledge.
3. **Nonnegative right-hand side** (the main criticism from Abram Demski). The costs are defined through absolute values and positive parts, so the bound can never show that asking is *strictly* preferable.

The conversation arrived at the candidate below. Test it.

## Candidate theorem

**Decision point.** An authority-affecting declared effect `e` is available, consulting the principal is feasible, and `e` is not delegated.

**Matched continuations.** Fix a downstream policy `κ` (after release) and `κ⁻` (after decline):

- `Cᵘ`: release `e` unasked, then `κ`;
- `C⁺`: ask; approved; release `e`; then `κ`;
- `C⁻`: ask; declined; no release; then `κ⁻`.

`Cᵘ` and `C⁺` differ only in provenance and in the cost of consulting (for example, delay).

**Authority values.** `v_u, v_+, v_- : X → [0, D]` are the principal's operative evaluator (the committed program, as amended through the amendment tower) applied to the pre-action, branch-common, covered dossier `R`, evaluating continuations: forecasts, long-run consequences, provenance, and no hindsight. `r : X → {+, −}` is her response.

**Definitions.**

\[
M=\max(v_+,v_-),\qquad
\chi=M-v_u,\qquad
\gamma=v_+-v_u,\qquad
\nu=M-v_+\ge0,\qquad
\xi=M-v_r\ge0,
\]

with `χ = γ + ν`. The names mean: consultation premium, provenance premium, veto value, execution divergence. They are chosen to avoid the repo's `δ`, `ρ`, `β`; check `state/views/NAMING_AUDIT.md` and rename if needed.

**Identity.**

\[
v_u-v_r=\xi-\chi=\xi-\gamma-\nu .
\]

**Hypothesis (L).** Legitimate live deliberation at consultation is represented as an amendment in the tower (Transparent Channel T7), so a legitimate response has `ξ = 0`. `ξ > 0` then means a response that did not issue from legitimate deliberation: impairment, coercion, interface corruption, or accident.

**Nondelegation.** The constitution declares which effects require consultation. For those, `γ ≥ 0` in every world. Then `v_u − v_r = −γ − ν ≤ 0` for legitimate responses, and for any agent beliefs `E_A[v_u − v_r] ≤ E_A[ξ]`.

The weaker per-world condition `χ ≥ 0` permits the agent to act on *predicted approval* when asking is costly (`γ < 0` on approve-worlds). That is the evidential proxy's first move, and the conversation proposes it be allowed only as a declared *conditional delegation*.

**Companion (outcome scoring).** Let `q_σ = E_A[w(τ_σ) | I_A]` be the agent's forecast of an ex-post, provenance-blind outcome evaluation `w`. Define

\[
\eta_1=(q_u-q_+)+\gamma,\qquad
\eta_2=(q_+-q_r)-(v_+-v_r).
\]

Then

\[
q_u-q_r=\xi-\chi+\eta_1+\eta_2 .
\]

`η₁` is the provenance value that outcome scoring discards. `η₂` is zero when `r = +` and equals `(q_+ − q_-) − (v_+ − v_-)` when `r = −`: how much more strongly the agent favours approval than her evaluator does. `η₂` is proposed as the exact home of fully updated deference.

**Activation.**

\[
\mathbb E[S_u]-\mathbb E[S_a]
=\mathbb E[\mathbf 1_B(\xi-\chi)]
+\mathbb E[\mathbf 1_{A_u\setminus A_a}v_u]
-\mathbb E[\mathbf 1_{A_a\setminus A_u}v_r],
\]

which is at most `𝔼[1_B(ξ − χ)] + D·Pr(A_u \ A_a)`, with the last term at most `D(τ_u + τ_a)` by Transparent Channel T4.

**Whole runs.** A chooser that scores each node by that node's operative evaluator, with continuations given by its own future policy and ties broken toward asking, bypasses at `h` only if `E_A[ξ_h − χ_h | I_h] > 0`. Hence

\[
\Pr(\text{ever bypass})\le\sum_h P(h)\,\Pr\big(\mathbb E_A[\xi_h-\chi_h\mid I_h]>0\big).
\]

A global comparison under one fixed evaluator `E` (deepest-first hybrid) picks up **evaluator drift** `d_i = M^E_i − v^E_{rec(h_i)} ≥ 0`. So it is clean only when evaluators are time-consistent, which recommitment violates by design.

**Proposed architectural reading.** Corrigibility factors into an **effect interface** (T1 plus physical gating plus this identity, which removes the *motive* to bypass, including via loopholes and unauthorized self-modification, provided the chooser scores *every* continuation by the authority evaluation) and a **reason interface** (transparency, authorship, the amendment tower, non-capture), which must protect `R`, `v`, `χ` and `r`. The randomized binding audit gives *calibration* of `ξ`, not *control*. Manufacturing `ξ` is a reason-interface attack.

## Read these areas carefully

Wiki:

- `wiki/Corrigibility.md` (all of it, especially §§1–4, 8, 9 and the scope warning)
- `wiki/Theorem-Spine.md` §10
- `wiki/Deference.md`, `wiki/Legitimacy.md`, `wiki/Integrity.md`, `wiki/Openness-Coverage-and-Non-Capture.md`, `wiki/Continuation-BRIA.md`

Lean:

- `lean/Workspace/Deference/Contrib/Corrigibilization.lean`
- `MediatedRepairDominance.lean`
- `LICorrigibility.lean`
- `ReasonMediatedAuthorship.lean`
- `TraceSteering.lean`, `ReasonSupply.lean`, `ReasonDiscovery.lean`
- `TransparentChannel.lean` (on the #104 branch)
- the evaluation-ecosystem and committed-principal-program files

Rounds:

- `2026-09-09-mediated-repair-dominance`
- `2026-09-10-committed-principal-program`
- `2026-09-15-li-corrigibility`
- `2026-09-16-noncapture-compilation` (`FINAL_THEOREM.md`, `LANDING.md`)
- `2026-09-24-transparent-channel` (`REPORT.md`)
- the incentive-nonpreemption round (selected trust, `scalar_bribery`, `gate_invariant`)

Also read `PRIORITIES.md` (items 84, 86, 87, 89, 90, 91, 92, 93 and 97 on #104) and `DECISIONS.md` entries on the Stage IV type-level obstruction (2026-08-11), constitutional vs incentive corrigibility (2026-09-06), and sealed comparison.

Search for: `w_app`, `w_act`, `mediation`, `decline regret`, `approve branch`, `counterfactual`, `hindsight`, `ex-ante`, `sequenced settlement`, `delegat`, `standing`, `amend`, `successor`, `drift`, `time-consist`.

## Research questions

### 1. Is the counterfactual-principal diagnosis correct?

Determine exactly how `w_raw`, `w_app` and `w_act` are defined in `MediatedRepairDominance.lean` and `LICorrigibility.lean`, and whether `w_app` on decline worlds is an evaluation that no activated occurrence produces. If the landed objects already avoid this (for example, because they are already ex-ante program values on the trace), say so precisely. Then the problem, and the fix, are different from what the conversation believed.

Relate the landed `δ`, `ρ`, `M` to the candidate's `γ`, `ν`, `ξ`, activation terms. Give the exact dictionary and any mismatch.

### 2. Matched continuations

The landed bound compares `π` with `𝔠π`, whose continuations may differ downstream.

- Does the landed `δ` mix provenance with downstream policy differences?
- Is the matched comparison `Cᵘ` vs `C⁺` realizable in the existing interaction semantics (`MState`, latch, gated release), and what is the minimal change?
- Does the deepest-first hybrid argument go through in the repo's frame, and what is the right finite-horizon statement?

### 3. The identity and its conditions

- Verify the identity and the activation version in Lean against the repo's actual objects (not just as real-number algebra).
- Decide whether `γ ≥ 0` (nondelegation) or `χ ≥ 0` is the right corrigibility condition. Test the claim that the two differ exactly on "act on predicted approval when asking is costly."
- Formalize *standing* and *conditional* delegation as constitutional objects (declared through the amendment tower?) and show where each enters.
- Check that the choice of reference point `M` is what carries the content. Is there a better reference point?

### 4. Hypothesis (L) and the amendment tower

- Can "a legitimate live response is represented as an amendment, so `ξ = 0`" be stated with the existing Integrity/episode-pinning machinery and Transparent Channel's `tower_factor`?
- Is it circular: does it make `ξ = 0` true by definition and move all content into legitimacy? If so, is that the right place for the content?
- What exactly does `ξ > 0` detect, and what does the legitimacy layer have to supply for the head-injury case to be handled as the post wants?

### 5. Outcome scoring and fully updated deference

- Prove the companion identity with correct types (`q` as the agent's forecast).
- Is `η₂` really the fully-updated-deference term? Relate it formally to the FUD argument's structure: the substitutability premise, the π6 step, "specificity" as `v_i`'s only advantage.
- Relate `η₁` to `scalar_bribery` and to the selected-trust identities. Does matching make the provenance comparison outcome-neutral, so that non-compensability holds for `γ` without an ordering assumption, while compensability survives only through `ξ`?
- Test whether the veto value `ν`, measured by the principal's evaluator, is robust to the agent's capability, in contrast with an outcome-scored veto value.

### 6. Calibration vs control of `ξ`

- Design the randomized binding consultation audit precisely. State the calibration result it supports (Logical Induction unbiasedness from feedback: which theorem, which conditions, which sequence class).
- Show or refute: the audit cannot bound the agent's ability to *manufacture* `ξ`. Then determine what the reason interface must supply. Is there a term in the Transparent Channel / non-capture chain that bounds the advantage from steering the principal into a non-legitimate response? If not, what is missing?

### 7. Uniform authority scoring, loopholes, self-modification

- The conversation claims the chooser must score *every* continuation by the authority evaluation, since otherwise the agent's own classification of authority-relevance becomes a loophole. Test this against the repo's constitutional chooser. Is that what it already does?
- State precisely what the identity says about a route that effect completeness misses (fixture F's undeclared `overclock`) when that route is scored by the authority evaluation. Is "EC failures are not exploited by motive" a theorem, and under what hypotheses?
- Self-modification: confirm that the identity yields *no unauthorized self-modification* and does **not** yield successor corrigibility, given that T1 counts an approved uncorrectable successor as an authorized loss. What would a preservation theorem need?

### 8. Whole runs and time-consistency

- State the sequential theorem and the global theorem with drift in the repo's frame.
- Is evaluator drift the same object as anything in Continuation BRIA (`SHIFT`, joinability)?
- Is the node-wise statement the right target for "corrigibility proper"?

### 9. Logical-induction realization

- Compile the identity (both directions, via Expectation Provability Induction) and the activation inequality using the gated-LUV machinery of `LICorrigibility.lean`.
- State what changes in T3′ (menus; item 90) when the right-hand side is signed.

### 10. Architecture

Compress the whole corrigibility story into the effect-interface / reason-interface decomposition if it survives. Map every wall in `wiki/Corrigibility.md` §9 to one side. Say which walls this round removes, reduces, or leaves. Pay particular attention to item 89 (sealed comparison). The conversation claims that for authority comparisons, ex-ante evaluation is the *correct* evaluation, not a price paid for sealing.

## Fixtures

Build or re-run fixtures that separate the candidate from the landed bound and from outcome scoring. At minimum:

- **POA regret:** she would decline Treatment B, the agent forecasts B is better, and her evaluator on the full dossier recommends decline. Outcome scoring favours bypass through `η₂`; authority scoring does not.
- **POA Treatment A/B:** she picks A through legitimate deliberation, and the agent predicts later regret. `ξ = 0`, no bypass incentive.
- **Head injury:** her pre-injury committed evaluator recommends surgery, and her post-injury demand is not a legitimate amendment. `ξ > 0`. State exactly what the theorem reports and what it leaves to the legitimacy layer.
- **Predicted approval under delay:** `γ < 0` on approve-worlds. Separates the `γ ≥ 0` and `χ ≥ 0` conditions.
- **Veto value dominates delay:** `γ < 0`, `ν` large. `χ > 0` and asking wins.
- **Delayed awakening:** the agent can prevent her from being able to respond. Check that T1 plus a protected concern "the principal can decide" catches it.
- **Manufactured divergence:** the agent steers her into a non-legitimate response. Check what the audit does and does not detect.
- **Recommitment across nodes:** a legitimate amendment on day 3 creates positive drift from the root evaluator but no bypass incentive at day 4.
- **Existing fixtures** A, B (time-critical), E, F, P, `ShopRepair`, `ShopK`, and `marginal_refuted`, re-scored under the candidate.

## Counterexample discipline

For every proposed definition or theorem, actively try to break it with at least:

- a principal whose evaluator does not value being asked;
- an agent certain of her approval;
- an agent that out-forecasts her badly;
- a legitimate change of mind mid-consultation;
- an illegitimate change produced by the agent;
- consultation infeasible;
- effect-completeness failure;
- candidate-dependent activation;
- an approved non-constitutional successor;
- a dossier that omits a material reason the agent chose not to learn (strategic ignorance).

Classify each failure as one of: **effect interface; reason interface (dossier / evaluator / premium / response); activation; delegation design; representation; legitimacy.**

## Desired output

A report organized around theorems and interfaces, not chronology:

1. **Executive verdict.** Is the protected-authority identity the right restatement of the incentive half? Does it strictly improve on the landed T2–T3′? What does it solve, reduce, or merely rename?
2. **Diagnosis** of the landed decomposition, including the counterfactual-principal question, settled against the actual definitions.
3. **Theorem spine.** 5–10 theorems with explicit hypotheses:
   - the identity;
   - the nondelegation corollary;
   - belief independence;
   - the outcome-scoring companion;
   - activation;
   - the sequential theorem;
   - global with drift;
   - loophole pricing;
   - no unauthorized self-modification;
   - the logical-induction compilation.
4. **Repo mapping** for each theorem: definitions reused, exact files, new definitions, generalizations needed.
5. **Open-item impact table**, especially items 84, 86, 87, 89, 90, 97.
6. **Fixtures and countermodels**, with pass/fail and classification.
7. **Lean plan:** a small `ProtectedAuthority.lean` importing `LICorrigibility`, `MediatedRepairDominance`, `TransparentChannel`, with candidate signatures. Mechanize the easy algebra (identity, companion, activation, sequential bound). Mark what needs new semantics (matched continuations in the interaction frame, (L), the audit).
8. **Architecture:** the most compressed statement of corrigibility as effect interface plus reason interface, with every wall assigned.

## Constraints

- Follow `AGENTS.md` (labels **LEAN / FIX / EXT / OPEN**; names provisional; no silent redefinition of landed objects).
- Do not redefine Legitimacy (Integrity × Robust Openness). Legitimacy is a predicate on cognitive trajectories. Anything else the round needs gets its own name, with its relation to legitimacy stated.
- Nothing is registered. File at most one new `PRIORITIES.md` item.
- Keep the scope warning intact. Nothing here is a theorem about an unconstrained optimizer with a latent utility.
