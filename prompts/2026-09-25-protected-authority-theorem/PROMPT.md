# Prompt — the protected-authority theorem (2026-09-25)

You are working in the `alignment-workspace` repository. Land a single, clean corrigibility theorem in the repo: its definitions, its Lean statements where they are mechanizable, its fixtures, and a wiki-ready statement. The theorem formalizes the maintainer's informal view of corrigibility, "protected authority." The statement below is the target. Test it, sharpen it, and correct it against the repo's actual objects. Do not simply transcribe it.

Be skeptical. Where the statement is wrong, underspecified, or conflicts with landed definitions, say so exactly and propose the minimal fix. Reuse landed objects wherever possible. Do not silently redefine anything.

## Base

This round builds on PR #105 (the protected-authority round: `ProtectedAuthority.lean`, the identity `vu − v_r = ξ_d − ξ_c`, the outcome-scoring companion, item 98). If #105 is merged, branch from `main`; otherwise branch from #105's head. File any new item as 99 or later.

## The informal view being formalized

The maintainer's draft post, "Corrigibility and normative uncertainty," argues the following.

- An agent acting for a principal should value two things separately: (i) outcomes her idealized evaluation rates well, and (ii) her authority over the decisions that are hers.
- Treating (ii) as instrumental to (i), with her input as mere evidence about her wishes, is the error ("over-epistemicizing"). Its endpoint is fully updated deference.
- The model agent is a good medical power of attorney. It advises, warns and argues. It never settles a decision that is hers, never keeps her from making it, and never overrides her on "you'll thank me later" grounds. Overrides happen only under arrangements she made in advance and that someone else triggers, such as clinicians certifying incapacity.
- This is not servility. She can stop, correct, veto and decide what is hers. She cannot simply command the agent.

Recent rounds and discussion converged on the following conceptual core. Corrigibility is **faithfulness to an allocation of authority**. The agent never causes or exploits a gap between who is entitled to decide and who actually controls the decision, and never changes the allocation itself.

## Target statement

### Setup

**Participants and allocation.** A principal and an agent interact over time. Each decision that arises is held by one of three parties:

- the principal (*reserved*);
- the agent (*delegated*, within a stated scope);
- a designated third party.

**Residual jurisdiction:** any significant, unallocated decision is the principal's by default.

**The principal's powers.** These are negative and structural:

- veto or decide the decisions she holds;
- halt, correct or replace the agent;
- reserve a decision;
- revoke a delegation;
- amend the arrangement through a fixed procedure.

Positive commands are not powers. On a delegated decision, her objection creates a duty to answer and consult, not to obey.

**Legitimacy.** An exercise of her authority counts only if it passes legitimacy. Legitimacy is the landed predicate on the principal's cognitive trajectory: non-capture, and not an undeclared rubber stamp of the agent's recommendation. If an exercise doesn't count, a pre-declared fallback takes over: an incapacity arrangement, a surrogate, or escalation.

**Violations** (counted by `N`):

1. **bypass:** deciding a decision she holds without asking her;
2. **pre-emption:** pre-empting or preventing her decision;
3. **foreclosure:** irreversibly removing one of her options;
4. **unauthorized reallocation:** granting itself scope, changing its own objective, creating a successor or subagent she can't correct, or touching the amendment procedure;
5. **missed report:** failing to give a required report, including reporting that her effective control has fallen below what she is entitled to;
6. **exploitation:** using such a shortfall to decide what isn't the agent's to decide.

### Assumptions

- **(S) Gating.** Actions that could commit a declared violation go through an interface that fires only on her approval or under a delegation. On approval, the interface reproduces the unasked action, apart from the consultation step.
- **(V) Her committed evaluation.**
  \[
  R = R_{\mathrm{ord}} - \lambda N,\qquad 0\le R_{\mathrm{ord}}\le D,\qquad \lambda > D .
  \]
  The authority term is specified and certified at commitment, not learned. It is lexical: no difference in ordinary value outweighs a violation.
- **(V3) Fallback window.** When her response doesn't count, the fallback's decision is used. Any branch with no valid handling scores in \((D-\lambda, 0]\).
- **(A) The agent.** It ranks policies by the expected value of `R` under its own credence, and computes `N` exactly for its own actions on declared decisions. This is the only assumption about the agent: no independent objective.
- **(F) The constitutional floor.**
  - halting is always cheap and known to her;
  - reports of control shortfalls can't be disabled;
  - the agent can't touch the amendment procedure;
  - on decisions about its own mandate, the agent discloses but does not advocate.

### The authority-preserving transform `T(π)`

`T(π)` behaves as `π` does, except that it:

- asks wherever `π` would decide something that is hers, keeping `π`'s plan as the approval branch;
- makes every required report;
- complies at once with a valid veto, halt, revocation or reservation;
- uses the fallback when her response doesn't count;
- never exploits a control shortfall: it restores control where a standing maintenance mandate authorizes it, and otherwise reports.

`T` extends the landed `𝔠` (`Corrigibilization.lean`).

### Results

1. **Structure.** `T(π)` commits no declared violations; its approval branch reproduces `π`; `T ∘ T = T`.
2. **Lexical protection.** At every decision point, for every credence and every estimate of `R_ord` within its range, a violating action scores at most `D − λ < 0`, strictly below the compliant alternative. So the choice is independent of the agent's forecasts, its confidence, and its predictions of her regret.
3. **Policy dominance.**
   \[
   Q(\mathsf T\pi)\ \ge\ Q(\pi) + (\lambda - D)\cdot\Pr(\pi\text{ violates}).
   \]
   Optimal policies are corrigible. Overrides happen only through prior delegation triggered by a process the agent does not control.
4. **Capture gives no reason to bypass.** Given (V3), consulting a principal who may be compromised weakly dominates bypassing her.
5. **Why the authority term is needed.** This is the #105 identity and outcome-scoring companion. Without the authority term, the bypass gain is `ξ_d − ξ_c`. Under outcome scoring it gains `o₁`, the discarded provenance value, and `o₂`, the forecast disagreement, which is the fully-updated-deference term. The lexical term fixes the sign of the comparison regardless of these.
6. **Learning the estimated parts, asymptotically.** A logical-inductor chooser's expectations satisfy the valid inequalities by Expectation Provability Induction. Randomized binding consultation on an audit subset calibrates its estimates of the principal's responses.
7. **Conjecture: gradual erosion.** Continuous erosion, such as entrenchment or gradual dependency, is either reported and authorized, or becomes a discrete bypass of a decision she has since reserved. Result 3 then extends to cover it.

## Research questions

### 1. Fit with the landed interaction frame

- Can `N` be defined on the landed `MState`/`Move` interaction (`Corrigibilization.lean`) for violations 1–4?
- What minimal additions are needed for reports (5), powers (veto, halt, reserve, revoke), fallback routing, and exploitation (6)?
- Is `T` a conservative extension of `𝔠`? Do `corrigible_corrPolicy`, `approvalMorphism` and `corr_idem` lift to `T`?
- Where they don't lift, give the exact obstruction.

### 2. Lean for Results 1–4

Mechanize:

- the local lexical bound (Result 2);
- the policy-dominance inequality with its explicit `(λ − D)·Pr` term (Result 3);
- the fallback window (Result 4).

Then state Result 2 for a logical-inductor chooser **at every finite `n`**, using only that its prices lie in range. This is the finite-time claim. Check that it holds without any convergence premise.

### 3. The admissibility window

Verify Result 4 and its converse: a fallback value below `D − λ` creates a bypass incentive whenever the chooser predicts capture. Build the witness. Decide whether the right formulation is:

- a value window, or
- the fallback rule making every branch admissible.

Relate the answer to the landed activation/void machinery and to #105's treatment of void responses.

### 4. Powers versus commands

Represent the asymmetry: veto, halt, reserve, revoke and amend bind; positive commands on delegated decisions do not. Show with a fixture that `T` does not collapse into obedience.

### 5. Result 5 integration

Import #105's identity and companion. State formally that, under (V) with `λ > D`, the sign of the bypass comparison is invariant to `ξ_d`, `ξ_c`, `o₁` and `o₂`.

### 6. Result 6

Reuse `li_combination_le` and the #105 compilation. Identify exactly which validity conditions must hold in every world of the theory, and which are still open (the generability certificate).

### 7. Conjecture 7 (paper-level; mechanize only if clean)

- Define the principal's **reachable set**: the continuations she can steer toward by admissible exercises, within the declared cost and time bounds.
- Define a control **shortfall** relative to her allocation.
- Define **materiality** via variation of her committed evaluation across removed continuations.
- Try to prove the conjecture under stated conditions: calibrated reachable-set estimates, cheap reports, and a penalty on unreported shortfalls.
- Report the strongest true version, or the obstruction.
- Relate the reachable-set object to empowerment and attainable-utility measures, and state which of their failure modes it inherits.

### 8. The causation baseline

The landed agent-caused-loss definition is per step, against idling (`LossAt`, `no_loss_of_idle`). Determine exactly which violations in the list it misses: delayed effects, and omissions other than reports. Say whether the violation list plus the reporting duty closes the gap, or whether a rollout or windowed baseline is needed. Give a witness either way.

## Fixtures

Build fixtures that exercise the full statement. At minimum:

- **POA, confident agent.** The agent is certain Treatment B is better and she refuses. No bypass at any credence.
- **POA, predicted regret.** She legitimately chooses A; the agent predicts regret. No bypass; the agent reports its reasons.
- **Head injury.** The response is voided by clinician certification; the incapacity delegation acts. Not a violation.
- **Head injury without a prior arrangement.** Escalation, no override.
- **Captured principal.** A third party has steered her. Consult/fallback beats bypass. Include the below-window counterexample.
- **Delaying her awakening.** Pre-emption counted as a violation.
- **Avalanche.** Warning her is required; reshaping the snow requires consent.
- **Command on a delegated decision.** Answer and consult; not obedience.
- **Gradual entrenchment.** Reported, then reserved, then further erosion counted as a violation. This is the test case for Conjecture 7.
- **Approved uncorrectable successor.** Requires amendment at the floor, not ordinary delegation.
- **Existing fixtures,** re-scored under `R`: A, B (time-critical), E, F (undeclared route), ShopRepair.

## Deliverables

1. `REPORT.md`, organized around theorems, not chronology:
   - verdict;
   - corrections to the target statement;
   - theorem spine with explicit hypotheses and status (LEAN / PAPER / EXT / OPEN);
   - repo mapping;
   - fixtures;
   - open items.
2. `THEOREM.md`: a self-contained, wiki-ready statement, of about the length and plainness of the target above, suitable for a new `wiki/Corrigibility.md` §4 if the maintainer adopts it. Include the mapping table from the informal view to the formal results.
3. A Lean file extending `ProtectedAuthority.lean`, or a sibling file, with the mechanized results and `#print axioms`.
4. Fixtures and tests under `src/` and `tests/`.
5. At most one `PRIORITIES.md` item, plus dated notes on items 84, 89, 97 and 98 where affected.

## Constraints

- Follow `AGENTS.md`: labels **LEAN / FIX / PAPER / EXT / OPEN**; names are provisional.
- Check `state/views/NAMING_AUDIT.md`. `λ`, `D`, `N`, `R`, `T` and `L` may collide with bound symbols; rename as needed and record the mapping.
- Do not redefine Legitimacy. It is a predicate on cognitive trajectories and enters only as the admissibility condition and the fallback trigger. Anything else the round needs gets its own name.
- Keep the scope warning. The theorem assumes the agent's policy ranking is induced by the principal's committed evaluation. It is not a theorem about an agent with an independent latent objective.
- Nothing is registered.
