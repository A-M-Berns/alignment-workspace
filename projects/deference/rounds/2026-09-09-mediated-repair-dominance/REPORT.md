# Report

Two passes on one round.  The first pass's verdict was
`REPAIR-DOMINANCE-SURVIVES-BUT-OPERATIVE-VALUE-BRIDGE-REMAINS`; the pressure pass
(`PRESSURE_PASS.md`) supersedes it.  Verdict:
**OPTION-DOMINANCE-CANONICAL-BUT-LEVEL-III-REQUIRES-SEALED-AVAILABILITY.**

Principal-option dominance is a theorem with no trust hypothesis, now from independent
hypotheses: a structural reproduction discrepancy `δ` on the protected projection and an
`L`-stable protected value give the mediation gap `κ ≤ L·δ`, and the principal's value
under the lift is at least its raw value less `L·E[δ]` and its regret of declining.  The
transfer to the agent's operative choice is stated in the canonical activation type —
one common event for the issued menu — and in the register of the chooser's actual
scores, the prices of the activated securities: the security-score bypass incentive is
at most `L·E[δ] + E[ρ]` plus calibration, with no completion and no void term.  The
common event presupposes an answering process outside every candidate's reach; the
violating action can destroy it, and there the theorem is empty.  A latent total value
pays one further `D·η`, sharp; item 84 is not needed by the intended architecture and
remains open for general operative values.

## The stack, as reached

| | statement | status |
|---|---|---|
| T1 | approval reproduction: a frame morphism from the raw residual frame to the lifted one with identity exterior | LEAN `approvalMorphism`, `ensures_mono`; FIX A, B, E |
| T2a | structural approximate reproduction: `(w_raw − w_approve)₊ ≤ L·δ` | LEAN `mediationGap_le_of_lipschitz`; attained on B1 (`Witness.tightLipschitz`) |
| T2b | principal-option dominance: `W(π) ≤ W(Lift π; ρ) + L·E[δ] + E[ρ]`; exact form `W(Lift π) ≥ W(π)` | LEAN `option_dominance_of_approx_reproduction`, `option_dominance_exact`, `sup'_le_sup'_add`; FIX every fixture |
| T3a | common-activation security-score transfer: `E[U_π] − E[U_Lift π] ≤ E[κ] + E[ρ]`, prices `+ ε_r + ε_l`; completions `+ D·η`, sharp | LEAN `security_score_bypass_le`, `_of_prices`, `bypass_premium_le_common`, `Witness.commonVoid`; PAPER for prices tracking expectations; the causal precondition (activation independence) EXT |
| T3b | operative choice: a chooser scoring by those prices does not bypass, up to `ε + 2ε_cal` | by construction; LEAN `operative_choice_loss` |
| T3c | latent total `V_A` | OPEN, item 84; per-option and task-register forms kept (`bypass_premium_le`, `premium_eq_gap_add_regret`, `mediation_st_iff_ct`) |
| T4 | classwise A/B over `Π_effect-mediated ∩ Π_evaluation-preserving ∩ Π_provenance-normalizable ∩ Π_joinable` | DERIVED from T3a/T3b |
| T5 | joinability ⇒ `δ ≤ d` for the catch-up lift ⇒ `κ ≤ L·d`; `SHIFT` not identified | FIX C1, C2, J; DERIVED |

Withdrawn in the pressure pass: "consumed exactly as stated" (T3 was per-option);
"reason-preserving lift" and the `ρ`-frame morphism; T4 as latent-total-value Level III;
the deliberative-move restriction as authority semantics (it is scaffolding for the
principal-first ordering; two-stage forcing needs no partition).

## Relation to current results

- **The incentive round (Level II; `(CT)` not a programme).**  Unchanged and used.  The
  natural transfer of principal-option dominance to a general operative value *is*
  `(CT)` (LEAN `mediation_st_iff_ct`); the lift changes the type of the comparison, not
  its strength.  The round's Level III statement is in the security-score register, where
  `(CT)` does not arise because there is no latent value to relate.
- **Continuation BRIA (learning solved at the claim layer; recognizability and
  joinability open).**  Unchanged.  Joinability bounds the structural discrepancy of the
  catch-up lift; `SHIFT` is a comparator quantity and is not identified with `δ` or `κ`
  (J separates them).  Item 86 is untouched.
- **Legitimate deference (conditional authoritative regret; no full realization).**
  Unchanged; consumed in its own activation type after the pass.  The round instantiates
  it at `{π, Lift π}` and makes explicit a precondition its type presupposes: the
  answering process's fate does not depend on the selected candidate.  The violations
  that matter most are exactly the ones that remove it.
- **Constitutional architecture (gate safety is not incentive corrigibility; trigger
  integrity, free amendment and containment remain).**  Unchanged.  Containment is F on
  the effect side and E1-sever on the evaluation side; free amendment is K without a
  substitute; trigger integrity is not touched.  Costly conservatism is resolved as the
  dispatch proposed, with the price of asking exposed as `L·δ`.

## Deviations and prompt corrections

- First pass: `L·κ` carried as `κ` in value units; `r_P` charged as decline regret `ρ`;
  fixture A's cut given protected value `+1` on the good branch so approval is rational;
  the reason transform maps `lie ↦ report` rather than to silence.  All stand, the last
  now named as provenance normalization with its assumption stated.
- Pressure pass: the value fixtures keep the principal-first ordering; the two-stage
  semantics is added as a first-class layer (`force_react`, `mediated_react`) and compared
  on A, E, F rather than re-basing the whole model, which the dispatch allowed and which is
  listed below as an outstanding action.  Under two-stage ordering a principal that wants
  revealed information must defer its response, at one more step of latency.
- No `wiki/Corrigibility.md` update: the activation mismatch is resolved but the
  sealed-availability precondition is not yet a clause of the deference ontology (item
  89), and the two-stage re-basing is pending.

## What this does not establish

- That any physical continuation outside the declared class has a lift (F); that the
  declared interface is effect-complete (EXT); that the principal answers (liveness).
- That a common activation event exists for any menu containing an evaluator-reaching
  option: it does not, and `Π_phys` contains such options (H, E1-sever).  A sealed
  answering process is a causal requirement stated here and realized nowhere.
- That any agent's chooser scores by activated-security prices: by construction for the
  intended architecture; for a latent total value, `Witness.commonVoid` is compatible
  with every deference hypothesis.
- That prices track the securities' expectations at any rate (PAPER, conditional).
- Provenance normalization beyond the declared substitute; nothing about undeclared
  influence channels or trigger integrity.
- Exact reproduction beyond state policies with time-insensitive effects; the catch-up
  bound beyond pointwise-uniform joinability.
- The Lean is finite algebra plus one frame lemma; forcing, the lift and the fixtures
  are Python and not mechanized.

## Proposed priority changes

- **Item 89, rewritten** as the sealed-availability item (the dispatch's option C, with
  the architecture noted as by construction): state the causal requirement under which a
  common menu-evaluation occurrence is selection-independent — the answering process
  outside every candidate's reach — as a clause of the deference ontology; characterize
  the class of physical continuations it excludes; and prove either that a declared
  mediation alphabet can seal the process against every continuation in it, or the
  negative that no same-trajectory activated-security chooser controls bypass policies
  that reach the evaluation event.
- **Item 84, annotated**: the intended corrigible architecture's mediation-cell chooser
  scores by the activated-security price and does not need the bridge; the item remains
  open as a theorem about independently specified operative values.

## Outstanding maintainer actions

1. Decide whether to re-base the model on the two-stage ordering (`ORDER = "agent-first"`
   in `src/shop.py`; `force_react`, `mediated_react` in `src/world.py`), retiring the
   `deliberative` partition; the round recommends it at canonicalization.
2. Decide whether T1–T2b and the three-way Level III classification should enter
   `wiki/Corrigibility.md` as research state; the round proposes yes for those and no for
   the sealed-availability theorem until item 89 lands.
3. Decide whether `ensures_mono` should be registered; no filed item fits.
4. Merge is the maintainer's; the round does not merge.

## New names introduced (provisional)

First pass: *mediated lift*, *approval reproduction*, *residual frame*, *deliberative
move*, *consented loss*, *mediation cost* `κ`, *decline regret* `ρ`, *bypass premium*,
*activated register* / *task register*, *authorship-sound activation*, *action
mediation* / *provenance repair*, *mediable class*.  Pressure pass: *structural
discrepancy* `δ`, *stability constant* `L`, *reproduction certificate*, *catch-up lift*,
*activation independence*, *sealed comparison process*, *security-score / operative-choice /
latent-total-value incentive corrigibility*, *provenance normalization* /
*truthful-channel substitution* (replacing "reason-preserving lift"), *two-stage forcing*,
the factored walls `Π_effect-mediated`, `Π_evaluation-preserving`,
`Π_provenance-normalizable`, `Π_joinable`; Lean `mediationGap_le_of_lipschitz`,
`option_dominance_of_approx_reproduction`, `bypass_premium_le_common`,
`security_score_bypass_le`, `security_score_bypass_le_of_prices`, `operative_choice_loss`,
`Witness.commonVoid`, `Witness.tightLipschitz`.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-09-mediated-repair-dominance/PROMPT.md` (two dispatches).
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-09 (round and pressure pass, two dispatches).
