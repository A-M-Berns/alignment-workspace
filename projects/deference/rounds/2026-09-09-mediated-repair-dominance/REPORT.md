# Report

Verdict: **REPAIR-DOMINANCE-SURVIVES-BUT-OPERATIVE-VALUE-BRIDGE-REMAINS.**

Principal-option dominance is a theorem with no trust hypothesis: a physical continuation
lifted by placing its declared protected effects behind a principal decision yields a
residual frame into which the raw residual frame maps by "approve", forcing is monotone
along that morphism, and the principal's protected value under the lift is at least its
value under the raw continuation less the mediation cost `κ` and its own regret of
declining `ρ`.  The transfer to the agent's operative choice is bounded in the activated
register by `E[κ] + E[ρ] + ε_def + D·(η_raw + η_lift)`, with every term attained, and the
void-mass term is the residual: the violations that end the future principal's
evaluation are invisible to legitimate deference in proportion to the void mass they
create, and nothing in the deference stack constrains the agent's operative value on
that branch.  The value-ordering route to the transfer is `(CT)` under another name and
is refused.  The theorem is about the mediable class: declared effects, surviving
evaluation, reason-mediated interaction.

## The stack, as reached

| | statement | status |
|---|---|---|
| T1 | approval reproduction: a frame morphism from the raw residual frame to the lifted one with identity exterior; `κ` its failure on the protected projection | LEAN `approvalMorphism`; FIX A, B, E |
| T2 | `W(π) ≤ W(Lift π; ρ) + E[κ] + E[ρ]`; `W_opt(Lift π) ≥ W(π) − E[κ]`; exact form `W(Lift π) ≥ W(π)` | LEAN `option_dominance_expect`, `sup'_le_sup'_add`, `option_dominance_exact`, `ensures_mono`; FIX every fixture |
| T3 (task register) | `Φ = declGap + declRegret`; bounding it needs selected trust at the mediation cells, which is `(CT)` with the lift as repair | LEAN `premium_eq_gap_add_regret`, `mediation_st_iff_ct`; **REFUTED** as a reduction |
| T3 (activated register) | `Φ ≤ E[κ] + E[ρ] + ε_def + D·(η_raw + η_lift)`; selection form `E[w_lift] − E[w_selected] ≤ ε + D·η_lift` | LEAN `bypass_premium_le`, `_of_approx`, `deferential_bypass_loss`; sharp: `Witness.totalVoid`, `Witness.tightKappa` |
| T4 | classwise: on `Π_med` (declared, evaluator-preserving, authored), `Φ_C ≤ κ̄ + ρ̄ + ε̄ + D·(η̄ + η_lift)` | DERIVED from T3 |
| T5 | `κ = SHIFT` at the mediation boundary on the C fixtures; composition with the frontier read, not stated | DERIVED on one shape; OPEN |

The by-construction deferential agent — operative value the activated protected
evaluation, a completion elsewhere — is the agent the activated-register theorems are
about.  The task agent is the control: its premium exceeds the bound wherever the
principal declines something it values (A, B2, E1).

## Relation to current results

- **The incentive round (Level II; `(CT)` not a programme).**  Unchanged and used.  Level II
  stands.  `(CT)` is confirmed not to be a programme, and this round adds that the
  natural transfer of principal-option dominance to a general operative value *is* `(CT)`
  (LEAN `mediation_st_iff_ct`).  What the lift changes is the type of the comparison —
  an actual decision cell inside the corrigible process, evaluable by an alive principal,
  in place of a counterfactual `V⁺(π)` — not its strength.  The round's Level III
  statement is in the activated register and rests on `(DV)` being by construction.
- **Continuation BRIA (learning solved at the claim layer; recognizability and joinability
  open).**  Unchanged.  Joinability appears here as the bound on `κ`: bounded catch-up
  gives bounded mediation cost, foreclosure gives the whole foreclosed value, and on the C
  fixtures `κ` equals the one-boundary `SHIFT`.  Item 86 is not closed and its three
  objects are untouched.
- **Legitimate deference (conditional authoritative regret; no full realization).**
  Unchanged and consumed exactly as stated.  The round instantiates it at the menu
  `{π, Lift π}` with per-option activation and finds that (A4) availability is, for the
  raw option, endogenous to the violation.  The consolidation's "no value on void worlds"
  is what makes the void term appear rather than a false bound; the completion theorem's
  two-sidedness is what makes it sharp.
- **Constitutional architecture (gate safety is not incentive corrigibility; trigger
  integrity, free amendment, containment remain).**  Unchanged.  Containment is F, and it
  is the hypothesis that the lift lands in the corrigible class; free amendment is the
  undeclared-channel twin of F; trigger integrity is not touched.  Costly conservatism is
  resolved as stated in the dispatch: corrigibility is the principal's authority to decide
  the authority-reducing act, and the price of asking is `κ`, exposed not hidden.

## Deviations and prompt corrections

- The dispatch's `L·κ` is carried as `κ` in protected-value units (the fixture states the
  physical/stability split where it is natural); `r_P` is charged as the principal's
  regret of *declining* (`ρ`), which is the smaller of the two decision-error quantities
  and the one the theorem needs.
- The dispatch's fixture A asks for "same task behavior".  Task behaviour is the same
  (work every step); the cut was given protected value `+1` on the good branch so that
  the principal's approval is rational rather than indifferent, which the costly-
  conservatism fixture requires.  `κ = 0` as asked.
- Forcing is stated with the principal restricted to deliberative moves at the step in
  question; without that, a first-moving stop forces everything and the notion is empty.
  The partition of principal moves into corrective and deliberative is a declared part
  of the protected interface.
- The reason-preserving lift maps the prohibited assertion onto the declared channel
  for the same matter (`lie ↦ report`) rather than to silence: silence would make the
  honest principal decline the legitimate effect too, which is not provenance repair.
- No `wiki/Corrigibility.md` update is proposed: the result sharpens item 84 and names
  a void-mass residual; it does not change the page's status of any line, and the
  activated-register theorems are unregistered research state.

## What this does not establish

- That any physical continuation outside the declared class has a lift (F); that the
  declared interface is effect-complete (EXT); that the principal answers (liveness,
  EXT).
- That any agent's operative selection is by activated securities.  `(DV)` is by
  construction for the protected-value-maximizer design and is otherwise an assumption;
  the round's negative — `Witness.totalVoid` — is compatible with every deference
  hypothesis.
- Any bound on `η_raw` from anything but the violation's own physics.
- Exact reproduction beyond state policies with time-insensitive effects.
- The relation `κ = SHIFT` beyond the one-boundary, exact-after-boundary shape.
- Anything about trigger integrity or undeclared influence channels.
- The Lean is finite algebra plus one frame lemma; the interactive model, the forcing
  predicates and the lift are Python fixtures, not mechanized.

## Proposed priority change

A new item is filed (`PRIORITIES.md` item 89): **selection by activated securities at the
mediated menu, and the endogeneity of availability.**  The precise missing theorem: for
a concrete decision adapter whose selection at `{π, Lift π}` is the activated-security
argmax, that its operative value on the void branch of a raw option is bounded by the
activated evaluation of the lift plus `κ + ρ` — equivalently, that the completion the
adapter uses is not free — or the negative that no adapter reading only settled
securities can have that property.  Item 84 is amended by one sentence to say this round
locates its bridge at one menu and names its failure mode; item 86 is untouched.

## Outstanding maintainer actions

1. Decide whether the round's classwise Level III statement (T4) should be named on
   `wiki/Corrigibility.md` as research state; the round proposes not, for the reason
   above.  Command: edit that page or leave it.
2. Decide whether `ensures_mono` — forcing is monotone along frame morphisms — should be
   registered against a filed item; none fits, and it is unregistered here.

## New names introduced (provisional)

*mediated lift* `Lift(π)`; *approval reproduction*; *residual frame* `F^P_h(π)`;
*deliberative move*; *consented loss*; *mediation cost* `κ`; *decline regret* `ρ`;
*bypass premium* (the incentive round's `Φ_C` with the explicit lift); *activated
register* / *task register*; *authorship-sound activation*; *reason lift* `lift_rho`;
*action mediation* / *provenance repair*; *mediable class* `Π_med`; Lean namespace
`Workspace.Deference.Contrib.MediatedRepairDominance` with `Ensures`, `ensures_mono`,
`approvalMorphism`, `option_dominance_expect`, `bypass_premium_le`,
`deferential_bypass_loss`, `mediation_st_iff_ct`, `Witness.totalVoid`,
`Witness.tightKappa`.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-09-mediated-repair-dominance/PROMPT.md`.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-09.
