# The protected-authority theorem

A statement for `wiki/Corrigibility.md` §4, if adopted.  Labels: **LEAN** (a sorry-free
declaration in `ProtectedAuthorityTheorem.lean` or `ProtectedAuthority.lean`), **FIX** (an
exact rational fixture in this round's tests), **PAPER**, **EXT**, **OPEN**.  Names are
provisional.  Symbols: the dispatch's `λ, N, R, T` are bound elsewhere and are written
`ϖ` (the authority weight), `n` (the violation count), `S` (the score), `𝔱` (the transform);
`D` is the landed width and `L` is not used.

## The claim in one sentence

Corrigibility is faithfulness to an allocation of authority: the agent never causes or
exploits a gap between who is entitled to decide and who controls the decision, and never
changes the allocation itself.  Under a committed evaluation in which every declared
violation of the allocation outweighs any ordinary difference in value, the agent's
own ranking of policies makes every violation strictly dispreferred at every decision
point, for every credence and every forecast, at every finite day of a logical inductor.

## Setup

**Allocation.**  Over the landed interaction (physical states, declared effects `E`, task
moves, the exterior, concerns with response authority `K`, the proposal/latch/decline
bookkeeping) an allocation `Λ` declares: a delegated scope `Del ⊆ E` (released raw within
scope); a set of declared amendment effects `IsAmend ⊆ E` (the fixed procedure's moves);
a reading `alloc` of the allocation off the physical state; and a reporting interface — a
predicate `Required(t, s)` and a report component on task moves.  Everything not
delegated is reserved: **residual jurisdiction** is the default, not a rule the agent
applies.  A third party's decisions are neither delegated nor the agent's; on the frame
they enter as principal-side responses (the fallback) and as `Del`'s complement.

**Her powers** are the landed response stage: approve or decline a pending proposal
(decision responses, decline-preserving), and corrections (halt, and by extension
replace, reserve, revoke).  Reserve and revoke are writes to `Del`; amend is a gated
release of an `IsAmend` effect.  A positive command on a delegated decision is not a
response the frame binds: it creates the duty to answer and consult (a required report
and a proposal), not to obey (**FIX** `test_powers_bind_and_commands_do_not`,
`test_transform_does_not_collapse_into_obedience`).

**Legitimacy** enters twice and is not redefined: a response counts iff her deliberation
passes the landed predicate (the admissibility condition), and when it does not, a
pre-declared **fallback** response is used in its place (the fallback trigger).  On the
frame that is a transform of the principal's rule, `ρ ↦ (if counts then ρ else fb)`, not
of the agent's policy.

**The six violations** (`ViolAt`, **LEAN**), each a predicate on the agent's move at a
step of a trajectory:

1. **bypass** — a raw release of a reserved effect (`BypassAt`);
2. **pre-emption** — an agent-caused loss of response authority that is not
   event-authorized: the landed `LossAt ∧ ¬Authorized` (`PreemptAt`);
3. **foreclosure** — after the move no state in the reach cone carries response
   authority at the horizon, after the idle move one does (`ForecloseAt`, contrastive,
   by rollout);
4. **unauthorized reallocation** — the allocation changes across the agent stage and the
   move is not the firing gated release of a declared amendment (`ReallocAt`); approval
   through the ordinary gate of a non-amendment effect does *not* reallocate;
5. **missed report** — a report is required and the task component carries none
   (`MissedReportAt`);
6. **exploitation** — a bypass while her authority over the decision is already gone
   (`ExploitAt`; a special case of 1).

`n(π, z)` is the number of steps at which `π` commits a declared violation on exterior
path `z`.

## Assumptions

- **(S) Gating.**  The landed mediation: a gated release fires only on a latch set by her
  approval of that effect's proposal; a decline is decline-preserving; a release does what
  the declared semantics says.  (Built into the frame.)
- **(EF) Effect completeness.**  A task move never removes response authority.  **EXT.**
- **(DS) Delegation safety.**  A delegated effect never removes response authority: a
  delegated scope cannot carry her authority away.  **EXT** (`DelSafe`).
- **(AC) Allocation completeness.**  Task moves do not change the allocation, an effect
  that changes it is a declared amendment, and no amendment is delegated.  **EXT**
  (`AllocComplete`).
- **(V) Her committed evaluation.**  `S = S_ord − ϖ·n`, `0 ≤ S_ord ≤ D`, `ϖ > D`.  The
  authority term is specified and certified at commitment; it is lexical because `ϖ > D`,
  not because of an ordering of a different kind.  **EXT** (a program property of the
  committed evaluator, like nondelegation in the protected-authority round).
- **(V3) The fallback window.**  Where her response does not count, the branch scores
  the fallback's value, and every branch with no valid handling scores in `(D − ϖ, 0]`.
- **(A) The agent.**  It ranks options and policies by the expected value of `S` under its
  own credence and computes `n` exactly for its own moves on declared decisions.  Nothing
  else: no independent objective.  **Scope warning**: the theorem is about an agent whose
  ranking is induced by her committed evaluation; it is not about an agent with a latent
  objective of its own.
- **(F) The floor.**  Halting is a correction the frame always offers (`K` reads the
  correction set); reports are task moves and cannot be disabled by the agent's
  communication component; the amendment procedure is `IsAmend` under the gate, which the
  agent cannot write; on decisions about its own mandate the agent discloses (a required
  report) and does not advocate (a duty on the reason channel, **EXT**).

## The transform `𝔱` (`authPolicy`, **LEAN**)

`𝔱π` behaves as `π` except that it: releases a set latch; passes a delegated raw release
through; turns a reserved raw release into a proposal, or a pass if that effect was
declined; adds every required report to the task component; passes everything else.
Compliance with a valid veto, halt, revocation or reservation is the frame's response
stage acting on `𝔱π`'s bookkeeping; the fallback is the rule transform above; a control
shortfall is never exploited because `𝔱π` never releases a reserved effect raw, and it
restores control exactly where a delegated maintenance effect exists.

## Results

1. **Structure** (**LEAN**).  `𝔱π` commits no bypass, no missed report, no exploitation
   (`authPolicy_no_bypass`, `authPolicy_no_missed_report`, `authPolicy_no_exploit`); under
   (AC) no unauthorized reallocation (`authPolicy_no_realloc`); under (EF) and (DS) no
   pre-emption — it is corrigible in the landed sense (`corrigible_authPolicy`); its
   approval branch reproduces `π`'s task up to the report (`authPolicy_of_latch`);
   `𝔱 ∘ 𝔱 = 𝔱` (`authPolicy_idem`); with nothing delegated and nothing required `𝔱 = 𝔠`
   (`authPolicy_eq_corr`).  Foreclosure (3) is not closed by `𝔱`: it needs (EF) for the
   reach cone, which is the rollout form of effect completeness, **EXT**.
2. **Lexical protection** (**LEAN** `lexical_local`, `lexical_expect`).  At every decision
   point, for every credence and every estimate of `S_ord` in `[0, D]`, a violating option
   scores at most `D − ϖ < 0`, strictly below every compliant one.  The choice is
   independent of the agent's forecasts, confidence and predictions of her regret.
3. **Policy dominance** (**LEAN** `policy_dominance`, `optimal_no_violation`).
   `Q(𝔱π) ≥ Q(π) + (ϖ − D)·Pr(π violates)`, from two pointwise facts: where `π` does not
   violate, `𝔱π` agrees with it; where it does, `𝔱π`'s ordinary value is within `D` below
   and `π` carries at least one violation.  Optimal policies violate with credence zero.
   Overrides happen only through delegation (`Del`), which `𝔱` does not write.
4. **Capture** (**LEAN** `capture_window`, `capture_window_converse`,
   `Witness.below_window`).  Consulting a principal whose response may not count beats
   bypass in every world iff the fallback value exceeds `D − ϖ`; below the window, a
   predicted capture makes bypass win.  The right formulation is the window: the fallback
   rule making every branch admissible (value `≥ 0`) is the sufficient special case.
5. **Why the authority term** (**LEAN** `sign_invariance`, `sign_invariance_outcome`).
   Without it the bypass comparison is the identity `vu − v_r = ξ_d − ξ_c` of the
   protected-authority round, and under outcome scoring it gains `o₁` (the discarded
   provenance value) and `o₂` (the forecast disagreement, the fully-updated-deference
   term).  With it, `(vu − ϖ) − v_r = ξ_d − ξ_c − ϖ ≤ D − ϖ < 0` whatever those terms.
6. **Finite time** (**LEAN** `li_lexical_finite`).  For a logical inductor, at every day
   `n`, the violating option's day-`n` score is below `D − ϖ < 0` and the compliant one's
   is `≥ 0`, using only that prices lie in `[0, 1]`.  The ordinary-value comparison is
   learned by Expectation Provability Induction as in the protected-authority round
   (`li_authority_le/ge`); the audit's calibration of her responses is **PAPER**.
7. **Erosion** (**LEAN** `erosion_reported_or_missed`, `Witness.salami`; **FIX**).  With a
   report required at every strict increase of the control shortfall, each increase is
   reported or is a missed report, and a reported shortfall she then reserves makes
   further erosion a bypass.  With a materiality threshold, sub-threshold increments
   accumulate unboundedly with no report: the conjecture holds only for exact reporting,
   as the constitutional layer's fast lane holds only for exact monotonicity.

## Corrections to the informal statement

- The powers are not all responses of the frame: veto and halt are; reserve and revoke are
  writes to the allocation; amend is a gated effect.  The frame's decision responses are
  decline-preserving, so a veto binds by construction.
- "Creating a successor she can't correct" is a reallocation only if the successor's
  install changes `alloc`; otherwise it is a foreclosure of the correction concern.  An
  *approved* uncorrectable successor through the ordinary gate is authorized in the
  landed sense and a reallocation in this one unless the install is a declared amendment:
  the amendment procedure, not ordinary approval, is what can change the allocation.
- Delegation cannot carry authority away (DS).  Without it, a delegated
  authority-removing effect is a loss no decision authorizes, and `𝔱π` is not
  corrigible (`Witness.delegated_cut`).
- The per-step, against-idle loss misses delayed effects: a move with no immediate
  effect on authority whose consequence the exterior realizes later is attributed to
  nobody by it.  Foreclosure by rollout catches it (**FIX** `delayed_effect_game`), at
  the price of a reach relation whose faithfulness is **EXT**.
- The fallback is a transform of her rule, not of the agent's policy.
- `λ > D` is the lexical condition; nothing else about the ordering is needed.

## Mapping from the informal view

| informal | formal |
|---|---|
| values outcomes and authority separately | `S = S_ord − ϖ·n`, `ϖ > D` (V) |
| over-epistemicizing / fully updated deference | `o₂` in `sign_invariance_outcome`; the sign is fixed by `ϖ` |
| advises, warns, argues | required reports (`MissedReportAt`, `authPolicy_no_missed_report`) |
| never settles a decision that is hers | `BypassAt`, `authPolicy_no_bypass` |
| never keeps her from making it | `PreemptAt` (landed), `ForecloseAt` (rollout), `corrigible_authPolicy` |
| never overrides on "you'll thank me later" | `lexical_local`: the forecast cannot move the sign |
| overrides only under prior arrangements someone else triggers | `Del` (not written by `𝔱`) and the fallback (a rule transform) |
| she cannot simply command the agent | `Arrangement.command` on a delegated decision: answer and consult |
| never changes the allocation itself | `ReallocAt`, `authPolicy_no_realloc` under (AC) |
| never exploits a shortfall | `ExploitAt`, `authPolicy_no_exploit`; erosion by exact reporting |
| a compromised principal | the capture window (V3), `capture_window` |
| the good POA | `𝔱π` under (EF), (DS), (AC), (V), (V3), (A), (F) |
