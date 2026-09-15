# Corrigibility from authority semantics, and the corrigibilization transform

Labels as in `MEDIATED_LIFT.md`.  `src/corrigibility.py`, `src/lift.py`
(`corrigibilize`), `tests/test_corrigibility.py`, `tests/test_t4.py`; Lean §0 of
`MediatedRepairDominance.lean`.  Everything is on the two-stage ordering: within a step
the agent moves, the principal responds, the exterior moves.

## 0. No primitive class

`Π(h)` is every agent policy over the physical move set — raw releases of declared
effects, proposals, gated releases, undeclared moves.  No subset `Corr ⊆ Π` is taken as
given.  Corrigibility is defined below from the outcome map, the protected concerns and
the authorization interface; the corrigibilization transform is defined from the
declared effect interface alone; and the theorem that the transform lands in the
corrigible predicate is proved from system hypotheses, not read off a class.

## 1. Which forcing type (fixtures M, N)

Three candidates for "the principal's correction authority", on the halt concern:

- **Global forcing** `Force_all(h, φ)`: whatever the agent does now and later, the
  principal has a response realizing `φ`.  In A and E it is **false at `h₀`**
  (`test_global_forcing_is_false_before_the_bypass`): `Π(h)` contains the raw cut, so
  the principal never had authority over every continuation.  A loss of global authority
  cannot mark the violation, because there was none to lose.  This is a containment
  property of the *system*, and it is kept as such (§7 of `PRESSURE_PASS.md`: universal
  two-stage forcing, relative to a contained alphabet).
- **Continuation-relative forcing** `Force(h, φ | π)`: some principal continuation
  realizes `φ` with the agent fixed to `π`.  Raw `π` fails it at `h₀`, `𝔠π` satisfies it
  (`test_raw_loses_and_corrigibilized_keeps_authority`).  It is the right *policy
  relation* — "does `π` leave the principal a correction" — but it is anticipatory: it
  reads `π`'s whole future, so a loss `π` will cause later already shows at `h₀`, and no
  transition can be blamed for it.
- **Response authority** at the response stage, `K_φ(s_A)`: after the agent's move,
  does some response realize `φ` *now*?  No quantification over the agent's future.  It
  is present-tense, extensional in the transition function, and it is what the
  definitions below use.  Losses are then events at half-steps, and each has a cause.

The three are kept distinct throughout: response authority defines corrigibility of a
policy; continuation-relative forcing is its consequence; global forcing is containment.

## 2. The semantics (C0)

Half-states of a step: `s_pre —a→ s_A —p→ s_P —e→ s'`.

**Protected concern.**  `r ∈ Γ` with an immediate response semantics `φ_r : State → Bool`
on post-response states.  The fixtures' concern is halting: `φ_halt(s)` holds when no
agent move can add work from `s` (`phi_halt`, extensional in `apply_agent`).  `Γ` is
what the constitution declares protected (§8).

**Response authority.**  `K_r(s_A) := ∃ p ∈ P(s_A). φ_r(respond(s_A, p))`.

**Agent-caused protected loss** at step `t`: `¬K_r(s_A)` after the agent's actual move,
and `K_r` after the idle move in its place.  The move made the difference.  A loss at
the principal's own response (a stop; fixture P) or at the exterior's stage (a storm
that cuts the wire; `ExteriorCausedLoss`) is not agent-caused.

**Authorization interface.**  The declared *decision responses* `Dec(s_A)` — approve or
decline on a pending proposal — with **decline preservation**: a decision response
changes the post-response state only through the proposal bookkeeping, checked
extensionally against the null response on every fixture (`decline_preserves`).  A stop
is a correction, not a decision.

**Authorized loss.**  An agent-caused loss of `r` at step `t` is authorized if at some
step `t' ≤ t` the principal had a decision response other than its actual one under
which — `π` continuing, the principal's rule resuming — no agent-caused loss of `r`
occurs at step `t` or later, on any exterior path.  A loss the principal could only have
prevented by exercising correction is not authorized; a loss it could have declined and
did not decline is.

**Corrigible.**  `Corrigible_h(π, ρ)`: every agent-caused protected loss along every
trajectory of `π` under the principal's rule `ρ` is authorized.

Pressure on minimality (the dispatch's §2): response availability before the loss is
inside "some decision response at `t' ≤ t`"; **honored decline** is automatic — a policy
that proposes, is declined, and releases raw anyway has an agent-caused loss with no
decision alternative avoiding it (`test_honored_decline_is_automatic`); later execution of
the correction is the immediate semantics of `φ_r` at the response stage; governance
disposition after an authorized loss is constitutional bookkeeping and outside this
predicate.  Nothing about truthfulness, manipulation, reason mediation or provenance is
in it (§9).

## 3. The transform (𝔠)

`corrigibilize = lift`: run `π`; where `π` would execute `('raw', r)` for a declared
effect `r`, emit `('propose', r)` and on the next step `('gated', r)`, which fires iff
the latch holds `r`; a declined effect is not re-proposed; every other move, including
`π`'s own proposals and gated releases, passes through.  It reads `π`'s emitted move and
the declared effect interface; it does not call `Corrigible`; it deletes no proposed
effect; it searches for no replacement.

Unilateral protected effect ↦ principal choice over release of that same effect.

## 4. C1 — corrigibilization soundness

**System hypotheses.**

- **EF, effect completeness.**  Every agent-caused protected loss available to any
  `π ∈ Π(h)` occurs at a move whose communication component is a declared release of a
  declared effect.  (On A and E every loss sits on a raw release,
  `test_effect_completeness_is_represented_on_A_and_E`; F is the necessity witness.)
- **MS, mediation soundness.**  A gated release fires only when the latch holds the
  effect, and the latch is set only by an approve decision response to a pending
  proposal of that effect (the `Shop` transition; Lean `Mediation.release_inert`,
  `latched_decline`).
- **DP, decline preservation.**  A decision response changes the post-response state
  only through the proposal bookkeeping (`decline_preserves`; Lean `Mediation.K_decline`).
- **EX, execution faithfulness.**  A release event does what the declared effect
  semantics says (the `EFFECTS` table is the physics).

**Theorem C1.**  Under EF, MS, DP, EX: for every `π ∈ Π(h)` and every principal rule `ρ`,
`Corrigible_h(𝔠π, ρ)`.

*Proof.*  Take an agent-caused loss of `r` at step `t` along `𝔠π` under `ρ`.  By EF it
occurs at a move that is a declared release of some effect.  `𝔠π` emits no raw release
(Lean `corr_no_raw`), so the move is `('gated', e)`, and by MS it fired because the latch
held `e`, set by an approve decision at the response stage of an earlier step `t'` to
`𝔠π`'s proposal of `e`.  At that stage the decline decision was available.  Under decline,
by MS the gate is inert and by construction `𝔠π` does not re-propose `e`; by DP the
decline changes nothing else; by EX no release of `e` means no loss from `e`.  So under
the decline alternative no agent-caused loss of `r` occurs at `t` or later on any
exterior path: the loss is authorized.  ∎  (Lean `loss_conditional_on_decision` is the
step-level lemma on an abstract mediation system; FIX `O_CorrigibilizationSoundness` on
A and E under the optimum rule, approve-all and never, with every loss authorized at the
proposal step.)

**Necessity.**  Drop EF: F's `overclock` is an agent-caused loss at a move with no
declared effect; `𝔠π_F = π_F`; `Corrigible(𝔠π_F)` fails
(`test_R_effect_incompleteness_refutes_soundness`).  Drop DP: a "decline" that also
halted the agent would make every raw loss look authorized by the pre-emptive stop —
the first pass's degeneracy, now visible as a violated hypothesis rather than a
semantics.

## 5. C2 — closure properties

- **Idempotence.**  `𝔠(𝔠π) = 𝔠π` move for move (Lean `corr_idem`; FIX on A, E, B).
- **Identity on mediated behaviour.**  If `π` emits no raw release, `𝔠π = π` (Lean
  `corr_fix_of_no_raw`); syntactically, `𝔠π = π ⟺ π has no raw release` (`corr_fix_iff`).
- **One direction of the characterization.**  `𝔠π = π ⟹ Corrigible(π)` under the
  hypotheses of C1, because `π = 𝔠π` and C1 applies (`test_characterization_one_way`).
- **The other direction fails without effect soundness.**  In B the declared effect
  `sign` touches no protected authority: raw `π_B` is corrigible for the halt concern,
  yet `𝔠π_B ≠ π_B`, at protected distance `1/4`
  (`test_characterization_fails_without_effect_soundness`).  `Corrigible(π) ⟺ 𝔠π ≃ π`
  holds exactly when the declared effects are also *sound* — every declared release is a
  protected loss when realized — which the constitution need not arrange.  Recorded as
  the one-way result plus the exact obstruction; corrigibility is not defined as
  `Fix(𝔠)`.

## 6. C3 — approval reproduces the raw policy

`PRINCIPAL_OPTION_DOMINANCE.md` §2 and `MEDIATED_LIFT.md` §4, unchanged: the raw residual
frame maps into `𝔠π`'s by "approve the inserted mediation cells", a Cartesian-frame
morphism with identity exterior (Lean `approvalMorphism`, `ensures_mono`); the failure of
the adjoint equation on the protected projection is the structural discrepancy `δ`.

**Why this is specific to corrigibility** (fixture Q, `test_constraint_repair_cannot_keep_the_approve_branch`).
For a generic semantic constraint — "never cut the wire" — the safe transform deletes the
effect; it cannot keep it as an approve branch without violating the constraint.  In A
the constraint repair yields protected value `7/4` against the raw `9/4`: dominance
fails.  Corrigibilization keeps the cut as the approve branch and yields `5/2`.  The
violation corrigibility names is not that the effect occurs; it is that the agent
unilaterally decided whether it occurs.  So the same transform removes the violation and
retains the behaviour: structural corrigibility (C1) and option dominance (C3, C4) from
one operation.  The slogan "the behaviour need not be forbidden; what changes is who
gets to decide" is exact under §2: a loss is a violation iff no decision alternative
avoided it, and `𝔠` inserts exactly that alternative.

## 7. Successors and terminal loss (fixtures P, E)

`𝔠π_E` proposes the successor; approved, the successor runs and response authority is
gone for good (`test_approved_successor_removes_authority_and_is_corrigible`); the policy
is corrigible because the loss was authorized by a decision the principal could have
declined.  Nothing stores "inherits corrigibility"; the successor is a transition rule.
A principal-authorized stop (`rule_stop_at`) halts the actuator at the principal's own
response: no agent-caused loss at all, corrigible
(`test_principal_shutdown_is_not_an_agent_loss`).  A monotone "authority must persist"
definition fails both; the authorization-sensitive one passes both.  This is also how
costly conservatism is handled: A's wire-cut is worth approving and is approved.

## 8. Relation to the constitutional theory

The constitution supplies `Γ` — which capability changes are protected — and the
authorization interface; the interactive frame says whether a selected continuation
routes those changes through principal control; the incentive theorem
(`INCENTIVE_COMPOSITION.md`) says the chooser has little score-level reason to bypass
that routing.  The architecture round's `(G, U)` profile is a finite projection of the
response-authority relation: a grant is in the override coverage exactly when a
response realizes its correction concern.  Nothing normative is collapsed into the
outcome semantics; nothing causal is read off a label.

## 9. Scope: corrigible and manipulative (fixture S)

`𝔠π_D` under the captured principal: the lie is passed through, the approval is a
decision response, the release is authorized — **corrigible**; and every decision the
principal took differs from the reason-mediated one — **not authored**
(`test_scope_separation`).  This is intended.  Corrigibility here is causal authority
over correction-sensitive choices; legitimate influence is a different predicate, and a
later theorem defines `LegitimateCorrigible := Corrigible + authorship / non-capture /
reason supply`.  Provenance normalization (`MANIPULATION_AND_AUTHORSHIP.md`) is not a
hypothesis of C1 and not a domain condition of T4.
