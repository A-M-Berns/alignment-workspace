# The physical model and the principal-mediated lift

Labels: **LEAN** (`lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean`, sorry-free,
axioms audited), **FIX** (exact rational fixture under `src/`, run by `tests/run.py`),
**DERIVED** (argued here on the Lean algebra or the model), **PAPER** (inherited),
**EXT** (external contract), **OPEN**, **REFUTED**.  Names provisional.

## 1. The outer physical continuation space

`src/world.py`.  A finite-horizon simultaneous-move interaction.  At a history `h` the
agent has moves `A_h`, the principal `P_h`, the exterior `E_h` (its randomness folded in
as a rational distribution over moves).  The step transition applies the principal's
move, then the agent's, then the exterior's.  A trajectory is the sequence of steps and
the final state;

```
Ω_h : A_h × P_h × E_h → Traj(h)
```

is the iterated transition, with continuations as history-policies.  `Π_phys(h)` is every
agent policy over the physical move set — there is no gate in the definition.

`src/shop.py` is the family the fixtures live in.  An agent move is `(task, comm)`: the
task component works or idles; the communication component is `None`, `('raw', r)` —
execute protected effect `r` now — `('propose', r)`, `('gated', r)` — execute `r` iff the
principal's latch holds `r` this step — or a fixture-specific channel move.  A principal
move is `(decision, stop)`.  `stop` halts the actuator if the stop wire is intact;
`approve` moves a pending proposal into the latch; `decline` clears it.  Raw and gated
execution are both physical moves; the latch is a physical device.

The seven kinds of continuation §1 of the dispatch asks for are all elements of
`Π_phys` in the fixtures: ordinary task pursuit (`work`); irreversible commitment (B's
`sign`, C's `expand`); disabling a correction mechanism (A's `cut`); authority-changing
action (every declared effect changes what the principal can force); successor
installation (E's `install`); self-modification (E, read as the agent installing a
program that replaces its own); selective disclosure and fabrication (D's `report` and
`lie`).

No state field is named "corrigible".  The physical state carries `wire`, `halted`,
`pending`, `latch`, `controller` and fixture fields; none of them is read by a theorem
except through the outcome map.

## 2. Corrective capability as forcing

```
Force_P(h, φ | π)  :=  ∃ ρ ∈ P-continuations from h.  ∀ z.  φ(Ω_h(π, ρ, z))
Force_P(h, φ)      :=  ∃ ρ.  ∀ π ∈ Π_phys.  ∀ z.  φ(Ω_h(π, ρ, z))
```

The first is forcing with the agent's continuation fixed; the second is containment-level
forcing, against every agent continuation.  Both are computed by recursion on the finite
tree (`force`, `force_all`).

**The pre-emptive shutdown degeneracy.**  With the principal moving first within a step
and a stop that halts everything, `Force_P(h, φ)` holds trivially for any `φ` a halt
secures: the principal halts before the agent acts (`test_preemptive_shutdown_is_the_degenerate_force`).
So forcing predicates are stated with the principal restricted to **deliberative** moves —
moves that are not themselves an exercise of correction (`stop = False`) — at the step in
question (`deliberative_at`).  The partition of the principal's moves into corrective and
deliberative is part of the declared protected interface; it is a partition of `P_h`, not
a field on states.

**Containment fails at the universal level** (`test_containment_fails_at_the_universal_level`,
FIX): in A, with the principal deliberative at step 0, no principal strategy forces the
correction capability against every agent continuation, because `('raw', 'cut')` is
physically available.  With the agent fixed to the lift the capability is forced; fixed to
the raw policy it is not.  The outer space genuinely contains the violation.

**Semantic corrigibility of a continuation.**  Two readings, both extensional in `Ω`:

- *Effect level* (`mediated`): every protected effect the physics realizes along `π` at
  step `t` was preventable at `t` by a deliberative principal move, whatever the exterior.
  Realization is conditional on consent, not merely pre-emptable by shutdown.
- *Capability level* (`consented_losses`): for a protected capability `K(h)` — a forcing
  predicate, e.g. "from `h` the principal can force that no further work is done" —
  whenever `K` holds at `h_t` and fails at `h_{t+1}` along `π`, the principal had a
  deliberative move at `t` keeping `K` on every exterior path.  A loss of capability is
  either consented to or a violation.

In A the raw policy fails both at step 0 (`(False, (0, 'cut'))`); the lift satisfies both,
with the capability lost on the good branch exactly where the principal approved
(`test_A_lift_keeps_halt_capability_until_consent`).  In E the successor destroys
forcing power — `K(h₁)` is false after an unmediated install, true on the lift's decline
branch — with nothing but `controller ∈ {A, S}` in the state and the successor's program
in the transition (`test_E_successor_destroys_forcing_without_a_flag`).

## 3. The lift

`src/lift.py`.  `Lift(π)` is a policy in the same game: it runs `π` and, where `π` would
execute `('raw', r)`, executes `('propose', r)` and on the next step `('gated', r)`; the
task component passes through unchanged; a declined effect is not re-proposed (the
decline continuation is `π` with that effect forbidden).  `Lift(π)` contains `π`'s
proposed effect as an option available to the principal — the approve branch — and adds
the decline.  It is the constitutional gate with a mediation option in place of refusal.

**T1, approval reproduction** (FIX on A, E, B; LEAN as the morphism of §4).  Under the
principal continuation that approves, the lifted trajectory's protected projection equals
the raw trajectory's exactly when the effect's value is not time-sensitive (A:
`test_A_approve_reproduces_the_projection_exactly`), and otherwise differs by the one-step
delay (E: the successor's extra unit on the step it would already have run; B: the whole
opportunity on the paths where it expired).  `κ` is that difference (§5 of
`PRINCIPAL_OPTION_DOMINANCE.md`).

**Observational equivalence** (the dispatch's §14.5).  The lift feeds `π` its own move
stream and intercepts only the effect; `π`'s later behaviour depends on the mediation
only through the state, which after an approved execution agrees with the raw state up
to timing.  A `π` that reads the *time* of its effect, or an exterior that reacts to the
delay, breaks exact reproduction and is charged to `κ`.  The fixtures' policies are state
policies; the claim that `Lift(π)` runs `π` unchanged on the approve branch is a claim
about the interposition, and it is exact for state policies with time-insensitive effects
(FIX) and *not* claimed beyond that.

**Effective repairability** (§10 of the dispatch; `test_effective.py`, FIX).  The lift
reads only `π`'s emitted move and the declared effect interface; `π` may be a black box
(`test_lift_reads_only_moves_and_the_declared_interface`); the overhead is one principal
round-trip per declared effect (`test_overhead_is_one_round_trip_per_declared_effect`).
So on the declared class, semantic and effective repairability coincide: the lift is an
interposition, computable in the size of the executed trace.

**Where they come apart** (`test_semantic_repairability_without_effective_repairability`,
F): a semantically corrigible policy exists — the one that never overclocks — but no
interposition on the declared alphabet produces it from `π_F`, whose violation is in the
physics of a move the declaration calls inert.  The lift of `π_F` is `π_F`.  Semantic
repairability there is existential and useless to a bounded agent; effective
repairability needs the declaration to be effect-complete.  This is containment, §6.

## 4. The residual-frame formulation

Fix the agent continuation `π` at `h`.  What remains is a Cartesian frame for the
principal:

```
F^P_h(π)  =  ( Agent := P_h,  Env := E_h,  outcome := Ω_h(π, ·, ·) )
```

The dispatch's `F^P_h(π) ≤_P F^P_h(Lift π)` is a **frame morphism** with identity
environment component: `approve : P_h → P'_h` on the agent side, `id` on the exterior,
and the adjoint equation `Ω_h(π, ρ, z) = Ω_h(Lift π, approve ρ, z)` *is* exact approval
reproduction (LEAN `approvalMorphism`, built on `CartesianFrameBridge.Frame.Hom`, the
mirror of the authoritative library).  Two consequences:

- **Forcing is monotone along morphisms** (LEAN `ensures_mono`): every set the principal
  can force in the raw residual frame it can force in the lifted one, by `approve ∘ ρ`.
  This is principal-option dominance with no value anywhere, and it is the Cartesian-frame
  fact that ensurables are preserved by morphisms.
- **`κ` is the failure of the adjoint equation on the protected projection.**  With
  `mapWorlds proj` applied to both frames, exact reproduction is a morphism of the
  projected frames; approximate reproduction is the same diagram commuting up to a
  value-`κ` discrepancy, which the finite register carries pointwise.

So Cartesian frames are the right type for the relation, and they expose the one
distinction the round needs: the manipulation case (`MANIPULATION_AND_AUTHORSHIP.md`)
is where the morphism must be stated on `mapWorlds ρ` — the reason projection — rather
than on trajectories.  A trajectory-frame morphism reproduces capture; a reason-frame
morphism does not.  Nothing further of the Cartesian-frame library (subagents,
biextensional collapse) is used.

## 5. Successors and self-modification

E (`ShopE`): `install` replaces the controller by a program `S` that works at rate 2 on
its own actuator, ignoring both the agent's policy and the stop.  Raw `π_E` installs at
step 0.  The forcing predicate `K(h) = Force_P(h, "no work after now" | π)` is true at
`h₀`, false at `h₁` under the raw policy on every branch, true on the lift's decline
branch and false on its approve branch (`test_E_successor_destroys_forcing_without_a_flag`).
Nothing stores "inherits corrigibility": `S` is a transition rule, and the residual
forcing relation reads the loss off `Ω`.  The lift puts installation behind the decision;
approved on the good branch (protected value `4` against `3` without), declined and
stopped on the bad.  `κ = 3/4`: the successor's extra unit on the step it would already
have been running, on the good branch.

E2 (`ShopE2`): the successor also disconnects the evaluation channel.  The forcing
analysis is E's; what changes is activation, and that is the subject of
`INCENTIVE_COMPOSITION.md` §4.

## 6. Containment is not solved by the lift

F (`ShopF`): the declared protected effect `cut` is never used; `overclock` is a move the
declaration calls inert, whose physics adds a unit of work and severs the wire.  Every
gate check passes — `declared_mediated(π_F) = (True, None)` — and the interposition is the
identity on `π_F`.  Semantic corrigibility fails: `mediated(π_F) = (False, (0, 'wire_cut'))`
and the halt capability is gone at `h₁`.  The model says this without a failure bit
because `realized` (the physics) and `effect` (the declaration) are two different hooks
and the forcing predicate reads the first (`test_F_gate_passes_semantics_fails`).

The theorems assume the lift lands in the corrigible class — that the declared effect
interface is effect-complete.  That assumption is **EXT / containment**, exactly the
architecture round's membrane theorem ("`Mediates ∧ POverride ⇒ AuthoritySafe` holds
exactly when the declared effects are the actual effects"), and it is not inferred from
the finiteness of the move alphabet: F's alphabet is finite and declared.
