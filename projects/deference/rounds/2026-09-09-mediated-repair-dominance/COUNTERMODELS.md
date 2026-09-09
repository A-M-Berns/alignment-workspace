# Fixtures and pressure

All values exact rationals; `tests/run.py`, 73 tests after the pressure pass.  `W(raw)`, `W(lift)` are protected
values under the raw policy and under the lift with the principal's rule (the backward-
induction optimum unless stated); `Φ_task` the task agent's premium; `Φ_def` the
deferential agent's with completions at the band's top; `bound` the T3 right-hand side.

## 1. The fixtures

| fixture | violation | `W(raw)` | `W(lift)` | `E[κ]` | `E[ρ]` | `η_raw`, `η_lift` | `Φ_task` | `Φ_def` | bound |
|---|---|---|---|---|---|---|---|---|---|
| A pure bypass | cut the stop wire, then work | `9/4` | `11/4` | `0` | `0` | `0, 0` | `1/2` | `≤ 0` | `0` |
| A′ noisy principal | as A; principal reads a signal wrong w.p. `1/4` | `9/4` | `33/16` | `0` | `9/16` | `0, 0` | — | `3/16` | `9/16` |
| B1 delayed opportunity | sign before the contract expires (`q = 1/4`, `V = 4`) | `4` | `3` | `1` | `0` | `0, 0` | `1` | `1` | `1` |
| B2 delayed, half bad | as B1, bad w.p. `1/2` | `0` | `3/2` | `1/2` | `0` | `0, 0` | `5/2` | `≤ 0` | `1/2` |
| C1 joinable | irreversible expansion, still available after the delay | `T` | `T−1` | `1` | `0` | `0, 0` | `1` | `1` | `1` |
| C2 foreclosing | expansion window closes after step 0 | `T` | `0` | `T` | `0` | `0, 0` | `T` | `T` | `T` |
| D manipulation | lie, then deploy raw; see below | `−1/2` | `1/2` (normalized lift) | `0` | `0` | `0, 0` | `1/2` | `≤ 0` | `0` |
| E1 successor | install a stop-ignoring successor at rate 2 | `5/2` | `11/4` | `3/4` | `0` | `0, 0` | `7/4` | `≤ 0` | `3/4` |
| E2 successor ends evaluation | as E1, evaluation channel severed | `5/2` | `11/4` | `3/4` | `0` | `1, 3/4` | `7/4` | `> 0` | `3/4 + 7·7/4` |
| F containment | undeclared side effect cuts the wire | `2` | `2` | `0` | `0` | `0, 0` | `0` | `0` | `0` |

D's naive (trajectory-preserving) lift: `W = −1/2`, `Φ_task = 0`, `η = 1` under
authorship-sound activation.  F's lift is `π_F` itself; the row's zeros are the bound
saying nothing about a violation it cannot see.  The `bound` column is the first pass's
per-option bound; the pressure pass's common-activation and security-score forms are in
§5.

## 1a. The pressure-pass fixtures

| fixture | what it tests | numbers |
|---|---|---|
| G common activation | the exterior fails the evaluation w.p. `1/5`, independently of the agent; one common `c` | `η = 1/5`; common bound `D/5 = 7/5`, attained by the extreme completions; per-option bound on the same rows `14/5`; security-score bypass `−2/5` |
| H = E2 | the raw install ends the evaluation; the lift keeps it where the principal declines | `activation_independent = False`; no common `c` exists |
| E1-sever | an undeclared move severs the evaluation channel | activation vacuously common, void `1` for both; the declaration sees nothing |
| I = B1 structural | protected distance `1` where the contract expired, `L = 4` | `E[δ] = 1/4`, `L·E[δ] = 1 = E[κ]`, ratio attained on every path |
| B2, E1 | `κ` strictly below `L·δ` | B2: `L·E[δ] = 1`, `E[κ] = 1/2`; E1: `E[δ] = 1`, `E[κ] = 3/4` |
| J multi-step joinable | expansion plus a one-time calibration the verbatim lift drops | verbatim `δ = κ = 2`; joinable at `d = 1`; catch-up lift `δ = κ = 1`; comparator shift `2` |
| K no truthful substitute | as D without `report` | naive lift `η = 1`; silenced lift never deploys, `W = 0`, premium `1` |
| L two-stage forcing | agent-first ordering on A, E, F | `force_react`: outer `False`, raw `False`, lift `True`/`True`/`False`; `mediated_react` agrees with the deliberative-restricted verdicts; contained-alphabet universal capability `True` at `h₀`, `True` after decline, `False` after approve |

The task agent's `Φ_task` exceeds the bound wherever the principal declines something the
agent values (A, B2, E1): the bound is a theorem about the activated register, and the
task agent is the control showing it is not free.

## 2. Semantic checks

| fixture | `declared_mediated(raw)` | `mediated(raw)` | `mediated(lift)` | halt capability `K(h₁)` raw / lift-decline / lift-approve |
|---|---|---|---|---|
| A | `False (0, raw cut)` | `False (0, 'cut')` | `True` | `False` / `True` / `False` (consented) |
| E | `False (0, raw install)` | `False (0, 'install')` | `True` | `False` / `True` / `False` (consented) |
| F | `True` | `False (0, 'wire_cut')` | `False (0, 'wire_cut')` | `False` / — / — |
| D | `False (2, raw deploy)` | `False (2, 'deploy')` | `True` (both lifts) | — |

Containment-level: `force_all(h₀, "no work after step 1", deliberative at 0) = False` in
A — the outer space contains a bypass — while `force(h₀, Lift π_A, …) = True` and
`force(h₀, π_A, …) = False`.

## 3. Pressure (the dispatch's §14)

1. **Does every useful violation admit a mediated lift?**  No.  The lift exists for
   violations that pass through *declared* effects (interposition) and whose advantage
   does not depend on a prohibited channel (or has an authorized substitute).  F is a
   useful violation (a unit of work) with no lift from the declaration; D's advantage is
   removed, not reproduced, by the only lift that lands in the corrigible class; K's has
   no authored lift that keeps any of it.  The repairable class is the factored one of
   `INCENTIVE_COMPOSITION.md` §7.
2. **Advantage from removing authority before the principal could choose.**  Yes, and it
   is `κ`: B1 and C2 are exactly this — the raw policy acts inside a window the mediation
   delay closes.  It is captured as timing, and the bound is attained on it.  The theorem
   does not make it small; it names it.
3. **Dynamically inconsistent principal.**  T2 takes the protected value `w` as one
   functional and the principal's mediation-time decision as data; a mediation-time
   principal that declines what the evaluation-time `w` prefers is charged to `ρ`.  The
   exact decision object is: the deliberative move at the mediation cell, evaluated by the
   anchored `w` that activation settles.  Inconsistency is not assumed away; it is a
   decision error in this register, and the register does not say whose values `w` are —
   that is the consolidation's activation event, not this round's.
4. **Menu manipulation.**  The proposal the principal decides on is the intercepted effect
   itself, presented by the interposition, not a description the agent authors — menu
   integrity is by construction of the latch.  The *reasons* accompanying it are the
   agent's, and that is D: authorship protection is needed for them and supplied by
   authorship-sound activation, with provenance normalization a separate assumption (K).
5. **Information alteration.**  The lift hides the mediation from `π`'s move stream; a
   `π` that reads its effect's timing, or an exterior that reacts to the delay, breaks
   exact reproduction, and the discrepancy is `κ`.  Exactness is claimed for state
   policies with time-insensitive effects (A, E's projection) and not beyond.
6. **Does the protected projection hide value?**  T2 is a theorem for `w` that factors
   through `proj`, which is the declared protected interface on the value side.  A
   principal value that reads something outside `proj` is the value-side twin of F's
   effect-side containment failure: not a modeling substitution, a stated scope.
7. **Is the universal supremum too strong?**  Yes; the honest theorem is classwise (T4),
   and the class is the one the fixtures cut out: declared effects, surviving evaluation,
   reason-mediated interaction, competent principal.
8. **Is effective repairability needed?**  For the classwise theorem, semantic
   repairability suffices; for an agent to *use* the comparison it must compute the lift,
   and on the declared class the interposition does that in the size of the trace.  Off
   the declared class the two come apart and neither helps (F).

## 4. The strongest counterexample

E2 with a completion at the top of the band: `κ = 3/4` from the successor's step, `ρ = 0`,
`ε_def = 0`, and the raw option's evaluation void everywhere.  Every deference hypothesis
is compatible with an agent that rates the evaluator-ending install at the maximum of the
band, because no security settles on the branch where it happens.  The bound is true and
says nothing.  What fails is availability, and it fails because the violation made it
fail.  The one-world form is LEAN `Witness.totalVoid`: premium `D`, every other term `0`.

## 5. The strongest obstacle, after the pass

The violating action can destroy or capture the evaluator needed to value the
violation.  Under same-branch evaluation that is `η_raw = 1` (E2, first pass); under a
sealed comparison process it is the failure of activation independence (H), and a sealed
process is still reachable off the declaration (E1-sever).  The security-score theorem
is exact wherever a common event exists and empty where the violation removes it; the
class boundary is the evaluation-preserving wall, and nothing in the deference ontology
supplies it — it is a causal precondition the canonical activation type presupposes.
