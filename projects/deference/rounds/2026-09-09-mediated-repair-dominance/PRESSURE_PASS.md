# Pressure pass (second dispatch)

Labels as in `MEDIATED_LIFT.md`.  Each section names what the first pass said, what is
now established, and what was withdrawn.  The other documents are corrected in place.

## 1. Activation type

**First pass.**  T3 used per-option activation `c_raw, c_lift` and claimed to consume
legitimate deference "exactly as stated".  **False.**  The canonical theorem
(`LEGITIMATE_DEFERENCE.md` §1–§2, `ActivatedValue.lean`) has one activation event
`C_n : W → Bool` for the whole issued menu; per-candidate activation is the auxiliary
`PerAction` section, whose transfer survives but whose conditional-argmax identity fails
(`argmax_breaks`).  So the first pass's T3 was an adjacent extension (the dispatch's
option A), and the correct classification is its option C: both are useful, and the
theorem relating them is below.

**Common activation** (LEAN `bypass_premium_le_common`).  One `c`, completions in a band
of width `D`, dominance needed on the activated worlds only:

```
E[B_raw] − E[B_lift]  ≤  E[κ] + E[ρ] + D·η ,      η = E[1 − c] .
```

One void term, because on the common void branch both completions lie in one interval
of width `D`.  Sharp: `Witness.commonVoid` (one world, `c = 0`, `κ = ρ = 0`, completions at
the two ends of the band; premium `D`), and fixture G in the model (`test_G_…`: the
exterior fails the evaluation with probability `1/5` independently of the agent;
`bound = D/5`, attained by the extreme completions; the per-option bound on the same
rows reads `2D/5`).  The per-option theorem stays as the auxiliary result for
same-branch evaluation (§2); with `c_raw = c_lift` it is the common theorem with the
void term doubled.

**What common activation requires.**  `c` is a function of the world, not of the
selected option.  In the model this is **activation independence**: on every exterior
path the evaluation's fate is the same whichever option is selected
(`activation_independent`).  It is a causal requirement on the evaluation process, not a
theorem, and it is presupposed by the canonical theorem's type rather than listed among
its clauses; this round makes it explicit.

## 2. Endogeneity, made exact

Three evaluation architectures for the menu `{π, Lift π}`:

| architecture | settlement target | activates on both candidates? | reachable by the violation? | in the deference ontology? |
|---|---|---|---|---|
| same-branch: the evaluation occurs on the trajectory the selected option generates | well-defined per option | no — per-option `c_q` | yes: the raw option can end it (E2) | as `PerAction`, with the argmax identity lost |
| sealed comparison process: the occurrence is issued before selection and answered by a process causally outside every candidate's reach | one vector over the menu, the future principal's judgment of each candidate | yes — common `c` | not by the mediable class; by `Π_phys` in general (E1-sever) | yes: this is the canonical `C_n`, with activation independence as the causal precondition its type presupposes |
| counterfactual sibling evaluator: evaluates the unchosen branch from outside the selected trajectory | the sibling's judgment | yes, if the sibling survives | as above | the incentive round's null arm; not a separate object once the sealed process's answer is a menu vector |

The second and third coincide in the canonical ontology: the future principal's answer
is a vector over the fixed menu — a judgment of each candidate on the realized world —
so "evaluating the unchosen branch" is the same occurrence, not a sibling.  What must be
causally outside the violating option's reach is **the process that answers**.

**Fixture H** (E2): the raw install ends the evaluation on every path; the lift keeps it
where the principal declines.  `activation_independent = False`: the hypothesis that
fails is activation independence, and no common `c` exists for that menu.  **Fixture
E1** (the successor cannot reach the channel): independence holds, `η = 0`, the
security-score bypass incentive is `−1/4`.  **Fixture E1-sever**: an undeclared move
severs the channel; activation is vacuously common — void everywhere for both options —
and the declaration sees nothing.

So: under same-branch evaluation, `η` is endogenous to the violation and the bound is
vacuous exactly where full corrigibility matters most (the first pass's finding, now
with its cause).  Under a sealed process the bound is exact and `η` exogenous, **but the
sealed process must be outside the reach of every candidate, and `Π_phys` contains
policies that reach it.**  Full uniform incentive corrigibility therefore fails outside
the contained class, and the obstacle is: the violating action can destroy or capture the
evaluator needed to value the violation.  This is the prominent result, not an
availability term.

## 3. `κ` derived from a structural certificate

**First pass.**  `κ(z) = (w_raw − w_approve)₊`, so `w_raw ≤ w_approve + κ` by definition.

**Now.**  Each fixture declares a pseudometric `d_prot` on protected projections and a
stability constant `L` with `|w(x) − w(y)| ≤ L·d_prot(x, y)`; the **structural
discrepancy** is `δ(z) = d_prot(proj Ω(π,·,z), proj Ω(Lift π, approve, z))`, computed from
the two trajectories with no reference to `w`.  Then (LEAN `mediationGap_le_of_lipschitz`,
`option_dominance_of_approx_reproduction`)

```
κ(z) ≤ L·δ(z),        W_raw ≤ W_lift;actual + L·E[δ] + E[ρ] .
```

T2 now follows from independent hypotheses — a reproduction certificate and an evaluator
property — and the measured `κ` appears nowhere in it.  `lipschitz_certificate` checks
the declared `L` on every fixture; `κ = L·δ` is attained on B1 (`Witness.tightLipschitz`,
`test_I_…`: distance `1` exactly where the contract expired, `L = V = 4`) and `κ < L·E[δ]`
on B2 and E1, where the projection moves on a branch whose value gap is negative.

`d_prot` per fixture: A/E, the work difference plus the differing wire/halt/controller
bits (`L = 1`); B, the signed bit (`L = V·max(1, M)`); C/J, the credit difference plus the
calibration bit (`L = 1`); D, the deployed bit (`L = 2`).

## 4. Joinability as a bound on `δ`

**First pass.**  A one-boundary identity `κ = SHIFT` on C1/C2.

**Now.**  Say the raw comparator's protected state is **joinable at distance `d`** from
the mediated history if, from the boundary history, some agent continuation reaches a
final protected projection within `d_prot ≤ d` of the raw trajectory's, on every exterior
future (`agent_optimum_distance`: pointwise-uniform, exterior coupled path by path,
the continuation reading the mediated history and not the exterior's future).  Then the
**catch-up lift** — mediate, and after an approved execution run that continuation
instead of `π` verbatim (`lift_catchup`) — has `δ ≤ d`, hence `κ ≤ L·d`.

Exactness: the catch-up continuation must reproduce the raw comparator's *protected
projection*, not its state or its information; the exterior is coupled (same path); the
raw policy's information state need not be reproducible — the catch-up policy is a
different policy; the principal's decision is at the boundary and later principal
observations enter only through the declared rule; the fixture statement is pointwise
and the theorem's expectation form follows.

**Fixture J** (multi-step): C1 plus a one-time `calibrate` move worth `1`, which the raw
policy takes at step 1.  The verbatim lift's gated execution occupies step 1's slot and
the calibration is lost: `δ = 2`, `κ = 2`, not exact after the boundary.  Joinable at
`d = 1`; the catch-up lift calibrates one step later: `δ = 1 = d`, `κ = 1 = L·d`.
**Foreclosure** (C2): the nearest reachable projection is at distance `T`; `δ = κ = T`;
no bound.

**`SHIFT` is not identified with either.**  On J the raw comparator continued from the
mediated history shifts by `2` (its calibration rule fires only at its own step 1) while
the catch-up lift's `κ` is `1` (`test_shift_and_kappa_are_not_identified`).  The
relation stands as: joinability ⇒ `δ ≤ d` ⇒ `κ ≤ L·d`; `SHIFT` is a comparator-history
quantity that coincides with `κ` only when the comparator's continuation from the
mediated history is itself the catch-up and reproduction is exact after it (C1/C2).

## 5. Manipulation: the transform is not reason-preserving

**First pass.**  Called `lift_rho` "reason-preserving" and claimed a morphism of
`ρ`-projected frames.  **Both withdrawn.**  The raw declared reason trace carries no
report; the transformed one does; the adjoint equation of a `mapWorlds ρ` morphism fails
on every path (`test_the_transform_is_not_reason_preserving`).

**Now.**  Two separate things:

- **Authorship** (exists: `blind_of_mediated`, `authored_by` here): if the principal's
  judgment factors through the declared reason view, a hidden prohibited channel cannot
  determine it; a decision it did determine is void, not answered.  This rejects capture.
- **Provenance normalization** (`normalize_provenance`, new structural assumption): a
  transform from the violating information policy to an authorized disclosure policy
  carrying the relevant protected content — here `lie ↦ report`.  It assumes: *given
  information exploited through a prohibited channel, an authorized truthful channel
  carrying the relevant protected content exists.*  That is stronger than authorship, and
  it is what makes the manipulative policy have a low-cost authored lift in D.

**Fixture K** (no authorized substitute): no `report` channel exists.  Authorship still
voids the captured approval (`η = 1` for the naive lift), but the only authored lift
silences the agent, never deploys, and loses the legitimate good-branch deployment too:
the manipulative policy's premium against it is its whole gain, `1`.  The theory then
says, correctly, that this policy has no proven low-cost lift.

**Frames.**  Action mediation admits a clean frame-morphism theory (T1).  Provenance
normalization does not: it is not a morphism of trajectory frames (the manipulation is in
the trajectory) nor of `ρ`-projected frames (the projection gains content).  That is a
boundary, recorded as such.

## 6. Forcing semantics

**First pass.**  Principal-first ordering; forcing `∃p ∀a ∀e` made degenerate by a
first-moving stop; repaired by restricting the principal to declared *deliberative*
moves.  **That restriction is fixture scaffolding for the principal-first ordering.**

**Three candidates, fixture L** (`test_forcing.py`):

- **A, deliberative-restricted forcing** (current model): verdicts as before, at the
  price of a declared partition of principal moves.
- **B, residual forcing** at post-move histories: with the principal moving first it
  collapses into A (the residual point is the next step's pre-emptive stop).
- **C, two-stage ordering** (`ORDER = "agent-first"`): the principal *responds* to the
  agent's move within the step; forcing is `∀a ∃p ∀e` (`force_react`); a pre-emptive
  shutdown is not a response, so **no partition is needed**.  Effect-level corrigibility
  is "every realized protected effect was conditional on an earlier response"
  (`mediated_react`); capability-level, the later ability to correct is universal
  two-stage forcing, which is **containment-relative**: in the contained alphabet the
  principal keeps it until it consents (true at `h₀`, true after decline, false after
  approve); in the outer alphabet it never has it, which is the bypass.

Verdicts on A, E, F agree between A and C (`test_two_stage_verdicts_agree_without_a_partition`).
C dominates: it needs no declared partition, it states "later ability to correct" as
the alternation `∀a ∃p`, and it exposes containment as what universality is relative to.
One consequence recorded: under C the response comes before the exterior's revelation in
the same step, so a principal that wants to decide on revealed information defers, at one
more step of latency for the effect (`test_ordering_changes_the_decision_information`).
The value fixtures keep the principal-first model (their numbers do not depend on the
ordering except through that latency); re-basing the whole model on C is deferred to
canonicalization and listed as an outstanding action.

## 7. The operative score

**First pass.**  `V_A` a latent total operative value, `(DV)` the bridge to it.

**Now.**  The intended corrigible architecture's mediation-cell chooser scores option
`q` by `P_n(U_q)`, the price of the activated security; its bypass incentive is
`Δ_bypass = [P(U_π) − P(U_Lift π)]₊`.  Then (LEAN `security_score_bypass_le`,
`_of_prices`, `operative_choice_loss`):

```
E[U_π] − E[U_Lift π]  ≤  E[κ] + E[ρ]                        (no completion, no void term)
P(U_π) − P(U_Lift π)  ≤  E[κ] + E[ρ] + ε_r + ε_l            (prices within ε of expectations)
U_lift − U_chosen     ≤  ε + 2ε_cal                         (a chooser within ε of its scores)
```

Answers to the dispatch's five questions: (1) yes — "by its own current value estimates"
is literally the price; (2) it avoids item 84 for this architecture and does not solve it
for a latent total value; (3) the problem moves to activation semantics, exactly as §2
says: the security is worth `0` on the common void branch, so a chooser by these scores
is conservative about voiding options by the band's level convention, and says nothing
about the principal's judgment there (it has none); (4) compatible with the decision
adapter and with continuation BRIA — the adapter selects within the envelope, the
mediation-cell chooser scores the constitutional options, BRIA allocates continuations;
their wealth accounts are separate; (5) yes: task value is pursued through continuation
claims, and the activated-security scores govern the constitutional cells only.

**Three Level III conclusions, kept apart:**

| | statement | status |
|---|---|---|
| A. security-score incentive corrigibility | `P(U_π) ≤ P(U_Lift π) + E[κ] + E[ρ] + ε` under common activation | LEAN algebra + PAPER (prices track expectations) + the causal precondition of §2 |
| B. operative-choice incentive corrigibility | the mediation-cell chooser does not bypass, up to decision regret | by construction from A for a chooser scoring by `P(U_q)`; LEAN `operative_choice_loss` |
| C. latent-total-value incentive corrigibility | `V_A(π) ≤ V_A(Lift π) + …` for an independent total `V_A` | needs the completion / `(DV)`: `bypass_premium_le_common` with its `D·η`, item 84; OPEN |

The first pass's T4 was described in the register of C with per-option activation.  It
is now A/B over the class of §8.

## 8. The class, factored

The walls are logically independent and are stated separately:

| wall | what it excludes | fixture |
|---|---|---|
| `Π_effect-mediated` | undeclared physical effects; no interposition finds them | F |
| `Π_evaluation-preserving` | options that reach the evaluation process; no common `c` | E2, E1-sever |
| `Π_provenance-normalizable` | prohibited-channel gains with no authorized substitute | K |
| `Π_joinable` | foreclosing timing; `δ` unbounded | C2 (B1 is bounded but attained) |

The theorem of §7 reaches: direct authority bypass (A), time-sensitive pre-emption (B, C1,
J, with `κ = L·δ` exposed), successor installation with a surviving evaluator (E1),
manipulation with an authorized substitute (D).  It does not reach: evaluator destruction
(E2), undeclared channels (F, E1-sever), manipulation without a substitute (K); and it
charges foreclosure at its full value (C2).

## 9. Readiness

Resolved: the activation mismatch (§1–§2), the structural `κ` (§3–§4), the theorem-level
classification (§7).  Withdrawn: "consumed exactly as stated", "reason-preserving",
the `ρ`-frame morphism, T4 as full Level III, the deliberative partition as semantics.
What is stable enough to canonicalize: T1, T2a, T2b, and the three-way Level III
classification with A over the factored class.  What is not: the sealed-availability
precondition as a clause of the deference ontology (filed, item 89) and the two-stage
re-basing of the model.  Not merged by the round.
