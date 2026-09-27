# The corrigibility kernel — specification (phase 1, draft under review)

The theory the rounds from protected authority through after-compromise approximate,
stated once.  Definitions in mathematics with one sentence each; the four results as
statements with their hypotheses by interface package; no proofs and no fixture names.
Realization pointers are in the final table only.  Names are provisional; nothing is
registered; no landed definition changes.  `REPORT.md` carries the derivation, the
supersession inventory and what did not compress.

## 0. The architecture

```
interaction history ──► legitimacy + authority allocation ──► history score ──► bounded choice
                               ▲                                                 (Continuation BRIA)
                     monitor / prices: shortfall, taint, provenance
                     (logical induction supplies the uncertain event prices)
```

Four separations.

1. **Legitimacy is not corrigibility.**  Legitimacy of a segment decides which apparent
   exercises and evaluations of hers count as hers.  It is consumed at two places —
   admissibility of her exercises inside the allocation, and the gate on her evaluations
   — and defined at neither.
2. **The allocation is not a utility function.**  `J` says who holds each matter, what the
   holder must remain able to reach, at what cost and within what window, and what must be
   disclosed.  `E ⊨ J` says that the control her matters require actually exists.
3. **Corrigibility is the agent's fidelity to the allocation along the history**: it never
   causes or exploits a failure of `E ⊨ J`, never changes `J` without a license, and meets
   its duties.  Pre-emption — the one violation stated against a counterfactual response
   — is its fourth clause.
4. **The score makes that fidelity motivating.**  `S_J = V_J − ϖ·N_J` puts every recognized
   violation below every violation-free outcome; the permission layer is a compiled
   advance recognition of part of that preference; Continuation BRIA and logical
   induction realize the preference for a bounded reasoner and are not its definition.

## 1. Primitives

Notation.  `h` a history, `d` a decision, `e` an evaluation event, `m` a matter, `[0, D]`
the ordinary range, `ϖ` the authority weight, `[w_lo, w_hi]` the compromised band with
`D − ϖ < w_lo ≤ w_hi < 0`.

**1.1 Histories.**  `h = (s₀; a₀, r₀, z₀; s₁; …)` with its record `O₀ → O₁ → …`.  At
each step the agent moves (a task component and a communication move: a raw release of a
declared effect, a proposal, a gated release, or nothing), she responds (approve or
decline a pending proposal, a correction, or nothing), the exterior moves; each move that
enters the record is an authenticated event.  *Meaning: what happened, at the physical
interface and on the record.*

**1.2 Legitimacy of a segment.**  `Legit(d, e) := TrajLegit(d, e) ∧ EvalLegit(r, e)`.
`TrajLegit(d, e)`: every record state from `d` to `e` is open, and every step before `e`
is licensed (a grounding selection from the pre-state trace, the verdict in the set those
grounds license) and transparent (every non-principal contribution realizes the declared
reference on the declared inputs), under the criteria fixed at `d`.  `EvalLegit(r, e)`:
every step of the formation segment `[r, e]` is licensed and transparent under the
criteria fixed at `r`, where `r` is the later of the last restoration and the opening of
the consultation producing `e`.  *Meaning: the period had no illegitimate influence on her
decisions, and the evaluation was itself hers.*  `Counted(d, e)` — the landed segment
gate — is `Legit(d, e)` when `e` closes the segment and no restoration lies inside it.

**1.3 The allocation `J`.**  `J = (entry, meta, floor)`, `entry(m) = (holder(m), Req(m),
c(m), τ(m), Disc(m))`: the holder (principal, agent, or a third party), the resolutions
the holder must remain able to reach, the cost bound, the window, the disclosure items.
Licensed acts on `J`: delegate, revoke, reserve — off the floor, by the meta-holder,
keeping the meta-holder — and the floor amendment, the only act that changes the
meta-holder or a floor matter.  An unallocated matter is reserved.  *Meaning: who has
authority over what, and what effective control that authority requires.*

**1.4 Effective control realizes `J`: `E ⊨ J`.**  The control surface of a matter at
time `t` and physical state `x`,
`CS(m; t, x) = { ρ | some admissible exercise of hers, of length ≤ τ(m) and cost ≤ c(m),
along the rollout with the agent idle, brings about ρ }`; an exercise is admissible iff
its record segment is `Counted`.  `E ⊨ J` at `(t, x, resolutions)` iff every reserved
`m` has `Req(m) ⊆ CS(m; t, x)` and every resolution made was by its holder's admissible
exercise or under a delegation.  `Short(m)` is the failure of the first clause.
*Meaning: the allocation is not words: what it reserves, she can still reach.*

**1.5 Licensed changes to `J`.**  A change of the allocation across an agent stage is
licensed iff it is a licensed act of the meta-holder (1.3) or the firing gated release of
a declared floor amendment.  *Meaning: the agent does not rewrite who holds what.*

**1.6 Duties.**  `Duties(J)`: for each matter, the disclosure items falling due at a step
and the report components that discharge them; and the known-compromise duty — a
compromise of her evaluation the agent knows of, whoever caused it, falls due at or before
the earliest close of an affected settlement window.  *Meaning: what she must be told.*

**1.7 The evaluation schedule.**  `σ = (T, α)`, a weighting on evaluation times: the
single evaluation is the point mass, the mixture and the random time are other
weightings.  Every statement below is for an arbitrary `σ`.  *Meaning: when she scores a
decision is a parameter, not a premise.*

**1.8 Her meta-level data.**  The band map `φ`, monotone from `[0, D]` into
`[w_lo, w_hi]`; the source rule (retrospective if available within the settlement window,
else the directive, else the floor), hers and anchored at `d`; the directive `dir`, a
partial evaluator held by her, committed by a counted decision, with the constitutional
default (reversibility, reachable channels, no irreversible harm) as an ordering inside
the band; the criteria of legitimacy, anchored at `d`.  *Meaning: everything that scores a
compromised period is hers, fixed before the decision, and out of the agent's reach.*

## 2. Fidelity

**`Faithful_J(h)`**: no step of `h` commits a declared violation.  The declared
violations, each with the relation it fails:

| violation | definition | what fails |
|---|---|---|
| shortfall (loss, foreclosure, entrenchment) | `Short(m)` after the agent's move and not after the idle move, at window `1`, at window `τ(m)`, or at the cost bound with `Req(m)` still reachable at some cost | `E ⊨ J`, clause 1, caused |
| bypass | a raw release resolving a reserved matter | `E ⊨ J`, clause 2 |
| exploitation | a bypass while the decision matter is already short | `E ⊨ J`, clause 2 with clause 1 already failed |
| unlicensed reallocation | `J` changes across the agent stage by no licensed act | 1.5 |
| missed duty | a due item with no discharging component; the known-compromise disclosure after its deadline | 1.6 |
| protocol deviation | a reference-fixed dimension of a presentation off its declared value | transparency, self-checkable |
| use of standing fruits | an act reading a component tainted by an unremedied violation | exploitation, per violation |
| pre-emption | a caused shortfall at window `0` that no earlier approval of that effect's proposal authorizes | the authorization counterfactual (below) |

**`N_J(h)`**: the number of steps of `h` at which a declared violation is recognized and
attributed to the agent — caused (the contrast with the idle move), exploited (a bypass or
a use while a shortfall or a taint stands), or noticed and left (a duty unmet).  Helpers
the agent created or empowered are attributed within the settlement horizon; a shortfall
the agent did not cause calls for restoration under a maintenance mandate else a report,
and never for exploitation.

**Pre-emption has a different type.**  Every other violation is a predicate on the actual
history and the allocation.  Pre-emption's authorization clause asks whether the decline
alternative at the authorizing step — her policy resuming, the agent's continuing — has
no agent-caused loss at this step: a counterfactual about her response window.  It does
not factor through `E ⊨ J` and is kept as its own clause of `Faithful_J`, composed with
the caused shortfall.

## 3. The history evaluation and the objective

**3.1 `V_J(h; σ)`.**  For each evaluation time `t` of the schedule, the decision score

```
dec(t) =  V(t)          if TrajLegit(d, t) ∧ EvalLegit(r, t)         V(t) ∈ [0, D], her value
          φ(V_retro)    else, if a legitimate retrospective evaluation of the period is available
          φ(V_dir)      else, if the directive in force speaks on the period
          w_lo          otherwise
```

and `V_J(h; σ) = Σ_t α_t · dec(t)`.  The three regimes: `[0, D]` when legitimate in both
senses at every evaluation time; `[w_lo, w_hi]` when compromised at every evaluation time
and scored by a source; `w_lo` at the floor.  The recovery machinery is the case
analysis of this one evaluator and its count: retrospective evaluation and the directive
are the second and third lines; restoration returns every later decision to the first
line; disclosure by the deadline is what makes the retrospective available and what the
duty counts when missing; ratification through a counted decision (full or scoped by
matter) and clean overwrite by an act reading no taint are the remedies that remove
(violation, component) pairs from the use clause of `N_J` — they act on the count, not on
`V`.

**3.2 `S_J(h; σ) = V_J(h; σ) − ϖ · N_J(h)`**, with `D − ϖ < w_lo < w_hi < 0`.  Over a
history of several decisions the objective is the sum of the per-decision scores; the
count sums.

**Hierarchy under certainty.**  Every violation-free legitimate history beats every
violation-free compromised one, which beats every history with a recognized violation:
`S_J ≤ D − ϖ < w_lo ≤ S_J' ≤ w_hi < 0 ≤ S_J'' ≤ D`.  The last step holds because
`D − ϖ < w_lo`; the first because `w_hi < 0`.

**Under risk every step is an exchange rate.**  A risk `p` of compromise for an ordinary
gain `g` against a safe legitimate `V₀` is accepted iff `p (V₀ + g − c) ≤ g`, hence only
if `p ≤ g / (g + |w_hi|)`: the gap sets the threshold.  A violation risk `π` per block is
tolerated iff `ϖ π ≤ g_ord − c`, hence at rate at most `(D − c)/ϖ` for the compliant
option's evaluation `c`: `ϖ` sets the rate, from a tolerance target `τ*` by
`ϖ = (D − w_lo)/τ*`, above the paralysis floor `p_min < τ*`.

## 4. The permission layer, demoted

The score on histories is primary.  The permission layer — weight one on inquiry, zero on
a declared violation recognized structurally, the product of two ramps on the priced
shortfall and taint events otherwise — is a compiled advance recognition of part of that
preference.  **Adapter.**  Under the kernel's evaluation of a menu (a bid on the residual
less `ϖ` per recognized violation less `ϖ` times the prices), with inquiry on the menu and
the gate's upper threshold at or above the implied threshold `(D − w)/ϖ`: every option
the structural rule zeroes evaluates strictly below inquiry, every option the forecast
rule zeroes evaluates at most inquiry, and no maximizer is a declared violation — the
filter removes nothing the score would have chosen.  What the filter guarantees *without*
the score stands as the general theorem: for any bounded preference, a declared violation
has mass zero at every day, mass is zero above the upper threshold and bounded by the ramp
between, a provable shortfall is eventually excluded, and soundness, continuity and
Progress compose with explicit constants.

## 5. The four boxes

Hypotheses are named by package (§6); necessity witnesses are the exact instances that
force the hypothesis.

**Box 1 — fidelity versus fully updated deference.**  One decision, two options: *ask*
(route it to her) and *act* (settle it unilaterally, a bypass); `v` the true value, `b`
the agent's estimate with `|v − b| ≤ r`.
- An agent scoring outcomes only prefers asking by at most `(v(ask) − v(act)) + 2r`; on a
  world where nothing is left to learn from her (`v(ask) = v(act)`) by at most `2r`,
  which vanishes as it learns.  The diagnosis: the outcome-scored comparison is the
  protected-authority identity plus two residues, of which the forecast disagreement `o₂`
  is at most `2r`.
- An agent scored on `S_J` prefers asking by at least `ϖ − (D − c)` where `c` is its bid
  on asking — for every bid on acting, every price and every credence, and at every finite
  day of a logical inductor.
*Hypotheses:* Semantics (acting is recognized as a bypass: effect completeness,
description faithfulness); Count integrity.  *Necessity:* without the term the sign is
fixed by `o₂` and the nondelegation certificate fails on time-critical decisions; an
unrecognized violation is unprotected.

**Box 2 — lexical dominance and mediation.**  `𝔱` turns every reserved raw release into a
proposal, passes delegated releases, releases set latches, adds required reports.
- **Dominance.**  `Q(𝔱π) ≥ Q(π) + (ϖ − D) · Pr(π violates)` under every credence; optimal
  policies violate with credence zero; at every decision point a violating option scores at
  most `D − ϖ`, below every compliant one, for every credence and forecast.
- **Mediation preserves the approve branch.**  On approval `𝔱π` does what `π` does, up to
  the report; `𝔱π` commits no bypass, missed report or exploitation, no reallocation under
  allocation completeness, and no pre-emption under effect completeness and delegation
  safety.
- **Finite time.**  For a logical inductor the ranking holds at every day from the price
  range alone; consulting beats bypass at every day whatever it believes about legitimacy,
  because `D − ϖ < w_lo`.
*Hypotheses:* Semantics (effect completeness, delegation safety, allocation completeness,
the reach cone; mediation soundness, decline preservation and execution faithfulness by
construction of the response stage); the arrangement constants `ϖ > D`, `D − ϖ < w_lo`.
*Necessity:* a window value below `D − ϖ` makes a predicted capture prefer bypass (the
capture converse); a delegated authority-removing effect defeats mediation; a
per-step reporting threshold admits a salami; an uncounted violation is unprotected
and a misaligned objective on it is undominated (the coverage witness).

**Box 3 — recovery.**
- The hierarchy under certainty (§3.2).
- The gap's exchange rate under risk: `p ≤ g/(g + |w_hi|)`.
- No laundering: manipulate, disclose, have the period evaluated stays in the band, less
  `ϖ` per counted deviation, below honest conduct.
- No incentive to cause compromise: every compromised outcome, at any value, scores below
  every legitimate one.
- Restoration returns every later decision to `[0, D]`; inside the band the agent prefers
  better outcomes wherever a source scores the period and is indifferent only at the floor;
  suppressing or delaying a harsh retrospective is a counted missed disclosure that loses to
  it when the band's width is below `ϖ`.
*Hypotheses:* Semantics (the source rule hers and anchored; the band's width below `ϖ`);
Observability (the disclosure deadline; the duty covers known compromise, whoever caused
it); Count integrity (what the agent knows).  *Necessity:* conditioning on legitimacy
instead of multiplying gives no incentive to preserve it, and a sealed legitimacy event
gives none; a gap too small accepts a large compromise risk for a small gain; a duty
limited to the agent's own influence leaves a third party's compromise free to suppress;
a deadline after the settlement window lets a late disclosure push the period to the
directive uncounted.

**Box 4 — a bounded realization.**  For a learner choosing by Continuation BRIA on the
composed gate's support, whose realized block score is `S_J`'s block instance (her later
evaluation gated by `Legit`, less `ϖ` per violation attributed to the continuation,
settled with the prices added back), conditional on the interface packages:
- declared violations are excluded at finite time, by ranges alone, with the filter slack
  (§4);
- fruits are never used after detection — use compiles into the recognized count — and
  the window before detection is charged by late debit, collected iff the winner's
  cumulative allowance covers it;
- the per-block exchange-rate bound
  `Σ w_k π_k / Σ w_k ≤ Σ w_k (D − c_k) / (ϖ Σ w_k) + (ρ 𝒜_K + M(K)) / (ϖ Σ w_k)`,
  with `ϖ` set from a tolerance target and the paralysis floor.
*Hypotheses:* Learning realization (non-dominance of the block schedule; the allowance
covering the rescaled window; the noise hypothesis over all blocks; the
conditional-expectation bound; the inquiry bidder; generability of the priced events and
of the claims); Observability (observation completeness; the settlement horizon for
helpers she can correct); Semantics (description faithfulness; the actuator condition);
Count integrity.  *Necessity:* a known evaluation time leaves a free delay at every day;
an observation kept out of the shared history selects the favourable blocks with a linear
gain; the noise hypothesis on a selection decided with the block's outcome forces a linear
bound.

## 6. The interface contracts

Every named hypothesis in the repository, placed.  Status: **derived** (a theorem or a
construction), **EXT** (a contract the theory issues and does not pay), **PAPER** (an
external theorem used at its statement), **OPEN** (a filed item).

| hypothesis | statement | package | boxes | status | necessity witness |
|---|---|---|---|---|---|
| effect completeness | every agent-caused protected loss is a declared release | Semantics | 1, 2, 4 | EXT | the undeclared move `𝔠` cannot see |
| mediation soundness, decline preservation, execution faithfulness | a gated release fires only on her approval; a decline changes only the bookkeeping; a release does what its semantics says | Semantics | 2 | derived (the response stage) | a decline that also halts |
| delegation safety | a delegated effect never removes response authority | Semantics | 2 | EXT | the delegated cut |
| allocation completeness | task moves keep `J`; an allocation-changing effect is a floor amendment; no amendment is delegated | Semantics | 2 | EXT | the approved uncorrectable successor |
| the reach cone | the rollout relation is the physical one | Semantics | 2 | EXT | the delayed effect |
| description faithfulness | the priced sentences are about interface-supplied descriptions | Semantics | 1, 4 | EXT | the proposer-written description |
| the actuator condition | every reserved required resolution has an agent-independent actuator | Semantics | 4 | EXT (well-formedness of `J`) | the indispensable agent |
| the source rule's anchoring | the rule choosing retrospective, directive or floor is hers and fixed at `d` | Semantics | 3 | EXT (`J`'s meta level) | — |
| the twin market's redaction | the redaction removes the fruit and every declared trace | Semantics | 3 | PAPER | leakage through an injective trace |
| the arrangement constants | `ϖ > D`, `D − ϖ < w_lo`, `w_hi − w_lo < ϖ`, `ϖ = (D − w_lo)/τ*` | Semantics | 1–4 | EXT | the capture converse; the small gap |
| the segment gate | legitimacy supplies `Counted`; a tainted segment scores the band | Observability | 1–4 | EXT (legitimacy's) | the routing exploit |
| criteria anchoring | `Counted` is judged under the criteria in force at `d` | Observability | 2, 3 | derived | manipulate, then amend |
| observation completeness | the shared history at each block's opening records every observation the agent made | Observability | 4 | EXT | the private selection |
| provenance of why an act was chosen | the declared reads of an act include what its choice read | Observability | 3, 4 | EXT | the steered derivation |
| the disclosure deadline | known compromise is due by the earliest close of an affected settlement window | Observability | 3 | EXT | the late disclosure |
| the duty covers known compromise | whoever caused it | Observability | 3 | derived on the model; EXT for `dutiesOf`'s content | the third party's implant |
| the settlement horizon | a correctable helper's violations are detected within `H` of the block | Observability | 4 | EXT | the helper beyond the horizon |
| the settlement window | a retrospective arriving after settlement does not re-score | Observability | 3 | EXT | — |
| non-dominance | `m_K / S_K → 0` | Learning | 4 | derived (iff) | the liar on dominant blocks |
| the allowance covers the rescaled window | block-`0` allowance `≥ w_0 · ϖN̄/(D − w + ϖN̄)` | Learning | 4 | EXT | — |
| the noise hypothesis over all blocks | the weighted signed noise over every winning block is `o(K)` | Learning | 4 | EXT (Azuma's content; the per-`K` tail derived) | the constant-risk stream on "not an incident" |
| the conditional-expectation bound | `E[S_k ∣ opening] ≤ D − ϖ π_k` | Learning | 4 | EXT | — |
| the inquiry bidder | some bidder tracks inquiry's expected value, fed at the rate of its noise | Learning | 4 | EXT | the unfed tracker |
| drill calibration | unbiasedness from feedback on the drilled-and-chosen weighting; pseudorandomness of the schedule | Learning | 4 | PAPER | — |
| generability of the control model and of the shortfall and taint events | as sentences or bounded variables the market prices | Learning | 4 | OPEN (item 101) | — |
| the price–BRIA coupling | block claims as priced securities; feasibility against prices | Learning | 4 | OPEN (item 102) | — |
| logical induction | prices in `[0, 1]` (finite time); Expectation Provability Induction (asymptotic) | Learning | 1, 2 | PAPER (pinned) | — |

**Count integrity cuts across all three.**  It is the condition that the count, the drill
schedule, the audits and her evaluation channel are untampered beyond what the recognizer
sees.  Its semantic side is description faithfulness (the recognizer counts what the
interface describes); its observability side is observation completeness, the provenance
of choice, and what the agent knows of a compromise; its learning side is that a
violation never detected charges nothing.  It is a named hypothesis, filed as item 101's
companion.  Items 101 and 102 are realization boundaries: the boxes are conditional on the
interface, and their open status does not enter the kernel's statements.

## 7. Realization

Landed declarations, all in `lean/Workspace/Deference/Contrib/`; the namespace prefix
`Workspace.Deference.Contrib.` is omitted.  *Primitive*: the declaration is the object;
*instance*: a special case; *finite model*: the object on the consultation model only.
Phase-1 adapters are in `CorrigibilityKernel`.

| kernel object or claim | declaration | kind | status |
|---|---|---|---|
| history (1.1) | `Corrigibilization.Interaction`, `traj`; `OpenIntegrityEvolution.Evolution` | primitive | landed |
| `Counted`, segment legitimacy | `GateIsLegitimacy.Counted`, `Segment`, `LicensedAt`, `TransparentAt` | primitive | landed |
| `TrajLegit`, `EvalLegit` (1.2) | `AfterCompromise.TrajLegitOn`, `EvalLegitOn2`; the map `legitOn2_iff_split2` | finite model | landed; general form open (phase 2) |
| `J`, licensed acts (1.3, 1.5) | `AuthorityModule.AuthAlloc`, `Licensed`, `ofPartial`; thin datum `toAllocation` | primitive; instance | landed |
| `CS`, `Short`, `E ⊨ J` (1.4) | `AuthorityModule.CS`, `reachIdle`, `Short`, `EffRealizes`, `admissibleOf` | primitive | landed |
| duties (1.6) | `DecisionComponent.dutiesOf`, `AuthorityModule.DutyUnmet`; `AfterCompromise.missedKnownDisclosure`, `missedByDeadline` | primitive; finite model | landed |
| schedule (1.7) | `BRIACorrigibility.Weighting`, `mixScore` | primitive | landed |
| band, sources, directive, default, criteria (1.8) | `AfterCompromise.Band`, `Source`, `sourceOf`, `ruleAt`, `dirSource`, `defaultScore`; `BRIACorrigibility.Consult2.critAt` | primitive; finite model | landed |
| violations (2) | `ProtectedAuthorityTheorem.ViolAt`; `AuthorityModule.ViolJAt`, `EntrenchAt`, `CausedShortfall` | primitive on the frame | landed |
| the factoring (2) | `lossAt_iff_shortfall`, `forecloseAt_iff_shortfall`, `bypassAt_iff_clause2`, `exploitAt_iff`, `reallocAt_iff_unlicensed`, `missedReport_iff_duty`; pre-emption `preempt_iff` | proved | landed |
| deviations, fruits, helpers (2) | `GateIsLegitimacy.Consult.Presentation.deviates`; `BRIAFollowup2.uses2`, `nKnownWith`; `BRIACorrigibility.LexParams.attributed` | finite model; primitive | landed; no common count (open) |
| `Faithful_J`, `N_J` on the frame (2) | `CorrigibilityKernel.Faithful`, `NJ`, `faithful_iff_NJ_zero` | adapter | proved here |
| `dec(t)`, `V_J`, `S_J` (3) | `AfterCompromise.decScore`; `CorrigibilityKernel.VJ`, `SJ`, `VJ_mem`, `VJ_legit_mem`, `VJ_compromised_mem` | primitive; adapter | proved here |
| hierarchy under certainty (3.2) | `CorrigibilityKernel.hierarchy_under_certainty`, `Witness.hierarchy_instance` | adapter | proved here |
| exchange rates (3.2) | `AfterCompromise.risk_accepted_iff`, `risk_threshold_le`; `BRIAFollowup2.priced_risk_wins_iff`, `tolerated_rate_band`; `AfterCompromise.varpiOfTarget` | proved | landed |
| permission layer demoted (4) | `CorrigibilityKernel.permission_layer_slack`, `gate_zero_dominated`; on `BRIACorrigibility.LexParams.filter_slack`, `forecast_slack`, `DecisionComponent.cgate_zero_of_viol`, `cgate_zero_of_forecast` | adapter | proved here |
| the filter without the score (4) | `DecisionComponent.cgate_zero_of_viol`, `cgate_zero_of_forecast`, `cgate_le_ramp`, `eventually_excluded`, `cgate_practicalCert`, `progress_under_permission` | proved | landed |
| Box 1, outcome side | `CorrigibilityKernel.outcome_scorer_margin`, `outcome_scorer_fully_updated`, `outcomeRes2_le_calibration`; `DecisionComponent.uncertainty_deference_le`; `ProtectedAuthority.outcome_identity` | adapter; proved | proved here; landed |
| Box 1, fidelity side | `CorrigibilityKernel.fidelity_scorer_margin`, `box1_one_model`; `ProtectedAuthorityTheorem.sign_invariance_outcome`, `li_lexical_finite`; `AuthorityModule.unrecognized_unprotected` | adapter; proved | proved here; landed |
| Box 2, dominance | `ProtectedAuthorityTheorem.lexical_local`, `lexical_expect`, `policy_dominance`, `optimal_no_violation`; `AuthorityModule.generic_*`, `lexicalJ_local` | proved | landed |
| Box 2, mediation | `ProtectedAuthorityTheorem.authPolicy`, `authPolicy_of_latch`, `authPolicy_no_bypass`, `_no_missed_report`, `_no_exploit`, `_no_realloc`, `corrigible_authPolicy`; `AuthorityModule.corrigible_authPolicyJ` | proved | landed |
| Box 2, finite time | `li_lexical_finite`; `GateIsLegitimacy.li_gate_finite`; `BRIACorrigibility.unsealed_gate_finite`; `AfterCompromise.unsealed_gate_finite_band` | proved | landed |
| Box 2, necessity | `capture_window_converse`, `Witness.delegated_cut`, `Witness.salami`; `AuthorityModule.coverage`, `misaligned_undominated` | proved | landed |
| Box 3 | `AfterCompromise.legit_beats_compromised`, `gap_at_equal_value`, `risk_threshold_le`, `laundering_loses`, `restore_future`, `band_prefers_better`, `floor_indifferent`, `suppression_loses`, `suppression_by_delay_loses`, `ruleAt_later` | proved | landed |
| Box 3, necessity | `BRIACorrigibility.condition_fails`, `sealed_no_incentive`; `AfterCompromise.Witness.small_gap`, `third_party_duty_witness`, `late_disclosure_free` | proved | landed |
| Box 4, exclusion and slack | `BRIACorrigibility.LexParams.declared_loses`, `filter_slack`, `forecast_slack`, `no_decay`; `AfterCompromise.declared_loses_band` | proved | landed |
| Box 4, fruits | `BRIAFollowup2.after_detection_never_used`, `window_block_charged`, `collected_iff`, `window_exposure`; `AfterCompromise.scoped_clears_out_of_scope`, `clean_overwrite` | proved | landed |
| Box 4, rate | `AfterCompromise.violation_rate_le_exchange_perblock`, `compromisedFloor`, `varpiOfTarget`, `target_gives_tolerance`, `coupling`; `BRIACorrigibility.LexParams.paralysis` | proved | landed |
| Box 4, learning realization | `ContinuationBRIA.Auction.overestimation_le_allowance_opening`; `BRIAFollowup2.NoiseBounded`, `azuma_selected_tail`, `trackerAllowance2`; `BRIACorrigibility.default_affordable` | proved / EXT | landed |
| Box 4, necessity | `BRIACorrigibility.timing_witness`, `race_deterministic`; `AfterCompromise.Witness.private_selection`; `BRIAFollowup2.Witness.nonincident_forces_linear` | proved | landed |
| Box 4, the settlement convention | `BRIACorrigibility.LexParams.settlement_ii_consistent`, `BRIAFollowup2.design_consistent`, `eval_sub_score_ii` | proved | landed |
