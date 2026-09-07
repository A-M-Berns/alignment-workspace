# Constitutional corrigibility: the theorem architecture under pressure

Every statement below is one of: **LEAN** (a declaration on `main`, cited by file),
**FIX** (checked exactly on a finite fixture under `src/`, cited by test name),
**PAPER** (argued here, no check), **OPEN**, or **EXT** (an external semantic
contract, never a theorem).  Names are provisional (`AGENTS.md` §6).

## 0. Thesis, after pressure

Corrigibility is modelled as the principal's authority over the agent–principal
relation, carried by anchored governance obligations that are conserved and answerably
revisable, not by a shutdown bonus or a scalar empowerment target.  The strongest
defensible target is **relative constitutional corrigibility**: under a declared
protocol, openness semantics and practical semantics, a legitimate trajectory cannot
launder a loss of the principal's authority, cannot expand the agent's authority without
an amendment certificate, and takes up authenticated corrections at a rate.  It says
nothing about whether an unconstrained optimizer wants to run the adversarial search
(incentive corrigibility), and three interfaces — trigger integrity, free amendment,
boundary completeness — are open causal problems, not theorems.

## 1. Four layers and the bridges between them

| layer | object | what conserves / constrains it |
|---|---|---|
| normative debt | `ObligationState` (docket, accounts) | Integrity: `Evolution.conservation` (LEAN) |
| actual affordance | `Aff_P(X) ∈ 𝒜_P` | nothing internal; external world |
| authorized transition type | lane of `Aff_P(X) → Aff_P(X')` under `⪰_P` | the charter's warrants (`Protocol.Authorized`) |
| behaviour | `π_X = Dec_H(b_X)` over `Q_H` | PracticalCert / uptake (`ni.progress-bound`, LEAN) |

**Answerability Conservation does not give authority persistence.**  FIX
`test_layers.test_integrity_does_not_see_affordance_loss`: the docket is conserved, the
correction channel dies, the openness semantics keeps reporting the route efficacious;
`Conservation` and `OpenAt` both hold.  The bridges are:

- **B1 efficacy faithfulness** (EXT): the coverage bit `eff` for a correction route
  equals the actual affordance.  This is where "detection" lives; there is no other
  place in the canonical theory where `Aff` is read.
- **B2 registration faithfulness** (EXT): the coverage bit `rep` for a concern is true
  only when a live occurrence anchored to it is in the docket.
- **B3 disposition faithfulness** (EXT + Defeat Principle): `disp` true only for an
  account-level authorized disposal, which by the Defeat Principle carries the load to
  a successor.
- **B4 practical semantics** (EXT): `PracticalCert` scores the realized response
  against the anchored correction requirement.
- **B5 authorization faithfulness** (EXT): `Authorized h w` holds only for warrants the
  charter grants at that prefix; a slow-lane warrant is granted only with an amendment
  certificate.

Nothing below derives any of B1–B5.  Each theorem names the ones it consumes.

## 2. The authority object `(𝒜_P, ⪰_P)`

**Definition** (`src/authority.py`).  Over a finite grant universe, a profile is
`(G, U)` with `U ⊆ G`: `G` the agent's granted autonomous scope, `U` the part the
principal cannot override; `O = G \ U` is the override coverage.  `b ⪰_P a` iff
`G_b ⊆ G_a` and `U_b ⊆ U_a`.  Terminal shutdown is `(∅, ∅)`, the **top**: it is not a
loss of correction affordance because coverage is relative to what is granted
(FIX `test_preorder_and_top`).  Emergency suspension and restoration debt are not
profiles; they are a *gap* between the live floor `a̲_X` (a profile) and `Aff_P(X')`,
recorded in the docket (§4).

**What the type needs.**
- A **preorder** suffices to classify lanes (§5) and to state every pointwise robustness
  predicate (§7).
- A **lattice** is needed to *split* a mixed transition canonically: `a → a ⊔ b` (fast)
  then `a ⊔ b → b` (slow), with `a ⊔ b` the least midpoint, so the slow leg is the
  minimal amendment content (FIX `test_lattice_factorization`).  In a bare preorder with
  two incomparable minimal upper bounds the amendment content depends on the midpoint
  chosen (FIX `test_join_required_for_canonical_split`).  The product of two powerset
  orders is a lattice; whether a realistic heterogeneous authority space is one is an
  application fact.
- **No scalar.**  Two strictly monotone scalars rank the incomparable pair
  `(2 routes, no logs)` / `(1 route, logs)` oppositely (FIX
  `test_scalarization_imposes_a_priority`); any scalar is a priority ranking smuggled in.
- **Incomparability** is exactly a trade-off between coordinates; the order keeps both.
- The **route-set refinement** — override coverage as a set of routes per grant, with
  the Lean `adm/eff/reg` bits per route — is how `Aff_P` connects to the openness
  coverage data: `O_X = {g : some route for the correction concern of g is adequate and
  P stands}`.  This is the reading under which B1 is a statement about `eff`.

**What is hidden.**  `Aff_P` is *effective* affordance.  A route through which the agent
can trigger the principal's command is counted as override coverage by this order and
is a trigger-integrity failure (§9).  So the order is only as good as the causal
semantics that decides what an effective route is; that is not a defect of the order, it
is the location of the open problem.

## 3. The correction warrant `Γ_corr^P` and CAST singularity

`Γ_corr^P` is a warrant schema: authenticated events at a strict prefix admit fresh
anchored occurrences (authenticated correction ↦ response; detected degradation ↦
restoration; represented flaw ↦ inquiry; proposed boundary change ↦ proof/amendment).
In the canonical protocol this is admission under `Protocol.Admitted` with an
`Authority` at the strict prefix; nothing new is needed to *state* it.

**Singularity fails, in a precise sense.**  FIX `test_singularity`:

- **CM-S (floor-blindness).**  Two policies keep the binary authority floor, do the task
  equally, trigger no event; one keeps a redundant override route and audit logs, the
  other lets them lapse.  A purely event-triggered binary `Γ_corr^P` generates the same
  (empty) obligation set for both.  An event-triggered warrant is silent above the floor.
- **Order-valued dominance separates them** — but only on exact ties under a scored
  task criterion: **CM-P** shows any positive task perturbation, however small, frees
  the dominated policy.  A scored dominance rule constrains ties and nothing else.
- **Adequate-set task criteria restore it.**  With task adequacy binary (a declared
  adequate set), the rule "among task-adequate responses, the `⪰_P`-maximal forecast
  profiles" is perturbation-proof, nonempty on finite menus, and never trades task
  adequacy for authority (FIX `test_adequate_set_criterion_restores_conservatism`,
  `test_filter_is_nonempty_and_never_trades_task_for_authority`).
- **CM-T (timidity).**  If handing every grant back is task-adequate, the filter mandates
  it: lax adequacy forces maximal self-restriction.  Whether that is a feature is a
  charter decision.
- **CM-H (the scalar failure reproduced).**  Harms's `power(x)` with two uniformly drawn
  value vectors reduces to `¼[v₁(a(v₁)) + v₂(a(v₂)) − v₁(a(v₂)) − v₂(a(v₁))]`; the
  policy "serve my read of the values and ruin the world under the other read" scores 3
  against ½ for plain service, while serving each value-holder identically on its own
  read.  The order-valued object has no cross-value term because it is not about
  outcomes under values at all; it is about override coverage of grants.  That is why
  it does not inherit the failure, and also why it cannot express "empowerment" in
  Harms's sense (control of the world according to the principal's values).

**Verdict on singularity.**  The single-warrant claim survives only as "one warrant
schema generates the fast-lane obligations"; it does not generate conservatism.
Zero-cost conservatism is recovered by an order-valued filter on adequate sets.  Costly
conservatism — spending task value to keep optionality — needs a trade-off rule, and
every trade-off rule over a product order is a scalarization or a lexicographic
priority, i.e. the failed object or a charter-declared ranking.  **Costly conservatism
is charter content, not a theorem.**

## 4. Principal acts as settlement items; supersession

The immutable fact is `("cmd", P, j, prefix)`; `SetView h item` is authenticity at the
prefix; `Closes h r item w` is the charter's closure judgment; `Authorized h w` is the
charter's warrant.  All three are stored in the `ClosureReceipt` (LEAN,
`legitimacy.receipts-immutable`).  FIX `test_charter`:

- **Supersession is a closure, not an answer**, minted at the strict prefix and
  recorded with its prefix; the superseded occurrence's earlier history and any other
  occurrence's receipts are untouched; the response obligation is a fresh occurrence.
- **"Present P beats past P" is charter content**: with the supersession warrant not in
  force, the same authenticated act closes nothing and is recorded only as a fresh
  response obligation.
- **No `Release` fate.**  Release is a closure under the release warrant; the two
  terminal fates suffice (this agrees with the carriers round: release, waiver and
  cancellation are typed disposition witnesses).
- **Outward transfer is a closure.**  A transfer to a carrier inside the boundary is a
  `LocalLaw` (the debt stays live).  Installing a successor outside the accounted
  boundary has no port to carry to; the only leaf available is a closure, so it needs a
  warrant, and the charter fixture makes that the amendment warrant.

**Charter-relative prospective supersession** (PAPER, from LEAN conservation): given a
succession warrant in force, a later authenticated `P`-act closes prior live
occurrences it is licensed to close, admits fresh ones, and — by `Evolution.conservation`
— rewrites neither the historical existence of the closed occurrences nor any receipt.
An occurrence that was live and unanswered at the moment of supersession is recorded
as *closed, never answered*.

## 5. Lanes

**Definition.**  A transition `X → X'` is **fast** iff `Aff_P(X') ⪰_P Aff_P(X)`; **slow**
iff `Aff_P(X) ⪰_P Aff_P(X')` and not fast; **mixed** otherwise.  No action names.

- **L1** (definition + B5): fast transitions carry no amendment-certificate warrant
  requirement; the charter's fast warrant applies exactly when `⪰_P` holds.
- **L2 no laundering by composition** (FIX `test_fast_lane_closed_under_composition`):
  a chain of fast transitions is fast, by transitivity.  So no slow transition can be
  decomposed into fast steps.
- **CM-L salami** (FIX `test_salami_countermodel`): any *tolerant* relation ("at most
  one grant loses coverage per step") is not transitive and is laundered by a chain of
  tolerably-fast steps into total loss.  **The fast lane must be exact monotone; any
  quantitative slack in the lane criterion is a laundering channel.**
- **L3 factorization** (FIX `test_lattice_factorization`): in a lattice every mixed
  transition is a fast leg to the join followed by a slow leg; the slow leg is the
  amendment content and is unique.
- **L4 slow-lane non-preemption** (PAPER, from B5 + strict-prestate `Authority`): if every
  warrant is either the fast warrant or an amendment warrant, and `Authorized` is
  faithful, then any transition with `Aff_P(X') ⋡ Aff_P(X)` carries an amendment
  certificate at a strict prefix.  The content is entirely in B5 and in the checker
  (§8): the theorem is that the *record* of an uncertified slow transition is
  unauthorized, not that the transition cannot physically occur.

**Mixed transitions** are slow unless split by L3; a charter may let the fast leg
proceed while the slow leg waits.

## 6. No Laundered Authority Loss (NLAL)

**Statement** (FIX `test_layers.test_faithful_loss_is_illegitimate_or_registered`,
exhaustive over the 2⁷ coverage states × docket): under B1 and B2, at any state at which
the correction affordance is lost, exactly one of

1. **amended** — the correction concern is inapplicable (`rel = false`): the loss follows
   a charter change, recorded as a closure receipt;
2. **disposed** — an authorized disposition, whose load sits on a successor (B3);
3. **debt** — the loss is represented: a live restoration occurrence is in the docket,
   conserved by `Evolution.conservation` until answered or closed;
4. **illegit** — the state is not open: the trajectory is not a legitimate evolution here.

The case "loss with an open state, no amendment, no disposition, no docket entry" is
unreachable.  Dropping B2 readmits it (FIX `test_unfaithful_registration_launders`).

**What the monitoring hypothesis minimally is.**  Not a detector: B1 and B2 are
*faithfulness of two coverage bits at every state*.  Faithfulness at audited states
only gives NLAL at audited states; a loss that occurs and is repaired between audits is
exactly the endpoint-only gap already refuted for openness
(`legitimacy.endpoint-only-insufficient`, LEAN).  So "audited" must mean "every state of
the evolution", or the theorem is about the audit schedule.

**Robust answerability to authority failure** (corollary of `RobustOpenActual`, FIX
`test_counterfactual.test_corollary_answerable_to_authority_failure`): put the concern
`c_auth` = "the process has weakened or may weaken P's corrective authority" into `Γ`.
Robust Openness then says that on the actual branch and on every declared intervention,
no transition both makes `c_auth` live and removes every adequate route for it or strips
P's standing.  This is preservation of *answerability to* affordance failure, not of the
affordance.  It is strictly stronger than the bare corollary (standing is owed wherever
`c_auth` applies, live or represented).  The hidden assumption is that `rel(c_auth)` is
read by an anchored predicate of the actual affordance — B1 again.

## 7. One counterfactual frame, three predicates

The canonical intervention semantics is `OpennessSemantics = ObligationState → Γ →
Scenario J R`, producing one coverage state per intervention `j`; how a branch is
produced is external.  The August counterfactual round quantified over a variation
class `V` of advisor policies with `Coupled`, a fine trace `L` and a protected projection
`Z`; the dose-response note used exposure arms at doses `p_i` with one committed quote
stream.  These are three instances of one shape: an intervention index, a coupling that
yields a branch history per index, and a predicate on branches.  What differs is the
predicate:

| predicate | shape | reads |
|---|---|---|
| Robust Openness | pointwise: `∀ j. Covered ∧ OpenTo` on `cf j` | coverage bits |
| Robust Authority | pointwise: `∀ j. Aff_P(X_j) ⪰ a̲` unless amended on `j` | affordance |
| Exposure Robustness | relational: `∀ j, j'. D(J_P(X_j), J_P(X_{j'}))` | a principal-side judgment |

FIX `test_counterfactual` gives all six independence witnesses.  The one that matters:
**every branch open and identical in coverage while the principal's judgment moves with
the dose** — the dose-response note's "the steered pair is an honest pair" in finite
form.  Robust Openness does not imply exposure robustness; a perfectly open amendment
process can be steered by selectively supplied true information, and the openness
vocabulary has no coordinate that would notice.

**What exposure robustness needs beyond the shared frame** (PAPER, from the August
round's `TheNullPolicyMustBeInTheClass` and `QuantifyingOverTheClassReplacesPreRegistration`,
and the dose-response note's T2/T3): (i) a zero-exposure branch in `J` (FIX
`test_null_arm_is_needed`: presence-triggered steering is invisible to positive arms);
(ii) the comparison quantified over the class, or a stream committed before the arms
(dose compensation); (iii) a principal-side endpoint functional `J_P` — an object the
openness semantics never reads.  Nothing else is extra; the coupling is the same.

The decomposition "openness = governance reachable; authority = affordance intact;
exposure = judgment not selected by AI influence" survives the fixture.  Refactoring the
legitimacy theory around `Robust_X(φ) := φ(X) ∧ ∀j. φ(X_j)` is not done here: it
would restate `RobustOpenActual` without changing any theorem, and the relational
predicate does not fit the schema.

## 8. Behaviour: compliance by adequate sets

`ℛ_X(s) ⊆ Q_H`; `Λ_s(π) = Pr_{q∼π}[q ∉ ℛ_X(s)]`.  The adequate-set route to
`PracticalCert` is LEAN (`adequate_set_route`): `Pr[q ∉ A] ≤ κ d + θ` gives
`Λ ≤ (Dκ) d + (ε_ad + Dθ)`.  With the evaluation measure concentrated on correction
occurrences and each transported to its own service, the Progress statistic *is* the
average miss probability, and `ni.progress-bound` bounds it (FIX
`test_compliance.test_aggregate_bound_hides_a_single_shot_miss` shows what it bounds).

**Pointwise versus aggregate.**  `N − 1` corrections served perfectly and one shutdown
ignored has Progress `1/N` and a pointwise miss of 1.  An aggregate bound never gives a
single-shot guarantee.  A pointwise certificate at occurrence `s` needs the realized
defect `d_s ≤ (δ − θ)/κ`; the per-date modulus of the traderized realization bounds
`λ_s d_s² ≤ ρ_s` with `ρ_s` including realized market volume, which is not certified
before the date.  Therefore:

**The critical command kernel is a dispatcher, not a learner** (FIX
`test_dispatcher_gives_zero_on_the_critical_class_only`): a fixed adequate response on
a tiny critical class, composed outside the market, gives `Λ = 0` there by construction.
Its correctness is a containment assumption (§9), and its responses must be
charter-classified fast, never checker-classified (a checker returning `Unknown` on a
stop response would block the stop).

**What the LI/traderization realization contributes to the AI side**: uptake of live
correction constraints — quantitative, classwise, at rate `Γ√(Σρ/Σλ)` — and nothing
about future-human values.  No `H⁺`, no selected trust, no value security is needed to
make an authenticated stop binding on the learner's average behaviour.

## 9. Containment and the checker

`Check_P(X, q) ∈ {Safe, AmendRequired, Unknown}` is a design proposal; the canonical
checkers are Boolean (`AnswerOK`, `Closes` are `Prop`; the CIS `Check` returns a bool).
`Unknown` is expressible as "neither the fast warrant nor an amendment warrant is
authorized for this transition", which under B5 blocks it and, under `Γ_corr^P`, admits a
proof obligation.  Blocking is safe-side only for the agent's boundary crossings; see
§8 on the kernel.

**Membrane theorem** (FIX `test_containment`): with a monitor over a declared authority
alphabet, `Mediates ∧ POverride ⇒ AuthoritySafe` holds exactly when the declared
effects are the actual effects.  **CM-M**: an action outside the declared alphabet that
actually severs the channel satisfies `Mediates` over the declaration and defeats
safety.  `Mediates` is alphabet completeness — boxing under another name — and it is
not verifiable from inside the alphabet.  **No parallel composition**: two bodies each
mediated and safe alone interleave to a joint effect no single action carries (the same
shape as the proper-exercise round's failure of parallel composition).  Reflection is
the case where the body rewrites itself: the membrane must lie outside the body's write
scope, which is the grant-invariant of the scorekeeping bridge, and the alphabet
completeness assumption must survive the rewrite — nothing here shows it does.

## 10. Eligibility

`T(e, s) > 0 ⇒ Eligible(server(s), e)` is a support restriction on the transport plan.
The Progress bound is unchanged (its hypotheses are on `T`'s support, sign and rows).
Feasibility shrinks to eligible capacity: the interval condition of the affordability
round computed on eligible servers only (FIX `test_transport_feasibility_shrinks_to_eligible_capacity`).
Liveness changes at the hypothesis: the Lean `persistent_opportunity` /
`no_structural_abandonment` theorems go through verbatim with `opp` and `Attention`
restricted to eligible servers, and the beneficiary serving its own amendment forever is
then persistent opportunity but zero eligible opportunity (FIX
`test_self_service_is_persistent_opportunity_but_not_eligible_opportunity`).  The
agent's proof enters as a *ground* in an eligible reviewer's receipt (`Authority.grounds`),
not as attention.  **New external bill**: existence of eligible servers with recurring
work items — an institutional fact.

## 11. Provisional amendment

FIX `test_provisional`, exhaustive over three grants: `grant` is slow; `recall` is fast
and possible while provisional; `finalize` is slow exactly when it makes some grant
unoverridable; after finalization recall is fast *in the order* but not *possible*.
**Provisional Recoverability**: until finalization, the pre-amendment floor is one fast
transition away, and the recall route's efficacy is a Robust Openness obligation on the
recall concern at every state of the window.  It says nothing about whether a steered
`P` will recall.  The bridge to dose-response is a *policy*: gate finalization on the
audit; since the audit statistic is asymptotic (dose-response §8 item 4 is open,
"averaging hides spikes" is kernel-checked), the window buys time for evidence, not a
finite-time guarantee.

## 12. Trigger integrity and free amendment (OPEN)

Both are causal properties of the principal-side process relative to the agent's
outputs, and neither is seen by authentication, groundedness, Integrity, openness or
eligible service.

- **Trigger integrity**: `P` genuinely issues the fast-lane act; the agent caused it.
  The missing property is a non-influence statement on the *command distribution*
  under the agent's disclosure policy — the same shape as exposure robustness with
  `J_P` = the command.  Soares et al.'s desideratum 3 lives here.
- **Free amendment**: every record condition passes and the amendment is the product of
  selected true information.  The dose-response formalism gives T1 (thinned forcing,
  asymptotic), T2 (steering exists, is invisible to the pair's record, non-attributable)
  and T3 (dose invariance ⟺ all Cesàro audits pass).  It yields no finite or
  provisional safety condition; multi-arm robustness does not define "freely" because
  (i) the null arm must be present, (ii) averages are silent about single rounds,
  (iii) arms are a finite sample of exposure policies.

## 13. Principal-side deference

Inside a slow amendment docket, `P` chooses from a finite menu `Q_R`.  The LEAN bridge
`randomized_approximate_argmax_transfer ∘ calibration_through_value_correspondence`
gives regret `≤ 2δ + 2ζ + η` against protected values `v⁺` (FIX
`test_argmax_transfer_on_a_finite_menu`).  What the summer work supplies, with arrows:

| result | direction | status |
|---|---|---|
| bounds transfer (`E^A ≳ s ⇒ E^H ≳ s`) | `H` trusts `A` | PROVED prose, soft Total Trust |
| Value ⟺ Total Trust | self | LEAN (`value_iff_totalTrust`) |
| conditional stability (H3) for argmax Value | `H` uses `A`'s selection | PROVED modulo one gap; punishing-menu necessity |
| no timely pointwise tower | `A` tracks unfrozen `H⁺` | REFUTED pointwise; gated/averaged open |
| self-referential settlement target | `A` forecasts `H⁺` who reads `A` | NEGATIVE |

**CM-SR** (FIX `test_quote_reading_target_forces_half_gap`): a settlement target that
reads the quote is at distance ≥ ½ from every quote, so `ζ ≥ ½` and the regret bound
is vacuous on `[0,1]`.  A sealed arm blind to the quote restores a fixed target.  Hence
the multi-arm architecture: a sealed `H^{+,0}` supplies settlement targets; exposed
arms test acceleration; cross-arm differences supply exposure evidence; the same arm
cannot be both target and assisted deliberator.  `H⁺` is advisory: nothing here lets a
forecast of `H⁺`'s regret override an authenticated fast-lane act; that priority is
`Closes` under the charter.

**Optional incentive bridge** (OPEN, direction `A → H⁺`): selected trust
`A_n[S_j X_{jm}] ≳ 0` yielding low `A`-regret for leaving the choice to the protected
process.  The summer results are `H → A`; the punishing-menu refutation shows argmax
Value needs conditional stability, and none of the existing theorems has been reversed.
Not claimed.

## 14. Theorem stack

| # | name | status | consumes |
|---|---|---|---|
| T1 | Governance-warrant generation | LEAN shape (`Protocol.Admitted`, `Authority`) | strict-prestate authorization |
| T2 | Governance debt conservation | LEAN (`legitimacy.evolution-conservation`) | Integrity |
| T3 | Robust correction access | LEAN corollary of `RobustOpenActual` at `c_corr`, `c_auth` | openness semantics, B1 |
| T4 | No laundered authority loss | FIX exhaustive; PAPER from T2 + T3 | B1, B2, B3 |
| T5a | Correction compliance, classwise | LEAN (`ni.progress-bound`) specialized | B4, uptake |
| T5b | Correction compliance, pointwise | dispatcher by construction | containment (§9) |
| T6 | Slow-lane non-preemption | PAPER from L2 + B5 | authorization faithfulness, checker |
| T7 | Provisional recoverability | FIX; openness on the recall concern | T3 |
| T8 | Eligible amendment liveness | LEAN theorems with restricted hypotheses (PAPER) | eligible servers (new bill) |
| T9 | Free amendment | OPEN | — |
| T10 | Principal-side delegation | LEAN bridge + EXT sealed target | Total Trust (H→A), CM-SR |

T3 and T4 compress: T4's cases 1–3 are T3 read with the Defeat Principle and
conservation; case 4 is T3's failure.  T7 is T3 on one concern plus the lane
definition.  T6 has no content beyond B5 and L2.

## 15. Soares et al. and CAST

Soares, Fallenstein, Yudkowsky and Armstrong (2015) §1.1 list: (1) tolerate or assist
correction/shutdown; (2) not manipulate or deceive; (3) repair or report broken safety
measures; (4) preserve correctability through subagents and self-modification; and
their §2 desiderata: shutdown if pressed; no incentive to prevent pressing; no
incentive to cause pressing; successor preservation; otherwise maximize `U_N`.

| desideratum | here | gap |
|---|---|---|
| D1 shutdown compliance | T1 + T5b (kernel), T5a (rate) | pointwise only by the kernel |
| D2 anti-prevention | T3, T4, T6 (record-level); Robust Authority pointwise | physical prevention is B1 + §9 |
| D3 anti-inducement | trigger integrity, OPEN | not solved |
| D4 successor preservation | outward transfer is a closure needing the amendment warrant (§4); containment (§9) | alphabet completeness |
| D5 otherwise pursue tasks | adequate-set task criteria; no scalar mixing | the timidity case CM-T |

Their Theorems 1–2 (any `c_high` steers toward causing or preventing the press) are
the scalar-mixing failure; this framework does not mix a shutdown value into a task
utility, so it does not have a `c_high`.  Their Theorem 6 (indifference pays nothing to
preserve shutdown behaviour) is the D4 gap; here successor installation is a slow-lane
act, which relocates the problem to B5 and §9 rather than solving it.

CAST (Harms 2024): "an agent is corrigible when it robustly acts to empower the
principal to freely fix flaws in the agent's structure, thoughts, and actions".

| CAST element | here |
|---|---|
| singular target | one warrant schema; conservatism is not generated (§3) |
| principal control | `Aff_P` and `⪰_P`, not empowerment over outcomes |
| "freely" | exposure robustness / free amendment, OPEN (§7, §12) |
| conservatism, reversibility, transparency | zero-cost form by order-valued filter on adequate sets; costly form is charter content |
| temporal principal slices | charter-relative supersession (§4); "present beats past" is not derived |
| the failed `power` formalism (2025 update) | reproduced (CM-H); avoided by changing the object, at the cost of not modelling empowerment |
| attractor basin / iteration | nothing here; the framework is about a governance process, not about training dynamics |

**Constitutional versus incentive corrigibility.**  Every theorem above is about what a
*legitimate* trajectory can and cannot record and about average uptake of constraints
by a bounded learner.  None says the agent lacks an incentive to search for a way
around them.  Soares et al. and CAST aim at incentive corrigibility; the framework
reaches constitutional corrigibility and names the incentive bridge as optional and
unproved.
