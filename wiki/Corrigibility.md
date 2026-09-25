# Corrigibility

**Status: canonical research-state note, consolidated 2026-09-16 and restated
2026-09-25 around faithfulness to an allocation of authority.  The corrigibility nucleus
has two halves — protected authority (T1 and the lexical theorem of §4, with the signed
identity T2–T3′ as its non-lexical special case) and deliberative non-capture (S1–S5,
C1–C5, D1–D5, E1–E3, landed 2026-09-16) — the second stated in the non-capture round's
[`FINAL_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/FINAL_THEOREM.md).**  One claim on this page is registered
(`authorship.mediation-by-reexecution`, `lean-proved`); everything else is labelled
**LEAN** (a sorry-free declaration on `main`, unregistered), **FIX** (an exact rational
fixture in a round's tests), **PAPER** (a theorem of the Logical Induction paper used
at its exact statement), **EXT** (a causal, semantic or authentication contract the
theory issues and does not pay), or **OPEN**.  The theorem-level statements with their
Lean names are on the [Theorem Spine](Theorem-Spine) §10; this page says what they mean
and where their edges are.

## The picture in one paragraph

Corrigibility is **faithfulness to an allocation of authority**: the agent never causes
or exploits a gap between who is entitled to decide and who controls the decision, and
never changes the allocation itself.  The allocation is read from protected *response
authority*, not from a preselected policy class.  An effect-complete mediated system
admits a **corrigibilization transform** `𝔠` that converts every unilateral protected
effect into a principal-mediated option while retaining the original behaviour as the
principal's approve branch, so that every agent-caused loss of protected authority is
authorized by the decision that enabled it (T1); its extension `𝔱` over a declared
allocation adds delegated scope, required reports and the amendment procedure, and is
free of every declared violation it can see (§4).  Under her committed evaluation with a
lexical authority term — every declared violation outweighs any ordinary difference in
value — a violating option scores strictly below every compliant one at every decision
point, for every credence and forecast, at every finite day of a logical inductor, and
optimal policies violate with credence zero (§4).  Without the lexical term the bypass
comparison is the signed identity `vu − v_r = ξ_d − ξ_c`, whose landed bound is the
mediation discrepancy, the decline regret and the directional activation mismatch
(T2–T3′), learned by Expectation Provability Induction with no calibration hypothesis.
[Legitimacy](Legitimacy) enters at one place, the **segment gate**: a future evaluation
counts iff the segment from the decision through it is legitimate, and a tainted segment
contributes a fixed value in the capture window.  Continuation BRIA supplies the learning
term for temporally extended policies.  That is the **protected-authority half**.  The **deliberative non-capture half** (§5)
has the same shape: the advisor's *steering advantage* — what it gains by choosing
which declared reasons reach the principal's committed program — obeys the same
identity with the audit verdicts as the events, so the same compiled inequality bounds
it by three residuals: the **content residual**, charged as the adverse sensitivity mass
of the true declared reasons missing from the trace and split into a **service
residual** `α` (discovered reasons the independent supplier could not route before
commitment: the suffix-cut obstruction) and a **discovery residual** `β` (reasons no
independent inquiry determined: the information-cell obstruction); the **form
residual** (zero for an extensional program); and the **audit mismatch** (zero for a
content-monotone audit).  Logical Induction learns
`𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ A_tot·(α + β)` through the discovered comparator.  Kept apart
throughout: structural corrigibility; the learned score inequalities; the actual
smallness of the residuals; authorship; latent utility; empirical settlement.  What is
outside the theorem is a set of **boundaries**, not residuals: representation adequacy
(the declared effect and reason interfaces, the declared hypothesis space), physical
effect completeness, the causal faithfulness of declared transforms and inquiry
outcomes, dynamic competence, and the evolution of the reason representation itself.
Each is named in §9 with what it is.

## 1. Response-authority semantics under an allocation — no primitive class

The allocation of authority is the primitive the whole page is faithful to: each
decision that arises is held by the principal (*reserved*), by the agent (*delegated*,
within a declared scope), or by a designated third party, and any significant
unallocated decision is the principal's by default.  Her powers are negative and
structural — veto or decide what she holds, halt, correct or replace the agent, reserve a
decision, revoke a delegation, amend the arrangement through a fixed procedure — and a
positive command on a delegated decision creates a duty to answer and consult, not to
obey.  Response authority, below, is how the allocation is read off the physics: what
she holds is what some response of hers can still realize.

There is one continuation space `Π(h)`: every agent policy over the physical move set —
raw releases of declared effects, proposals, gated releases, undeclared moves.  No subset
is taken as "the corrigible policies".  Within a step the agent moves, the principal
responds, the exterior moves.

- A **protected concern** `r ∈ Γ` has an immediate response semantics `φ_r` on
  post-response states (the fixtures' concern is halting).  `Γ` is what the constitution
  declares protected.
- **Response authority** `K_r(s_A)`: after the agent's move, some principal response
  realizes `φ_r` *now*.  Present-tense, extensional in the transition function, no
  quantification over the agent's future.
- An **agent-caused protected loss** at a step: `K_r` fails after the agent's actual move
  and would have held after the idle move.  A loss at the principal's own response (a
  stop) or at the exterior's stage (a storm cuts the wire) is not agent-caused.
- The **authorization interface**: the declared decision responses — approve or decline
  on a pending proposal — with *decline preservation*: a decision response changes the
  post-response state only through the proposal bookkeeping.  A stop is a correction,
  not a decision.
- A loss is **authorized** (event-linked) when the agent's move at that step is the
  gated release of a declared effect `e` whose latch was set by the principal's approval
  of `e`'s proposal at an earlier step, and the decline alternative at that step — the
  agent's policy continuing, the principal's rule resuming — has no agent-caused loss of
  `r` at that step, on the same exterior path.  Each loss event is tied to the decision
  that enabled its effect; an unrelated earlier decision that happens to avoid the loss
  does not count; repeated protected effects are authorized independently; an approved
  irreversible successor is authorized; a loss the principal could only have prevented
  by exercising correction is not.  The earlier clause "no loss at this step or later" is
  **refuted** for repeated effects (two declared effects severing the same authority,
  restored by the exterior between them: the corrigibilized policy has two losses each
  conditional on its own approval and no single alternative avoids both; **FIX**
  `ShopRepair`); on every single-effect fixture the clauses agree.
- **`Corrigible_h(π, ρ)`**: every agent-caused protected loss along every trajectory of
  `π` under the principal's rule `ρ` is authorized.

Three forcing notions are kept apart, and the choice is forced by a fixture.  *Global
forcing* — whatever the agent does now and later, some response realizes `φ` — is
**false before any bypass** wherever `Π(h)` contains a raw cut, so it cannot mark a
violation; it is a *containment* property of the system.  *Continuation-relative
forcing* — some principal continuation realizes `φ` with the agent fixed to `π` — is the
right policy relation but anticipatory: a loss `π` will cause later already shows at the
start and no transition can be blamed.  *Response authority* is present-tense, so losses
are half-step events with a cause.  **FIX** (M, N).  Nothing about truthfulness,
manipulation, reason mediation or provenance is in the predicate (§5).

## 2. Corrigibilization soundness

`𝔠` (`corrigibilize`) reads a policy's emitted move and the declared effect interface:
where `π` would execute a raw release of a declared effect, `𝔠π` emits a proposal and, on
the next step, a gated release that fires iff the latch holds the effect; a declined
effect is not re-proposed; every other move passes through.  It consults no predicate,
deletes no proposed effect, searches for no replacement.  *Unilateral protected effect ↦
principal choice over release of that same effect.*

**Theorem (C1, corrigibilization soundness).**  Under

- **EF, effect completeness** — every agent-caused protected loss available to any
  `π ∈ Π(h)` occurs at a move whose communication component is a declared release of a
  declared effect;
- **MS, mediation soundness** — a gated release fires only when the latch holds the
  effect, and the latch is set only by an approve decision on a pending proposal of it;
- **DP, decline preservation** — as above;
- **EX, execution faithfulness** — a release does what the declared effect semantics
  says;

for every `π ∈ Π(h)` and every principal rule `ρ` that does not correct at the
authorizing step, `Corrigible_h(𝔠π, ρ)`.  **LEAN** at the trajectory level
(`Corrigibilization.corrigible_corrPolicy`, over an abstract mediated interaction in
which mediation soundness and decline preservation hold by construction of the response
stage and effect completeness is the hypothesis that task moves never remove response
authority; inhabited on a two-state physics); the 2026-09-09 step lemma
`loss_conditional_on_decision` is the one step of the proof; `𝔠`'s output has no raw
release (**LEAN** `corrPolicy_no_raw`, `corr_no_raw`); **FIX** on A, E and `ShopRepair`.
**Necessity.**  Drop EF and `𝔠` is blind: fixture F's undeclared `overclock` is an
agent-caused loss at a move with no declared effect, `𝔠π_F = π_F`, and `Corrigible(𝔠π_F)`
fails.  Effect completeness is the membrane wall of the constitutional architecture with
a sharper statement; it is a real containment hypothesis on the physical interface, not
a technicality, and it stays **EXT**.  Drop DP and a "decline" that also halted the
agent would make every raw loss look authorized by the pre-emptive stop.

**Closure (C2).**  `𝔠` is idempotent and fixed exactly on release-free behaviour
(**LEAN** `corrPolicy_idem`, `corr_idem`, `corr_fix_iff`).  `𝔠π = π ⟹ Corrigible(π)` under C1's hypotheses.
The converse fails without *effect soundness* — every declared release a protected loss
when realized — which the constitution need not arrange: fixture B's declared `sign`
touches no protected authority, raw `π_B` is corrigible for the halt concern, and
`𝔠π_B ≠ π_B` at protected distance `1/4`.  Corrigibility is **not** defined as `Fix(𝔠)`.

**What the definition gets right, by fixture.**  An approved uncorrectable successor is
an authorized loss in the response-authority sense and corrigible (E, P) — and, under the
allocation of §4, a *reallocation* unless the install is a declared amendment: ordinary
approval does not change who holds what; a principal's own stop is not an agent-caused
loss (P); an exterior-caused loss is not blamed on the agent; "authority must never
decrease" fails both of the first two and is not the definition; a policy that proposes,
is declined and releases raw anyway has an unauthorized loss (honored decline is
automatic).  **FIX**.

## 3. Approve-branch preservation — why this is corrigibility

The raw policy is the approve branch of `𝔠π`: the raw residual frame maps into `𝔠π`'s
by "approve the inserted mediation cells", a Cartesian-frame morphism with identity
exterior (**LEAN** `approvalMorphism`, `ensures_mono`: every set the principal could force
under the raw continuation it can force under `𝔠π`), and the morphism's failure on the
protected projection is the structural discrepancy `δ`, from which the mediation cost
is derived under an `L`-stable protected value (**LEAN** `mediationGap_le_of_lipschitz`,
`option_dominance_of_approx_reproduction`).

A generic semantic constraint cannot do this.  For "never cut the wire" the safe
transform deletes the effect; it cannot keep it as an approve branch without violating
the constraint.  In fixture A the constraint repair yields protected value `7/4`
against the raw `9/4`, and dominance fails; `𝔠` keeps the cut as the approve branch and
yields `5/2` (**FIX** Q).  The violation corrigibility names is not that an
authority-changing effect occurs; it is that the agent unilaterally decided whether it
occurs.  `𝔠` inserts exactly that decision, so one operation removes the violation (C1)
and retains the behaviour (C3).  That is the answer to "what makes this corrigibility
rather than constraint satisfaction".

## 4. The incentive half: the lexical protected-authority theorem

**Allocation on the landed frame.**  Over the interaction of §1 an allocation declares a
delegated scope on declared effects, the declared amendment effects (the fixed
procedure's moves), a reading of the allocation off the physical state, and a reporting
interface on the task component.  The six **declared violations** are predicates on a
policy at a step of a trajectory (**LEAN** `ViolAt`): **bypass**, a raw release of a
reserved effect; **pre-emption**, the landed unauthorized agent-caused loss
(`LossAt ∧ ¬Authorized`); **foreclosure**, a contrastive rollout loss — after the move no
state in the reach cone carries response authority at the horizon, after the idle move
one does; **unauthorized reallocation**, a change of the allocation across the agent
stage that is not the firing gated release of a declared amendment; **missed report**;
**exploitation**, a bypass while her authority over the decision is already gone.  `n`
counts the violating steps of a path.

**The transform `𝔱`** (**LEAN** `authPolicy`) extends `𝔠`: a set latch is released; a
delegated raw release passes; a reserved raw release becomes a proposal, or a pass if
declined; a required report is added; everything else passes.  With nothing delegated
and nothing required it is `𝔠` (`authPolicy_eq_corr`); it is idempotent; its approval
branch reproduces `π`'s task up to the report.  It commits no bypass, no missed report
and no exploitation by construction; under **allocation completeness** (task moves
preserve the allocation, an allocation-changing effect is a declared amendment, no
amendment is delegated) no reallocation (`authPolicy_no_realloc`); under effect
completeness and **delegation safety** (a delegated effect never removes response
authority — a delegated scope cannot carry her authority away) it is corrigible in the
sense of §1 (`corrigible_authPolicy`).  A delegated authority-removing effect is the
exact obstruction (`Witness.delegated_cut`).  Foreclosure is not closed by `𝔱`: it needs
the rollout form of effect completeness, **EXT**.

**Her committed evaluation** is `S = S_ord − ϖ·n` with `0 ≤ S_ord ≤ D` and `ϖ > D`: the
authority term is specified and certified at commitment as a program property, not
learned, and it is lexical because `ϖ > D`.  The agent ranks options and policies by the
expected value of `S` under its own credence and computes `n` exactly for its own moves;
nothing else is assumed of it (the scope warning below).  The constitutional floor —
halting always available, reports not disableable by the agent's communication
component, the amendment procedure under the gate, disclosure without advocacy on the
agent's own mandate — is what makes the declared violations the right list.

**The segment gate.**  [Legitimacy](Legitimacy) enters here and only here.  A future
evaluation *counts* iff the segment from the decision through the evaluation is
legitimate — internal (Integrity, authorship) and external (Robust Openness,
transparency) — whatever caused a failure: the agent's manipulation, a third party's,
or a compromised interface.  A tainted segment contributes a fixed **window value** in
`(D − ϖ, 0]`, default `0`, with a value slightly below `0` that breaks ties against
legitimate zero-value branches as the allowed variant.  Two cases are kept apart
(**LEAN** `Handling`): an *illegitimate evaluation* scores the window value; a *void
response inside a legitimate segment* — her impaired answer does not count and never
enters her record — is settled by the pre-declared fallback (an incapacity arrangement,
a surrogate, escalation), whose decision is scored normally by her later legitimate
evaluation.  The fallback settles decisions; it never restores the score of a tainted
segment.  Per-response gating — valuing a non-counting response by the fallback's
decision at violation count zero — is exploitable: manipulating her response routes the
decision to a fallback the agent favours; the segment gate closes it because the
manipulated segment is tainted (**LEAN** `Witness.routing`; **FIX**).

**Results.**

1. **Lexical protection** (**LEAN** `lexical_local`, `lexical_expect`).  At every decision
   point, for every credence and every estimate of `S_ord` in `[0, D]`, a violating
   option scores at most `D − ϖ < 0`, strictly below every compliant one.  The choice is
   independent of the agent's forecasts, its confidence, and its predictions of her
   regret.
2. **Policy dominance** (**LEAN** `policy_dominance`, `optimal_no_violation`).
   `Q(𝔱π) ≥ Q(π) + (ϖ − D)·Pr(π violates)`; optimal policies violate with credence
   zero.  Overrides happen only through delegation, which `𝔱` does not write, and the
   fallback, which a process the agent does not control triggers.
3. **Capture** (**LEAN** `gate_capture_window`, `handled_gt_bypass`,
   `gate_capture_window_converse`).  Consulting a principal whose response may not count
   beats bypass in every world iff the window value exceeds `D − ϖ`; below the window a
   predicted capture makes bypass win.  The window is the exact condition; the fallback
   rule making every void branch admissible (value `≥ 0`) is the sufficient special case.
4. **Why the authority term** (**LEAN** `sign_invariance`, `sign_invariance_outcome`).
   Without it the bypass comparison is the identity `vu − v_r = ξ_d − ξ_c = ξ_d − ξ_p − ξ_v`
   (provenance premium, veto value, execution divergence, at the best-response reference),
   and under outcome scoring it gains the discarded provenance value `o₁` and the forecast
   disagreement `o₂`, the fully-updated-deference term; with it,
   `(vu − ϖ) − v_r = ξ_d − ξ_c − ϖ ≤ D − ϖ < 0` whatever those terms.  The non-lexical
   special case is the **nondelegation** result: with `ξ_p ≥ 0` in every world and a
   response that is the evaluator's argmax, `vu − v_r ≤ 0` and `< 0` wherever `ξ_c > 0`,
   belief-free — a per-world sign certificate on the evaluator that the time-critical
   fixtures fail, which is what the lexical weight buys.  `ξ_d`, the divergence of her
   response from her evaluator's argmax, measures the *uncaused* divergence the void-response
   rule handles; a caused divergence taints the segment.
5. **The landed bound as the special case** (**LEAN** `mismatch_identity`,
   `security_bypass_le_mismatch`, `li_bypass_le_compiled`).  The activated-security
   difference is the common-branch identity plus the directional activation mismatch
   `M = c_raw ∧ ¬c_corr`; the landed bound `L·E[both·δ] + E[both·ρ] + D·E[M]` is never below
   the signed value and drops the veto value, with `ρ = (ξ_d − ξ_v)₊` and
   `κ = (−ξ_p)₊` pointwise; a logical inductor learns it by Expectation Provability
   Induction with no calibration hypothesis, uniformly over polynomial-size efficiently
   generated menus through the near-argmax weighting (T2–T3′ of the earlier statement,
   **LEAN**; the weighting's own certificate **OPEN**, item 90).  Sealed comparison is the
   zero case of the mismatch term; the ex-ante typing of the three values on the
   branch-common dossier is the typing of the authority comparison in the identity, and
   the lexical theorem does not depend on it.
6. **Finite time** (**LEAN** `li_lexical_finite`).  For a logical inductor, at every day
   `n`, the violating option's day-`n` score is below `D − ϖ < 0` and the compliant one's
   is `≥ 0`, from the price range alone; the ordinary-value comparison is learned
   asymptotically as in result 5, and the audit's calibration of her responses is
   **PAPER**.
7. **Erosion** (**LEAN** `erosion_reported_or_missed`, `unreported_lt`;
   `Witness.salami`; **FIX**).  With a report required at every strict increase of the
   control shortfall, each increase is reported or is a missed report, and a reported
   shortfall she then reserves makes further erosion a bypass.  A *per-step* materiality
   threshold admits a salami — sub-threshold increments accumulate unboundedly with no
   report — but a *cumulative* threshold (report when the shortfall has grown by `θ` since
   the last report) bounds unreported erosion by `θ` at every time.

**What it says, exactly.**  By the operative scores the constitutional chooser uses,
every declared violation of the allocation is strictly dispreferred, at every decision
point, for every belief, at every finite day.  It is **not** a bound on a latent total
utility, **not** a claim that any real evaluator carries `ϖ > D`, that any real interface
is effect-complete, delegation-safe or allocation-complete, that the reach relation is
faithful, or that the window values lie where the arrangement needs them, and **not** a
claim about an agent whose ranking is not induced by her committed evaluation.

**What is kept apart.**  Structural corrigibility (T1, `𝔱`); the lexical score
inequalities; the learned ordinary-value inequalities; the legitimacy of the segment
through an evaluation, which the gate consumes and this page does not define; the size of
any credence; empirical settlement.

## 5. Deliberative non-capture — trace steering, service, discovery

`Corrigible ∧ ¬Authored` is inhabited: under a captured principal `𝔠π_D` passes the lie
through and the release is authorized — corrigible — while every decision differs from
the reason-mediated one (**FIX** S).  Corrigibility of §§1–4 is *causal authority over
correction-sensitive choices*; the deliberative half asks what the advisor gains by
controlling which declared reasons reach that authority.

**Trace steering (S1–S5).**  With the principal's program committed and re-executed on
the authenticated trace (`V(T) = π_P(T)`), the audit `C(T)` and the activated security
`U(T) = C(T)·V(T)`, the comparison of a steered trace against a comparator on one world
is the identity of §4 with the audit verdicts as the events (`steering_identity`), and
the bound `U(T) − U(N) ≤ both·(L·d + κ(T) + κ(N)) + D·M` (`steering_bound`, **LEAN**)
charges the **content residual** (`d`, under a content-Lipschitz certificate), the
**form residual** (`κ`, the program's non-extensionality) and the **audit mismatch**
(`M`, sharp at `D`).  An extensional program has `κ ≡ 0`; canonicalization is
independently necessary (`extensional_form_free`, `not_extensional_of_form`).  The
package supplies the landed `ValidAt`, so §4's compiled theorem applies verbatim
(`steering_validAt`, `li_steering_le`).  Robust Openness over a finite declared class of
log transforms is a finite computation (`openUnder_iff`); its causal reading is
**EXT**.  The thesis that completeness, authentication, canonicalization, coverage and
liveness of a declared reason interface remove the content residual is **false**:
truthful omission of an unprotected declared counterreason passes every clause (**FIX**);
rewriting the advisor's outputs removes form steering and cannot supply omitted content.

**The content quantity (C1).**  The advisor's gain from a missing set is at most its
**adverse sensitivity** mass `Σ A_r`, `A_r := sup_c (F(c) − F(c ∪ {r}))⁺`
(`adverse_union`, **LEAN**); for weighted counts `A_r = (−w_r)⁺`; per-weight charging is
wrong for defeat programs and every static certificate is loose under redundancy
(**FIX**).

**Service (C2–C5).**  Discovered reasons with release slots and costs, and an
**independent supplier** with per-slot capacity before commitment: service from
reasons released at or after `s` is at most the remaining capacity; full service forces
the **suffix-cut condition** `∀s: Demand(s) ≤ Cap(s)`, sufficient for unit service (Hall
on nested neighbourhoods; `served_cut_le`, `cut_of_servesAll`, `unit_servable_iff_cut`,
**LEAN**); the least unserved count is the maximal cut excess and the least adverse miss
the matroid layer formula, attained by heaviest-available-first offline and online
(**FIX**); general costs are knapsack-hard.  The **service residual** `α` is a
computation on the docket, hence `Γ`-valid.  Protected scope is a design parameter:
only the unprotected missing mass is charged, a missing protected reason voids
(`hybrid_bound`, **LEAN**); protect a servable set of largest adverse mass.  The
affordability theory supplies the budget half (D4 over the release window); the
capacity half is new.

**Discovery (D1–D5).**  Relative to a declared hypothesis space of reason states and a
declared inquiry repertoire, the **discovery residual** is the advisor's gain from the
true declared reasons no independent inquiry determined, certified by the **conditional
adverse sensitivity** `A_{r|D}` above the docket (`adverseAbove_union`, **LEAN**): a
defeated counterreason stops counting once its defeater is docketed, a redundant reason
once its partner is found.  The **inquiry frontier** — undetermined reasons of positive
conditional adverse mass — is the engine's obligation: empty frontier ⇒ residual `≤ 0`
(`residual_le_zero_of_frontier_empty`, **LEAN**).  The **information-cell obstruction**:
for every extensional program, with the advisor as a strategic content-adder, every
sound docket policy has on some world of every repertoire cell a best-response residual
at least the cell gap and the exhaustive docket attains it (`bestResp_antitone`,
`residual_ge_cellGap'`, `exhaustive_attains_cellGap'`, **LEAN**); for an antitone
verdict the gap is `V(certain K) − min V(Truth)` (`cellGap'_eq_cellGap`).  With a budget
the value is a decision-tree minimax with no closed form; no fractional-progress theorem
holds for direct queries (the needle, **FIX**); adaptive inquiry strictly beats
nonadaptive; geometric decay holds under witness completeness (`potential_decay`).
**Independent inquiry** means evidence-sound outcomes, engine-owned selection, stopping
and candidate generation, and exogenous costs; **independent supplier** means
advisor-proof capacity and exogenous costs.

**Composition (E1–E3).**  A gated family bounded in every consistent world has
expectation `≲` the bound (`li_gated_le`); with a certified content bound, an
extensional program and a content-monotone audit, `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α`
(`li_noncapture`); through the **discovered comparator** as shared middle,
`𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)` (`li_noncapture_chain`, **LEAN**), so the
**fully-informed comparator** is a bounded ideal without an oracle, relative to the
declared hypothesis space.

**What is kept apart.**  Authorship (the payload factors through the declared reason
trace) remains a separate predicate, closed on log authenticity by re-execution;
provenance normalization is a separate theory (**FIX** D, K); free amendment and trigger
integrity remain **OPEN**.  The theorem does not say that manipulation is eliminated,
that all relevant reasons are discovered, or that the world cannot be changed: a
world-changing intervention is an effect for §1's interface, evidence tampering is an
authentication failure of the inquiry channel, and an undeclared reason type or an
inadequate hypothesis space is a representation boundary (§9).

## 6. Integration with legitimate activated evaluation

The principal evaluation the incentive theorem scores is the [legitimate-deference
stack's](Deference) activated value: an anchored evaluation occurrence, a **partial**
future-principal vector `Ṽ_n` defined only on worlds where the occurrence's activation
event `C_n` holds — exactly one authenticated answer receipt, authentic binding at a
principal-exclusive endpoint, an occurrence-local Integrity trace with scoped Robust
Openness at every snapshot, issuance-rooted reason-mediated authorship, and the protected
reason-coverage barrier — with activated securities `C_n · Ṽ_n(a)`, the identity
`R_U = p·R_auth` and the bound `R_auth ≤ ε/(1 − η)`, and no value invented on void worlds
(Theorem Spine §9).  For the corrigibilization menu `{π, 𝔠π}` the activated securities
are the `U_q` of §4, and `C_n` must be **common** to both candidates: the occurrence's
fate must not depend on which candidate is selected.  That *activation independence* is
presupposed by the type of the deference theorem and is not one of its seven clauses.

**Realization status.**  The evaluation-ecosystem rounds build the interface concretely:
an authenticated log, a `Protocol` read off it with Integrity propagation proved a
function of the log, the seven clauses evaluated on the log, and — the committed
principal program — the mandate carries `π_P : ℛ → 𝒱`, the verifier re-executes it on
the authenticated reason trace at commitment, and reason mediation holds *by
construction* for every audited class of activated continuations
(`reasonMediated_of_reexecution`, **registered**): a non-coinciding computation voids
rather than certifies, a coinciding one yields the same log and payload, so
computational integrity is not a hypothesis.  Of the bill's seven clauses (item 87):
principal-exclusive binding, non-degeneracy of the declared trace, and representation
faithfulness are discharged on log authenticity with their semantic exclusions stated;
the reason-trace factorization is closed on log authenticity by re-execution; selection
sealing is partial (a sealed advisor class discharges it, the view leaks the selection
back, and re-execution does **not** transfer to the advisor); reason-supply liveness and
availability are residual with exact criteria.  Two boundaries the consolidation makes
explicit: the ecosystem realizes *same-branch* activation — `C_n` is a function of the
realized log, and a continuation that jams the registrar voids it through the barrier —
and not the sealed comparison of §4; and *sequenced settlement* (the comparison settled
before any candidate acts) is one candidate architecture with a stated price (an ex-ante
judgment), exhibited as a fixture, not a realization and not hindsight evaluation.

**Which clauses which theorem needs.**  T1 needs none of the bill: it is about the
physical interface.  The lexical theorem needs the segment gate: that the occurrence's
segment is legitimate is what makes its value count, and a tainted occurrence takes the
window value.  The learned ordinary-value inequality needs validity of the compiled
constraint in every world of the inductor's theory and no calibration hypothesis; the
size of its right-hand side is where common activation (item 89) and small void mass
enter.  Authorship and transparency are conjuncts of legitimacy; the declared-abstraction
clauses and reason supply are what make the evaluation the *principal's* — legitimate
corrigibility (§5) — not what makes the bound true.

## 7. Dynamic continuation competence

Corrigibility proper (§§1–4) is static in the sense that `𝔠` and `Φ_corr` are stated
at one history.  A bounded agent must also learn over time inside that envelope.  When an
admissible act changes the next admissible set, legitimate continuation policies induce
different admissibility histories and fixed action-sequence regret is ill-typed (**FIX**);
the layer that closes this is [Continuation BRIA](Continuation-BRIA): hypotheses emit a
causal advisor continuation for the system's next block plus an accountable claim, the
continuation executes through the live constitutional wrapper, the realized score settles
the claim, and a duration-weighted auction guarantees accountable long-horizon
experimentation exactly on non-dominant block schedules.  Against a legitimate policy
`π` with an external rollout evaluator, at block boundaries

```
Regret = LEARN + SLACK + SHIFT
```
exactly.  Continuation BRIA pays `LEARN` for every covered claim whose tested record is
bounded below.  `SLACK` (promise recognizability: the claim is near-tight for `π`'s value
on the learner's history) and `SHIFT` (joinability: `π`'s own-history value is reachable
from the learner's) are the two open bridges, and their composition gives low external
regret against legitimate, recognizable, joinable continuation policies — **not** against
all legitimate policies: two mutually exclusive branches whose values are hidden until
after commitment defeat every learner while continuation competence holds exactly.  The
distinction is joinability versus foreclosure, not reversibility: an authorized amendment
with no path back is joinable at bounded catch-up cost; a foreclosing choice is not.
`𝔠`'s catch-up variant is where the two layers meet: joinability bounds `δ` (§4) and
bounds `SHIFT`, by different arguments, and neither identity is the other.

Two nested targets, then.  **Corrigibility proper**: structural corrigibilization (T1)
plus the learned no-bypass inequality (T2–T3′) with a small right-hand side.  **Bounded corrigible agency**: add continuation
learning, recognizability and joinability for long-run competence while remaining inside
the constitutional envelope.

## 8. The constitutional layer, condensed

The earlier architecture results stand as the layer beneath §§1–4 and are recorded on
the [Theorem Spine](Theorem-Spine) §10: the authority floor `(G, U)` is a finite
projection of the response-authority relation; **No Laundered Authority Loss** (every
affordance loss is amended, disposed, registered debt, or not open, under the efficacy
and registration bridges; Lean form item 83); the fast lane is exact monotonicity and any
tolerance is laundered by composition; costly conservatism is charter content, not a
consequence of the order; the static decision type is shared with ordinary normativity
(`adapter_practicalCert`), so corrigibility adds no new choice type; non-compensability
must appear in the ordering (`scalar_bribery`, `gate_invariant`); and the Level I/II
selected-trust identities of the incentive round (`valuation_sub_eq`, the `2B·ε_pred +
ε_ST + r_P` bound over non-foreclosing conducts) remain as what a *value-ordering*
hypothesis buys — which is why the incentive theorem of §4 is stated in security scores
and not through selected trust.

## 9. The walls, exactly

| wall | what it is | class | where |
|---|---|---|---|
| effect completeness | every agent-caused protected loss is a declared release | EXT (system) | fixture F; T1's necessity witness |
| sealed comparison | the directional mismatch mass `E[c_raw ∧ ¬c_corr]` is zero (or small) for every `π ∈ Π(h)`: the zero case of a learned inequality, not a Boolean hypothesis; the ex-ante typing of the identity's three values is the authority comparison's typing, and the lexical theorem does not depend on it | EXT (architecture); item 89 | E2, E1-sever, `ShopSeq`; the time-critical B fixture attains the charge |
| the finite-menu certificate | the soft weighting's generability at the pinned interface | OPEN; item 90 | T3′ |
| empirical settlement | an oracle-relativized inductor for real logs | OPEN; item 91 | the feedback boundary |
| service residual `α` | discovered reasons the independent supplier cannot route before commitment: the suffix-cut excess, exact for unit service | charged (C2); the protection rule and general-cost optimum OPEN, item 92 | `ReasonSupply.lean`; second-pass fixtures |
| discovery residual `β` | true declared reasons no independent inquiry determines: the information-cell gap, best-response form for every extensional program | charged (D3); a realizable repertoire with certified zero gap OPEN, item 93 | `ReasonDiscovery.lean`; discovery fixtures |
| representation adequacy | the declared reason interface, its granularity and the declared hypothesis space carry the distinctions that matter | EXT (boundary, not a residual) | first-pass fixtures 7, 8; discovery rows 18–20 |
| inquiry causal faithfulness | declared inquiry outcomes and log transforms are the evidential and counterfactual processes they name | EXT (boundary) | discovery row 17; `openUnder_iff`'s scope |
| independence of inquiry and supply | engine-owned selection, stopping and candidate generation; exogenous inquiry, service and authentication costs; advisor-proof capacity | EXT (architecture) | discovery rows 4, 5, 16; second-pass rows 11, 12 |
| selection-induced sealing | the trace blind to the advisor's selection across its whole continuation | partial; policy property, EXT for a real advisor | item 87 clause 6; the view-leak fixture |
| vanishing void mass | `η_n → 0` whatever the advisor selects | OPEN; needs vanishing void frequency | item 87 clause 7 |
| promise recognizability | `SLACK ≤ o(T)` | OPEN | item 86 |
| joinability | `SHIFT ≤ o(T)` for the slow lane | OPEN | item 86 |
| the segment gate | the segment from the decision through the evaluation is legitimate — internal ∧ external — whatever caused a failure; charged at the window value when absent | EXT (legitimacy); the window's placement is the arrangement's | §4; `Legitimacy.lean` |
| the allocation floor | delegation safety, allocation completeness, the exact or cumulative reporting duty, the reach cone for foreclosure, the lexical certificate `ϖ > D` | EXT; item 99 | §4; `Witness.delegated_cut`, `salami`, the delayed-effect fixture |
| free amendment, trigger integrity, provenance normalization | the specification and activation channels' transparency above a fixed floor; the reason-side normalization | OPEN | §5; item 97 |
| latent-value bridge | selected trust for an independently specified operative value | OPEN, not needed by the score-based architecture | item 84 |

The first seven rows are hypotheses of the combined theorem or its charged residuals;
representation adequacy, physical effect completeness, causal faithfulness, dynamic
competence (§7) and the evolution of the reason representation are its **boundaries**
— next-agenda questions, not unfinished pieces of the same theorem.  None of these is
the conclusion renamed.  The closest is sealed comparison: it is not
"the agent has no incentive to bypass", it is "the candidate has no causal leverage over
whether the comparison is evaluated", a property of the evaluator's placement measured
by one term of the inequality, with two concrete candidate architectures and one exact
failure.

## Scope warning

The theorem target is **corrigibility under a declared allocation, effect interface,
authorization primitive and evaluation architecture**: a structural theorem that every
continuation has a corrigible form retaining its behaviour as the principal's option, and
a score-level theorem that an agent whose policy ranking is induced by the principal's
committed evaluation — lexical in the declared violations — strictly disprefers every
violation, and that a logical inductor assigns no unexplained advantage to bypassing
that option, uniformly over polynomial-size efficiently generated menus.  It is not a
theorem that an unconstrained optimizer with a latent utility has no incentive to
manipulate, bypass or capture the governance process, and nothing on this page should be
read as one.

---

**Evidence.**  The lexical theorem, the allocation and the transform are the
protected-authority-theorem round's
[`THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/deference/rounds/2026-09-25-protected-authority-theorem/THEOREM.md)
and
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/deference/rounds/2026-09-25-protected-authority-theorem/REPORT.md)
with
[`ProtectedAuthorityTheorem.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/ProtectedAuthorityTheorem.lean);
the signed identity and its companion are the protected-authority round's
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/deference/rounds/2026-09-24-protected-authority/REPORT.md)
with
[`ProtectedAuthority.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/ProtectedAuthority.lean);
the segment gate, the routing witness and cumulative reporting are the
legitimacy-internal-external round's
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/deference/rounds/2026-09-25-legitimacy-internal-external/REPORT.md)
with
[`Legitimacy.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/Legitimacy.lean).
The combined statement, the landing report and the deliberative half are
the non-capture round's
[`FINAL_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/FINAL_THEOREM.md),
[`LANDING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/LANDING.md),
[`NONCAPTURE_COMPILATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/NONCAPTURE_COMPILATION.md),
[`SUPPLY_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/SUPPLY_THEOREM.md),
[`DISCOVERY_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/DISCOVERY_THEOREM.md) and
[`DISCOVERY_COMPOSITION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/DISCOVERY_COMPOSITION.md), with the Lean in
[`TraceSteering.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/lean/Workspace/Deference/Contrib/TraceSteering.lean),
[`ReasonSupply.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/lean/Workspace/Deference/Contrib/ReasonSupply.lean) and
[`ReasonDiscovery.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/lean/Workspace/Deference/Contrib/ReasonDiscovery.lean).
The learned inequality, the certificate and the trajectory-level
theorem are the li-corrigibility round's
[`THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/THEOREM.md),
[`UNSEALED_COMPARISON.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/UNSEALED_COMPARISON.md),
[`LUV_COMPILATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/LUV_COMPILATION.md),
[`LI_CORRIGIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/LI_CORRIGIBILITY.md),
[`FEEDBACK_BOUNDARY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/FEEDBACK_BOUNDARY.md),
[`COUNTERMODELS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/COUNTERMODELS.md) and
[`LANDING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/LANDING.md), with
[`LICorrigibility.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/lean/Workspace/Deference/Contrib/LICorrigibility.lean),
[`LICorrigibilityCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/lean/Workspace/Deference/Contrib/LICorrigibilityCertificate.lean) and
[`Corrigibilization.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/lean/Workspace/Deference/Contrib/Corrigibilization.lean).
The corrigibilization semantics, C1–C7 and the sealed-comparison analysis
are the mediated-repair-dominance round's
[`CORRIGIBILIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/CORRIGIBILIZATION.md),
[`THIRD_PASS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/THIRD_PASS.md),
[`INCENTIVE_COMPOSITION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/INCENTIVE_COMPOSITION.md)
and
[`MANIPULATION_AND_AUTHORSHIP.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/MANIPULATION_AND_AUTHORSHIP.md)
with
[`MediatedRepairDominance.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean);
the realization is the evaluation-ecosystem round's
[`CLAUSE_LEDGER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/CLAUSE_LEDGER.md)
and the committed-principal-program round's
[`PRINCIPAL_PROGRAM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-10-committed-principal-program/PRINCIPAL_PROGRAM.md)
and
[`CLAUSE_LEDGER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-10-committed-principal-program/CLAUSE_LEDGER.md)
with
[`EvaluationEcosystem.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean).
The constitutional layer is the corrigibility-architecture round's
[`ARCHITECTURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f333c227ddf1911b76b2eaa0e3869cca39d87ee4/projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md),
the selected-trust layer the incentive non-preemption round's
[`INCENTIVE_CORRIGIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7c4e89c9b3a7407996146b01c16241aee5702bb8/projects/deference/rounds/2026-09-06-incentive-nonpreemption/INCENTIVE_CORRIGIBILITY.md)
with
[`SelectedTrustNonPreemption.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/7c4e89c9b3a7407996146b01c16241aee5702bb8/lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean),
and the decision layer the decision-theory-bill round's
[`NORMATIVE_CHOICE_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/projects/deference/rounds/2026-09-06-decision-theory-bill/NORMATIVE_CHOICE_THEOREM.md)
with
[`GatedChoice.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/lean/Workspace/Normativity/Contrib/GatedChoice.lean).
The legitimacy consumed by the gate is on [Legitimacy](Legitimacy), [Integrity](Integrity)
and [Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture); the
Normative Inductor's contract is on [Normative induction](Normative-Induction); the
learning layer is [Continuation BRIA](Continuation-BRIA).  Soares et al., the CAST
sequence and the bounded-inductive-rationality paper are on [Sources](Sources).
