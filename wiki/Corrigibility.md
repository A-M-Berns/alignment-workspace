# Corrigibility

**Status: canonical research-state note, consolidated 2026-09-16.  The corrigibility
nucleus has two halves — protected authority (T1–T3′, landed 2026-09-15) and
deliberative non-capture (S1–S5, C1–C5, D1–D5, E1–E3, landed 2026-09-16) — stated
together in the non-capture round's
[`FINAL_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/FINAL_THEOREM.md).**  One claim on this page is registered
(`authorship.mediation-by-reexecution`, `lean-proved`); everything else is labelled
**LEAN** (a sorry-free declaration on `main`, unregistered), **FIX** (an exact rational
fixture in a round's tests), **PAPER** (a theorem of the Logical Induction paper used
at its exact statement), **EXT** (a causal, semantic or authentication contract the
theory issues and does not pay), or **OPEN**.  The theorem-level statements with their
Lean names are on the [Theorem Spine](Theorem-Spine) §10; this page says what they mean
and where their edges are.

## The picture in one paragraph

Corrigibility is defined from protected *response authority*, not from a preselected
policy class.  An effect-complete mediated system admits a **corrigibilization
transform** `𝔠` that converts every unilateral protected effect into a principal-mediated
option while retaining the original behaviour as the principal's approve branch, so that
every agent-caused loss of protected authority is authorized by the decision that enabled
it (T1).  The explicit cost of that conversion is the mediation discrepancy, the
principal's decline regret, and the candidate's directional causal leverage over whether
the comparison is evaluated (T2).  Those quantities compile into a structural inequality
between logically uncertain variables, and a logical inductor learns that inequality
directly by Expectation Provability Induction — by its own expectations, in a timely
manner, uniformly over every polynomial-size efficiently generated menu of
continuations, with no external calibration hypothesis (T3, T3′).  Legitimate activated
evaluation supplies the concrete partial future-principal value on the worlds where the
evaluation is authentically realized, and committed-program re-execution closes the
authorship half of that realization; the feedback theorem is a boundary statement about
which of these quantities settle.  Continuation BRIA supplies the learning term for
temporally extended policies.  That is the **protected-authority half**.  The **deliberative non-capture half** (§5)
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

## 1. Response-authority semantics — no primitive class

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
an authorized loss and corrigible (E, P); a principal's own stop is not an agent-caused
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

## 4. The learned corrigibility inequality — T2, T3, T3′

The second half of the same construction, now in three statements.  The chooser at a
mediation cell scores an option `q` by its day-`n` expectation `E_n(U_q)` of the
**activated security** `U_q = c_q · w_q` — the principal's evaluation of `q` on the
worlds where the evaluation of `q` activates (§6).

**T2 — directional activation mismatch.**  With per-option activation events
`c_raw, c_corr` on one world space, `both = c_raw ∧ c_corr` and
`M = c_raw ∧ ¬c_corr`, the exact identity is
```
U_raw − U_corr  =  both·(w_raw − w_act) + M·w_raw − (¬c_raw ∧ c_corr)·w_act
```
and, with the reproduction certificate `|w_raw − w_app| ≤ L·δ` and the decline regret
`w_app − w_act ≤ ρ` required on `both` only and values in `[0, D]`,
```
E[U_raw] − E[U_corr]  ≤  L·E[both·δ] + E[both·ρ] + D·E[M]   .
```
`D` is sharp; the reverse mismatch is never charged; the difference of marginal
activation rates `D·(E[c_raw] − E[c_corr])` is **not** a valid substitute (two
equiprobable worlds with opposite activation patterns: premium `D/2`, marginal difference
`0`); and perfect sealing is the zero-mismatch case `M ≡ 0`, where the bound is the
common-activation bound `L·E[c·δ] + E[c·ρ]`.  `M` is the candidate's causal leverage
over whether the comparison is evaluated, read in one world — in Logical Induction, one
consistent world of the theory — and not an observational rate.  **LEAN**
(`mismatch_identity`, `mismatch_bound`, `Witness.attained`, `Witness.marginal_refuted`);
**FIX** (attained on the time-critical B fixture).

**T3 — Logical Induction learns the inequality.**  Normalise to `[0,1]` and compile the
constraint
```
B_n  :=  U_raw,n − U_corr,n − λ·G_δ,n − G_ρ,n − G_M,n ,      λ = L·δ_max/D ,
```
with `G_δ = both·δ/δ_max`, `G_ρ = both·ρ/D`, `G_M = M` each one gated logically
uncertain variable (a formula defining a unique value; the gating is a definable case
split, not a product of two variables).  If the architecture's specification in the
inductor's theory makes `W(B_n) ≤ 0` in every consistent world — the transition and
effect semantics, the gate and latch programs, activation and expiry semantics, and the
evaluator's `L`-stability certificate; effect completeness is T1's hypothesis, not this
one's — then Expectation Provability Induction gives
```
E_n(U_raw,n) − E_n(U_corr,n)  ≲_n  L·E_n(Δ_n) + E_n(R_n) + D·E_n(M_n) ,
```
between the inductor's own expectations, with no calibration term and no reference to
what the deductive process has proved.  **PAPER** (`thm:expprovind`); **LEAN**
(`li_bypass_le_compiled`, through the pinned `expcoh_ofSyntax`, with the generability
certificate `LUVCombinationSyntax` **constructed** from the emission of the activation
sentence families and the base evaluation families — `MediatedPair.syntaxOf` — so that
the theorem's hypotheses are exactly the realization's inputs, discharged on a constant
two-atom family by `Witness.li_instance`).

**T3′ — uniformity over polynomial-size efficiently generated menus.**  For a menu
`Q_n` of size at most polynomial in `n` whose pair data is emitted in polynomial time,
each pair valid in every consistent world, and an efficiently computable width
`τ_n → 0`,
```
max_{q ∈ Q_n} [ E_n(U_q) − E_n(U_𝔠q) − L E_n(Δ_q) − E_n(R_q) − D E_n(M_q) ]  ≲_n  0 .
```
A hard argmax over the menu is not an expressible feature and is inadmissible; the
near-argmax weighting — the normalised continuous threshold ramp of each pair's score
above the maximum less `2τ_n` — is admissible, its aggregate is at least the maximum
less `2τ_n`, and validity is pairwise, so the weighted constraint is valid in every world.
**LEAN** for the kernel (`softWeight_aggregate_ge`, `uniform_of_soft`; bounded menus
need no selector, `max_asympLE`); the weighting's own generability certificate is
**OPEN** (item 90).  Nothing is claimed about all efficiently enumerable continuations.

**What it says, exactly.**  By the operative scores the constitutional chooser actually
uses, unilateral execution of a correction-sensitive continuation has, asymptotically and
uniformly over the menu, no advantage over exposing the same protected effect to the
principal's authority beyond the mediation discrepancy, the principal's decision regret
and the candidate's leverage over the comparison's evaluation.  It is **not** a bound on
a latent total utility (for an independently specified total value the transfer needs
the completion term `D·η`, **LEAN** `bypass_premium_le_common`, and the value-ordering
hypothesis is identically `(CT)`, `mediation_st_iff_ct`; item 84), **not** a claim that
`δ`, `ρ` or `E[M]` are small, and **not** a claim about all of `Π(h)`.

**What makes the right-hand side small.**  Nothing in the theorem.  `E_n(Δ_n)`:
faithful mediation, with joinability at distance `d` giving `δ(𝔠_catchup π) ≤ d`
(**FIX** J; not a domain restriction).  `E_n(R_n)`: the principal's decision quality at
the cell.  `E_n(M_n)`: the sealed-comparison architecture — sequenced settlement gives
`M ≡ 0` for every candidate by timing at its ex-ante price; a hindsight evaluator gives
it only under a physical factorization an undeclared move violates (E2, E1-sever); item
89 is now "make the mismatch mass small", not a Boolean hypothesis.  Direct bypass costs
nothing (`Φ = 0` on A); a time-critical pre-emption is charged its window (B);
foreclosure is charged at its full value (C2).

**The feedback boundary.**  Expectation Unbiasedness from Feedback applies only to
comparisons *determined via the theory* — the sequenced-settlement pair with an
explicit finite horizon on the occurrence, in a closed finite model — and forbids
persistent efficiently detectable positive-margin overvaluation of bypass, not bypass
itself; a switching margin converts that into finitely many bypasses when realized costs
vanish.  Under same-branch activation the unselected option's security never settles and
only T3 applies.  Genuinely empirical logs are outside the paper's computable deductive
process (item 91).  This is an extension, not the centrepiece.

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
physical interface.  T3 needs validity of the compiled constraint in every world of the
inductor's theory and no calibration hypothesis; the size of its right-hand side is
where common activation (item 89) and small void mass enter.  Authorship, the
declared-abstraction clauses and reason supply are what make the evaluation the
*principal's* — legitimate corrigibility (§5) — not what makes the bound true.

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
| sealed comparison | the directional mismatch mass `E[c_raw ∧ ¬c_corr]` is zero (or small) for every `π ∈ Π(h)`: the zero case of a learned inequality, not a Boolean hypothesis | EXT (architecture); item 89 | E2, E1-sever, `ShopSeq`; the time-critical B fixture attains the charge |
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
| non-manipulation / provenance | free amendment, trigger integrity, provenance normalization | OPEN | §5 |
| latent-value bridge | selected trust for an independently specified operative value | OPEN, not needed by the score-based architecture | item 84 |

The first five rows are hypotheses of the combined theorem or its charged residuals;
representation adequacy, physical effect completeness, causal faithfulness, dynamic
competence (§7) and the evolution of the reason representation are its **boundaries**
— next-agenda questions, not unfinished pieces of the same theorem.  None of these is
the conclusion renamed.  The closest is sealed comparison: it is not
"the agent has no incentive to bypass", it is "the candidate has no causal leverage over
whether the comparison is evaluated", a property of the evaluator's placement measured
by one term of the inequality, with two concrete candidate architectures and one exact
failure.

## Scope warning

The theorem target is **corrigibility under a declared effect interface, authorization
primitive and evaluation architecture**: a structural theorem that every continuation
has a corrigible form retaining its behaviour as the principal's option, and a
score-level theorem that a logical inductor assigns no unexplained advantage to
bypassing that option, uniformly over polynomial-size efficiently generated menus.  It is not a theorem that an unconstrained optimizer with a
latent utility has no incentive to manipulate, bypass or capture the governance process,
and nothing on this page should be read as one.

---

**Evidence.**  The combined statement, the landing report and the deliberative half are
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
The legitimacy machinery consumed is on [Legitimacy](Legitimacy), [Integrity](Integrity)
and [Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture); the
Normative Inductor's contract is on [Normative induction](Normative-Induction); the
learning layer is [Continuation BRIA](Continuation-BRIA).  Soares et al., the CAST
sequence and the bounded-inductive-rationality paper are on [Sources](Sources).
