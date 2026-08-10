# Theory 8: diachronic identity — migration, composition, transport, and the ledger

This part covers what survives when the vocabulary changes: how one migration is
certified, how migrations compose, how obligations and authority transport
across them, how local acceptance becomes global acceptance, and what the
answerability ledger records throughout. Every symbol used here is defined here.

## 1. Definitions

An **occurrence** is an item of record content with a sort, a status — active,
suspended, or terminated — and an identifier. A **migration state** is a finite
set of occurrences together with a compiler specification: an assignment of
credal content to the state's native distinctions.

A **migration certificate** presents, for each input occurrence, a
**disposition cell**: a mode — carried, refined, identified, suspended, or
terminally disposed — together with the target occurrences and the evidence for
that mode. A certificate is **accountable** when every input occurrence has
exactly one cell and every cell's evidence is present.

A **history** is a finite sequence of states joined by certificates. An
**administrative grant** is a declared transfer of authorization identifiers,
consuming tokens, and at most one retaken snapshot.

**Standing** is the entitlement to be answered; a **burden** is an unresolved
obligation. A **transport plan** assigns, for each input occurrence, where its
standing and burden go.

## 2. One migration

**Accountability is checkable.** {#AM-J1} **Status: PROVED (single
derivation).** Whether a certificate is accountable is decided by a finite
program over the two states and the certificate.

**Proof.** The conditions are: each input occurrence appears in exactly one
cell — a finite counting check; each cell's mode is one of the declared modes —
a finite membership check; each cell's targets exist in the output state — a
finite lookup; and each cell's evidence is present in the declared form — a
finite structural check. All are total on finite inputs. `square`

**Exact outstanding meaning, or an explicit legacy disposition.** {#AM-J3}
**Status: PROVED (single derivation).** Under an accountable certificate,
outstanding content either arrives exactly on the common carrier or receives a
declared legacy disposition; it is never silently substituted.

**Proof.** Each input occurrence has exactly one cell. Modes carried, refined
and identified name targets in the output state, and the compiler's agreement
condition requires the target's credal content to agree with the input's on the
common carrier — the distinctions both states express — so the content arrives
exactly there. Modes suspended and terminally disposed name no target and record
a declared disposition instead. There is no fourth possibility, so no occurrence
leaves the certificate without either an exact arrival or a declared
disposition. `square`

**Legacy distinctions are retained or explicitly discharged.** {#AM-J4}
**Status: PROVED (single derivation).** A distinction the new state does not
express is either retained as legacy content with its own liability, or
discharged by a declared authorized act.

**Proof.** By `AM-J3` such a distinction cannot arrive exactly, since the
carrier does not express it. So its cell is suspended or terminally disposed,
and both record a declared disposition; the suspended case retains the content
with liability attached, the disposed case discharges it under the recorded
authorization. `square`

**Authorization cannot be manufactured.** {#AM-X10} **Status: REFUTED (witness
displayed).** The proposal that a migration may create authorization for content
it introduces is false.

**Witness.** A certificate whose output state contains an occurrence with no
cell naming it as a target and no administrative grant naming it. Accountability
is silent about it — accountability quantifies over *input* occurrences — yet the
occurrence is active in the output state and carries authority nothing conferred.
The repair adopted is that authority in the output state must be either
transported by a cell or conferred by a declared grant, which the composition
check of §3 enforces. `square`

## 3. Composition across migrations

**Administrative continuity.** {#CM-J0} **Status: PROVED (single derivation).**
Between two certified migrations the only permitted edit is a declared
administrative grant. Hence no re-settlement occurs between certified
migrations.

**Proof.** A history's steps are certificates; anything between them is an edit.
The permitted-edit rule admits only grants, whose content is authorization
identifiers, consuming tokens, and at most one snapshot — none of which writes
record content. Since re-settlement would write record content, it is
structurally impossible in the gap. `square`

**Composite accountability.** {#CM-J1} **Status: PROVED (single derivation).**
The composite of two accountable certificates is accountable, with each input's
composite cell determined by chasing its cell through the intermediate state.

**Proof.** Each input occurrence has exactly one first cell, whose targets are
occurrences of the intermediate state; each of those has exactly one second
cell. Composing gives exactly one composite cell per input, with targets in the
final state and evidence the pair of evidences. Modes compose by the declared
table: a carried step composes with any mode to that mode; suspended and
terminally disposed absorb. `square`

**Composition is associative on histories.** {#CM-J2} **Status: PROVED (single
derivation).** For three composable certificates, composing the first two and
then the third gives the same composite cells as composing the first with the
composition of the last two.

**Proof.** Composite cells are determined by chasing targets through
intermediates, and target-chasing is function composition on finite sets, which
is associative. The evidence in each case is the same triple in the same order.
`square`

**Endpoint recertification is assumed, not inherited.** {#CM-J5}
**Status: PROVED-CONDITIONAL (conditions listed).** The joint-theorem endpoint
conditions hold of a composite when they are assumed afresh at each version;
whether they can be inherited across the composite instead is open.

**Proof.** The composite's conclusion is the conjunction of per-version
conclusions, each of which is available by the joint theorem under its own
endpoint hypotheses. Nothing in composition supplies those hypotheses at the
later versions, so they are assumed. The open direction is carried in
`OPEN_PROBLEMS.md`. `square`

## 4. Transport of standing and burden

**Transport soundness.** {#ST-J1} **Status: PROVED (single derivation).** A
transport plan is accepted only if: no standing is created without a sponsor; no
authority is duplicated or transferred except by a declared grant; no unresolved
burden disappears; and no suspension is laundered into a clean state.

**Proof.** Each condition is a finite check over the plan and the two states.
Created standing is standing in the output with no input source and no grant;
duplication is one input authority appearing at two outputs; a disappeared
burden is an unresolved input burden with no output carrier and no declared
discharge; laundering is a suspended input whose output is active with no
declared reinstatement basis. Each is decidable, and the plan is accepted
exactly when none fires. `square`

**Semantic support is not standing.** {#ST-N1} **Status: NECESSITY WITNESS.**
Mixed semantic and deontic support does not substitute for standing or
authority.

**Witness.** A cell whose input occurrence is semantically supported in the
output state — its content is expressible and endorsed — while no plan edge
carries its standing. The support is real and the standing is absent, so a
predicate reading support as standing would accept a plan that creates an
unanswered obligation. The accepted predicate therefore reads support and
standing separately, and the displayed cell is rejected. `square`

**Terminal disposition does not manufacture unrelated standing.** {#ST-N2}
**Status: NECESSITY WITNESS.** The terminal-disposition exception is per cell: a
response to one input is not a warrant for another.

**Witness.** A plan discharging one input by terminal disposition and citing
that disposition as the sponsor for a second, unrelated input's output standing.
The second input has no sponsor of its own, so the plan creates standing without
one; the per-cell reading rejects it, and a global reading would not. `square`

## 5. Local to global

**Local acceptance composes to global transport.** {#ST-J2} **Status: PROVED
(single derivation).** If every step of a history is accepted, the composed
transport is accepted, and each resource's global route is the composite of its
local routes.

**Proof.** Acceptance is the conjunction of the four conditions of `ST-J1`, each
of which is preserved under composition: created standing at the composite would
be created at some step; duplicated authority at the composite would be
duplicated at some step, since composition of injective assignments is
injective; a burden disappearing across the composite disappears at some step;
and a laundered suspension across the composite is laundered at some step. So
the composite fires no condition. Routes compose by target-chasing. `square`

**Global acceptance does not localize.** {#ST-N3} **Status: NECESSITY
WITNESS.** The converse fails: a composite may be acceptable while an
intermediate step is not.

**Witness.** A two-step history in which the first step duplicates an authority
and the second discards one of the copies. The composite assignment is
injective, so the composite is accepted; the first step is not. Hence step-wise
acceptance is a strictly stronger requirement, and the theory demands it.
`square`

**Accumulated authority.** {#ST-J3} **Status: PROVED (single derivation).** Over
a history, authority at the endpoint is limited by initial authority plus the
authority conferred by declared grants.

**Proof.** By `ST-J1` no step creates or duplicates authority except by grant,
so the count of distinct authorities is non-increasing along a step apart from
grants, which increase it by their declared content. Summing over steps gives
the bound. `square`

## 6. The answerability ledger

The ledger records **obligations** — identified, carried, refined, suspended,
covered, discharged, disposed, closed, or reopened — as an append-only log of
typed events. **Coverage** relates a response to an obligation, with a
**structural adequacy** condition on the pair.

**Conservation.** {#AL-J1} **Status: PROVED (single derivation).** Every
obligation in an accepted log is in exactly one state at every date, and its
state changes only by a recorded event.

**Proof.** The log is append-only and each event names the obligation it acts
on. The state function folds the log in order; each constructor maps a state to
exactly one successor state, and no constructor acts on an obligation it does
not name. So the state is total, single-valued, and changes only at named
events. `square`

**Coverage is checked, not asserted.** {#AL-J2} **Status: PROVED (single
derivation).** A coverage edge is accepted only when the response's structural
adequacy condition holds against the obligation it claims to cover.

**Proof.** The condition is a finite structural comparison of the response
against the obligation's kind and target. The verifier evaluates it; an edge
failing it is recorded as an obstruction rather than as coverage. `square`

**Ledger composition.** {#AL-J3} **Status: PROVED (single derivation).** The
composition of two accepted logs over disjoint obligation identifiers is
accepted, and the fold of the composite is the union of the folds.

**Proof.** With disjoint identifiers no event of one log names an obligation of
the other, so the fold of the concatenation acts independently on each family
and each obligation's state is exactly its state in its own log. Acceptance is
per obligation, so it is preserved. `square`

**Reopening is bounded and recorded.** {#AL-J4} **Status: PROVED (single
derivation).** A closed obligation reopens only on a recorded basis, and the
reopening is itself an event that later folds may inspect.

**Proof.** The reopen constructor requires a basis field, and the fold rejects a
reopen without one. Since the log is append-only, the reopening event persists
and is visible to every later fold. `square`


## Transcribed rows: the source ledger's remaining claims

The rows below complete the consolidation's discard test for this layer. They
are **transcriptions**, carried folder-locally from the source tree's own claim
ledger during the completing pass: no new mathematics, no reinterpretation, and
no status change to any claim already stated above. Each carries its hypotheses,
its conclusion, and — for a drop-contract or necessity row — the witness the
source displayed, so the instance is readable here rather than only named.

Two conventions apply throughout this section. Where the source recorded a
status of a compound form, the status here is the plain mandated one and the
qualifier is carried in the ledger's verification column as provenance: the
mandated vocabulary of this package has no compound forms, and the qualifier
describes how the source established the claim rather than what its status is.
And where the source's verification pointer names a file of the source tree,
that pointer is recorded as historical provenance only — it is **not** evidence
a reader of this package can follow, and the folder-local evidence for a
transcribed row is the displayed witness itself.

**occurrence-cell conservation.** {#AM-J0} **Status: PROVED (single derivation).** no orphan/duplicate occurrence; split/merge lineage is the unique cell input block

*Hypotheses.* finite typed disposition cells; unique IDs; input and live/suspended-output coefficient-one partitions; legal cardinalities

*Necessity / sharpness.* authority conservation is an additional invariant, exposed by AM-X16 Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**migration reference-jump theorem.** {#AM-J2} **Status: PROVED (single derivation).** migration movement is well typed and capped by `NL-J1`, without holdings norm/reserve

*Hypotheses.* exact live payoff transport; common comparison evaluations; old/new reference lifts in `P_Gamma`; inherited payoff range

*Necessity / sharpness.* payoff discrepancy or missing lifts blocks theorem; legacy coordinate escapes

**exact harm-refinement trace.** {#AM-E1} **Status: PROVED (single derivation).** the raw certificate passes all nine checks; derived movement is `1/6`

*Hypotheses.* raw four-state arena, typed states/cells/edges/routes, payoff, references, compiler vertices, authorization, and activation identities

*Witness.* finite Python instance only; neither AM-J3 nor the transition protocol is Lean-mechanized Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**finite revision trilemma.** {#AM-N1} **Status: PROVED (single derivation).** no exact new-only factorization; preservation/collapse/no-residual cannot all hold

*Hypotheses.* two comparison states collapsed by new projection; live observable separates them

*Witness.* exact separation is minimal for this obstruction Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**preserved claim/lost ancestry.** {#AM-X1} **Status: NECESSITY WITNESS.** semantic preservation does not preserve entitlement

*Hypotheses.* equal claim table; old entitlement has evidence; new active entitlement has no graph path to an authorized root

*Witness.* relation audit or new evidence repairs

**split challenge orphan.** {#AM-X2} **Status: NECESSITY WITNESS.** omitted descendant silently escapes burden

*Hypotheses.* typed occurrence target splits in two; transported challenge targets one output

*Witness.* computed descendant-frontier equality repairs

**merged incompatibility loss.** {#AM-X3} **Status: NECESSITY WITNESS.** incompatibility silently disappears

*Hypotheses.* transported incompatibility image is absent after a merge

*Witness.* self-conflict, suspension, or loss repairs

**changed outstanding payoff.** {#AM-X4} **Status: NECESSITY WITNESS.** outstanding settlement changes

*Hypotheses.* comparison payoffs differ on one covered state; nonzero holdings; no authorized legacy treatment

*Witness.* exact map or a retained authorized carrier is required

**preactivation force.** {#AM-X5} **Status: NECESSITY WITNESS.** proposed ontology can constrain quotes during audit

*Hypotheses.* proposed compiler identity appears in the force record before CAS

*Witness.* old force identity until atomic activation

**inexpressibility-as-discharge.** {#AM-X6} **Status: NECESSITY WITNESS.** burden is orphaned, not discharged

*Hypotheses.* old live target/challenge; discharge cell has no response certificate

*Witness.* legacy target, suspension, or terminal failure required

**duplicate loss entry.** {#AM-X7} **Status: NECESSITY WITNESS.** one loss is counted twice

*Hypotheses.* same loss ID or semantic `(source,lost-content)` key entered twice

*Witness.* unique typed keys repair

**coupling-as-authorization.** {#AM-X8} **Status: NECESSITY WITNESS.** semantic correspondence cannot determine activation

*Hypotheses.* semantic span and compiler remain; certificate-bound prior authorization record is absent

*Witness.* external authorization is load-bearing

**lossless collapse.** {#AM-X9} **Status: NECESSITY WITNESS.** exact lossless new-only migration impossible

*Hypotheses.* comparison states collapse under the new projection while a live table separates them

*Witness.* retain distinction/residual or record loss

**duplicate disposition cells.** {#AM-X11} **Status: NECESSITY WITNESS.** coefficient becomes two

*Hypotheses.* two cells each consume and produce the same occurrence IDs

*Witness.* one split hypercell repairs

**partial activation.** {#AM-X12} **Status: NECESSITY WITNESS.** full occurrence coverage fails

*Hypotheses.* commitment moves; live challenge cell omitted

*Witness.* shadow transaction repairs

**late burden reassignment.** {#AM-X13} **Status: NECESSITY WITNESS.** assignment is not descendant-frontier determined

*Hypotheses.* frozen frustration-edge target replaced with physical/coercive edge

*Witness.* publish typed descendant frontier before freeze

**incomplete rollback.** {#AM-X14} **Status: NECESSITY WITNESS.** uncertified operative interval remains historical

*Hypotheses.* active pointer swaps before endpoint recheck

*Witness.* shadow state plus final identity-bound CAS repairs

**disclosure-as-loss-authorization.** {#AM-X15} **Status: NECESSITY WITNESS.** disclosed terminal semantic loss remains unauthorized

*Hypotheses.* loss entry disclosed; loss ID absent from prior authorization allow-list

*Witness.* bind exact loss ID into prior authorization

**split authority duplication.** {#AM-X16} **Status: NECESSITY WITNESS.** semantic/ancestry refinement duplicates practical authority

*Hypotheses.* one authoritative input; two authoritative split outputs; no new grants

*Witness.* authority-output conservation or cell-bound grants repairs

**asserted eventual route coverage.** {#AM-X17} **Status: NECESSITY WITNESS.** a stored coverage assertion cannot supply a terminal path

*Hypotheses.* live challenge and burden; route graph empty

*Witness.* compute coverage from authorized assigned consuming routes

**lineage normalization.** {#CM-J3} **Status: PROVED (single derivation).** normalized composite ancestry is well defined and order-independent; path count is at least ancestry count, with equality exactly when no pair has two intermediates

*Hypotheses.* AM-J0 at both steps

*Necessity / sharpness.* split-then-merge realizes strict inequality (8 paths, 7 ancestry pairs); authority and residue must be computed off ancestry, not paths Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**composite movement additivity.** {#CM-J4} **Status: PROVED (single derivation).** composite reference movement is the sum of step movements and enters NL-J2 as two jumps; no holdings norm is used

*Hypotheses.* AM-J2 at both steps; outstanding holdings transported unchanged; distinct consuming tokens

*Necessity / sharpness.* each charge is a holdings-weighted reference difference; substitution into NL-J2 uses `m_-+2+m_+` jumps Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**liveness monotonicity.** {#CM-N1} **Status: PROVED (single derivation).** output liveness and practical authority do not exceed the input's, except at a terminal disposition or a named authorization grant; this excludes CM-X1

*Hypotheses.* statuses ordered terminal < suspended < live; per cell, per input-output pair

*Witness.* sufficient to exclude the exhibited obstruction and necessary in that dropping it readmits CM-X1; not shown to be weakest

**exact two-step harm history.** {#CM-E1} **Status: PROVED (single derivation).** both components pass all nine checks, all thirteen composition checks pass, derived movements are `1/6` and `2/15` with total `3/10`

*Hypotheses.* raw `v_0`, `v_1`, `v_2` states, two certificates, one grant, four covered fiber pairs

*Witness.* finite Python instance only; CM-J5 is not mechanized for general `n` Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**component validity is not composite validity.** {#CM-X1} **Status: REFUTED (witness displayed).** both certificates pass all nine checks; the composite fails on liveness, resurrection, and unreconciled duplication

*Hypotheses.* merge cell joining a live authoritative entitlement and an inherited suspended one to a live authoritative output

*Witness.* minimal: one cell, two inputs, one output; cell counting and authority totals both hold

**naive lossless collapse.** {#CM-X2} **Status: REFUTED (witness displayed).** every start claim still reconstructs exactly, yet two intermediate distinctions are destroyed

*Hypotheses.* coercion and preference frustration merged with no residual object

*Witness.* start-claim conservativity is strictly weaker than composite conservativity

**locally adequate arena.** {#CM-X3} **Status: REFUTED (witness displayed).** the second certificate stays locally valid while the composite loses a live column

*Hypotheses.* second arena truncated to three comparison states

*Witness.* realizes the failure direction of CM-J2

**self-consistent activation records chain.** {#CM-X4} **Status: REFUTED (witness displayed).** both components remain valid; the public event chain does not link

*Hypotheses.* intermediate state identity relabelled and the second certificate updated to match

*Witness.* activation identities are per-step and cannot see their predecessor

**one token authorizes two migrations.** {#CM-X5} **Status: REFUTED (witness displayed).** each step checks only its own token; the history spends one token twice

*Hypotheses.* the same consuming migration token bound by both certificates

*Witness.* token distinctness is a history-level condition

**stored expected output launders a certificate.** {#CM-X6} **Status: REFUTED (witness displayed).** recomputation still rejects; the declared total is refuted against the derived `3/10`

*Hypotheses.* discrepancy values overwritten with zeros; composite total declared to be `1/6`

*Witness.* no report value is stored; every rational is rederived

**challenge follows one descendant.** {#CM-X7} **Status: REFUTED (witness displayed).** the omitted composite descendant escapes the burden

*Hypotheses.* frozen ancestry target split into two composite images; successor covers one

*Witness.* end-to-end frontier equality is required, not per-step equality alone

**states may be edited between migrations.** {#CM-X8} **Status: REFUTED (witness displayed).** an uncertified state change hides between two certified ones

*Hypotheses.* force holdings changed on the departure state outside the grant

*Witness.* grant confinement is load-bearing independently of whether the next certificate notices

**component composite migration.** {#CM-J6} **Status: PROVED (single derivation).** the component composite is a well-formed certificate accepted by `verify_migration`, consuming each live start occurrence once, with the composite reference charge of CM-J4

*Hypotheses.* (L) and (S); no component with several starts and several ends; no component with a terminal disposition on one branch and a surviving other branch

*Necessity / sharpness.* canonical up to fiber representative, legacy retention, and re-sourcing choice; not unique Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**composite certification is incomparable with composability.** {#CM-J7} **Status: PROVED (single derivation).** a certified composite exists for an inadmissible history, and an admissible history has no certified composite

*Hypotheses.* the displayed five-history family

*Necessity / sharpness.* both directions witnessed: `merged-live` and `naive` give the first, `authorized-loss` the second; forces (S) as separate data Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**no double authority.** {#CM-J8} **Status: PROVED (single derivation).** authority-bearing occurrences at the end version are at most those at the start plus scoped grants, per component

*Hypotheses.* lineage components; AM-J0 partitions; AM-X16 per-cell authority bound

*Necessity / sharpness.* descendants may be genuinely distinct with common provenance; the bound is on authority-bearing descendants only

**legacy discharge.** {#CM-J9} **Status: PROVED (single derivation).** the group may be collapsed with frontiers, roots, payoff meaning, and movement unchanged

*Hypotheses.* a retained arena group; no live challenge or burden; payoff and discrepancy constant on the group

*Necessity / sharpness.* the payoff clause is automatic for distinctions introduced after the start version, so only live dependents and recorded discrepancies block collection Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**composite movement subadditivity.** {#CM-J10} **Status: PROVED (single derivation).** composite movement is at most the sum of step movements, with equality iff the step charges are not oppositely signed

*Hypotheses.* one payoff coordinate transported across both steps with unchanged holdings

*Necessity / sharpness.* equality holds in the displayed trace (`1/6 + 2/15 = 3/10`); CM-X10 exhibits strict inequality

**blind composition preserves ancestry.** {#CM-X9} **Status: REFUTED (witness displayed).** a split whose branches later merge consumes its common ancestor once per branch

*Hypotheses.* one composite cell per pair of step cells

*Witness.* the obstruction certificate names occurrence, paths, descendant, and the consuming disposition at risk

**a composite accounts for its history.** {#CM-X10} **Status: REFUTED (witness displayed).** steps charge `0` and `3/10`; the composite charges `0` and consumes one token instead of two

*Hypotheses.* reference path `3/5, 3/4, 3/5` with holdings `-2`

*Witness.* a composite may summarize a history but never account for it in NL-J2

**burden conservation.** {#ST-J4} **Status: PROVED (single derivation).** every unresolved burden reaches a carrier that still carries it and is no stronger, or a witnessed authorized termination scoped to that input

*Hypotheses.* plan condition 5

*Necessity / sharpness.* the carrier monotonicity clause is `CM-N1` restricted to burden-carrying pairs; dropping it readmits case A with a live carrier

**comparison with CM-N1.** {#ST-J5} **Status: PROVED (single derivation).** `CM-N1` with burden conservation and authority allocation implies transport acceptance, with 0 counterexamples; the converse fails on 902 cells

*Hypotheses.* realizable sub-scope; canonical plan

*Necessity / sharpness.* `CM-N1` alone is insufficient: it accepts 291 cells, 330 burden-vanished and 40 authority-duplicated counterwitnesses; the two conditions are incomparable Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**two-step compositionality.** {#ST-J6} **Status: PROVED (single derivation).** the three composing repairs are accepted at every cell and the laundering repair is rejected at exactly one

*Hypotheses.* the two-step history of CM-E1; unresolved-burden bits read from the previous certificate's suspension entries

*Necessity / sharpness.* one finite history only; per-cell acceptance is not shown to imply composite acceptance in general Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**canonical maximality.** {#ST-J7} **Status: PROVED (single derivation).** if any plan is accepted then the canonical plan is accepted, so satisfiability is decided by one plan

*Hypotheses.* enumeration scope §7.2; the declared plan family; a fixed record setting

*Necessity / sharpness.* non-trivial at the bare setting, where only 218 of 576 cells are satisfiable; 15,228 plans examined, 0 failures Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**exhaustive finite classification.** {#ST-E1} **Status: PROVED (single derivation).** 24,336 cells and 97,344 deterministic plan checks with the displayed acceptance counts

*Hypotheses.* shapes (1,1),(1,2),(2,1),(2,2); status x authority x burden per occurrence; four record settings

*Witness.* facts about the stated finite space only; no adequacy claim of any kind Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**CM-N1 conserves burdens.** {#ST-X1} **Status: REFUTED (witness displayed).** status does not rise and no authority appears, yet the burden is gone

*Hypotheses.* one suspended burdened input; one suspended output without the burden

*Witness.* minimal: one input, one output

**CM-N1 blocks authority duplication.** {#ST-X2} **Status: REFUTED (witness displayed).** one source licenses two branches and `CM-N1` accepts

*Hypotheses.* one authoritative input; two authoritative outputs; no grant

*Witness.* AM-X16 counting catches this instance but misses the declared duplication of ST-J3

**a terminal disposition is a grant.** {#ST-X3} **Status: REFUTED (witness displayed).** `CM-N1`'s cell-level exception accepts the unrelated live authoritative output

*Hypotheses.* two suspended inputs, one burdened; outputs a burdened residual and a live authoritative occurrence; a terminal disposition at the cell

*Witness.* only a scoped reinstatement with a named basis lifts liveness

**semantic support sponsors liveness.** {#ST-X4} **Status: REFUTED (witness displayed).** content contribution supplies neither liveness nor authority

*Hypotheses.* one suspended input; one live authoritative output; total semantic support and nothing else

*Witness.* re-declaring the same edge as liveness support fails too: the input is too weak

**a cell-scoped termination discharges every input.** {#ST-X5} **Status: REFUTED (witness displayed).** the frozen `cell.unbacked_retraction` check is satisfied while one burden goes unanswered

*Hypotheses.* terminal cell with two burdened inputs and one witness

*Witness.* input scoping repairs it; this is item 2 of ST-C1

**case B is expressible as one frozen cell.** {#ST-X6} **Status: REFUTED (witness displayed).** all eight disposition modes are rejected on shape

*Hypotheses.* a (2,2) entitlement cell with one live and one suspended output

*Witness.* the separated two-cell form of the same migration does verify; this is the missing expressive resource

**accumulated authority bound.** {#LG-J0} **Status: PROVED (single derivation).** `A_j(K) <= A_i(K) + sum of g_{t,t+1}(K)` for every `i <= j`

*Hypotheses.* lineage component of a finite linear history; AM-J0 partitions; AM-X16 per-cell bound; step-indexed grants

*Necessity / sharpness.* corrects the pooled-grant display of CM-J8, whose second inequality fails whenever a grant is issued at the first step; grant-free corollary `A_j <= A_i` survives

**authority injections compose.** {#LG-J2} **Status: PROVED (single derivation).** for every `i <= j` there is an injection from authoritative occurrences at `V_j` into licences alive at `V_i` together with grants issued in `[i,j)`

*Hypotheses.* every cell allocates authoritative outputs injectively into eligible sponsors and scoped grants

*Necessity / sharpness.* composition of injections; injectivity at every step is what forbids two endpoints resolving to one licence

**ledger-relative burden condition.** {#LG-J5} **Status: PROVED-CONDITIONAL (conditions listed).** every history whose cells are accepted composes without obstruction

*Hypotheses.* a termination scoped to an input closes exactly one owed answer borne by it; the inherited burden ledger is available

*Necessity / sharpness.* verified only over the burden scope; the repair rejects exactly the 783 counterexamples and nothing else

**associativity up to outcome equality.** {#LG-J6} **Status: MACHINE-CHECKED (stated finite scope).** both bracketings agree with each other and with the direct fold on the outcome map

*Hypotheses.* the three-step split-merge-split history

*Necessity / sharpness.* literal equality is the wrong notion: resource identifiers encode the bracketing

**bounded local-to-global search.** {#LG-E1} **Status: MACHINE-CHECKED (stated finite scope).** burden scope: 222,376 histories, 783 local-pass/global-fail, all `global.termination_over_scope`; authority scope: 8,400 histories, 0

*Hypotheses.* two-step histories of one cell per step; shapes `(m,k,n)` with `m,k` in `{1,2}` and `n` in `{0,1,2}`

*Witness.* the scope is the claim; deeper histories, larger cells, and multi-cell steps are outside it

**authority composes in scope.** {#LG-E2} **Status: MACHINE-CHECKED (stated finite scope).** 0 histories in which every local plan is accepted and the composition reports an obstruction

*Hypotheses.* authority scope

*Witness.* 14 apparent witnesses were composer bugs from greedy licence allocation, not obstructions; the composer must use the same matching as the local predicate

**local burden acceptance composes.** {#LG-X1} **Status: REFUTED (witness displayed).** both cells are locally accepted and two owed answers are closed by one witness

*Hypotheses.* two suspended burdened inputs merged onto one burdened carrier, then terminated by one scoped witness

*Witness.* minimal: two cells, three occurrences, no authority, no grant; the missing datum is a multiset, not a bit

**revised burden interface.** {#LG-C1} **Status: PROPOSED (interface revision).** the set is the smallest datum supporting both obstruction detection and the outcome map

*Hypotheses.* replace the per-occurrence burden bit by a set of borne burden lineages; retain input-scoped terminal dispositions

*Necessity / sharpness.* the datum is historical, not intrinsic to one migration, which is why it is not adopted into the one-step interface

**identification need not merge obligations.** {#AD-J5} **Status: PROVED (single derivation).** one adequacy argument grounds one coverage edge per identified obligation; every filing keeps its identity, edge, and disposition

*Hypotheses.* an equivalence certificate with grounds other than carrier merger

*Necessity / sharpness.* strictly dominates merger on auditability; removes any operation that could destroy an objector's filing

**benchmark examples.** {#AD-E1} **Status: MACHINE-CHECKED (stated finite scope).** the displayed verdicts, computed from raw records

*Hypotheses.* the seven finite ledger histories of §5

*Witness.* finite instances only; no general claim

**three-system comparison.** {#AD-E2} **Status: MACHINE-CHECKED (stated finite scope).** certified coverage accepts 68 against the rivalrous system's 36, accepts all 8 legitimate shared responses the rivalrous system rejects, and accepts 0 unsafe closures against the bit system's 24

*Hypotheses.* 92 scenarios over at most two obligations and two responses, all coverage and discharge subsets

*Witness.* the scope is the claim; the bit system is modelled by the absence of the check

**one witness answers one obligation.** {#AD-X2} **Status: REFUTED (witness displayed).** it rejects all 8 scenarios in which one response carries two independently certified coverage edges

*Hypotheses.* the rivalrous restriction

*Witness.* safety bought by being unable to record a true fact

**ledger conservation implies frontier coverage.** {#AD-X3} **Status: REFUTED (witness displayed).** conservation holds while prefix challenge-frontier coverage fails

*Hypotheses.* a carry event retargets an obligation onto an unrelated carrier

*Witness.* the two conditions remain independently necessary

**ledger bridge to the migration certificate.** {#AD-C1} **Status: PROPOSED (interface revision).** would replace ST-C1 item 1 entirely

*Hypotheses.* a migration certificate emitting one ledger event per open obligation

*Necessity / sharpness.* not adopted; compatibility with every AM-, CM-, ST-, and LG- claim unchecked

## 7. What this part does not establish

Composition here is of certificates and plans, not of behaviour. Nothing
predicts what a migration will do; the results say what the record must show for
one to be accountable. Endpoint recertification across composites is open
(`CM-J5`). Branching histories and several simultaneous actors are not treated:
the results are stated for a linear history with one migrating actor, and the
generalization is carried in `OPEN_PROBLEMS.md`. Comparison objects weaker than
the strict fiber product are likewise open.
