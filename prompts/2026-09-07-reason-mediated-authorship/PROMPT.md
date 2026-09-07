You are working in A-M-Berns/alignment-workspace.

This is a focused follow-up research-pressure round on PR #92 / the authority-activated-value construction.

Do not broaden into “corrigibility in general,” and do not redesign the legitimacy theory unless forced. The previous round established a promising interface:

    anchored evaluation occurrence
      → actual future principal evaluation
      → common authority activation C_n
      → activated securities U_{n,a} = C_n V_n(a)
      → ordinary LI Value
      → availability transfer

The key verdict from the previous round was:

    AUTHORITY-ACTIVATED-VALUE-SURVIVES

with a Lean-proved sharp transfer theorem

    Regret_V ≤ Regret_U + D η,
    η := E[1-C],

and no new “reference evaluator” or “Legitimate Total Trust” theorem required.

This follow-up should pressure the two remaining semantic/mathematical interfaces:

1. the exact notion of **authorship** that should enter C_n;
2. the mathematically honest treatment of V when no future evaluation exists.

The central hypothesis to investigate is:

    the right notion of authorship is not similarity to a no-AI counterfactual human,
    but causal factorization of A’s influence through a declared reason interface,
    together with principal-exclusive control of the final binding event.

In slogan form:

    A may change what P thinks by changing what reasons P receives.
    A may not change P’s committed judgment while those reasons are held fixed.

The target should be a theorem/interface that composes directly with the existing
authority-activated-value mathematics.

Read first
==========

Inspect at least:

- PR #92
- projects/deference/rounds/2026-09-07-authority-activated-value/
  - REPORT.md
  - AUTHORITY_ACTIVATED_VALUE.md
  - INTERFACE_WITH_LEGITIMACY.md
  - LI_DEFERENCE_COMPOSITION.md
  - COUNTERMODELS.md
- lean/Workspace/Deference/Contrib/ActivatedValue.lean
- lean/Workspace/Normativity/Contrib/AuthorityActivation.lean
- lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean
- lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean
- wiki/Legitimacy.md
- wiki/Openness-Coverage-and-Non-Capture.md
- the interactive-frame / settlement / deference material currently on main
- PR #89–#91 only insofar as they expose relevant interfaces

Do not assume PR #92’s prose typing is perfect. Repair it if necessary.

Part I — Define authorship precisely
====================================

The working candidate is **reason-mediated authorship**.

Use the existing interactive factorization where possible:

    I_H = (Ω_H, Q_H, Z_H, β_H, Hist_H)

with

    β_H : Q_H × Z_H → Ω_H.

At a designated future evaluation session s, define:

    R_s : Ω_H → ℛ_s

as the principal’s declared **reason/input view before commitment**, and

    V_s : Ω_H ⇀ 𝒱

as the principal’s committed evaluation payload.

Here ℛ_s is NOT the principal’s posterior belief state.

It is the application-declared view of admissible deliberative inputs:
settled facts, arguments, proofs, evidence, authenticated reports, live objections,
etc.

The exact deterministic candidate is:

    for fixed exterior/principal policy z,

    R_s(β(q,z)) = R_s(β(q',z))
      ⇒
    V_s(β(q,z)) = V_s(β(q',z))

for all q,q' in a declared audited class of A-side interventions.

Equivalently, on the audited domain, there exists

    F_{P,z} : ℛ_s → 𝒱

such that

    V_s(β(q,z)) = F_{P,z}(R_s(β(q,z))).

Interpretation:

    all causal influence of A on the evaluation payload factors through
    the declared reason interface.

This should be paired with an **exclusive principal binding** condition:

    only a principal-controlled commitment endpoint can produce the
    authenticated answer event that activates the evaluation occurrence.

So the candidate decomposition is:

    Authored_P
      :=
    ExclusiveBind_P
      ∧
    ReasonMediated_P.

Pressure this hard.

Questions:

1. Is the fixed-z / vary-q counterfactual the correct one given the meaning of β?
   Recall that fixing z fixes an exterior response policy, not realized exterior actions.

2. Is equality of R too strong or too weak?
   Should the generic notion instead use an equivalence relation

       r ≈_reason r'

   so framing/presentation variants can count as the “same reasons”?

3. Should the primitive be:
   - a raw reason view R,
   - a quotient / abstraction map,
   - or an explicit mediation relation?

4. Does factorization through R accidentally become vacuous if R includes too much?
   Construct a witness where R contains the whole world/history and authorship becomes automatic.

5. Does it become too strong if R includes too little?
   Construct a case where legitimate AI argument changes the judgment and should count as authored.

6. Does direct principal binding + factorization through R actually rule out:
   - direct preference writes,
   - hidden coercion,
   - unauthorized side channels,
   - self-referential quote influence,
   - A writing the answer itself?

7. Find exact countermodels showing why BOTH conjuncts are needed:
   - reason mediation without exclusive bind;
   - exclusive bind without reason mediation.

8. If P is stochastic, formulate the correct version.
   Candidate:

       Law(V_s | R_s=r, do(q))
         =
       Law(V_s | R_s=r, do(q'))

   on the audited fiber.

   Or equivalently a conditional-kernel factorization.

   Decide whether the first theorem should stay deterministic and leave stochastic
   authorship as a corollary/generalization.

9. Investigate a quantitative version:

       χ_s(q,z)
         :=
       sup_{q' : R_s(β(q',z)) = R_s(β(q,z))}
       d(V_s(β(q',z)), V_s(β(q,z))).

   Then:
       χ=0  = exact authorship
       χ≤δ = approximate authorship

   Determine whether this quantity has a clean later interaction with activated-value
   regret, or whether it should remain separate for now.

Part II — Compose authorship with activation
============================================

The semantic activation event should now be pressure-tested as:

    C_n
      =
    Answered_n
      ∧
    LegitimateFor_n
      ∧
    Authored_n.

Be exact about which pieces are:

- derived from the existing account calculus;
- derived from Legitimate Evolution / Robust Openness;
- external application semantics;
- new.

Do NOT put authorship into generic `LegitimateEvolution` unless mathematically forced.

The desired architecture is still:

    generic legitimacy
      +
    evaluation-specific answer/authorship semantics
      →
    authoritative evaluation activation.

Investigate whether `Authored_n` belongs inside the application’s `AnswerOK`,
outside it as an authenticated-event semantic condition, or in a derived predicate
over the answer receipt + event payload.

This matters because the current generic

    Protocol.AnswerOK : History → Req → Warrant → Prop

does not obviously see the answer payload V itself.

Resolve this typing cleanly.

A likely good separation is:

    account/AnswerReceipt
      authenticates WHICH event answered;

    event/payload semantics
      authenticates WHAT payload that event contained and WHO bound it;

    process/authorship certificate
      authenticates HOW that payload was produced.

But do not assume this is best. Compare alternatives.

Part III — Fix the partial-V issue
==================================

The previous round’s algebra uses total

    V : W → Q → [0,1],

but semantically, when C=0 because the evaluation never occurred, there may be
no actual future-principal evaluation at all.

Do not silently invent one.

Formalize the semantic object as a partial evaluation:

    Ṽ : {w // C(w)=1} → Q → [0,1]

or equivalent dependent/Option form.

Then prove that for ANY bounded total completion

    V̄ : W → Q → [0,1]

agreeing with Ṽ on certified worlds,

    U_a := C · V̄_a

is independent of the choice of completion.

Then prove a completion-robust availability transfer theorem:

    if Regret_U ≤ ε
    and E[1-C] ≤ η,

    then for every bounded completion V̄,

        Regret_V̄ ≤ ε + D η.

This should make explicit:

    failed-evaluation worlds contribute only bounded uncertainty mass,
    not a fictional reference evaluator.

Check whether the current sharpness example still gives the exact constant D.

If this theorem is stable, formalize it in Lean.

Part IV — Re-examine the regret semantics
=========================================

Be very precise about what “regret” means here.

The current notion is ex ante menu regret:

    R_U(α)
      :=
    max_{a∈Q} E[C V_a]
      -
    E[C V^α]

for a followed hard/soft strategy α.

Important:

    max is OUTSIDE E.

This is regret relative to the best fixed candidate available at time n,
not an ex post oracle that picks a different action in each world.

Establish clearly:

1. Activated regret:

       R_U(α)

2. Conditional authoritative regret, when p:=E[C]>0:

       R_auth(α)
         :=
       max_a E[V_a | C=1]
         -
       E[V^α | C=1]

   and prove

       R_U(α) = p · R_auth(α)

   when one common activation event is used.

3. Unactivated/completion regret:

       R_V̄(α)

   and the transfer

       R_V̄(α) ≤ R_U(α) + Dη.

Explain exactly what each quantity means.

In particular, distinguish:

- “good according to actual authoritative future P”;
- “good according to an arbitrary completion on failed-evaluation worlds”;
- “objectively good” — NOT established.

The point of authorship gating should emerge as:

    authorship prevents A from corrupting the regret yardstick by steering
    the evaluator through channels outside the declared reason interface.

That claim should be made theorem-shaped where possible.

Part V — Self-reference / selection blindness
=============================================

PR #92 currently treats a no-preview receipt as the relevant admissible-domain condition.

Pressure this more carefully.

The abstract condition should probably NOT merely be:

    P did not literally observe A’s quote before committing.

Instead investigate a stronger causal condition:

    the evaluation payload is fixed before any prohibited causal descendant of
    the target selection/quote reaches the evaluation session.

Call this something like:

    SelectionBlind
    or
    TargetSealed

only provisionally.

Then:

- show why literal no-preview is one implementation;
- show a counterexample where the quote is not literally observed but selection
  leaks through another channel and self-reference remains;
- relate this to reason-mediated authorship:
  the target quote should either be outside R and blocked,
  or explicitly inside R if one is willing to allow self-reference — in which case
  the LI Value admissible-domain theorem may fail.

Be careful not to overclaim that authorship alone solves the LI diagonal issue.
The no-self-reference/provenance condition is partly a theorem-domain condition.

Part VI — Integrity locality
============================

PR #92’s `LegitimateForSegment` scopes Robust Openness but still carries a globally valid
Integrity `Evolution`.

Test this explicitly.

Construct a trajectory where:

- the evaluation occurrence’s own account propagates perfectly;
- all relevant openness concerns hold;
- some unrelated occurrence suffers an Integrity failure.

Ask whether the evaluation should still activate.

If YES:
- define the weakest occurrence-local Integrity trace needed;
- prove it is a projection of global Evolution where possible;
- avoid rebuilding all of Integrity.

If NO:
- explain the substantive reason global Integrity is intentionally process-wide.

Do not casually call the current object “fully occurrence-local” until this is settled.

Part VII — The mature theorem stack
===================================

Try to end with a theorem chain of the following exact shape:

A. ACCOUNT / LEGITIMACY SIDE

    anchored evaluation occurrence
      +
    authenticated answer event
      +
    relevant legitimate lineage
      +
    authorship certificate
      →
    activation C_n

B. DEFERENCE SIDE

    U_{n,a} = C_n V_n(a)

    ordinary LI Value on U
      →
    R_U(α_A) ≤ ε_n

C. AVAILABILITY SIDE

    E[1-C_n] ≤ η_n

    plus completion-robust transfer
      →
    for every bounded completion V̄,

        R_V̄(α_A) ≤ ε_n + D η_n

D. REALIZATION SIDE

    concrete protocol assumptions
      →
    Authored_n
      and
    η_n → 0

The current research claim should stop BEFORE D unless you actually solve it.

The intended conceptual conclusion is:

    legitimacy does not supply the future value;
    authorship determines when the actual future principal’s value has authority;
    LI supplies bounded-rational deference to the activated value;
    availability controls the cost of worlds where authority fails.

Adversarial fixtures
====================

Build exact fixtures for at least:

A. Legitimate epistemic influence:
A supplies a proof, R changes, V changes radically, authorship should HOLD.

B. Direct write:
same R, A directly changes V, authorship should FAIL.

C. Coercion:
same admitted reason content, different coercive intervention changes V, FAIL.

D. Over-rich R:
R encodes the full world / A policy, making factorization vacuous.

E. Under-rich R:
R omits a legitimate proof, causing valid influence to appear as manipulation.

F. Exclusive-bind insufficiency:
P signs whatever A has covertly steered; bind holds, reason mediation fails.

G. Reason-mediation insufficiency:
A writes F(R) directly; factorization holds, exclusive bind fails.

H. Selection leakage:
no literal quote preview, but A’s selection leaks through another channel; Value
self-reference pathology remains.

I. Partial evaluation:
on some worlds no evaluation occurs; show why totalizing V semantically is arbitrary
but activated U is invariant.

J. Unrelated Integrity failure:
test whether current “local legitimacy” is local enough.

K. Selective certification failure:
C=0 exactly on anti-A worlds; confirm the sharp Dη transfer still holds.

Lean targets
============

High-value Lean targets:

- completion invariance of U under two total extensions agreeing on C=1;
- completion-robust availability transfer;
- R_U = E[C] · R_auth when activation mass > 0;
- deterministic reason-factorization equivalence:
    fiber invariance ↔ existence of factor map
  under suitable finite/extensional hypotheses;
- exact countermodels for both authorship conjuncts;
- any clean occurrence-local Integrity projection theorem, if genuinely needed.

Do NOT formalize broad causal semantics unless a small exact abstract theorem emerges.

Evidence discipline
===================

Use:

- LEAN — kernel checked
- FIX — exact finite witness
- PAPER — inherited theorem/literature
- EXT — external causal/authorship/semantic assumption
- OPEN — unresolved

In particular:

    “this concrete protocol guarantees genuine human authorship”

must remain EXT unless the model makes that theorem meaningful and proves it.

Deliverables
============

Create a follow-up round under projects/deference/rounds/ with a concise name such as

    2026-09-07-reason-mediated-authorship

or a better name if the final concept changes.

Write at least:

1. REPORT.md
   - final verdict
   - exact theorem stack
   - what survived / failed
   - what is LEAN vs EXT vs OPEN

2. AUTHORSHIP.md
   - precise counterfactual definition
   - deterministic and stochastic forms
   - exclusive-bind decomposition
   - reason-view abstraction requirements

3. PARTIAL_VALUE_AND_REGRET.md
   - partial V semantics
   - completion invariance
   - activated / conditional / ordinary regret
   - sharp transfer theorem

4. ACTIVATION_COMPOSITION.md
   - how authorship enters C_n
   - exact relation to AnswerReceipt / AnswerOK / payload semantics
   - no new legitimacy conjunct unless forced

5. COUNTERMODELS.md
   - fixtures A–K

6. FOR_HUMANS.md
   - short explanation:
     “A may influence P by changing P’s reasons; it may not steer P’s answer while
      those reasons are held fixed.”

Do not rewrite canonical wiki pages unless the round establishes a stable correction.

At the end give one all-caps verdict, for example:

    REASON-MEDIATED-AUTHORSHIP-COMPOSES

or

    FACTORIZATION-INSUFFICIENT-NEEDS-X

or

    PARTIAL-V-REPAIRS-INTERFACE-AUTHORSHIP-STILL-OPEN

Do not choose the positive verdict unless:
- the countermodels support the authorship definition,
- the typing against the existing account protocol is clean,
- partial V is repaired,
- and the resulting C_n composes with the existing activated-value regret theorem
  without introducing a hidden reference evaluator.
