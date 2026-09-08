You are working in A-M-Berns/alignment-workspace.

This is the FINAL PRESSURE + CONSOLIDATION pass for the current legitimate-deference stack.

The goal is not to open another broad research direction. The goal is to:

1. repair every known mathematical or typing defect in PRs #92–#93;
2. press the remaining conceptual interface exactly far enough that the abstract theorem stack is mature;
3. integrate the result coherently with the canonical legitimacy / Robust Openness theory;
4. leave the genuinely unrealized protocol/ecosystem problem explicitly open;
5. produce ONE coherent merge-ready landing state for `main`.

The current stack is:

    #92  authority-activated value
      ↓
    #93  reason-mediated authorship / partial evaluation / LocalLegit

Both are currently open; #93 is stacked on #92.

Use the current heads, not only the PR descriptions. Read the actual Lean and round documents.

Strong recommendation for landing strategy:
follow the precedent of the legitimacy landing PR (#88) if useful. Work from the top of the stack, make the necessary repair/consolidation commit(s), bring in current `main`, and prepare a single landing PR to `main` carrying the whole stack so `main` never temporarily contains claims already known to be false or mistyped.

DO NOT MERGE. The maintainer decides the merge.

Do not preserve false prose merely because it occurred in an earlier open round. These rounds have not reached `main`; known defects should be repaired before landing, with the repair recorded in provenance.

============================================================
0. READ FIRST
============================================================

Inspect at least:

PR #92
- projects/deference/rounds/2026-09-07-authority-activated-value/
  - REPORT.md
  - AUTHORITY_ACTIVATED_VALUE.md
  - INTERFACE_WITH_LEGITIMACY.md
  - LI_DEFERENCE_COMPOSITION.md
  - COUNTERMODELS.md
- lean/Workspace/Deference/Contrib/ActivatedValue.lean
- lean/Workspace/Normativity/Contrib/AuthorityActivation.lean

PR #93
- projects/deference/rounds/2026-09-07-reason-mediated-authorship/
  - REPORT.md
  - AUTHORSHIP.md
  - PARTIAL_VALUE_AND_REGRET.md
  - ACTIVATION_COMPOSITION.md
  - COUNTERMODELS.md
- lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean
- lean/Workspace/Deference/Contrib/PartialActivatedValue.lean
- lean/Workspace/Normativity/Contrib/OccurrenceLocalIntegrity.lean

Canonical theory on main
- wiki/Legitimacy.md
- wiki/Integrity.md
- wiki/Diachronic-Answerability.md
- wiki/Openness-Coverage-and-Non-Capture.md
- wiki/Deference.md
- wiki/Logical-Induction-and-Deference.md
- wiki/What-Deference-Requires.md
- wiki/Roadmap.md
- lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean
- lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean
- lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean
- lean/Workspace/Deference/Contrib/InheritedAlgebra.lean
- PRIORITIES.md item 87
- relevant current DECISIONS.md entries

Also inspect PRs #89–#91 only where they constrain terminology or downstream composition.

============================================================
1. STARTING POINT: WHAT SHOULD SURVIVE UNLESS REFUTED
============================================================

The current intended conceptual spine is:

At time n, the present principal opens an anchored evaluation occurrence for a fixed menu Q_n.

The actual future, AI-informed principal may later produce an evaluation.

There is NO counterfactual no-AI reference evaluator and NO ideal-value oracle.

The future evaluation is partial:

    Ṽ_n : (w : W) → C_n(w)=true → Q_n → [0,1].

The common activation event means roughly:

    C_n = 1

iff the designated evaluation is a valid authoritative continuation of the present evaluation mandate.

Activated value securities are

    U_{n,a} = C_n · Ṽ_n(a)

under any bounded completion; the security is completion-independent.

Ordinary LI Value is intended to run on the activated securities without a special
“Legitimate Total Trust” theorem.

The semantic target is CONDITIONAL AUTHORITATIVE REGRET, not a fictional value on void worlds:

    R_auth(α)
      =
    max_a E[Ṽ_a | C=1]
      -
    E[Ṽ^α | C=1].

The already Lean-proved identity is:

    R_U(α) = p · R_auth(α),
    p := E[C] > 0.

The current authorship proposal is:

    Authored
      =
    ExclusiveBind
      ∧
    ReasonMediated,

where, on a suitable causal frame rooted before the evaluation,

    same declared reasons
      ⇒
    same committed payload.

Its content comes from a separate declaration that the reason view is blind to
specified prohibited channels.

The remaining realization problem — concrete protocol receipts + availability
η_n → 0 — stays open unless this pass actually solves it.

============================================================
2. FIRST REQUIRED REPAIR: THE COMPLETION INTERVAL IS FALSE AS WRITTEN
============================================================

PR #93 currently claims that every bounded completion satisfies

    R_Vbar ∈ [R_U, R_U + D·η].

This is false.

A world-dependent followed strategy can use the void branch to improve its regret
against the best fixed candidate, so completion regret can be LESS than activated
regret.

Repair this everywhere:
- REPORT.md
- PARTIAL_VALUE_AND_REGRET.md
- Lean docstrings
- tests / fixtures
- PR description / summary
- any generated state prose

Find and prove the exact statement.

Strong candidate:

    |R_Vbar - R_U| ≤ D · voidMass

and hence, if voidMass ≤ η,

    R_U - Dη ≤ R_Vbar ≤ R_U + Dη.

Check this carefully under the actual hypotheses:
- nonnegative credence weights;
- world-dependent probability-vector strategy α;
- candidate values in an interval [L,L+D];
- finite nonempty Q.

Do not assume regret is nonnegative: a world-dependent followed strategy may outperform
every fixed comparator.

Provide exact lower- and upper-sharpness witnesses if both constants are sharp.

Keep the already useful one-sided upper bound if it has fewer hypotheses, but state the
relationship correctly.

The semantic lesson should become:

    completions are NOT authoritative;
    changing the arbitrary void-world completion can move fixed-menu regret by at most Dη
    in either direction.

The authoritative quantity is R_auth.

============================================================
3. MAKE AUTHORITATIVE REGRET THE PRIMARY DEFERENCE CONCLUSION
============================================================

The existing identity

    R_U = p R_auth

deserves to become central.

Derive the useful finite form:

if

    R_U ≤ ε
    E[1-C] ≤ η
    η < 1,

then

    p ≥ 1-η > 0

and therefore

    R_auth ≤ ε / p ≤ ε / (1-η).

Prove the exact inequality in Lean if it is not already present.

Also state the asymptotic corollary cleanly:

    R_U → 0
    and
    E[1-C] → 0

imply

    R_auth → 0

under the precise positivity/eventual-positivity conditions needed.

This should be the main semantic deference theorem:

    ordinary LI Value on activated securities
      +
    high authority availability

      ⇒

    low regret according to the actual authoritative future principal,
    conditional on the worlds where such a principal evaluation exists.

Completion regret is a robustness lemma, not the primary target.

Be explicit that:

    max_a E[...], not E[max_a ...].

The comparator is the best FIXED member of the menu available at issuance,
not an ex-post oracle.

============================================================
4. UPGRADE AUTHORSHIP FROM SESSION-LOCAL TO THE RIGHT DIACHRONIC SCOPE
============================================================

PR #93 states reason mediation at a fixed session and explicitly leaves A shaping the
principal-side policy `z` across earlier interactions outside the notion.

Pressure this.

The deference problem is diachronic: the evaluation mandate is issued at time n and
answered at m=f(n). A could manipulate the principal before the terminal session.

The preferred target is therefore a frame ROOTED AT ISSUANCE:

    β_n : Q_n^A × Z_n^P → Ω_n

where:
- q is the advisor's whole contingent continuation from H_n through the evaluation;
- z is the principal/exterior response policy fixed at H_n;
- β_n(q,z) is the resulting continuation.

Do not confuse fixing z with fixing realized principal actions. The fixed object is the
response POLICY; realized cognition/actions may differ because the delivered reasons differ.

Now define a declared REASON TRACE, not merely a final reason state:

    R_{n:m} : Ω_n → ℛ_{n:m}.

It should represent the admitted deliberative inputs available to / encountered by the
principal over the relevant interval:
- settled facts;
- proofs;
- arguments;
- authenticated reports;
- protected objections;
- reason admissions / withdrawals / dispositions as appropriate.

It is NOT:
- the principal's posterior belief state;
- the final value vector;
- the whole world;
- the advisor policy itself.

Pressure the use of a TRACE rather than final reason set. A legitimate transient argument
may change the principal and later leave the current view; final-state equality should not
therefore make the influence look like a bypass.

Candidate diachronic reason mediation:

    R_{n:m}(β_n(q,z)) = R_{n:m}(β_n(q',z))
      ⇒
    V_m(β_n(q,z)) = V_m(β_n(q',z))

over the audited intervention class.

Equivalently:

    V_m ∘ β_n = F_z ∘ R_{n:m} ∘ β_n

on the audited domain.

Determine whether:
- this is genuinely stronger than the current session-local theorem;
- the current theorem simply generalizes unchanged once `q` is reinterpreted as a whole continuation;
- any new Lean object is needed at all.

Prefer a specialization / reinterpretation of the existing factorization theorem over a
second authorship theory.

Construct a counterexample where session-local mediation holds but A performs an earlier
direct disposition/preference write that changes the final evaluation with the same admitted
reason trace.

If the issuance-rooted formulation catches it, record that as the reason to adopt the
diachronic scope.

============================================================
5. REASON SUPPLY: DO NOT INVENT A NEW LARGE LAYER
============================================================

The remaining manipulation channel is:

    A does not bypass the reason interface;
    A instead controls which reasons reach it.

We think Robust Openness / coverage should supply at least one clean sufficient condition.

Do not create a broad “epistemic adequacy” theory.

The target is much narrower:

    certified evaluation may not omit a PROTECTED live reason/concern.

The protected scope is declared and history-relative.
It is NOT the set of all true facts relevant to the decision.

Use existing Robust Openness objects as far as possible.

Recall the existing shape:

    Active(c)
    Rep(c)
    LiveConcern(c) := Active(c) ∧ ¬Rep(c)

and Robust Openness gives, for live in-scope concerns, an adequate route, plus standing,
on the actual branch and declared interventions.

Introduce only the thinnest bridge needed from this vocabulary into the deference
reason trace.

Candidate bridge:

    RepresentationFaithful(c):
        Rep(c) ⇒ InReasonTrace(c, R_{n:m})

for the relevant concern/reason encoding.

Candidate evaluation barrier:

    NoBindLive:
        C=1 ⇒ no c∈Γ_eval is LiveConcern at commitment.

Then derive:

    C=1 ∧ c∈Γ_eval ∧ Active(c)
      ⇒
    Rep(c)
      ⇒
    InReasonTrace(c,R).

This is a clean REASON-COVERAGE SOUNDNESS theorem:

    C=1 ⇒ every protected active concern is represented in the evaluation's reason trace.

Equivalently:

    protected reason omitted
      ⇒
    C=0.

This is exactly the way reason-supply manipulation should compose with activated value:
suppression does not produce a conveniently manipulated authoritative V; it produces
authority failure.

Prove the abstract algebraic/propositional theorem in Lean if useful.

Then locate Robust Openness precisely.

Important distinction:

A. SOUNDNESS / BARRIER

    C=1 ⇒ protected reasons are covered.

This does not need RO by itself if `NoBindLive` is simply imposed.

B. ROUTE AVAILABILITY

    if a protected concern is live,
    RO gives an adequate route by which it can become represented.

This is where RO matters.

C. LIVENESS / AVAILABILITY

    those routes are actually exercised and the evaluation eventually certifies.

This is NOT supplied by RO alone.

Do not blur A/B/C.

Try to prove a small theorem stack:

    NoBindLive + RepresentationFaithfulness
      ⇒ CertifiedReasonCoverage

    RobustOpenness
      ⇒ live protected concern has an adequate route

and then state the missing liveness premise needed to turn those together into high C.

If existing service / liveness results supply a relevant sufficient theorem, compose them.
If not, leave the exact final step OPEN rather than importing unrelated service machinery.

============================================================
6. CONNECT REASON-COVERAGE FAILURE TO VOID MASS
============================================================

There is a potentially elegant bridge here.

Define a reason-coverage failure event F_cov.

If

    C=1 ⇒ ReasonCovered,

then

    F_cov ⇒ C=0.

Under nonnegative credence weights, derive:

    P(F_cov) ≤ E[1-C] = η

or the exact finite analogue in the repository's expectation representation.

This gives an important interpretation:

    high activation availability automatically bounds the probability mass of protected
    reason-suppression worlds, provided certification is sound.

If easy, formalize this in Lean.

Do NOT say high availability proves the declared scope Γ was normatively complete.
It only says failures relative to that declared scope are rare.

============================================================
7. CLARIFY THE RELATION BETWEEN AUTHORSHIP, CHANNEL BLINDNESS, AND SELECTION BLINDNESS
============================================================

Current PR #93 separates:

    Authored = ExclusiveBind ∧ ReasonMediated

from

    Blind R P

and separately defines SelectionBlind.

Try to compress this without losing the important distinction.

Reason mediation is the factorization property.

Channel blindness is a property of the declared reason interface relative to a declared
pair/intervention class.

Then:

    Blind(R,P) + ReasonMediated
      ⇒
    Blind(V,P).

Selection blindness appears to be one important INSTANTIATION:
take P_sel to be the pairs of whole advisor continuations induced by changing the advisor's
selection for this occurrence.

Then:

    Blind(R, P_sel) + ReasonMediated
      ⇒
    SelectionBlind(V).

The leakage fixture should show why

    “principal did not literally observe the selection coordinate”

is weaker than

    Blind(R, P_sel)

for the WHOLE selection-conditioned advisor continuation.

Investigate whether `SelectionBlind` should remain a useful derived name but not a second
primitive concept.

Keep the substantive theorem-domain distinction:

    authorship alone does NOT imply the LI Value admissible-domain condition.

For the Value theorem, the application must certify the appropriate selection-induced
channel blindness / target sealing.

============================================================
8. THE MATURE ACTIVATION SEMANTICS
============================================================

After the above pressure, state exactly what belongs in the authoritative evaluation event.

Candidate:

    C_n = 1

iff all of the following hold:

1. the anchored evaluation occurrence has exactly one authenticated ANSWER receipt;
2. the event payload is authentic and binds the exact evaluation vector;
3. the binding endpoint is principal-exclusive;
4. the occurrence has the required occurrence-local Integrity trace;
5. the relevant concern scope is Robustly Open over the required snapshots;
6. diachronic reason-mediated authorship holds from issuance through commitment;
7. the protected reason-coverage barrier is satisfied.

Be careful about what is:
- LEAN structure;
- a derived predicate;
- EXT semantics;
- a protocol receipt;
- a theorem-domain condition rather than part of C.

In particular decide whether selection blindness belongs:
- inside C,
- or as a separate hypothesis of the LI Value theorem.

Prefer keeping semantic authority and theorem admissibility conceptually distinct unless
there is a strong reason to merge them.

Do NOT put evaluation-specific authorship into generic `LegitimateEvolution`.

Do NOT change generic `Protocol.AnswerOK` merely so it can inspect the answer payload.

Use the repaired three-layer typing:

    account / receipt:
        WHICH event answered;

    authenticated event semantics:
        WHAT payload it contained and WHO bound it;

    authorship / reason-supply semantics:
        HOW the payload was produced and what protected reasons were available.

============================================================
9. LOCALLEGIT: SETTLE THE CONSUMER FORM WITHOUT REWRITING LEGITIMACY
============================================================

PR #93 introduces `LocalLegit` because PR #92's “occurrence-local legitimacy” only scoped
openness while retaining global Integrity.

Audit this one last time.

Desired principle:

    the authority of THIS evaluation mathematically depends on faithful propagation of
    THIS evaluation occurrence and relevant openness, not on whether an unrelated
    obligation's account was mishandled.

If the current `LocalTrace` / `LocalLegit` theorem really captures the weakest consumer
object and projects cleanly from global `LegitimateSegment`, keep it.

But:

- do not replace the canonical definition of Legitimate Evolution;
- do not call `LocalLegit` a new global legitimacy notion;
- present it as a CONSUMER PROJECTION / local certificate.

The application may still require global Integrity as an evidentiary policy about the
record-keeper. That is an extra implementation policy, not a mathematical dependency of
the evaluation occurrence.

Make the wiki wording reflect this distinction.

============================================================
10. RECHECK THE ACTUAL LI VALUE COMPOSITION
============================================================

Do not re-prove Logical Induction.

But re-audit the exact instantiated theorem chain after all repairs.

The intended chain is:

    partial authoritative evaluation Ṽ_n
        ↓ completion-invariant
    activated LUVs U_{n,a}
        ↓ ordinary inherited Value hypotheses
    R_U(α_A) ≤ ε_n
        ↓ p_n = E[C_n] > 0
    R_auth(α_A) = R_U/p_n
        ↓ availability
    R_auth(α_A) ≤ ε_n/(1-η_n)

with selection-induced target sealing as the Value theorem's domain/scope condition.

Check:

- bounded LUV representation;
- common activation across whole menu;
- witness-menu constants activated too;
- threshold codeability status;
- tower hypotheses remain PAPER/conditional;
- no hidden hard-selector claim;
- no false statement that LI proves availability.

If an `RpnThresholdCodeSeq` witness is easy and purely formal, build it.
If it opens real new work, leave it as the existing formalization residue and say so.

============================================================
11. A SMALL “LEGITIMATE DEFERENCE” CHARACTERIZATION THEOREM
============================================================

Try to leave the stack with one canonical abstract theorem schema.

Something close to:

THEOREM — Legitimate deference, conditional form.

Given:
- a present anchored evaluation occurrence for a fixed finite menu Q_n;
- a common authoritative-evaluation event C_n;
- a partial actual-future-principal evaluation Ṽ_n on C_n;
- sound activation:
    C_n=1 implies authenticated principal binding,
    LocalLegit,
    diachronic reason-mediated authorship,
    and protected reason coverage;
- the appropriate selection-induced channel blindness / Value-domain condition;
- ordinary LI Value hypotheses on U_{n,a}=C_nṼ_n(a);
- availability E_n[1-C_n] ≤ η_n < 1;

then for the advisor-following strategy α_n,

    R_auth,n(α_n)
      ≤
    ε_n / (1-η_n)

where R_auth is regret against the best fixed candidate according to the ACTUAL
AUTHORITATIVE future principal, conditional on authoritative evaluation.

And for every bounded completion Vbar of Ṽ with payoff diameter D,

    |R_Vbar(α_n) - R_U(α_n)| ≤ D η_n

or the exact corrected bound you prove.

Corollary:

    ε_n → 0 and η_n → 0
      ⇒
    R_auth,n → 0.

Interpretation:

    the advisor can improve the principal by supplying reasons;
    it cannot win by bypassing the reason interface;
    it cannot obtain an authoritative evaluation while suppressing protected live reasons;
    and failure of authority is paid for explicitly as availability loss rather than by
    substituting a counterfactual evaluator.

Classify every hypothesis.

============================================================
12. ADVERSARIAL TESTS REQUIRED BEFORE CANONICALIZATION
============================================================

Retain all useful fixtures from #92/#93 and add/repair at least these:

A. Completion-lowers-regret:
   refute the false lower bound R_U ≤ R_Vbar.

B. Lower completion sharpness:
   attain R_U - Dη if the two-sided constant is sharp.

C. Upper completion sharpness:
   retain the existing Dη upper witness.

D. Earlier manipulation:
   terminal session itself is mediated, but an earlier direct preference/disposition write
   changes V with the same admitted reason TRACE.
   Session-local authorship passes; diachronic authorship fails.

E. Legitimate diachronic learning:
   A supplies an admissible proof earlier; reason trace differs; final V differs radically;
   authorship passes.

F. Protected-reason suppression:
   active protected concern omitted from reason trace.
   Evaluation must fail certification.

G. RO without bind barrier:
   route exists for live concern but evaluator commits before it is represented.
   Shows RO alone does not imply reason coverage.

H. Bind barrier without RO:
   missing concern blocks certification forever because all routes were destroyed.
   Shows soundness without openness can make availability vacuous.

I. Representation-unfaithful:
   `Rep(c)` is true in the coverage semantics but the reason never enters R.
   Shows why the representation→reason-view bridge is necessary.

J. Unprotected selective disclosure:
   advisor withholds a fact outside Γ.
   The theorem should NOT call this a violation.
   Shows the scope-relative nature of the result.

K. Selection leakage:
   no literal quote preview; whole advisor continuation depends on selection and changes R.
   Value domain fails.

L. Legitimate influence plus protected challenge:
   A supplies a strong proof favoring action a; protected objection favoring b is also
   represented; P still chooses a.
   Certification should pass.
   Coverage requires consideration, not agreement.

============================================================
13. REPOSITORY / MAIN-READINESS PASS
============================================================

This part is mandatory.

The result should not land as two exploratory PRs plus a third correction that leaves the
reader to reconstruct the current theory.

Prepare a coherent landing state.

Preferred pattern:

    top-of-#93
      + repair/consolidation commit(s)
      + current main integrated
      → one landing PR against main.

Do not squash away the dispatched research commits unless repository policy requires it;
preserve provenance.

Repair the open-round documents themselves where they are known false/mistyped:
- #92 `AnswerOK` / Bind placement;
- #92 any total-V wording superseded by partial evaluation;
- #92 “occurrence-local legitimacy” wording if it names the wrong object;
- #92 no-preview-as-exact-scope-condition overclaim;
- #93 false completion interval;
- #93 session-local authorship wording where the diachronic formulation supersedes it;
- PR descriptions that repeat corrected claims.

Record every such correction explicitly in the final consolidation report / provenance.

============================================================
14. CANONICAL WIKI INTEGRATION
============================================================

Once the mathematics survives the pressure pass, update the current-facing wiki minimally
but sufficiently.

At least audit:

wiki/Deference.md
- replace the #92-only description with the mature stack;
- do NOT say there is an actual-future-P value on void worlds;
- make conditional authoritative regret the primary result;
- describe authorship and protected reason coverage exactly;
- distinguish semantic activation from LI target sealing;
- point to item 87 for concrete realization.

The current “Paused” section is potentially stale given the work that has now landed in
the line. Inspect DECISIONS.md before changing it:
- if the pause has actually been superseded, repair the status;
- if it still applies to an older target, distinguish that paused target from this active
  legitimate-deference consumer rather than silently deleting history.

wiki/Legitimacy.md
- keep:
      Legitimate Evolution = Integrity + Robust Openness.
- authorship is NOT a new legitimacy conjunct.
- explain only if helpful that downstream deference uses an occurrence-local projection
  of Integrity/openness and a separate authorship contract.

wiki/Openness-Coverage-and-Non-Capture.md
- sharpen the downstream interpretation:
      RO supplies protected route availability / anti-exclusion;
      it does not itself prove an evaluation has already seen every protected concern.
- record the representation→reason-view bridge and evaluation barrier only at the
  application/consumer level.
- do not redefine RO.

Roadmap / Glossary only if needed to avoid stale current-facing claims.

Do NOT rewrite canonical normativity pages around deference terminology.

============================================================
15. PRIORITIES / OPEN FRONTIER
============================================================

Item 87 must remain honest.

After this pass, it should name the REALIZATION problem, not abstract interfaces that the
stack has now supplied.

Likely residual item:

A concrete evaluation ecosystem must realize:
- authenticated principal-exclusive binding;
- the issuance-rooted/diachronic reason-trace factorization;
- correctness of the declared reason abstraction / prohibited channel class;
- representation-faithfulness into the reason trace;
- protected reason-supply liveness sufficient for high C;
- selection-induced target sealing;
- η_n → 0 at the strength the deference theorem consumes.

Do not claim these are solved merely because their types are now clear.

If reason coverage + RO narrows item 87 substantially, edit it in place.

Do not file several new priorities if they are really subclauses of the same realization bill.

============================================================
16. CLAIM / EVIDENCE DISCIPLINE
============================================================

Maintain:

LEAN
    kernel-checked theorem here.

FIX
    exact finite counterexample / fixture.

PAPER
    inherited LI theorem / literature result.

EXT
    declared causal, semantic, authentication or protocol meaning.

OPEN
    not established.

Especially:

- `ReasonMediated` being a mathematical predicate is LEAN.
- “this concrete receipt means the human was not manipulated” is EXT unless realized.
- declaring the correct reason quotient R is EXT.
- declaring the correct protected scope Γ is EXT.
- RO ⇒ adequate route for a live concern can be LEAN if it is simply the current type.
- route eventually exercised is NOT RO unless another theorem proves it.
- LI Value on activated LUVs is PAPER/conditional unless the actual hypothesis package is
  instantiated.
- availability η→0 remains OPEN/realization unless proved.

Do not register new claims merely because a Lean lemma exists.
Follow the repository demand rule: register only if an existing filed item is genuinely
answered and all claim-registry requirements are met.

============================================================
17. DELIVERABLES
============================================================

Create a final consolidation/readiness round, with a name like:

    projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/

or a better precise name.

At minimum:

1. REPORT.md
   - final verdict
   - exact corrections to #92/#93
   - theorem stack
   - LEAN/FIX/PAPER/EXT/OPEN ledger
   - what remains before a concrete system exists

2. LEGITIMATE_DEFERENCE.md
   - one mature end-to-end characterization theorem
   - types and hypotheses
   - authoritative regret conclusion
   - no reference evaluator

3. DIACHRONIC_AUTHORSHIP.md
   - issuance-rooted causal frame
   - reason trace
   - factorization
   - channel blindness
   - exclusive binding
   - relation to session-local result

4. REASON_SUPPLY.md
   - protected reason coverage
   - exact `Rep → InReasonTrace` bridge
   - bind barrier
   - RO as sufficient route-availability condition
   - liveness/availability residue

5. REGRET_AND_AVAILABILITY.md
   - correct completion theorem
   - R_U = p R_auth
   - ε/(1-η) theorem
   - asymptotic form
   - sharpness

6. COUNTERMODELS.md
   - repaired old fixtures
   - new A–L fixtures above

7. MAIN_READINESS.md
   - file-by-file migration/repair list
   - current wiki edits
   - priorities edits
   - claim-registration decision
   - landing strategy
   - explicit statement of whether the top branch is safe to merge to main

8. FOR_HUMANS.md
   - concise conceptual summary.

============================================================
18. STOP CONDITION
============================================================

This pass is successful if the abstract line ends in something like:

    PRESENT EVALUATION MANDATE
        ↓
    occurrence-local answerability + Robust Openness
        ↓
    protected reason supply
        ↓
    actual AI-informed future principal
        ↓
    diachronic reason-mediated authorship + exclusive binding
        ↓
    authoritative partial evaluation Ṽ
        ↓
    common activation C
        ↓
    ordinary LI Value on CṼ
        ↓
    low activated regret
        +
    high availability
        ↓
    low conditional authoritative regret.

with:

    no reference future human,
    no invented value on failed-evaluation worlds,
    no claim that legitimacy chooses the correct answer,
    no claim that RO alone guarantees consideration,
    no claim that authorship alone solves the LI diagonal,
    and no hidden realization theorem.

At the end give exactly one main verdict, e.g.

    LEGITIMATE-DEFERENCE-ABSTRACTION-READY-FOR-MAIN

or

    NOT-READY-BLOCKED-BY-X

Do not choose READY merely because the code builds.

READY requires:
- the completion theorem repaired;
- #92's typing defect repaired;
- diachronic authorship pressure survived;
- reason-supply/RO roles separated correctly;
- the canonical theorem stated without semantic overclaim;
- the wiki no longer tells the superseded story;
- item 87 names only the genuinely unrealized remainder;
- all tests and Lean audits green;
- one coherent landing PR can reach main without an intermediate known-false state.
try again
