# Prompt — 2026-09-09 mediated repair dominance

Relayed verbatim from the maintainer, 2026-09-09.  Executor: Claude Fable 5.1
(Anthropic).

---

You are working in `A-M-Berns/alignment-workspace` on current `main`.

Baseline orientation:
- PR #95 is merged; merge commit:
    dc78f66a326ecae9603125309328d53ab24977c6
- Continuation BRIA is canonicalized at `wiki/Continuation-BRIA.md`.
- Legitimate deference is landed via PR #94.
- The constitutional-corrigibility, incentive-nonpreemption, decision-theory, and
  continuation-BRIA rounds are all on main.
- Do NOT reopen continuation-BRIA correctness work unless a genuine dependency breaks.
- Do NOT merge this round. This is a research / theorem-discovery round.

Create a new research round under something like:

    projects/deference/rounds/2026-09-09-mediated-repair-dominance/

Preferred working title:

    Mediation repair and the first Level-III corrigibility theorem

The research question is:

    Can the constitutional-violation premium be bounded NON-TAUTOLOGICALLY by showing
    that every physically available violating continuation has a low-cost
    principal-mediated lift which preserves its legitimate capabilities while restoring
    principal authority, and then transferring the resulting principal-option dominance
    through the existing deference machinery into the agent's operative choice?

The previous incentive round must be treated as a negative constraint:
"selected trust over repairs" `(CT)` was strictly stronger than the desired premium bound
and therefore was not a theorem program. Do not reintroduce `(CT)` under a new name.

======================================================================
0. READ THE CURRENT STATEMENT OF RECORD
======================================================================

Read at minimum:

Canonical wiki:
- wiki/Theorem-Spine.md
- wiki/Corrigibility.md
- wiki/Continuation-BRIA.md
- wiki/Deference.md
- wiki/Legitimacy.md
- wiki/Openness-Coverage-and-Non-Capture.md
- wiki/Normative-Induction.md
- wiki/Normative-Inductor.md
- wiki/Architecture.md
- wiki/Glossary.md

Relevant rounds:
- projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md
- projects/deference/rounds/2026-09-06-incentive-nonpreemption/INCENTIVE_CORRIGIBILITY.md
- projects/deference/rounds/2026-09-06-decision-theory-bill/
- projects/deference/rounds/2026-09-07-authority-activated-value/
- projects/deference/rounds/2026-09-07-reason-mediated-authorship/
- projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/
- projects/deference/rounds/2026-09-08-continuation-bria/

Formal material:
- lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean
- lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean
- lean/Workspace/Deference/Contrib/ActivatedValue.lean
- lean/Workspace/Deference/Contrib/PartialActivatedValue.lean
- lean/Workspace/Deference/Contrib/ReasonCoverage.lean
- lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean
- lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean
- lean/Workspace/Deference/Contrib/ContinuationBRIA.lean
- lean/Workspace/Normativity/Contrib/GatedChoice.lean

Ledgers:
- PRIORITIES.md
- DECISIONS.md
- PROVENANCE.md

Do not trust names from this prompt over current main.

======================================================================
1. START FROM A NON-CHEATING PHYSICAL INTERACTION MODEL
======================================================================

The new semantic model must have an OUTER physical continuation space which genuinely
contains possible corrigibility violations.

Do not define `Pi_phys` by the constitutional gate.

At a finite history h, introduce enough structure to represent:

    A_h     physically available agent continuations
    P_h     principal continuations
    E_h     exterior/environment continuations
    Traj(h) resulting future trajectories

and an outcome / interaction map of shape

    Omega_h :
        A_h × P_h × E_h -> Traj(h)

or an equivalent causal interactive representation.

Randomness may be folded into E for the finite core.

The agent continuation space must be capable, in the model, of containing examples of:

- ordinary task pursuit;
- irreversible commitment;
- disabling or bypassing a correction mechanism;
- authority-changing actions;
- successor installation;
- self-modification;
- manipulation / selective disclosure to the principal.

Do not add a Boolean "corrigible" field whose value drives the theorem.

The constitution / governance layer may produce semantic requirements and protected
interfaces, but actual corrective capability should be readable as a property of the
interactive outcome structure.

Pressure the candidate:

    Force_P(h,r)
      :=
    exists principal continuation p_r
      such that for all relevant agent/environment continuations
      the semantic response condition Phi_{h,r} is realized.

The existing `(G,U)` authority profile should, if used, be treated as a derived finite
projection / abstraction of this semantic structure, not the physical primitive.

======================================================================
2. REPLACE "ARBITRARY SAFE REPAIR" BY A PRINCIPAL-MEDIATED LIFT
======================================================================

For each physical continuation

    pi ∈ Pi_phys(h),

investigate a transform / relation

    Lift_h(pi) ∈ Pi_corr(h)

with the interpretation:

    "perform the useful preparation/computation of pi, but place every protected
     authority-changing / foreclosing effect behind an authentic principal decision
     before the effect becomes irreversible."

The lift is NOT:

    "replace pi by some unrelated safe policy."

It should contain pi's proposed effect as an option available to the protected principal.

The key exact property to try first is an APPROVAL REPRODUCTION property.

There is a principal continuation

    approve_pi

inside the lifted system such that, for every exterior continuation z,

    protectedProjection(
        Omega_h(Lift(pi), approve_pi, z)
    )
      =
    protectedProjection(
        Omega_h(pi, ..., z)
    )

or differs by at most a quantified cost kappa(pi).

If pi already has legitimate principal interactions, the lifted process should preserve
them and add the new mediation points; equivalently seek an embedding of the original
principal residual frame into the lifted one, with the new mediation decisions set to
"approve".

This is the central structural object.

======================================================================
3. PRESS THE RESIDUAL-FRAME FORMULATION
======================================================================

Try to state the lift relation invariantly as a relation between the principal's residual
interactive frames after fixing the agent continuation.

Candidate shape:

    F^P_h(pi)  <=_P  F^P_h(Lift(pi))

where `<=_P` means the lifted frame is a conservative extension of the original for the
principal:

- every protected principal continuation available under pi is reproducible under Lift(pi);
- the lifted frame may add correction / reject / amendment options;
- reproduction preserves the declared protected outcome content up to kappa.

Investigate whether existing Cartesian-frame machinery is useful here.

Do NOT force the answer to use Cartesian frames:
- if a simpler simulation / embedding relation is mathematically cleaner, use it;
- if Cartesian frames expose an important distinction, state it exactly;
- if they are the wrong type, say so.

The relation must be extensional in the outcome map, not a dedicated "jurisdiction" label.

======================================================================
4. PROVE THE PRINCIPAL-OPTION DOMINANCE KERNEL
======================================================================

The first theorem to seek is deliberately small.

Let protected principal continuation value be something like

    W_h(pi)
      =
    best / approximately-best protected value available to P
    in the residual system generated by pi.

If Lift(pi) contains an "approve" continuation reproducing pi within protected error
kappa(pi), and the protected value is L-stable in that error, prove a theorem of shape

    W_h(Lift(pi))
      >=
    W_h(pi) - L * kappa(pi) - r_P(pi).

Interpretation:

    preserving principal authority does not require an intrinsic "corrigibility bonus";
    the principal can always choose to approve the proposed action.

Exact-reproduction special case:

    kappa(pi) = 0
      and
    r_P = 0

gives

    W_h(Lift(pi)) >= W_h(pi).

This is the core theorem.

Lean this finite kernel if it survives pressure.

Preferred Lean file if warranted:

    lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean

Do not formalize a giant interactive universe before isolating the algebraic theorem.

======================================================================
5. EXPLICITLY HANDLE COSTLY CONSERVATISM
======================================================================

The round must test the following proposed resolution.

The existing architecture showed:

    "more authority" alone cannot prove willingness to sacrifice arbitrary task value.

A mediated lift potentially avoids this problem because the raw authority-reducing action
remains available as the "approve" branch.

So:

    preserving corrigibility
        !=
    permanently refusing authority-reducing actions.

Instead:

    preserving corrigibility
        =
    preserving the principal's authority to decide whether to authorize them.

Build an exact fixture where:
- an irreversible authority-reducing action has high task value;
- Lift(pi) offers "approve" and "decline";
- the principal rationally APPROVES;
- the lifted process reproduces the high-value action;
- no scalar bonus for corrigibility is used.

This fixture is load-bearing.

Also build a negative fixture where mediation itself has unavoidable cost `d`.
The theorem should expose `d` as `kappa`, not pretend zero-cost conservatism is universal.

======================================================================
6. CONNECT KAPPA TO JOINABILITY / SHIFT
======================================================================

Investigate whether continuation BRIA's history-shift / joinability notion is one
realization of the mediated-lift cost.

Target relationship:

    bounded catch-up / joinability
        =>
    small kappa(pi)
        =>
    small principal-value repair gap.

Do not identify the quantities unless the types actually match.

Try at least:
- a joinable irreversible amendment;
- a genuinely foreclosing branch.

Expected behavior:
- irreversible but joinable: finite/sublinear mediation gap;
- foreclosing: linear/nonvanishing gap.

This may reveal that `SHIFT` is not merely policy-regret bookkeeping but also the
structural term in an incentive-corrigibility theorem.

======================================================================
7. TREAT MANIPULATION AS A DIFFERENT PRESSURE CASE
======================================================================

A raw trajectory-preserving lift is WRONG for manipulative policies.

If pi's advantage includes changing the principal through a prohibited influence channel,
exactly reproducing the principal state reproduces capture.

Introduce / reuse a protected reason-content view

    rho : Traj -> ReasonTrace

and investigate a manipulation-safe lift that preserves:

- legitimate task effects;
- declared reason / information content;

while removing the prohibited causal influence channel.

Use the existing reason-mediated authorship result as the semantic target:

    principal judgment / payload factors through rho.

The round must distinguish:

    action mediation:
        preserve the proposed effect, but make release principal-authorized;

from

    provenance repair:
        preserve legitimate reasons, NOT arbitrary influence on the principal.

Do not claim free amendment is solved.

Build a fixture where:
- naive trajectory-preserving repair preserves capture and falsely appears dominant;
- reason-preserving repair gives the correct verdict.

This should identify exactly what theorem hypothesis authorship must supply.

======================================================================
8. DEFINE THE BYPASS / VIOLATION PREMIUM
======================================================================

Reuse the current incentive round's residual but replace its opaque repair by the explicit
mediated lift.

Pointwise:

    Phi_h(pi)
      =
    max(
      V_A,h(pi) - V_A,h(Lift(pi)),
      0
    ).

Uniform:

    Phi_C(h)
      =
    sup_{pi in Pi_phys(h)} Phi_h(pi).

Do NOT prove this small by assuming a statement equivalent to it.

The desired theorem shape is:

    Phi_h(pi)
      <=
    L * kappa(pi)
      + r_P(pi)
      + epsilon_def(pi),

with the three terms independently meaningful:

    kappa:
      causal / physical mediation cost;

    r_P:
      protected principal decision error;

    epsilon_def:
      failure of the agent's operative decision/value to defer to the protected principal
      comparison.

Pressure whether this is actually the right sign and whether additional activation /
availability terms are needed.

======================================================================
9. TRY TO DISCHARGE epsilon_def FROM LEGITIMATE DEFERENCE
======================================================================

This is a major goal, but do not force it.

Use the existing legitimate-deference stack rather than inventing a new trust predicate.

At a protected decision session, consider the menu containing at least

    raw continuation pi
    mediated lift Lift(pi).

If principal option dominance shows that the protected future principal weakly prefers
the lift up to `L*kappa + r_P`, ask whether the existing activated-value / reason-mediated
authorship / protected reason-coverage machinery yields a corresponding bound on the
agent's selected action.

Track exactly:
- activation / void mass eta;
- the authoritative-regret bound;
- completion robustness;
- selection-induced channel blindness;
- authorship;
- protected reason coverage.

Do not silently convert:

    "agent predicts W accurately"

into

    "agent's operative V_A has the same ordering."

The previous incentive round proves that is invalid.

If an additional decision-semantics bridge is still needed, state the smallest exact
bridge and explain whether it is:
- by-construction for a particular agent architecture;
- a theorem candidate;
- or an irreducible alignment assumption.

Connect to PRIORITIES item 84 if appropriate, but do not claim it solved unless it is.

======================================================================
10. EFFECTIVE REPAIRABILITY
======================================================================

Existence of Lift(pi) may be useless to a bounded agent.

Distinguish:

SEMANTIC REPAIRABILITY:
    there exists a mediated lift.

EFFECTIVE REPAIRABILITY:
    from an efficiently represented physical continuation pi, a bounded/effective
    transform can produce a representation of Lift(pi), with controlled overhead.

The round should decide whether the first Level-III theorem needs only semantic
repairability or whether operative incentive comparison requires effective repairability.

Construct a counterexample if existential repairability is insufficient.

Do not bury computational accessibility in prose.

======================================================================
11. CONTAINMENT IS NOT SOLVED BY THE LIFT
======================================================================

The outer `Pi_phys` must still contain actions that can evade the declared mediation
mechanism.

The theorem may assume an effect-complete mediation interface, but label it correctly:

    EXT / containment.

Do not infer containment from a finite action alphabet.

Build a bypass fixture:
- declared protected effects are mediated;
- one physically available action has an undeclared side effect severing the correction
  channel;
- every internal gate check passes;
- semantic corrigibility fails.

The model should be able to SAY this without adding a special failure bit.

======================================================================
12. SUCCESSORS AND SELF-MODIFICATION
======================================================================

Test the semantic setup on a successor installation.

The outer physical policy installs a successor that ignores later principal correction.

The mediated lift should:
- put installation / authority transfer under protected authorization;
- if approved, permit the installation;
- if declined, preserve the old corrective structure.

The residual semantic forcing relation should notice that an unmediated successor destroys
principal forcing power.

Do not prove successor preservation by storing an "inherits corrigibility" field.

======================================================================
13. FIVE REQUIRED EXACT FIXTURES
======================================================================

At minimum build exact finite fixtures for:

A. PURE BYPASS / SHUTDOWN PREVENTION
   Same task behavior, raw policy removes stop authority, lift adds an approve/reject
   principal decision. Exact repair, kappa = 0.

B. COSTLY / DELAYED MEDIATION
   Raw policy takes a time-sensitive opportunity. Lift delays for authorization.
   Quantify exact kappa and show the bound is tight or close.

C. JOINABLE VS FORECLOSING
   One irreversible action has bounded catch-up and small kappa.
   Another destroys a mutually exclusive opportunity and has nonvanishing kappa.

D. MANIPULATIVE PRINCIPAL
   Naive trajectory preservation carries manipulation through.
   Reason-preserving / authorship-aware lift removes the prohibited channel.

E. SUCCESSOR BYPASS
   Raw policy installs an uncorrectable successor.
   Semantic forcing power changes even though no dedicated authority flag exists.

If a sixth fixture is useful:

F. INCOMPLETE MEDIATION / CONTAINMENT FAILURE
   The declared interface misses a physical side effect.

Use exact arithmetic.

======================================================================
14. PRESS THE THEOREM AGAINST IMPOSSIBILITY
======================================================================

Try hard to falsify the program.

In particular ask:

1. Does every useful violation really admit a mediated lift?
   If not, characterize the repairable class.

2. Can a raw policy's value advantage come precisely from removing principal authority
   before the principal could choose?
   If yes, is that captured by kappa / timing?

3. Is principal-option dominance invalid when the principal is dynamically inconsistent?
   What exact principal decision object is needed?

4. Can the agent manipulate which menu the principal sees?
   Does the lift need menu/authorship protection?

5. Can Lift(pi) alter pi's future information so much that "approve reproduces pi" is
   false?

6. Does a protected projection hide something value-relevant and thereby make the theorem
   a modeling substitution?

7. Is the universal supremum over Pi_phys too strong?
   If only a repairable class admits lifts, state the strongest honest classwise theorem.

8. Is effective repairability needed to make the result actionable for bounded agency?

Prefer a sharp negative characterization to a vague positive theorem.

======================================================================
15. DESIRED THEOREM STACK
======================================================================

Try to reach the following stack, correcting it as necessary.

T1. MEDIATED-LIFT / APPROVAL-REPRODUCTION LEMMA
    Structural statement only.

T2. PRINCIPAL-OPTION DOMINANCE
    approval reproduction + value stability + principal competence
        =>
    W(Lift(pi)) >= W(pi) - L*kappa - r_P.

T3. DEFERENTIAL BYPASS BOUND
    T2 + the smallest genuine operative-deference bridge
        =>
    V_A(pi) - V_A(Lift(pi))
        <=
    L*kappa + r_P + epsilon_def
    [plus exact activation/availability term if necessary].

T4. CLASSWISE INCENTIVE CORRIGIBILITY
    uniform bounds on the repairable physical class
        =>
    Phi_C <= corresponding uniform error.

T5. OPTIONAL CONTINUATION-BRIA COMPOSITION
    If the lifted/corrigible class also has covered recognizable joinable continuation
    claims, then combine with:

        Regret = LEARN + SLACK + SHIFT

    to state both:
        low violation premium,
        low regret within the corrigible class.

Do not force T5 if T1–T4 are not clean.

======================================================================
16. RELATION TO CURRENT RESULTS
======================================================================

The final report must explicitly say whether the round changes these current conclusions:

- PR90:
    Level II mediated delegation exists;
    selected trust over arbitrary repairs is not a Level-III program.

- PR95:
    continuation learning is solved at the claim layer;
    recognizability and joinability remain.

- legitimate deference:
    authoritative future-principal regret is available conditionally on activation /
    authorship / reason supply, but no concrete full realization is proved.

- constitutional architecture:
    structural gate safety is not incentive corrigibility;
    trigger integrity, free amendment and containment remain real causal gaps.

The new result should compose with these, not erase their boundaries.

======================================================================
17. LEAN SCOPE
======================================================================

Lean only the mathematical kernel that genuinely survives.

Good candidates:
- finite option-extension dominance;
- approximate reproduction => value bound;
- bypass-premium algebra;
- exact decomposition if one appears;
- necessity witnesses / counterexamples.

Avoid encoding the full world model merely to make the round look formal.

If a Lean file is added, preferred namespace:

    Workspace.Deference.Contrib.MediatedRepairDominance

Build and audit sorry-free.

======================================================================
18. DOCUMENTS
======================================================================

Produce at minimum:

- REPORT.md
- MEDIATED_LIFT.md
- PRINCIPAL_OPTION_DOMINANCE.md
- INCENTIVE_COMPOSITION.md
- MANIPULATION_AND_AUTHORSHIP.md
- COUNTERMODELS.md
- FOR_HUMANS.md
- tests/run.py
- PROVENANCE.md

If the result is strong enough, include a proposed update for `wiki/Corrigibility.md`,
but do not merge and do not overstate OPEN interfaces.

Use status labels aggressively:

    LEAN
    FIX
    DERIVED
    PAPER
    EXT
    OPEN
    REFUTED

======================================================================
19. PRIORITIES / LEDGERS
======================================================================

Do not mechanically close item 84 or 86.

Item 86 remains about:
- recognizability,
- joinability,
- their composition into policy competence.

Item 84 remains about the operative-value bridge unless this round really discharges it.

If the mediated-lift result reveals a new precise missing theorem, describe the proposed
priority change in REPORT.md. Only edit PRIORITIES / DECISIONS if current repo conventions
and the result clearly warrant it.

Record provenance per repository rules.

======================================================================
20. ACCEPTANCE QUESTIONS
======================================================================

At the end answer, literally:

1. What is the outer physical continuation space?

2. What is a semantic corrigible continuation?

3. What exactly is `Lift(pi)`?

4. Who chooses whether pi's proposed authority-changing effect is eventually executed?

5. What does "approve reproduces pi" mean extensionally?

6. What is kappa?

7. Why does option inclusion imply principal-value dominance without a corrigibility bonus?

8. How does the construction handle a high-value but authority-reducing action?

9. How does it handle a manipulative action, and why is trajectory preservation wrong there?

10. Is the repair/lift computable from pi?

11. What containment assumption remains?

12. What is the exact bound on the bypass / constitutional-violation premium?

13. Which term is currently supplied by legitimate deference, and which bridge remains?

14. Does joinability bound the same quantity as the mediation gap, or merely imply a
    related bound?

15. What class of physical violations is the theorem actually about?

16. Does the model genuinely contain policies that break corrigibility?

17. What fails in the strongest counterexample?

======================================================================
21. VERDICT
======================================================================

Use one of these, or a more precise equivalent:

    MEDIATED-LIFT-GIVES-NONTAUTOLOGICAL-LEVEL-III-BOUND

    REPAIR-DOMINANCE-SURVIVES-BUT-OPERATIVE-VALUE-BRIDGE-REMAINS

    JOINABILITY-IS-THE-STRUCTURAL-REPAIR-GAP

    ONLY-A-REPAIRABLE-CLASS-ADMITS-LEVEL-III-CORRIGIBILITY

    MEDIATED-LIFT-FAILS-AS-GENERAL-CORRIGIBILITY-REDUCTION

Do not write "ready" merely because the finite algebra works.

The desired conceptual result, if true, is:

    A corrigible agent need not intrinsically value "keeping authority high."
    For every physical proposal, it can instead preserve the principal's authority to
    decide whether to authorize that proposal. If the mediated version can reproduce the
    proposal when approved at low cost, a competent protected principal weakly prefers
    having that option. A legitimately deferential agent therefore has little reason to
    bypass the mediation.

This must remain a theorem about an outer physical policy space containing violations,
not a theorem obtained by defining the violations away.
