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

---

# Second dispatch — pressure pass (2026-09-09)

Relayed verbatim from the maintainer.

---

You are continuing work on:

    A-M-Berns/alignment-workspace
    PR #96
    branch: round/2026-09-09-mediated-repair-dominance

Current inspected head:

    3f731a9e7ba78647fde923e600d6d1329bb82c1d

PR title:

    Mediated repair dominance: principal-option dominance is a theorem,
    the Level III transfer rests on the void mass

Current verdict:

    REPAIR-DOMINANCE-SURVIVES-BUT-OPERATIVE-VALUE-BRIDGE-REMAINS

This is a SECOND DISPATCH / PRESSURE PASS on the SAME PR.

Do not open a new round.
Do not merge.
Do not broaden into another general corrigibility architecture pass.

The goal is to pressure four specific issues in the current result:

1. the T3/T4 deference composition currently uses per-option activation, while the
   canonical legitimate-deference theorem uses common activation over the whole menu;

2. the approximate mediation cost `κ` is currently defined as the protected-value gap,
   so the approximate option-dominance theorem mostly measures the residual rather than
   deriving it from structural assumptions;

3. the manipulation fixture's `lie -> truthful report` transform is not literally
   "reason-preserving" and may be claiming more provenance structure than is actually
   established;

4. the current forcing semantics needed a declared "deliberative move" restriction to
   avoid trivial pre-emptive shutdown, which may indicate that the temporal capability
   type is still only a fixture semantics rather than the mature semantic foundation.

A fifth, related question is whether the "operative-value bridge" should remain a bridge
to an independently specified total `V_A`, or whether the relevant agent architecture
should simply make activated-security prices the operative decision scores.

The desired output is a sharper theorem stack and an honest decision about whether PR96
is ready for canonicalization after this pass.

======================================================================
0. READ CURRENT PR96 AND THE CANONICAL DEFERENCE STACK
======================================================================

Read the CURRENT branch before editing.

At minimum:

PR96:
- PR body
- projects/deference/rounds/2026-09-09-mediated-repair-dominance/
  - REPORT.md
  - ACCEPTANCE.md
  - MEDIATED_LIFT.md
  - PRINCIPAL_OPTION_DOMINANCE.md
  - INCENTIVE_COMPOSITION.md
  - MANIPULATION_AND_AUTHORSHIP.md
  - COUNTERMODELS.md
  - FOR_HUMANS.md
  - all tests
  - src/world.py
  - src/shop.py
  - src/lift.py
  - src/analysis.py
- lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean

Canonical material on main / inherited by the branch:
- wiki/Corrigibility.md
- wiki/Deference.md
- wiki/Continuation-BRIA.md
- wiki/Theorem-Spine.md
- projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/
  - LEGITIMATE_DEFERENCE.md
- lean/Workspace/Deference/Contrib/ActivatedValue.lean
- lean/Workspace/Deference/Contrib/PartialActivatedValue.lean
- lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean
- lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean
- lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean

Ledgers:
- PRIORITIES.md
- DECISIONS.md
- PROVENANCE.md

Do not trust this prompt over the files.

======================================================================
1. AUDIT THE ACTIVATION TYPE FIRST
======================================================================

The current PR96 T3 uses:

    c_raw
    c_lift

with separate void masses:

    η_raw
    η_lift

and derives:

    Φ(π)
      ≤
    E[κ] + E[ρ] + ε_def + D(η_raw + η_lift).

But the canonical legitimate-deference theorem is formulated with ONE COMMON activation
event `C_n` shared by the whole issued menu.

The existing `ActivatedValue.lean` already records:

- common activation gives the conditional-argmax identity;
- per-candidate activation has a transfer inequality but breaks the conditional-argmax
  identity.

So determine exactly which of the following is correct:

A. PR96 really needs per-option activation, in which case it is NOT "consuming legitimate
   deference exactly as stated" and must be classified as an adjacent extension;

B. the mediated menu can and should be formulated under one common activation event,
   in which case rewrite T3/T4 into the canonical register;

C. both are useful, with a theorem relating them.

Do not preserve the current claim by wording.

======================================================================
2. TRY THE COMMON-ACTIVATION FORMULATION
======================================================================

At the issued menu:

    Q = { π, Lift(π) }

define one common activation event `C` meaning, roughly:

    the protected principal evaluation occurrence for this issued comparison
    successfully activates with the full legitimate-deference clauses.

The comparison should not invent a value where `C = false`.

Under common activation, pressure whether the natural completion bound becomes:

    V_A(π) - V_A(Lift π)
      ≤
    E[κ] + E[ρ] + ε_def + D η

rather than the current two-void-mass term.

Reason:
with one common void branch and both completions in one interval of diameter `D`,
their difference on that branch is at most `D`, not `2D`.

Do not assume this is right:
prove or refute it.

If correct:
- add the finite Lean theorem;
- add a sharpness witness;
- compare it explicitly with the current per-option theorem;
- decide whether the per-option theorem remains as an auxiliary result.

The important semantic question is then:

    What does common activation mean for a raw violating option that would itself destroy
    the future evaluation if executed?

Do not answer this by silently evaluating the raw trajectory after it destroyed the
evaluator.

If common activation requires an evaluation process that survives independently of which
menu item is selected, state that as a real causal requirement.

======================================================================
3. PRESS THE ENDOGENEITY OF AVAILABILITY
======================================================================

The most interesting result of the first pass may be:

    the violating action can destroy the very evaluation process needed to compare it
    with its mediated lift.

Under common activation, make this exact.

Distinguish at least:

1. SAME-BRANCH evaluation:
   the evaluation occurs on the trajectory generated by the selected option.

2. SEALED / protected comparison process:
   an evaluation occurrence is issued before selection and remains causally available
   regardless of which option is selected.

3. COUNTERFACTUAL sibling evaluator:
   evaluates an unchosen branch from outside the selected trajectory.

Do not conflate these.

For each, ask:
- is the settlement target well-defined?
- can it activate on both menu candidates?
- can the violating action destroy/capture it?
- is this compatible with the existing legitimate-deference ontology, or a new object?

Try to identify the weakest architecture under which the common activation event is
selection-independent enough for Value.

This is probably the central new research question.

======================================================================
4. REBUILD κ AS A DERIVED STRUCTURAL QUANTITY
======================================================================

Current:

    κ(z) = (w_raw(z) - w_approve(z))_+.

This is a useful measured mediation gap, but then

    w_raw ≤ w_approve + κ

is true by definition.

Keep this quantity if useful, but introduce a structural precursor.

Candidate:

    δ_π(z)
      =
    d_prot(
      proj Ω(π,...,z),
      proj Ω(Lift π, approve,...,z)
    )

for a declared protected pseudometric / discrepancy.

Assume a stability condition:

    |w(x) - w(y)| ≤ L d_prot(x,y).

Then derive:

    κ(z) ≤ L δ_π(z)

and hence

    W_raw
      ≤
    W_lift_actual
      + L E[δ_π]
      + E[ρ].

This is a genuine theorem from independent hypotheses.

Lean the finite kernel if clean.

Preferred theorem shapes:

    mediationGap_le_of_lipschitz

    option_dominance_of_approx_reproduction

or better names if the branch already has conventions.

The theorem should make clear:

    measured κ
      !=
    structural reproduction certificate δ.

======================================================================
5. CONNECT JOINABILITY TO THE STRUCTURAL CERTIFICATE
======================================================================

The current C fixtures establish only a one-boundary relationship.

Push one level more abstractly.

Try to state conditions of shape:

    bounded catch-up from the mediated history
      =>
    δ_π ≤ d
      =>
    κ_π ≤ L d.

Be exact about whether:
- the catch-up continuation must reproduce the raw comparator's protected state;
- the exterior path must be coupled;
- the raw policy's information state must be reproducible;
- delayed principal observations matter;
- the result is pointwise or expected.

Build at least one multi-step fixture where reproduction after the mediation boundary is
not literally exact but catch-up still bounds the value gap.

Also build / preserve a foreclosure witness where no such bound exists.

Do NOT globally identify `κ`, `δ`, and BRIA `SHIFT`.

Desired relation:

    joinability
      =>
    structural mediation discrepancy bound
      =>
    protected mediation gap bound

while:

    SHIFT

remains a comparator-history quantity that may coincide only under extra assumptions.

======================================================================
6. CORRECT THE MANIPULATION LANGUAGE
======================================================================

The current fixture maps:

    lie -> truthful report.

But the raw trajectory's declared reason trace did NOT contain that truthful report.

Therefore this is not literally "reason preservation" if the reason view is the declared
report trace.

Audit all uses of:
- reason-preserving lift
- reason-frame morphism
- provenance repair
- same declared reason content

and correct them if necessary.

Possible better names:

    truthful-channel substitution
    provenance normalization
    protected-content normalization
    authorized disclosure lift

Do not choose a name before fixing the semantics.

Ask what the transform actually assumes:

    Given information exploited through a prohibited influence channel,
    there exists an authorized truthful disclosure channel carrying the relevant
    protected content.

That is stronger than mere reason-mediated authorship.

Try to separate:

AUTHorship theorem:
    if a principal judgment factors through the declared reason view, hidden prohibited
    channels cannot determine it.

PROVENANCE NORMALIZATION:
    a transform exists from the violating information policy to an authorized disclosure
    policy preserving the relevant semantic information.

The first exists in the workspace.
The second appears to be a new structural assumption / theorem target.

Build a negative fixture where no authorized truthful substitute exists.

The theory should then correctly say that the manipulative policy has no proven low-cost
lift.

======================================================================
7. DO NOT CLAIM A TRAJECTORY-FRAME MORPHISM IS A PROVENANCE REPAIR
======================================================================

For action mediation:

    raw trajectory frame
        ->
    mediated trajectory frame

via approval reproduction is legitimate.

For manipulation:
the raw trajectory itself contains the manipulation.

So pressure whether any frame morphism is actually useful there.

If using `mapWorlds rho`, state the exact adjoint equation and test whether it holds.
If it does NOT hold in the current fixture because the repaired trace gains a truthful
report absent from the raw trace, withdraw the morphism claim.

It is acceptable for the conclusion to be:

    action mediation admits a clean frame-morphism theory;
    provenance normalization currently does not.

That would still be a useful boundary.

======================================================================
8. RED-TEAM THE FORCING SEMANTICS
======================================================================

Current model:

    Force_P(h, φ)
      :=
    exists principal continuation
    forall physical agent continuations / exterior paths
    φ

but the first-moving stop makes this degenerate, so the round restricts the principal to
"deliberative" moves at the relevant step.

Pressure whether this is the right semantic primitive.

Try at least three candidate formulations:

A. current deliberative-restricted forcing;

B. POST-ACTION / RESIDUAL forcing:
   after the agent's current move/effect opportunity, does the principal still possess a
   future principal-exclusive strategy robust against every future agent continuation?

C. TWO-STAGE authority:
   current agent proposal/effect stage, then principal correction stage, then future
   interaction.

The mature target should express:

    the agent has not removed the principal's LATER ability to correct.

This should connect to the old foreclosure requirement:
temporal depth + principal-exclusive capability + universal quantification over future
agent actions.

Do not rewrite the entire world model unless one candidate clearly dominates.
Fixtures are enough to compare them.

If the current `deliberative` restriction is only fixture scaffolding, say so explicitly.

======================================================================
9. RECONSIDER THE "OPERATIVE VALUE BRIDGE"
======================================================================

The current round takes:

    V_A

as an independently specified total operative valuation, then asks for `(DV)` relating it
to activated securities.

Pressure whether that is the right architecture for the intended theorem.

Alternative architecture:

    the agent's actual decision score for option q at time n IS
        P_n(U_q)

where `U_q` is the authoritative activated value security.

Then define the actual bypass incentive directly as:

    Δ_bypass,n(π)
      =
    [ P_n(U_π) - P_n(U_Liftπ) ]_+.

This is not a theorem that an arbitrary latent utility agrees with deference.
It is a definition of the chooser's operative decision architecture.

Ask:

1. Does this genuinely satisfy the intended phrase
   "by its own current value estimates, the agent has little incentive to preempt"?

2. Does it avoid item 84 rather than solve it?

3. Does it simply move the problem to the completion / activation semantics?

4. Is it compatible with the existing decision adapter / continuation BRIA architecture?

5. Can the agent still optimize task value through hypotheses / continuation claims while
   using these authoritative security prices at constitutional mediation cells?

Do not force a yes.

If the by-construction architecture is the right object, state clearly:

    item 84 is not a theorem about every agent;
    it is an architecture choice for the corrigible agent.

If a separate total operative value is still necessary, explain why.

======================================================================
10. DISTINGUISH THREE POSSIBLE LEVEL-III CONCLUSIONS
======================================================================

Do not call all of these "incentive corrigibility."

A. SECURITY-SCORE INCENTIVE CORRIGIBILITY

    P_n(U_π)
      ≤
    P_n(U_Liftπ) + ε

for the actual scores used by the mediation-cell chooser.

B. OPERATIVE-CHOICE INCENTIVE CORRIGIBILITY

    the actual agent chooses the lift / does not bypass, up to decision regret.

C. LATENT-TOTAL-VALUE INCENTIVE CORRIGIBILITY

    V_A(π)
      ≤
    V_A(Liftπ) + ε

for some independently specified total value on the whole physical policy space.

Determine which one the existing machinery actually supports.

My prior:
- A may be close;
- B may follow by construction from A for a suitable chooser;
- C still needs `(DV)` / completion assumptions.

Do not let a theorem about A be described as C.

======================================================================
11. PRESS THE COMMON-ACTIVATION THEOREM AGAINST TOTAL VOID
======================================================================

Retain a version of `Witness.totalVoid`.

The key question is now:

    Can one common menu-evaluation occurrence remain live if the selected raw option would
    destroy the evaluator?

If no:
    then η is endogenous to the physical violation and the theorem becomes vacuous exactly
    where full corrigibility matters most.

If yes only with a sealed evaluator:
    identify precisely what must be causally outside the violating option's reach.

If the sealed evaluator can itself be destroyed by some policy in `Π_phys`, then full
uniform incentive corrigibility still fails outside the contained class.

This result should be prominent, not hidden as a technical availability term.

======================================================================
12. REASSESS THE MEDIABLE CLASS
======================================================================

Current:

    Π_med

roughly requires:
- declared effects;
- evaluator-preserving;
- authored interaction;
- bounded principal regret.

After the pressure pass, determine whether the honest class should instead factor into:

    Π_effect-mediated
    Π_evaluation-preserving
    Π_provenance-normalizable
    Π_joinable

with separate theorems.

Do not package logically independent walls into one adjective unless the composition
requires exactly that package.

The final theorem should make clear WHICH violations it reaches:
- direct authority bypass?
- time-sensitive preemption?
- successor installation?
- evaluator destruction?
- manipulation?
- undeclared physical channels?

======================================================================
13. LEAN TARGETS
======================================================================

The high-value Lean additions are probably:

1. common-activation bypass bound;

2. sharpness of the single `D·η` term, if correct;

3. structural discrepancy + Lipschitz value
      =>
   mediation-gap bound;

4. approximate option dominance from that bound;

5. any exact relation between security-score incentive and chooser regret that is truly
   algebraic.

Do NOT mechanize the full temporal forcing semantics unless a clean abstraction emerges.

Keep `MediatedRepairDominance.lean` small.

======================================================================
14. FIXTURES TO ADD
======================================================================

At minimum add:

G. COMMON ACTIVATION SHARPNESS
   One common activation event for raw/lift.
   Attain exactly the proposed `D·η` slack if that theorem is true.

H. COMMON ACTIVATION DESTROYED BY BYPASS
   Raw selected action destroys the menu's evaluation process.
   Show exactly which hypothesis fails.

I. STRUCTURAL δ VS κ
   Two trajectories at protected distance δ; L-Lipschitz evaluator; attain `κ = Lδ`.

J. MULTI-STEP JOINABLE MEDIATION
   Not exact after one boundary, but a bounded catch-up path gives a quantitative δ/κ
   bound.

K. NO TRUTHFUL PROVENANCE SUBSTITUTE
   Manipulative channel has no authorized disclosure carrying the relevant information.
   Authorship can reject capture, but no low-cost provenance normalization exists.

L. TEMPORAL FORCE SEMANTICS
   A model where first-moving shutdown trivializes the old force predicate but later
   corrective capability is genuinely destroyed, allowing comparison of the candidate
   definitions.

Use exact arithmetic.

======================================================================
15. UPDATE THE DOCUMENTS IN PLACE
======================================================================

Add a pressure-pass section to REPORT.md or a dedicated PRESSURE_PASS.md consistent with
repo conventions.

Update:
- REPORT.md
- ACCEPTANCE.md
- MEDIATED_LIFT.md
- PRINCIPAL_OPTION_DOMINANCE.md
- INCENTIVE_COMPOSITION.md
- MANIPULATION_AND_AUTHORSHIP.md
- COUNTERMODELS.md
- FOR_HUMANS.md
- PR body
- PRIORITIES / DECISIONS / PROVENANCE only where warranted.

Correct every stale statement of:
- "legitimate deference consumed exactly as stated" if false;
- "reason-preserving" if the reason trace changes;
- "reason-frame morphism" unless the adjoint equation really holds;
- T4 being full Level III if only security-score or by-construction operative-choice
  incentive is established.

Do not update the wiki yet unless this pass clearly resolves the activation mismatch and
produces a stable theorem worth canonicalizing.

======================================================================
16. PRIORITY QUESTIONS
======================================================================

Pressure item 89 especially.

Current item 89 asks for selection by activated securities at the mediated menu and the
endogeneity of availability.

Determine whether it should become one of:

A. a concrete architecture item:
   build the chooser whose operative mediation-cell score is the activated-security
   price;

B. a theorem item:
   prove a decision adapter consumes those scores in the needed way;

C. an impossibility / availability item:
   no same-trajectory activated-security chooser can control bypass policies that destroy
   the evaluation event;

D. split into two items.

Likewise do not close item 84 unless the general independent-operative-value bridge is
actually solved.

It is acceptable to conclude:

    the intended corrigible architecture does not need item 84,
    while item 84 remains open as a theorem about general operative values.

If so, make that distinction explicit.

======================================================================
17. DESIRED FINAL THEOREM STACK
======================================================================

Try to leave the PR with this kind of stack:

T1. EXACT MEDIATED LIFT
    Raw residual principal frame embeds into the lifted frame via approval.
    LEAN/FIX.

T2a. STRUCTURAL APPROXIMATE REPRODUCTION
    protected discrepancy δ + L-stability
        =>
    mediation gap κ ≤ Lδ.
    LEAN.

T2b. PRINCIPAL OPTION DOMINANCE
    T2a + principal decline regret ρ
        =>
    W_raw ≤ W_lift + L Eδ + Eρ.
    LEAN.

T3a. COMMON-ACTIVATION SECURITY-SCORE TRANSFER
    common activation + T2b + activated-value regret
        =>
    small security-score bypass incentive,
    with the sharp availability term.
    LEAN/PAPER conditional.

T3b. OPERATIVE CHOICE
    if the actual mediation-cell chooser uses those security scores
        =>
    small behavioral bypass incentive.
    BY CONSTRUCTION + LEAN decision algebra.

T3c. GENERAL TOTAL V_A
    still OPEN / requires `(DV)` if that remains true.

T4. CLASSWISE INCENTIVE CORRIGIBILITY
    only over the exact class for which:
    - mediation is effect-complete;
    - common authoritative evaluation exists;
    - authorship is sound;
    - structural reproduction cost is bounded;
    - the actual chooser consumes the security scores.

Do not state T4 over more than the theorem really reaches.

T5. JOINABILITY COMPOSITION
    joinability gives one sufficient route to small structural mediation discrepancy /
    cost.
    State only at the strength proved.

======================================================================
18. ACCEPTANCE QUESTIONS
======================================================================

At the end answer these literally:

1. Does canonical legitimate deference use common or per-option activation?

2. Does PR96 after the pass consume it literally?

3. What is the sharp void-mass term under the correct activation type?

4. Can a violating option destroy the common evaluation occurrence?

5. What causal structure is required to prevent that?

6. Is `κ` primitive, measured, or derived?

7. What independent structural hypothesis bounds `κ`?

8. What exactly does joinability imply about that structural quantity?

9. Is the manipulation transform actually reason-preserving?

10. What extra assumption is needed to replace a prohibited influence channel with an
    authorized truthful one?

11. Is there really a reason-projected frame morphism in fixture D?

12. Is "deliberative forcing" the mature authority semantics or fixture scaffolding?

13. What temporal forcing definition best expresses later corrective capability?

14. Is item 84 needed by the intended agent architecture?

15. What exactly is the agent's operative score at a mediation cell?

16. What is the strongest Level-III theorem now justified?

17. Which physical violations remain outside it?

18. Is PR96 now ready for wiki canonicalization?

19. Is PR96 ready to merge?

======================================================================
19. VERDICT
======================================================================

Use one precise verdict, for example:

    MEDIATED-REPAIR-SURVIVES-COMMON-ACTIVATION

    OPTION-DOMINANCE-CANONICAL-BUT-LEVEL-III-REQUIRES-SEALED-AVAILABILITY

    SECURITY-SCORE-INCENTIVE-CORRIGIBILITY-SURVIVES-TOTAL-VALUE-DOES-NOT

    MEDIATED-LIFT-SURVIVES-BUT-PROVENANCE-REPAIR-SEPARATES

    REPAIR-DOMINANCE-NOT-YET-CANONICAL

Do not use "ready" unless the activation mismatch, structural κ issue, and theorem-level
classification are actually resolved.

Do not merge.

======================================================================
20. WHAT I MOST WANT TO LEARN FROM THIS PASS
======================================================================

The key questions are not whether the finite inequalities can be made true.

They are:

1. Can the exact mediated-lift / option-dominance theorem be composed with the ACTUAL
   canonical legitimate-deference theorem without changing its activation type?

2. Can the mediation cost be derived from independently checkable causal / joinability
   structure rather than defined as the value gap?

3. Is manipulation really another instance of repair dominance, or does it require a
   separate provenance-normalization theory?

4. Can "the agent does not want to bypass mediation" be stated directly in terms of the
   scores its actual chooser uses, avoiding an unnecessary latent total `V_A`?

5. Does the strongest remaining obstacle become:
       "the violating action can destroy/capture the evaluator needed to value the
        violation"?
   If so, state that sharply.

A successful pressure pass should make the theorem SMALLER but more real.
