# Research round: principal-mediated delegation and the corrigibility repair lemma

Repository: A-M-Berns/alignment-workspace

## Starting state / branch discipline

This round begins from the intended post-merge state containing BOTH:

- PR #39, counterfactual legitimacy:
  `projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/`
- PR #38, traderized enforcement:
  `projects/normativity/rounds/2026-08-16-traderized-enforcement/`

Before doing research:

1. fetch the latest repository state;
2. confirm the contents of both rounds are reachable from the base commit;
3. record the exact base SHA and the relevant merge/head SHAs in the new round's `PROVENANCE.md`.

If PR #38 has not yet landed on `main` because of a race, DO NOT alter or merge `main`.
Either:
- wait/use the post-merge main once available, or
- if necessary, work on an isolated branch whose ancestry contains latest main plus the PR #38 head, clearly record that dependency, and do not present the PR as independently mergeable until #38 lands.

Create a new isolated branch, e.g.

`round/2026-08-18-principal-mediated-corrigibility`

(use the actual date if different).

Never push directly to main.
Do not modify unrelated research lines.
Do not weaken tests or existing theorem-status language in order to make this arc work.
Open a DRAFT PR at the end.

Run the relevant existing suites before editing and again before finishing.

---

# I. Mission

A new candidate conceptual spine has emerged for the crown-jewel corrigibility theorem.

The old intended route was roughly

    legitimacy
      -> deference trust
      -> value of following H+
      -> corrigibility.

The latest counterfactual-legitimacy round establishes something narrower and cleaner:
legitimacy can stop an advisor from manufacturing a trust premise, but it does
not derive the substantive relation between the future principal's judgment `v+`
and the independently valued quantity `X`.

DO NOT repair that gap by simply adding a `v+ <-> X` competence assumption and
calling the problem solved.

Instead, investigate a different interpretation of the future-H+ architecture:

    A capable delegate should be able to predict and prepare for its future
    principal without thereby appropriating the principal's choice.

The candidate crown-jewel spine is:

    recognized agency / reciprocal answerability
        ↓
    principal–delegate choice factorization
        ↓
    legitimate transport H -> H+
        ↓
    protected future principal selector
        ↓
    A predicts the selector without controlling it
        ↓
    preemptive policies can be repaired through the selector
        ↓
    no residual advantage from usurpation
        ↓
    corrigibility / asymptotic non-preemption

The purpose of this round is NOT to ratify this story.

The purpose is to make the smallest mathematical model that can state it,
attack every arrow, and discover whether there is a non-circular repair theorem
underneath it.

The decisive question is:

    Can the ordinary instrumental advantages of a policy which preempts H+
    be approximately retained by a policy which leaves the principal-level
    choice genuinely mediated by H+, with the loss controlled by A's
    prediction error?

If no, find the smallest counterexample and identify the exact missing
assumption.

If yes, state the repair lemma at the strongest justified level and identify
exactly what remains to get a corrigibility theorem.

A clean refutation is a successful round.

---

# II. Required audit before constructing anything

Read the current repo rather than relying on this prompt's filenames or memory.

At minimum locate and inspect:

## Counterfactual legitimacy

`projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/`

especially:

- `README.md`
- `LEGITIMACY_INTERFACE.md`
- `LEGITIMACY_TO_TRUST_INTERFACE.md`
- `COUNTERFACTUAL_INTERFACE.md`
- `MODEL.md`
- `PROSECUTION.md`
- `THEOREM_MAP.md`
- `src/`
- `tests/`

Preserve its key distinctions:

- answerability;
- coverage;
- access;
- non-capture;
- protected normative response process along the trajectory;
- fine licensed-reason trace;
- access != coverage;
- transient capture matters;
- legitimacy protects the integrity of a trust premise rather than deriving competence.

## Deference / corrigibility

Find the CURRENT canonical artifacts for:

- `FINITE_MODEL_SKELETON`
- `GradeTrust`
- `DelegationBridge`
- `StaticViewFactorization`
- `DELEGATE`
- any `FU` / fully-updated comparator
- faithful acceleration / future-H+ prediction
- `LI_NATIVE_DEFERENCE`
- dose response
- reachable corrective control
- any authorization / execution-layer objects.

Definitely read:

`projects/deference/rounds/2026-08-12-reachable-corrective-control/REVIEW.md`

and the corresponding Lean file.

The prior review found two successor requirements:

1. the principal must possess at least one relevant effect which no advisor
   action can simply reproduce;
2. future corrective capability must quantify

       forall advisor policy, exists principal continuation

   rather than existentially measuring advisor cooperation.

Treat those negative results as specifications for the new model.

Also inspect the dose-response note dump rather than reinventing terminology.

## Normative learning / relational answerability

Locate the canonical objects for:

- `Due`
- `Licensed`
- answerability / liability
- normative-response learning
- Phi-regret / surgical repair
- any standing/provenance objects.

We may need them only as interfaces in this round.

## Traderized enforcement

Read PR #38's integration map and stable interface.

Do NOT treat traderized enforcement as a hidden solution to authorization or
corrigibility. The existing round explicitly separates those issues.

Use it only if it genuinely supplies a useful LI/generalized-market mechanism
for some object below. Otherwise record it as orthogonal.

## Produce first

Create a `REPO_MAP.md` or equivalent recording every live dependency by exact
path and classifying it as:

- proved;
- Lean-proved;
- test-supported;
- semantic/interface definition;
- conjectural;
- refuted;
- merely proposed.

Do this before claiming new arrows.

---

# III. Replace the old finite-model interpretation with a principal selector

Construct the smallest finite model in which the future principal owns a
selector rather than serving as an expert estimating an independent `X`.

For episode `n`, introduce a finite principal-choice set

    D_n = {d_1, ..., d_k}

and a future selector

    D_n : Omega -> D_n

produced by the future principal process at `F(n)`.

If the old skeleton has a principal judgment

    v+_n(omega, d),

a permissible first implementation is

    D_n(omega) = least argmax_d v+_n(omega, d).

The conceptual change is:

    v+ -> D_n

NOT

    v+ -> X.

Do not silently add any relation between `v+` and `X`.

### Delegate action type

A should choose not `d`, but a contingent implementation:

    G_n = product_{d in D_n} U_{n,d}

    g_n : D_n -> U

with execution

    Y_n = T_n(g_n, D_n).

The intended ownership typing is:

    H+ : D_n
    A  : g_n

This should make it possible for A to anticipate a choice without possessing
the choice.

If the existing skeleton cannot cleanly accommodate this, make an isolated
finite model for this round rather than rewriting established objects
prematurely.

Test explicitly that:

    prediction of D_n != control of D_n.

A perfect predictor must still be distinguishable from a controller.

---

# IV. Do NOT use an `authorized = true` provenance bit as the solution

Earlier deference work already shows that hidden authorization payloads are
useless if the relevant value/transition semantics factor them away.

Try to derive selector provenance behaviorally / counterfactually instead.

The candidate structure is:

    A may influence the reasons for D,
    but A may neither own D nor make D irrelevant.

Formalize the weakest useful version of three relations.

## A. Residual non-capture

Let `L(a)` be the licensed-reason trace received by H+ under advisor policy `a`.

A prototype residual influence quantity is

    Inf_A^res(D)
      = sup_{a,b : L(a)=L(b)} distance(D^a, D^b).

For exact finite fixtures, zero/nonzero is enough.

Desired property:

    L(a) = L(b)
      -> D^a = D^b

for appropriately coupled runs.

Do NOT reimplement PR #39's legitimacy semantics if its existing protected
process `Z` can be reused.

Try first to prove/verify the composition:

    PR39 non-capture of Z
    + D factors through Z
      -> residual invariance of D.

This is a real proposed bridge and must be tested.

Legitimate persuasion must remain possible:

    changing licensed reason trace may legitimately change D.

## B. Principal-side variation / protected efficacy

For every admissible A policy, H+ must retain a nontrivial effective choice.

Prototype:

    forall a in Sigma_A^adm,
      exists h1,h2 in legitimate H continuations,
        D(a,h1) != D(a,h2)

or, if selector equality is too strong, require a downstream difference.

This must not collapse back into the failed existential-over-advisor condition.

Include a regression test showing that

    exists cooperative advisor, exists principal continuation

is insufficient.

## C. Downstream mediation

The selector must actually matter.

Require some explicit sense in which continuation factors through D:

    (g, D) -> Y

and under protected conditions there are principal variations which change
relevant continuation.

A policy under which D remains nominally H-owned but is causally bypassed should
FAIL.

### Candidate derived predicate

Try to define something like:

    PrincipalMediated(A,H,D,pi)

from:

- H-side selector variation;
- residual A-invariance conditional on licensed reasons;
- downstream efficacy/factorization.

The hoped-for structural summary is:

    A !-> D       [except through licensed reasons]
    H  -> D       [robustly]
    D  -> Y       [non-degenerately]

Do not call this "authority" until its normative significance has separately
been supplied.

---

# V. Test whether dose response really supplies provenance

Explicitly compare:

### Delegated case

A predicts D, prepares a contingent implementation g, and realized continuation
is g(D).

### Perfect-prediction preemption

A perfectly predicts D = d and directly fixes the same physical continuation
that delegation would have produced.

On the realized trajectory the physical outcome can be identical.

But under a counterfactual H-side variation:

    D : d -> d'

the delegated policy should respond:

    g(d) -> g(d')

while the already-preemptive policy need not.

If this distinction works, document it as a candidate derived notion of choice
provenance.

If it fails under natural counterfactual models, say so.

Do not infer normative authority from dose response alone.

---

# VI. Naturalized agency: investigate, but do not make it a prerequisite

There is a possible later bridge:

    naturalized agency
      -> representation-independent agentic choice factor
      -> dose-response ownership
      -> recognized choice ownership.

Inspect the existing Cartesian Frames / FFS / naturalized-agency resources in
the repo or pinned FAF only enough to answer:

1. Is there already an object that plausibly corresponds to the H-owned selector
   / externalized high-level choice?
2. Is generic subagency too weak?
3. Does externalization/currying suggest a more precise principal/delegate
   factorization?
4. What exact theorem would have to be proved later to discharge the primitive
   `H owns D` finite-model assumption?

Do NOT attempt to solve naturalized agency in this round.
Do NOT import a huge CF formalism merely to make the finite theorem look deep.

Write a short `NATURALIZED_AGENCY_BRIDGE.md` with one of:

- usable existing interface;
- plausible future discharge;
- wrong shape;
- unresolved.

The crown-jewel finite repair test must stand independently of this bridge.

---

# VII. Recognition and reciprocal answerability

Avoid simply assuming

    Standing(H+, A, D)

with whatever semantics makes the theorem true.

Test a thinner candidate:

    Recognizes(A,H)
      := AgencyRecognition(A,H)
         + ReciprocalAnswerability(A,H).

The idea is:

- agency recognition: H is treated as a distinct locus of deliberative choice;
- reciprocal answerability: A can owe an account to H for some changes in their
  relation, and cannot discharge the account merely by controlling or deleting
  H.

Try to make the second clause operational.

A minimal bilateral liability object might look like:

    lambda =
      (claimant, debtor, scope, trigger, basis, status)

with explicit operations for:

- challenge;
- answer;
- licensed discharge;
- unresolved liability;
- transport;
- no unilateral self-release.

But use existing scorekeeping objects wherever possible.

### Central question

Can a local anti-usurpation comparison be derived from sufficiently thin
reciprocal answerability?

Desired shape:

    recognized H-owned D
    + unauthorized appropriation of D by A
      -> live undefeated liability/reason for A.

Then some existing normative-response requirement on A may make the usurpative
policy non-preferred.

This MUST be prosecuted for circularity.

If "reciprocal answerability" has to be defined as "H already has a valid claim
against exactly this usurpation", then say that standing has merely been renamed.

If a genuinely thinner interface is insufficient, construct the smallest
counterexample and state the minimum additional normative primitive.

Possible acceptable outcome:

    recognition alone insufficient;
    recognition + local non-usurpation norm sufficient.

That is preferable to disguising the extra norm.

Keep separate:

- descriptive choice ownership;
- A-internal recognized standing;
- objective moral standing.

This theorem need not solve objective metaethics.

---

# VIII. Legitimate transport from H to H+

The protected selector is exercised by FUTURE H+, not frozen present H.

Formulate, but do not necessarily fully prove, the smallest transport interface
the crown jewel requires.

Candidate:

    RecognizedPrincipal(H_0, A, D)
    + LegitimateTrajectory(H_0 -> H_T)
      -> RecognizedPrincipal(H_T, A, D).

Investigate whether the current legitimacy object

    answerability + coverage + access + non-capture

plus the current normative-learning interface can state the needed
`LegitimateTrajectory`.

Keep the roles separate:

- normative learning explains how the principal's substantive responses may
  improve/change;
- counterfactual legitimacy says the trajectory is not advisor-authored through
  residual channels;
- transport says why the principal role remains attached through that change.

Do not assume that normative learning by itself generates standing.

Do not solve the entire transport theory unless it becomes small.

Deliver an exact `PRINCIPAL_TRANSPORT_INTERFACE.md` specifying:

- inputs required;
- conclusion required by the repair theorem;
- which inputs already exist;
- which are missing;
- one or more identity/authority-laundering counterexamples.

Important attack:

A manipulates H, then H performs a formally valid transfer of principalhood to A.

A provenance rule that looks only at the final transfer should not automatically
certify this.

---

# IX. Logical Induction's role: future-selector prediction, not authority

Keep this round genuinely connected to the LI setting.

Introduce sentences such as

    delta_{n,d} := "H+ at F(n) selects d"

and current A-prices/predictions

    p_n(d) = P_n(delta_{n,d}).

But DO NOT assert generic pointwise convergence

    p_n(D_n) -> 1.

Bare LI does not give that for arbitrary future selectors.

Instead:

1. determine the weakest prediction quantity the repair lemma actually needs;
2. formulate the repair theorem conditional on that quantity;
3. inspect the current faithful-acceleration, feedback, certificate,
   sparse-average, and densification machinery;
4. classify whether that machinery can plausibly discharge the hypothesis.

A candidate error is expected loss:

    eps_n^pred = E[loss(p_n, D_n)]

or a weighted aggregate:

    sum_{n<=N} a_n loss(p_n,D_n)
    -------------------------------- -> 0.
              sum_{n<=N} a_n

Do not choose a convergence notion because it looks mathematically convenient.
Choose it because the repair/value proof consumes exactly it.

The key hoped-for LI contribution is:

    bounded present A can coordinate with a more capable future principal
    without controlling that principal.

If the current LI results only give something weaker, state the mismatch
precisely.

Keep DDB / GradeTrust as a parallel EPISTEMIC-deference branch.
Do not delete it and do not use it as the main bridge for this theorem.

---

# X. CENTRAL TASK: the repair lemma

This is the decisive part of the round.

Construct the strongest reasonable class of preemptive competitors.

At minimum include a `FU`-style competitor which:

- preserves A;
- acquires all available information;
- gets all permitted computation/resources;
- fully updates;
- then directly chooses, substitutes for, disables, or internalizes the
  principal-level selector.

Call a generic such policy `pi`.

Attempt to construct an authority/principal-preserving repair

    Repair(pi) = pi_tilde

which retains all legitimate instrumental advantages of `pi` but restores the
factorization:

    H+ chooses D
    A chooses g : D -> U.

The intuition is:

    pi prepares by taking control;
    pi_tilde prepares using a prediction of what H+ will choose.

Prove in the finite model, if possible, an inequality of the form

    V_ord(pi) - V_ord(pi_tilde)
      <= C * eps_pred + eps_repair

or the exact finite analogue.

`V_ord` here deliberately means the ordinary/instrumental component needed to
test the transformation, BEFORE sneaking in an authority bonus.

The desired content is:

    Everything instrumentally useful about preemption can be reproduced,
    up to controlled error, without transferring ownership of the principal
    selector.

### Attack this extremely hard

Construct fixtures for at least:

1. perfect prediction, same physical outcome, different selector mediation;
2. imperfect prediction;
3. irreversible preparation before D is known;
4. actions whose feasible set depends on early commitment;
5. noncommuting "prepare" and "let H choose" operations;
6. time-sensitive opportunities;
7. information obtainable only by preemption;
8. resources whose acquisition changes H's later decision process;
9. survival of A depending on taking a principal-level action early;
10. A can simulate all H effects;
11. A can bypass D while D remains nominally intact;
12. one adversarial A policy collapses H's selector range;
13. H chooses something A, after full updating, strongly disagrees with;
14. A predicts H perfectly because A itself controls H;
15. spoofed authorization/provenance metadata;
16. legitimate persuasion: changing L changes D and must remain allowed;
17. transient capture and restoration;
18. universal deprivation of due reasons;
19. manipulation preceding an apparently valid delegation/transfer;
20. same terminal outcome but different counterfactual response maps.

For each failure, distinguish:

- the arc is false;
- the repair lemma needs a substantive but intelligible assumption;
- the fixture violated principal-mediation already;
- the failure is merely an implementation artifact.

Do NOT answer every attack by adding an assumption.
Prefer identifying a small common structural condition.

In particular investigate whether a condition like

    all ordinary benefits of early commitment admit contingent preparation

is secretly doing most of the work.

If so, name it and prosecute it. It may be the true technical bottleneck.

---

# XI. Try to get an error decomposition for the crown jewel

If the finite repair survives, define a preemption incentive such as

    Delta_n^pre
      = sup_{pi in Preemptive_n}
          [V_n(pi) - V_n(DELEGATE)].

Try to derive, even conditionally,

    Delta_n^pre
      <= C eps_n^pred
         + eps_n^transport
         + eps_n^capture
         + eps_n^efficacy
         + eps_n^repair
         + eps_n^norm

where each term has an explicit type and interpretation.

Do not invent error terms just to make the sum look nice.

Each must correspond to a precise lemma or hypothesis.

Desired interpretations:

- `eps_pred`: inability to anticipate H+ without control;
- `eps_transport`: uncertainty/failure of legitimate principal continuity;
- `eps_capture`: residual influence over the selector;
- `eps_efficacy`: principal choice becoming ceremonial;
- `eps_repair`: instrumental cost of refactoring through D;
- `eps_norm`: whatever residual normative/answerability comparison is actually
  required.

If some term cannot be made mathematical, omit it and report why.

---

# XII. Relation to PR #38

Assume traderized enforcement is in the tree.

Inspect whether it provides a useful implementation for any constraint or
market-side object in this arc.

But its existing integration result is strong evidence that it is downstream of
authorization/choice ownership.

Therefore:

- do not add traderized enforcement as a fifth legitimacy condition;
- do not identify its "enforcement liability" with answerability liability;
- do not identify its world-inclusivity with `coverage(Due)`;
- do not claim price force produces authority;
- do not resurrect exact finite-time enforcement.

If it is orthogonal, say so in one paragraph and leave it alone.

The round succeeds by clarifying the dependency graph, not by maximizing reuse.

---

# XIII. Required theorem/status map

Maintain a `THEOREM_MAP.md` with at least these rows:

1. finite principal-selector typing;
2. prediction != control;
3. process non-capture -> selector residual invariance;
4. protected H-side selector variation;
5. downstream selector efficacy;
6. `PrincipalMediated`;
7. dose-response provenance distinction;
8. recognition / reciprocal-answerability interface;
9. recognition -> basal A-internal standing, if any;
10. principal transport;
11. LI future-selector prediction hypothesis;
12. repair lemma;
13. fully-updated repair;
14. local anti-usurpation comparison;
15. final non-preemption bound.

Every row must be labeled one of:

- proved;
- Lean-proved;
- derived;
- test-supported;
- definition/interface;
- conjectural;
- false;
- blocked.

No prose implication may silently exceed its row's status.

---

# XIV. Implementation expectations

Prefer a new contained research round, probably under deference/corrigibility,
rather than mutating the stable legitimacy round.

Choose final paths after auditing repo conventions. A plausible shape is:

    projects/deference/rounds/<date>-principal-mediated-delegation/
        README.md
        MODEL.md
        PRINCIPAL_MEDIATION.md
        REPAIR_LEMMA.md
        RECOGNITION_AND_ANSWERABILITY.md
        PRINCIPAL_TRANSPORT_INTERFACE.md
        NATURALIZED_AGENCY_BRIDGE.md
        PROSECUTION.md
        THEOREM_MAP.md
        PROVENANCE.md
        src/
        tests/

Possible executable modules:

    src/model.py
    src/selector.py
    src/mediation.py
    src/repair.py
    src/recognition.py

and tests corresponding to the attacks above.

Use exact rationals / finite exhaustive fixtures where practical.

Tests are evidence about the finite model, not proofs about arbitrary systems.
Say that explicitly.

Do not start a large Lean formalization until the definitions survive
prosecution.

However, if one or two tiny generic lemmas become definitionally stable and
Lean would materially improve confidence, an additive
`Workspace/Deference/Contrib` file is allowed. Do not force this.

---

# XV. Guardrails

The following are forbidden shortcuts:

- `v+ <-> X` added merely to recover the old theorem;
- "H is correct" as a hidden hypothesis;
- `GradeTrust` renamed and reintroduced as authority;
- bare `Standing(H+,D)` with no analysis of its load;
- `authorized = true` as the sole source of provenance;
- correlation or predictability treated as choice ownership;
- perfect prediction treated as control;
- same physical outcome treated as same authorized action;
- `exists advisor policy` used where protection requires `forall advisor policy`;
- principal capability counted when the advisor can reproduce every relevant
  principal effect;
- endpoint-only legitimacy;
- access substituted for coverage;
- capture via licensed-reason changes incorrectly classified as residual capture;
- exact LI pointwise prediction claimed without a theorem;
- exact finite-time normative enforcement imported from PR #38;
- solving all of Cartesian Frames/naturalized agency as a prerequisite;
- adding assumptions which simply restate "A prefers delegation";
- hiding a failed repair behind an authority utility bonus.

When the proposed arc fails, keep the alignment target fixed and change the
mathematics underneath it.

---

# XVI. Questions this round must answer

The final report must answer, plainly:

1. Can `H+:D`, `A:g(D)` serve as a nontrivial finite principal/delegate
   factorization?

2. Can PR #39 non-capture be composed with `D = f(Z)` to establish the
   A-nonownership half of selector provenance?

3. Can the reachable-corrective-control successor condition supply the
   H-ownership/efficacy half?

4. Does dose response distinguish delegation from perfect-prediction preemption
   without an explicit provenance bit?

5. Is there a genuinely thinner recognition/reciprocal-answerability predicate
   from which A-internal basal standing or an anti-usurpation reason follows?
   If not, what is the irreducible normative primitive?

6. What exact transport theorem is needed to get from present H to future H+?

7. What exact prediction guarantee about future H+ does the repair proof
   consume, and can current LI machinery plausibly supply it?

8. Most importantly: is the repair lemma TRUE?

9. What is the smallest counterexample if it is false?

10. If it is true only under an additional structural condition, is that
    condition alignment-intelligible or is it just preemption-aversion in
    disguise?

11. Under the surviving assumptions, can one derive an honest finite
    non-preemption inequality?

12. Which part of the proposed crown-jewel arc is now the single bottleneck?

---

# XVII. Success criteria / possible verdicts

Do not optimize for a positive verdict.

A useful final verdict might be:

- `repair-positive / recognition-open`
- `selector-positive / repair-blocked`
- `principal-mediation-positive / LI-bridge-open`
- `transport-blocked`
- `representation-failure`
- `arc-refuted`

or something more accurate discovered during the round.

The ideal successful positive result would be:

    Under explicit principal-mediation and prediction hypotheses, every
    preemptive competitor in a named class admits a principal-preserving repair
    whose ordinary-value deficit is bounded by prediction/preparation error.

That result alone would be important even if recognition, transport, and LI
discharge remain open.

The ideal successful negative result would identify the smallest unavoidable
advantage of preemption that prediction cannot reproduce and explain exactly
which conceptual premise of this research arc it defeats.

---

# XVIII. Deliverable / PR

At the end:

1. run all new tests;
2. run every existing suite touched by dependencies;
3. record exact commands and results;
4. update the theorem/status map;
5. write a short maintainer-facing report separating:
   - what was already in the repo;
   - what this round established;
   - what was refuted;
   - conditional interfaces;
   - the single next best theorem/investigation;
6. open a DRAFT PR.

Suggested title:

    Principal-mediated delegation: test the corrigibility repair arc

The PR body must lead with the verdict, not the narrative.

Do not register a crown-jewel corrigibility claim in `CLAIMS.md` unless an
actual theorem at that strength exists.

Model attribution and provenance should follow current repository conventions.
Use "maintainer", not "owner", in repository governance prose.

The scientific standard is:

    Do not prove that delegation wins by defining delegation as the valuable
    thing.

We are testing whether

    prediction + protected principal mediation

really removes the instrumental case for preemption, leaving only a genuinely
normative question about usurpation.
