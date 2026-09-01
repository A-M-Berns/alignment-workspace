# Report: faithful semantic preservation and grounded slice admission

## Result

All three attacks survive, with local repairs that preserve the architecture.

First, PR73's original induction has a real gap: settled outstanding evolution
does not constrain the load of a persistent issue. Generalized Transfer must
cover every semantic mutation, including in-place edits, with an identity frame
for carriers outside the affected batch. PR73's live theorem statement is
amended accordingly. No Continuity change is needed.

Second, authentication soundness relative to a denotation is insufficient for
the strong No Semantic Laundering claim. A join-preserving map can collapse a
slice-relevant distinction. The weakest reusable strong condition is order
reflection on admissible carrier representations modulo a domain-supplied
slice-relative equivalence. Equality reflection suffices only for exact
translation. Global injectivity is unnecessary.

Third, semantic authentication of a new slice and normative grounding of its
admission are independent. Existing Due and Grounded Replay can realize the
standing-authorizer lineage, but they do not derive the domain evidence or
semantic meaning of every admission. No Groundless Accretion is an interface
condition above that machinery.

## Answers

1. **Does PR73 fail under in-place mutation?** Yes. A persistent issue can
   change \(a\to0\) while every original resolution-batch premise is vacuous.
2. **Minimal repair?** One generalized affected batch per transition and slice,
   plus an identity frame outside it.
3. **Must Transfer cover every semantic change?** Yes, including changes on
   structurally persistent carriers.
4. **Explicit semantic identity?** Identity is the default frame condition and
   may be reified as a trivial certificate for composition.
5. **Does repaired conservation survive?** Yes by a finite-prefix partition and
   substitution induction.
6. **Is soundness alone sufficient for laundering?** No.
7. **Can a join-preserving anchored map be lossy?** Yes; mapping a relevant
   token to bottom hides both strengthening and weakening.
8. **Global injectivity?** Not necessary.
9. **Weakest useful faithfulness?** An order embedding of admissible
   representations modulo anchored slice-relative equivalence.
10. **Is equality reflection enough?** For exact translation only.
11. **Is order reflection required?** For the strong weakening/strengthening
    classification, yes.
12. **Only admissible representations?** Yes. This avoids freezing irrelevant
    or unreachable ontology.
13. **Does faithfulness compose?** Yes with compatible relevance quotients,
    targets, contexts, and a shared anchored domain.
14. **Can repeated revisions erode meaning?** They can if local quotients drift
    or maps are merely sound.
15. **Does the stable codomain prevent erosion?** Only together with anchored
    quotient compatibility and order reflection.
16. **Coverage distinctions?** Target, applicability, scope, unresolved and
    registration status, route quality, and qualifying registration conditions.
17. **Reason distinctions?** Provenance, target/content, answer mode,
    unresolved status, and adequate-answer criterion.
18. **Authentication versus grounding?** Distinct and jointly necessary.
19. **What grounds a slice?** Domain origin evidence acted on by a currently
    standing permitted authorizer with strict-prefix lineage.
20. **Can Legitimate Evolution / Due supply it?** They supply a clean
    realization of authorizer ancestry and rising-edge representation, not the
    entire domain or semantic certificate.
21. **Evaluator declaration alone?** No.
22. **Continuity surgery?** None.
23. **Seed-quality assumptions?** Genesis standing, adequacy of relevance
    quotients, checker soundness, admission-rule validity/completeness, and
    authenticated revision of those rules.
24. **Strongest justified laundering theorem?** Repaired slice conservation
    plus sound, order-reflecting authentication and grounded admission prevents
    carrier, semantic, and provenance laundering modulo explicitly anchored
    slice irrelevance.

## Theorem dependency

    grounded origin + authenticated meaning        [domain / seed interface]
                         |
                         v
    faithful admissible quotient into L_alpha      [semantic adequacy]
                         |
                         v
    generalized Transfer for every mutation
    + identity frame outside affected batch        [local accounting]
                         |
                         v
    outstanding evolution / birth / ancestry       [settled Continuity]
                         |
                         v
    repaired Slice-wise Conservation               [finite-prefix induction]
                         |
                         v
    No Semantic Laundering + No Groundless Accretion

Progress/fairness, liability, and eventual response are not used.

## Verification

Run:

    python3 tests/run.py

The runner executes 22 exact finite hostile cases. It checks the three laundering
counterexamples, accepted repairs, noninjective faithful quotients, failed
order reflection, bridge compatibility, cumulative erosion, grounded and
ungrounded admissions, and independent Coverage/Reason instances. These are
test-supported unregistered paper results, not registered claims.

## Provisional names

Provisional names introduced: **generalized Transfer**, **identity frame**,
**slice-relative faithfulness**, **authentication adequacy**, **grounded
admission**, and **No Groundless Accretion**.

## Deviations

No Lean was added because the repaired hypothesis is semantic and requires no
new Continuity field. The round amended PR73's open theorem and report rather
than leaving the known counterexample only in a follow-up. The prompt record
compresses repeated displays and framing while preserving every numbered
requirement, hostile case, deliverable, question, and verdict option.

## What is not shown

The round does not prove that the chosen relevance preorder is morally
adequate, that admission rules discover all valid new obligations, or that a
response eventually occurs. It does not derive domain evidence, seed standing,
or checker correctness from the calculus. Infinite traces are covered only
prefix by prefix. No result is registered.

## Outstanding maintainer actions

None.

IN-PLACE-REPAIR-LOCAL

SLICE-RELATIVE-FAITHFULNESS-SUFFICES

FULL-INJECTIVITY-TOO-STRONG

ADMISSION-GROUNDING-SEPARATE-FROM-SEMANTICS

### PR73-CONSERVATION-NEEDS-IN-PLACE-MUTATION-REPAIR
