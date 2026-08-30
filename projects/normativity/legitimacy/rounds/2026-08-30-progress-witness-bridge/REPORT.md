# Progress witness bridge — report

Status: research report; unregistered; not frozen or settled. PR69 remains the upstream
checkpoint and its architecture is unchanged.

## Executive result

The witness bridge closes in a deliberately restricted but nontrivial fragment.
`SW-density` decomposes into:

\[
\boxed{
\text{Persistent Relevance}
+\text{Typed Witness Completeness}
+\text{Stagnation Persistence}.}
\]

For a fixed finite service alphabet and an enabled typed reason whose payload is
`v(y)-v(x)>=gamma>0`, a sound nonempty compiler and complete pairwise repair family
prove Typed Witness Completeness:

\[
g_n(rho_{x\to y})\ge\gamma p_n(x).
\]

If service keeps exposing that surface and the designated defective response retains
positive service density, the fixed pairwise repair satisfies all of `SW-density`.
PR69 Uptake then rules out that stagnant tail.

The conceptual advance is real: inquiry, defeater assessment, conflict handling, and
evaluator revision can use exactly the same theorem because the compared objects are
service responses, not external actions. The qualification is also real: each case
needs a typed, licensed answer-mode comparison. A bare unanswered question or conflict
does not entail one.

## The new theorem

The Restricted Stagnant-Tail Witness Lemma in `WITNESS_BRIDGE.md` assumes:

1. fixed finite `X`, stable episode/surface, and fixed `x,y`;
2. one enabled, undefeated `ServiceCompare(x,y,gamma)` occurrence on the tail;
3. a sound compiler exposing its row in nonempty `K_n`;
4. the pairwise repair `x->y` in the fixed repair family;
5. Persistent Relevance, hence `W_N->infinity`;
6. behavior-only stagnation `limsup D_N/W_N>0`, with `d_n=p_n(x)`.

It derives Sensitivity pointwise and therefore all of `SW-density`. Composed with PR69,

\[
\boxed{
\text{Continuity service}
+\text{restricted typed reason semantics}
+\text{Persistent Relevance}
+\text{Uptake}
\Longrightarrow
\text{No Persistent Stagnation}.}
\]

This is not a restatement of SW-density: the positive-gain repair and Sensitivity are
derived from reason semantics and repair expressivity. Relevance and positive defect
density remain separately visible premises.

## Answers to the final questions

### 1. Can `SW-density` be decomposed cleanly?

Yes. `W_N->infinity` is engagement, `g_n>=gamma d_n` is typed dominance plus repair
expressivity, and positive `limsup D_N/W_N` is behavioral defect persistence. They have
independent countermodels and different realization owners. The single name can remain
as a convenient bundled conclusion, but it should no longer be the primitive bridge.

### 2. Does unbounded Continuity service imply relevant engagement under a plausible condition?

Yes. Persistent Relevance or the stronger Surface Fairness condition connects them. In
the fixed-alphabet fragment, the reason's surface is exposed on every service date, so
`c_n=1` and `W_N=A_N` on the tail. In a richer interface this is a fairness/conformance
obligation; Continuity alone cannot rule out attention theater.

### 3. Can action-directed reasons yield a provable repair witness?

Yes, when their typed semantic content supplies a strict rational comparison over
available service/action labels. The pairwise gain calculation proves the witness for
every admissible valuation, not merely sampled values.

### 4. Can inquiry-directed reasons be represented as robustly preferred service moves?

Yes, when a represented inquiry-duty schema ranks `investigate` over a type-specific
`ignore` response. The proof is identical to the action case and asserts no ordering of
external acts. A bare question without that procedural comparison does not compile and
correctly leaves the theorem silent.

### 5. What is the weakest non-circular semantic notion of unansweredness?

In the restricted fragment: the reason remains enabled/applicable/undefeated; no
recognized defeat, discharge, or translation event disposes it; and its designated
nonresponse does not vanish on exposed service mass. The last clause is behavioral and
mentions neither gain nor a repair. Event-only unansweredness is too weak because
behavior may take the reason up asymptotically while the issue stays live.

Persistent Relevance stays outside the definition so a service implementation cannot
hide irrelevance by declaring that the reason was never “engaged.”

### 6. Can a restricted Stagnant-Tail Witness Lemma be proved?

Yes. `WITNESS_BRIDGE.md` gives exact hypotheses and a two-line pointwise proof. The
pairwise map moves mass `p_n(x)` from `x` to `y`, so its gain at every `v in K_n` is
`p_n(x)(v(y)-v(x))>=gamma p_n(x)`. Infimizing proves Sensitivity; the other decomposed
bridges provide the remaining SW clauses.

### 7. What prevents generalization to arbitrary reasons?

Arbitrary reason targets may be evidence, questions, incompatibilities, expressive
demands, or several incomparable answer modes. They need not contain a strict comparison.
Conflicts can make `K_n` empty; local reasons may dominate only on an unselected face;
general affine rows may not be realizable by a feasible distribution repair; and a
recognized answer may be unavailable. These are semantic/compiler obstacles, not regret
obstacles.

### 8. Does the service-response ontology substantially reduce witness completeness?

Yes. It moves inquiry, defeater, conflict-procedure, and revision reasons into the same
finite pairwise theorem without claiming a better external action. The remaining bridge
is Answer-Mode Adequacy: an answerable reason type must register a feasible response and,
when nonresponse is defective, a licensed strict comparison favoring it. This is much
narrower than deriving a utility order from arbitrary normativity, but remains a genuine
normative condition.

### 9. Is infinite explicit revision still the main diachronic loophole?

Yes for the stronger cross-era theory. A cheap Reason Carry condition prevents an
unresolved burden from disappearing at succession unless explicitly disposed or
translated. It does not ensure that translations preserve one alphabet, margin, or
repair. Endless surface-changing successor churn therefore remains outside the fixed
witness theorem and basic Progress.

### 10. Does Grounded Replay acquire a genuine consumer?

Yes. Operative Constraint Grounding requires every compiled normative row to carry a
license occurrence in historical `Adm_n`. Settled historical Grounded Replay then gives
that license a finite authorization tree. The resulting Operative Row Grounding theorem
authenticates every row's authority ancestry. It is an interpretation/legitimacy theorem
for the realization, not a premise of the gain algebra.

### 11. What exact theorem should the next formal pass target?

Formalize a small `ServiceCompare` fragment, not the whole Progress layer:

> **`restrictedStagnantTailWitness`.** For finite `X`, nonempty `K_n`, fixed distinct
> `x,y`, positive `gamma`, a compiler invariant
> `forall v in K_n, gamma <= v(y)-v(x)`, and pairwise repair `x->y`, prove
> `gamma*p_n(x) <= robustGain(K_n,Phi_(x->y),p_n)` at every tail date. Package this
> with a separate `surfaceFairness_tendsto` lemma deriving `W_N->infinity` from
> `A_N->infinity` and the exposure-floor inequality.

Then state an abstract sequence-level composition consuming a behavior-only
nonvanishing-defect predicate and PR69 Uptake. Do not formalize the reason graph or
traderization in the same pass. The authority corollary can be a second tiny theorem:
OCG's `license in Adm_n` plus existing `grounded_replay_admitted` implies every compiled
row has grounded license ancestry.

## Compiler and certificate findings

The small compiler should emit rows only for typed service comparisons, retain reason,
applicability, episode, surface, and license provenance, and run a feasibility gate.
Incompatible rows create a Continuity-visible conflict issue; none is silently dropped.
Prefix-conditional comparisons are ordinary applicability. Value-face-local comparisons
need an independently authenticated face-selection step.

LP dual witnesses should be derived proof receipts referencing strict-prefix row ids,
not new operative rows or sources of authority. They can support later repair proposals
through the reason state's transcript-source sort. This preserves provenance and avoids
self-certification.

## Hostile-example result

All requested attacks are classified in `COUNTERMODELS_2.md`; exact finite fixtures cover
the pairwise theorem, inquiry isomorphism, conflict infeasibility, attention theater,
sparse applicability, vanishing defect, defeat, face locality, and alternating repair
churn. The refined schematic either proves the intended service response, recognizes an
answer, or remains silent for a named failed premise. No trace is incorrectly classified.

## What remains open

The restricted bridge does not prove universal Answer-Mode Adequacy, relevant-surface
fairness for a concrete service scheduler, cross-era translation invariance, or the
reason-to-row compiler for the full reason language. Those are now distinct targets
rather than one opaque witness-completeness conjecture.

### PROGRESS-WITNESS-BRIDGE-CLOSED-IN-RESTRICTED-FRAGMENT
