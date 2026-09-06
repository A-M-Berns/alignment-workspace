Work in `A-M-Berns/alignment-workspace`, starting from the current state around PR85/PR86.

Your task is a **final mathematical pressure pass before full canonicalization**.

PR86 appears to have found the right overall theory. Do not launch another broad architecture search. Instead, pressure-test and repair the remaining type-level issues that could still make the canonical theory misleading or brittle.

The target is:

> After this round, either the legitimacy / normative-induction spine is genuinely ready for canonicalization, or there is one explicit counterexample showing why not.

Read at minimum:

* PR85 synthesis and adversarial integrity work;
* PR86 mathematical consolidation;
* `OccurrenceIntegrity.lean`;
* `NonCaptureCertificate.lean`;
* `NormativeInductionInterface.lean`;
* `NormativeInductorComposition.lean`;
* current normativity wiki pages for orientation only.

Preserve the current major conclusions unless the mathematics forces a change:

* obligation **occurrence identity** is distinct from semantic content;
* Integrity is proof-relevant and history-segment based;
* settlement items and internal `Closes` judgments are distinct;
* Progress is the transport-weighted edge endpoint;
* `PracticalCert` is edge-local and evaluated against one realized response per service occurrence;
* Robust Openness is distinct from Integrity;
* counterfactual semantics remain externally supplied;
* the NI realization remains conditional where semantic/engineering connectors are not proved.

Do not rewrite the canonical wiki yet.

# 1. Make the normative endpoint state explicit

PR86 currently has:

* `Boundary`;
* `anchor`;
* `Accounted`;
* `Segment`.

But the proposed public relation still speaks approximately about

```text
Segment A B
```

while the actual normative state needed by a downstream consumer is more like

```text
(boundary, anchor, current account).
```

This matters because an arbitrary intermediate state is not an `Initial` state: it may already contain answered and closed occurrences whose immutable receipts must survive into the future.

## Pressure this hard

Define or derive the smallest object corresponding to the **current qualitative obligation state**, schematically:

$$
\boxed{
\mathcal O_P
=
(B,\operatorname{anchor},\operatorname{account})
}
$$

where `account` gives the authenticated current account of every exposed occurrence.

Then ask whether Integrity should be a relation

$$
\boxed{
\operatorname{IntegrityEvolution}(\mathcal O_m,\mathcal O_n)
}
$$

witnessed by a `Segment` whose propagation sends the source account to the target account.

The core law should be something like:

$$
\operatorname{account}_n
=
\operatorname{propagate}(
  \text{segment},
  \operatorname{account}_m).
$$

`Initial` should become merely one way to construct the first accounted state, not a premise required to talk about every legitimate history segment.

The downstream relation should support:

$$
\mathcal O_m \preceq_{\mathrm{int}} \mathcal O_n
$$

and composition should be genuinely typed:

$$
\mathcal O_0\preceq_{\mathrm{int}}\mathcal O_1
\land
\mathcal O_1\preceq_{\mathrm{int}}\mathcal O_2
\Rightarrow
\mathcal O_0\preceq_{\mathrm{int}}\mathcal O_2.
$$

Do not settle for an existential segment relation whose witnesses can disagree about the source or target account.

## Questions

* Is the account itself part of the normative state or merely a proof certificate?
* If proof-irrelevance/witness nonuniqueness matters, what should the endpoint relation quantify over?
* Should the public object contain a chosen account or merely certify existence of one?
* What exact form is easiest for the future deference/corrigibility theorem to consume?
* Does the current `Segment` representation support restriction and concatenation of arbitrary accounted states cleanly?

Produce Lean definitions/lemmas if the repair is straightforward.

# 2. Make Legitimate Evolution truly trajectory-relative

PR86 currently proposes roughly

$$
\Leg_P(H,m,n)
=
\Segment(H_m,H_n)
\times
\RobustOpen_P(H_n).
$$

Pressure whether checking Robust Openness only at the endpoint is sufficient.

Construct the obvious attack:

```text
open at m
→ captured / inaccessible / principal loses standing in middle
→ restored at n
```

If endpoint-only Robust Openness accepts this trajectory, decide whether that contradicts the intended meaning of legitimate cognitive evolution.

The likely target is something like:

$$
\boxed{
\LegEvolution_{P,\Gamma}(H_{m:n})
=
\IntegrityEvolution(H_{m:n})
\land
\forall k\in[m,n],
\RobustOpen_{P,\Gamma}(H_k)
}
$$

or a weaker transition/event-local form if full prefixwise quantification is stronger than necessary.

Do not adopt full prefixwise openness merely because it is simple. Determine the weakest trajectory condition that blocks temporary exclusion from being laundered by later restoration.

Press especially on:

* temporary loss of the principal's standing;
* temporary absence of all adequate routes;
* temporary suppression of settlement/evaluation access when that route matters;
* concern representation being strategically delayed and later restored.

Ask whether the right thing is:

* openness at every prefix;
* openness at every normative transition;
* persistence only while a concern is live;
* some interval/obligation-relative variant.

The result should compose naturally under concatenation of legitimate segments.

# 3. Properly type the actual/null intervention

PR86 says actual standing can be recovered from `(P)` at the null intervention.

But the current `Scenario` interface has:

```text
actual
cf : J → CovState
```

and no formal requirement that some `j₀ : J` satisfies

```text
cf j₀ = actual.
```

Repair this rather than relying on prose.

Compare at least two designs:

### Option A — distinguished null intervention

```text
null : J
cf_null : cf null = actual
```

Then Robust Openness quantifies over all `j`, including `null`.

### Option B — actual branch explicit

Define Robust Openness as:

```text
actual.Covered
∧ actual.OpenTo
∧ ∀ j, (cf j).Covered ∧ (cf j).OpenTo
```

and leave `J` for proper counterfactual interventions only.

Choose the cleaner public interface.

The result must make it formally true—not merely intended—that Robust Openness contains the actual-history standing condition needed by Diachronic Answerability.

Also revisit the "persistence bill" terminology.

The **minimal external bill** should probably be:

> supply/certify `RobustOpen` under a declared intervention semantics.

Componentwise persistence is a useful sufficient construction:

$$
\text{persistence certificate}
\Rightarrow
\RobustOpen,
$$

but PR86 already proves that persistence is strictly stronger than necessary.

Do not describe a sufficient plugin as the unique external contract.

# 4. Fix the answer-versus-closure semantics

The current `Protocol` uses:

```text
Evidence : Req → Type
answer_sound : AnswerOK ... → Evidence r
closure_sound : SetView ... → Closes ... → Evidence r
```

and `Program.evaluate` treats both answer and close leaves as producing `Evidence r`.

But our conceptual distinction is:

> answering an obligation and legitimately closing/discharging it are different fates.

A settlement-backed discharge need not constitute an ordinary answer to the underlying question.

Pressure whether `Evidence` is simply misnamed or genuinely mistyped.

Possible repair:

$$
\boxed{
\operatorname{ResolutionWitness}(r)
}
$$

or

$$
\operatorname{AccountWitness}(r)
$$

meaning "sufficient evidence that the anchored obligation has been legitimately accounted for," with constructors/sources corresponding to:

* adequate answer;
* valid closure;
* live successor structure.

Then an answer receipt supplies a witness one way and a closure receipt supplies one another way.

Alternatively, if answer evidence and closure evidence genuinely need distinct types, split them.

Do **not** introduce separate types merely for aesthetic purity. Prefer the smallest structure that preserves the normative distinction.

The resulting Integrity theorem should say something like:

> every occurrence remains represented by a proof-relevant account whose terminal leaves are live, adequately answered, or validly closed.

It should not accidentally imply:

> every validly closed obligation has been substantively answered.

Audit names and theorem prose accordingly.

# 5. Pressure the `LocalLaw` arity claim

PR86 describes `LocalLaw`

$$
r\to(r_1,\ldots,r_k)
$$

as handling carry, split, merge, and re-representation.

Check whether **general merge** is actually expressible.

A true merge could look like:

$$
(r_1,r_2)\longrightarrow c
$$

where a response to `c` jointly resolves both parents, even though neither parent individually maps to `c`.

Determine whether the current occurrence-indexed account representation can express this through shared ports/programs, or whether it only supports unary-parent decomposition/refinement.

If current machinery only supports unary-parent transformations:

* correct the claim;
* call it carry/split/refinement/re-representation;
* leave many-to-one obligation aggregation as an explicit later extension if needed.

Do not generalize the whole core to hypergraphs unless there is an actual theorem/application requiring it.

This is a **pressure test**, not necessarily a blocker.

# 6. Retype Normative Induction directly on the qualitative export

PR86 says `Evaluation` is "typed on the Integrity export," but in Lean it takes roughly:

```text
boundary
anchor
```

rather than the full authenticated qualitative state/account.

Once §1 settles the public \(\mathcal O_P\) type, decide whether downstream evaluation should literally be:

```text
Evaluation (O : ObligationState ...)
```

even if its quantitative proofs use only:

* `O.boundary.exposed`;
* `O.anchor`.

This is valuable because it makes the public theorem chain type-check conceptually:

$$
\boxed{
\LegitimateEvolution
\to
\mathcal O_P
\to
\NormativeInduction(\mathcal O_P)
\to
\Progress.
}
$$

The theorem is allowed to project away fields it does not use.

Do not require quantitative NI to inspect historical receipts merely because they are present in the type.

# 7. Re-state Answerability after the repairs

After §§1–4, state the strongest clean theorem actually justified.

The desired shape is something like:

$$
\boxed{
\IntegrityEvolution(\mathcal O_m,\mathcal O_n)
\Rightarrow
\AnswerabilityConservation(\mathcal O_m,\mathcal O_n).
}
$$

Clarify exactly what "Answerability Conservation" means now.

It should capture at least:

* occurrence multiplicity is preserved;
* no occurrence silently disappears;
* terminal answer receipts remain immutable;
* terminal closure receipts remain immutable;
* live content is faithfully transformed;
* every current account remains anchored to the original occurrence specification.

Then identify what additional statement comes from Robust Openness, e.g.:

* protected principal retains standing on applicable/live carriers;
* relevant concerns retain adequate routes.

This may give a nice decomposition:

$$
\boxed{
\text{Diachronic Answerability to }P
=
\text{content/account conservation from Integrity}
+
\text{standing/access from Robust Openness}.
}
$$

State this precisely enough that it is not merely prose.

# 8. Re-state Legitimate Evolution

The ultimate goal of this round is the exact public type that deference/corrigibility should later consume.

Aim for a form such as:

```text
LegitimateEvolution P Γ O₀ O₁
```

or

```text
LegitimateSegment P Γ H[m:n]
```

with a derived endpoint relation.

It should satisfy:

### Reflexivity

if appropriate.

### Composition

the central property:

$$
\Leg(O_0,O_1)\land\Leg(O_1,O_2)
\Rightarrow
\Leg(O_0,O_2).
$$

### Initial-state neutrality

It should **not** imply that `O₀` is substantively correct or good.

### History sensitivity

It should preserve proof-relevant information needed to distinguish two trajectories with the same endpoint if one evolved illegitimately.

This last point is important.

The endpoint relation can existentially hide the witness for consumers, but the proof-relevant segment certificate should remain available for auditing.

# 9. Check the external bills one final time

At the end there should be no ambiguity about what the generic theory intentionally does not solve.

## Settlement

Separate:

* interface authenticity;
* source trustworthiness;
* historical receipt immutability;
* internal `Closes`;
* authorization;
* counterfactual anti-suppression.

## Non-Capture

Minimal public bill:

```text
a certified RobustOpen object/proposition
under declared scope + intervention semantics + protected relation.
```

Persistence is one sufficient external theorem.

## Practical semantics

Minimal public bill remains:

$$
\PracticalCert(e,s,\Pi_s)
$$

against the one actually realized response.

## Evaluation

The evaluation measure/transport is externally declared; generic legitimacy does not determine moral weights.

Make sure no external bill is listed as an "unfinished theorem" of the generic theory.

# 10. Do not reopen solved parts

Unless the repairs force it, preserve:

* the edge-loss Progress endpoint;
* the three-term bound;
* the PR82 normalization;
* one joint operative region;
* the distinction between price feasibility and practical compatibility;
* the direct `PracticalCert`;
* the conditional NI theorem structure;
* occurrence-indexed multiplicity;
* stored closure receipts;
* the separation of Integrity and Non-Capture.

Do not start a new broad search over normativity architectures.

# 11. Lean deliverables

Where the conceptual repairs are straightforward, implement them.

High-value Lean targets:

1. `ObligationState` / accounted qualitative-state package;
2. a segment/evolution relation transporting an existing account;
3. composition/transitivity of that relation;
4. an actual/null-intervention repair for Robust Openness;
5. a trajectory-relative openness/legitimacy certificate, at least structurally;
6. rename/retype `Evidence` if needed;
7. `Evaluation` indexed by the qualitative export object;
8. re-prove the conditional Progress/NI theorem against the repaired type;
9. exact counterexample to endpoint-only openness if that formulation is rejected;
10. exact witness that legitimate segments compose nonvacuously.

Do not inflate theorem count with wrappers.

# 12. Final readiness verdict

Produce one concise document containing:

## Final canonical object graph

Ideally no more complicated than:

```text
Protocol / external semantics
        ↓
Accounted obligation state O
        ↓
Integrity evolution O₀ → O₁
        +
trajectory-relative Robust Openness
        ↓
Legitimate Evolution
        ↓
qualitative export O_P
        ↓
Normative Induction / PracticalCert
        ↓
Progress
        ↓
LI Normative Inductor realization
```

## Exact major theorem spine

For every theorem:

* type;
* hypotheses;
* conclusion;
* evidence status.

## Remaining external contracts

Exactly what other theories/applications supply.

## Remaining research problems

Only genuine unsolved mathematics.

## Canonicalization blockers

Use one of:

### `READY FOR FULL CANONICALIZATION`

Only if the endpoint state, trajectory relation, openness-over-time, settlement/closure semantics, and NI handoff all have stable types.

### `NEARLY READY — ONE BLOCKER: ...`

Give the exact smallest mathematical ambiguity.

### `NOT READY`

Only if one of these repairs exposes a major architectural failure.

The bar is:

> Could we now rewrite the wiki, register the central theorem spine, and treat subsequent work as realization, instantiation, or downstream deference/corrigibility research—without expecting another reorganization of the generic theory?

If yes, say so clearly.
