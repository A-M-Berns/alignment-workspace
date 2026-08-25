Attach the **Canonical Formal Specification v2 — Reflective Integrity** to the fresh-context agent, then give it this prompt:

---

You are taking over a formal-specification project in a **fresh context**.

Your job is to repair the attached **Canonical Formal Specification v2 — Reflective Integrity**, integrate it into the live research repository as **Reflective Integrity Core v1.0**, validate the repairs adversarially, and open a PR.

This is **not** an exploratory architecture task. A fresh hostile red-team agent already audited v2. Its verdict was:

\[
\boxed{\texttt{LOCAL-REPAIR-REQUIRED}}
\]

and explicitly concluded that the central architecture survives.

The exact text of red-team repairs **R1–R5 was lost when the previous agent context was cleared**. Do not pretend otherwise and do not invent their exact wording.

However, the surviving portion of the audit contains enough information to recover the *required properties after R1–R5*. Your job is therefore:

\[
\boxed{
\text{reconstruct the smallest necessary local repairs directly against v2,}
\atop
\text{using the surviving hostile report as constraints.}
}
\]

Do not create repairs merely to fill missing numbered slots.

If the surviving audit says some property must hold after R1–R5, inspect v2 and derive the minimal change that makes it true.

# 1. Architectural status

Treat the following as frozen unless a repair produces a concrete contradiction.

The persistent state is

\[
S_t=(L_t,\mathcal R_t,N_t),
\]

where:

* \(L_t\): **Settlement Ledger**
* \(\mathcal R_t\): **Reason Ledger**
* \(N_t\): **Normative Record**

Keep:

\[
\boxed{\text{settlement}\neq\text{reason}\neq\text{normative uptake}.}
\]

The trajectory has four step kinds:

\[
SystemStep ::=
Settle
\mid Reason
\mid Norm
\mid Respond.
\]

Reflective Integrity is:

\[
\boxed{
RI=
GroundingConservation+
AnswerabilityConservation.
}
\]

It is a **safety/integrity** property, not a progress theorem.

Object-level and normative ontology may change under a minimal stable metalayer:

\[
\boxed{\text{preserve historical reference, not semantic representation}.}
\]

## Standing

Keep:

\[
StandingState=(status,pred,payload)
\]

with no custodian field.

Actual stance is derived from active stance-bearing commitments.

Operative force is derived from active `PForce` standing.

No separate mutable stance or force store.

## Effects

Keep:

\[
StandingEffect ::=
Create
\mid Supersede
\mid SetStatus
\]

and:

\[
NormEffect ::=
Standing(StandingEffect)
\mid Transfer(StandingId,PrincipalId).
\]

No:

* `SetCustodian`
* `AmendProto`
* `Do(ActionSpec)` in the reason language.

Transfer does not mutate standing.

`effect(a)` and `basis(a)` are derived, not stored.

Multiple licensed reason-based responses to the same reasons are permitted.

## Custody

Keep:

\[
\boxed{AnsRoot=CustodyEpisode.}
\]

Custody is the **answerability baton**: who is presently responsible for carrying a standing object through its next accountable transition.

It is not ownership, endorsement, authority, causation, residual liability, or authorship.

`PrincipalId` is thin.

Historical `StageRef`s may be creditors; ordinary temporal succession is not custody transfer.

Custody is derived from the unique current episode.

## Answerability

Keep:

\[
Closed_t(q),\quad Live_t(q),\quad Due_t(q)
\]

with:

\[
Closed
\oplus
(Live\land\neg Due)
\oplus
Due.
\]

`Due` means "an answer is now owed," not "a deadline was violated."

Indefinite:

\[
Live\land\neg Due
\]

is allowed.

Temporary `Due` is allowed.

Keep:

\[
ContinuityOK_t(q)
\iff
(Live_t(q)\land\neg Due_t(q))
\vee
\left(
Closed_t(q)\land
\forall q'\in succ_t(q).\ ContinuityOK_t(q')
\right).
\]

And keep the corrected central theorem, with the quantifier repair described below:

\[
\boxed{
\neg ContinuityOK_t(q)
\iff
\exists r\in Desc_t^*(q).\ Due_t(r).
}
\]

Do **not** restore either false invariant:

\[
\forall q.\ ContinuityOK_t(q)
\]

or

\[
\forall q.\ ContinuityOK_t(q)\vee Due_t(q).
\]

Residual liability, transfer consent, competence, rich protocol semantics, relational `AnswerableTo`, fairness/progress, and full normative correctness remain outside core RI unless an actual theorem requires them.

# 2. Surviving hostile audit

The following is the surviving verbatim portion of the hostile report:

> **Repair:** §16: "for every q ∈ Roots_t".
>
> **Class:** [LOCAL]
>
> **Changes architecture?:** No
>
> ────────────────────────────────────────
>
> **#:** R6
>
> **Repair:** Declare steps : Derivation → Finset StandingId; G3 :⟺ ∀s∈steps(D_a). Std_{<τ}(s) = (Active,_,PAuth _). State
>
> explicitly that RI checks licensing of inference steps, not their soundness; no inference interpreter is part of the
>
> theorem. Order WF so G4₁ precedes any evaluation of effect(a).
>
> **Class:** [LOCAL]
>
> **Changes architecture?:** No
>
> ────────────────────────────────────────
>
> **#:** R7
>
> **Repair:** §10: "acceptance via authorization" → "admissibility via authorization".
>
> **Class:** [LOCAL]
>
> **Changes architecture?:** No
>
> ────────────────────────────────────────
>
> **#:** R8
>
> **Repair:** Restore the definitions of StandingChanges, I_s^{A_s}, D_t, R_t, New_t (absent from the document as
>
> delivered). Clause (8) cannot be frozen without them.
>
> **Class:** [LOCAL]
>
> **Changes architecture?:** No
>
> ────────────────────────────────────────
>
> **#:** —
>
> **Repair:** Creditor.Prin unused; Grounded decorative; G4₂ redundant after R3.
>
> **Class:** [TASTE]
>
> **Changes architecture?:** —
>
> **Re-run after R1–R5.** EP induction: base by Z3+Z3′+Z6 (all seed roots current at 0 since D2 ⇒ no closing without a
>
> disposer, and N₀=∅); Norm step per §9.3 with R3 guaranteeing fresh subjects; Respond step: by D2 any root closed at
>
> t+1 has a disposer in N_t, hence was Due at t, hence not current — no current episode is removed, none added. ✓
>
> Custody Locality, Fate Monotonicity, T-NoInv follow as in the document. Due-Witness never needed the repair.
>
> **18. Architecture verdict**
>
> The four-constructor step type, derived custody, frozen digests, parametric SchemaCode, axiomatic seed, and the
>
> biconditional Due-Witness are all sound and mutually consistent; the dependency order is strictly τ-well-founded with
>
> no hidden cycle. The one substantive defect is an asymmetry in the parametric interface: SchemaCode received six
>
> structural assumptions and DemandCode received none, while four of the eight main clauses depend on two properties of
>
> DemandCode that were proved only for the single built-in value. Adding D1–D2 (and Z6) closes it without touching any
>
> definition, constructor, or store. Everything else is typing hygiene and wording.
>
> $$\boxed{\texttt{LOCAL-REPAIR-REQUIRED}}$$
>
> ---
>
> **Recap.** I read the (partially corrupted) v2 spec, built the dependency DAG, and attacked every listed target with
>
> explicit finite histories. Due-Witness, TargetCoverage, Digest Stability, GC, and the DAG claims survive
>
> unconditionally. Episode Uniqueness / Custody Locality / Fate Monotonicity / No-Invisible-Discontinuity fail for a
>
> one-object, one-step history whenever a seed root carries a non-gated or non-monotone DemandCode — the theorem's
>
> stated assumptions don't exclude that. Repair is structural assumptions D1–D2 plus seed clause Z6 (R1), with seven
>
> smaller local fixes (R2–R8). No architectural change. One caveat: clause (8) and the cohort theorems rest on
>
> definitions missing from the file you sent, so they are audited only under my reconstruction.

This text is authoritative.

Again: **the exact text of R1–R5 is unavailable.** Reconstruct only what is mathematically forced by this report and by v2.

# 3. First task: reconstruct the missing local repairs

Before editing the repository, perform a focused audit of v2 aimed specifically at reconstructing the missing R1–R5.

Write a small internal table:

| Needed post-repair fact from hostile report | Why v2 currently fails it | Minimal repair |
| ------------------------------------------- | ------------------------- | -------------- |

At minimum recover the following.

## Demand interface: D1 and D2

The hostile report identifies this as the one substantive formal defect.

v2 parameterized `SchemaCode` but did not impose the generic structural properties on `DemandCode` that later theorems require.

Repair the demand interface.

At minimum episode-closing demand semantics must satisfy:

### D1: monotonicity

Adding responses cannot make a satisfied demand unsatisfied.

Give the exact condition, including whatever compatibility is required of the cited-digest map.

### D2: disposition gating

A custody episode cannot become `Closed` unless a real disposition of that root has occurred and is validly represented by the cited evidence.

At theorem level this should imply:

\[
Closed_t(q)\Rightarrow
\exists a.\ Disposes(a,q).
\]

These are structural properties, not substantive normative correctness.

If the cleanest signature distinguishes generic `DemandCode` from an `EpisodeDemand` carrying proofs of D1/D2, that is allowed if it is strictly local and simpler.

The hostile report says the lack of D1/D2 is what broke:

* Fate Monotonicity;
* Episode Uniqueness;
* Custody Locality;
* the preservation form of No-Invisible-Discontinuity.

Close those counterexamples explicitly.

## Seed strengthening: recover Z3′ and Z6 minimally

The hostile rerun says:

\[
Z3+Z3'+Z6
\]

establishes the EP base, because D2 ensures seed roots cannot already be `Closed` without a disposer and \(N_0=\varnothing\).

Inspect the existing v2 `WFSeed`.

Recover the **smallest exact** additional seed conditions needed.

Do not invent a large constitutional seed theory.

The desired base result is:

\[
status_0(x)\neq Terminated
\iff
\exists!q\in Roots_0.
CurrentEpisode_0(q)\land subject(q)=x.
\]

The seed remains axiomatic.

## Freshness repair

The hostile rerun says:

> "Norm step per §9.3 with R3 guaranteeing fresh subjects."

Inspect the allocation rules and add the minimum precondition needed to guarantee:

\[
fresh(effect(a))
\cap dom(Std_{<\tau(a)})=\varnothing
\]

and pairwise distinct new standing IDs.

Deterministic allocation by \((\tau,index)\) is preferred.

Do not add mutable allocator state.

Explicitly test Create and Supersede against collision with:

* seed standing;
* earlier standing;
* sibling fresh IDs.

## WF / `effect(a)` evaluation order

R6 also says:

> "Order WF so G4₁ precedes any evaluation of effect(a)."

Repair any circular-looking definition in which evaluating `effect(a)` requires already knowing that `schemaRef(a)` points to an active `PAuth σ`.

The intended order is:

1. resolve `schemaRef(a)` in strict-prestate standing;
2. verify active `PAuth σ`;
3. evaluate
   \[
   \llbracket\sigma\rrbracket_{\mathcal S}(wit(a),PreState_{<\tau(a)});
   \]
4. check output preconditions/freshness.

If a former `schemaRef ∉ fresh(effect(a))` clause becomes redundant after strict-prestate lookup plus true freshness, delete it unless it still performs real work.

## Due-Witness domain

Apply the known local repair:

\[
\boxed{
\forall q\in Roots_t,\quad
\neg ContinuityOK_t(q)
\iff
\exists r\in Desc_t^*(q).\ Due_t(r).
}
\]

Do not claim the theorem for arbitrary malformed/non-issued root values.

# 4. Apply R6 exactly in substance

Separate **inference-step licensing provenance** from the semantics of practical schemas.

Introduce something like:

\[
steps:Derivation\to Finset\ StandingId
\]

and:

\[
G3(a)
\iff
\forall s\in steps(D_a),
Std_{<\tau(a)}(s)
=================

(Active,_,PAuth\ _).
\]

State explicitly:

\[
\boxed{
\text{RI checks that inference steps were licensed;}
\atop
\text{RI does not prove their inferential soundness.}
}
\]

There is no need for an inference-semantic interpreter in the RI theorem.

Do not make the practical:

\[
SchemaCode\to NormEffect
\]

interpreter serve double duty as an inference semantics.

Use the smallest typing distinction that makes this explicit.

# 5. Apply R7

Replace language claiming:

> "acceptance via authorization"

with:

> **"admissibility via authorization."**

Core RI establishes a licensed custody assignment.

It does not establish recipient consent.

Keep:

\[
\boxed{
\text{valid custody assignment}
\neq
\text{recipient consent}.
}
\]

Transfer consent remains deferred to legitimacy.

# 6. Resolve R8 rather than blindly restoring it

The hostile agent says the final theorem referenced undefined:

* `StandingChanges`;
* \(I_s^{A_s}\);
* \(D_t\);
* \(R_t\);
* \(New_t\).

`StandingChanges` is needed for TargetCoverage and should simply be defined exactly.

For the **cohort/source/diachronic-conservation package**, make a deliberate minimality decision.

The newer root-DAG machinery may make the old cohort bookkeeping redundant.

Choose one:

### RETAIN

Retain it only if you can:

1. define every symbol exactly;
2. prove the theorem from repaired core RI;
3. explain what it adds beyond successor-root continuity and Due-Witness;
4. do so without new state or architecture.

Then place it among derived theorems, not foundational definitions.

### DEMOTE

If it is redundant, historical baggage, or not consumed by anything, remove it from the **Core v1.0 main theorem**.

If useful, leave a short optional-derived-lemma note.

Do not leave undefined notation merely because an earlier draft had it.

Prefer the smaller theorem.

# 7. Minimality cleanup

The hostile audit also observed:

* `Creditor.Prin` may be unused;
* `Grounded` may be decorative;
* G4₂ may become redundant.

These are `[TASTE]`, not required repairs.

Resolve each conservatively:

* delete if it strictly simplifies the signature with zero theorem loss;
* retain if it has an immediate clear consumer.

Record what you decided.

Do not expand scope around them.

# 8. Repository integration

Now inspect the live repository.

Do not assume where the spec belongs.

Find the existing legitimacy / normative-learning / answerability materials and repo conventions.

Then integrate the repaired result as the canonical:

\[
\boxed{\textbf{Reflective Integrity Core v1.0}}
\]

Update or supersede stale local versions as appropriate.

Do not duplicate a canonical spec in multiple places unnecessarily.

Search the repo for stale architecture including:

* mutable `custodian` fields;
* `SetCustodian`;
* `AmendProto`;
* separate mutable stance;
* false global `ContinuityOK` invariant;
* old "acceptance via authorization" wording;
* `DemandCode` used without D1/D2 assumptions;
* undefined cohort notation.

Do not rewrite unrelated research prose.

# 9. Core v1.0 document requirements

The final canonical document should be organized for **mechanization**, not as a diary of previous revisions.

Include at least:

1. scope and non-goals;
2. Meta-Stability;
3. Standing Locality;
4. seed/genesis;
5. Settlement / Reason / Normative stores;
6. `SystemStep`;
7. reason representation;
8. inference-step licensing provenance;
9. parametric practical-schema interface;
10. parametric episode-demand interface with D1/D2;
11. standing ontology;
12. standing-effect interpreter;
13. freshness;
14. normative-event well-formedness;
15. answerability roots / derived custody;
16. Transfer;
17. minting;
18. responses and frozen digests;
19. `Closed / Live / Due`;
20. Episode Uniqueness;
21. Custody Locality;
22. successor DAG;
23. `ContinuityOK`;
24. Due-Witness;
25. No Invisible Discontinuity;
26. Grounding Conservation;
27. Answerability Conservation;
28. local preservation by step kind;
29. main RI theorem;
30. optional liveness under FAIR;
31. changing-ontology boundary;
32. deferred machinery;
33. exact minimal signature;
34. mechanization order;
35. vertical-slice interface.

Keep it compact where definitions already carry the semantics.

# 10. Main theorem target

The final theorem should fundamentally say:

\[
\boxed{
WFSeed+
\text{well-formed system trajectory}
\Longrightarrow
GC+AC.
}
\]

Derived consequences should include:

### Trichotomy

\[
Closed
\oplus
(Live\land\neg Due)
\oplus
Due.
\]

### Fate Monotonicity

Under D1/D2:

\[
Live\land\neg Due
\to
Due
\to
Closed
\]

with no backwards moves.

### Episode Uniqueness

\[
status_t(x)\neq Terminated
\iff
\exists!q.
CurrentEpisode_t(q)\land subject(q)=x.
\]

### Custody Locality

If the custodian of the same existing \(x\) changes from \(A\) to \(B\neq A\), an intervening:

\[
Transfer(x,\cdot)
\]

occurred.

### TargetCoverage

Standing changes happen only at targeted/fresh standing IDs.

### Effect Determinacy

Actual normative effect is the deterministic result of the selected licensed practical schema and strict pre-state.

### Due-Witness

For all issued roots:

\[
\boxed{
q\in Roots_t
\Rightarrow
\left[
\neg ContinuityOK_t(q)
\iff
\exists r\in Desc_t^*(q).\ Due_t(r)
\right].
}
\]

### No Invisible Discontinuity

Any answerability discontinuity is represented by a persistent outstanding Due witness, which can only be discharged through the frozen demand interface.

Do not assert eventual closure.

# 11. Validation: reproduce the hostile failures

Do not merely repair prose.

Build executable/reference-model tests if the repo has an appropriate place for them. If an existing finite-history test harness exists, extend it instead.

At minimum test the exact red-team fault class.

## Demand interface tests

Construct at least:

1. a non-monotone demand;
2. a demand that closes without a disposition;
3. valid `AccountForSuccession`;
4. valid closure followed by unrelated responses;
5. response citing unrelated event.

The first two must be rejected as invalid episode-demand instances or fail theorem preconditions.

## Seed / EP tests

Test:

* one seed standing + root;
* multiple seed standing objects;
* malformed duplicate seed roots;
* seed root with demand that would close immediately absent D2;
* valid repaired seed.

## Freshness

Attempt:

* Create collision with existing standing;
* Supersede fresh successor collision;
* sibling fresh-ID collision;
* distinct `(τ,index)` allocation.

## Custody / answerability

Test:

* suspend → resume;
* transfer;
* repeated transfer;
* transfer before old response;
* supersession;
* split;
* merge;
* revocation;
* third-party disposition;
* response after disposition;
* response citing unrelated event.

## Due-Witness

Test:

* Due root;
* Closed parent with Due child;
* deep Due descendant;
* split with one Due branch;
* merge/shared descendant;
* Closed revocation;
* `Live ∧ ¬Due` leaf;
* multi-level graph with no Due.

## Reason/schema distinction

Produce a finite example showing:

* `Derivation` has licensed inference-step references;
* RI checks those references were active authorizations;
* RI does not assert inference soundness;
* independently, the selected practical `SchemaCode` produces the `NormEffect`.

# 12. Independently reconstruct the lost audit details

Because R1–R5 are unavailable, do one extra focused adversarial pass **after implementing the repairs**.

Ask:

> Is there any smallest finite history consistent with the repaired signature that recreates one of the failures described by the surviving red-team recap?

Specifically try again to break:

* EP under Respond;
* EP under Create/Supersede collision;
* Fate Monotonicity;
* Custody Locality;
* Digest Stability;
* Due-Witness;
* strict-prestate schema evaluation.

If you discover another local defect plausibly corresponding to lost R2–R5, fix it minimally and document it as:

> "reconstructed local audit repair; exact original R-number unavailable."

Do not invent numbering.

If you discover an architectural problem, stop.

# 13. End-to-end compatibility

This PR is supposed to freeze the RI core immediately before an executable vertical slice.

Do not build the full demo here.

But verify that the repaired architecture naturally permits:

\[
\boxed{
\Gamma
\to
L
\to
\mathcal R
\to
N
\to
O
\to
K
\to
\text{trader}
\to
\text{Logical Inductor}.
}
\]

In particular:

* `Settle` writes only \(L\);
* `Reason` writes only \(\mathcal R\);
* `Norm` produces certified normative effects;
* `Respond` accounts for dispositions without producing them;
* \(O_t\) is a projection of active `PForce`;
* downstream market code can consume \(O_t\) without becoming RI state.

Add a short **Vertical Slice Interface** section to the canonical spec if appropriate.

Do not solve \(N\to O\to K\) generally in this PR.

# 14. PR execution

Work on a branch.

Make the changes.

Run all relevant repository tests.

Run the new finite-history/adversarial tests.

Inspect the final diff.

Before opening the PR, produce this audit table:

| Finding                                   | Source                                | Repair | Validation | Architecture changed? |
| ----------------------------------------- | ------------------------------------- | ------ | ---------- | --------------------- |
| Demand D1/D2                              | surviving hostile recap               |        |            | No                    |
| Seed strengthening Z3′/Z6                 | reconstructed from hostile rerun + v2 |        |            | No                    |
| Fresh standing IDs                        | reconstructed from hostile rerun + v2 |        |            | No                    |
| WF/effect evaluation order                | hostile R6 + v2                       |        |            | No                    |
| Due-Witness root quantifier               | surviving hostile report              |        |            | No                    |
| Inference-step licensing                  | R6                                    |        |            | No                    |
| Transfer "admissibility" wording          | R7                                    |        |            | No                    |
| Cohort notation                           | R8                                    |        |            | No                    |
| Any additional reconstructed local repair | independent re-audit                  |        |            | No/STOP               |

Do not claim to have reproduced the exact lost R1–R5.

Say explicitly in the PR:

> The original red-team context containing the verbatim R1–R5 entries was lost. Their necessary consequences were preserved in the surviving audit recap. This PR reconstructs the minimal repairs directly against v2 and reruns the affected finite histories.

That is the correct provenance.

# 15. PR description

The PR description should explain:

### Why

A fresh hostile audit returned:

\[
\texttt{LOCAL-REPAIR-REQUIRED}
\]

and explicitly found no architecture break.

### Central repair

The parametric demand interface now has the structural properties actually required by the RI theorems:

* monotonicity;
* disposition gating.

### Other repairs

Seed/EP conditions, fresh-ID guarantees, well-founded schema resolution, inference-step licensing, Due-Witness domain, transfer wording, and cleanup/demotion of undefined cohort machinery.

### Architecture unchanged

* three append-only ledgers;
* four system-step constructors;
* derived custody;
* `AnsRoot = CustodyEpisode`;
* Transfer outside standing mutation;
* frozen digests;
* successor DAG;
* Due-Witness;
* safety/liveness split;
* minimal stable metalayer.

### Deferred

* residual liability/release;
* transfer consent;
* principal competence;
* rich protocol semantics;
* relational answerability;
* fairness/progress;
* full normative correctness;
* end-to-end LI instantiation.

### Next step

Executable vertical slice:

\[
\Gamma
\to L
\to\mathcal R
\to N
\to O
\to K
\to trader
\to LI.
\]

# 16. Freeze criterion

Before opening the PR, determine one of:

\[
\boxed{\texttt{FREEZE-READY}}
\]

\[
\boxed{\texttt{REPAIR-INCOMPLETE}}
\]

\[
\boxed{\texttt{ARCHITECTURE-REOPENED}}
\]

Only open the PR if:

\[
\boxed{\texttt{FREEZE-READY}}.
\]

If any reconstructed repair requires a new persistent store, a new core philosophical conservation law, abandonment of derived custody, or substantive restructuring of the answerability DAG, stop and give the smallest counterexample.

Do not improvise an architecture change.

# Final response

Return:

* branch name;
* commit hash(es);
* PR number and link;
* tests run and results;
* final repair table;
* exact reconstructed D1/D2 and seed conditions;
* any additional local issue recovered that may have corresponded to lost R2–R5;
* whether the cohort theorem package was retained or demoted, and why;
* exact canonical spec path;
* final verdict.

Desired endpoint:

\[
\boxed{
\textbf{Reflective Integrity Core v1.0}
\quad
\texttt{FREEZE-READY}
}
\]

After that, do not continue conceptual RI development in this task. The next phase is the end-to-end normative-reasoner / Logical-Inductor demo.
