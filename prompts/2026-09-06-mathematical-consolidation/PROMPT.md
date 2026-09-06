Work against the current `A-M-Berns/alignment-workspace` repository, taking PR85 (`round/2026-09-05-integrity-synthesis`) and the preceding normativity/legitimacy/Normative-Inductor rounds as research evidence, **not as canonical truth**.

Your task is to perform an author-level mathematical consolidation whose goal is:

> **Get the normativity / legitimacy / Normative Inductor part of the repository into the strongest coherent mathematical state we currently know how to justify, so that a subsequent pass can canonicalize the theory without first needing another conceptual repair round.**

This is not primarily a documentation task and not a request to preserve the current architecture. Press on the mathematics. If two abstractions should collapse, collapse them. If an apparent implication is tautological, weaken the premise until the theorem says something. If a current "missing bridge" is an artifact of a silently changed endpoint, remove it. If a Lean interface encodes the wrong theorem, repair the interface rather than canonizing it.

Do not optimize for producing lots of new machinery. Optimize for a **small, exact, compositional theorem spine** with clean type boundaries and an explicit bill of genuinely external assumptions.

## 0. Evidence discipline

Read at minimum:

* the current canonical/checkpoint legitimacy material;
* PR80/defeat/standing material now on `main`;
* PR82 Normative Inductor realization round;
* all relevant PR85 rounds, especially:

  * integrity constructive work;
  * integrity adversarial/cross-review;
  * integrity synthesis;
  * Non-Capture certificate;
  * practical-semantics certificate;
  * NI gap audit;
  * `NormativeInductorComposition.lean`;
* the current normativity wiki pages, especially Legitimacy, Diachronic Answerability, Normative Induction, Normative Inductor, Actionability/Force, settlement-related material;
* landed Lean modules that the theory is supposed to consume.

Respect the repository evidence taxonomy. Never turn a proposed interface into a theorem or a conditional theorem into an unconditional realization.

Treat exact counterexamples as first-class evidence. Prefer discovering that a proposed compression is false to preserving a pretty architecture.

## 1. Recover the mathematical theory before editing it

First reconstruct the best current end-to-end theory independently from the prose.

The public shape should probably remain approximately

$$
(\mathfrak I,H,\SetView,\ldots)
\longrightarrow
\text{Legitimacy certificate}
\longrightarrow
\mathcal O_P
\longrightarrow
\text{service / uptake / practical semantics}
\longrightarrow
\Progress_P,
$$

with an LI/market implementation realizing the quantitative half.

But do not assume the existing factorization is exactly right. Determine:

1. What are the primitive structures?
2. What are merely certificates about those structures?
3. What are actual mathematical consequences?
4. What belongs to the generic normative theory?
5. What belongs to an external application semantics?
6. What belongs only to the LI/Normative-Inductor realization?

The result should have no object/predicate type confusions and no theorem whose premise simply restates its conclusion in different names.

## 2. Settle the Integrity → Answerability question properly

PR85 strongly suggests that generic record integrity alone does not imply substantive Diachronic Answerability. Preserve that lesson.

Try to obtain the cleanest nontrivial hierarchy of the form

$$
\boxed{
\text{Record Integrity}
+
\text{Content Integrity}
\Longrightarrow
\text{Diachronic Answerability / Answerability Conservation}.
}
$$

But **do not define `ContentIntegrity` as literally "every obligation is answered, discharged, or carried" and then announce this implication**. That would merely rename Answerability.

Find the lowest-level local invariant from which the global three-fate accounting theorem genuinely follows.

At minimum investigate whether the right primitive package involves:

* append-only authenticated event identity;
* immutable anchored obligation occurrence identity;
* immutable anchor/specification and cited basis;
* strict-prefix provenance and transition authority;
* authenticated local transformation of normative content;
* answer receipts whose adequacy is certified relative to the immutable anchor;
* settlement discharge carrying both an authenticated external settlement item and an immutable internal closure certificate;
* faithful carry preserving the relevant anchored normative content;
* preservation of standing/authority conditions needed for the successor to remain genuinely answerable;
* explicit handling of split/merge transitions.

The PR85 attacks must remain blocked:

* unchecked "answer" labels;
* self-grounded/unauthorized disposal;
* manufactured settlement or manufactured closure;
* retroactive recomputation of `Closes`;
* zero-ledger/bottom-witness vacuity;
* existential segment witnesses that do not agree at boundaries;
* multiplicity collapse when two distinct obligation occurrences carry identical semantic content.

In particular, **obligation occurrence identity must survive even when semantic content is equal**. Decide whether the semantic lattice should be occurrence-indexed, whether accounting needs an additive/multiset layer, or whether occurrence identity lives outside the semantic content lattice. Do not leave this ambiguous.

Aim for a theorem with real mathematical content:

> local authenticated conservation conditions on every transition + authenticated initial exposure data ⇒ global complete accounting of every incurred obligation occurrence.

If the right object is a proof-relevant segment certificate, make its boundary data explicit enough that composition/transitivity is actually typed rather than merely intended.

## 3. Make settlement semantics exact

Preserve and sharpen the important PR85 distinction:

* `SetView(H_n)` supplies externally available authenticated settlement items;
* `Closes(H_n,s,α)` is an **internal normative/interpretive closure certificate** under the rules, licences, grounds, and interpretation operative at that prefix.

A valid historical discharge should store enough immutable evidence that later reasoning cannot retroactively alter whether the discharge was properly certified at the time.

Later rejection should be modeled as an appended reconsideration/challenge event and, where appropriate, a fresh obligation—not mutation of the historical discharge.

Separate clearly:

1. boundary/interface authenticity;
2. epistemic trustworthiness of the external settlement source;
3. append-only historical availability;
4. the internal `Closes` judgment;
5. authority to use the closure;
6. counterfactual resistance to suppression/delay.

Only (6), where relevant to the declared intervention class, should migrate into Non-Capture. Do not use the overloaded phrase "settlement integrity" to hide these distinct assumptions.

## 4. Finish the Legitimacy factorization

Pressure-test whether the mature top-level statement really is

$$
\boxed{\Leg_P = \Integrity_P \wedge \RobustOpen_P}
$$

with Diachronic Answerability derived from Integrity rather than an independent conjunct.

If this does not work, exhibit the exact counterexample and retain the minimum additional primitive.

For Robust Openness / Non-Capture, use PR85's necessity work to seek the smallest useful public bill. The current candidate is approximately:

* actual Coverage at the factual prefix;
* adequate route for concerns that become live only counterfactually;
* preservation or adequate replacement of routes for concerns live in both branches;
* preservation of the protected principal's standing on counterfactually relevant carriers.

Keep concern identity, applicability transport, branch coupling, protected principal/relation, and what exterior policy is held fixed in the **intervention semantics/type**, rather than duplicating them as arbitrary Boolean clauses.

Keep Integrity and Non-Capture sharply separate:

* Integrity governs what happens to normative content that has entered the trajectory.
* Robust Openness governs whether relevant content and the protected party can continue to enter / act under declared interventions.

Try to state the conceptual theorem in a way that supports the compression:

> **Integrity blocks evasion by revision; Robust Openness blocks evasion by exclusion.**

But the formal definitions, not the slogan, decide whether this is actually true.

## 5. Freeze the qualitative public handoff

Determine the minimal public \(\mathcal O_P\) exported by Legitimacy.

The current candidate is roughly

$$
\mathcal O_P=(E,\Live,\Spec,\Status,\text{authenticated lineage/provenance as needed}).
$$

Maintain the distinction:

* historical exposure \(E_{\le N}\): everything for which responsibility was incurred;
* current live docket: what remains owed now.

Do not smuggle quantitative weights, importance, service intensity, probabilities, market geometry, or LI-specific securities into this handoff.

Check that every downstream theorem consumes only the fields it actually needs.

## 6. Correctly state Progress and the practical-semantics boundary

This is especially important because PR85 may have silently changed the endpoint.

Recover the exact abstract Progress theorem we intended before accepting the new Lean theorem as canonical.

The intended public practical certificate is currently:

$$
\boxed{
\PracticalCert(e,s,\Pi_s;M_{es},\epsilon_{es})
:\quad
\Lambda_{es}(\Pi_s)\le M_{es}d_s+\epsilon_{es},
}
$$

where \(\Pi_s\) is the **one actually realized response distribution at service occurrence \(s\)**.

All exposures sharing service occurrence \(s\) must certify themselves against that same \(\Pi_s\). This is the right location of joint practical-response compatibility.

Counterfactual value vectors, approximate argmax, finite policy menus, replicated policy-evaluation ecologies, adequate-set semantics, etc. should remain **sufficient plugins for producing `PracticalCert`**, not public structure unless genuinely necessary.

Now audit PR85's `progress_bound`.

PR85 introduced an exposure-level loss \(\ell(e)\) and an assumption resembling

$$
T(e,s)>0\implies \ell(e)\le\Lambda_{es}(\Pi_s),
$$

calling this `HeadlineToEdgeDominance`.

Determine whether this is actually required by our established Progress definition.

My current expectation is that the canonical statistic should remain the **transport-weighted edge response loss plus residual mass**, i.e. the matched part is directly

$$
\sum_{e,s}T(e,s)\Lambda_{es}(\Pi_s),
$$

so no extra headline-dominance adapter is required.

If that is correct:

* restore the canonical Progress theorem to that type;
* treat the exposure-level `HeadlineToEdgeDominance` theorem as an optional stronger corollary for applications that want a single headline loss per exposure;
* do not list it as a missing core arrow.

If instead the exposure-level statistic is mathematically superior, justify the change carefully and show why incremental/multiple-service answering is still represented correctly.

Do not silently switch endpoints merely because a Lean proof happened to be convenient.

The target theorem should still decompose failure into the recognizable three terms:

$$
\boxed{
\Progress_N
\le
\Gamma_N\,\Psi_\phi(\chi_N)
+
\bar\epsilon_N
+
D r_N
}
$$

or its precisely typed equivalent.

## 7. Reassess the Normative Inductor realization against the cleaned abstract theory

Once the abstract contracts are repaired, re-type-check the entire LI realization conceptually.

The implementation should still look approximately like

$$
\mathsf{NI}
=
\mathsf{MarketMaker}\!\left(
\mathsf{TradingFirm}^{\mathcal L}
+
\mathsf{JointProjectionEnforcer}[\Compile(\mathcal O_P)]
\right)
+
\mathsf{DecisionAdapter}.
$$

Preserve the important PR82 lessons unless contradicted:

* compile all simultaneously serviced normative requirements into **one joint region**, not independent reason traders;
* public defect \(d_s=\operatorname{dist}_\infty(b_s,K_s)\);
* service intensity \(a_s=\lambda_s\);
* Euclidean projection may remain an internal enforcement implementation;
* normalization should be invariant under enforcement-null coordinate padding;
* normative admissibility does **not** imply truth of policy-value securities;
* counterfactual-value semantics remain externally authenticated;
* one response distribution serves all edges at a service occurrence;
* joint price-space feasibility is distinct from joint practical-response compatibility;
* compiler failure must conserve the original obligations rather than erase them.

Now determine which remaining connectors are:

### A. generic mathematics we should prove now;

### B. executable/engineering integration we should implement now;

### C. genuine research problems;

### D. intentionally external assumptions.

Do not let category D continue appearing in prose as if the generic NI is expected eventually to derive it.

## 8. Strengthen the conditional end-to-end theorem without laundering assumptions

Try to produce the best current **conditional end-to-end Normative Inductor theorem**.

Its hypothesis package should name every still-open bridge explicitly and its conclusion should compose all already-landed pieces.

It should be possible to read the theorem signature and see exactly why it is not yet an unconditional realization.

Aim for a shape like:

$$
\begin{aligned}
&\text{authenticated legitimate obligation process}\\
+{}&\text{sound strict-prefix compiler}\\
+{}&\text{joint feasible/effective operative regions}\\
+{}&\text{safe/affordable predictable service}\\
+{}&\text{projection uptake certificate}\\
+{}&\text{joint edge-local practical certificates}\\
+{}&\text{adapted transport}\\
+{}&\text{computable augmented market}
\\[1ex]
&\Longrightarrow
\text{ordinary LI preservation}
\;\wedge\;
\text{finite Progress bound}.
\end{aligned}
$$

But do not accept this exact list blindly. Minimize it.

If several hypotheses can be derived from one stronger natural certificate, package them. If one field is never used, remove it.

The theorem should preferably consume the cleaned \(\mathcal O_P\) handoff rather than an unrelated parallel representation.

## 9. Audit the remaining mathematical gaps aggressively

At the end, I want the unresolved list to be **shorter and more precise** than PR85's.

Especially press on:

### Convex representability

What exact class of anchored normative obligations can the compiler soundly realize as finite rational convex constraints?

Separate:

* representability;
* compiler soundness;
* compiler completeness within a declared class;
* joint feasibility;
* affordable enforceability.

Do not conflate any of these.

### Scheduling / affordability

Determine exactly what has been proved for predictable finite workloads and what remains open for adaptive/adversarial/closed-loop service.

Tie service intensity units to the actual liability/enforcement theorem.

### Practical semantics

Do not merely say "authenticated values needed." State the exact certificate that a practical-semantics plugin must output.

The value-correspondence construction from PR82 may remain a worked sufficient instance, but the public boundary should be the simpler `PracticalCert` if possible.

### Semantic transport through ontology change

Specify exactly what has to be transported when an anchored obligation is answered in a later representation, and where those constants enter \(\bar\epsilon\).

### Non-Capture

Leave it application-relative. Do not attempt to derive causal intervention semantics, the right intervention class, or evaluator independence from the generic theory.

## 10. Lean work

Modify Lean where useful to make it match the cleaned mathematics.

Priorities:

1. repair the current PR85 axiom-audit CI failure;
2. retain theorem names/status only when they mean what the surrounding prose says;
3. prove the correct finite Progress theorem at the correct endpoint;
4. if `HeadlineToEdgeDominance` remains, classify it as an optional adapter/corollary rather than core machinery unless the endpoint audit proves otherwise;
5. make obligation occurrence multiplicity impossible to erase by semantic-idempotent bookkeeping;
6. make closure certificates immutable historical data rather than recomputed predicates where the Lean interface currently permits recomputation;
7. package segment/boundary compatibility strongly enough that composition/transitivity has the claimed type;
8. improve the final conditional NI theorem so it composes the actually landed pieces without claiming semantic premises have been proved.

Do not spend large effort proving routine algebra merely to increase theorem count. Prefer a few theorems that lock down the abstraction boundaries.

All Lean claims must be sorry-free and pass the repository audit.

## 11. Produce a canonicalization-readiness document

Create one synthesis document whose purpose is **not** to become canonical automatically. Its job is to tell the maintainer exactly what the canonical theory should now say.

It should contain:

### A. The final proposed theorem spine

A minimal set of definitions and major theorems, in dependency order.

For each object, identify its type.

For each theorem, state:

* hypotheses;
* conclusion;
* proof/evidence status;
* whether generic or realization-specific.

### B. The cleaned architecture

Ideally something no larger than:

$$
\text{Interactive history}
\to
\boxed{\text{Integrity + Robust Openness}}
\to
\mathcal O_P
\to
\boxed{\text{Progress interface}}
\to
\text{NI realization}.
$$

If you need more boxes, justify every one.

### C. Exact external bill

List assumptions which are intentionally not solved by the generic theory:
settlement trust, intervention semantics, normative scope, practical/counterfactual semantics, evaluator adequacy/non-capture, etc.

### D. Exact remaining research frontier

Only genuine research problems, not integration chores and not intentionally external premises.

### E. Canonicalization blockers

This should ideally be empty or very short.

A blocker means: "we do not yet know what the canonical mathematical statement should be," not merely "we have not proved or implemented every downstream application."

### F. Migration map

For each important current wiki concept/page, say:

* retain;
* redefine;
* merge;
* demote to realization/plugin;
* archive as superseded.

This is crucial: we want the next pass to be able to rewrite the canonical wiki mechanically from the mathematical state rather than rediscovering the theory.

## 12. Repository changes and final verdict

Make the repository changes needed to support the consolidation, including repairs to provisional Lean/interfaces and new consolidation documents/tests.

Do **not** rewrite the canonical wiki wholesale merely to make it agree with your new proposal unless the evidence is genuinely settled enough and repository conventions explicitly make that appropriate. The key deliverable is a state from which full canonicalization is safe.

At the end give a hard verdict in one of these forms:

### `READY FOR FULL CANONICALIZATION`

Use this only if you believe all major objects and theorem boundaries are now mathematically settled, even though some realization hypotheses or downstream research problems remain open.

### `NEARLY READY — BLOCKED BY: ...`

List only exact unresolved conceptual questions whose answer would change the canonical mathematical theory.

### `NOT READY`

Use this only if the consolidation reveals another major architectural problem.

The standard is not "everything is solved." The standard is:

> **Can we now state the generic legitimacy/normative-induction theory canonically, state the LI realization canonically as conditional where necessary, and name every remaining unsolved or external premise without expecting another conceptual reorganization?**

That is the target.
