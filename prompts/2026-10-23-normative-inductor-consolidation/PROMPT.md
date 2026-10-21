# PR #129 — Final Normative Inductor Consolidation

Continue working on the existing branch for **PR #129** in `A-M-Berns/alignment-workspace`. Do not merge the PR.

The previous integration round was successful. It produced a substantially unified construction:

- A canonical `NormState.bundle` with grounded survivor semantics.
- A warrant enforcer operating on the actual augmented deductive market.
- An odds-based liability bound and preservation of Logical Induction.
- Finite-time rowwise conformance at the realized market.
- Certificate transport from enforced rows to displayed prices.
- A nonconstant soft-gate adapter with derived `PracticalUptake` and Progress.
- A nontrivial Lean witness discharging computability and liability.

**Do not repeat that work or start another broad research round.**

Our objective is to make the existing result a coherent, mathematically honest, and externally intelligible endpoint for this PR.

The standard is:

> After merging, we should have one canonical conditional Normative Inductor theorem, one convincing dynamic example, and an architecture whose remaining limitations are explicit rather than concealed by interfaces.

I want you to focus on four specific matters.

## 1. Clarify admission, entitlement, and authorization

The first remaining issue is the gap between the intended normative interpretation and the existing formal admission interface.

Currently, `WarrantInductor.Admission` primarily establishes that every warrant occurrence maps to an exposed occurrence in the accounted obligation state.

This is a useful provenance link, but it does not establish that the warrant was legitimately incurred, faithfully expresses the originating obligation, or was authorized for enforcement.

At the same time, the framework has `NormState.Licensed` and the authorization of verdict-selection events, but the market enforcer does not consume those verdict licences.

These are different concepts, and we should not conflate them.

### Tasks

First, identify and distinguish the following roles:

1. **Historical provenance:** which accounted occurrence a warrant originates from.
2. **Warrant admission or entitlement:** what authorizes this particular substantive constraint to participate in the market.
3. **Verdict support and licensing:** what authorizes a particular certificate-backed selection of a credal verdict.
4. **Operative enforcement:** what makes the admitted constraint influence the market.

Determine whether the present `Admission` structure should retain its name or be renamed to reflect its weaker contents.

Consider whether an explicit, parametric admission/entitlement condition would be appropriate, with a theorem saying that the compiler enforces only admitted warrants.

This condition should not purport to *solve legitimacy*. It may be a typed external input whose intended semantics are stated clearly.

However, it should be more than a rhetorical label for an arbitrary origin mapping.

In particular, investigate whether the existing legitimate-evolution, provenance, or entitlement machinery can supply a more meaningful interface without undertaking a new theory of normative legitimacy.

**Do not make verdict licensing a prerequisite for enforcing a warrant unless there is a substantive reason to do so.** A licence to announce or select a verdict is not automatically the same as authority to introduce a constraint.

The desired outcome is a clean specification of how a legitimately incurred normative commitment is admitted to the system, and which parts of that specification are actually proved.

If making admission substantive requires future legitimacy research, state that openly and preserve an appropriately named assumption.

## 2. Make compilation failure accountable

The second issue concerns `WarrantInductor.compileAt`.

Currently, an unsuccessful feasibility check produces the empty bundle, withholding enforcement.

This is a reasonable safety behavior for the trader. It avoids attempting to enforce an inconsistent constraint system.

But an empty enforcement bundle does not explain what happened to the obligations that generated it.

The existing Normative Inductor architecture requires something stronger: when a joint constraint cannot be compiled or serviced, the system should not silently erase the corresponding commitments or pretend they were discharged.

### Tasks

Investigate the current failure path and determine the smallest clean way to distinguish:

- No operative obligations.
- A successful compilation of operative obligations.
- Obligations present but enforcement withheld because compilation or feasibility failed.

Ideally, compilation should produce a typed outcome, with successful compilation carrying the enforced bundle and unsuccessful compilation carrying enough information to account for what was not serviced.

Use the existing compiler-conflict and Farkas-certificate machinery where applicable. Do not invent a second conflict theory merely to satisfy this task.

The central desiderata are:

**Conservation:** withholding force must not extinguish an obligation from the accounted record.

**Transparency:** the construction must distinguish the empty region, a failed certificate or witness check, and genuinely having no constraints to enforce.

**Evaluation:** obligations not serviced should remain eligible for residual-mass accounting, rather than disappearing because no enforcement position was created.

**Preservation:** the market's LI-preservation guarantee should survive legitimate withholding of enforcement.

Do not require the enforcer to keep trading against an infeasible region. The purpose is to account for failure, not to force inconsistent commitments into a market.

If a fully unified accounting theorem would require substantial new machinery, implement the smallest principled representation and state the remaining interface obligation explicitly.

## 3. Strengthen the dynamic witness

The current witness is significantly better than its predecessor, but two limitations remain.

First, its principal warrant is undercut at date 5, removing the dependent strength occurrence. When the conclusion is refuted at date 8, the strength occurrence is no longer active.

Thus the fixture does not directly exhibit **rebuttal of a still-active conditional warrant**.

Second, the response adapter is evaluated on the principal decision at date 4, then on a different decision involving the independent \(Z\) warrant at date 9.

This demonstrates continued responsiveness to a surviving commitment, but not how the same decision question changes when its supporting warrant is revised.

### Tasks

Add the smallest informative dynamic test that addresses these issues.

I suggest separating the scenarios if that produces cleaner mathematics:

**Scenario A: Undercutting.**

Keep the existing example in which a warrant's applicability is defeated and its dependent strength constraint ceases to be operative.

Demonstrate precisely what guidance is lost, what survives, and what changes in the space of admissible credences.

**Scenario B: Direct rebuttal.**

Construct a companion path in which the conditional warrant remains active until its consequent is refuted.

Demonstrate:

1. The warrant is operative before the refutation.
2. The consequent settles false while the relevant antecedent can remain true.
3. The conditional row is withdrawn by the rebuttal semantics.
4. Withdrawal prevents the unwarranted contraposition that would otherwise suppress the antecedent.
5. The remaining constraints are feasible and continue to be enforced.
6. The financial liability guarantee survives the revision under explicitly demonstrated conditions.

Where possible, examine **the same decision question before and after revision**, rather than substituting a different independent question.

The ideal result would show that a previously warranted behavioral recommendation ceases to be warranted, or that a newly supported response becomes appropriate.

But be careful:

**Removing a reason to act does not prove that the agent must reverse its action.**

Do not force a behavioral reversal by changing the declared adequate set arbitrarily between dates. If the same-question adapter can no longer guarantee the original recommendation, that is already a meaningful result.

Distinguish:

- The constraints actually changing.
- The region of admissible prices changing.
- The guarantees about the adapter changing.
- The adapter's actual behavior changing.

Prove the strongest claim justified by the construction, without conflating these.

Retain the existing witness's actual-market results. Do not replace them with a stipulated clearing-price history.

The preferred endpoint is a compact pair of complementary examples, not an enormous collection of fixtures.

## 4. Reconcile the canonical mathematical exposition

The wiki and older architecture still describe the Normative Inductor primarily as a projection-based enforcer with public defect

\[
d_t=\operatorname{dist}_\infty(P_t,K_t).
\]

The new warrant construction instead uses a rowwise violation-proportional trader and establishes per-row conformance. Its adapter's operative defect is based on certified inadequate-score excess.

These are related, but they are not identical.

The discrepancy is mathematically legitimate; the documentation should no longer leave readers guessing about it.

### Tasks

Produce a coherent description of the current architecture that distinguishes:

- The **general Normative Inductor interface**, which should be implementation-independent.
- The **projection-based realization**, with its distance-to-region guarantee.
- The **rowwise warrant-enforcement realization**, with its per-row tolerance and certificate-mass transport.
- The **decision adapter**, which consumes the relevant quantitative guarantee and derives a practical certificate.

Do not declare one realization obsolete without a mathematical reason.

If a general interface accommodates both, state it. The right abstraction might concern a quantitative defect together with a certified bound on the response-relevant functionals, rather than require every realization to provide the same geometric distance.

Prefer using the existing Progress and practical-certificate interfaces rather than introducing another redundant abstraction.

Ensure that `wiki/Normative-Inductor.md`, `wiki/Normative-Induction.md`, `wiki/Normativity.md`, the theorem spine, and the new `THEOREM_STORY.md` tell a consistent story.

In particular, distinguish the claim

> Normative warrants constrain the prices of the market,

from

> Normative warrants produce warranted guidance about the behavior of the decision adapter.

The first follows from enforcement under feasibility and affordability. The second additionally requires substantive adequacy semantics and the appropriate certificates.

Neither independently establishes that the admitted warrants are morally correct.

## 5. Audit the flagship theorem

Before concluding, reread the exact statement and proof of `WarrantInductor.warrant_inductor` and its instantiation in `WarrantInductorWitness`.

Ask whether every assumption is indispensable, meaningful, and correctly categorized.

In particular:

- Is the admission hypothesis substantive, or is it merely an arbitrary labeling of occurrences?
- Do the enforced rows and the adapter's certificates really refer to the same state and market?
- Are the quantified normative states temporally unconstrained? If so, does the theorem's description acknowledge that it is pointwise with respect to an externally supplied state sequence?
- Does the feasibility-withholding policy make any advertised conformance guarantee conditional on compilation success?
- Is the liability guarantee properly distinguished from computability?
- Are `Excludes` and `Margins` checkable geometric conditions, and where does their normative meaning enter?
- Is Progress genuinely informative in the witness, with positive evaluation mass, meaningful losses, and nontrivial response probabilities?
- Are any conclusions only restatements of assumptions under changed notation?

If there is a clean opportunity to strengthen the main theorem, take it.

If the theorem is already at the right level, **do not complicate its signature simply to add more hypotheses and conclusions**.

The goal is a more meaningful result, not a longer one.

## 6. Scope and stop conditions

Keep this round narrow.

Do not undertake any of the following unless a genuine defect in the current theorem makes it necessary:

- General affordability across arbitrarily many reopenings.
- A complete theory of legitimate warrant generation.
- Learning of warrant strengths from experience.
- Full convergence of normative verdicts.
- Multi-reasoner convergence.
- LI+BRIA decision theory.
- A full corrigibility theorem.
- General distance-to-region estimates for arbitrary polyhedra.

These remain legitimate research questions, but they are not required to merge this PR as the first conditional end-to-end construction.

Follow `AGENTS.md` and repository layer restrictions. Keep specification-layer changes out of the branch unless explicitly authorized; propose necessary maintainer decisions rather than silently making them. Preserve prior registered results, proof provenance, and Lean's kernel-checked status.

Avoid adding new definitions if the existing theory can express the required distinction.

A small counterexample or an exact statement of an unresolved obstacle is preferable to an unjustified generalization.

## 7. Deliverables

Produce:

1. **The final formal construction.** Any necessary Lean changes to admission, accountable compilation, dynamic examples, or the theorem interface.

2. **A revised end-to-end witness.** It should distinguish undercutting from direct rebuttal and make the effect on normative guidance clear.

3. **A short canonical theorem statement.** Give the main mathematical result in paper-ready form, with a readable explanation of its genuinely substantive content.

4. **A precise assumption ledger.** Separate facts established by market mathematics, assumptions about warranted normative states, assumptions about adequacy, and conditions specific to the witness.

5. **Consistent wiki and theorem-story documentation.** One account of the architecture, with the projection and rowwise realizations distinguished.

6. **A final merge review.** State what was repaired, what remains genuinely open, what the mathematical results now warrant claiming, and whether PR #129 is ready to merge.

Run the full Lean build, axiom audit, tests, claims checker, and workspace-state checker. Report exact results. Do not silently promote claim statuses.

## 8. Final standard

I do **not** want another round that finds five adjacent open problems and pursues all of them.

I want this PR to have a clear, defensible stopping point.

The substantive result we are trying to land is:

> A system of defeasible normative warrants, admitted under an explicitly specified normative interface and revised through a coherent defeat-and-settlement process, can be compiled into enforceable market constraints. Under feasible and affordable enforcement, the resulting reasoner preserves Logical Induction, satisfies finite-time quantitative bounds on its warranted credences, and—with a certified decision adapter—achieves a corresponding bound on practical normative failure.

That is a real result, even though legitimate admission, substantive normative truth, and the general dynamics of warrant learning remain open.

Push toward making that statement exactly accurate, in the mathematics and in the exposition.

**Then stop.**

At the end, give your considered merge recommendation, not merely a statement that the tests passed.
