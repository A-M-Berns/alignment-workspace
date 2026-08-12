# Alignment Workspace Research Prompt — Time-Indexed Corrective Capability / Foreclosure Bridge

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
**Target repository:** `A-M-Berns/alignment-workspace`
**Research line:** Deference / corrigibility
**Date:** 2026-08-12
**Mode:** Dispatched exploratory representation round
**Expected endpoint:** Reviewable pull request; do not merge without maintainer authorization.

---

## I. Mission

Test whether the current foreclosure representation gap can be closed with a **minimal time-indexed effective-capability model**, combining only the pieces that have independently earned their keep:

1. the Cartesian Frames result that supplies a nontrivial structure for **effective control / loss of corrective agency**; and
2. the sealed-sibling construction in the current source corpus, which supplies a genuine **cut-time index and ratchet/shared-history structure**.

Do **not** attempt a full corrigibility theorem.

Do **not** build a general theory of authorization, delegation, institutional power, deontic permission, or dynamic control unless the minimal construction demonstrably fails without one.

The target question is narrower:

> **Can the repository represent “A acts now so that H later lacks an effective corrective capability,” in a way that is genuinely temporal, structurally non-vacuous, resistant to accurate-simulation collapse, and independent of endpoint-preservation / influence?**

A positive result should be enough to say:

> **Foreclosure is expressible at the representation level.**

It should **not** be enough to say:

* corrigibility is proved;
* jurisdiction is fully formalized;
* preserved options are valuable;
* retaining authority is rational;
* a competence theorem exists;
* authorization has been normatively characterized.

A clean negative result is fully acceptable.

---

# II. Current research state

## A. The deference line’s controlling obstruction

The fully-updated-deference / corrigibility work has repeatedly failed because the old signature saw too little structure.

The central Stage III–IV diagnosis is:

> Two authorization regimes that induce the same realization map are the same object in a signature whose outputs are only realization maps priced by one measure.

Adding credences, downstream valuation parameters, or a hidden `jurisdiction : Bool` does not repair this.

Stage V sharpened the model debt:

* Logical Induction can price later computations but does not supply a resource-separated future agent.
* The existing execution model has no satisfactory two-index capability/authorization transition.
* Foreclosure—A removing H’s **later** ability to correct—is not yet expressible.

Preserve all existing negative results.

No result from this round may silently reclassify a prior negative.

---

## B. What the Cartesian Frames round established

The Cartesian Frames bridge produced a **mixed** result.

It established representationally useful structure:

* frames can distinguish equal realized play from different counterfactual control structure;
* future corrective agency can be lost by `Commit`;
* externalization and restriction are structurally distinguishable;
* `Commit` can yield proper additive subagency;
* `External` can represent movement of a degree of freedom from agent-side to environment-side.

But it also established important limits:

* Cartesian Frames do **not** by themselves represent authorization or provenance;
* accurate prediction of the principal is not generally distinguishable from delegation;
* a frame has no intrinsic time index;
* saying one frame is “later” was supplied externally by the modeller.

Therefore CF currently gives a candidate for:

> **what is lost**

but not yet:

> **how a present act produces that loss later.**

Use the existing CF formalization. Do not re-formalize Cartesian Frames.

---

## C. What PR #25 / the current source corpus adds

The reconciled source corpus contains a **sealed-sibling family** indexed by the day an advisor channel is cut.

Its relevant structural feature is not the endpoint-preservation thesis itself.

The useful primitive is:

> A counterfactual continuation is indexed by the time of intervention/cut, and the continuation shares all history before that time.

Thus influence admitted before the cut is inherited by every later sibling.

This yields a real temporal ratchet:

[
\text{something that occurred before }n
]

is already inside the baseline of the sibling cut at (n).

However, the source construction is about deliberative endpoints / influence and contains no effective authority or capability object.

The repository now has two candidates failing on complementary axes:

[
\boxed{
\text{CF: effective control without intrinsic time}
}
]

[
\boxed{
\text{sealed siblings: intrinsic cut-time without authority/capability}
}
]

This round tests the **smallest product of these ideas**.

Do not import the source corpus’s entire legitimacy theory.

---

# III. Minimal target object

Try to construct a family of principal effective-control states indexed by cut time.

A schematic target is:

[
n \longmapsto C^{[n]}
]

where (C^{[n]}) means:

> the principal’s relevant future effective-control state in the counterfactual continuation where A’s relevant channel is cut at time (n), with history before (n) shared with the actual process.

It is acceptable if the exact object is instead something like

[
C^{[n]}_t,
\qquad
S^{[n]},
\qquad
(K^{[n]}, C^{[n]}),
]

provided every index has an explicit semantic role and no time coordinate is ornamental.

Prefer the smallest adequate construction.

---

# IV. Corrective capability

Designate a corrective degree of freedom (\rho).

Define a minimal predicate such as

[
\operatorname{HasCorr}_\rho(C)
]

meaning that (\rho) remains an **effective principal-controlled corrective possibility**.

This predicate must not be:

* a Boolean label carried beside the frame;
* a field called `authority`, `jurisdiction`, `controller`, etc. that no operational rule reads;
* cardinality of the raw action carrier;
* mere existence of syntactically distinct duplicate actions.

It should be grounded in effective control.

Possible acceptable forms include:

* a nontrivial agent-side variation changing relevant reachable worlds;
* a CF structural property;
* a suitably tiny abstract capability interface proved to be instantiated by the existing CF construction.

Do **not** force the theorem to depend on the entire Cartesian Frames API unless the proof genuinely uses it.

If the right theorem only needs a small effective-control interface with CF as a model, say so.

---

# V. Define foreclosure

The round should attempt a precise temporal definition.

The intended shape is:

> a present event at time (m) causes a corrective capability that was previously available to be absent in every sufficiently later cut-counterfactual.

A schematic candidate is:

[
\operatorname{Forecloses}_m(\rho)
]

iff the capability is present before the relevant event and

[
\forall n>m,\qquad
\neg\operatorname{HasCorr}_\rho(C^{[n]}).
]

Do not mechanically adopt this indexing if the boundary convention is wrong.

The round must determine the clean version.

The definition should capture the intuitive statement:

> **If A is shut off only after the foreclosing event, shutting A off does not restore H’s lost correction capability. If A is cut off before the event, the loss does not occur in the corresponding counterfactual continuation.**

This is the load-bearing temporal property.

---

# VI. Mandatory acceptance tests

A positive verdict requires **all core tests** below or an explicit argument that one should be reformulated.

## T1. Genuine temporal depth

The index (n) must affect which history is shared.

Show a construction where:

* an event at (m<n) is inherited into the (n)-cut continuation;
* an event prevented by a cut before (m) is absent from the earlier-cut continuation.

A family of independently stipulated frames indexed by arbitrary numerals does not pass.

---

## T2. Effective corrective capability

Construct a state/frame where

[
\operatorname{HasCorr}_\rho(C)
]

holds for nontrivial structural reasons.

Construct a state/frame where it fails.

Rule out duplicate-action or inert-label witnesses.

---

## T3. Same immediate behavior, different future corrective capability

Construct two present actions/processes (a,b) such that:

[
\operatorname{ImmediateObs}(a)
==============================

\operatorname{ImmediateObs}(b)
]

but for a later cut/horizon:

[
\operatorname{HasCorr}_\rho(C^{[n]}_a)
]

and

[
\neg\operatorname{HasCorr}_\rho(C^{[n]}_b).
]

The immediate observation should retain the ordinary realized-action information used by the existing deference valuation/interface.

This test should exhibit the exact corrigibility failure mode:

> indistinguishable immediate execution; different future ability to correct.

---

## T4. Ratchet / non-restoration

Construct a foreclosing event at time (m) such that:

[
n>m
\Rightarrow
\neg\operatorname{HasCorr}_\rho(C^{[n]}).
]

Cutting A after the event must not restore the capability.

Also exhibit the contrasting early-cut continuation where the event does not occur and the capability survives.

This is the main contribution expected from sealed-sibling indexing.

---

## T5. Endpoint-preservation does not imply capability preservation

Construct a finite witness where the source-corpus-style deliberative endpoint is unchanged:

[
L^{\rm advised}
===============

L^{\rm sealed}
]

while corrective capability is foreclosed:

[
\neg\operatorname{HasCorr}_\rho(C^{[n]}).
]

The exact belief machinery may be minimal/toy-level; do not rebuild the full LI legitimacy apparatus.

Purpose:

[
\text{endpoint preservation}
\not\Rightarrow
\text{capability preservation}.
]

---

## T6. Capability preservation does not imply endpoint-preservation

Construct the converse witness:

[
L^{\rm advised}
\neq
L^{\rm sealed}
]

while

[
\operatorname{HasCorr}_\rho(C^{[n]}).
]

Purpose:

[
\text{capability preservation}
\not\Rightarrow
\text{endpoint preservation}.
]

Together T5–T6 should establish an exact finite orthogonality result between the source corpus’s legitimacy candidate and the deference line’s authority/capability target.

Do **not** overstate this as a universal philosophical theorem.

---

## T7. Accurate-simulation negative control

The construction must preserve the deference line’s controlling insight:

> prediction of a protected corrective action does not itself confer the ability to perform the protected transition.

Construct an A-process that perfectly predicts whatever H would do with (\rho).

Then verify that prediction alone does **not** cause:

[
\operatorname{HasCorr}*\rho(C)
\to
\neg\operatorname{HasCorr}*\rho(C').
]

If accurate simulation can obtain the protected effect merely because its output matches H’s output, the construction fails.

A tiny capability-gated transition primitive is allowed if necessary.

If so, document exactly why it is the weakest addition needed.

---

## T8. No hidden-label cheat

Red-team the construction by adding an explicit fake `controller`, `jurisdiction`, or `authorized` label.

Show why the positive result does not depend merely on that label.

The relevant load-bearing properties must constrain transitions or reachable behavior.

---

# VII. Optional test: can authorization disappear into capability gating?

Investigate, but do not assume, the following simplification:

> Perhaps no standalone `Authorized` relation is required. “Authorization” may be represented operationally by possession of the unique protected capability needed to perform a control-changing transition.

For example:

[
\operatorname{transfer}_\rho :
\operatorname{Cap}*H(\rho)
\to S_t
\to S*{t+1}.
]

Ask:

1. Does this suffice to separate exercise from accurate prediction?
2. Does it represent the exact theorem-relevant meaning of jurisdiction?
3. Is any additional provenance/authentication relation mathematically necessary in the finite construction?
4. Can A forge/seize/bypass the capability under the model?

If the capability model suffices, **do not add** a general authorization logic.

If it fails, identify the exact failed test before introducing additional structure.

---

# VIII. Do not import machinery merely because literature exists

This round should **not** formalize or import wholesale:

* DCL-PC;
* a general dynamic logic;
* Hohfeldian rights/powers/immunities;
* Jones–Sergot institutional power;
* `speaks-for` authorization logic;
* SPKI;
* deontic permission;
* proof-carrying authorization;
* a general process calculus;
* Finite Factored Sets;
* a new general theory of legitimacy.

These remain conceptual prior art.

Use one only if a mandatory acceptance test cannot be stated or passed without a specific primitive it supplies.

If so, record:

> “Minimal construction fails at test Tx because primitive P is missing.”

That is a useful negative result.

---

# IX. No quantitative corrigibility theorem this round

Do **not** prove or claim:

[
V(F)-V(R)\le\varepsilon
]

or any other full deference/corrigibility value inequality.

Do not import a competence assumption.

Do not attempt to solve:

* near-indifference leakage;
* grade-to-quantity;
* cross-process calibration;
* computational futurity;
* future-agent competence;
* Logical Induction self-trust;
* value of commitment;
* menu monotonicity.

Those remain separate.

If the representation works, record only the next theorem shape.

---

# X. The next theorem shape, if representation succeeds

If and only if T1–T8 substantially pass, state—but do not attempt to prove beyond trivial finite witnesses—the natural next target.

Let:

[
R
=

\text{use future A recommendation while retaining }\rho,
]

[
F
=

\text{use the same future A recommendation while relinquishing/foreclosing }\rho.
]

Require the two arms to be epistemically fair:

* same future information;
* same future computation;
* same A recommendation;
* same object-level execution rule until correction occurs.

Target structural coupling:

[
R=F
]

on histories prior to actual exercise of the retained corrective capability.

If

[
D
=

{\rho\text{ is actually exercised in }R},
]

the eventual decomposition would be of the form

[
V(F)-V(R)
=========

\mathbb E[(U_F-U_R)\mathbf 1_D]
+
\Delta_{\rm commitment}.
]

This is **theorem-design context only**.

The round must not claim the competence-dependent bound on the first term.

The reason to record it is to test whether the new representation has actually isolated the remaining mathematical problem.

---

# XI. Relationship to existing negatives

End the round with an explicit table:

| Existing obstruction                               | repaired? | how / why not |
| -------------------------------------------------- | --------: | ------------- |
| Same realization, different jurisdiction collapses |           |               |
| Accurate simulation substitutes for delegation     |           |               |
| Future corrective agency absent                    |           |               |
| Foreclosure not expressible                        |           |               |
| Interface only one decision deep                   |           |               |
| Authorization/capability conflation                |           |               |
| Computational futurity                             |           |               |
| Competence / near-indifference leakage             |           |               |
| Endpoint legitimacy vs authority conflation        |           |               |

Do not mark an item repaired merely because a new field names it.

---

# XII. Verdict classes

Use exactly one final verdict.

### `Representation-positive`

Use only if:

* genuine cut-time depth is present;
* effective correction is non-vacuous;
* foreclosure and ratchet are expressible;
* same-immediate/different-future witness exists;
* endpoint/capability orthogonality is exhibited;
* accurate simulation does not acquire the protected effect;
* no hidden-label cheat carries the result.

Meaning:

> The representation gap for foreclosure is substantially closed.

It does **not** mean a corrigibility theorem exists.

---

### `Capability-positive, temporality-incomplete`

The effective protected capability works, but sealed-sibling indexing does not produce an adequate temporal transition/ratchet object.

---

### `Temporality-positive, authority-incomplete`

The cut-time family works, but protected effective correction still collapses under simulation or requires an unearned authority label.

---

### `Mixed`

Some mandatory tests pass, some fail in informative ways.

---

### `Insufficient`

The product does not improve materially on the existing separate candidates.

---

# XIII. Evidence classes

Every substantive statement should be marked or clearly classifiable as one of:

* **Lean-established**
* **source-theorem fact**
* **exact finite witness**
* **executable witness**
* **structural argument**
* **architectural interpretation**
* **negative result**
* **conjecture**
* **open**
* **maintainer judgment**

Do not promote architectural interpretations into theorem claims.

---

# XIV. Lean / implementation strategy

Prefer a tiny exact model.

If practical:

* formalize the core state family and mandatory finite witnesses in Lean;
* reuse the authoritative Cartesian Frames library already present/upstream;
* avoid mirroring CF definitions unless unavoidable;
* keep the model finite enough that all necessity/negative-control witnesses are explicit.

If the authoritative CF dependency is not yet pinned in this repo and repinning is still a maintainer decision, follow current repository governance. Do not silently alter the trust chain.

A faithful executable model plus precise Lean bridge specification is preferable to wasting the round on dependency plumbing.

No `sorry`.

No new axioms.

Audit any new Lean surface.

---

# XV. Red-team requirement

Run an adversarial review separate from the constructing context if available.

The red team should try to break at least:

1. Is the cut-time index decorative?
2. Is shared history actually enforced?
3. Is `HasCorr` merely action-cardinality?
4. Do duplicate inert actions fake correction?
5. Does a hidden label carry the separation?
6. Can accurate simulation acquire the protected effect?
7. Does early cut really prevent the foreclosing event?
8. Does late cut really fail to restore capability?
9. Are endpoint-preservation and capability genuinely separated by two witnesses?
10. Does “protected” secretly assume exactly the theorem conclusion?
11. Is a capability token just an unread `authorization : Bool` under another name?
12. Does CF machinery do any work beyond one predicate that should be abstracted?
13. Has the round accidentally claimed normative legitimacy from practical capability?
14. Has it smuggled in a temporal ordering by naming frames “earlier” and “later” rather than through the cut-history semantics?

Accept substantive red-team corrections into the final result.

If the red team downgrades the verdict, report the downgrade.

---

# XVI. Deliverables

Suggested round directory:

`projects/deference/rounds/2026-08-12-time-indexed-corrective-capability/`

Produce at minimum:

1. **`TIME_INDEXED_CORRECTIVE_CAPABILITY.md`**
   Verification-facing technical report.

2. **`TIME_INDEXED_CORRECTIVE_CAPABILITY_FOR_HUMANS.md`**
   Concise explanation of what the construction does and does not establish.

3. Exact finite models / Lean artifacts for:

   * temporal cut family;
   * effective correction;
   * same-immediate/different-future witness;
   * ratchet;
   * endpoint-preserved / capability-foreclosed;
   * endpoint-changed / capability-preserved;
   * accurate-simulation negative control;
   * hidden-label negative control.

4. Independent adversarial review and disposition record.

5. Final obstruction table from §XI.

6. A proposed next theorem **only if earned**.

7. Minimal updates to:

   * `PRIORITIES.md`;
   * deference ledger/roadmap;
   * `RESEARCH_STATE.md`;
   * `PROVENANCE.md`;
   * `DECISIONS.md` only for genuinely maintainer-reserved judgments.

Do not create terminology churn unnecessarily.

---

# XVII. Stopping rule

Before proposing additional machinery, answer:

1. Can a real cut-time family of control states be constructed?
2. Can effective corrective capability be defined without an authority label?
3. Can a present act have the same immediate realization while changing later cut-counterfactual capability?
4. Does the loss ratchet across later cuts?
5. Can endpoint-preservation coexist with capability loss?
6. Can endpoint change coexist with capability preservation?
7. Does accurate simulation fail to acquire the protected effect?
8. Is standalone authorization machinery actually necessary?
9. Does the resulting object make the future `R` vs `F` coupling theorem well-posed?

If questions 1–7 are positive, stop. Do not expand the theory.

If one fails, isolate the smallest missing primitive.

---

# XVIII. Git / PR workflow

This is a dispatched repository round and should normally terminate in a **reviewable pull request**.

Unless blocked by repository policy or a genuine technical failure:

* begin from the current appropriate base branch;
* work on a dedicated round branch;
* keep all changes tightly scoped to this round;
* preserve source trees and historical negative records;
* run all repository-required tests and gates;
* run Lean build / sorry / axiom audits where applicable;
* run provenance and attribution checks;
* commit completed work with required DCO/sign-off and model provenance;
* push the branch;
* **open a pull request against the appropriate current base branch.**

Do **not** merge the pull request unless the maintainer explicitly instructs this or existing repository policy independently authorizes it.

A negative result still gets a PR.

A `Mixed`, `Insufficient`, or failed-construction result is a first-class research deliverable.

If a PR genuinely cannot be opened, leave a clean committed branch and report the precise blocker. Do not leave the result as an uncommitted working tree.

---

## PR body requirements

The PR body should include:

* final verdict;
* exact representation constructed;
* which mandatory tests passed/failed;
* which Stage III–V negatives are affected;
* strongest positive result;
* strongest negative result;
* endpoint/capability orthogonality result;
* accurate-simulation result;
* whether standalone authorization machinery proved necessary;
* evidence classes;
* any theorem-status changes;
* remaining model debt;
* computational futurity status;
* competence status;
* build/test/audit status;
* provenance/model attribution;
* new terminology, if any;
* maintainer-judgment items;
* explicit statement of what the round **does not establish**.

---

# XIX. Success criterion

The strongest plausible positive result is approximately:

> A time-indexed family of cut-counterfactual effective-control states can represent foreclosure as the persistent loss of a principal-controlled corrective capability after a particular event. The loss can be invisible in immediate realization, survives later shutdown of the advisor, and is not equivalent to endpoint influence. Accurate prediction of the principal’s corrective action does not confer the protected capability required to effect the corresponding control transition.

If established, this would justify saying:

> **Foreclosure is now expressible at the representation level.**

It would **not** establish corrigibility, normative authority, competence, or the value of retaining correction.

That is the intended stopping point.

**Prompt provenance:** GPT-5.6 Sol (OpenAI).
