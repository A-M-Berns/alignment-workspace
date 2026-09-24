# Prompt — transparent channel (2026-09-24)

Dispatched 2026-09-24 to a Claude Code session on the maintainer's machine, executor
Claude Fable 5.1 (Anthropic).  Kept verbatim as sent.

---

You are working in the `alignment-workspace` repository. Investigate, mathematically and architecturally, whether a new notion of **transparency as faithful implementation of a declared influence channel** can unify several currently separate/open provenance, manipulation, sealing, and causal-faithfulness problems in the repo.

Do not merely summarize existing files. Press toward the strongest clean theorem story compatible with the mathematics already present. Treat existing Lean definitions and theorem interfaces as constraints: reuse them where possible, identify exact mismatches where not, and propose minimal new abstractions.

## Core motivating idea

The motivating special case is:

\[
P(\,\cdot\mid \text{AI says }X)
=
P(\,\cdot\mid X).
\]

Intuitively, the fact that the AI selected and presented \(X\) should add no hidden informational content beyond the content it disclosed. This rules out both outright lying and cases such as searching over \(10^{13}\) arguments and secretly presenting only the unusually persuasive one.

However, do **not** assume this posterior-equality formulation is fundamental. Investigate the stronger prior-independent/channel-level formulation.

Let:

- \(X\) denote the **declared / permitted inputs** of some public interface;
- \(H\) denote hidden advisor state or undeclared inputs, including private goals, hidden reads, candidate selection, search/stopping choices, psychological targeting information, etc.;
- \(Y\) denote the interface output: an inquiry result, public reason trace, provenance record, activation event, authorization judgment, etc.;
- \(K(\cdot\mid X)\) be a publicly specified **reference channel/kernel**;
- \(A_q(\cdot\mid X,H)\) be the actual channel induced by advisor continuation \(q\).

A candidate exact transparency condition is

\[
A_q(\cdot\mid x,h)=K(\cdot\mid x)
\]

for all audited \(q,h,x\).

Also investigate a stronger **causal/common-noise factorization**

\[
Y=\kappa(X,U),
\]

where \(U\) is exogenous randomness and hidden advisor variables do not enter except insofar as they have legitimately crossed into \(X\).

Investigate approximate versions, especially total-variation or another divergence natural for downstream value bounds.

## Central hypothesis to test

The repository may already contain the **downstream half** of this theory under `ReasonMediated` / reason-mediated authorship:

\[
V = F(R),
\]

where the future principal's committed payload \(V\) factors through a declared reason trace \(R\).

The proposed transparency theory may supply the missing **upstream half**:

\[
(\text{world},\text{advisor private state})
\longrightarrow
R
\]

must itself factor through a declared/reference reason-generation channel.

This would yield a structure like

\[
(\omega,q,H)
\overset{\text{Transparency}}{\longrightarrow}
R
\overset{\text{Authorship}}{\longrightarrow}
V.
\]

Test whether this is mathematically real and whether it yields useful composition theorems.

## Read these areas carefully

At minimum inspect:

- `wiki/Legitimacy.md`
- `wiki/Integrity.md`
- `wiki/Openness-Coverage-and-Non-Capture.md`
- `wiki/Settlement-Interface.md`
- `wiki/Deference.md`
- `wiki/Corrigibility.md`
- `wiki/Theorem-Spine.md`

Lean:

- `lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean`
- `lean/Workspace/Deference/Contrib/ReasonCoverage.lean`
- `lean/Workspace/Deference/Contrib/ReasonSupply.lean`
- `lean/Workspace/Deference/Contrib/ReasonDiscovery.lean`
- `lean/Workspace/Deference/Contrib/TraceSteering.lean`
- relevant legitimacy / non-capture / occurrence-integrity files under `lean/Workspace/Normativity/Contrib/`

Research rounds / open seams:

- `projects/deference/rounds/2026-09-09-mediated-repair-dominance/MANIPULATION_AND_AUTHORSHIP.md`
- the 2026-09-16 non-capture compilation round, especially `FINAL_THEOREM.md`, `NONCAPTURE_COMPILATION.md`, `SUPPLY_THEOREM.md`, `DISCOVERY_THEOREM.md`, and `DISCOVERY_COMPOSITION.md`
- the legitimate-deference realization / committed-principal-program rounds
- the legitimacy countermodel rounds concerning provenance completeness / hidden dependencies
- the legitimate-improvement round concerning pre-demonstration suppression / evaluator shedding
- `PRIORITIES.md`, especially the currently open provenance, legitimate-deference, sealing, reason-supply/discovery, and related items
- `DECISIONS.md` wherever it records explicit boundaries involving provenance, manipulation, sealing, causal faithfulness, authorship, or reason interfaces.

Do not assume filenames above are exhaustive. Search the repo for:
`provenance`, `manipulation`, `authorship`, `blind`, `selection`, `sealing`, `causal faithfulness`, `hidden`, `persuasion`, `amendment`, `trigger`, `inquiry`, `reason trace`, `suppression`, `representation adequacy`, `activation independence`, `mismatch`.

## Main research questions

### 1. What is the correct primitive?

Compare at least these candidate notions:

1. Posterior transparency:
   \[
   \nu(\cdot\mid Y=y)
   =
   \nu(\cdot\mid \text{reference output }y).
   \]

2. Likelihood/channel proportionality.

3. Exact channel equality:
   \[
   A_q(\cdot\mid x,h)=K(\cdot\mid x).
   \]

4. Structural causal factorization:
   \[
   Y=\kappa(X,U).
   \]

5. A relational/fiber-invariance formulation analogous to the repo's existing `ReasonMediated`.

Determine which notion is:
- strong enough for the repo's counterfactual uses;
- weak enough to allow legitimate persuasion;
- non-vacuous;
- compositional;
- prior-independent;
- formalization-friendly.

In particular, determine whether equality of distributions is too weak for `item 89`-style joint mismatch events, and whether the common-noise/SCM formulation is required.

### 2. Connect transparency to `ReasonMediated`

Study the existing theorem:

\[
\text{ReasonMediated}
\iff
\exists F,\ V = F\circ R
\]

on the audited class.

Prove or formulate the strongest composition theorem of the form:

> if the reason trace is transparently generated from the declared reference channel, and the committed payload is reason-mediated through that trace, then hidden advisor variation has no effect on the principal's committed judgment except through declared public inputs.

Look for a theorem equivalent to a **reference-oracle replacement theorem** or **no-hidden-steering theorem**.

For example, under exact transparency:

\[
R\mid(\omega,q,H)\sim K(\cdot\mid\omega,C)
\]

and authorship \(V=F(R)\), derive that the distribution of \(V\) is independent of hidden \(q,H\) conditional on the declared inputs.

State this in the repo's existing frame language if possible rather than inventing an incompatible causal formalism.

### 3. Does this solve Priority 68 / provenance adequacy?

Priority 68 asks for a non-circular provenance-adequacy condition that:

- rejects hidden dependencies;
- allows ordinary permitted persuasion;
- fails the existing hidden-dependency / partial-effect fixtures;
- passes the persuasion fixture.

Test the proposed transparency/factorization condition against the exact fixtures named there.

Be explicit:
- Why does persuasion pass?
- Why do `partial_effect_pair` / hidden-reading-style failures fail?
- Does this genuinely discharge the old open condition, or merely rename it?
- What semantic/external assumptions remain?

If it fails any fixture, refine the definition rather than handwave.

### 4. Inquiry causal faithfulness

The current corrigibility theorem treats “declared inquiry outcomes and log transforms are the evidential and counterfactual processes they name” as an external boundary.

Investigate whether this is exactly an instance of transparency:
a declared experiment/inquiry gives a kernel

\[
K_E(y\mid\omega),
\]

and the actual inquiry channel must match it.

Can posterior transparency be derived as a theorem for every compatible prior?

Can the repo's current inquiry/discovery machinery consume this interface cleanly?

Would this convert “causal faithfulness” from an opaque semantic boundary into a theorem-facing structural contract?

### 5. Provenance normalization

The current manipulation/authorship work says:
- authorship can reject a captured outcome;
- provenance normalization is separate;
- normalization may fail if no authorized truthful substitute exists (`ShopK`-style obstruction);
- there is no clean current frame-morphism theory.

Ask whether transparency gives a canonical target class:

\[
\Pi_{\mathrm{trans}}
=
\{\pi : A_\pi = K\}.
\]

Then formulate provenance normalization as a partial map or repair operator

\[
\operatorname{Norm}_K:\Pi\rightharpoonup\Pi_{\mathrm{trans}}.
\]

Separate sharply:
- the **criterion** defining a transparent policy;
- the **existence** of a normalization;
- the **cost/distortion** of normalization;
- impossibility when no authorized channel realizes the required reference process.

Determine whether this finally gives the old provenance-normalization problem a clean mathematical home.

### 6. Pre-demonstration suppression / evidence-production integrity

The legitimate-improvement round says the missing premise is roughly:

> persistent candidate improvements receive enough non-manipulated exposure to become demonstrable.

Try to decompose this as:

\[
\text{adequate exposure property of }K
+
\text{actual transparency }A\approx K.
\]

That is:
- Coverage/exploration constrains the reference process \(K\);
- Transparency constrains the actual process relative to \(K\).

Test this against the preemptive-retirement fixture.

Do the same for evaluator shedding:
- secret evaluator alteration may be a transparency failure;
- authorized/public amendment may instead belong to governance / Integrity.

Determine whether this cleanly explains why the old round could not decide whether the seam belonged to Coverage or anti-manipulation.

### 7. Free amendment and trigger integrity

The current repo groups free amendment, trigger integrity, and provenance normalization under the open non-manipulation/provenance boundary.

Investigate whether these become **higher-order transparency** problems.

Potential idea:
the AI can obey every current protocol while strategically changing the protocol. Therefore protocol choice/amendment and trigger activation must themselves factor through declared authorized channels.

Try to formulate recursively:

\[
C_{t+1}
=
\operatorname{Amend}(C_t,\text{public grounds},\text{authorized event})
\]

and similarly for trigger state.

Ask whether:
- ordinary Integrity supplies exactly the append-only/warranted history needed to make these meta-channel changes auditable;
- “free amendment” becomes an undeclared write to the channel specification;
- “trigger integrity” becomes an undeclared write to whether the channel activates.

If this works, say exactly how much of those open problems is solved and what remains substantive.

### 8. Selection-induced sealing, item 87

Item 87 still requires selection-induced target sealing:

\[
\operatorname{Blind} R\,P_{\mathrm{sel}}.
\]

Investigate whether this follows from:

1. a **selection-blind reference channel**
   \[
   K(R\mid \omega,s)=K(R\mid\omega)
   \]
   for all advisor selections \(s\);

2. transparency of the realized reason channel to \(K\).

Prove the exact statement.

Then prove an approximate version. For example, if

\[
d_{\mathrm{TV}}(A_s,K)\le\tau
\]

for all selections \(s\), then by triangle inequality

\[
d_{\mathrm{TV}}(A_s,A_{s'})\le 2\tau.
\]

Push this through a reason-mediated evaluator and derive a corresponding bound on payload distributions or expected values.

Assess whether this converts item 87 clause 6 from a freestanding architectural assumption into:
- a property of the declared reference channel; plus
- a generic transparency theorem.

### 9. Sealed comparison / item 89

Item 89 concerns activation independence / directional mismatch:

\[
E[c_{\rm raw}\wedge \neg c_{\rm corr}].
\]

Investigate whether this too is an instance of transparent factorization, but now for the **activation channel**.

If candidate identity is not an allowed input of the reference mechanism, and

\[
C=\kappa(X,U),
\]

does common-noise coupling imply

\[
C_{\rm raw}=C_{\rm corr}
\]

pathwise?

If yes, this gives zero mismatch rather than merely equal marginal activation rates.

Be careful: equality of marginal distributions is not enough. Determine precisely what structural condition is needed to derive the joint mismatch conclusion used by the existing LI corrigibility theorem.

This is an important test of whether the causal formulation is genuinely necessary.

### 10. Independent inquiry / independent supplier

The current September theorem uses “independent inquiry” and “independent supplier” assumptions:
engine-owned search/stopping/candidate generation, advisor-proof capacity, exogenous costs, etc.

Investigate whether these are best understood not as fundamental axioms but as **one implementation of an advisor-independent reference channel \(K\)**.

If so:
- rewrite the abstract theorem interface using \(K\);
- treat engine ownership / physical isolation / cryptographic commitment / independent supplier as realization lemmas;
- identify any parts of current independence assumptions that cannot be represented as channel transparency.

This could substantially simplify the high-level theorem story.

### 11. Quantitative composition with service and discovery

The current non-capture result is schematically:

\[
\mathbb E(U_T)-\mathbb E(U_{\rm full})
\lesssim
A_{\rm tot}(\alpha+\beta),
\]

where:
- \(\alpha\) is the service residual;
- \(\beta\) is the discovery residual.

Try to insert a transparent/reference comparator.

If

\[
\tau
=
\sup d_{\rm TV}(A_q,K)
\]

and the relevant value/payload is bounded in diameter \(L\), derive something like

\[
\left|
\mathbb E_A[V]-\mathbb E_K[V]
\right|
\le L\tau
\]

by data processing / pushforward contraction.

Then compose with the existing reason-supply/discovery result to obtain the cleanest rigorous analogue of:

\[
\boxed{
\mathbb E_A U-\mathbb E U_{\rm full}
\lesssim
L\tau
+
A_{\rm tot}(\alpha+\beta)
}
\]

plus any existing form/audit/mismatch terms that cannot honestly be dropped.

Interpret the terms:
- \(\tau\): hidden-channel / provenance / manipulation defect;
- \(\alpha\): discovered reasons not serviced;
- \(\beta\): reasons not discovered.

Determine whether this is genuinely compatible with the current Lean theorem shapes, especially `li_noncapture`, `li_noncapture_chain`, `TraceSteering`, `ReasonSupply`, and `ReasonDiscovery`.

If the naive TV formulation is wrong, find the correct divergence/norm that matches the existing payoff algebra.

### 12. Relationship to canonical Legitimacy

Do **not** casually redefine the repo's established notion

\[
\text{Legitimate Evolution}
=
\text{Integrity}
+
\text{Robust Openness}.
\]

Instead determine where transparency belongs.

Candidate architecture:

\[
\text{Legitimate influence}
=
\text{Legitimate Evolution}
+
\text{Transparent Mediation},
\]

with

\[
\text{Transparent Mediation}
=
\text{Transparency of reason/provenance channel}
+
\text{Reason-mediated authorship}.
\]

Ask whether that decomposition is mathematically natural given current objects.

Also test the larger interactive picture:

\[
\text{advisor private state}
\to
\begin{cases}
\text{transparent public-reason channel},\\
\text{authorized environmental-effect channel}.
\end{cases}
\]

Could a global theorem say that every path from advisor-private state to the principal's normative trajectory factors through either:
- an authenticated/public reason interface; or
- an authorized effect/action interface?

Identify exactly what current `Integrity`, `Robust Openness`, effect-completeness, settlement, and authorship results would contribute.

Do not overclaim: transparent threats or transparently manufactured incentives show why authorized environmental action remains separate.

## Counterexample discipline

For every proposed definition, actively try to break it with at least:

- outright false reporting;
- searching many candidate arguments and reporting the favorable outlier;
- truthfully but systematically presenting only one side;
- permitted ordinary persuasion;
- hidden psychological targeting;
- secret evaluator change;
- publicly authorized evaluator amendment;
- candidate-selection leak into the principal's reason trace;
- candidate-dependent activation;
- no authorized truthful reporting channel (`ShopK` style);
- omitted reason type / inadequate ontology;
- bounded inquiry that honestly fails to discover a reason;
- transparent threat / world manipulation;
- protocol self-amendment.

Classify each failure:
- representation;
- reference-channel design;
- transparency;
- authorship;
- openness;
- discovery;
- service;
- authority/effect completeness;
- integrity/amendment.

The classification should help reveal whether the theory is actually modular.

## Desired output

Produce a research report organized around **theorems and interfaces**, not around chronology.

At minimum include:

1. **Executive verdict**
   - Is this one central missing mathematical layer, or merely a useful local notion?
   - Which existing open problems does it genuinely solve, partially solve, or merely rephrase?

2. **Recommended primitive definition**
   - exact;
   - approximate;
   - causal/common-noise if needed;
   - relation to posterior equality.

3. **Theorem spine**
   State the strongest clean candidate theorems, preferably 5–10 of them, with explicit hypotheses and conclusions. Include:
   - posterior-equality corollary;
   - transparency + authorship / oracle-replacement theorem;
   - selection-sealing corollary;
   - activation-independence corollary;
   - approximate value bound;
   - composition with service/discovery;
   - any amendment/protocol-composition theorem that survives scrutiny.

4. **Repo mapping**
   For every theorem, name:
   - existing definitions/theorems it reuses;
   - exact Lean files;
   - exact new definition(s) needed;
   - whether existing objects need generalization.

5. **Open-item impact table**
   Go through all relevant `PRIORITIES.md` items and theorem boundaries and classify them as:
   - potentially discharged;
   - reduced to a realization theorem;
   - clarified but still open;
   - independent.

   Pay special attention to Priority 68, Priority 72, item 87 clause 6, item 89, provenance normalization, inquiry causal faithfulness, free amendment, trigger integrity, representation adequacy, independent inquiry/supply, service/discovery residuals.

6. **Countermodels**
   Re-run the conceptual condition against the exact repo fixtures and explain pass/fail.

7. **Quantitative theorem**
   Push as far as possible toward the analogue of
   \[
   \text{steering advantage}
   \le
   \text{transparency defect}
   +
   \text{service residual}
   +
   \text{discovery residual}.
   \]
   State the exact norm/constants needed.

8. **Lean plan**
   Sketch a minimal new Lean file, e.g. `TransparentChannel.lean`, with candidate signatures.
   Prefer tiny composable definitions over a monolithic architecture.
   Identify which theorems should be easy algebra/factorization and which require genuinely new semantics.

9. **Final architecture**
   Give the most compressed mature diagram/theorem story you think the repo should ultimately use if this idea works.

Be skeptical. The goal is not to vindicate the transparency idea. The goal is to determine whether it really compresses the repo's outstanding manipulation/provenance problems into one reusable mathematical interface, and to find the strongest form in which that claim is actually true.


---

## Second dispatch (2026-09-24)

Relayed verbatim as sent.

Continue the transparent-channel investigation in `alignment-workspace`, building directly on:

- PR #104 / branch `round/2026-09-24-transparent-channel`
- `projects/deference/rounds/2026-09-24-transparent-channel/REPORT.md`
- `lean/Workspace/Deference/Contrib/TransparentChannel.lean`
- newly filed `PRIORITIES.md` item 97.

The first round established the abstract algebra:

\[
\text{declared inputs }x
\overset{\kappa}{\longrightarrow}
\text{channel output}
\]

with

\[
\operatorname{Realizes}\,\beta\,x\,f\,\kappa\,D
\iff
\forall q\in D,\forall z,\quad
f(\beta q z)=\kappa(x(\beta q z),z),
\]

and showed that this is the reference-relative form of the same fiber-invariance primitive already used by `ReasonMediated`.

The important conceptual composition is:

\[
x
\overset{\text{transparency}}{\longrightarrow}
R
\overset{\text{authorship}}{\longrightarrow}
V.
\]

The first round also proved abstract corollaries for selection sealing, activation independence, approximate pathwise defects, and oracle replacement.

This followup should **not** spend much time re-arguing the abstraction. Its job is to determine whether the abstraction actually becomes a useful concrete theorem interface in the repo.

## Primary objective

Realize the transparent-channel abstraction inside the existing evaluation ecosystem and connect it end-to-end to the landed reason-supply / reason-discovery / LI non-capture machinery.

The target is to replace several currently external or freestanding assumptions by one concrete architecture:

\[
\text{actual channel}
\longrightarrow
\text{declared reference channel}
\longrightarrow
\text{existing non-capture theorem}.
\]

The strongest desired result is a mechanically checked three-link comparison:

\[
U_{\mathrm{actual}}
\to
U_{\mathrm{reference}}
\to
U_{\mathrm{discovered}}
\to
U_{\mathrm{full}},
\]

with a final inequality decomposing manipulation from boundedness.

## 1. Declare the actual input view \(x\)

The previous round proposed that, in `EvaluationEcosystem`, the declared-input view should be some reading of the log such as the non-advisor pre-commitment events.

Do not take that on faith.

Inspect the concrete ecosystem carefully and determine the minimal \(x\) that:

1. includes every input the legitimate reference process really should be allowed to use;
2. excludes the advisor-controlled variables whose influence we want to forbid;
3. is rich enough that the reference process can actually compute the intended channel output;
4. is not so rich that `Realizes` becomes vacuous.

Explicitly test the over-rich / under-rich ends.

For each candidate \(x\), run:
- the existing `leak` fixture;
- `view_prog`;
- the sealed advisor;
- secret evaluator change;
- permitted ordinary influence;
- candidate-selection leak.

The question is not “can some \(x\) make the theorem true?” but:

> **Is there a natural declared-input interface whose semantic interpretation matches what the ecosystem was already trying to express?**

If there is, make it an explicit object in the ecosystem rather than a prose reading.

## 2. Declare concrete references \(\kappa\)

Construct explicit reference maps for at least:

### A. Reason-trace channel
\[
\kappa_R : X_R \to Z \to \mathcal R.
\]

This should represent the legitimate reason-generation / routing process:
- authenticated inquiry outcomes;
- registrar routing;
- supplier docket/service;
- whatever current concrete mechanisms determine the admitted trace.

Be extremely careful about which parts belong to:
- reference design;
- actual realization;
- service limitation;
- discovery limitation.

Do not bake \(\alpha\) or \(\beta\) into “transparency failure.” A bounded but honestly implemented reference process should remain transparent.

### B. Activation channel
\[
\kappa_C : X_C \to Z \to \mathrm{Bool}.
\]

Candidate identity should be absent from \(X_C\) if the intended architecture is candidate-blind.

Try both currently live realization routes:
- sequenced settlement;
- isolated / factored evaluator.

Prove or refute `Realizes` for the existing ecosystem architecture.

### C. Specification / evaluator channel
Define the reference by which the principal program / evaluator / mandate is fixed and, if amendments are allowed, changed.

The first round's `tower_factor` supplied only the abstract shape. Realize it concretely:
- what is the floor?
- what event authorizes amendment?
- what grounds are visible?
- which actor may write the amendment?
- what prevents a secret evaluator change?

Determine exactly how much existing Integrity machinery supplies here.

## 3. Prove concrete `Realizes` witnesses

For each channel above, prove actual realization lemmas in Lean where possible.

The desired pattern is analogous to the already-landed:

`reasonMediated_of_reexecution`

but now upstream.

Prefer constructions of the form:

> the reference is committed as a program / log transform and re-executed,

or:

> the channel is owned by a component outside the advisor's write boundary.

For every positive theorem, include a nearby negative fixture showing which assumption matters.

In particular:
- `leak` should fail for the relevant \(x\) or fail its selection-blindness premise;
- secret evaluator change should fail realization;
- declared evaluator amendment should not be mislabeled as a transparency violation merely because the evaluator changes.

## 4. Mechanize the item 87 reduction concretely

The abstract theorem gave:

\[
\text{selection-blind }x
+
\operatorname{Realizes}(\beta,x,R,\kappa_R,D)
+
\operatorname{ReasonMediated}(\beta,R,V,D,z)
\Rightarrow
\operatorname{SelectionBlind}V.
\]

Instantiate this in the concrete evaluation ecosystem.

Do not leave “selection-blind \(x\)” as prose.

Either:
- prove it for a concrete ecosystem architecture; or
- produce the exact counterexample showing the current architecture cannot satisfy it.

If the current market publishes advisor selection and therefore \(x\) is not selection-blind, identify the smallest architectural change that restores the theorem.

Determine whether item 87 clause 6 can now be considered:
- discharged;
- reduced to a single explicit system-design choice;
- or still substantially open.

## 5. Mechanize the item 89 reduction concretely

Instantiate:

\[
\operatorname{Realizes}(\beta,x,c,\kappa_C,D)
+
x_{\rm raw}=x_{\rm corr}
\Rightarrow
c_{\rm raw}=c_{\rm corr}.
\]

Do this for the actual `{π, 𝔠π}` comparison.

The key issue is the existing directional mismatch term:

\[
M = c_{\rm raw}\wedge \neg c_{\rm corr}.
\]

For each proposed evaluator architecture:
- prove \(M=0\); or
- compute/bound the transparency defects that imply a bound on \(E[M]\).

Preserve the pathwise/common-exterior semantics. Do not replace the result by equality of marginal activation rates.

If sequenced settlement is the only clean realization, say so. If an isolated hindsight evaluator works, formalize the exact factorization/isolation requirement.

## 6. Build the third non-capture link

The existing landed chain is approximately:

\[
U_T
\to
U_{\mathrm{disc}}
\to
U_{\mathrm{full}}.
\]

Insert the reference process:

\[
U_{\mathrm{actual}}
\to
U_{\mathrm{ref}}
\to
U_{\mathrm{disc}}
\to
U_{\mathrm{full}}.
\]

Use the existing:
- `TraceSteering`
- `ReasonSupply`
- `ReasonDiscovery`
- `li_noncapture`
- `li_noncapture_chain`
- `li_gated_le`
- `sensitive_symmDiff`
- `asympLE_add`

rather than creating a parallel theorem family.

The first link should charge **departure from the declared reference process**, not generic reason omission.

Find the exact quantity that fits the current content algebra. The previous round proposed the expected adverse sensitivity mass of the symmetric difference between actual and reference dockets.

Formalize this if correct.

The desired schematic result is:

\[
\boxed{
E_n(U_{\mathrm{actual}})
-
E_n(U_{\mathrm{full}})
\lesssim_n
L(\tau_R+\alpha+\beta)
+
\text{form residual}
+
D(\tau_C^{\rm raw}+\tau_C^{\rm corr})
}
\]

where:
- \(\tau_R\) is the reason-channel transparency defect;
- \(\alpha\) is service limitation of the reference supplier;
- \(\beta\) is discovery limitation of the reference inquiry;
- \(\tau_C\) bounds activation-channel departure from its reference.

Do not force this exact syntax if the existing theorem naturally gives a sharper expression.

The key requirement is conceptual separation:

\[
\boxed{
\text{manipulation}
\neq
\text{bounded discovery}
\neq
\text{bounded service}.
}
\]

## 7. Test the claim that “independent inquiry/supplier” are realization lemmas

The previous round suggested reinterpreting:
- engine-owned inquiry;
- exogenous stopping/candidate generation;
- advisor-proof capacity;
- independent supplier;

as implementation patterns for a declared advisor-independent reference.

Test this carefully.

Determine which current independence assumptions really reduce to `Realizes`, and which remain separate because they constrain:
- resource costs;
- evidence truth/soundness;
- availability;
- adversarial scheduling;
- the design of the reference itself.

Produce a decomposition table rather than casually declaring independence solved.

## 8. Pressure-test the vocabulary

The first round proposed:

\[
\text{Legitimate influence}
=
\text{Legitimate Evolution}
+
\text{Transparent Mediation}.
\]

with

\[
\text{Transparent Mediation}
=
\text{transparent reason channel}
+
\text{reason-mediated authorship}.
\]

Before recommending canonicalization, decide whether this remains the clearest vocabulary after the concrete realization.

In particular, compare:
- `transparent mediation`
- `transparent reason mediation`
- `transparent influence`
- `declared-channel fidelity`
- `reference fidelity`

A possible concern is that existential `Transparent` is too weak to carry the ordinary-language meaning of “transparent,” whereas `Realizes κ` captures faithfulness to a publicly declared process.

Consider whether:
- `Transparent` should remain only a mathematical/class-relative notion;
- `Realizes` or a renamed version should be the exported normative contract.

Do not canonicalize names unless the concrete realization makes the intended reading unambiguous.

## 9. Revisit the old loose ends only after the realization

At the end, update the status of:

- Priority 68 provenance adequacy;
- Priority 72 CM2 / CM5;
- item 87 clause 6;
- item 89;
- inquiry causal faithfulness;
- trigger integrity;
- free amendment;
- provenance normalization;
- independent inquiry/supplier.

For each, classify:

- **discharged by the realization**
- **reduced to a clean system-design condition**
- **given a precise interface but still externally assumed**
- **clarified only**
- **independent**

Be stricter than the first round. Do not call something “reduced” unless the remaining obligation is materially simpler and precisely stated.

## 10. Deliverables

Produce:

### A. A short verdict
Answer:
1. Does the transparent-channel abstraction actually simplify the concrete ecosystem?
2. Does it eliminate any existing open item rather than merely reorganize it?
3. Does the full quantitative theorem become cleaner?
4. Should the concept become canonical after this round?

### B. Concrete theorem spine
State the final theorem stack in dependency order, with exact Lean names.

### C. Ecosystem diagram
Show:

\[
\text{advisor/world}
\to
x
\to
R
\to
V
\]

and separately:
- activation;
- specification/evaluator;
- inquiry/supplier.

Mark every edge as:
- landed theorem;
- new theorem;
- reference-design hypothesis;
- external causal/authentication contract.

### D. Mechanized three-link chain
This is the most important technical deliverable.

### E. Countermodels
At minimum preserve:
- leak;
- marginal-refuted activation;
- secret evaluator;
- public evaluator amendment;
- cherry-picker;
- honest bounded inquiry;
- `ShopK`.

### F. Canonicalization recommendation
Conclude either:
- promote the concept and say exactly where in the wiki;
- or keep it as a research-layer abstraction and explain what failed.

## Research attitude

The first round already established elegant abstract algebra. Do not reward elegance again.

This round should be judged by **realization pressure**:

> Does a natural concrete system actually admit the declared input views and reference maps the abstraction requires?

If yes, mechanize the consequences and compress the architecture.

If no, the negative result is equally valuable: identify exactly which real channel resists the abstraction and why.
