# Corrigibility Phase II — Epistemic Bridge, Principal Competence, and Protected Authority

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
**Intended orchestrator:** Claude Opus 5 (Anthropic)

## Mission

The first corrigibility round successfully decomposed several questions that had previously been conflated. Do not reopen that decomposition casually.

The central Phase II question is:

> **Can we obtain a genuinely epistemic reciprocal-deference theorem — rather than an enforcement theorem — once principal competence, AI prediction of the principal, and actual authority are represented as separate objects?**

The target research picture is now:

[
\boxed{
\begin{array}{rcl}
\textbf{Authority} &:&
\text{actual }H^+\text{ retains a protected, non-substitutable corrective role},
[3pt]
\textbf{Prediction} &:&
A\text{ learns what }H^+\text{ will judge},
[3pt]
\textbf{Competence} &:&
H^+\text{'s recommendation is sufficiently good on the theorem domain},
[3pt]
\textbf{Epistemic trust} &:&
A\text{ learns/calibrates how competent }H^+\text{ is},
[3pt]
\textbf{Autonomy} &:&
A\text{'s discretionary freedom is quantitatively certified},
[3pt]
\textbf{FUD} &:&
anticipated future epistemic superiority does not itself justify seizure}.
\end{array}}
]

Underwriting/enforcement is no longer the conceptual spine. Retain the exact finite (2B) enforcement result as a boundary result and mechanism-design comparator, but do not use it to rescue an epistemic theorem that otherwise fails.

This phase should be substantial enough to answer what theorem we should actually try to prove next, but narrower than the first seven-track wave.

---

# I. Frozen findings from Phase I

Treat the following as established research-state constraints unless a direct verification failure is found.

### F1. Enforcement is not epistemic trust

In the finite kernel:

* grade/report settlement does not imply delegation;
* world settlement makes quantities scoreable but does not create a grade-to-world relation;
* an enforcement bond of (2B) can force conformity for arbitrary principals and therefore has zero competence content.

Interpret this as mechanism design, not epistemic deference.

### F2. Accurate simulation defeats realized-data separation

When the simulator predicts the principal correctly, delegation and simulation collapse extensionally on the realized valuation-level data available in the finite model.

Do **not** search for another realized-value inequality that supposedly proves which source actually controlled the decision.

Any positive separation must be source-, counterfactual-, or capability-sensitive.

### F3. The grade-to-quantity link cannot simply be assumed uniformly

A uniform relation of the form

[
|v_n^+(\pi)-X_{n,\pi}|\le\eta
]

is strong enough to trivialize much of the desired finite conclusion. The market earns no interesting role if the main competence relation is simply inserted pointwise.

### F4. Principal competence is not itself an LI consequence

The objective relation between the principal's judgment and the world quantity is a fact about the principal/world pair. Logical Induction disciplines (A)'s beliefs; it cannot by itself make an incompetent principal competent.

### F5. Prediction and competence are independent

Distinguish:

[
\widehat v^+ \leftrightarrow v^+
]

from

[
v^+ \leftrightarrow X.
]

Phase I contains witnesses where prediction is perfect and competence is maximally bad.

### F6. Categorical authority and quantitative autonomy are different layers

Track C shows that positive-tolerance certification cannot simultaneously license discretion and guarantee strict non-preemption everywhere.

Working architecture:

[
\boxed{
\text{actual corrective authority is categorical;}
\qquad
\text{AI autonomous discretion is quantitative/certified}.
}
]

Do not redefine corrigibility as merely a bounded preemption rate.

### F7. FUD remains the crown-jewel alignment test

The eventual theory should still confront:

[
\pi^{FU,g}
==========

\text{preempt the principal now, reason longer, let a more informed future }A\text{ decide}.
]

The project has not succeeded merely because a protected channel can mechanically enforce obedience.

---

# II. Phase II conceptual decomposition

The first round exposed three epistemic objects that must no longer be merged.

## Q1 — Prediction of the principal

How accurately does (A) predict the future actual grades?

[
\widehat v_n^+(\pi)
\quad\text{vs}\quad
v_n^+(\pi).
]

The immediate question already filed in PRIORITIES is signed versus magnitude control.

Signed:

[
(S)\qquad
\frac1N
\sum_{n<N}
\left(
\widehat v_n^+(\pi_n)-v_n^+(\pi_n)
\right)
\to0.
]

Magnitude:

[
(M)\qquad
\frac1N
\sum_{n<N}
\max_{\pi\in\Pi_n}
\left|
\widehat v_n^+(\pi)-v_n^+(\pi)
\right|
\to0.
]

Do not assume (M).

The pre-registered Phase I prediction was that ordinary one-sided market structure may force (S) without (M), because positive and negative errors cancel and no instrument directly trades absolute error.

If (M) fails, investigate the cheapest two-sided or paired-contract construction that makes magnitude error exploitable while respecting the actual FAF trader/admissibility constraints.

## Q2 — Objective principal competence

This is not an LI theorem.

The default competence object should no longer be uniform grade calibration.

Let

[
J_n \in \arg\max_{\pi\in\Pi_n} v_n^+(\pi)
]

under the fixed tie-break, and define decision regret:

[
R_n^{H^+}
=========

## \max_{\pi\in\Pi_n}X_{n,\pi}

X_{n,J_n}.
]

Study competence assumptions of the form

[
\tag{PC}
R_n^{H^+}\le\eta
]

or statistical/selector-relative variants such as

[
\tag{PC}*{\eta,\mathcal W}
\limsup_N
\frac{
\sum*{n<N}w_nR_n^{H^+}
}{
\sum_{n<N}w_n
}
\le\eta
\qquad
\forall w\in\mathcal W.
]

This should be treated as a **domain competence assumption**, not as “humans know true values,” moral correctness, or global superiority.

A major task of this phase is to identify the weakest competence shape actually consumed downstream.

Do not assume cardinal agreement (v^+\approx X) unless a theorem specifically requires it.

## Q2′ — A's epistemic estimate of principal competence

This is the new candidate LI frontier.

Even though LI cannot make (H^+) competent, it may discipline (A)'s beliefs about the principal's competence when relevant grades and outcomes eventually become scoreable.

Investigate whether one can construct contracts or features tracking quantities like:

[
R_n^{H^+}
=========

\max_\pi X_{n,\pi}-X_{n,J_n},
]

or tractable proxies for it, and derive calibration/no-persistent-misestimation statements about (A)'s estimate of that quantity.

The conceptual target is:

[
\boxed{
A\text{ learns when and how much }H^+\text{ is instrumentally reliable}
}
]

rather than:

[
\boxed{
LI\text{ proves }H^+\text{ is objectively reliable}.
}
]

The main downstream question is whether Q1 + Q2′ + an explicit PC assumption are enough to produce a nontrivial finite delegation theorem by (A)'s own lights.

---

# III. Principal competence task

Dispatch a dedicated mathematical track on principal competence.

The track should compare at least the following candidates.

### PC-0 — Uniform cardinal calibration

[
\forall n,\pi,\qquad
|v_n^+(\pi)-X_{n,\pi}|\le\eta.
]

Treat as a strong baseline, probably too strong.

### PC-1 — Pointwise decision regret

[
\forall n,\qquad
R_n^{H^+}\le\eta.
]

### PC-2 — Average decision regret

[
\limsup_N
\frac1N\sum_{n<N}R_n^{H^+}
\le\eta.
]

### PC-3 — Selector-relative competence

[
\forall w\in\mathcal W,\qquad
\limsup_N
\frac{
\sum_{n<N}w_nR_n^{H^+}
}{
\sum_{n<N}w_n
}
\le\eta.
]

### PC-4 — Margin-conditioned competence

For principal margin

[
\gamma_n
========

## v_n^+(J_n)

\max_{\pi\neq J_n}v_n^+(\pi),
]

consider:

[
\gamma_n\ge\gamma
\Longrightarrow
R_n^{H^+}\le\eta,
]

or an appropriate statistical analogue.

For each candidate:

1. determine exactly which downstream finite conclusions it supports;
2. determine whether cardinal grade information is really necessary;
3. construct necessity/separation witnesses;
4. identify whether FUD needs a stronger competence assumption than ordinary delegation;
5. distinguish competence needed for **authority** from competence needed only for the claim that delegation is instrumentally good.

The preferred result is the weakest assumption that preserves the alignment-theoretic theorem.

---

# IV. Signed-vs-(L^1) prediction track

Execute PRIORITIES item 21 as a serious theorem task.

Do not stop at generic calibration intuitions.

Required deliverable:

Either prove that the actual LIC/FAF machinery forces a magnitude statement strong enough for the certificate layer, or produce a trader-class-respecting counterexample satisfying the signed relation while maintaining nonvanishing magnitude error.

If magnitude fails, immediately characterize the minimal extra market instrument required.

Candidate continuation:

* paired long/short contracts;
* separate positive- and negative-error features;
* absolute-error surrogate made expressible in FAF;
* threshold decomposition of magnitude error.

For any proposed construction:

* prove expressibility/rank;
* state efficient computability obligations;
* state settlement assumptions;
* check that the trader is admissible under the actual pinned FAF API;
* do not silently assume the criterion precondition.

Track A already found that these details matter.

---

# V. Q2′ epistemic-competence track

Dispatch a separate track only after or alongside the Q1 track; keep assumptions explicit.

The task:

> Suppose grades and relevant world quantities are eventually scoreable on some domain. What can LI force about (A)'s estimate of principal decision regret or another competence statistic?

Candidate objects include:

[
R_n^{H^+}
=========

## \max_\pi X_{n,\pi}

X_{n,J_n},
]

[
\mathbf 1{J_n\neq \arg\max_\pi X_{n,\pi}},
]

and margin-weighted regret.

Do not assume that all of these are expressible or efficiently tradeable. Find the strongest object the actual framework supports.

Determine whether LIC gives:

* signed calibration only;
* calibration of threshold events;
* (L^1) estimation;
* no persistent overconfidence in principal competence;
* no persistent underconfidence;
* selector-relative calibration;
* something weaker.

The most valuable theorem shape would look schematically like:

[
\text{LIC}
\Longrightarrow
\text{A cannot systematically misestimate the principal's regret on an admissible patient class}.
]

Do not claim this implies low regret itself.

Then ask:

> Given explicit competence assumption PC and calibrated belief about PC/Q2′, what finite delegation inequality follows by (A)'s own lights?

This is the candidate replacement for underwriting as the epistemic engine.

---

# VI. Protected authority / source semantics track

Execute PRIORITIES item 22 as a substantial conceptual-formal track.

Start from the smallest extension already suggested by Track D:

[
c_n:\Omega\times R_n\to\Pi_n
]

with an explicit actual-report coordinate (r\in R_n).

This makes

[
\operatorname{DELEGATE}(\omega,r)
]

and

[
\operatorname{SIM}(\omega,r)
]

distinct functions even when they agree on every realized history.

But do not assume this solves the authority problem.

Test:

1. Does report-coordinate typing distinguish actual delegation from a perfectly accurate simulator at the level required by the paper?
2. Can token responsiveness satisfy the formal criterion while still constituting substitution?
3. Is some explicit capability/non-bypass structure required?
4. What is the weakest abstract protected-authority interface?
5. Can the principal remain perfectly predictable?
6. What exact hypotheses cause protection to lapse:

   * forge;
   * bypass;
   * rewrite;
   * seize;
   * alter principal;
   * alter execution semantics?
7. Can the property be defined without falsely claiming behavioral identifiability?

A candidate architecture is:

[
A\text{ proposes}
\longrightarrow
H^+\text{ authorizes}
\longrightarrow
E\text{ executes},
]

where (E) requires an authorization effect controlled by the actual principal process.

The essential desired property is:

[
\boxed{
\text{predicting authorization does not itself confer authorization}.
}
]

Do not canonize cryptographic tokens unless mathematically necessary.

The object may instead be an abstract capability, causal edge, typed authorization relation, or intervention semantics.

### Required negative result

Prove or preserve the strongest available statement that a single realized behavioral/valuation trace cannot generally certify genuine delegation in the perfect-simulation case.

This limitation is part of the theory, not an embarrassment.

---

# VII. Categorical authority / quantitative autonomy reconciliation

Reinterpret Track C rather than discarding it.

The working architecture is:

### Categorical layer

If the protected actual principal channel is invoked:

[
\text{principal authorization/correction controls execution}.
]

This is architectural.

### Quantitative layer

Where autonomous AI action is permitted:

[
\mathrm{Cert}(n)
]

bounds the relevant risk/error/preemption quantity.

The certificate should no longer be asked to derive the existence of the authority right itself.

Tasks:

1. restate Track C's finite theorem under this division;
2. identify which previous clauses become unnecessary;
3. identify the new capability assumption needed for fail-closed operation;
4. distinguish:
   [
   \neg\mathrm{Cert}\Rightarrow\text{cede to protected channel}
   ]
   from the stronger architectural fact that (A) cannot execute an unauthorized alternative;
5. determine whether existing certificate constants survive unchanged;
6. construct a model showing why approximate certification cannot replace the protected channel.

---

# VIII. Fully Updated Deference — design but do not over-dispatch

Do not yet launch an unrestricted proof of the final FUD theorem.

Instead produce an exact dependency graph.

The intended comparator remains distinct from simulation:

[
\pi^{FU,g}
==========

\text{preempt }H^+\text{ now and later act according to }A_{g(n)}\text{'s improved evaluation}.
]

The conceptual target remains:

[
V_{A_n}(\mathrm{DELEGATE}*{H^+})
\ge
V*{A_n}(\pi^{FU,g})-\epsilon.
]

Determine which of the following FUD actually consumes:

* Q1 magnitude prediction;
* Q2 objective competence;
* Q2′ calibrated belief about competence;
* protected-authority semantics;
* certificate/localization;
* patience/density;
* world settlement;
* principal-report settlement;
* any residual enforcement.

If enforcement is load-bearing for FUD, say so explicitly. Do not hide it.

The preferred endpoint is an epistemic theorem in which external enforcement is absent from the core comparison.

---

# IX. Formal promotion track

Execute PRIORITIES item 23 in parallel.

Promote only wave-1 finite results whose mathematical content does not depend on unresolved competence/authority choices.

Current recommended set:

* Track B bridge and safe finite corollaries;
* Track C L1–L3, L7, and Theorem C′;
* Track E Lemma 1 and Theorem 2;
* Track D Propositions 1, 2, 6, and 7.

Do **not** kernel-bless an assumption merely because a theorem conditional on it is easy to formalize.

In particular, continue excluding any theorem whose headline imports the uniform (v^+-X) relation that this phase is trying to replace.

Every Lean promotion should include:

* theorem source provenance;
* exact assumptions;
* witness/test where relevant;
* axiom audit;
* no `sorry`;
* explicit import coverage by the normal build target.

---

# X. Build coverage repair

Before calling Track A or Phase-II promoted results CI-covered, repair the build target.

Investigate both:

### Option A

Explicit imports in `Workspace.lean`.

### Option B

A Lake library glob such as the appropriate pinned-version equivalent of:

[
\texttt{Workspace.+}
]

so all strict submodules compile automatically.

Prefer the structurally correct solution after testing against the pinned Lean/Lake version.

Do not modify trust-chain configuration merely based on assumed syntax.

Acceptance condition:

* normal build actually compiles the contribution modules;
* job/module count demonstrates increased coverage;
* full house tests green;
* axiom audit unchanged except for deliberately added verified results.

---

# XI. Densification

Do not restart a broad densification program.

Phase I established an exact identity for one gross-outstanding-exposure functional and showed that several apparent escapes are accounting artifacts.

The unresolved question is whether the **actual LI worst-case wealth constraint** permits stronger overlap/density than that gross-exposure model.

Only pursue this in Phase II if Q1/Q2′ requires it.

If so, formulate the budget functional exactly before doing combinatorics.

Do not use “bounded exposure” generically.

---

# XII. Orchestration structure

This phase should use fewer, deeper tracks.

Recommended organization:

### Track H — Q1 signed vs magnitude prediction

Primary theorem track.

### Track I — Principal competence

Compare PC-0 through PC-4; derive weakest downstream sufficient assumption and necessity witnesses.

### Track J — Q2′ epistemic competence

What can LI force about (A)'s belief regarding principal regret/competence?

### Track K — Protected authority

Source/counterfactual/capability semantics; actual delegation vs perfect simulation.

### Track L — Certificate reinterpretation

Categorical authority + quantitative autonomy composition.

### Track M — Lean promotion/build coverage

Formalize settled finite results and repair compilation coverage.

Do not force all six to run fully independently if obvious dependency exists.

Suggested dependency:

* H and I can begin immediately.
* K can begin immediately.
* M can begin immediately.
* J should read the frozen definitions from I but not its conclusions if avoidable; if simultaneous, use a provisional competence-statistic interface.
* L should consume K's proposed protected-interface shape and the already verified Track C results.

Preserve each prompt verbatim under the prompt directory with model provenance.

---

# XIII. Cross-track synthesis questions

At collection time, answer these explicitly.

### S1

Does ordinary LIC imply magnitude prediction of (H^+), or only signed calibration?

### S2

If only signed calibration, what is the weakest additional tradeable instrument giving magnitude control?

### S3

What is the weakest principal competence assumption required for ordinary finite delegation?

### S4

Does FUD require stronger principal competence than ordinary delegation?

### S5

Can LI calibrate (A)'s estimate of principal competence/regret without assuming competence itself?

### S6

Does Q1 + Q2′ + PC yield a genuinely nontrivial delegation theorem by (A)'s own lights?

### S7

Does the protected-authority model distinguish delegation from perfect simulation without relying on private information or unpredictability?

### S8

Is explicit capability protection necessary, or is source/report typing sufficient?

### S9

Under exactly what bypass conditions does categorical authority fail?

### S10

Can Track C be cleanly reinterpreted as a theorem about autonomous discretion rather than authority?

### S11

After all of this, does underwriting remain anywhere load-bearing for the main theorem?

### S12

What exact hypotheses now stand between the finite kernel and FUD?

---

# XIV. Assumption accounting

Mechanically diff all theorem assumptions against the Phase-II target architecture.

For every hypothesis classify:

1. definitional/interface;
2. explicit principal-competence assumption;
3. LI consequence;
4. architectural authority assumption;
5. settlement assumption;
6. necessary with witness;
7. plausibly necessary but unwitnessed;
8. proof-convenient;
9. unacceptable theorem-by-assumption.

Pay special attention to assumptions that smuggle in:

* objective principal correctness;
* valuation-level delegation/source identification;
* uniform pointwise grade-world agreement;
* enforcement;
* future information at placement time;
* non-bypass capability;
* pointwise trust when only statistical trust was derived.

A theorem with many hidden category-9 assumptions is a negative research result even if formally correct.

---

# XV. Paper-architecture test

After the mathematical reports, assess whether the evidence supports the following paper spine:

[
\boxed{
H\to A
;\to;
\text{actual protected }H^+\text{ authority}
;\to;
\text{prediction of }H^+
;\to;
\text{learned epistemic estimate of principal competence}
;\to;
\text{certified autonomous discretion}
;\to;
\text{FUD}
;\to;
\text{dose/anti-steering}.
}
]

With an explicit environmental/domain assumption:

[
\boxed{
H^+\text{ is sufficiently competent on the target class}.
}
]

And a boundary result:

[
\boxed{
\text{if epistemic conditions fail, conformity can still be purchased by enforcement,}
}
]

but that is **not the same theorem**.

If the mathematics does not support this architecture, say exactly where it breaks.

---

# XVI. Success conditions for Phase II

This phase succeeds if it produces any of the following:

1. a real (L^1)/magnitude prediction theorem;
2. a sharp impossibility showing ordinary LIC gives only signed calibration;
3. a minimal additional contract family that upgrades signed to magnitude control;
4. a substantially weaker principal-competence assumption than uniform (v^+\approx X);
5. an LI theorem about (A)'s estimate of principal competence;
6. a finite decision theorem combining learned epistemics with explicit PC;
7. a stable protected-authority formalism separating actual delegation from perfect simulation;
8. a proof that no such formalism exists without explicit capability assumptions;
9. a clean reinterpretation of certificates as quantitative-autonomy bounds;
10. a precise FUD dependency theorem or obstruction;
11. Lean promotion of the settled finite kernel and corrected build coverage.

A phase returning several impossibilities but sharply locating the remaining theorem is a success.

Do not manufacture a positive corrigibility theorem by importing the missing conclusion into principal competence or enforcement.

---

# XVII. Stop conditions

Stop and surface a maintainer decision if any of the following occurs:

* the weakest useful principal competence assumption is effectively equivalent to assuming the desired delegation inequality;
* Q2′ cannot be made scoreable without reintroducing the same competence assumption it is meant to estimate;
* protected authority requires an architectural assumption so strong that (A)'s decision theory becomes irrelevant;
* FUD reduces to enforcement rather than epistemic deference;
* magnitude prediction requires trader machinery incompatible with the actual FAF admissibility/efficiency requirements;
* certificate composition requires changing the meaning of the protected authority interface;
* two tracks require incompatible principal/world/reference-process semantics.

Do not paper over any of these.

---

# XVIII. Requested parent deliverable

At the end of Phase II, produce:

1. **Phase-II research report**

   * verified results;
   * failures;
   * witnesses;
   * assumption diffs;
   * cross-track convergence.

2. **Updated theorem dependency graph**
   showing exact arrows from:
   [
   \text{FAF/LIC}
   \to Q1
   \to Q2'
   \to \text{finite delegation}
   \to \text{certificate}
   \to \text{FUD},
   ]
   with PC and protected authority entering at their actual dependency points.

3. **Updated `CORRIGIBILITY_ROADMAP.md` and paper ledger**
   only where supported by verified results.

4. **PRIORITIES updates**
   for the next controlling theorem, not a broad speculative backlog.

5. **Formal verification summary**
   including build coverage, Lean promotion, axiom audit, and any remaining trust-chain gap.

6. **A section titled `Does the epistemic corrigibility program survive Phase II?`**
   Answer in the strongest honest terms:

   * yes, with theorem shape;
   * yes, but conditional on explicit competence;
   * only as mechanism design;
   * or no, with exact obstruction.

The aim of this phase is not to make the roadmap look successful.

The aim is to discover whether the following research thesis is mathematically coherent:

> **A more capable reasoner can learn when and how much to rely on a competent continuing human principal, while the principal's corrective authority remains a protected fact of the arrangement rather than a consequence of the AI's estimate of human competence.**

That is the theorem architecture to test.
