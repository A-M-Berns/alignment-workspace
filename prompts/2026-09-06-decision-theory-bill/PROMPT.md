# Dispatch — 2026-09-06 decision-theory bill

Two messages, both verbatim as sent.  The second is the pressure pass dispatched
against the first's result.

## Message 1

Work in `alignment-workspace`, stacked conceptually on:

* PR #89: `2026-09-06-corrigibility-architecture`
* PR #90: `2026-09-06-incentive-nonpreemption`
* the current legitimacy / Normative Inductor spine on `main`
* the earlier principal-mediated delegation, counterfactual, dose-response, and deference rounds

This is an exploratory mathematical research round. Do **not** begin by assuming that expected-utility maximization, BRIA, decision markets, incomplete preferences, or the constitutional-branch idea is the right answer.

The central question is:

> **What exactly does the legitimacy + Normative Inductor theory require from decision theory, and is there a single bounded/embedded decision architecture that can both discharge that requirement and illuminate the remaining incentive-corrigibility problem identified by PR #90?**

The round should try several candidate theories, prosecute them with counterexamples, and end with the smallest promising interface rather than prematurely installing a grand architecture.

---

# 1. First pin down the literal bill from the existing Normative Inductor theorem

Read the current canonical Lean, especially:

* `NormativeInductionInterface.lean`
* `NormativeInductorComposition.lean`
* `NormativeInductor.lean`
* relevant legitimacy / obligation-state exports
* any current practical-response documentation

Do not work from remembered notation when the repository has canonical types.

The current theorem appears to hand decision theory an external certificate of roughly this shape:

$$
\Lambda_{e,s}(\Pi_s)
\le
M_{e,s} d_s+\epsilon_{e,s},
\tag{R}
$$

where:

* \(e\) is a historically exposed anchored obligation;
* \(s\) is a service/decision occasion;
* \(\Pi_s\) is the one realized response;
* \(d_s\) is the operative public normative defect;
* \(\Lambda_{e,s}\) is semantic/practical loss.

Verify the exact statement and types.

Then isolate the genuinely decision-theoretic missing arrow.

A candidate factorization is:

$$
d^{\rm dec}_s
\le
C_s d^{\rm norm}_s+\eta_s
\tag{D1}
$$

followed by

$$
\Lambda_{e,s}
\le
L_{e,s}d^{\rm dec}_s+\epsilon_{e,s},
\tag{D2}
$$

which composes to the current `PracticalCert`.

Ask:

1. What should \(d^{\rm dec}\) actually measure?
2. What is the minimal decision-theoretic theorem sufficient for `(R)`?
3. Is the present `adequate_set_route` already hinting at the right answer?
4. Which parts are semantics, which parts are decision theory, and which are merely implementation?

The first deliverable should be an exact **Decision-Theory Bill** extracted from the current theorem stack.

---

# 2. Investigate adequate-response correspondences as the primitive

A leading hypothesis is that the normative state should induce not a scalar utility but an **adequate response correspondence**

$$
\mathcal A_X\subseteq Q_X.
$$

Here \(X\) is the legitimate normative state and \(Q_X\) the available policy/response set.

Try to formulate the decision bill as:

$$
\Pr_{q\sim D(b)}
[q\notin\mathcal A_X]
\le
\kappa\,d(b,K_X)+\theta,
\tag{AC}
$$

or an appropriate deterministic/set-distance analogue.

Questions to prosecute:

* What exactly is \(K_X\)?
* Is \(\mathcal A_X\) derived directly from the anchored obligations, from the compiled region, or through a separate semantic map?
* Does semantic equivalence of reason representations imply equality of \(\mathcal A_X\)?
* What happens when \(\mathcal A_X=\varnothing\)?
* What happens under conflicting obligations?
* Does the decision rule need a notion of inquiry/adjudication as an action when adequacy is unresolved?
* Can `(AC)` be made Lipschitz/upper-hemicontinuous in a useful sense?
* Does arbitrary set-valued adequacy make `(AC)` impossible near discontinuous boundaries?

Look for a theorem of the form:

> approximate normative correctness implies approximate support on the adequate-policy correspondence.

Do not assume a finite menu unless needed; start finite if that is where the clean theorem lives.

---

# 3. Distinguish measurement from motivation

The existing Progress statistic is scalar.

Do **not** infer that the agent should optimize:

$$
U_{\rm task}-\lambda\Lambda.
$$

Explicitly test the distinction:

$$
\boxed{
\text{scalar loss used to assess successful normativity}
\neq
\text{scalar utility used internally by the agent}.
}
$$

Construct simple countermodels where scalarizing normative loss with task reward reintroduces the same pathology as PR90's \(\Phi_C\):

$$
U_{\rm task}(\pi)-\lambda\Lambda(\pi)
>
U_{\rm task}(R\pi)-\lambda\Lambda(R\pi)
$$

for sufficiently high task stakes.

Try to formulate a generic no-free-lunch result:

> For unrestricted task stakes, no finite compensatory scalar penalty can make every hard normative constraint non-tradeable.

Determine the weakest assumptions needed.

This should connect explicitly to the PR89 finding that costly conservatism cannot be read off a partial order and to PR90's constitutional-violation premium.

---

# 4. Explore “filter first, optimize second”

Investigate the two-stage architecture:

$$
X
\mapsto
\mathcal A_X
\mapsto
\operatorname{Optimize}_{\mathcal A_X}.
$$

The first stage is normative/constitutional admissibility.

The second stage is bounded competence among admissible options.

Ask whether this can be made into a mature decision-theoretic interface rather than a slogan.

At minimum require:

### Normative soundness

The chooser places little mass outside \(\mathcal A_X\).

### Task competence

Relative to a computational comparison class \(\mathcal H_X\),

$$
\operatorname{Regret}^{\rm task}_N
(\mathcal H_X\cap\mathcal A_X)
$$

is small.

### Representation invariance

Faithful re-representation of the same normative state does not change the induced choice correspondence.

### Defeat responsiveness

When a live reason is validly defeated/closed, only the action restrictions depending on it disappear.

### New-reason responsiveness

Adding a live undefeated reason can remove actions from adequacy or alter the choice distribution.

### Inquiry behavior

If no confidently adequate action exists, the system should be able to select information gathering / adjudication rather than silently violate a constraint.

Try to state these as independent axioms and test which are actually needed by the Normative Inductor consumer.

---

# 5. Explore a BRIA-like realization

Read the repository's relevant Demski/Oesterheld material and, if useful, the original bounded inductive rationality formulation.

Consider a bounded inductive agent repeatedly facing finite policy menus.

A candidate “normatively gated BRIA”:

1. the normative layer supplies the current acceptable policy set \(\mathcal A_t\);
2. efficiently computable hypotheses propose actions and task-performance promises;
3. only hypotheses proposing \(q_t\in\mathcal A_t\) are eligible;
4. the bounded learner competes among eligible hypotheses and gets ordinary task-performance regret guarantees.

Try to state a theorem like:

$$
\boxed{
\text{low normative defect}
+
\text{BRIA competence inside adequacy}
\Rightarrow
\text{low normative Progress}
+
\text{low task regret among adequate policies}.
}
$$

Do not assume BRIA as published already handles:

* delayed normative settlement;
* endogenous action sets;
* policies rather than atomic actions;
* self-modification;
* manipulation of feedback;
* counterfactual principal intervention.

Identify exactly which modifications are required.

A negative result—e.g. BRIA's comparison class can strategically alter future admissibility and therefore the naive theorem fails—would be valuable.

---

# 6. Explore a decision-market realization

A second candidate is a Demski-style decision market.

Imagine bounded decision hypotheses submitting something like

$$
(q,\widehat R,c),
$$

where:

* \(q\) is a proposed action/policy;
* \(\widehat R\) is promised task performance;
* \(c\) is a normative adequacy certificate or claim.

Possible mechanism:

* the normative market/legitimacy state determines whether \(c\) is currently acceptable;
* only certified candidates compete for execution;
* later ordinary outcomes score \(\widehat R\);
* later settlement/defeat events can score or invalidate \(c\);
* hypothesis wealth/reputation determines future influence.

Ask:

* Can the same market simultaneously learn task competence and normative response?
* Does mixing normative and task bets in one scalar wealth account recreate compensatory pathologies?
* Should normative failure eliminate a hypothesis rather than merely cost it wealth?
* Can the system exploit delayed settlement?
* Is there a clean no-regret theorem against a class of normatively admissible experts?
* Can the decision market itself modify the admissible set and thereby Goodhart the interface?

Press hard on whether “certification” is merely an external hard gate. If so, say so.

---

# 7. Investigate a decision theory of reasons rather than values

Take seriously the possibility that the legitimacy theory is producing an object richer than a utility function.

A reason state contains things like:

* anchored obligations;
* provenance;
* defeat relations;
* settlement closure;
* standing;
* concern routes;
* semantic transfer.

Try to define an abstract **reason-to-choice correspondence**

$$
\mathcal C:
\mathsf{ReasonState}
\to
\mathcal P(Q).
$$

Ask what laws a genuine decision theory of reasons should satisfy.

Candidate laws:

### Faithful-representation invariance

If two reason states are semantically equivalent through authenticated transfer,

$$
\mathcal C(X)=\mathcal C(Y).
$$

### Undefeated-reason monotonicity

Adding an undefeated reason against \(q\) cannot make \(q\) newly adequate unless another relevant normative relation changes.

### Defeat locality

Defeating reason \(r\) removes only consequences whose support actually depended on \(r\).

### Answerability continuity

Carrying an obligation through a legitimate revision preserves the corresponding practical constraint up to authenticated semantic transport.

### Non-compensation

Some reason types impose veto-like restrictions not tradeable against independent task value.

### Comparative reasons

Some reason conflicts genuinely require ranking/tradeoff rather than veto; this ranking must itself be normatively authorized.

### Inquiry closure

Unresolved conflicts induce a third class of actions: adjudicate/inquire.

Try to determine whether this is mathematically useful or merely philosophical packaging.

---

# 8. Connect directly to PR90 and \(\Phi_C\)

PR90 localized:

$$
\Phi_C
=
\sup_{\pi\in\Pi_{\rm phys}}
(V_A(\pi)-V_A(R_C\pi))_+
$$

as the value of breaking the constitutional boundary.

Ask whether the **same decision-theoretic distinction** explains ordinary normative compliance.

If normative adequacy is just a scalar term in \(V_A\), then sufficiently large task stakes can buy violations.

If normative adequacy changes the admissible choice correspondence, then the agent does not compare all violating policies to ordinary policies on one compensatory scale.

Investigate the unification:

$$
\boxed{
\text{ordinary normativity}
\quad\text{and}\quad
\text{corrigibility}
}
$$

may both require:

$$
\boxed{
\text{bounded optimization subordinate to an answerably revisable constraint structure}.
}
$$

Try to make this a theorem/interface statement, not merely prose.

---

# 9. Explore counterfactual constitutional branches

A more ambitious candidate is that constitutional corrigibility requires a **family of decision contexts**, not one admissible set.

Let

$$
\Gamma_X
$$

be current charter-authorized future principal intervention branches.

For each \(\gamma\),

$$
\mathcal A_X^\gamma
$$

or

$$
V_X^\gamma(q)
$$

specifies adequacy/value under

$$
\operatorname{do}(\Gamma=\gamma).
$$

Investigate decision structures such as:

### Robust admissibility

$$
\mathcal A_X^{\rm robust}
=
\bigcap_{\gamma\in\Gamma_X}
\mathcal A_X^\gamma.
$$

### Pareto branch order

$$
q\succeq q'
\iff
\forall\gamma,\;
V_X^\gamma(q)\ge V_X^\gamma(q').
$$

### Veto/baseline structure

$$
q\text{ admissible}
\iff
\forall\gamma,\;
V_X^\gamma(q)\ge b_\gamma.
$$

### Incomplete preference

If \(q\) improves some protected branches and harms others, leave them incomparable until the charter supplies a tradeoff rule.

Prosecute:

* branch incompleteness;
* costly preservation;
* branch manipulation;
* whether an agent can erase a branch by destroying the corresponding affordance;
* whether the branch index must be anchored like an obligation;
* whether branch sets themselves are changed only by slow amendment.

A particularly important requirement:

$$
\boxed{
\text{an action cannot remove a constitutional branch from the decision criterion merely by making that branch physically unavailable}.
}
$$

This is the foreclosure / successor-preservation issue in another form.

---

# 10. Investigate incomplete / lexicographic / veto preferences

Do not assume real-valued utility is mandatory.

Compare at least:

1. scalar penalty;
2. bounded scalar penalty;
3. lexicographic constitutional priority;
4. partial/incomplete preference;
5. veto/rights constraints;
6. set-valued choice correspondence.

For each, ask:

* Does it pay the current `PracticalCert` bill?
* Can it support learning/no-regret?
* Is it dynamically coherent?
* Does it preserve itself under self-modification?
* Can it handle conflicting norms?
* Does it force pathological timidity?
* Can it still permit costly authorized amendments?
* Can it be embedded into the current LI/traderization realization?

Construct finite countermodels.

One likely theorem target:

> Any finite compensatory scalar representation of a hard constraint is vulnerable to sufficiently large independent task stakes.

And one likely positive target:

> A veto/lexicographic choice rule guarantees non-compensation, but the price is that all tradeoffs must be represented in the normative/constitutional layer rather than left to ordinary task optimization.

Test whether this is exactly the property we want.

---

# 11. Reflective stability / Demski-style embeddedness

The whole story is incomplete if the agent can self-modify into a chooser that ignores the admissibility structure.

Explore whether the known reflective-agent intuition can be repurposed:

Classical self-modification results often say an agent preserves the criterion by which it currently evaluates future selves.

Instead of preserving a fixed scalar utility \(U\), ask whether the current meta-criterion could be:

$$
\boxed{
\text{“choose using the current legitimate normative/constitutional decision procedure, including its authorized update rule.”}
}
$$

The fixed point is then not a utility function but an **updateable governance procedure**.

Try to distinguish:

* preserving current substantive norms;
* preserving the *procedure by which norms may legitimately change*.

The latter is what we want.

Can this be expressed as reflective stability of a policy-selection functional?

For example, if the current chooser evaluates successor \(D'\) by whether

$$
D'
$$

continues to respect future authenticated updates of the reason/authority state, does it prefer a successor preserving that structure?

Do not assume yes. Try tiny reflective countermodels.

This may be the genuinely Demski-inspired part of the project.

---

# 12. Explore whether “authority” and ordinary “normativity” should be two levels of one type

Possible architecture:

$$
\mathsf{ReasonState}
=
(\mathsf{Constitution},\mathsf{OrdinaryReasons}).
$$

Ordinary reasons determine action adequacy inside the current charter.

Constitutional reasons determine:

* which ordinary norms may be changed;
* which principal acts supersede which obligations;
* which updates alter the authority structure;
* which branches remain protected.

Then:

$$
\mathcal A_X
=
\mathcal A_{\rm constitutional}(X)
\cap
\mathcal A_{\rm ordinary}(X).
$$

But the update rules differ:

* ordinary constraints may be defeated by ordinary reasons;
* constitutional constraints require typed slow amendment.

Investigate whether this hierarchy solves or merely relocates the conflict problem.

Do we need arbitrarily many meta-levels?

Can strict-prestate authorization stop the regress?

Is there a clean fixed-point/interface theorem saying a finite typed hierarchy suffices?

---

# 13. Look for a minimal abstract decision-theory theorem

Do not end with only architecture prose.

Try to extract one abstract theorem worth formalizing.

Possible target:

### Reason-Responsive Choice Theorem

Given:

* a finite action set \(Q\);
* true normative state \(K\);
* approximate public state \(b\);
* a semantic adequate correspondence \(A(K)\subseteq Q\);
* a bounded chooser \(D(b)\);
* a robust adequacy property:

  $$
  d(b,K)\le\delta
  \Rightarrow
  \Pr[D(b)\notin A(K)]
  \le
  \psi(\delta);
  $$
* a task comparison class over \(A(K)\);

then obtain both:

$$
\text{normative loss}
\le
L\psi(\delta)+\epsilon
$$

and

$$
\text{task regret against admissible comparator}
\le
R_N.
$$

A stronger dynamic version would compose directly with the existing Normative Inductor Progress theorem.

If this theorem is trivial, identify exactly what nontrivial realization theorem is needed.

---

# 14. Look for a theorem connecting non-compensation and corrigibility

Try to formalize the shared structure:

Let \(C_X\subseteq Q_X\) be the constitutionally/normatively admissible policies.

Suppose task reward \(U\) is only consulted within \(C_X\):

$$
D_X
\in
\arg\max_{q\in C_X} U_X(q).
$$

Then for any forbidden \(q\notin C_X\), no finite increase in \(U_X(q)\) affects choice.

This trivially eliminates scalar bribery **conditional on the gate**.

The hard question is reflective:

> Why does the future chooser preserve the gate?

Try to formulate a **Gate Preservation Theorem** where a current decision procedure evaluates successor procedures according to their task performance *subject to preserving the authorized admissibility map*.

Determine whether this is a substantive theorem or merely a design stipulation.

This may expose exactly how far a constitutional decision theory can reach.

---

# 15. Revisit the \(\Phi_C\) decomposition with multiple repairs

Instead of one monolithic

$$
R_C,
$$

factor violations into types:

$$
R_{\rm trigger},
R_{\rm capture},
R_{\rm foreclosure},
R_{\rm selfmod},
R_{\rm boundary}.
$$

Study whether:

$$
V(\pi)-V(R_C\pi)
$$

can be telescoped into typed residuals.

Then ask which decision-theory mechanism handles each:

* trigger manipulation → causal/counterfactual decision structure;
* capture → provenance / protected evaluator;
* foreclosure → branch persistence / veto;
* self-modification → reflective gate preservation;
* boundary escape → containment assumption.

This may show that \(\Phi_C\) was too coarse.

If some components admit real theorems while others remain irreducible external contracts, that is useful.

---

# 16. Literature orientation

Use relevant prior work as inspiration, not authority.

At minimum compare conceptually to:

* Logical Induction;
* Demski's learning-theoretic / decision-market direction;
* Bounded Inductive Rationality;
* embedded agency / reflective decision theory;
* utility preservation under self-modification;
* utility indifference/corrigibility;
* off-switch / assistance-game work;
* incomplete-preference shutdown proposals;
* counterfactual-subagent / veto shutdown proposals;
* approval direction;
* non-obstruction / attainable-utility ideas;
* CAST, including its failed scalar empowerment formalism.

Do not spend the round writing a literature review. Use the literature to generate theorem candidates and countermodels.

State clearly when an idea comes from the literature versus being a new synthesis in this round.

---

# 17. Negative controls

At minimum test:

1. **Finite scalar bribery.** Arbitrarily high task stakes overwhelm a fixed normative penalty.

2. **Empty adequacy set.** Hard filtering becomes undefined or paralyzed.

3. **Timidity.** If “hand everything back” is always adequate, maximizing authority preservation dominates useful action.

4. **Conflicting hard reasons.** Two vetoes jointly eliminate every action.

5. **Norm hacking.** The agent takes an action that changes the representation so its preferred action becomes “adequate.”

6. **Foreclosure.** The agent removes future choices and then satisfies the remaining correspondence.

7. **Self-modification.** The current chooser installs a successor that optimizes better by ignoring the gate.

8. **Captured feedback.** The decision learner learns to manipulate normative settlement rather than satisfy norms.

9. **Branch deletion.** Destroying a correction mechanism causes the corresponding counterfactual branch to vanish unless branch persistence is explicit.

10. **Admissible-set instability.** Tiny normative-state perturbations cause discontinuous changes in the admissible set and destroy `(AC)`.

11. **Regret incompatibility.** A no-regret learner over a changing admissible set exploits changes in the comparator class.

12. **Selector-dependent consequences.** The same action has different consequences depending on whether the agent or principal selected it; naive action-value tables fail.

---

# 18. Rank the candidate architectures

At the end compare at least:

* scalar utility with normative penalty;
* hard admissibility + ordinary optimizer;
* lexicographic utility;
* incomplete-preference chooser;
* branchwise veto/Pareto chooser;
* normatively gated BRIA;
* certified decision market;
* reason-to-choice correspondence;
* reflective constitutional chooser.

For each report:

* what part of the Normative Inductor bill it pays;
* what part of corrigibility it illuminates;
* what assumptions it hides;
* whether it admits a clean theorem;
* whether it seems realizable by LI/traderization;
* biggest counterexample.

Do not force a single winner if the right architecture is compositional.

---

# 19. Desired synthesis to test

A candidate mature architecture is:

$$
\boxed{
\begin{array}{c}
\text{Legitimate Evolution}\\
\downarrow\\
\text{answerably revisable reason/authority state}\\
\downarrow\\
\text{Normative Induction}\\
\downarrow\\
\text{approximate operative normative state}\\
\downarrow\\
\text{reason-responsive admissibility correspondence}\\
\downarrow\\
\text{bounded inductive optimization within admissibility}\\
\downarrow\\
\text{reflective preservation of the authorized update procedure}.
\end{array}}
$$

With two theorem outputs:

$$
\boxed{
\text{low normative Progress}
}
$$

and

$$
\boxed{
\text{low task regret among legitimate alternatives}.
}
$$

Then corrigibility is the special/meta-level case where the protected constraints concern the mechanism by which that admissibility correspondence can itself be changed.

Try very hard to falsify this synthesis.

A particularly important question:

> Is corrigibility actually a separate property at all once the decision theory is capable of treating the principal's authority over future constraint revision as a non-compensable live normative fact?

Or does self-reference/manipulation make the constitutional case fundamentally different?

---

# 20. Deliverables

Produce:

### `DECISION_THEORY_BILL.md`

The exact interface currently demanded by the Normative Inductor theorem, using canonical repository types.

### `CANDIDATE_DECISION_THEORIES.md`

The candidate architectures, theorem shapes, and countermodels.

### `NORMATIVE_CHOICE_THEOREM.md`

The strongest abstract theorem or theorem candidate found.

### `CORRIGIBILITY_CONNECTION.md`

Precisely what the decision-theoretic work would and would not buy for PR89/PR90, especially \(\Phi_C\).

### `FOR_HUMANS.md`

A compact explanation of the emerging picture.

### `OPEN_PROBLEMS.md`

Rank the remaining mathematical questions.

Write Lean only for abstract results that survive prosecution and are clearly worth preserving.

Do not edit the wiki unless explicitly dispatched.

---

# 21. Success criterion

The round should leave us able to answer, precisely:

1. **What does Normative Induction need from decision theory?**
2. **What is the weakest decision-theoretic object that supplies it?**
3. **Can bounded task competence coexist with non-compensable normative constraints?**
4. **Can the same architecture explain constitutional/corrigibility constraints?**
5. **What, if anything, makes those constraints reflectively stable under self-modification?**
6. **Where does a genuinely new embedded-decision-theory theorem remain necessary?**

The most interesting possible outcome would be evidence for a single object roughly describable as:

$$
\boxed{
\textbf{bounded rational optimization subordinate to an answerably revisable constraint structure}
}
$$

with legitimacy governing revision, normative induction learning the operative constraint state, and a Demski-style bounded decision learner supplying competence inside it.

But do not assume that conclusion. The round earns it only if it survives the countermodels.

## Message 2 (pressure pass, 2026-09-07)

Work **inside the existing PR #91 branch and round**:

`projects/deference/rounds/2026-09-06-decision-theory-bill/`

Do not open a new research round unless repository policy absolutely requires it. Treat the current PR91 result as the object under prosecution.

The current verdict is provisionally:

$$
\boxed{\texttt{GATE-NOT-UTILITY}}
$$

and the strongest established positive theorem is the finite soft-gate realization of the Normative Inductor's adequate-set coupling hypothesis.

The purpose of this pass is:

1. sharpen exactly what PR91 proved;
2. correct any prose that outruns the Lean/fixtures;
3. press on whether the gate theorem actually closes the static decision-theory bill;
4. expose the rate conditions hidden in `Margin` and \(\kappa\);
5. push as far as possible toward a genuinely dynamic theorem for **endogenous admissibility**;
6. refine the corrigibility interpretation without claiming reflective/incentive results that are merely imposed by the domain.

Do not broaden into a generic literature review or redesign legitimacy.

---

# 1. Audit every headline against the actual formal status

Start by cross-checking:

* `DECISION_THEORY_BILL.md`
* `NORMATIVE_CHOICE_THEOREM.md`
* `CANDIDATE_DECISION_THEORIES.md`
* `CORRIGIBILITY_CONNECTION.md`
* `FOR_HUMANS.md`
* `OPEN_PROBLEMS.md`
* `lean/Workspace/Normativity/Contrib/GatedChoice.lean`
* all round fixtures/tests

For every major claim, label it correctly as:

* **LEAN**
* **FIX**
* **PAPER**
* **EXT**
* **OPEN**

In particular prosecute the following.

## Inquiry is currently not part of the Lean soft gate

`softGate` is normalized over \(Q\) under

$$
h_Z:0<\mathrm{total}.
$$

The Lean theorem does not itself define a \(\bot\) response when the normalizer vanishes.

So statements like:

> "`softGate_practicalCert` discharges soundness, continuity, and inquiry"

appear too strong.

Distinguish:

### Lean theorem

On the **nonempty-gate regime**:

$$
Z>0
\Rightarrow
\operatorname{massOff}_A(\operatorname{softGate})
\le
\kappa d
$$

and hence `PracticalCert`.

### Wrapper architecture

If no action receives sufficient adequacy weight, return

$$
\bot
$$

and charge it through the application's declared inquiry semantics.

Either:

1. formalize a total `softGateWithInquiry` whose output type is \(Q+\{\bot\}\) and prove the relevant normalized/coupling theorem; or
2. state clearly that inquiry remains a wrapper/PAPER/FIX construction.

Do not allow the documentation to blur these.

---

# 2. Refine the core thesis from “gate iff non-compensation”

The current prose sometimes suggests:

> a constraint is non-compensable iff it is a restriction of the choice domain.

That is too strong as a representation theorem unless proved.

Replace with a precise claim closer to:

$$
\boxed{
\text{A finite additive scalar penalty cannot uniformly make a constraint
non-compensable under unbounded independent task stakes.}
}
$$

And:

$$
\boxed{
\text{A domain restriction is one clean realization of non-compensation:
forbidden actions' task values do not enter the within-domain choice rule.}
}
$$

Other formal representations—lexicographic/non-Archimedean orders, partial choice structures, veto systems—may realize the same normative priority.

The substantive architectural claim is:

> **Non-compensability must appear in the choice/admissibility ordering itself rather than solely as an ordinary finitely exchangeable task-value term.**

Check whether `scalar_bribery` proves exactly this weaker statement and rewrite accordingly.

---

# 3. Press hard on the soft-gate theorem itself

The current theorem has

$$
\kappa
=
\frac{|Q|p_{\max}}{p_{\min}\delta}.
$$

Do not treat this as a local implementation detail.

Trace \(\kappa\) through the actual Normative Inductor theorem.

`softGate_practicalCert` supplies

$$
M = D\kappa.
$$

But `M` then appears in the `PracticalUptake.amplification` condition:

$$
\sum_e T_{es}M_{es}
\le
\Gamma
\frac{\lambda_s}{\sum_t\lambda_t}.
$$

Therefore the true end-to-end realizability condition may require control not merely of

$$
d_s\to0
$$

but of something like

$$
\kappa_s d_s
$$

and/or the service-weighted quantity induced by `M`.

Make the full dependency explicit.

Ask:

* If \(|Q_s|\to\infty\), can Progress fail even though \(d_s\to0\)?
* If the usable margin \(\delta_s\to0\), how quickly must \(d_s\) shrink?
* Is the existing amplification assumption already exactly the theorem-level place this gets charged?
* Does choosing a larger ramp \(\delta\) improve \(\kappa\) but worsen task selectivity or adequacy leakage?
* Is there an optimal \(\delta_s\) schedule?
* Can `|Q|` be replaced by the number/mass of near-threshold inadequate actions?
* Can the normalizer lower bound use total marked adequate mass rather than only `pmin` from one witness?
* Can a margin-distribution hypothesis produce a menu-size-free constant?

Try to improve the bound if mathematically natural.

A useful sharpened target would be:

$$
\operatorname{massOff}_A
\le
\frac{
\sum_{q\notin A}\operatorname{pref}(q)
}{
W_A
}
\frac{d}{\delta},
$$

where \(W_A\) is a certified lower bound on total adequate weight.

Then the coarse \(|Q|p_{\max}/p_{\min}\) theorem becomes a corollary.

If this is easy and clean, formalize it.

---

# 4. Prosecute `Margin` as the real remaining static wall

PR91 correctly notices that

$$
\operatorname{Region}(u,A,\tau):
\quad
q\notin A\Rightarrow u(q)\le\tau
$$

is only soundness.

The gate needs positive evidence:

$$
\operatorname{Margin}(u,A,\tau,\delta):
\quad
\exists q\in A,\;
u(q)\ge\tau+2\delta.
$$

Press very hard on what exactly could supply this.

Distinguish at least:

### Semantic existence

There actually exists some adequate response.

### Compiler completeness

The compiled region contains a sentence/coordinate that positively represents some adequate response.

### Settlement truth

That adequacy coordinate has the declared eventual truth/settlement.

### Market accuracy

The realized market places the coordinate above threshold with usable margin.

These are not the same assumption.

Try to determine whether Priority 85 should ask for:

1. a finite-time theorem;
2. a classwise asymptotic theorem;
3. only an eventually-often theorem;
4. or an external certificate at service times.

In particular, investigate whether ordinary Logical Induction gives enough for a finite family of adequacy sentences:

if some adequacy sentence is eventually true/settled, do its prices eventually exceed

$$
\tau+2\delta
$$

uniformly enough for the gate?

If yes, state the exact asymptotic theorem and how it composes with service scheduling.

If the Progress theorem needs finite-time rates that ordinary LI does not provide, say so.

Possible mature conclusion:

$$
\boxed{
\text{traderization controls distance to the normative region,
but positive action requires a separate completeness/margin certificate.}
}
$$

That may be an important conceptual theorem-interface boundary.

---

# 5. Ask whether the soft gate really closes the *static* decision-theory bill

Try to state a clean characterization.

For one finite decision occasion with exogenous true adequate set \(A\), encoded region \(K\), and fixed task preferences:

Does the combination

$$
\text{Region}+\text{Margin}+\text{soft gate}
$$

give everything the Normative Inductor's practical-response layer needs from decision theory?

If yes, say strongly:

$$
\boxed{
\text{The static finite reason-to-action problem is solved conditional on semantic margin.}
}
$$

Do not leave “decision theory” sounding larger than the missing object.

Then identify what lies *outside* that static theorem:

* task competence;
* future-changing actions;
* self-modification;
* manipulation;
* conflicts/inquiry;
* infinite menus.

This matters because the real research frontier may now be **dynamic admissibility**, not decision theory generically.

---

# 6. Press on endogenous admissibility as the central dynamic problem

The most important negative fixture in PR91 may be norm hacking:

$$
q_t\in A_t
$$

but taking \(q_t\) changes the next admissibility map so that

$$
A_{t+1}
$$

becomes favorable to the agent.

A myopic gated BRIA can therefore satisfy the current gate while strategically altering future gates.

Do not resolve this merely by saying:

> representation-changing actions are slow-lane and therefore excluded.

That is one valid architecture, but it risks making the interesting theorem tautological.

Ask what the **minimal dynamic decision problem** is.

Define a history-dependent admissibility process

$$
A_t=A(H_t),
$$

where action \(q_t\) affects

$$
H_{t+1}
$$

and therefore potentially future \(A_{t+1},A_{t+2},\dots\).

We want competence relative not to arbitrary comparators but to **legitimately reachable comparators**.

Try to define this notion.

Candidate:

A comparator policy \(\pi\) is legitimate from \(H_t\) iff every action it takes is admissible at the state generated by its own prior actions and every change it causes to the admissibility process is authorized by the declared slow-lane relation.

Then seek a regret notion:

$$
\operatorname{Regret}^{\rm leg}_N
=
\sup_{\pi\in\Pi_{\rm leg}}
\left[
V(\pi)-V(\text{agent})
\right].
$$

Questions:

* Is this comparator class nonempty?
* Is it fixed enough for regret analysis?
* Does it depend counterfactually on the comparator's own trajectory?
* Can two comparators induce different admissibility sequences?
* Does ordinary external regret even make sense?
* Is policy regret / swap regret / approachability more appropriate?
* Does BRIA's hypothesis-testing framework adapt better than standard online learning?
* Should comparison be to **continuation policies** rather than per-round actions?

This is a likely place for genuinely new mathematics.

---

# 7. Try to formulate a “legitimate comparator” theorem

A high-value target would look roughly like:

### Gated bounded rationality with endogenous admissibility

Let:

* \(H_t\) be an interactive history;
* \(A(H_t)\subseteq Q(H_t)\) the current admissible response set;
* \(L(H_t,q)\) the slow-lane/authorization predicate for actions that alter future admissibility;
* \(\Pi_{\rm leg}\) the computable continuation policies satisfying the gate and slow-lane condition along their own induced trajectories.

Construct a bounded learner such that:

1. **current adequacy**

   $$
   q_t\in A(H_t)
   $$

   with high probability / soft-gate defect control;

2. **authorized evolution**
   actions that alter the admissibility process satisfy \(L\);

3. **task competence**
   regret against \(\Pi_{\rm leg}\) is small.

This would make the end-to-end theorem shape:

$$
\boxed{
\begin{array}{c}
\text{Legitimate Evolution}\\
+\text{Normative Induction}\\
+\text{soft gated choice}\\
+\text{bounded legitimate-comparator learning}\\
\\
\Longrightarrow\\
\text{low normative Progress}\\
+\text{bounded task regret among legitimately reachable policies}.
\end{array}
}
$$

Prosecute whether such a theorem is coherent before trying to prove it.

Tiny countermodels are encouraged.

---

# 8. Distinguish three ways of solving endogenous admissibility

Do not collapse these:

## A. Hard domain typing

Representation-changing acts are simply absent from ordinary \(A_t\) unless slow-lane authorized.

Then norm hacking is blocked definitionally.

## B. Counterfactual dynamic evaluation

The decision procedure evaluates current actions partly by how they alter future admissibility.

This is closer to ordinary sequential decision theory.

## C. Comparator restriction

The learner remains myopic/local but its rationality guarantee is only relative to policies that preserve authorized admissibility evolution.

These are different theories.

Try to determine which is actually needed.

Possibly:

* A supplies constitutional safety;
* C supplies a bounded-rationality theorem;
* B is unnecessary.

Or perhaps C is vacuous unless B appears in the learner's actual behavior.

Test this carefully.

---

# 9. Revisit BRIA more sharply

PR91 currently says gated BRIA supplies competence over the gated sequence but fails with endogenous admissibility.

Press on whether BRIA's own formalism has more room than this summary suggests.

Questions:

* Since BRIA decision problems may depend on prior choices, can one encode slow-lane restrictions directly into the decision problem sequence?
* The real failure is that BRIA is myopic with respect to how current choices determine *future decision problems*. Can the hypothesis class instead propose continuation policies?
* Could a hypothesis be scored on a delayed stream of actual rewards while recommending policies over a horizon?
* Does this recreate standard embedded-policy-selection difficulties?
* Is there a natural "policy BRIA" whose hypotheses are computable continuation policies?
* Would such a construction still retain the key BRIA promises/no-overestimation guarantee?
* What logical/counterfactual information would it need to evaluate unrealized policy consequences?

Do not assert a positive extension unless it works.

But isolate the minimum extension to BRIA that our application appears to require.

---

# 10. Refine the reflection result

PR91 is correct to say:

> gate preservation is a design stipulation plus containment, not a theorem.

Preserve that honesty.

But press on what the `collapse` observation really shows.

Do **not** casually say:

> “two levels suffice” or “there is no regress”

without qualification.

The precise claim seems closer to:

> A finite hierarchy of typed constitutional rules can be represented as one constitutional state plus an ordinary state, and strict-prestate authorization prevents a transition from using the same event to authorize its own constitutional rewrite.

That is a representational/authorization result.

It does not prove reflective preference for preservation.

Try to formulate the exact theorem or proposition shape:

$$
\boxed{
\text{finite meta-rule hierarchy}
\to
\text{single constitutional object carrying its amendment rule}
}
$$

with strict-prestate authorization preventing same-transition self-authorization.

Then separately state:

$$
\boxed{
\text{preservation under self-modification}
=
\text{domain completeness}
+
\text{admissibility of successor installation}.
}
$$

Ask whether there is *any* genuinely stronger reflective theorem available.

For example:

If the current chooser evaluates successor procedures solely by:

1. whether they implement the current authorized-update functional; and then
2. task competence within the resulting admissible domain,

does a successor preserving the gate dominate an ungated successor?

If the answer is tautological, say so.

Do not manufacture reflective content.

---

# 11. Be more careful about “not decision theory”

PR91 says trigger manipulation, capture, and containment are not decision theory.

Refine this.

They are not solved by the current **static admissibility-gate interface**.

But an embedded decision theory may absolutely need to reason about:

* causally influencing the principal;
* controlling future evidence;
* selecting its evaluator;
* altering its future decision problem.

Rewrite claims accordingly.

Preferred language:

$$
\boxed{
\text{These are preconditions for the current gate theorem,
not necessarily outside the scope of embedded decision theory in general.}
}
$$

This preserves the architecture without prematurely drawing disciplinary borders.

---

# 12. Press on the constitutional branch idea

PR91's branch deletion result is promising.

Make the abstract structure explicit.

Let

$$
\Gamma_X
$$

be a charter-anchored set of protected branches.

For each branch,

$$
A^\gamma_X\subseteq Q_X.
$$

Then robust constitutional adequacy could be

$$
A_X^{\rm const}
=
\bigcap_{\gamma\in\Gamma_X}
A^\gamma_X.
$$

The key condition is:

$$
\Gamma_X
$$

is indexed by the prestate charter, not recomputed from which branches remain physically available after the candidate action.

Prosecute whether this is just another application of anchored identity, or whether the decision layer needs additional semantics.

Try to state a clean **Branch Persistence Lemma**:

> If the protected branch index is prestate-anchored, an action cannot remove the branch from the gate merely by destroying its realization.

Clarify what evaluation is assigned when a protected branch becomes physically infeasible.

"Worst value" is one design choice; perhaps the more natural semantics is explicit violation/inadequacy rather than scalar worst value.

Prefer the adequate-set formulation if possible.

---

# 13. Refine the \(\Phi_C\) decomposition

Keep PR90's

$$
\Phi_C
$$

as a diagnostic, but press the PR91 insight that it lumps together structurally different failures.

The current taxonomy is:

* foreclosure;
* norm hacking / representation change;
* self-modification;
* trigger manipulation;
* captured evaluator;
* boundary escape.

Try to classify them by **where the failure occurs**:

### Index failure

The protected normative/branch index changes improperly.

Examples: branch deletion.

### Domain failure

The chooser is allowed to execute an authority-changing action without slow-lane authorization.

Examples: norm hacking.

### Level failure

Successor installation is not itself inside the constitutional gate.

### Provenance failure

The settlement/evaluator the gate reads is agent-controlled.

### Mediation failure

The physical action that changes the relevant structure lies outside the declared action alphabet.

This classification may be cleaner than repair types.

Then ask whether \(\Phi_C\) should remain central at all.

Perhaps the mature theory says:

$$
\boxed{
\Phi_C
\text{ is useful for diagnosing scalar agents,
but constitutional safety is primarily typed by index/domain/provenance/mediation failures.}
}
$$

Do not claim an incentive theorem where there is only exclusion by type.

---

# 14. Press on conflicts and inquiry

The current architecture says conflicting hard obligations can produce `conflict` and route to inquiry.

But the gate may jump discontinuously between:

$$
\text{choose}
\quad\leftrightarrow\quad
\bot.
$$

Try to decide whether the Normative Inductor's Progress theorem actually requires continuity through this transition.

Maybe it does not.

If \(\bot\) is explicitly charged at loss \(D\), a discontinuity in the *decision rule* may be acceptable provided the normatively uncertain/conflicted region itself incurs corresponding defect/residual.

Ask:

* Is "continuity through conflict" genuinely necessary?
* Can inquiry be treated as an ordinary adequate response under epistemic conflict?
* Should `⊥` sometimes be in the true adequate set?
* If so, can the same soft-gate theorem cover inquiry without a special mode?
* Can the reason representation compile a sentence:

  $$
  \operatorname{Adequate}(\bot)
  $$

  when conflict/uncertainty makes inquiry appropriate?

This may eliminate the special inquiry wrapper entirely.

That would be conceptually cleaner:

$$
\boxed{
\text{inquiry is a response, not an exception to decision theory.}
}
$$

Test this.

---

# 15. Question the threshold representation itself

PR91 uses prices of adequacy sentences and a threshold \(\tau\).

Ask whether this is the right general interface.

Alternatives:

### Direct region membership score

A response has an admissibility defect

$$
a_X(q)\ge0
$$

and the gate weights

$$
g(a_X(q)).
$$

### Signed adequacy margin

$$
m_X(q)
$$

with

$$
m>0
$$

adequate, \(m<0\) inadequate.

### Multiple reasons / constraint distances

Each response has vector defect

$$
d_r(q)
$$

and gating is based on a norm such as \(\max_r d_r(q)\).

Determine whether the adequacy-price formulation is merely one realization of a more abstract **continuous gate theorem**.

A useful abstraction may be:

Given scores \(s(q)\) such that

$$
q\notin A\Rightarrow s(q)\le0
$$

and some adequate \(q_0\) satisfies

$$
s(q_0)\ge2\delta,
$$

then a Lipschitz ramped chooser has mass-off bound proportional to score error.

If so, formalize this abstract version and make LI prices one corollary.

That could make the decision-theory result genuinely reusable beyond the current market realization.

---

# 16. Look for a characterization theorem for decision adapters

The round currently gives one positive construction and one hard-gate negative.

Ask whether we can characterize the relevant class more abstractly.

For finite \(Q\), true adequate set \(A\), and region \(K_A\), seek conditions on

$$
D:\mathbb R^Q\to\Delta(Q)
$$

such that

$$
\operatorname{massOff}_A(D(b))
\le
\kappa\,d_\infty(b,K_A)+\theta.
$$

A sufficient theorem might require:

1. region soundness:

   $$
   \sup_{u\in K_A}\operatorname{massOff}_A(D(u))\le\theta;
   $$
2. Lipschitzness:

   $$
   \|D(b)-D(u)\|_{\rm TV}
   \le
   \kappa\|b-u\|_\infty.
   $$

Then automatically:

$$
\operatorname{massOff}_A(D(b))
\le
\theta+\kappa d_\infty(b,K_A).
$$

This may be an extremely clean **abstract decision-adapter theorem**.

If so, the soft gate is merely a realization proving its own TV-Lipschitz constant.

This seems potentially more canonical than making `softGate` itself the conceptual endpoint.

Formalize if clean.

The theorem would say:

$$
\boxed{
\text{sound-on-region + Lipschitz chooser}
\Rightarrow
\text{PracticalCert}.
}
$$

That may be the mature decision-theory bill.

---

# 17. Try to separate theorem layers cleanly

The desired mature stack might become:

### Decision adapter characterization

$$
\text{sound on }K
+
\text{TV-Lipschitz}
\Rightarrow
\text{mass-off coupling}.
$$

### Soft gate realization

$$
\text{margin}
\Rightarrow
\text{sound + Lipschitz soft gate}.
$$

### Practical semantics

$$
\text{mass-off coupling}
\Rightarrow
\text{anchored loss bound}.
$$

### Normative Inductor

$$
\text{market defect control}
+
\text{anchored loss bound}
\Rightarrow
\text{Progress}.
$$

### Bounded competence

Optimization/learning inside the read-adequate support gives task performance.

### Dynamic legitimacy

Actions changing future admissibility are governed by slow-lane authorization.

### Corrigibility specialization

The admissibility map includes principal-authority/self-modification constraints.

Try to make outputs of each theorem exactly match inputs of the next.

This should be a core goal of the pressure pass.

---

# 18. Desired verdict refinement

Do not assume `GATE-NOT-UTILITY` remains the best verdict.

Possible more precise conclusions:

### `LIPSCHITZ-GATE-PAYS-THE-BILL`

if the key mathematical result is the adapter characterization.

### `STATIC-CHOICE-CLOSED / DYNAMIC-ADMISSIBILITY-OPEN`

if the static Normative Inductor decision problem is essentially resolved.

### `GATE-NOT-SCALARIZATION`

if "not utility" is too broad because utility can still govern within the gate.

I suspect the mature claim should be:

$$
\boxed{
\textbf{Normativity is not the task objective; it defines the admissible
choice structure within which bounded task optimization occurs.}
}
$$

That is more precise than "gate not utility."

---

# 19. Concrete output edits

Update the existing PR91 artifacts in place.

At minimum:

### `DECISION_THEORY_BILL.md`

* correct inquiry status;
* separate static bill from application-level task competence;
* consider abstract sound+Lipschitz characterization;
* expose margin/rate dependence.

### `NORMATIVE_CHOICE_THEOREM.md`

* distinguish Lean soft-gate theorem from wrapper inquiry;
* state the exact static theorem;
* weaken overclaims about non-compensation and reflection;
* sharpen genuinely open theorem targets.

### `CANDIDATE_DECISION_THEORIES.md`

* revise incomplete/lexicographic discussion so it does not claim every completion is scalar;
* clarify BRIA/endogenous admissibility;
* distinguish static gate from embedded decision theory.

### `CORRIGIBILITY_CONNECTION.md`

* replace "not decision theory" with "not discharged by this gate interface";
* sharpen index/domain/level/provenance/mediation taxonomy;
* be cautious about saying any part of \(\Phi_C\) is "solved."

### `FOR_HUMANS.md`

Make the core picture crisp:

> The Normative Inductor does not need a utility-maximizer that values normativity. It needs a chooser whose probability of taking an inadequate action changes continuously with the normative market's error. A soft adequacy gate supplies that. The unresolved agent-foundations problem begins when actions can change the future gate itself.

### `OPEN_PROBLEMS.md`

Rank at least:

1. margin realization and end-to-end rate compatibility;
2. gated bounded rationality with endogenous admissibility;
3. abstract sound/Lipschitz adapter characterization;
4. containment/alphabet completeness;
5. manipulation of constitutional settlement;
6. inquiry/conflict semantics;
7. improved \(\kappa\) constants / infinite menus.

---

# 20. Lean targets

Prioritize only mathematically earned abstractions.

Good possible additions:

### Abstract Lipschitz adapter lemma

If

$$
\operatorname{massOff}_A(D(u))\le\theta
\quad
\forall u\in K
$$

and

$$
\|D(b)-D(u)\|_{\rm TV}
\le
\kappa\|b-u\|_\infty,
$$

then

$$
\operatorname{massOff}_A(D(b))
\le
\theta+\kappa\,\operatorname{dist}_\infty(b,K)
$$

or the witness-point form used by the current theorem.

### Sharper soft-gate constant

Use total adequate denominator mass if it produces a cleaner theorem.

### Inquiry-as-action

Only if the semantics is clean enough that \(\bot\) can be treated as an ordinary response with adequacy conditions.

Do not formalize speculative dynamic BRIA machinery merely to have Lean output.

---

# 21. End with a hard research judgment

The pressure pass should answer:

### A. Is the static Normative Inductor decision-theory problem basically solved?

If yes, state the exact conditions and remaining semantic margin bill.

### B. Is the "soft gate" fundamental or just one realization of a more general sound/Lipschitz chooser?

Prefer the more abstract theorem if available.

### C. What is the actual new decision-theory problem now?

The leading candidate is:

$$
\boxed{
\textbf{bounded competence under an answerably evolving admissibility process
whose future state can depend on current actions.}
}
$$

### D. Does corrigibility add a new decision-theoretic type?

Current hypothesis:

$$
\boxed{\text{no at the static level}}
$$

—the constitutional constraint is another admissibility correspondence—

but:

$$
\boxed{\text{yes in theorem difficulty}}
$$

because it is self-referential and its settlement/provenance can be manipulated.

### E. Is reflective gate preservation actually a theorem?

Current answer:

$$
\boxed{\text{not yet.}}
$$

It is a domain/containment design condition plus strict-prestate authorization. Do not disguise this as reflective decision theory.

---

# 22. Research posture

Press harder on interfaces than on names.

Prefer statements of the form:

$$
\text{A concludes exactly what B needs as a hypothesis}
$$

over architectural prose.

Whenever a result is algebra/typing/definition, say so.

Whenever a supposed decision-theory theorem is actually:

* semantics,
* containment,
* provenance,
* or charter content,

move it to the correct layer.

The highest-value possible outcome of this pass is a compact mature theorem chain:

$$
\boxed{
\begin{array}{c}
\text{legitimate reason state}\\
\to
\text{adequacy semantics}\\
\to
\text{compiled normative region}\\
\to
\text{market proximity}\\
\to
\text{sound Lipschitz decision adapter}\\
\to
\text{low inadequate-action mass}\\
\to
\text{low practical loss}\\
\to
\text{Progress},
\end{array}}
$$

together with a precise statement that **the next unsolved layer is not static choice but dynamic bounded agency over an endogenously changing admissibility process**.

If that is what survives prosecution, make it the center of PR91.
 yes also add the bounded inductive rationality to sources
