# Dispatch — 2026-09-06 decision-theory bill

Verbatim as sent.

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
