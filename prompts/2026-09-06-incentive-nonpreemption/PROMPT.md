# Dispatch — 2026-09-06 incentive non-preemption

Verbatim as sent.

Work in `alignment-workspace`, building on the current corrigibility architecture round in **PR #89** (`projects/deference/rounds/2026-09-06-corrigibility-architecture/`) and the earlier deference / principal-mediation work.

This is a **research round**, not a consolidation pass.

The goal is to determine whether the new constitutional-corrigibility architecture admits a genuine and useful **incentive-level non-preemption corollary**, and exactly what remains between such a corollary and full Soares/CAST incentive corrigibility.

Do not weaken the distinction established by PR #89:

$$
\text{constitutional corrigibility}
\neq
\text{incentive corrigibility}.
$$

Do not simply add “the agent prefers to obey” as a hypothesis. The point is to see whether the existing deference/value machinery can derive an incentive statement from independently meaningful assumptions.

---

# 1. Read the relevant existing work first

At minimum inspect:

* PR #89 / `2026-09-06-corrigibility-architecture`, especially:

  * §8 behavioral compliance;
  * §11 provisional amendment;
  * §12 trigger integrity / free amendment;
  * §13 principal-side deference;
  * §14 theorem stack;
  * the explicit `CONSTITUTIONAL-NOT-INCENTIVE` verdict.

* the principal-mediated delegation / corrigibility round associated with PR #40:

  * `REPAIR_LEMMA.md`;
  * `PRINCIPAL_MEDIATION.md`;
  * `LI_PREDICTION_INTERFACE.md`;
  * the decomposition into `eps_pred`, `eps_over`, and `foreclosure_premium`;
  * the existing `delegation_bridge` Lean theorem it invokes.

* the summer deference / Total Trust / Value material:

  * exact arrow directions;
  * selected or gated trust statements if any;
  * `value_iff_totalTrust`;
  * the punishing-menu / conditional-stability negative;
  * the static-view / jurisdiction negatives;
  * the self-referential settlement-target negative.

* the current protected-value / authenticated-value correspondence theorem used by PR #89:

  $$
  \operatorname{Regret}_P(v^+)
  \le
  2\delta+2\zeta+\eta.
  $$

Do not infer that a result exists because a prose note gestures at it. Keep the repository's evidence classes straight.

---

# 2. First theorem target: Selected-Trust Non-Preemption

Fix one slow amendment case with a finite menu \(M\).

Let

$$
J\in M
$$

be the option selected by the **protected principal process**.

For every pair \(j,m\in M\), introduce two clearly distinguished comparison quantities.

### Principal comparison

$$
Y_{mj}
$$

is the protected / sealed principal-side value difference between executing \(m\) and \(j\).

The intended realization may be a sealed \(H^+\) value security, but define the abstract theorem without committing to LI first.

### Agent comparison

$$
X_{mj}
$$

is the difference in **\(A\)'s operative action value** between executing \(m\) and \(j\).

This must really be an action-value quantity. Do not silently replace it by:

> \(A\)'s prediction of what \(H^+\) will say.

That distinction is central.

For a candidate preemption policy / selector \(\sigma\), define selected events such as

$$
S^{\sigma}_{jm}
=
\mathbf 1[J=j,\sigma=m].
$$

Investigate a hypothesis of the form

$$
A_n\!\left[
S^\sigma_{jm}(X_{mj}-Y_{mj})
\right]
\le
\epsilon^\sigma_{jm}.
\tag{ST}
$$

This is an **\(A\to H^+\)** or \(A\to P^+\) selected-value-trust condition.

Determine the weakest sign/two-sided version actually needed.

Assume separately that the protected principal's selected action has low regret under \(Y\):

$$
A_n[Y_{\sigma J}]
\le r_P.
\tag{PR}
$$

Try to prove a finite theorem of the form

$$
\boxed{
A_n[X_{\sigma J}]
\le
r_P+\epsilon_\sigma
}
$$

with an explicit aggregation

$$
\epsilon_\sigma
=
\sum_{j,m}\epsilon^\sigma_{jm}
$$

or a sharper quantity if available.

Then derive

$$
\boxed{
\Delta_A^{\mathrm{choice}}
:=
\sup_{\sigma\in\Sigma}
A_n[X_{\sigma J}]
\le
r_P+\epsilon_{\rm ST}.
}
\tag{NP}
$$

Interpretation:

> relative to the specified preemption class, \(A\)'s own current action values give little advantage to replacing the protected principal's eventual choice with its own.

This is the central target.

## Prosecute the theorem

Check:

* whether pairwise selected trust is enough;
* whether signs have been reversed;
* whether the selector can depend on information not available at the relevant time;
* whether the theorem needs full menu quantification or only alternatives actually selected by \(\sigma\);
* whether random principal selection changes the statement;
* whether conditioning on \(S_{jm}\) creates zero-probability or selection pathologies;
* whether the theorem is merely algebra once the right assumption is stated.

If it is algebra, say so. The value of the result may be identifying the exact assumption the realization must supply.

---

# 3. Compose it with the protected-principal decision theorem

PR #89 already places the authenticated-value correspondence on the **principal side**.

Attempt the direct composition

$$
r_P
\le
2\delta+2\zeta+\eta.
$$

Hence derive

$$
\boxed{
\Delta_A^{\mathrm{choice}}
\le
\epsilon_{\rm ST}
+
2\delta+2\zeta+\eta.
}
\tag{A}
$$

Check the types carefully:

* what probability/credence evaluates \(r_P\)?
* what probability/credence evaluates selected trust?
* are both expectations under \(A_n\), \(H_n\), an authenticated correspondence, or different measures?
* if different, identify the exact transfer theorem required.

Do not write (A) unless these registers genuinely compose.

The sealed-target negative in PR #89 is load-bearing here. If the target reads the very \(A\)-quote used to predict it, then the existing \(\zeta\ge 1/2\) countermodel should make the bound vacuous. Preserve that negative.

---

# 4. Revisit the principal-mediation repair theorem

The earlier principal-mediated round proves a repair inequality of approximate shape

$$
V_A(\pi)-V_A(\operatorname{Repair}(\pi))
\le
2B\cdot
\operatorname{channelDisagreement}(\pi),
$$

with decomposition

$$
\operatorname{channelDisagreement}
=
\epsilon_{\rm acc}+\epsilon_{\rm over},
$$

where

$$
\epsilon_{\rm acc}\le\epsilon_{\rm pred},
$$

while `eps_over` was previously unbounded.

Read the old proof carefully and ask whether the new selected-value-trust theorem is **exactly a bound on the old `eps_over` term, or merely philosophically adjacent**.

Do not force them to match.

The old round describes `eps_over` as the value of \(A\)'s own preferred judgment over the principal's. If that can now be written as the selected operative-value difference \(X_{\sigma J}\), attempt to derive a composition of shape

$$
\boxed{
\Delta_A^{\mathrm{admissible\ preemption}}
\le
2B\epsilon_{\rm pred}
+
\epsilon_{\rm ST}
+
2\delta+2\zeta+\eta.
}
\tag{B}
$$

This is the main desired corollary.

Interpret the terms:

$$
2B\epsilon_{\rm pred}
=
\text{advantage of acting early because \(P\)'s choice is uncertain},
$$

$$
\epsilon_{\rm ST}
=
\text{\(A\)'s substantive disagreement with the protected principal},
$$

$$
2\delta+2\zeta+\eta
=
\text{imperfection of the protected principal's own amendment decision}.
$$

Test whether that decomposition is actually mathematically correct.

If the old repair theorem and the new selected-trust theorem use incompatible value registers, stop and isolate the missing bridge.

---

# 5. The critical missing bridge: epistemic prices versus operative action value

Investigate explicitly what an \(A\)-priced value security means.

There are at least three objects that must not be conflated:

1. \(A\)'s probability that \(H^+\) reports some value;
2. \(A\)'s expectation of a security settling to an \(H^+\)-evaluation;
3. \(A\)'s **own operative value difference** between two actions.

An incentive theorem requires (3).

Determine what interface would make a security price genuinely action-relevant.

A candidate is:

$$
\operatorname{AV}^A_n(m)
-
\operatorname{AV}^A_n(j)
\approx
A_n(X_{mj}),
\tag{DV}
$$

where \(X_{mj}\) is a utility/value security with a declared realization semantics.

Investigate whether any existing “utility securities” machinery actually supplies this, or whether it is currently just an idea.

This may be the correct narrow role for utility securities:

$$
\boxed{
\text{bridge LI prices to \(A\)'s operative decision values}.
}
$$

Do not make them the substrate of normativity or constitutional corrigibility.

If `(DV)` is an external decision-semantics contract, say so.

---

# 6. Separate admissible incentive compatibility from full incentive corrigibility

This distinction is mandatory.

Let

$$
\Pi_C
$$

be the constitutionally admissible policy class and

$$
\Pi_{\rm phys}
$$

the physically available policy class.

Define something like

$$
\Delta_A^{C}
=
\sup_{\pi\in\Pi_C}
\bigl[
V_A(\pi)-V_A(\pi_P)
\bigr],
$$

where \(\pi_P\) respects the protected principal process.

The theorem above may bound \(\Delta_A^C\).

But full incentive corrigibility concerns

$$
\Delta_A^{\rm phys}
=
\sup_{\pi\in\Pi_{\rm phys}}
\bigl[
V_A(\pi)-V_A(\pi_P)
\bigr].
$$

Introduce a residual **constitutional-violation premium**, perhaps

$$
\Phi_C
=
\sup_{\pi\in\Pi_{\rm phys}}
\left(
V_A(\pi)-V_A(R_C\pi)
\right)_+,
\tag{CV}
$$

where \(R_C\pi\) is a constitution-respecting repair when such a repair is defined.

Then investigate a decomposition

$$
\boxed{
\Delta_A^{\rm phys}
\le
\Delta_A^C+\Phi_C.
}
\tag{C}
$$

This is conceptually important even if the proof is trivial.

Do **not** set \(\Phi_C=0\) merely because a membrane makes violating policies inexecutable. That would turn an incentive theorem into the constitutional theorem by changing the feasible set.

The question is:

> How much would \(A\), by its own operative values, gain from violating the constitutional process if it physically could?

That is the Soares/CAST incentive question.

---

# 7. Revisit the old foreclosure premium

The principal-mediated round already discovered a failure mode:

> a policy can destroy the principal's options and then “defer” to the sole remaining option.

Its mediation repair can have zero cost while foreclosure itself has positive value.

Determine whether the old

$$
\texttt{foreclosure\_premium}
$$

is a finite-model instance or component of \(\Phi_C\).

If yes, formalize the relationship.

If not, explain why not.

This is important because it tells us whether the current constitutional architecture has localized the exact residual that separates:

$$
\text{non-preemption among admissible policies}
$$

from

$$
\text{no incentive to break the constitution}.
$$

---

# 8. Ambitious extension: selected trust over constitutional repairs

Ask whether selected-value trust can bound \(\Phi_C\) too.

Suppose for each audited violating policy \(\pi\) there is a constitution-respecting repair \(R_C\pi\).

Suppose the protected principal evaluation satisfies

$$
Y_\pi
=
V^+(R_C\pi)-V^+(\pi)
\ge 0.
\tag{PREF}
$$

Suppose \(A\)'s operative comparison is

$$
X_\pi
=
V_A(R_C\pi)-V_A(\pi).
$$

If one can establish

$$
A_n[X_\pi-Y_\pi]
\ge
-\epsilon_C,
\tag{CT}
$$

then derive

$$
V_A(\pi)-V_A(R_C\pi)
\le
\epsilon_C
$$

in the appropriate expected/selected sense, hence

$$
\Phi_C\le\epsilon_C.
$$

Then the full bound would have schematic form

$$
\boxed{
\Delta_A^{\rm phys}
\le
2B\epsilon_{\rm pred}
+
\epsilon_{\rm ST}
+
2\delta+2\zeta+\eta
+
\epsilon_C.
}
\tag{D}
$$

Do **not** present (D) as established unless every register lines up.

The point of the round is to determine whether (D) is a real theorem programme or hides the entire corrigibility problem inside `(PREF)` / `(CT)`.

In particular prosecute:

* Does defining \(V^+(\pi)\) for violating policies require evaluating worlds where the protected principal process itself has been destroyed?
* Can a sealed/sibling \(H^+\) evaluate such counterfactuals without being causally corrupted by \(\pi\)?
* Does \(A\)'s value comparison against those counterfactuals have a clean LI security?
* Is `(CT)` essentially equivalent to “\(A\) is already corrigible”?
* Does selected trust over all violating policies become too strong to be interesting?

A negative result here would be valuable.

---

# 9. Trigger manipulation and free amendment must remain separate

Even a successful non-preemption theorem does not solve:

### Trigger integrity

\(A\) causes \(P\) to issue a genuine fast-lane correction.

### Free amendment

\(A\) causes \(P\), through strategically selected truthful information, to choose delegation.

Do not absorb these into \(\epsilon_{\rm ST}\) unless there is an actual causal theorem.

In fact capture may not be an additive error at all. The previous principal-mediation work suggested that capture can destroy the very mapping required to define the repair comparison.

Try to state clearly whether:

$$
\text{non-capture}
$$

is a precondition for the incentive comparison, rather than a term in its error budget.

Relate this to the shared counterfactual frame and dose-response work, but do not claim that dose-response solves it.

---

# 10. Classify the strongest result honestly

At the end, classify the strongest theorem obtained into one of these levels:

### Level I — Choice Non-Preemption

Given a protected finite menu and selected-value trust,

$$
A
$$

has low regret for letting \(P\) choose rather than substituting its own menu item.

### Level II — Incentive-Compatible Mediated Delegation

Adds preparation/prediction effects and proves a bound such as (B) for a specified class of non-foreclosing admissible preemption policies.

### Level III — Constitutional-Violation Incentive Bound

Bounds \(\Phi_C\) for a specified class of authority-violating policies.

### Level IV — Incentive Corrigibility

Bounds the advantage of suppressing, inducing, manipulating, bypassing, or destroying the correction/amendment process itself, through self-modification and successor creation.

Do not call a Level I or II result “incentive corrigibility” without a qualifier.

A good name for Level II may be:

* **Non-Preemption Regret**;
* **Incentive-Compatible Mediated Delegation**;
* **Protected-Choice Incentive Compatibility**.

Choose only after seeing the theorem.

---

# 11. Negative controls

Construct tiny countermodels wherever possible.

At minimum test:

1. **No selected value trust:** perfect prediction of \(P\)'s choice, but \(A\) values the opposite action; preemption remains maximally attractive.

2. **No protected target:** \(H^+\) reads \(A\)'s quote; reproduce the \(\zeta\ge 1/2\) failure.

3. **No principal decision quality:** \(A\) perfectly trusts \(H^+\), but \(P\) systematically chooses the wrong menu option relative to \(H^+\).

4. **Foreclosure:** \(A\) leaves the final selector untouched but destroys all but its preferred option.

5. **Constraint-only versus incentive:** a membrane blocks preemption, but \(A\)'s counterfactual value for preemption remains high.

6. **Epistemic/operative mismatch:** \(A\) perfectly predicts \(H^+\) values while its own action utility is anti-correlated with them.

7. **Capture:** the same selected-trust-looking numerical relations can hold after \(A\) has causally selected the principal's evaluation process, unless protected-target assumptions exclude it.

8. **Menu selection / punishment:** re-run the relevant punishing-menu failure against any argmax Value step used.

A theorem that survives these would be substantially more credible.

---

# 12. What to formalize

If the Selected-Trust Non-Preemption Lemma is genuinely a finite algebraic theorem with clean assumptions, it is a good Lean target.

Prefer a theorem abstract over:

* finite menu \(M\);
* selector \(J\);
* alternative selector \(\sigma\);
* selected weights/events;
* two value-difference families \(X,Y\);
* a principal-regret hypothesis;
* selected-transfer inequalities.

Then derive the regret inequality.

Do **not** formalize the philosophical interpretation into Lean.

If composition with `DelegationBridge.lean` is type-clean, attempt a second theorem.

If it is not, document the exact mismatch rather than building an artificial adapter.

---

# 13. Deliverables

Produce:

### `INCENTIVE_CORRIGIBILITY.md`

The verification register containing:

* exact definitions;
* theorem statements;
* proofs/derivations;
* countermodels;
* status labels;
* relationship to PR #89 and the principal-mediated round.

### `FOR_HUMANS.md`

A compact explanation centered on:

> Constitutional corrigibility says \(A\) cannot legitimately get ahead of \(P\).
> The incentive extension asks whether, by \(A\)'s own current values, getting ahead of \(P\) would buy anything.

### `OPEN_PROBLEMS.md`

Rank the residuals, especially:

1. operative-value-security bridge;
2. \(A\to H^+\) selected value trust;
3. constitutional-violation premium \(\Phi_C\);
4. protected evaluation of violating counterfactuals;
5. trigger integrity;
6. free amendment/capture;
7. containment/boundary completeness.

### Lean, if earned

Port the abstract selected-trust lemma if it is clean and non-vacuous.

Do not touch canonical wiki/specification surfaces unless the dispatch separately grants that scope.

---

# 14. The conceptual standard

The round succeeds if it tells us exactly how far the following chain can be made mathematical:

$$
\boxed{
\begin{array}{c}
\text{constitutional corrigibility}\\
\text{defines the protected principal process and admissible boundary}\\
\downarrow\\
\text{principal-side value theorem}\\
\text{bounds how badly that process chooses}\\
\downarrow\\
\text{selected \(A\to H^+\) value trust}\\
\text{bounds \(A\)'s substantive incentive to substitute its own choice}\\
\downarrow\\
\text{principal-mediation repair}\\
\text{bounds the coordination advantage of preemption}\\
\downarrow\\
\text{constitutional-violation premium}\\
\text{isolates the remaining incentive to break the governance process itself}.
\end{array}
}
$$

The desired outcome is **not necessarily a full incentive-corrigibility theorem**.

A very good outcome would be a theorem such as

$$
\Delta_A^{\rm admissible\ preemption}
\le
2B\epsilon_{\rm pred}
+
\epsilon_{A\to H^+}
+
2\delta+2\zeta+\eta
$$

plus a proof that the only remaining step to full incentive corrigibility is a separately typed residual

$$
\Phi_C
$$

that current legitimacy/deference machinery does not bound.

That would sharply locate the frontier.

Spend most of the round trying to falsify this decomposition before consolidating it.
