# Exact No Clean Self-Sealing audit

Status: adversarial correction to PR71; unregistered.

## 1. The relevance objection succeeds

PR71 assumes \(c\) is active before a route-destroying transition, then concludes that
`Implements` is false after it. This does not follow. Since

\[
\operatorname{Active}_h(c)
=c\in\Gamma_\sigma\land\operatorname{Rel}_h(c)
\land\neg\operatorname{Disp}_h(c),
\]

the factual condition supporting \(\operatorname{Rel}\) can cease during the same
transition. Then \(c\) is not active at \(h_{n+1}\), and its lack of a route does not
falsify `(IMP)`. PR71 mentions applicability preservation elsewhere but its theorem does
not assume the cross-prefix fact needed by this inference.

The exact theorem should assume \(\operatorname{Active}_{h_{n+1}}(c)\). A transition
rule may derive this from

\[
\operatorname{Active}_{h_n}(c)\land
\operatorname{PreserveRel}(h_n,h_{n+1},c)
\land\neg\operatorname{AuthorizedDisposition}(c),
\]

but the one-step theorem consumes only post-transition activity. This is weaker and
avoids classifying genuine external obsolescence as self-sealing.

## 2. Three applicability conditions

- **Inquiry-local preservation:** within one patch,
  \(\widehat A_c(\beta(q,z))=A_c(z)\) for all admissible \(q,z\). This prevents the
  information-gathering choice from changing whether the criticism applies.
- **Revision relevance transport:** a certified self-revision preserves the anchored
  relevance facts it is not authorized to change. This can establish
  `PreserveRel` across prefixes.
- **External evolution:** facts outside the protected revision can make applicability
  genuinely true or false. NCSS reads the resulting post-transition `Active`; it does
  not require invariance under arbitrary world evolution.

Target preservation and inquiry-local applicability preservation belong to route
adequacy. Revision relevance transport belongs to Proper Exercise of the transition.
Post-transition activity belongs to NCSS. They have different consumers and should not
be collapsed into one equation.

| transition | classification |
| --- | --- |
| monitored policy actually retires | genuine obsolescence if audited `Rel` becomes false; outside NCSS |
| stakeholder no longer affected | genuine obsolescence if world-level relation changes; outside NCSS |
| empirical precondition ceases externally | genuine obsolescence; outside NCSS |
| agent deletes the concept | world-level `Rel` stays true; NCSS applies |
| agent changes the world to evade applicability | NCSS applies if the protected condition remains; if it truly ceases, legitimacy of causing that change is a separate Proper-Exercise question |
| inquiry changes applicability | route fails inquiry-local applicability preservation and is not adequate for that target |

## 3. Local resolution adequacy

PR71's Coverage Resolution Soundness can be stated without the phrase “self-sealing.” A
proposed resolution certificate declares one of:

1. **covered:** for each criticism predicted active in the post-transition anchored
   contract state, it is represented or a named route is post-transition adequate;
2. **disposed:** an anchored disposition certificate covers it; or
3. **carried:** the successor set is nonempty and the continuation certificate transports
   the anchored contract and unresolved exceptions.

Call this predicate \(\operatorname{CloseAdequate}_n(q;g,S,\xi)\), where \(\xi\) is the
proposed post-transition contract certificate. Require every accepted resolution of a
coverage carrier to have such a certificate. A terminal resolution has \(S=\varnothing\),
so only `covered` or `disposed` can justify it.

This is local and checkable relative to the supplied semantic oracles: it checks one
resolution proposal, named route witnesses, post-state predictions, and dispositions. It
does not quantify over future histories or state NCSS as a premise.

The settled `Resolve_n(q;g,S)` reads the strict prefix and does not have a post-state
argument. No structural change is needed: `CloseAdequate` is a Coverage conformance
condition on the accepted resolution record/batch, and the anchored `Resolve` semantics
may require \(xi\). Treating a pre-state route as enough would be unsound when the same
batch destroys that route.

## 4. Corrected theorem

> **Exact No Clean Self-Sealing.** Let \(m_\sigma\) be live at \(h_n\), and let
> \(c\in\Gamma_\sigma\). Assume at \(h_{n+1}\):
>
> \[
> \operatorname{Active}_{h_{n+1}}(c),\qquad
> \neg\operatorname{Rep}_{h_{n+1}}(c),\qquad
> \neg\exists R\;\mathsf{Adeq}_{h_{n+1}}(R,c).
> \tag{POST-DEFECT}
> \]
>
> Assume every accepted resolution of the last live carrier is
> `CloseAdequate`, and use settled exact outstanding-set evolution and fresh-successor
> ancestry. Then
>
> \[
> \boxed{
> \operatorname{Live}_{n+1}(m_\sigma)\ne\varnothing
> \quad\land\quad
> \neg\operatorname{Implements}_{h_{n+1}}(\sigma).}
> \tag{Exact-NCSS}
> \]

**Proof.** `(POST-DEFECT)` directly falsifies `(IMP)`. If the last carrier is not
resolved, exact outstanding-set evolution preserves it. If it resolves, a terminal
successor set would make `CloseAdequate` require representation, an adequate route, or an
authorized disposition, contradicting `(POST-DEFECT)` and `Active`. Hence its successor
set is nonempty. Fresh successors are outstanding at \(h_{n+1}\) and remain descendants
of \(m_\sigma\), so the matter is live. ∎

The common narrative “the transition destroys the final adequate route” is a sufficient
way to derive the third post-defect clause when a route existed before and no replacement
appears. It is not a load-bearing theorem hypothesis. Likewise pre-transition activity
is historical context; post-transition activity is the exact logical requirement.

## 5. Circularity boundary

Local closure adequacy contains the normative safety rule that a defective contract is
not terminally discharged. No structural theorem can derive that rule. The theorem's
additional content is diachronic: exact Continuity turns rejection of terminal closure
into persistence of the old carrier or a fresh descendant with the same matter ancestry.

Therefore NCSS is not a deep discovery theorem, but it is not the tautology “assume NCSS,
prove NCSS.” Its semantic premise is one-step certificate adequacy; its conclusion is a
cross-prefix matter-persistence and implementation-failure statement.

## 6. Registration stages

Four states must remain distinct:

\[
\boxed{
\text{registration-capable route exists}
\ne\text{route exercised}
\ne\text{qualifying receipt obtained}
\ne\text{criticism registered}.}
\]

For an unrepresented \(c\), \(\mathsf{Adeq}_h(R,c)\) means that exercising \(R\) under
its certified conditions produces a sufficient receipt and invokes a
registration-capable compiler. It does not assert current \(\operatorname{Rep}_h(c)\).
PR71's prose mostly has this meaning, and its “route never exercised” fixture depends on
it. Its Python field `represented` is a counterfactual outcome field, so it measures
capability along \(\beta(q,z)\); the method name `actual_registration` was misleading and
is corrected in PR71.

## 7. Necessity

Dropping each item admits a finite countermodel:

- no pre-live matter: there is nothing Continuity can preserve;
- no post-transition activity: genuine obsolescence makes `(IMP)` vacuously true;
- already represented: `(IMP)` imposes no route;
- replacement route exists: `(IMP)` remains true;
- no local closure adequacy: an accepted terminal resolution closes cleanly;
- no exact outstanding-set evolution: the carrier silently disappears;
- no fresh-successor ancestry: a nominal successor need not be a live descendant.

These are checked exhaustively in `tests/test_audit.py`.
