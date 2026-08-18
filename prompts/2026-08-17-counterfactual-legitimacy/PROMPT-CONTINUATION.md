# Continuation round: close counterfactual legitimacy into a trust-facing legitimacy interface

*The second dispatch for this round, sent after the first pass opened its draft
pull request. It arrived quoted inside a longer message; the quoting markers are
removed and nothing else is changed. `PROMPT.md` is the first dispatch and is
unaltered.*

---

Continue work on the existing draft PR:

**PR #39 — `Counterfactual legitimacy: the architecture works and splits in two`**

Work on its existing branch:

`round/2026-08-17-counterfactual-legitimacy`

Do **not** create a parallel legitimacy PR unless a repository rule makes continuation impossible.

This is a continuation and prosecution of the existing round, not a fresh theory proposal. Preserve the current evidence and history. Amend the existing report/artifacts rather than silently replacing the earlier verdict.

Follow `AGENTS.md` exactly. Re-orient against current remote state before editing. Do not touch PR #38 / `traderized-enforcement` or PR #37 except to read if absolutely necessary.

---

# Goal

The current round has established a promising architecture:

[
\text{record-internal accountability}
+
\text{reason-mediated non-capture}
+
\text{protected access}.
]

But this is **not yet the object we ultimately want**.

The research target is a notion of legitimacy that can actually compose with the existing deference/trust program:

[
\boxed{
\operatorname{Legit}(H^+,A,\mathcal D)
+
\text{minimal explicit competence assumptions}
\Longrightarrow
\operatorname{Trust}_A(H^+;\mathcal D)
}
]

where `Trust` must be an actual theorem-facing trust property used or sought in the deference line, not a newly invented philosophical synonym for legitimacy.

Then downstream:

[
\operatorname{Trust}
+
\operatorname{ProtectedAuthority}
\Longrightarrow
\operatorname{NoPreemption/Delegation}.
]

**This continuation should push the legitimacy side as far as possible toward that first implication.**

Do not merely strengthen PR #39 until its own finite attack table is green. Ask whether the resulting object exports the mathematical facts the deference theory needs.

---

# Starting verdict from PR #39

Preserve these findings unless new evidence overturns them:

1. legitimacy/non-capture is not a unary predicate of one realized trajectory;
2. reason-mediated non-capture and protected access are independent;
3. a delivered licensed-reason trace alone is insufficient because the advisor may select which due reasons arrive;
4. the initial four-coordinate protected projection is insufficient; distinction-collapse forced an `identification`/merge coordinate;
5. non-capture must permit autonomous error, radical transformation, and genuine persuasion;
6. a counterfactual legitimacy standard cannot in general be certified from one realized record;
7. `due_pool` is currently stipulated rather than derived.

The task is to determine whether these can be sharpened into a **closed, principled, trust-facing legitimacy interface**.

---

# I. First kill test: universal deprivation

The current `access` condition compares advisor policies against one another:

[
D^\alpha_t=D^\beta_t.
]

This permits a failure in which **every policy in the variation class withholds the same due reason**.

Build that attack explicitly.

Require a fixture in which:

* a reason/input is genuinely due;
* every advisor policy in (V) prevents it from reaching the principal;
* delivered due-input streams are therefore invariant across (V);
* current protected access passes;
* the resulting trajectory misses something substantively important.

Determine what this means.

Do **not** simply patch `access()` until the test fails.

Decide whether the architecture needs a distinct property such as:

[
\boxed{\text{Inquiry/Coverage}}
]

requiring that sufficiently important due inputs actually arise and become accessible, rather than merely being advisor-policy-invariant.

Keep sharply separate:

[
\text{advisor cannot select access}
]

from

[
\text{the process actually has adequate access}.
]

If both are needed, preserve the split.

The mature interface may therefore be:

[
\text{answerability}
+
\text{inquiry/coverage}
+
\text{non-capture}.
]

Do not compress these unless a theorem justifies doing so.

---

# II. Second kill test: transient capture with endpoint restoration

The current protected projection (Z) is primarily an endpoint object.

Build a case in which the advisor:

1. temporarily alters protected normative machinery;
2. thereby changes a liability fate, judgment, inquiry, or later decision;
3. restores the protected machinery before the final horizon;
4. leaves:

[
Z_T^\alpha=Z_T^\beta
]

despite a lasting difference in the normative trajectory or consequential output.

Test whether the current condition misses it.

If it does, **do not merely add another endpoint coordinate**.

Prosecute whether the correct protected object is instead:

[
Z_{0:T},
]

a protected event trace, or—preferably—a more principled **normative transition interface/transducer**.

Candidate shape:

[
\mathcal N :
(\text{prior normative state},
\text{encounter},
\text{licensed reasons})
\mapsto
(\text{due burdens},
\text{licensed revisions},
\text{liability fates},
\text{new normative state}).
]

Then non-capture might ask for invariance/factorization of the **induced normative dynamics**, not an arbitrary finite list of fields.

The purpose is to solve the current projection-closure problem in principle, not by discovering field six.

---

# III. Close the protected-object problem

PR #39 currently has:

```text
ProtectedNormativeProjection =
  generation
  entitlement
  bearing
  adequacy
  identification
```

and explicitly has no closure theorem.

This is not an acceptable final legitimacy interface if its meaning is "the coordinates our current attacks happened to touch."

Try to replace the open-ended coordinate list with a **role-defined protected object**.

Possible directions include:

* the transition relation determining what counts as `Due` and `Licensed`;
* the inferential/answerability practice itself;
* the induced mapping from reasons and encounters to liability creation/revision/discharge;
* an equivalence class of implementations with the same normative transition semantics.

A good object should automatically include merge/identification policy because it affects liability identity, without naming `identification` as a special case.

Acceptance criterion:

> Explain why attacks C/E/G/H/I/L alter the protected object for one common structural reason.

If no principled closure is available, produce the sharpest counterexample and leave the problem explicitly open. Do not declare a five-coordinate constitution final.

---

# IV. Refine `Due`

The current round identifies this as load-bearing:

> protected access needs a `Due` whose extension the advisor cannot select within.

Develop this substantially further.

The crown-jewel learning interface already has:

```text
Due : S -> D -> Prop
```

and says `Due` is determined by the public pre-action state, causal, non-anticipating, and not defined by performance.

Determine what additional structure legitimacy requires.

In particular separate:

1. **arising** — what encounter/question/reason becomes normatively relevant;
2. **due-ness** — what presently calls for an answer;
3. **availability** — what can actually reach the principal;
4. **service** — whether the process investigates/responds.

Ask whether `Due` itself should be advisor-independent, or whether advisor independence belongs to a counterfactual condition over the process generating `Due`.

Avoid simply stipulating an omniscient exogenous `due_pool` if a relational or procedural formulation can do the work.

But do not smuggle `L*`/normative truth back into `Due`.

Required control:

* the same `Due`/access structure should be compatible with an autonomously mistaken principal.

---

# V. Refine `Licensed`

Preserve the current finding that a reason must be individuated finely enough to determine what change it licenses.

Try to connect this directly to the mature learning interface:

```text
Licensed : S -> D -> A -> Prop
```

A reason-mediated legitimacy condition should quantify over **licensed transitions/responses**, not over names of messages.

Candidate abstraction:

[
\operatorname{LicensedStep}(S_t,d,r,S_{t+1}).
]

Determine whether that is actually required or whether the existing `Licensed(S,d,r)` plus a transition semantics is sufficient.

Preserve:

* provenance/scope correctness;
* reason-connectedness;
* defeater-respect;
* loss-blindness;
* non-laundering.

Do not define licensing by "whatever transition happened."

---

# VI. Reconcile with the best current answerability apparatus

Read the current relational-scorekeeping, procedural-legitimacy, and crown-jewel learning artifacts.

The existing answerability apparatus is not assumed final.

The continuation must report:

[
\boxed{\text{what the final scorekeeping/answerability theory must export}}
]

to support legitimacy.

At minimum evaluate whether the mature substrate needs:

* standing / provenance;
* `Due`;
* licensed response/revision;
* liability identity;
* branching liability fate;
* split/merge transport;
* disclosed revision of normative standards;
* inquiry/coverage;
* an arising interface;
* protected normative transition semantics.

Do not redesign all of scorekeeping unless necessary to answer the interface question.

The output should constrain that later rebuild.

---

# VII. The trust-facing requirement

This is the most important new part of the continuation.

Read the current deference corpus and identify the **actual trust properties** currently needed or available.

At minimum inspect:

* `projects/deference/notes/LI_NATIVE_DEFERENCE.md`;
* `FINITE_MODEL_SKELETON.md`;
* the current corpus reconciliation;
* faithful-acceleration / dose-response material;
* existing trust/self-trust / future-H⁺ interfaces;
* any currently named SelectedTrust, future-human-selected trust, calibration, feedback-unbiasedness, or analogous theorem-facing conditions that are genuinely present in the repo.

Do not rely on remembered terminology. Cite exact current paths/statements.

Produce a document such as:

`LEGITIMACY_TO_TRUST_INTERFACE.md`

with three columns:

| deference trust requirement | what legitimacy can plausibly supply | irreducible extra assumption |

For every trust property, ask:

[
\text{Does legitimacy entail it?}
]

If not:

[
\text{Does legitimacy + a clearly isolated competence assumption entail it?}
]

If not:

[
\text{Is this trust property simply orthogonal to legitimacy?}
]

The desired decomposition is something like:

[
\boxed{
\operatorname{Legit}
+
\operatorname{EpistemicAdequacy}
\Longrightarrow
\operatorname{Trust}
}
]

rather than:

[
\operatorname{Legit}
+
\operatorname{Trust}
\Longrightarrow
\operatorname{Trust}.
]

If the latter is all that can be obtained, say so. That is a major negative result.

---

# VIII. Try to state the Legitimacy-to-Trust theorem

By the end of the round, write the strongest **honest candidate theorem statement** supported by the interface analysis.

It may be conditional or conjectural.

Schematic target:

[
\begin{aligned}
&\operatorname{AccountableTrajectory}(H^+)\
&\wedge\operatorname{InquiryAdequate}(H^+)\
&\wedge\operatorname{ReasonMediatedNonCapture}(H^+,A,V)\
&\wedge\operatorname{ProtectedAccess}(H^+,A,V)\
&\wedge\operatorname{EpistemicAdequacy}_{\mathcal D}(H^+)\
&\Longrightarrow
\operatorname{Trust}^{\text{deference}}_A(H^+;\mathcal D).
\end{aligned}
]

But **do not preserve this shape if the repo's actual trust predicate demands another one**.

Use the actual deference target.

Identify exactly which hypotheses come from:

* normativity;
* anti-capture;
* inquiry;
* epistemic competence;
* logical-induction machinery;
* representation/quotation;
* anything else.

The theorem statement must make clear what legitimacy contributes that a generic competence assumption does not.

---

# IX. Attempt a finite composition witness

If feasible without inventing a fake trust theorem, build the smallest finite model in which:

1. a principal satisfies the matured legitimacy interface;
2. a future recommendation/judgment is generated;
3. a present evaluator has a trust-like choice between:

   * respecting the future principal-generated judgment;
   * substituting its own;
4. legitimacy removes a steering/self-fulfilling-trust failure that would otherwise invalidate the trust interpretation.

The point is **not** to prove the final deference theorem in a toy model.

The point is to demonstrate that legitimacy changes the semantics of a trust premise:

[
A\text{ trusts }H^+
]

becomes different from

[
A\text{ arranged }H^+\text{ and then accurately predicts it}.
]

If this cannot be represented without rebuilding the deference model, report exactly why.

---

# X. Distinguish legitimacy from authority/efficacy

Do not absorb the entire corrigibility problem into legitimacy.

Preserve the distinction:

[
\operatorname{Legit}(H^+)
]

= the normative process deserves standing / is not captured,

versus

[
\operatorname{EffectiveAuthority}(H^+)
]

= the principal actually retains robust ability to exercise correction/control.

The latter belongs to the protected-control/foreclosure line unless a theorem forces overlap.

The desired downstream architecture is allowed to be:

[
\operatorname{Legit}
+
\operatorname{Trust}
+
\operatorname{EffectiveAuthority}
\Rightarrow
\operatorname{NoPreemption}.
]

Do not make legitimacy synonymous with "everything needed for corrigibility."

---

# XI. Assurance/auditability boundary

PR #39 correctly notes that a counterfactual property is a good standard and a bad one-run test.

Close this conceptually.

For each mature legitimacy clause, classify how it could enter a theorem:

1. **architectural assumption** — guaranteed by system design/action-space restriction;
2. **physically instantiated audit** — alternative arms are actually run;
3. **derived property** — follows from some stronger formal model;
4. **self-certification only** — reject as insufficient unless backed by 1–3.

The legitimacy-to-trust theorem may consume a semantic property without the agent being able to verify it from one history. That is acceptable.

But do not equivocate between:

[
\text{legitimacy holds}
]

and

[
A\text{ knows legitimacy holds}.
]

If deference requires the latter, state the epistemic lifting problem explicitly.

---

# XII. Mandatory new prosecutions

Add explicit fixtures/tests for at least:

1. universal withholding of one due reason across every advisor policy;
2. transient capture + endpoint restoration;
3. temporary standard change causing irreversible liability/judgment effect;
4. same protected transition semantics under a representational rename;
5. an additional arbitrary state coordinate that is irrelevant, to show the protected object is semantic rather than "all mutable fields";
6. autonomous error under full inquiry;
7. licensed persuasion under full inquiry;
8. advisor-originated genuinely novel reason that was not antecedently due;
9. due reason withheld selectively;
10. due reason universally unavailable for reasons independent of the advisor;
11. advisor creates the circumstances generating a due reason;
12. advisor suppresses those circumstances;
13. push-then-restore attack;
14. one trust-facing finite witness or an explicit reason it cannot yet be built.

Retain all previous tests.

---

# XIII. Desired mature decomposition

Do not assume this exact answer, but test whether the evidence supports something near:

[
\boxed{
\begin{aligned}
\textbf{Internal accountability:};&
\text{standing/provenance}
+RR
+DA
+\text{disclosure}\
\textbf{Inquiry adequacy:};&
\text{due demands actually arise and can be serviced}\
\textbf{Counterfactual non-capture:};&
\text{advisor influence factors through licensed reasons}\
\textbf{Protected access:};&
\text{advisor cannot select which due inputs reach the process}\
\textbf{Legitimacy:};&
\text{the appropriate composition of the above}.
\end{aligned}
}
]

The point of the round is to decide which lines really survive and how they should be typed.

---

# XIV. Success criteria

## Full success

The continuation yields a legitimacy interface which:

* has a principled protected object rather than an attack-generated coordinate list;
* handles transient capture;
* distinguishes anti-selection of access from actual inquiry coverage;
* permits autonomous error;
* permits radical legitimate revision;
* permits genuine persuasion;
* handles selective information;
* handles control over what arises;
* states exactly what `Due` and `Licensed` must export;
* identifies how the property is assured counterfactually;
* and maps nontrivially into an **actual deference trust predicate**.

"Maps nontrivially" means legitimacy eliminates or supplies a premise that would otherwise have to be assumed as trust/anti-steering wholesale.

## Strong partial

Everything above except the final legitimacy-to-trust implication, with a sharp theorem-facing statement of the remaining missing lemma.

This is acceptable if the remaining obstacle is genuinely deference mathematics rather than vagueness in legitimacy.

## Negative

Any of:

* no principled protected object exists beyond enumerating coordinates;
* trajectory-sensitive non-capture rejects legitimate learning;
* adequate inquiry requires importing normative truth;
* legitimacy contributes nothing to the actual trust predicate;
* the only route to trust assumes essentially the full trust property already;
* or the counterfactual semantics cannot compose with the deference model's types.

A sharp negative result is preferable to a patched positive one.

---

# XV. Deliverables

Extend the existing round directory rather than creating a disconnected theory tree.

Add or substantially revise:

* `COUNTERFACTUAL_INTERFACE.md`
* `MODEL.md`
* `PROSECUTION.md`
* `BOUNDARY.md`
* `THEOREM_MAP.md`
* `REPORT.md`

and add:

* `LEGITIMACY_INTERFACE.md`
* `LEGITIMACY_TO_TRUST_INTERFACE.md`

if the evidence warrants those names; all names remain provisional.

Add code/tests for every new finite witness.

Preserve the original prompt verbatim. Record this continuation prompt separately under the same prompt family or a clearly linked continuation directory according to repository convention.

Do not edit the wiki.

Do not register substantive claims.

Do not Lean-formalize provisional ontology merely to make it look stronger.

---

# XVI. Final verdict

Replace the current one-line verdict only if the evidence actually earns a stronger one.

The report must end by answering these questions separately:

1. **Do we now have a principled definition/interface for a legitimate normative trajectory/process?**
2. **Is the protected object closed by role rather than by enumeration?**
3. **Have inquiry/coverage and advisor-independent access been cleanly separated?**
4. **Does the legitimacy notion survive transient-capture prosecution?**
5. **Exactly which existing deference trust property can consume it?**
6. **What additional competence assumption is irreducible?**
7. **Can we now state a non-circular Legitimacy-to-Trust theorem?**
8. **If not, what single missing mathematical bridge prevents it?**

The research target is:

[
\boxed{
\text{conditions on how }H^+\text{ reasons, revises, and remains uncaptured}
\Longrightarrow
\text{a trust property that makes preserving }H^+\text{'s authority rational for }A.
}
]

Do not stop at "counterfactual legitimacy looks plausible." Push until this composition is either explicit or sharply blocked.
