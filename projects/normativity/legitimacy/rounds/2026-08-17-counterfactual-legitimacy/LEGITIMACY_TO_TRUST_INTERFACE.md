# Legitimacy to trust

## 1. What the deference line actually has

Cited by path against the tree at this branch's base, not from memory.

| statement | where | what it says | class |
|---|---|---|---|
| `GradeTrust EX W eta` | `lean/Workspace/Deference/Contrib/DelegationBridge.lean:52` | on every cell and every intervention, `A`'s conditional expectation of the quantity is within `eta` of the principal's grade | definition; **imported as a hypothesis** |
| `delegation_bridge` | same file, line 71 | under grade trust, delegating beats any measurable comparator by the principal's own grade margin, less `2·eta` on the disagreement region | proved, finite, exact-rational, Logical-Induction-free |
| `delegation_bridge_unconditional` | same file, line 97 | with no trust hypothesis, the deficit is at most `2B` on the disagreement region | proved |
| `FactorsThroughStaticView`, `value_eq_of_price_realization_eq` | `lean/Workspace/Deference/Contrib/StaticViewFactorization.lean:24,33` | a value factoring through price and realization cannot distinguish hidden authorization payloads | proved |
| faithful acceleration | `lean/Workspace/Deference/Contrib/FaithfulAcceleration.lean`; residue in `projects/deference/notes/LI_NATIVE_DEFERENCE.md` §3 | `A`'s quotes are forced by no-exploitation to track the principal's own later credences | proved modulo `hEC`, `hbias`, `hworld` |
| `lic_self_trust`, `lic_no_expected_net_update`, `lic_expected_future_expectations` | pinned FAF `Properties/SelfTrust.lean:377,338,323`, per `LI_NATIVE_DEFERENCE.md` §6 | asymptotic price/expectation relations of one inductor about its own later prices | proved in the dependency |
| `lic_wub_ofComputation_unconditional` | pinned FAF `Construction/Witnesses/FeedbackUnconditional.lean:42`, per `LI_NATIVE_DEFERENCE.md` §7 | weighted signed-bias convergence of current prices against a completed truth stream | proved in the dependency |
| Total Trust / Value / Tower | `projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §1.2 | self-endorsement family; `tower => Value` refuted at full menu-quantifier strength, `Mart => Value` refuted | mixed, several arrows refuted |

Two facts about this list decide the round.

`DelegationBridge.lean`'s own docstring says grade trust "is the source's
substantive hypothesis and it is imported, not derived — the source's §1.1 and §4
argue at length that no settlement instantiation in the skeleton produces it."
The operative trust predicate is an unmet hypothesis, and that is where anything
legitimacy can supply has to land.

`FINITE_MODEL_SKELETON.md` §3 says of `v̂⁺` and `v⁺`: "**No axiom relates `v̂⁺` to
`v⁺`.**" The skeleton has no object by which `A` influences the principal's
grade, so it cannot state the failure legitimacy exists to rule out. That absence
is the interface gap, not a defect of the skeleton.

## 2. The three columns

| deference trust requirement | what legitimacy supplies | irreducible extra assumption |
|---|---|---|
| `GradeTrust EX W eta` | that `W` is invariant under the advisor's residual latitude, so the hypothesis is a fact about the principal rather than something the advisor arranged | that `EX` is within `eta` of `W` — `A`'s outcome model actually tracks the principal's grades. This is competence and legitimacy cannot supply it |
| `delegation_bridge`'s conclusion | nothing directly; the theorem is already proved from grade trust | as above, plus `J` pointwise grade-maximal, which is definitional |
| faithful acceleration | nothing to the forcing, which the criterion supplies on its own; legitimacy supplies the **complement** — forcing gives accuracy about where the principal lands, legitimacy gives non-authorship of where it lands | `hEC`, `hbias`, `hworld`, unchanged and untouched by this round |
| `lic_self_trust` and the self-trust family | nothing | orthogonal: one inductor about its own later prices, no second party in the statement |
| `lic_wub_ofComputation_unconditional` | nothing yet | orthogonal-adjacent: it can consume a quoted future principal output, and says nothing about whether that output was authored |
| Total Trust / Value / Tower | nothing | orthogonal: self-endorsement, wrong object, and several arrows refuted independently |
| `value_eq_of_price_realization_eq` | the same moral for a different relation: authorization had to enter the type, and so does the normative transition semantics | none; this is a convergence, not a dependency |

Two rows are the round's answer and the rest are honest negatives.

## 3. Why the composition is not circular

`GradeTrust` is a joint condition on `EX` and `W`. It can be made true from
either side.

```
EX moves toward a fixed W      competence
W moves toward a fixed EX      capture
```

The predicate does not distinguish them and `delegation_bridge` does not care.
This is the dose-response note's T2(c) — "a steered pair *is* an honest pair" —
arriving in the finite kernel's own types, and it is exhibited here rather than
argued: `manufactured_trust` fixes `A`'s outcome model in advance, rating the
cheap intervention at 1 and the sound one at 0. In the uninfluenced arm the
principal's grade is the reverse and grade trust fails at every level below 1;
`delegation_bridge`'s inequality fails with it, so the hypothesis is not being
carried for form. The advisor then replaces the principal's adequacy relation.
The grade lands on `A`'s model exactly, grade trust holds at zero, the bridge
applies, and `DELEGATE` selects the intervention the environment convicts.

Every record-internal condition holds in both arms. Non-capture is what fires.

So the two hypotheses are about different things: legitimacy constrains `W` given
the advisor's policy space, competence constrains `EX` given `W`, and neither
mentions the other's conclusion.

## 4. The candidate theorem

Provisional, and stated at the strength the evidence carries.

> **Grade-integrity under legitimacy.** Let `V` be an advisor variation class
> over a fixture, `Z` the protected normative process, `W` the principal's grade,
> `EX` a fixed outcome model, `eta >= 0`. Assume
>
> - **H1** answerability — the four conditions and disclosure hold on every arm;
> - **H2** coverage — every due input arrives on every arm;
> - **H3** access — the advisor's policy does not determine which due inputs arrive;
> - **H4** non-capture — coupled arms of `V` at equal licensed-reason traces have equal `Z`;
> - **H5** grade factorization — `W` factors through `Z`;
> - **H6** epistemic adequacy — `GradeTrust(EX, W, eta)`;
> - **H7** `J` is pointwise grade-maximal.
>
> Then
>
> **(a)** `W` is constant across the coupled arms of `V` at equal traces, by H4 and H5;
> **(b)** hence `GradeTrust(EX, W, eta)` has one truth value across `V` — H6 is not
> a proposition the advisor selected;
> **(c)** hence `delegation_bridge` applies with a hypothesis that is a fact about
> the principal:
> `valuation(EX, sel) + gradeMargin(W, J, sel) - 2·eta·D(sel) <= valuation(EX, J)`.

**What legitimacy contributes that a generic competence assumption does not.**
H6 alone yields (c) — that is `delegation_bridge`, already in the repo. What
H1–H5 add is that H6 cannot be satisfied by the advisor. Drop them and
`manufactured_trust` exhibits an advisor for which H6 is false in one arm and
true in another, so the bridge's conclusion is bought rather than earned.

**H5 is load-bearing and is not free.** `grade_reads_outside` is the witness: a
grade reading a field the protected object does not cover flips grade trust while
every legitimacy clause stays silent. So H5 is what fixes how much the protected
object must cover, and the role-definition in `LEGITIMACY_INTERFACE.md` §1 is
what makes "cover" mean something other than "list more fields".

**(a) and (b) are checked, not proved.** They are one-line consequences of the
definitions, and the round verifies them over every scenario rather than
formalizing them: where non-capture holds the grade is invariant and grade trust
takes one value; where it fails the grade is not.

## 5. What this is not

It is not `Legit + EpistemicAdequacy => Trust`. Grade trust remains an
assumption; legitimacy makes it an *honest* assumption. The distinction between
"A trusts H⁺" and "A arranged H⁺ and then accurately predicts it" is exactly the
distinction between H6 holding as a fact about the principal and H6 holding
because H4 fails, and that is the whole of what this round buys on the trust
side.

It is not a claim that the delegation inequality is the right target. Whether
`W` — what the principal judged — tracks `X` — the quantity that matters — is
declared open by the skeleton itself: **"The relation between `v⁺` and `X` —
none"** (`FINITE_MODEL_SKELETON.md` §8.5). That is the single missing bridge
between this interface and a deference theorem worth the name, and no amount of
legitimacy work supplies it: it is a statement about the principal's competence
about the world, which is the same residue the third column names.

It is not a statement about `A`'s knowledge. H4 and H3 are semantic properties of
a variation class and the procedural round's record-equivalence argument says no
statistic of one realized trajectory determines them. A theorem may consume them
regardless. A deference *decision procedure* may not, and the epistemic lifting
problem — how `A` comes to be entitled to H4 — is stated in
`LEGITIMACY_INTERFACE.md` §7 and not solved.

## 6. A live maintainer decision this bears on

`DECISIONS.md`'s *Awaiting the author* carries "Rule on whether
endpoint-preservation is a target this program wants": the source corpus's
proposal that an advisor's influence is legitimate when it changes the rate of
the principal's deliberation and not its endpoint, measured by the influence
defect at the deliberation horizon
(`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md`
§1.5).

This round's object is the same shape and differs in two ways that the evidence
here decides against endpoint-preservation, and the round reports them rather
than taking the decision.

*It protects more.* Endpoint-preservation compares verdicts at the horizon. The
`transient_capture` witness is an advisor that moves a standard, lets a liability
close under it, and restores the standard before the horizon: the endpoint
agrees, the fate does not, and the target fails. Any endpoint condition misses
it.

*It permits more.* Endpoint-preservation is catalyst-not-reagent, so it refuses
any endpoint change, including one a licensed reason produced. The persuasion
control is the case, and an architecture that refused it would be refusing the
learning it exists to describe — which is the procedural round's finding about
prospectivity, arriving again.
