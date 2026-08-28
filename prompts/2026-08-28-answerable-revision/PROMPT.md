# Answerable Revision under revisable warrants

One dispatch, 2026-08-28, phase II. Verbatim as received.

I’d dispatch this as a two-phase prompt: **close PR60 cleanly, merge it, then immediately start a fresh theorem round one level up**. The new PR should treat PR60 as a lemma/result, not keep modifying it.

````markdown
# Finish PR60, merge, then open a new Answerable Revision theorem round

Work in:

`A-M-Berns/alignment-workspace`

This task has TWO phases, in order.

1. Finish and merge PR #60.
2. From updated `main`, open a NEW branch/PR pushing the next theorem:
   **Answerable Revision under revisable comparison warrants.**

Do not use Lean.

Do not reopen the frozen Legitimate Evolution package unless you find an actual false
claim in it.

Do not turn the new round into another online-learning implementation round. PR60 has
done that work. The new round is primarily semantic/theorem-design work with small
executable countermodels where useful.

---

# PHASE I — finish and merge PR60

Current PR:

- PR: `#60`
- branch: `round/2026-08-27-legitimate-improvement`
- headline verdict:
  `NO-FREE-EVASION-SURVIVES-BUT-EVIDENCE-INTERFACE-OPEN`

The latest prosecution found and repaired:

- the invalid stochastic-matrix power-iteration assumption;
- the incorrect local computation of AdaNormalHedge's global `B`;
- the overstrong claim that a surgical repair automatically empties the LIVE cell;
- the conceptual conflation between improvement evidence and uptake regret.

It also established executable independence between:

```text
improvement evidence
    Δ_t(b,r) = <b_t,l_t> - <b_t M_r,l_t>

uptake regret
    Δ_t(p,r) = <p_t,l_t> - <p_t M_r,l_t>
````

with:

* evidence positive / uptake regret zero;
* uptake regret positive / demonstration absent.

And it found the open seam:

> Different admissible baselines can yield different answers to whether a repair has
> become a demonstrated improvement.

This is why the honest PR60 verdict is NOT `PR60-CLEAN-MERGEABLE` in the sense of
"the full evidence semantics is solved."

It IS intended to be mergeable as an **unregistered research round whose explicit open
question is the evidence interface**.

## 1. Check the current gate

Inspect current PR60 HEAD and CI.

If the gate is green, proceed.

If it is red:

* diagnose the failure;
* repair only failures caused by PR60;
* rerun the repository gate;
* do not broaden scope.

Do not merge a red gate.

## 2. Final PR60 consistency pass

Before merge, confirm that all prose and tests consistently reflect the prosecution.

PR60 should now say clearly:

### What is established

1. **Theorem A**
   A pure wide-range / repair-regret kernel.

2. **Theorem B**
   A generic witness adapter of the form

   `Adv >= eps D_live - xi`
   implies
   `D_live <= (B + xi)/eps`.

3. **Theorem C / No Free Evasion**
   Conditional on a supplied improvement-evidence semantics and a supplied challenge
   constitution:

   > Once a repair has been demonstrated and its withdrawal activates a challenge, later
   > diagnosed conduct cannot become normatively invisible merely because the repair was
   > withdrawn. The relevant demand remains outstanding or is explicitly resolved.

### Three separate interfaces

PR60 should make this conceptual split unmistakable:

```text
EVIDENCE
Why is r an improvement relative to some baseline b?

UPTAKE / REGRET
While r is a live comparison, is the actual process leaving its advantage unused?

ANSWERABILITY
Once evidence has generated a challenge, what happens if r or the comparison surface
is later withdrawn?
```

The key conceptual statement is:

> **Challenge formation is grounded by demonstrated comparative evidence, not by actual
> regret.**

`challenge.py` should not depend on regret quantities.

### What remains open

Especially:

* no generic derivation of the evidence baseline;
* no claim that predictability + precommitment makes a baseline normatively privileged;
* pre-demonstration evidence suppression remains open;
* evaluator manipulation remains open;
* indefinite contest remains possible;
* `SETTLED` means explicitly resolved, not correct;
* delay remains open;
* long-horizon / policy improvement remains open.

Reclassify the old "CM2 = Coverage" language if any remains.

The more exact boundary is something like:

> **pre-demonstration evidence suppression / opportunity control / self-blinding**

and only some consumers may instantiate this as ordinary Coverage.

## 3. Preserve provisional status where appropriate

Do NOT falsely freeze:

* `BASE_POLICY`;
* one universal evidence baseline;
* evidence threshold semantics;
* the exact challenge key unless the round has earned it;
* designation as universally challenge-generating;
* evaluator independence;
* any human/H+ interpretation.

It is fine for PR60 to merge with:

`NO-FREE-EVASION-SURVIVES-BUT-EVIDENCE-INTERFACE-OPEN`.

That is an informative successful research verdict.

## 4. Merge PR60

Once:

* current gate is green;
* docs match the final semantics;
* no known correctness bug remains in claims the PR actually makes;

merge PR60 using the repository's normal merge convention.

Record the merged SHA.

Then update local/research state from `main`.

Do NOT continue the next round on the PR60 branch.

---

# PHASE II — new theorem round: Answerable Revision

Create a fresh branch from updated `main`.

Suggested branch:

`round/2026-08-28-answerable-revision`

Suggested PR title:

`Legitimacy: answerable revision under revisable warrants`

Names are provisional under `AGENTS.md`.

The purpose of this round is to move ONE LEVEL ABOVE PR60.

PR60 says:

> once a particular demonstrated repair has generated a challenge, withdrawing the repair
> cannot silently erase the resulting demand.

The new question is:

> **What if the standards determining which comparisons count as reasons for revision are
> themselves revisable?**

We want to know whether there is a more general theorem in which:

```text
P_t        substantive policy / procedure
Lambda_t   evaluator / audit standard
W_t        comparison warrant: what evidence is entitled to count as a reason for revision
```

may ALL legitimately change over time.

The invariant should not be a fixed substantive target.

The candidate invariant is:

> **A reason legitimately generated under the standards then in force cannot be
> retroactively erased merely because those standards later change.**

---

# 5. Central conceptual architecture

Treat these as separate stages:

```text
counterfactual comparison
        |
        v
comparative evidence E
        |
        | interpreted under standing warrant W_t
        v
promotion to revision reason rho
        |
        +-----------------------------+
        |                             |
        v                             v
live repair / response          later change to P, Lambda, W,
        |                       repair availability, etc.
        v                             |
repair-regret / uptake                v
                              answerability of rho
```

The new theorem should focus primarily on the bottom-right structure:

> **Once `rho` has legitimately been generated, later normative revision does not erase
> its historical incurrence.**

PR60's regret theorem may be reused on the left branch.

Do not require regret to prove the core Answerable Revision theorem.

---

# 6. Introduce a provisional notion of comparison warrant W

Do NOT assume one canonical baseline.

A warrant should capture something like:

> Under these conditions, evidence of this comparative form is entitled to count as a
> reason concerning this target subsystem.

A provisional semantic shape might be:

```text
W =
    target subsystem sigma
    admissible baseline generator/class
    admissible repair/comparator class
    evaluator/audit jurisdiction
    context class
    promotion rule
```

But derive the smallest interface rather than blindly implementing this tuple.

Examples of warrant standing may include:

* incumbent procedure as baseline;
* previously endorsed procedure as baseline;
* authorized external benchmark;
* explicitly registered challenge;
* shadow execution of an incumbent protocol.

The generic theorem should NOT decide which of these is morally correct.

It should be parametric over legitimately standing `W`.

---

# 7. Promotion is the semantic hinge

The central new event is something like:

`Promote(W_t, E) = rho`.

Meaning:

> Under the warrant legitimately standing at strict prestate `t`, evidence `E` counts as
> a revision reason `rho`.

Important distinctions:

```text
true counterfactual comparison
!=
admissible evidence
!=
reason for revision
!=
Due obligation
```

Do not collapse them.

In particular:

* epistemic validity makes a comparison a valid comparison;
* warrant standing gives it normative relevance;
* promotion generates a reason;
* supplied Due semantics may or may not make that reason an immediate obligation.

Determine whether promotion should itself be represented as:

* a `ReasonOcc`;
* a derived relation from existing RI objects;
* or another sidecar record referencing existing occurrences.

Prefer existing `ReasonOcc` if it fits naturally.

Do not add a new RI event kind unless forced.

---

# 8. Main theorem target: Answerable Revision

Try to state the strongest clean result of the following flavor.

At strict prestate `t`:

```text
Standing(W_t)
Admissible_Wt(E)
Promote(W_t,E) = rho
```

Then `rho` becomes historically incurred / represented.

For later `s > t`, even if:

```text
P_t      -> P_s
Lambda_t -> Lambda_s
W_t      -> W_s
```

the process cannot make the historical incurrence of `rho` vanish merely through those
changes.

A candidate theorem shape is:

```text
Promoted_t(rho)
   =>
for every later s,
    Outstanding_s(rho)
    or Answered_s(rho)
```

with appropriate treatment of:

* incorporation;
* defeat;
* supersession;
* transfer/carry;
* explicit rejection.

The theorem should permit the process to conclude:

> "rho was legitimately generated under W_t, but later reasons defeat it."

It should prohibit:

> "W_t no longer exists, therefore rho was never a reason."

That is the central laundering attack.

---

# 9. Strict-prestate requirement

This round should test whether strict-prestate semantics gives the correct
non-circularity.

In particular:

`W_{t+1}` must not be able to authorize the evidence or promotion event that creates
`W_{t+1}` at the same step.

The intended shape is:

```text
W_t evaluates/promotes evidence at t
normative revision then produces W_{t+1}
```

not:

```text
W_{t+1} retroactively licenses its own creation
```

Build an executable same-step self-authorization countermodel and ensure the intended
interface rejects it.

---

# 10. W itself must be revisable

Do NOT solve the problem by fixing an eternal meta-warrant.

The round must explicitly permit:

`W_t -> W_{t+1}`

through ordinary legitimate normative revision.

The fixed substrate should be as weak as possible:

* how current warrant standing is identified;
* how a standing warrant is interpreted at strict prestate;
* how a promotion occurrence is recorded;
* how later reasons remain historically incurred;
* how normative revisions acquire standing.

Substantive warrant contents should remain revisable.

---

# 11. Reflective application: warrants criticizing warrants

Test the level-polymorphic case.

Suppose `W_t` allows some admissible comparison concerning warrant protocol `W_t` itself
or another warrant `W'`.

Then evidence yields:

`rho_W = reason to revise W`.

If the process then changes `W`, does the already-generated `rho_W` remain answerable?

The desired answer is yes.

This should work without inventing:

`W^0, W^1, W^2, ...`

as an infinite meta-hierarchy.

The same warrant/reason machinery should be able to target warrant protocols themselves.

If this requires an immutable substantive meta-warrant, report that as a failure of the
ambitious architecture.

---

# 12. Central countermodels

Build small executable or symbolic fixtures for at least these.

## AR1 — policy revision after promoted reason

* W standing;
* evidence promoted to rho concerning policy P;
* P changes;
* rho must remain outstanding or answered.

Expected: caught.

## AR2 — warrant revision after promoted reason

* W_t promotes rho;
* W_t is legitimately replaced by W_{t+1};
* W_{t+1} would not have promoted the same evidence.

Question:
Does rho remain historically answerable?

Expected: yes.

This is the crown-jewel fixture.

## AR3 — evaluator revision after promoted reason

* W_t + Lambda_t generate/promote rho;
* Lambda changes later.

Historical reason must not disappear merely because the scoring standard changed.

Expected: answerability survives; substantive defeat may be possible.

## AR4 — retroactive invalidation

After promotion, process changes W and declares:

> evidence of that old kind never counted.

Expected:
This may change current endorsement but cannot erase historical incurrence.

Distinguish:

```text
historical legitimacy of rho's occurrence
vs
current endorsement of rho's force
```

## AR5 — legitimate defeat

* rho generated;
* later reasons S explicitly defeat rho;
* Resolve accepts the defeat.

Expected: ANSWERED/SETTLED, not a theorem violation.

## AR6 — trivial defeat semantics

Resolve simply accepts "no."

Expected:
structurally answered.

The theorem must not claim the answer is substantively good.

## AR7 — supersession

* rho recommends repair r;
* later repair r' addresses the same concern better;
* rho is superseded/answered by r'.

Test whether existing carry/Resolve machinery can express this without bespoke machinery.

## AR8 — same-step self-authorization

W_new is invoked to justify the evidence/promotion that installs W_new.

Expected: rejected by strict-prestate semantics.

## AR9 — preemptive self-sealing

Before criticism of W crosses the promotion threshold:

* W revises itself to prohibit that criticism.

Expected:
NOT caught by Answerable Revision because no rho yet exists.

This is an explicit boundary.

Classify it as a future:

* reflective openness;
* evidence-service;
* anti-self-sealing;
* anti-manipulation

problem.

Do not hide it.

## AR10 — criticism of a warrant

Standing warrant W allows comparison of warrant protocols.

Evidence criticizes W itself and generates rho_W.

Then W changes.

Expected:
rho_W remains answerable.

This tests whether the theorem is genuinely reflective.

---

# 13. Separate historical validity from current endorsement

This distinction is central and should be explicit.

We want to permit:

```text
At t:
    W_t legitimately promoted rho.

At s:
    W_s no longer endorses the substantive inference embodied in rho.
```

Both may be true.

The process may say:

> "This really was a reason we incurred under our then-legitimate standards.
> We now reject its force for reasons S."

That is legitimate revision.

What must be forbidden is:

> "Because our standards changed, there never was an answerability relation."

Try to formalize:

```text
OccurredLegitimately(rho,t)
```

separately from something like:

```text
CurrentlyEndorsed(rho,s).
```

Do not require current endorsement for historical answerability.

---

# 14. Relation to PR60

Reuse PR60 rather than duplicating it.

PR60 should become a special case / lemma of the new architecture.

Try to show:

```text
PR60 demonstration
    =
one particular promotion rule under one particular W

PR60 withdrawal challenge
    =
one particular Answerable Revision instance
```

If this specialization is unnatural, that is evidence the new abstraction is wrong.

State explicitly what PR60 contributes:

* evidence/regret separation;
* repair-regret kernel;
* No-Free-Evasion for demonstrated repair withdrawal.

The new round should generalize the ANSWERABILITY part beyond repair retirement.

---

# 15. Responsive Revision corollary

After the core Answerable Revision theorem is stable, investigate—but do not force—a
second theorem/corollary:

## Responsive Revision

Suppose:

* rho is outstanding;
* rho points to or supports a live repair r;
* r remains represented, executable, licensed, applicable and auditable;
* the relevant opportunity stream receives sufficient service;
* a consumer proves a witness inequality;
* the process runs the repair-regret algorithm.

Then persistent non-uptake is quantitatively controlled.

Schematically:

```text
Outstanding(rho)
+ LiveRepair(rho,r)
+ Service
+ RepairStability
+ Witness
    =>
vanishing / bounded non-uptake on the relevant stream
```

This should import PR60's Theorem A/B.

Do NOT require this quantitative theorem in order for Answerable Revision itself to
survive.

---

# 16. The boundary after this theorem: Reflective Openness

Do not attempt to solve this round, but name it precisely.

Answerable Revision begins only after promotion:

```text
evidence -> rho
```

It therefore cannot prevent the process from strategically ensuring that criticism
never reaches promotion.

The next frontier is something like:

## Reflective Openness

> A cognitively significant component cannot permanently immunize itself from relevant
> criticism merely by controlling whether that criticism is represented, serviced,
> evaluated or promoted.

This may require:

* inquiry;
* service;
* exploration;
* anti-manipulation;
* liability;
* counterfactual reasoning.

Do not smuggle Reflective Openness assumptions into Answerable Revision.

The before/after-promotion boundary should be one of the round's main outputs.

---

# 17. Human / H+ export property

Try to state an implementation-independent property with no RI internals.

Candidate flavor:

> A process is answerably revising when reasons legitimately generated under its
> operative standards remain matters it must incorporate or explicitly answer, even as
> those operative standards themselves change.

This should make conceptual sense for:

* an engineered RI-like reasoner;
* an institution;
* a human deliberative process;

without claiming humans literally satisfy RI.

Do not yet connect this directly to the deference theorem.

Just see whether the abstraction is usable independently of the realization.

---

# 18. Deliverables for the new PR

Create a new round directory and PR with:

## A. Verdict

Choose a precise verdict, e.g.

* `ANSWERABLE-REVISION-SURVIVES`
* `WARRANT-REVISION-LAUNDERS-REASONS`
* `PROMOTION-INTERFACE-BLOCKED`
* `STRICT-PRESTATE-BLOCKED`
* `REFLECTIVE-INSTANCE-REQUIRES-META-WARRANT`

## B. Main theorem

Exact strongest defensible Answerable Revision theorem.

## C. Promotion interface

Minimal semantics for:

* warrant standing;
* evidence admissibility;
* reason promotion;
* historical incurrence.

## D. Revisable warrant model

Show `W_t -> W_{t+1}` without retroactive erasure.

## E. Countermodel table

AR1–AR10.

For every hypothesis, name the countermodel requiring it.

## F. PR60 specialization

Show whether PR60 is naturally recovered.

## G. Responsive Revision corollary

Only if it composes honestly with PR60.

## H. Boundaries

Especially:

* pre-promotion self-sealing;
* evaluator manipulation;
* substantive correctness of defeat;
* long-horizon policy effects.

## I. Export property

Implementation-independent process-level statement.

## J. Freeze / do-not-freeze

Only freeze invariants that survive the round.

---

# 19. Scope restrictions

Do NOT:

* modify frozen LE to make this easy;
* reopen PR60 after it is merged;
* build policy regret;
* solve evaluator independence;
* solve Reflective Openness;
* solve the evidence-baseline normative question universally;
* build the traderized construction;
* prove the LI specialization;
* claim corrigibility or deference.

The new round is successful if it answers one question cleanly:

> **Can substantive standards for what counts as a revision reason themselves change,
> while reasons legitimately incurred under earlier standards remain diachronically
> answerable?**

That is the theorem target.

The guiding slogan is:

> **Standards may change; reasons incurred under them remain answerable.**

And the quantitative follow-up, if it survives, is:

> **When an outstanding reason continues to support a live improvement, low repair regret
> prevents the process from indefinitely leaving that improvement unused.**

```

I like this as the next round because it lets PR60 remain exactly what it discovered rather than asking it to solve the baseline problem. The new abstraction begins **after promotion to a reason**, which is precisely where we currently have enough structure to say something strong while still allowing \(W\) itself to evolve. 
```
