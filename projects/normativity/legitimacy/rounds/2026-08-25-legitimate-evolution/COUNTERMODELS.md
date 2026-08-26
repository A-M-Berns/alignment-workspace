# Prosecuting the premises

Status: **prosecution record; unregistered.** Every entry names the process that
decides it and the test that runs it.

The first four sections each refute something the round had already shipped and
tested.

---

## 1. The grounding theorem was false: nothing required a ground set

**`office.ex_nihilo`.** An edit with `grounds = {}` that issues a fresh
authority.

The previous formulation's prior-grounding hypothesis is
`Valid(L,e) -> grounds(e) ⊆ Auth(L)`, which holds **vacuously** here. Its
grounding theorem then claims a finite tree with leaves in `G` for the issued
occurrence, and there is none: the occurrence's only tree is itself, and it is
not in `G`.

So the hypotheses did not imply the conclusion. Not a proof gap — the conclusion
is false on a frame satisfying every stated hypothesis.

**The repair is `S2`**: an accepted edit that changes the state has a non-empty
ground set. Which form is right was a real choice.

```text
Valid(L,e) -> grounds(e) != {}                       too strong
Valid(L,e) and changes(L,e) -> grounds(e) != {}      right
```

A no-op needs no authority. Anything that puts something in force or takes
something out of force does. The two halves are consumed by different results —
grounding needs it of edits that **issue**, persistence needs it of edits that
**dispose** — and stating it over any state-changing edit is their union.

*Reading.* If something may enter or leave legitimate normative state with no
prior authority premise, it is a new root, and roots that are wanted belong in
`G`. `test_a_root_that_is_wanted_belongs_in_the_base` puts one there and the
theorem holds again.

**Both premises are prosecuted the same way and neither subsumes the other.**
An edit grounded in an occurrence nobody issued breaks S1 and satisfies S2; the
ex-nihilo edit breaks S2 and satisfies S1; the theorem fails on each.

## 2. Historical time was being used as identity

The previous `Occ` was `(at, index, sort)` with `at` the historical index, and
`Edit.at` a free field. Two edits at one time therefore issued **the same
occurrence**, the replay applied the first one twice, and freshness — claimed to
follow from the type — rested on an unstated premise that historical times are
unique per edit.

The repair deletes the field. The trace is a **list**; position is identity and
order at once; `Occ = (pos, slot)`. Two edits with identical *values* at
positions 0 and 1 issue `o0.0` and `o1.0`, and no premise is needed.

**What the theorems consume is unique birth, not unique issuance of a content.**
`office.readoption` issues one content twice and the occurrences are distinct,
which is exactly what makes Corollary 2 true without poisoning the content.

A realization that manufactures its own occurrences is still caught, by
`fresh_by_construction`, which is a check rather than a hypothesis.

## 3. Soundness at the checker's own state is worth nothing

**`office.missed_revocation`.** A charter validly strips a deputy's warrant; the
deputy then acts.

```text
semantic replay    strips the warrant, refuses the later act
                   live = { w:charter }

checker that declines the revocation
                   keeps the warrant, accepts the later act
                   live = { w:charter, w:deputy, n:by-deputy }
```

The previous pass's `verifier_sound` evaluates `Valid` at the **checker's own**
state and reports this clean. It is: relative to a state containing `w:deputy`,
the stale act really is valid. But that state never legitimately existed, and the
checker's replay now contains an authority and a norm the semantics never
admitted.

So the previous pass's claim — *soundness suffices for recognition, completeness
is additionally needed for enforcement* — is **withdrawn**. A sound
under-approximation does not under-approximate the state: a missed disposal makes
it strictly larger, and both projections gain spurious members.

**The exact condition** is agreement along the trace:

```text
for every t:   Check(L_t, e_t)  <->  Valid(L_t, e_t)
```

evaluated at the states the **semantic** replay reaches. It gives `Lhat = L` by
induction, hence both projections. It is weaker than global extensional equality
— `test_a_checker_that_errs_off_the_trace_is_still_exact` builds a checker wrong
at every state the trace never visits, and it still simulates — and strictly
stronger than either one-sided condition.

**A weaker projection-specific condition is available and is not free.**
Agreement on the edits that touch a projection suffices for that projection only
if `Permit` factors through it, since validity may read the whole state. The
round states that and does not claim it.

## 4. A grounding tree does not certify currentness

**`office.lineage_versus_current`.** A charter appoints, the appointee acts, the
charter revokes the appointment.

```text
w:a    admitted, has a tree, and is not live
n:b    admitted, has a tree, and is live
```

The tree for `w:a` names positions 0 — nothing about position 2, the revocation.
A tree is built from grounds, and disposals are not grounds, so a tree
**structurally cannot** witness that nothing later removed the occurrence.

The previous `certificate` conflated the two by requiring `o ∈ replay(...)`
before building a tree, so it silently answered a currentness question with a
lineage object. `tree` now ranges over `admitted`, and the theorem says so.

Three predicates, and the relations are checked:

```text
Live_t  subset  Admitted            strict — w:a witnesses it
Grounded  =  Admitted               on a fixed trace
```

## 5. Content invariance was vacuous and is false

The previous `thm_content_unconstrained` built a relabelled dictionary and then
replayed the **unchanged** process, so it could not fail. And the claim is false
once permission reads content: `office.content_sensitive_jurisdiction` has a live
policy banning a scope, and an edit in that scope is refused.

Withdrawn, and replaced by a statement with no theorem attached:

> **No content-conservativity assumption.** Grounded Replay places no equality,
> distance, monotonicity or preservation requirement on the contents of
> predecessor and successor occurrences. Arbitrarily large substantive revision
> is permitted whenever the semantic relation permits that edit.

That follows because the kernel never inspects content — checked by reading
`apply_edit` and `replay` — and it is not a separate theorem.

## 6. Descriptive provenance and normative permission

Four processes, one shape: the descriptive view records what happened and
`Permit` decides what it means.

```text
persuasion            Bob's argument is in the view      permitted
forged_input          the signature is forged            refused
coerced_exercise      duress is in the view              the constitution decides
incomplete_provenance the view is inadequate             refused
```

`coerced_exercise(False)` is the same gazette with a constitution that declares
coercion does not invalidate, and the edit is accepted. The interface fixes
neither answer; what it requires is that whatever the rules treat as relevant to
authentic exercise crosses the interface.

Jurisdiction is `Permit`, not provenance: `office.unauthorized_scope`'s
out-of-scope act has complete provenance and clean grounds and is refused by the
permit clause alone.

## 7. Extraction, and the two ways it fails

```text
office.hidden_reading_pair     same trace, different Valid    -> different replay
cases.partial_effect_pair      same declared data, different effect -> different trace
```

The second is the sharper. Two records of equal length, equal `tau`s, the same
authority, the same witness, the same cited reason and settlement, differing only
in an **uncited** settlement the schema reads. `declared_data` is equal;
`extraction_agrees` reports *effect differs on equal declarations*.

This is where the old pre-state condition ended up. It is not a legitimacy
premise: the kernel's fold is deterministic by construction, and what can fail is
that a raw process determines the trace and the semantics through what it
declares.

## 10. A premise that cannot fail is not a premise

The first version of the obligation model routed an act's undeclared removals
through its discharges. A1 then had nothing to detect: every departure from the
outstanding set was, by construction, a declared discharge, and
`entitled_with_laundered_obligation` — a constitution whose entire purpose is to
lose an obligation while satisfying every entitlement premise — passed.

The repair is a fourth channel, `drops`, and an A1 clause that reports anything
leaving by it. The general lesson is the one this document keeps recording in
different forms: a premise stated over a type that cannot violate it is a
tautology wearing a premise's clothes, and the way to find out is to try to build
the violating instance rather than to inspect the statement.

## 11. Dilution is invisible to the kernel, and that is not repairable here

Four constitutions transfer every obligation to a named successor, satisfy A1 and
A2, satisfy Answerability Continuity and no-silent-loss, and reduce the total
burden — in `diluted_to_nothing`, to zero. The process can exhibit a successor
chain for every issue it has ever had and owe nothing.

This is the same fact as §5 and as round 5's `blind_permit`, in a third costume.
The kernel does not read what an occurrence *says*, so it cannot distinguish a
successor that carries an obligation from one that nominally replaces it. Any rule
that could would also forbid the legitimate revision in which a process discovers
an issue was smaller than it thought.

What survives is a conditional on `Transfers`, and prosecuting *that* produced a
second finding: per-parent accounting is not a weaker version of total accounting.
`merge_lenient()` sends two obligations of weight 1 to one of weight 1.5. Each
parent's successor outweighs it, so per-parent sees nothing; the total fell from 2
to 1.5. A conservation claim stated per-parent would be false and would look
proved.

## 12. The answerability conclusion was false

Refer a complaint, then answer the referral.

```text
O_0 = {q0};   t=0: transfer q0 -> q1;   t=1: discharge q1
```

Premises clean, entitlement clean. The shipped conclusion asked whether `q0` was
discharged in `[0,2)` -- no, `q1` was -- or carried to something outstanding at
`2` -- no, `q1` is closed. Both disjuncts fail on a process with nothing wrong
with it. `split -> discharge both` and `merge -> discharge successor` fail
identically; `split -> discharge one branch` passed only because the surviving
branch supplied the missing disjunct by accident.

The statement tracked the root's own fate where succession replaces the root with
others whose fate is the answer. The repair asks for a derivation and classifies
its frontier. This is the fourth time an object in this round was refuted by a
countermodel rather than under-proved, and the first time the defect survived a
whole pass and shipped.

A smaller sibling found while repairing it: a transfer naming **no** successor
produced a `carried` node with no children, and an empty frontier satisfies "every
leaf is open or discharged" vacuously. The conclusion now requires a non-empty
frontier.

## 13. A premise that was doing nothing

The previous pass claimed A2 (fresh openings) made transfer chains terminate.
Build the cycle

```text
q0 -> q1 at 0,   q1 -> q0 at 1,   discharge q0 at 2
```

by hand. Freshness is violated in every way the check reports -- mis-positioned
occurrences, an obligation reopened, an obligation its own descendant -- A1 holds,
and the corrected theorem holds with the finite derivation
`qG.0 -> qG.1 -> qG.0 [discharged]`. Termination comes from each step moving
strictly right along a finite trace.

A2 is demoted to representation hygiene. Under occurrence identity it is also
definitional: the constitution model cannot construct a violation, which is why
the countermodel had to be hand-built -- and why the premise looked safe.

## 14. One acceptance bit could not gate both channels

An unauthorized act is refused, so no normative standing changes. The fact that
the attempt occurred is represented and, by the process's own semantics, owed an
answer. Under the shared gate a rejected edit was a no-op on the obligation fold,
so no complaint could open: the architecture could not represent a process
becoming answerable for what it refused to do.

The repair gates the directions differently -- openings ungated, removals gated.
The corollary the shared gate secured is untouched, because discharge is still
gated, and `unauthorized_act_attempts_discharge` exercises both channels in one
act with only the opening landing. The direction is safe because opening is a
burden rather than a power, and laundering stays closed because transfer is a
removal.

This one is a design error rather than a mistake in a statement, and it was
visible in the previous pass's own framing: the corollary was described there as
the entire yield of packaging the two halves together, which is what a coupling
too coarse to say anything else looks like.

## 15. Recognized as due, and never entered

A process with impeccable entitlement, no removals at all, and a represented
reason its own semantics says is owed an answer, which it never enters. The
previous package passes it, because its only obligation premise constrained
departures and there were none.

Not a coverage failure -- the reason is represented. Not regret. The repair is
`D1`, one inclusion at one position, and it is the clause that makes the package
say something about evolution rather than about bookkeeping.

## 16. What remains open

**Provenance completeness.** The round tried to state it non-circularly and
failed. It is not "assume the relevant influences are visible", not "refuse every
influence", and not derivable from a record whose own episodes cover by
construction. It is carried as an explicit epistemic assumption on the
extraction, and `office.incomplete_provenance` is where it is false.

**`Permit` is opaque.** The interface requires it be consulted and constrains
nothing about it, so a constitution with a permissive `Permit` satisfies every
theorem here.

**Reflective Integrity has no jurisdiction on an authority**, so the permit clause
is nearly vacuous on a record. That is a gap the abstraction exposed and this pass
deliberately did not repair.

**`Due` has no realizer**, and this is now checked rather than read off an
intended correspondence. `History.roots(t)` is the seed roots extended by
`mint(a)` over `norm_events(t)`, and `mint` is typed on `NormEvent`; `ReasonOcc`
appears only in derivation leaves and as a `Reason` step's payload, and nothing
consults it. RI's `History.due(q, t)` is a different predicate -- it asks whether
a live root's episode is being succeeded. Since D1 is now a premise, this is a
premise the architecture cannot discharge. The smallest seam is a minting trigger
keyed on reason occurrences; `Reason` already exists, so no new event kind is
needed.

Worth recording in the other direction: RI's `continuity_ok` already recurses over
successors with a leaf condition of live-and-not-due, which is the corrected
frontier statement. The architecture had the right shape and the abstraction
shipped the wrong one.

## 17. What no entry above claims

That the theorem is deep. It is an induction over a list; two of its three
corollaries are two lines. What it earns is that three successive formulations of
this object failed it — one lost norms to unauthorized revocation, one admitted
ungrounded creation, and one answered a currentness question with a lineage — and
that its obligation-side counterpart failed a fourth way, by being stated over a
type that could not violate it.

That the semantic layer is settled. `Permit` and `ProvComplete` are parameters,
and every substantive normative question lives in them.
