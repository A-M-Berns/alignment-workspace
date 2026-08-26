# Answerability, and the Legitimate Evolution package

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

Grounded Replay is frozen and unchanged. `src/replay.py` does not import
`src/answer.py` and has no obligation notion — checked in
`tests/test_answer.py::TestTheKernelIsUntouched`.

**Three things in the previous version of this document were wrong.** The
continuity conclusion was false on every process that resolves an obligation
after transferring it; the second premise was doing no work; and the coupling
could not represent an unauthorized act that generates a complaint. §§1, 3 and 6
below are the repairs, and `COUNTERMODELS.md` §§12-14 are the refutations.

## MINIMAL LEGITIMATE-EVOLUTION STATEMENT

**State carried.** A trace of edits, replayed by two folds. Standing occurrences
`o`, and obligation occurrences `q`. Identity of each is its trace position paired
with a slot index, so unique birth is definitional.

**Local semantic inputs, three.**

```text
Permit   may this edit be made, given the strict pre-state and its declared input
Due      which represented reasons the semantics says are owed an answer
Resolve  done, or carry(successors)
```

`Auth` remains the base predicate the kernel is parameterised by rather than a
semantic input. `Disposes` and `Transfers` were two names for `Resolve`'s two
answers and are folded together.

**The two folds.**

```text
L_0     = G                                O_0     = Q
L_{t+1} = (L_t \ dispose_t) u issue_t      if Valid(L_t, e_t)
          L_t                              otherwise

O_{t+1} = (O_t \ (disch_t u moved_t)) u opens_t   if Valid(L_t, e_t)
        = O_t u opens_t                            otherwise
```

**Structural premises, three.**

```text
S1  grounds(e_t) subset { o in L_t : Auth(o) }        prior grounding
S2  apply_t(L_t,e_t) != L_t  ->  grounds(e_t) != {}   no ex nihilo
D1  owed_t subset O_{t+1}                             due realization
A1  q leaves O_t only via disch_t or moved_t, every   controlled resolution
    successor named is opened by that edit, and no
    transfer names an empty successor set
```

**The two theorems.**

> **Grounded Replay.** Under S1 and S2, every admitted occurrence has a finite
> grounding tree with leaves in `G` and strictly descending positions.

> **Answerability Continuity.** Under A1, every obligation outstanding at `s` has,
> at every later `t`, a finite resolution derivation whose frontier is non-empty
> and consists only of obligations still outstanding at `t` and obligations an
> accepted edit discharged before `t`.

**The role of Due.** D1 is what makes the package say more than "obligations
someone handed us are not lost". With it:

> **Corollary.** Every obligation the semantics ever made due has a resolution
> derivation from the position at which it became due.

**A2 does not survive.** See §3. It was representation hygiene, retained as
`fresh_by_construction` and named nowhere in a theorem.

**The witness object.** A finite tree, unfolded from a DAG. Nodes are `carried`;
leaves are `open` or `discharged`. Depth is bounded by `t - s` because every child
begins at a strictly later position.

**The coupling, asymmetric.**

```text
OPEN       ungated by entitlement    a process is answerable for what happened
DISCHARGE  gated by Valid            removing an obligation exercises authority
TRANSFER   gated by Valid
```

> **Corollary.** An act the process was not entitled to perform discharges
> nothing.

> **Corollary.** An obligation may open at an edit the process refused.

**Structural versus semantic.** S1, S2, D1, A1 and both folds are structural.
`Permit`, `Due` and `Resolve` are opaque and the kernel reads none of what an
occurrence says.

**Deferred.** Coverage (whether a reason is ever represented); progress (whether
an open obligation is ever closed); regret; substantive correctness; and any
quantitative burden law — §7.

**RI realization gap.** `roots()` mints `AnsRoot`s from `NormEvent`s only, so
`Due` has no realizer. §8, checked against the code.

### Whiteboard

```text
Two folds over one trace, sharing an acceptance predicate asymmetrically.
Standing: nothing enters without licensed ancestry           (S1, S2)
Obligation: what the process's own semantics calls due enters (D1)
            and leaves only by discharge or named succession  (A1)
Every obligation has a finite resolution tree whose leaves are
open-or-discharged. Unentitled acts discharge nothing and may still open.
```

## 1. The conclusion was false

Build a process that refers a complaint and then answers the referral.

```text
O_0 = {q0};   t=0: transfer q0 -> q1;   t=1: discharge q1
```

A1 holds, freshness holds, entitlement is impeccable. The shipped conclusion asked
whether `q0` was discharged in `[0,2)` — it was not, `q1` was — or carried to
something outstanding at `2` — it was not, `q1` is closed. Both disjuncts fail and
the theorem reported a violation on a process with nothing wrong with it.

It is not one case. `split -> discharge both`, `merge -> discharge successor` and
any chain ending in a discharge fail identically. `split -> discharge one branch`
passed only by accident, because the surviving branch supplied the missing
disjunct.

The defect is that the old statement tracked *the root* and asked about its own
fate, when succession replaces an obligation with others whose fate is the answer.
The corrected conclusion asks for a **derivation** and classifies its **frontier**.

Every one of the five is now clean, and the derivations are exhibited:

```text
merge -> discharge          q:a [carried] -> q:joint [discharged]
                            q:b [carried] -> q:joint [discharged]

reconverging split          q:complaint [carried]
                              q:left  [carried] -> q:rejoined [open]
                              q:right [carried] -> q:rejoined [open]
```

## 2. The witness is a tree, unfolded from a DAG

Global succession is a DAG: a merge gives one obligation two parents, and a split
whose branches later rejoin gives one obligation two ancestral paths. The
derivation *of a single root* is nevertheless a finite tree, because it unfolds
that DAG — `q:rejoined` above is two distinct leaves, one per path.

The alternatives were considered and are worse. A chain cannot branch, so splits
break it. A reachability relation plus a leaf classification states the theorem but
exhibits no witness, and this round's standard is that a claim is checked. A DAG
witness would need sharing, which buys nothing: the statement quantifies over
leaves, and the unfolding's leaf multiset is what the conclusion is about.

Finiteness is not an extra hypothesis. Each child starts at a strictly later
position and positions are bounded by `t`, so depth is bounded by `t - s`; each
node has finitely many successors. The proof is still an induction on `t - s`.

The one subtlety the tests caught: a `carried` node with **no** children is not a
derivation. `transfer_to_nowhere` produced exactly that, and an empty frontier
satisfies "every leaf is open or discharged" vacuously. The conclusion therefore
asks for a non-empty frontier, and A1's transferred-to-nothing clause is what
supplies it.

## 3. A2 was not load-bearing

The previous pass argued that freshness makes transfer chains terminate. It does
not; the interval does. Build a `Duties` with

```text
q0 -> q1 at 0,   q1 -> q0 at 1,   discharge q0 at 2
```

Every opened obligation was already open, occurrences are mis-positioned, an
obligation is its own descendant. Freshness is violated in every way the check can
report. A1 holds, and the theorem holds, with the derivation

```text
qG.0 [carried@0] -> qG.1 [carried@1] -> qG.0 [discharged@2]
```

finite despite the cycle, because each step moves strictly right along a finite
trace.

Verdict on the taxonomy the dispatch asked for: **A2 is representation hygiene**,
and under occurrence identity it is additionally definitional — `office.duties`
cannot construct a violation, and the countermodel above had to be built by hand.
It is removed from the premise list and retained as `fresh_by_construction`, which
guards the *encoding*, not the theorem.

That the package now has an asymmetric premise count (two on entitlement, two on
answerability, but one of the four doing different work) is not a defect to be
tidied. §6 explains why the symmetry was never real.

## 4. Recognized as due, and never entered

The conceptual attack, and it lands.

```text
a reason is represented
the process's own semantics says it is owed an answer
no obligation is ever opened
no outstanding obligation is ever removed
entitlement is impeccable
```

The previous package passes this without complaint, because A1 only ever
constrained *departures* from the outstanding set, and a process that never enters
anything has no departures. That is not a legitimate process. It is not a coverage
failure — the reason is represented — and not a regret failure; the process has
recognized, by its own lights, that it owes an answer, and has simply declined to
put it on the books.

The minimal law is one line:

```text
D1   owed_t subset O_{t+1}
```

What that gets right, and what it cost to see:

- **It is local.** One inclusion at one position. The global corollary comes from
  composing it with the theorem.
- **It does not require coverage.** `Due` speaks only about what is already
  represented. `unobservant()` recognizes nothing, owes nothing, and stays
  legitimate. Coverage remains where round 3 left it.
- **It does not require progress.** D1 forces entry, never closure. An obligation
  entered under D1 may stay open forever.
- **It forbids entering-and-closing in one breath.** The fold unions openings
  **last**, so an obligation opened and discharged at one position is outstanding
  afterwards, and A1 reports the discharge as disposing of something not open.
  Immediate resolution is therefore not expressible, which is the right answer to
  the dispatch's question: a resolution one position later costs nothing and keeps
  the obligation exhibitable. §5 has the strict-pre-state consequence.
- **It is indexed by position, not attached to a reason.** `Due` reads the
  normative state, so a reason represented at `u` can become owed at `t > u`
  without any new reason arriving. `due_arrives_later` is the fixture.

Two questions from the dispatch that the model answers rather than assumes. `Due`
names obligation *labels*; the structure mints the occurrence. So one reason may
make several things due, and two reasons may make the same thing due without
minting it twice — and occurrence identity stays structural rather than becoming
something the semantics has to supply.

## 5. Strict pre-state, on the resolution side

Both analogues hold and neither needed a premise of its own.

`due_entered_then_closed_same_act` opens what it owes and purports to discharge it
at once: refused, because openings are unioned last.
`self_ratifying_resolution` transfers an obligation to a successor and discharges
the successor in the same act: refused, for the same reason. A resolution cannot
use an obligation it creates to certify that it has already dealt with the
predecessor.

## 6. One acceptance bit could not gate both channels

This is the correction the dispatch flagged, and it is a real defect in what
shipped.

`Alice` acts without entitlement. The act is refused: no normative standing
changes. The *fact that the attempt occurred* is represented, and by the process's
own semantics that fact is owed an answer. Under the shared gate, a rejected edit
was a no-op on the obligation fold, so no complaint could open. The architecture
could not represent a process that becomes answerable for what it refused to do.

The fix is to gate the two directions differently:

```text
OPEN                 ungated
DISCHARGE, TRANSFER  gated by Valid
```

The corollary the shared gate was introduced to secure is unaffected, because
discharge is still gated. What is gained is its converse. The decisive fixture is
`unauthorized_act_attempts_discharge`, one act exercising both channels:

```text
accepted            ()
O_end               {q:complaint-about-alice, q:standing}
opened by rejected  {q:complaint-about-alice}
would have been discharged {q:standing}
```

The opening lands and the discharge does not.

**Why this direction is safe.** Opening an obligation is a burden on the process,
not a power over it, so an adversary who can only open is working against itself.
The laundering route is closed: an unentitled act cannot name a successor and
carry a real obligation away, because transfer is a removal and removals are
gated. `rejected_edit_with_descriptive_consequences` confirms the behaviour does
not depend on *why* the edit was refused — a provenance refusal behaves like a
scope refusal.

**What this does to the duality.** It ends it. The previous pass's slogan was
entitlement-controls-creation against answerability-controls-destruction, already
qualified there as narrower than it looked. With D1 the correct statement is

```text
entitlement     controlled creation of standing
answerability   required creation and controlled resolution of obligations
```

which is not a duality at all. The pretty version is dropped.

## 7. The quantitative question, stated narrowly

The previous pass's finding stands and was overstated. The narrow version:

> Quantitative burden conservation is not a generic structural consequence of
> answerability continuity.

Four constitutions transfer every obligation to a named successor and shrink the
burden, one of them to zero, while satisfying every structural premise. What is
**not** established is that no legitimacy semantics may impose a quantitative law:
a `Resolve` that refuses a successor which does not genuinely carry its
predecessor is perfectly coherent, and the structural layer is blind to it only
because it is blind to all content.

Where a quantitative law belongs, given that: **inside semantic `Resolve`** if it
is about whether a successor really carries an obligation, and **downstream in
traderization** if it is about whether enforcement is financially serviceable.
Not generically, and not in this kernel.

### The helper is withdrawn and replaced

`thm_no_dilution_gives_monotone_potential` was underspecified in two ways. It
checked per-parent rather than total dilution. And it ignored that a fresh
obligation raises the potential however well transfers behave, papering over that
with a discharge escape clause that made it unfalsifiable on any trace containing
a discharge. `high_regret` is the witness: no dilution at all, and the potential
runs `0 -> 1 -> 2 -> 3`.

The replacement names both hypotheses:

> **Conditional.** If no accepted edit dilutes in total, and every opened
> obligation is a successor named by a transfer of the edit that opens it, then
> the potential is non-increasing.

The per-parent result is preserved as the reason total accounting is required:
`merge_lenient` sends two obligations of weight 1 to one of weight 1.5, passes
per-parent and fails in total.

## 8. RI realization: checked against the code

The previous pass recorded this as a reading. It is now read off
`rounds/2026-08-24-reflective-integrity-core/src/ri_core.py`.

**Does `ReasonOcc` ever mint an `AnsRoot`, directly or indirectly?** No.
`History.roots(t)` is `seed.roots0` extended by `mint(a)` for every `a` in
`norm_events(t)`, and `mint` is typed on `NormEvent`. `ReasonOcc` appears in
`Derivation.leaves` and as the payload of a `Reason` history step; neither is
consulted by `roots`.

**What triggers MINT?** A `NormEvent`, in two cases: a `Transfer` effect mints one
root for the successor episode, debtor the transferee; anything else mints one per
freshly introduced standing, debtor the author.

**Can a represented reason be Due without a `NormEvent` already deciding to
mint?** No. There is no path from a `Reason` step to a root.

**Is `Due` derivable, representable, or a parameter?** None of the three, and
there is a name collision worth flagging. RI has `History.due(q, t)`, but it means
*this live root is disposed of by some norm event* — a property of an existing
root's episode, not of a reason. The `Due` this package needs is not representable
at all.

**The smallest missing seam,** and it is not a new event kind: `Reason` already
exists as a history step. What is missing is a minting trigger keyed on reason
occurrences — `roots()` consulting represented reasons under a semantic predicate,
the way it consults norm events. That is one clause in one function.

Worth recording in the other direction: RI's own `continuity_ok` recurses over
successors with a leaf condition of *live and not due*, which is the corrected
frontier statement of §1. **The architecture already had the right shape, and the
abstraction shipped the wrong one.**

## 9. What the package is

A **named package of two closure theorems and two coupling laws**, which is
option D. Not one joint theorem: the folds have disjoint carriers, disjoint
premises and disjoint proofs. Not a semantic definition: every premise is
structural. Not simply A + corrected-continuity: D1 is a third structural premise
that neither closure theorem contains, and without it the package passes a process
that recognizes an obligation and ignores it.

The two coupling laws are the asymmetric gate's two halves, and they are laws
rather than corollaries of a shared parameter, because after §6 there is no single
shared parameter to derive them from.

Interface comparison, as asked:

```text
smallest formally sufficient      one joint LegitStep relation with a Due
                                  projection; everything else recoverable
smallest semantically useful      Permit + Due + Resolve
```

They differ and the second is what the theorem uses. `LegitStep` would collapse
the distinction Grounded Replay needs (authority) into the one answerability needs
(resolution) and the one Legitimate Learning will need (Due), and the consumers
would have to project it back out. Going the other way, splitting `Resolve` into
`Disposes` and `Transfers` names one function twice.

## 10. Consumers

**Deference.** The strengthened package does support the intended statement: a
successor process is not merely genealogically descended, but any represented
reason it itself recognizes as demanding treatment is in its answerability
dynamics and can leave only by a resolution path. That is D1 plus the corollary in
§4, and it is strictly more than the previous package could say. No current-state
certification work in this pass; that gap is unchanged.

**Traderization.** Still consumes `Norm(L_t)` and needs neither coverage nor
regret. The distinction the dispatch asked to keep: outstanding obligations do
**not** affect which norm edits are legitimate — the two folds do not read each
other in that direction — and do affect financial serviceability, which is where a
quantitative law belongs if one belongs anywhere. §7.

## 11. What no claim above asserts

- No claim that an outstanding obligation is ever discharged.
- No claim that any situation *ought* to have become represented.
- No claim that a process satisfying everything here is good. `high_regret`
  satisfies all of it.
- No claim that quantitative liability is unavailable to a legitimacy semantics.
  §7 states only that it is not a structural consequence.
- No claim that the RI seam in §8 is easy, only that it is one function and needs
  no new event kind.
