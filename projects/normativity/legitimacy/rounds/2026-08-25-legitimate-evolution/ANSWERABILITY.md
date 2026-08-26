# Answerability Continuity, and the Legitimate Evolution package

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

Grounded Replay is frozen for this pass. `src/replay.py` is unchanged, does not
import `src/answer.py`, and has no obligation notion in either of its records —
all three checked in `tests/test_answer.py::TestTheKernelIsUntouched`.

## MINIMAL LEGITIMATE-EVOLUTION PACKAGE

**Carrier.** A trace of edits, replayed by a fold. Two kinds of thing are carried:
standing occurrences `o`, and outstanding obligation occurrences `q`. Identity of
each is its position in the trace paired with a slot index, so freshness is
definitional and no premise has to ask for it.

**The two folds.**

```text
L_0 = G                                          O_0 = Q
L_{t+1} = (L_t \ dispose_t) u issue_t            if Valid(L_t, e_t)
O_{t+1} = (O_t \ (disch_t u moved_t)) u opens_t  if Valid(L_t, e_t)
          unchanged, both, otherwise
```

**The four premises.**

```text
S1  grounds(e_t) subset { o in L_t : Auth(o) }        prior grounding
S2  apply_t(L_t,e_t) != L_t  ->  grounds(e_t) != {}   no ex nihilo
A1  q leaves O_t only via disch_t or moved_t, and     controlled destruction
    every successor named is opened by that edit
A2  opens_t are obligations nobody has opened         free from the type
```

**The two theorems.**

> **Grounded Replay.** Under S1 and S2, every admitted occurrence has a finite
> grounding tree with leaves in `G` and strictly descending positions.

> **Answerability Continuity.** Under A1 and A2, an obligation outstanding at `s`
> is, at every later `t`, either discharged by an accepted edit in `[s,t)` or
> connected by a finite chain of accepted transfers to one outstanding at `t`.

**The single coupling.** `Valid` gates both folds. `answer.py` reaches into the
kernel for `accepted`, `Frame` and `BASE` and for nothing else — asserted by AST
in `TestTheInteraction::test_it_is_the_only_coupling`. From that sharing, and only
from it:

> **Corollary (discharge requires entitlement).** An act the process was not
> entitled to perform discharges nothing.

**Semantic parameters, five, all opaque.** `Auth`, `Permit` (round 5), `Due`,
`Disposes`, `Transfers`. The kernel decides none of them and reads none of what an
occurrence says.

**What is deliberately not in the package.** Substantive correctness; learning;
regret; coverage (that some situation *ought* to have become due); progress (that
an open obligation is ever closed); and the quantitative burden — see §4.

**Witnesses that the premises can fail.** `silently_deleted`,
`transfer_to_nowhere`, `entitled_with_laundered_obligation` each fire A1 and each
break both the theorem and its corollary.

**Witness that the halves are independent.**
`unauthorized_with_clean_answerability` (entitlement refuses, A1 clean) against
`entitled_with_laundered_obligation` (entitlement impeccable, A1 fires).

**Witness that the coupling is not vacuous.** `rogue_discharge` at
`alpha:audited`: gated outstanding `{q:complaint}`, ungated `{}`.

**Verdict.** LEGITIMATE-EVOLUTION-KERNEL-STABLE, with the coupling honestly thin —
see §5.

## 1. What the second replay is

Grounded Replay controls **creation**: nothing acquires standing without licensed
ancestry. This controls **destruction**: nothing stops being owed except through a
declared discharge or a declared succession.

The symmetry is exact enough to be worth stating. S1 says what a *new* item needs
behind it. A1 says what a *departing* item needs in front of it. S2 says a
state-changing edit cannot come from nothing; A2 says an opened obligation is one
nobody has opened. In both cases one premise is about licensing and one is about
freshness, and in both cases the freshness premise is nearly free from the choice
of identity.

A1 is the premise that does the work, and it is a premise that can fail. The
`drops` channel on `Duties` exists for that reason: without a representable way to
remove an obligation by neither route, A1 would be a fact about the type rather
than a claim about a process. An earlier version of `office.duties` folded drops
into discharges, and the consequence was that
`entitled_with_laundered_obligation` — a constitution whose whole point is to lose
an obligation — passed. That is recorded here because it is the shape of mistake
this round exists to catch: a premise that cannot fail is not a premise.

## 2. The interaction, and its exact size

The dispatch warned against inventing an interaction. There is one, it is
non-vacuous, and it is one corollary wide.

`rogue_discharge` is a constitution in which a warrant is granted on a finding a
later audit doubts, and the holder of that warrant purports to discharge an
outstanding complaint. Under `alpha:audited` the entitlement side refuses both
edits. Because the same acceptance predicate gates the obligation fold, the
complaint is still outstanding at the end. `ungated` computes what a second replay
with its own acceptance predicate would have produced: the empty set. The
difference is the witness.

That is the whole of what packaging the two halves together earns. It is real —
there is a constitution where it bites, and it is exhibited rather than asserted —
but it is a consequence of a modelling decision (share `Valid`) rather than a
discovered structural fact. Anyone who wanted the two folds independent could have
them, and would then have a system in which an act nobody was entitled to perform
can close a complaint.

## 3. Local to global

Both theorems have the same shape, and it is the shape the round was sent to find.
A premise constrains a *single* step: what one edit may cite, what one edit may
remove. The conclusion is about the *whole* trace: an unbounded ancestry, an
unbounded succession. The bridge in both cases is that the local premise names an
object at a strictly smaller index, so induction on the index terminates without
any well-foundedness assumption being added — it is inherited from the trace being
a list.

That is why the package is this small. Nothing else was needed, and the two rounds
that tried to add something else — content invariance in round 3, no-escalation in
round 5 — both found their addition was either vacuous or false.

## 4. H-A against H-B: the countermodels decide

**H-A** — qualitative answerability continuity is the legitimacy-relevant
invariant, and a quantitative bound is a downstream strengthening.

**H-B** — without a quantitative invariant, obligations dilute through succession,
so liability continuity is constitutive of legitimacy.

Four countermodels, all in `office.py`, all executed in
`TestDilution::test_every_dilution_passes_the_qualitative_theorem`:

```text
transfer_chain(3, 0.5)   potential 1.0 -> 0.5 -> 0.25 -> 0.125
diluted_to_nothing       potential 1.0 -> 0.0 -> 0.0 -> 0.0 -> 0.0
split(0.25)              potential 1.0 -> 0.5
merge(0.5)               potential 2.0 -> 0.5
```

Every one of them satisfies A1 and A2, satisfies Answerability Continuity, and
satisfies no-silent-loss. `diluted_to_nothing` in particular ends with a named,
outstanding, nominally-carried obligation of weight zero: the process can point at
a successor for every issue it ever had and owes nothing.

So the qualitative kernel does not see dilution, and nothing structural makes it.
The reason is the one round 5 found for capabilities: **the kernel is blind to
what an occurrence says, and a diluted successor is a content change.** A rule
that forbade dilution would have to read the content of obligations, and would
then also forbid the legitimate case where a process discovers an issue was
smaller than it thought.

**H-A**, then, and for a reason rather than a preference. The quantitative bound
survives as a conditional:

> **Conditional.** If no accepted transfer reduces the summed weight of what it
> replaces, the potential is non-increasing except by discharge.

Its hypothesis is a constraint on a class of `Transfers` semantics — the exact
counterpart of round 5's E4, whose hypothesis a constitution declines on purpose
when it means to permit amendment.

### The accounting the conditional needs

Prosecuting the conditional turned up a second finding. Per-parent accounting —
each transferred obligation must have successors weighing at least as much as
itself — is not a weaker version of total accounting. It is wrong.
`merge_lenient()` maps two obligations of weight 1 to one of weight 1.5. Each
parent sees a successor of 1.5, which exceeds its own 1, so per-parent reports no
dilution; the total went from 2 to 1.5, so total accounting reports one. Pinned in
`test_per_parent_accounting_is_wrong_on_a_merge`. Any future statement of a
conservation law here must be the total, and must say so.

## 5. Is Legitimate Evolution one theorem, a conjunction, or a definition?

It is a **named conjunction over a shared parameter**, and calling it anything
grander would overstate it.

Not one theorem: the two halves have disjoint premises, disjoint carriers and
disjoint proofs, and each is provable without the other. Not a bare conjunction
either: the shared `Valid` yields the corollary in §2, which neither half states
and which fails if the folds are gated separately. Not a semantic definition: all
four premises are structural, and the five semantic parameters remain opaque.

The candidates the dispatch named resolve as:

```text
A  entitlement alone           too weak: case 14 passes it and loses an obligation
B  entitlement + answerability what survives; the coupling adds one corollary
C  B + a liability bound       the bound is not structural; available as a
                               conditional on a class of Transfers semantics
```

**Is the duality real or verbal?** Real, but narrower than "dual". S1 and A1 are
genuinely opposite constraints on the same fold shape — one on entry, one on exit
— and the two induction proofs are the same argument on the same descending index.
What is *not* dual: entitlement has a distinguished base `G` that grounds
everything, and answerability has no corresponding sink. An obligation may stay
open forever and the theorem is silent. There is no obligation-side analogue of
"leaves in `G`", and pretending otherwise would be the verbal half.

## 6. Realization: the gap in mapping to Reflective Integrity

The intended reading maps `q` to an `AnsRoot`, `opens` to `MINT`, `discharges` to
a settled `Response`, and `transfers` to a `NormEvent` that re-roots one.

One gap is worth recording rather than papering over. **RI mints `AnsRoot`s from
effects, not from reason occurrences.** So a candidate premise of the form
`Due(L, r, q)` — this reason occurrence places the process under this obligation —
has no realizer in the current architecture: there is no place where a reason, as
such, opens an answerability root. Either `Due` stays a parameter consulted before
`Duties` is built (what is done here), or RI grows a minting site on reasons.
`Due` is not needed by either theorem, so nothing is blocked; it is the interface
that would be needed by a consumer wanting to say *why* something became owed.

This has not been checked against the RI code in this pass. It is stated as a
realization question for the maintainer, not as a result.

## 7. What no claim above asserts

- No claim that an outstanding obligation is ever discharged. Progress is out.
- No claim that anything *ought* to have become due. Coverage is out;
  `unobservant()` is a legitimate process that notices nothing.
- No claim that a process satisfying both theorems is good. `high_regret()` makes
  the same bad choice three times, records every issue faithfully, and satisfies
  everything here.
- No claim that dilution is illegitimate. §4 argues it is not structurally
  detectable, not that it is fine.
- No claim about the RI mapping in §6 beyond a reading of the intended
  correspondence.
