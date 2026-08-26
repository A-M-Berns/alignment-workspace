# Prosecuting the hypotheses

Status: **prosecution record; unregistered.** Every entry names the record or
register that decides it and the test that runs it.

Each axiom of the spine is answered in the same shape: what fails without it,
and where the failure is a real record rather than a stipulation.

---

## 1. L0 — base stability

**Drop it and everything collapses into the base.** With `G` a set the challenge
may void, T3a fails at its base case: `G |-_q y` no longer gives `q |= y`, and
T3 loses its induction. A challenge that voids the charter voids every warrant
under it, and the derivable set is not the recognized base but whatever survives.

**It is not removable, and this round does not remove it.** Legitimacy is
definable only relative to a base recognition relation. The gain from the frame
is that L0 is a named axiom in a list rather than a fact hidden inside a
definition of `Legitimate`.

In the Reflective Integrity realization L0 is a theorem, not an assumption: an
excision voids an episode's settlements, the seed is not a settlement, and no
replay can reach it. That is a fact about the realization and it does not make
the abstract axiom dispensable, because a realization whose base *is* reachable
by a challenge is easy to write.

## 2. L3 — issuance stability, and the record that refutes it

**The Carroll round's `C28`, read as a statement about the interface.** A
practical schema that reads the strict pre-state mints the same identifier with a
different payload. The event survives the excision — `G4` finds an active `PAuth`
in the excised replay — and what it puts in force is not what it put in force in
the original. So `q |= t` and `not (q |= y)`, and L3 fails on a legal record.

```text
prestate_reading = True    prestate_blind(case) is False   L3 has a violation
prestate_reading = False   prestate_blind(case) is True    L3 is clean
```

`test_frame.TestWhereTheRealizationIsConditional` runs both arms.

**What breaks downstream.** T3a's induction step is exactly L3. Without it a
derivation can certify an exercise whose issue is not stable, and T3's conclusion
— that no ancestor was manufactured — no longer follows from the step-local
checks.

**The condition is a hypothesis on the realization, not a repair to the
interface.** `warrant.py` satisfies L3 for free, because stability there is
reachability in a monotone dependency graph and an act's grant does not depend on
what else the register contains. So L3 separates two realizations and is not an
artefact of either.

## 3. L3' — origin necessity

**Drop it and manufactured authority is recognized.** L3' is the half that does
the anti-laundering work: without it an authority may survive a challenge while
the act that granted it does not, and T3's chain from `q |= z` to
`mint(z) notin Chal(q)` has no first step.

**A system violating it is easy to describe** and is the reason the axiom is not
decoration: any representation in which an authority is a free-standing fact
about the present, with its origin recorded separately and defeasibly, admits a
challenge that voids the appointment and leaves the office. An institution that
treats a warrant as valid on its face satisfies L0-L3 and violates L3'.

**In our realization it holds from the identifier scheme alone**, with no
pre-state hypothesis: a non-seed standing is `@s{tau}.{i}`, excision preserves
`tau`, and only the event at that `tau` can mint that id. `test_frame` checks it
in the pre-state-reading arm, where L3 fails and L3' does not — which is the
evidence that the two are different hypotheses rather than one stated twice.

## 4. L5, L6 and the countermodel that kept answerability out of the spine

**`delegated_custody(answered=False)`.** An authority is created, transferred to
another principal under a licensed schema, and the episode the transfer ended is
never answered.

```text
spine violations            {}
derivable everywhere        auth.delegable is in it
continuity at the base      False
outstanding below the base  the disposed episode, forever
```

Every authority-side clause holds. The authority is *literally the same object* —
`applyEffect` is the identity on a `Transfer`, so the identifier, the payload and
the predecessors are unchanged — and the only thing that moved is who is
answerable.

**So answerability is not constitutive of the authority**, and adding it as a
conjunct of `|-` would make the relation refuse a case in which nothing about the
authority is wrong. It is out of the spine for that reason and not for economy.

**What it is constitutive of.** Two constructors and one fact:

- *delegation*: `src(t) = tgt(t)`, so `issued(t) = {}` and the authority graph
  has a self-loop carrying no lineage. Without the account layer a delegation and
  a no-op are the same exercise.
- *disposal*: `tgt(t) = {}`, so the authority graph has no edge at all. Without
  the account layer a revocation and a thing that never happened are the same.
  `split_with_due_branch`'s `a:revoke` is the witness and `test_frame` reads
  `f.tgt["a:revoke"] == frozenset()` off it.
- *T6*: the only clause of the interface that can fail with the authority side
  clean.

**Should recognition transport across an unanswered transfer?** This round's
answer is yes for the authority and no for deference, because they answer
different questions, and the distinction belongs at the interface boundary
(`CROSS_PROCESS_INTERFACE.md` §5) rather than inside `|-`. That is a position and
not a result; a reader who wants `Recognizes` to mean "recognizes an answerable
process" should add L5-L6 to what `A` requires, and the interface is arranged so
that this is a change to `A`'s side and not to the succession relation.

## 5. All of `src(t)`, not one of it

**`warrant.merge_register`.** One act revokes two warrants — one manufactured on
the challenged finding, one earned on a clean one — relies only on clean
findings, and issues a successor. The act itself survives the challenge.

```text
all-of-src   w:merged is not derivable
one-of-src   w:merged is derivable
```

`test_frame.test_all_of_src_and_not_one_of_it` runs both, the second inline so
the two rules can be compared on one register.

**And the choice is invisible in the other realization.** Reflective Integrity's
`G6` refuses a supersession whose target is absent, so a merge whose targets do
not all survive is not admitted at all and the two rules agree everywhere. The
design decision is therefore forced by a system that is not ours, which is the
clearest single case for having written a second realization.

## 6. Where a suspension is not an edge

`SetStatus` writes neither `pred` nor a fresh identifier, so a suspension and a
reactivation make no authority edge and no account movement. That is correct —
the authority is the same object throughout — and it has a consequence the
Carroll round already found from the other side: excising *more* can restore a
suspended authority and with it a later event's admissibility, which is why the
challenge operator is not monotone.

The frame does not repair that and does not need to: `derivable_everywhere`
intersects per-challenge verdicts and never excises a union.
`test_frame.test_no_verdict_is_assembled_across_two_challenges` checks it by
reading the function rather than by assertion.

## 7. The strongest counterexample to the whole thing

**Provenance incompleteness, unchanged from the Carroll round.** `Q` is the set
of challenges the record's own episodes generate, and an episode's ancestry class
is only as wide as the settlement-reference links the record carries. Two
episodes with no reference reaching each other are, as far as the record can
tell, causally unrelated, so an authority installed in the first is stable
against a challenge naming the second and is derivable.

Nothing in this round addresses it, and abstraction makes it *more* visible
rather than less: it is now plainly a condition on the realization's `Chal` and
`|=`, namely that the challenge set is wide enough to contain what the influence
actually produced. An external process could satisfy L0-L4 with a `Chal` that
names almost nothing, and the interface would certify its authority.

**So L0-L4 are conditions on the *form* of a legitimacy calculus and not on its
*coverage*.** A reader looking for the round's largest remaining hole should look
here rather than at the axioms.

## 8. What no entry above claims

That the spine is minimal. L2' is used only for canonicity and could be dropped
at the cost of T2'; nothing shows the remaining six cannot be merged further.

That the interface has no counterexample. It has thirty-two checks the round
wrote, against axioms the round wrote, in two realizations the round wrote. The
one piece of evidence that the exercise was adversarial at all is §2 and §5,
where an existing fixture and a new register each refuted a choice the round had
already made.
