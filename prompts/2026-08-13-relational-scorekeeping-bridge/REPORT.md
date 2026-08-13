# Report

**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Dates:** dispatched and executed 2026-08-13
**Verdict:** `Shared-substrate-positive`

The round's own documents carry the results: `THEOREM_MAP.md` for what was shown
and at what strength, `PROSECUTION.md` for where the architecture is weaker than
the verdicts read, `TWO_ARC_INTERFACE.md` for the interface and the dispositions,
`BRANDOM_MAP.md` for the source separation. This report carries what belongs to
the round rather than to the result: the answers to §XVII, the deviations, what
was not shown, and what is reserved.

## The construction, in one paragraph

Attribution is computed from the target's public acknowledgments under the
scorekeeper's own inferential practice — `commitments_i(j) = closure of ack[j]
under practice[i]`. Every move is agent-indexed and no move writes another agent's
acknowledgments or practice. Practical authority is a scoped grant relation read
by a transition precondition; altering it is itself a practical move over a
reserved subject, and doxastic moves are unconditioned, which stops the regress at
one level. 102 exact finite tests, exact rationals throughout, no Lean.

## §XVII, answered

**Q1 — reinterpretation, or a missing object?** A missing object, and it is one
equation rather than a formalism. The evidence that it is not a reinterpretation
is `test_the_perspectival_difference_is_what_carries_the_two_theorems`:
substituting the target's own practice for the scorekeeper's — the reading the
equation rejects — makes the central theorem fail on the same trajectory.

**Q2 — can the learner change what it takes itself to owe?** Yes, and it changes
nothing it remains answerable for. T2, with an exhaustive check that no move of
`H` writes `practice[C]` or `ack[C]`.

**Q3 — can another scorekeeper challenge it without becoming an oracle?** Yes.
Every agent scores every agent, both directions of challenge are entitled
simultaneously, and the model contains no oracle field. The limit is stated in
`PROSECUTION.md` §2: a unanimous, internally coherent, factually wrong position is
not caught, because the model has no world.

**Q4 — reified applicability without a rule regress?** Yes, and it needed no
machinery: `a_rho` is an ordinary content in `rho`'s premise set. Asserting it
installs nothing, checked against a scorekeeper whose practice lacks `rho`.

**Q5 — do the statics survive as a quantitative enrichment?** Partly, and the
round is honest that it produced no evidence either way about the quantitative
half. The qualitative half — warrants, strict consequence, defeaters,
applicability — is absorbed, two of those four as *derived* rather than
reinterpreted. The graded layer is untouched. The answer to the framing question
is that scorekeeping does not replace the statics; it says what they are statics
of.

**Q6 — nontrivial loss-blind fixed transformations, or does collapse remain?**
Both, and the shape is the round's sharpest learning finding. The collapse
reproduces under record-responsive admissibility, and the sharp form is not that
the class is thin but that the labels it pins are the repairs with content —
`disavow` is pinned, so no uniform comparator may replace erasing a challenged
commitment with reopening it. Widening admissibility removes the pinning and
gives a class that permits sending `vindicate` to `self-revise`. Neither uniform
reading is worth having. The fixed-program reading escapes both, and the diagnosis
is that the uniform reading imported a quantifier the source online-learning
theorem never carried: it asks for a fixed *rule* inducing a history-indexed
family, not a state-independent map.

**Q7 — epistemic deference without transferring jurisdiction?** Yes, over advisor
runs of any length, by invariant rather than by bounded search.

**Q8 — standing separated from access, then recombined?** Yes, all four cells
witnessed, and both of the deference review's requirements met.

**Q9 — is the shared architecture plausible?** Yes for the objects; not yet for
the arrows. Both arrows are missing their far end rather than a different object:
learning needs a learner and a regret theorem, and corrigibility needs a
derivation that the authority coordinate must be arranged as the fixture arranges
it.

## Deviations from the dispatch

1. **§IV's candidate state was not implemented as given.** The dispatch proposed
   `C_i(j)` and `E_i(j)` as state. They are derived operations here, not stored,
   because storing them would let a scorekeeper's attributions drift from the
   record and would make T1 a matter of write access rather than of the rules —
   which §VII.T1 explicitly forbids.

2. **§VI's "derive standing from availability of normative moves" was not
   followed for practical authority.** Standing for a *challenge* is derived, as
   asked. Practical authority is a primitive scoped relation, because deriving it
   from move availability inverts the dependency: `perform`'s precondition must
   read something, and if what it reads is which moves are available the
   definition is circular. `MODEL.md` records the comparison against the
   dispatch's four candidates and why two were rejected.

3. **§VIII.L3's expected negative did not appear where expected.** Date-indexed
   certification was anticipated as the residue of a state-sensitive comparator
   class and is absent, for a shallow reason recorded in `PROSECUTION.md` §5: the
   guard reads six booleans and there is no date in the state. Reported rather
   than absorbed, because the absence is less interesting than the dispatch's
   expectation implies.

4. **§IX.C5's suggested interpretation was partly declined.** The dispatch
   proposed reading the protected effect as making an entitled challenge
   effective. The fixture supplies a cleaner one: the protected effect is
   revocation of the advisor's scoped authority, and challenge-effectiveness is a
   separate matter that the model does not protect. `PROSECUTION.md` §3 says why —
   the burden a challenge generates is computed under the challenged party's own
   practice, so a party that revises its practice can make a challenge inert. That
   is C3, and it is why the two conjuncts are independent rather than composable
   into one.

5. **No Lean.** The dispatch permits but does not require it. The toolchain is
   present (`lean/lean-toolchain` pins `leanprover/lean4:v4.31.0`, and `lake` is
   on the path) and a port was not attempted; the results worth kernel-checking
   are the grant invariant and the write-discipline enumeration, and both are
   named as port targets below rather than half-done.

## How PR #27 was used

As evidence, replayed as an attack, never as a dependency. The branch was fetched
and read; nothing was cherry-picked, imported, or depended on, and no test
references it. The round branches from `origin/main` at `8ebb00f`.

Two of its findings were consumed. Its record-equivalence result — one trajectory,
two environments differing only in whether the reasoner's copy of a relation is
faithful, with no trajectory predicate separating them — is the obstruction this
round's central equation is built against, and `PROSECUTION.md` §1 states exactly
how much of it the equation removes and how much it does not. Its comparator
collapse is reimplemented here from scratch on this round's own fixture and
alphabet, under two admissibility notions rather than one.

The round's artifacts are coherent whether #27 merges, is rewritten, or is
abandoned: nothing here cites its paths, its identifiers, or its vocabulary.

## What this round does not establish

- Nothing is registered and nothing is kernel-checked. Class is `test-supported`.
- **Self-certification is repaired for a reasoner acting alone.** Two colluding
  scorekeepers face nothing here, and the model has no notion of collusion.
- **The protection is arranged, not derived.** The advisor cannot seize authority
  because the fixture withholds the reserved subject. The finding is that once
  authorization is a coordinate a precondition reads, the question is well-posed
  and has an exact answer — not that a real system's coordinate must be arranged
  this way.
- **No world.** Agents are convicted only by rules they hold. A coherent unanimous
  factual error is invisible to the model.
- **No learner.** L5 exhibits a comparator's saving and the lower bound's
  arithmetic at four horizons. No online algorithm was implemented and no regret
  curve measured; the Theorem 18 instantiation is inherited from the existing
  bridge round rather than re-established here.
- **The recurrence is staged.** Positions are re-filed at each date rather than
  allowed to evolve, which makes the loss exogenous and the comparison additive by
  construction. Endogenous evolution is the case the learning track's own
  applicability audit places outside its additive reduction, and it bites harder
  here because every repair in the grammar alters the position the next date's
  loss is read from. This is the sharpest untested hypothesis in the round.
- **Reasons-responsiveness thins rather than reduces.** Doxastic moves have no
  preconditions, so the condition becomes vacuous on that half. The round's
  position is that its work is done by the loss, which is a relocation.
- **The nine programs are hand-chosen**, as the existing track's nine are. The
  comparator-language question that track records as open is untouched.
- Declared modelling simplifications — challenge stratification, unchained
  testimony, opaque contents, committive rules transmitting entitlement, one
  occasion — are listed in `MODEL.md` with their reasons.

## New names introduced

All **provisional**, none proposed for adoption:

`relational scorekeeping state`, `answerability defect` (the public loss),
`public status` (the sealed guard context), `reserved authority subject`,
`pinned label`, `tolerant` and `record-responsive` admissibility,
`principal-exclusive effect`, `real answerability` (the combined predicate).

The loss weights (`1/2, 1, 1/2, 1`) and the choice of nine programs are
parameters, not results, and no result turns on their values beyond the exact
numbers reported.

## Structural defects found

None. No dead pointer, no status a document could not express, no convention that
would have forced a false statement. `AGENTS.md` §14's obligation is discharged by
this line rather than by an entry.

## Outstanding maintainer actions

Nothing is reserved. This round files no `PRIORITIES.md` item, appends nothing to
`DECISIONS.md`, registers no claim, and asks for no decision. The dispatch did not
grant scope to file items, and the round's findings are proposals recorded in its
own artifacts, per `AGENTS.md` §11.

Two port targets are named for a later round rather than reserved as actions: the
grant invariant behind C5b, and the write-discipline enumeration behind T2. Both
are short, both currently rest on Python, and neither is claimed.
