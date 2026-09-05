# Research round: Defeat Principle Landing, Horty Check, and Standing Repair

Prompt-author model: Claude Fable 5.1 (Anthropic), via chat. Executor: unrecorded in
the dispatch; the executor was Claude Opus 5 (Anthropic), recorded in the round's
`PROVENANCE.md`.

Work against the live alignment-workspace at current main with PR79 landed
(`2026-09-02-unified-grounds-answerable-defeat`). Inspect the actual head. This
round closes the two of PR79's outstanding maintainer actions the author has
ruled on, performs the prior-art check that `PRIORITIES.md` item 77 names as
part of its deliverable, and repairs one weakness in PR79's Lean that its report
did not flag. It does not touch items 58, 61, 75, 76, and it does not rule on
the load-discount, settlement-independence, or protected-participant
reservations, which stay in the queue.

Preserve: the settled `IssueTrace` layer (byte-identical), every PR79 theorem
that survives the repair in §3, the carriers/anchored-slices/faithful stack, and
the frozen affordability files.

## 1. First commit: the author's ruling

The author has ruled: **the Defeat Principle is adopted.** No participant
extinguishes a debt; a participant may pay it or move it onto the grounds for
saying it is not owed; only settlement extinguishes. Land this as a dated
`DECISIONS.md` entry as the round's first commit, per the standing practice
that chat rulings land as the next round's first commit (the Aug 24 entry on the
reservation bar and epistemic debt). Cite the ruling by date and content. Then
strike the corresponding "agent-decided, reversible" status from PR79's entry,
remove the Defeat Principle from *Awaiting the author*, and drop the
"conditional on the Defeat Principle" qualifier from every PR79 theorem
statement it now governs — in `THEOREMS.md`, `DEFEAT.md`, and the Lean
docstrings — leaving a one-line note that the round ran under it as hypothesis
before the ruling. Do not strike the other three reservations.

## 2. The Horty check

Item 77 says a prior-art check is part of its deliverable, names Horty's
priority orderings among defaults as the obvious place to look, and predicts
they are not enough: a priority ordering says which reason wins, not what
licenses the loser to stop being owed. `PRIOR_ART.md` §2 (Horty 2012, Pollock
1987) and its dependency note record the same open question. Settle it.

Work from the actual texts — *Reasons as Defaults* (2012), and Pollock 1987 for
the rebut/undercut distinction the round's `answer`/`dispose` kinds are built
on. Do the following, in order, and report each as a finding with a verdict:

1. **Expressibility.** Can a Horty priority ordering express `dispose`? Take
   the round's three kinds and ask what each corresponds to in Horty's
   apparatus: is a defeated default *disposed*, *answered*, or neither? State
   precisely what Horty's theory says happens to a default that loses — whether
   it retains any standing, whether it can be reactivated, whether anything is
   owed on its account — and compare to D2's successor-bearing transfer.
2. **The direction of the gap.** If Horty cannot express disposal, say which of
   D1–D3 has no image. The prediction to test: priority orderings have grounds
   (D1) but no successor (D2) and no separation (D3), because the ordering is
   exogenous and unauthored. If the prediction is wrong, say how.
3. **Undercutting.** Horty's treatment of exclusionary reasons and Pollock's
   undercutters are the closest things to `dispose`. Determine whether either
   is *answerable* in the round's sense — whether the exclusion is itself a
   claim that can be attacked in the same system — or whether it sits at a
   level the system cannot challenge. This is the crux: if an exclusionary
   reason is unchallengeable, it is a settlement fact in the round's typing,
   not a disposal, and the theory has one summand where the round has two.
4. **What survives as new.** State in one paragraph what the round's defeat
   theory adds that Horty and Pollock do not have, phrased so a reader of
   those books could check it, and what it inherits from them that
   `PRIOR_ART.md` must now cite as a dependency rather than a resemblance.
5. **Argumentation.** Do the same for ASPIC+ (Prakken 2010 / Modgil–Prakken
   2013) in one section, not a full treatment: whether argument defeat there
   has a successor, and whether the attack relation is authored. Prakken 2018
   is already cited for the statics; do not re-derive that.

Deliverable: `HORTY.md` in the round directory, with the five findings, and a
dated append to `PRIOR_ART.md` §2 and to its dependency note replacing "open
question" with the verdict. If the verdict is that Horty *can* express
disposal, that is a finding that changes what the round claimed as new; report
it prominently and do not soften it.

## 3. Repair `Answerable.contested`

PR79's `Licence` has `lic : Q → K → Ty → X → Prop` and `standsFor` has no
participant argument. So `Answerable.contested` reads `∃ b, b ≠ resolver ∧
(someone stands for q')` and `b` is unused: any participant type with two
elements satisfies the first conjunct, the standing side of D3 is vacuous, and
PR79's laundering result rests entirely on `foreign_ground`. `DEFEAT.md`'s D3
says "some `b ≠ resolver` has standing on the successor," which the Lean does
not say.

Repair by putting the participant into the licence: `lic : Q → A → K → Ty → X
→ Prop`, `standsFor Li n b κ τ x := ∃ q ∈ O n, Li.lic q b κ τ x`, and
`contested : ∃ b, b ≠ resolver n q ∧ standsFor Li n b (κ q') (τ q') (x q')`.
Carry the participant through `AnchorStanding` and `anchor_grounded` (the
licence-issue licensing a fresh issue's protocol now licenses it *for*
someone). Re-elaborate every PR79 declaration; report which ones needed more
than the type change.

Then prove the laundering theorem on both sides: a disposal walk whose
resolvers, ground-openers, **and standing-holders** all lie in one hand is
refused, with a fixture showing the standing side is now doing work — a
disposal with a foreign ground but standing held only by the resolver, refused
by `contested` alone.

State, as a definition only, the principal-relative form: `AnswerableFor P`
requires `standsFor Li n P …` on the successor. Prove the P-relative
laundering theorem (no coalition excluding P can walk a disposal to
completion). Do not present this as the general non-capture predicate; the
protected-participant question is the author's and stays in the queue.

## 4. Nonvacuity

PR79 has no Lean witness for `DefeatTrace` or `Disciplined`; every fixture is
Python, and the report's own "nothing shows a defeat-disciplined trace exists"
is the same gap. Supply one in Lean, in the style of the spine's `fixA`/`fixB`
fixtures: a finite trace with one answered issue, one settled issue, and one
answerable disposal with its successor, satisfying `Disciplined` after the §3
repair, with `#print axioms` on the witness. Add a second witness that fails
`Disciplined` by exactly one clause (a self-grounded disposal), proved to fail.
If constructing the witness reveals that `Disciplined` is unsatisfiable as
stated, that is the finding; stop and report it.

## 5. Hostile fixtures (Python, exact rationals)

Add to PR79's runner: standing held only by the resolver (refused by the
repaired `contested`); standing held by a second participant who is the
opener of every ground (accepted — the coalition case, unchanged, restated
under the new type); the P-relative walk where P holds standing at every
successor (P-laundering theorem's positive case); the same walk with P absent
from one successor (refused). Keep PR79's 24 tests passing.

## 6. Out of scope and reservations

Out: the coalition repair beyond the P-relative definition, load discount,
settlement independence, market realization of the contest charge, and
composition with the scorekeeping move grammar.

Reserve to the author only if the Horty check produces one: whether the
round's kind `settle` and Horty's exclusionary reasons are the same object
(*turns on* whether the program wants exclusion to be challengeable, which is
the settlement-independence reservation seen from prior art). Otherwise
reserve nothing new. Append per the reservation bar in `AGENTS.md`'s reserved-
items standard, with a one-line *turns on*.

## 7. Deliverables

Round directory under `projects/normativity/legitimacy/rounds/`: `REPORT.md`
first, then `HORTY.md`, `STANDING_REPAIR.md`, `WITNESS.md`, `PROVENANCE.md`,
`src/`, `tests/`. Lean edits in the spine file. Update item 77's status to
whatever the Horty verdict supports — it closes only if the check is done and
the licence predicate stands; say which. Provisional names listed in the
report per the provisional-naming standard. Fill `depends_on` in
`state/rounds.json`. Report every deviation. Do not edit `wiki/`; propose wiki
changes in the report for the maintainer.
