# Report — Defeat Principle Landing, Horty Check, and Standing Repair

Closes two of PR79's outstanding maintainer actions, performs the prior-art check
`PRIORITIES.md` item 77 names as part of its deliverable, and repairs a defect in
PR79's Lean that its report did not flag.

## Verdict

DEFEAT-PRINCIPLE-LANDED-HORTY-CANNOT-EXPRESS-DISPOSAL-AND-THE-STANDING-CLAUSE-WAS-VACUOUS — the Defeat Principle is adopted by maintainer ruling and its consequences are no longer conditional; Horty's machinery cannot express authorized disposition, and the reason is deeper than item 77 states, since his theory says what to conclude rather than what is owed and therefore has no account for a licence to operate on, while his exclusion mechanism turns out to be challengeable in-system and so is closer to disposal than to settlement, leaving the round's two summands intact rather than collapsed; ASPIC+ has neither a successor nor an authored attack relation, and its reinstatement is computed by the semantics rather than licensed by a participant, which is the opposite of a transfer; PR79's separation condition bound a participant its body never mentioned, so the standing half of D3 was vacuous and every laundering result in that round in fact rested on the foreign-ground clause alone, a defect the Python model did not share and therefore did not catch; with the participant carried into the licence the standing side alone refuses a single-handed disposal, which closes the case of a disposal citing only settlement facts, since such a disposal satisfies the foreign-ground clause vacuously; and the specification PR79 wrote down now has a Lean model, together with a second trace proved to fail it at exactly one clause, which turns the round's first finding from a remark into a checked pair.

## 1. The ruling, landed

The Defeat Principle is adopted (`DECISIONS.md`, 2026-09-03, maintainer ruling), landed
as this round's first commit. The reservation is struck from *Awaiting the author*;
PR79's entry no longer reads "conditional on the Defeat Principle"; and the qualifier
is gone from `THEOREMS.md`, `DEFEAT.md` and the two Lean docstrings that carried it,
each leaving a one-line note that the round predates the ruling. **The other three
reservations are untouched.**

## 2. The Horty check — five findings

Full text in `HORTY.md`. Headlines:

1. **Expressibility — no.** And the item's own reason concedes too much. Horty computes
   a *proper scenario*: a defeated default is simply not selected, with no residue and
   nothing attached to it. His theory says **what to conclude, not what is owed**, so
   there is no account for `MayDispose` to operate on and the question does not arise
   inside it.
2. **Direction of the gap — the prediction is right about *which* clauses have images
   and wrong about *why*.** Grounds yes, successor no, separation no. But separation is
   missing **not** because the ordering is exogenous: Horty specifically built variable
   priority default logic, where priorities are established by higher-order defaults.
   What is missing is **authorship, not endogeneity** — a default theory has no
   participants. So the gap is not repairable by making priorities more dynamic.
3. **Undercutting — the crux resolves the other way.** Horty implements undercutting as
   a triggered default lowering the undercut rule's weight below a threshold. The
   undercutter is itself a default and so is itself defeasible: **exclusion is
   challengeable in-system.** An exclusionary reason is therefore a `dispose` without a
   successor, **not** a `settle`. The theory does *not* have one summand where the round
   has two, and the round's separation of the two survives.
4. **What is new**, checkable by a reader of the books: *proper scenarios and ASPIC+
   extensions are a function of the current theory and of nothing in the history of
   defeats.* Delete the record of which defaults lost, recompute, same answer. The
   round's successor-bearing transfer makes the future depend on that history. What
   becomes a **dependency** rather than a resemblance: `answer`/`dispose` **is**
   Pollock's rebut/undercut, transposed from a belief's warrant to a debt's.
5. **ASPIC+** — no successor; reinstatement exists but is computed by the semantics
   rather than licensed, which is the opposite of a transfer; preference ordering
   exogenous in the canonical framework, so the attack relation is unauthored. Here the
   dispatch's prediction is exactly right.

## 3. The standing repair

`STANDING_REPAIR.md`. PR79's `contested` bound `b` and never used it, so it reduced to
`(∃ b, b ≠ resolver) ∧ (someone stands)` — vacuous for any participant type with two
elements. Repaired by putting the participant into the licence.

Two things worth stating plainly:

- **No PR79 theorem was false.** Everything it proved is true; the definition was
  weaker than its own prose, and the laundering claim rested on one clause while
  appearing to rest on two.
- **The repair closes a case, not just a binder.** `foreign_ground` is satisfied
  *vacuously* by a settlement ground, since no participant opened it. So a disposal
  citing only settlement facts previously satisfied all of D3 uncontested. After the
  repair `contested` is what refuses it. `foreign_ground_dichotomy` states exactly what
  the grounds side gives, rather than overstating it.

**Nothing needed more than the type change** — which is itself the confirmation that no
prior result was consuming `contested`.

## 4. Nonvacuity

`WITNESS.md`. `Witness.witness_disciplined` is the first Lean inhabitant of
`Disciplined`; `Witness.witnessBad` fails `Answerable` at `not_self` and is proved to
satisfy `grounded`, `born` and `inherits`, turning PR79's first finding into a checked
pair.

## 5. Deviations (standard 8)

1. **PR79 had not landed.** The dispatch says to work "at current main with PR79
   landed"; `main` was `51898f2` and PR79 was open. This round is **stacked on PR79's
   head** rather than on `main`, since merging is the maintainer's and the ledger says
   a merge is never a queue entry. If #79 merges first this rebases cleanly.
2. **The Horty check is partial.** The dispatch says "work from the actual texts."
   *Reasons as Defaults* was **not read** — author-site certificate mismatch, blocked
   archive, paywall — and neither was Pollock 1987. Findings rest on the ASPIC+ tutorial
   (read directly), SEP, and the publisher's description. Claims that would need the
   primary text are marked *unverified* and not asserted. **Item 77 does not close on
   this.**
3. **`PRIOR_ART.md`'s Pollock URL is dead**, though marked "citation verified
   2026-09-01". Recorded rather than quietly repaired; the verification stands as a fact
   about its date, the link does not.
4. **No new reservation was appended.** The dispatch permits one *if the Horty check
   produces it*. Finding 3 answers the `settle`-vs-exclusion question rather than
   raising it, so there is nothing to reserve.
5. **A fixture bug of my own**, found while writing §5 and recorded in
   `STANDING_REPAIR.md` §5: standing was first read at the live prefix instead of the
   disposal's own batch. Same class of error as the defect being repaired.

## 6. Provisional names (standard 6)

`InOneHand`, `LaunderingWalk`, `AnswerableFor`, `not_in_one_hand_of_contested`,
`foreign_ground_dichotomy`, `no_laundering_walk`, `no_coalition_excluding_principal`,
`Witness.*` (`bornAt`, `resAt`, `Resolves`, `witness`, `witnessBad`, `wlic`),
`StandingModel`, `standing_holders`, `edge_holders`, `principal_holds_throughout`,
`coalition_walks_excluding`, `single_handed_edges`.

## 7. What this does not establish (standard 9)

- **The Horty check is incomplete** — see deviation 2. This is the largest gap and it
  is the item's own deliverable.
- **The coalition hole is not closed.** `AnswerableFor` is a *definition* plus a
  one-line theorem, deliberately not offered as the general non-capture predicate. The
  two-participant alternating walk still launders under plain separation.
- **The P-relative form names a party**, which is exactly what the open reservation is
  about. Nothing here argues that a legitimacy predicate may do so.
- **The witness is small.** It exercises the three kinds and not the prerequisite/route
  machinery; it shows `Disciplined` is satisfiable, not that any interesting practice
  satisfies it.
- **T1, T3, T4, T5 of PR79 remain paper-derived**, unchanged by this round.
- **`Auth` and grounds-nonemptiness still do not re-derive** from ancestry.
- Findings 1–4 are **readings of secondary sources**, not of the books.

## 8. Outstanding maintainer actions (standard 10)

1. **Merge or rebase PR79** — this round is stacked on it and does not stand alone.
2. **Commission the primary-text Horty check**, or rule that the secondary-source
   verdict suffices. Item 77 stays open until one or the other.
3. **Repair `PRIOR_ART.md`'s Pollock link** or drop the URL; the "verified" mark now
   over-claims.
4. **Three reservations remain in the queue**, untouched: load discount, settlement
   independence, protected participant.
5. **Wiki changes proposed, not made** (the dispatch forbids editing `wiki/`):
   `wiki/Normativity.md` or a new page has no account of defeat at all, and now could
   carry one — obligation, the three kinds, and why disposal moves rather than
   extinguishes. Recommend a short section rather than a page.
6. **Register Lean headlines** if wanted; nothing is registered.
