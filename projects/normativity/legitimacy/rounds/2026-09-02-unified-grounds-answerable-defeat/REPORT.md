# Report — Unified Grounds and Answerable Defeat

**Answers `PRIORITIES.md` item 77** (what licenses authorized disposition). Touches
items 58, 61, 75 and 76 only to file non-goals against them.

## Verdict

GROUNDS-UNIFIED-AND-DEFEAT-IS-ANSWERABLE-BUT-SEPARATION-IS-NOT-COALITION-PROOF — a disposal must be able to cite prior issues, standing facts, rule revisions and settlement facts, and no pre-unification type held them: Q held issues, N held standing and the effect of a revision, nothing held settlement, and the two families were joined by a predicate rather than an embedding, so a mixed set of grounds had no type at all. Ground := Q + S repairs this, and the unification is exact rather than analogical because the standing layer's update law is literally the issue layer's: Ladd is birth, Ldel is resolution, grounds is par, and Requirement 1's step is resolution_continuity. StandingTrace, Licensing and the inductive Grounded are deleted as primitives; freshness becomes a theorem of born_unique, Grounded Replay becomes strong induction on birth position with the strictly-decreasing-position clause a consequence rather than a hypothesis, standsFor becomes a filter on the outstanding set, and anchor_grounded loses its cross-layer bridge because there is one trace. Two requirements do not re-derive and are carried as side conditions: the Auth filter on grounds is data ancestry does not supply, and nonemptiness of grounds is false of genesis issues. Met becomes a definition, which makes Requirement 9 a theorem and makes a disposed root meet nothing; because Routes is ancestry-closed and every disposal is required to open a fresh successor inheriting the disposed issue, a wait on a disposed root reroutes with no new axiom, so a prerequisite cannot be disposed away. Answerable disposal is grounded, routed and separated, and separation forbids any disposal walk whose edges, grounds and standings lie in one hand. Two findings run against expectation. Priority does not refuse self-grounding: the disposed issue is by construction in the record strictly before its own disposal, so the transition-certificates collapse of no-self-grounding covers the successor and everything born in the batch and fails for the issue itself — priority refuses grounding in what a record mints and cannot refuse grounding in what it consumes — so the not-self clause is a clause and not a lemma. And separation stops one participant but not two: an alternating walk in which each participant supplies the other's foreign ground and foreign standing satisfies D3 at every edge and launders indefinitely, because D3 is the coalition predicate at C = {resolver}; the general form needs a designated protected participant outside every coalition quantified over, since it is unsatisfiable at C = A. Disposal contributes zero to either terminal fate on both accounting layers: the carrier layer's disp receipt is identically bottom and Slice-wise Conservation loses a term, while on the service layer disposal is a claim-to-claim transport step with L = 1 and epsilon = 0, F3 factors through it, and the contest residual adds D kappa to the F3 bound as a corollary of F3 plus conservation and nothing more. Persistence acquires a second conjunct — the total contest duration must be summable — under exogenous durations only; the closed-loop version is item 75. Reach is preserved for a principal whose corrective matters are separated, but that is reach and not the ability to open a challenge nor its service, and the composition is not proved. Item 77 is not fully discharged: the Horty prior-art check it asks for was not performed.

## In short

One ground type replaces two traces; `StandingTrace`, `Licensing` and the inductive
`Grounded` are deleted as primitives and everything they proved is re-derived from
ancestry, with two named exceptions. Disposal is given a licence predicate (D1–D3)
with a soundness theorem and a laundering theorem. `Met` becomes a definition, and the
strengthening the dispatch asked about — *a prerequisite cannot be disposed away* —
holds and is proved. Two findings run against the dispatch's expectations: priority
does **not** refuse self-grounding, and separation does **not** stop a two-participant
coalition.

## 1. What was established

**The diagnosis.** A disposal must be able to cite prior issues, standing facts, rule
revisions and settlement facts. `Q` held the first; `N` held the second and the
*effect* of the third; **nothing** held the fourth; and the two families were joined
only by a predicate, not an embedding. So a mixed set of grounds had **no type at
all** — that is the gap item 77 hits before any question about which grounds suffice.
`GROUNDS.md` §1.

**The unification.** `Ground := Q ⊕ S`. The two layers were already the same equation
— `L(n+1) = (L n \ Ldel n) ∪ Ladd n` **is** `O(n+1) = (O n \ Res n) ∪ Born n` — so
`Ladd` is birth, `Ldel` is resolution, `grounds` is `par`. Re-derived in Lean:
`fresh` (was a postulate), `grounded_replay` (now by strong induction on birth
position, with the decreasing-position clause a consequence rather than a hypothesis),
`grounded_replay_live`, `standsFor` (a filter on `O n`), `anchor_grounded` (no bridge,
because one trace).

**`Met` as a definition.** Requirement 9 becomes the theorem `met_persistent'`. A
disposed root meets nothing (`dispose_not_met`). And `routes_survive_dispose`: because
`Routes` is ancestry-closed and `dispose_successor` supplies a fresh child, a wait on
a disposed root **reroutes to the successor with no new axiom**. Asked as
"theorem or refute it" — it is a theorem.

**Answerable disposal and separation.** D1–D3 with `Disciplined`; laundering
characterized as a single-participant walk in the disposal graph and forbidden by D3's
foreign-ground clause.

**Conservation.** One rule lands on both layers: `dispose` contributes zero to either
terminal fate. Carrier layer — the `disp` receipt is identically bottom and the
invariant loses a term. Service layer — disposal is a claim-to-claim transport step
with `L = 1, ε = 0`, F3 factors through it, and the contest residual `κ^r_N` adds
`D·κ^r_N` to the F3 bound as a corollary of F3 plus conservation and nothing more.

## 2. The two findings

**Priority does not refuse self-grounding.** The transition-certificates round's
postulate 5 collapsed because self-certification died on priority alone. On the
unified trace that collapse covers the successor and everything born in the batch —
and **fails for the disposed issue itself**, which is by construction in the record
strictly before its own disposal, so `Grounded` holds of it. The clean reading:
priority refuses grounding in what a record *mints* and cannot refuse grounding in what
it *consumes*; a certificate mints, a disposal consumes. `Answerable.not_self` is a
clause, not a lemma, and `self_grounding_not_excluded_by_priority` records it in Lean
as a positive statement.

**Separation does not stop coalitions.** Two participants alternating disposals each
satisfy D3 in full — each supplies the other's foreign ground and foreign standing —
and the pair launders indefinitely. D3 is the coalition predicate at `C = {resolver}`.
The general form needs quantification over coalitions, which is unsatisfiable at
`C = A` without a **designated protected participant**. Filed with the statement the
general predicate would need; not repaired. `DEFEAT.md` §5.

## 3. Deviations from the dispatch

Declared per `AGENTS.md` standard 8.

1. **New fields go on `DefeatTrace extends IssueTrace`, not on `TraceData`.** Adding
   `S` and `A` to `TraceData` makes it `TraceData Q D S A`, and the two extra type
   parameters propagate through every theorem, every fixture and `IssueTraceCore` —
   changing the settled Continuity specification the same dispatch instructs be
   preserved. Extending leaves the settled spine byte-identical.
2. **`Met` keeps its field, with `met_def` asserting it equals the definition.**
   Deleting the field would touch `TraceData` for the same reason. `met_def` is
   checkable and makes `met_persistent'` derivable exactly as asked.
3. **The field named `by` is `resolver`.** `by` is a Lean keyword.
4. **The dispatch's R-numbers do not resolve.** It cites "(R2)", "(R4)", "(R5)",
   "(R9)" for agent-decided reversibility, provisional terminology, Lean headline
   registration and depends-on/rests-on. `AGENTS.md`'s numbered standards are
   1 consolidated work, 2 exact arithmetic, 3 four things, 4 Lean discipline,
   5 runners, 6 provisional names, 7 citation integrity, 8 declared deviations,
   9 reports state what was not shown, 10 reserved items. Only R5→runners and
   R9→"what was not shown" are near-misses; R2 and R4 are not. Per standard 7
   (never a remembered label) the intent is followed and the labels are not
   reproduced: reversibility is recorded in `DECISIONS.md`, names are marked
   provisional per **standard 6**, and `depends_on` is filled in `state/rounds.json`.
5. **Postulate 5 is cited by content, not by label.** The dispatch says it is "a
   theorem of its checker, not an axiom — see its `MEMO.md` row 5". Verified: row 5 of
   that memo, failure code `posterior-basis`, test
   `test_no_self_grounding_clause_exists_yet_the_attacks_fail`. The citation checks out
   and the finding above narrows it rather than contradicting it.
6. **`κ^r_N` uses `μ^r_N`, not the pre-audit "claim measure".** The September naming
   audit (PR #78) renamed claim→obligation. The dispatch's "terminal claim measure"
   is written here as the terminal obligation measure `μ̃^r_N`; the symbol is
   unchanged, per that audit's rejected-alternative note.

## 4. Provisional names introduced (standard 6)

`Ground`, `Kind` (`answer` / `dispose` / `settle`), `Kind.Discharges`, `DefeatTrace`,
`dispose_successor`, `met_def`, `DefeatTrace.Grounded`, `Licence`, `standsFor`,
`AnchorStanding`, `Answerable` (D1–D3: `grounded`, `not_self`, `born`, `inherits`,
`contested`, `foreign_ground`), `Disciplined`, terminal obligation measure `μ̃^r_N`,
contest residual `κ^r_N`, contest duration `τ(q')`, **answerable disposal**,
**defeat-disciplined trace**, **laundering walk**.

All marked provisional; none is proposed for the wiki or `state/vocabulary.json`.

## 5. What this does not establish (standard 9)

- **The Defeat Principle is no longer a hypothesis.** The round ran under it as a hypothesis; it was adopted by maintainer ruling on 2026-09-03 (`DECISIONS.md`). The theorem
  statements below are therefore unconditional on it. Nothing else about them changed.
- **Only T2 and the §5 supporting results are Lean.** T1 (service layer), T3, T4 and
  T5 are paper-derived and test-supported, which is not citable as proven.
- **D3 is broken against coalitions** and the round does not fix it.
- **The `Auth` filter and grounds-nonemptiness do not re-derive** from ancestry and are
  carried as side conditions. The unification is not free.
- **T4's contest charge has no market realization.** It is a budget drain by
  stipulation.
- **`τ` is policy-dependent** and the closed-loop version is item 75, untouched.
- **T3 preserves reach only** — not the ability to open a challenge (item 58), not
  service. The composition is not proved.
- **Nothing here shows a defeat-disciplined trace exists** for any interesting
  practice.
- **Horty's priority orderings were not reviewed.** Item 77 asks for a prior-art check
  and names them as the obvious place to look. **This round did not do it**, and item
  77 is therefore *not fully discharged*. See Outstanding actions.

## 6. Verification

- `python3 tests/run.py` from the round directory: **24 tests, all passing**, exact
  rationals throughout (standard 2).
- Lean: `lake build Workspace.Normativity.Contrib.NormativeContinuity` — **clean, 976
  jobs**; sorry-free; **35 declarations audited, every one to exactly
  `[propext, Classical.choice, Quot.sound]`** (standard 4).
- Every pre-existing theorem in the spine re-elaborates. The `IssueTrace` layer is
  byte-identical to the settled specification.

## 7. Outstanding maintainer actions (standard 10)

1. ~~**Rule on the Defeat Principle.**~~ **Done** — adopted by maintainer ruling,
   `DECISIONS.md` 2026-09-03.
2. **Decide whether disposal transfers load in full or at a discount.** *Turns on*
   taste about second-order liability; changes T4's constants, not its structure.
3. **Decide whether settlement's independence from the disposer's writes is a standing
   hypothesis of the program or a per-realization assumption.** *Turns on* where `L_t`
   comes from in the assessment-process generalization. Fixture 3′ shows the hypothesis
   is load-bearing either way.
4. **Rule on the coalition finding.** *Turns on* whether legitimacy may presuppose a
   designated protected participant. Without one the coalition-indexed predicate is
   unsatisfiable at `C = A`.
5. **Commission the Horty prior-art check** that item 77 asks for, or re-scope the
   item. This round did not do it and item 77 should not be closed until someone does.
6. **Register the Lean headlines** if wanted. Nothing is registered by this round; all
   eleven `DefeatTrace` declarations are unregistered and marked provisional.
