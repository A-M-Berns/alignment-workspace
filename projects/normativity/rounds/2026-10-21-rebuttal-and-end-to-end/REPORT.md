# Report — 2026-10-21-rebuttal-and-end-to-end

| | |
|---|---|
| Prompt author | the maintainer (`prompts/2026-10-21-rebuttal-and-end-to-end/PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Base | the branch `round/2026-10-20-warrant-enforcement-semantics` at `b5cc2b1e`, shipped in PR #129 (see *Corrections*) |
| Lean | `SeedStatics.lean` (133 declarations), `ConvergenceMeasure.lean` (55), `WarrantEntitlement.lean` (273, Part A added), `EndToEndWitness.lean` (121); all audited to the three allowed axioms, no `sorry` |
| Fixture | `src/rebuttal.py`, `src/exhibit.py`; `tests/run.py` (19 checks); the landed branch rounds' runners (28 and 20 checks) |
| Registrations | nine `lean-proved` entries in `projects/normativity/CLAIMS.md`, as the dispatch lists them |
| Filed | `PRIORITIES.md` items 117–123; items 35, 39, 112, 113 narrowed |
| Wiki | `wiki/Seed-Theory.md` (new); `Normativity.md`, `Theorem-Spine.md`, `_Sidebar.md` (entries) |
| Date | 2026-10-21 |

**Verdict.** REBUTTAL-BY-SETTLEMENT-LANDS-THE-ORPHAN-CANNOT-FORM-THE-BANKROLL-ACROSS-ONE-REOPENING-IS-THREE-RHO-TIMES-TWO-PLUS-RHO-NOT-THREE-RHO-THE-SEED-STATICS-AND-THE-INTERVAL-DATA-LAYER-ARE-ON-MAIN-AND-THE-FIRST-END-TO-END-RUN-REACHES-THE-REBUTTAL-WITH-EVERY-STAGE-HOLDING. The gloss is in `README.md`.

**Depends on** `2026-10-20-warrant-enforcement-semantics` (the odds bankroll, the licence
chain, the fixture), `2026-09-16-seed-statics` and `2026-09-17-convergence-measure` (landed
here as sources), `2026-08-16-traderized-enforcement`, `2026-09-07-final-pressure-pass`.

## Corrections to the prompt (`AGENTS.md` §8)

1. **Base deviation.** The dispatch requires `main` after the merge of PR #129 and says to
   stop if `WarrantEntitlement.lean` is not on `main`. At dispatch time PR #129 was open and
   `main` was at `2b7a1453`; the round stopped and reported. The maintainer then instructed:
   commit directly on `round/2026-10-20-warrant-enforcement-semantics`, ship both rounds in
   PR #129, keep this round's own directory and `prompts/` entry, update the warrant round's
   report where superseded, and record the deviation here. Done as instructed; the warrant
   round's documents carry dated supersession notes rather than silent edits.
2. **`IsForcedInterval.mono` and `forcedInterval_mono` are not false** under M1–M2 in their
   current form: they are about `forcedRegion`, the unspecialized-row region with the row set
   fixed, and remain true and landed. What fails is their transfer to the *settled* region
   (`Countermodel.settled_not_anti`); A4 is proved for that region.
3. **"`liability_of_odds` applies with the same `3ρ`"** is false across the rebuttal. The
   bound is `3ρ(2 + ρ)` (`netWorth_ge_neg_odds_reopened`); the two-phase cushion exhibit
   realizes `24 > 12` on the fixture (`REBUTTAL.md` A2). Before `n_E` the bound is `3ρ`.
4. **M5** remained bracketed in the dispatch; the two rulings were landed from PR #102's
   citation and marked for confirmation (`DECISIONS.md`, 2026-10-21, second entry; queued).
5. **"The bound on `Y`"** (C2, C3): C1's fragment has no coherence row tying `Y` to `X∧A∧Y`,
   so `Y`'s interval is `[0, 1]` throughout; the certificates and intervals reported are on
   the first warrant's conclusion coordinate `X∧A∧Y`.
6. **"`forcedInterval` computed by elimination (not by hand)"**: the kernel cannot evaluate
   the elimination over `ℚ` (`decide` and `rfl` stall on `Rat` normalization, probed and
   recorded). The elimination *is* run — the `#eval` lines in `EndToEndWitness.lean` print its
   output in the build log — and each interval theorem pins that output by the elimination's
   correctness theorem (`forcedInterval_eq_of_bounds` from `forcedInterval_spec`): valid
   bounds attained in the real region determine the computed pair. The hand part supplies the
   candidate and the attaining points, not the value's status as the elimination's output.
7. **"One substantive item (the first warrant)"** (C1): the first warrant is three forms; the
   seed's substantive layer carries the three, the second warrant enters as the warrant list
   `W`. `HumbleItems` holds.
8. **B3** lists `forcedRegionR_anti_warrants`; `forcedRegionR_anti_defeat` and
   `forcedInterval_nest_of_subset` (the rest of the branch's §4) are landed with it because
   they are three lines and the convergence items cite them.
9. **Retirement propagation.** M2's "every row of that occurrence leaves" is realized one
   step along `cites` plus the settlement's closure; without closure a chain of three keeps
   its last link. Stated in `REBUTTAL.md` A1, tested, filed as item 121.

## Part A — the rule and what it changes

`REBUTTAL.md`. `settleForm` with `settleForm_eq_some_iff` (P1's soundness), the contraposing
shape lemmas, M3 as `settleForm_strength`; `Grounds.survivors`, `settledRegion`,
`region_subset_settledRegion`. A2: `Fixture.survivors_eq`, `schedRebutted_eq_survivors`,
`no_strength_after`, `rebutted_region_nonempty`, `liability_rebutted` at `−3ρ(2 + ρ)` through
the new `netWorth_ge_neg_odds_reopened`; the harmonic buyer has nothing to buy
(`nothing_to_buy`); the "same `3ρ`" refuted (`cushion_exhibit`, `test-supported`). A3:
`Fixture2.old_rule_empty` (the countermodel to the warrant round's premise-guard reading),
`survivors_refuteX`, `retired_region`. A4: `settled_not_anti`, `survivors_anti`,
`settledRegion_anti_of_survivors_eq`, `settledRegion_subset_kept`, `reopening_bound`; widening
`0` on the fixture, attained. A5: the table in `REBUTTAL.md`.

## Part B — the landing

`LANDING.md`. One `SeedStatics.lean` (§1–6, 8, 10 of the branch; §7, 9, 11 excluded by the
dispatch; the transport's negated-form drop filed as item 122), `WarrantEntitlement.lean`
importing it with its Part 0 removed, `ConvergenceMeasure.lean` §1–4. The seed subproject with
both branch rounds verbatim and `ORIGIN.md`, their prompts, their runners green in the
repository runner, `normativity.seed` in `state/projects.json`, their records in
`state/rounds.json`. Items 93–96 of the branches re-filed as 117–120.

## Part C — the witness

`WITNESS.md`. Every stage of C1–C7 is a theorem on the fixture; `Run.witness` is the
conjunction of C8. The run reaches `n_E` and continues: the strength occurrence is rebutted at
`n_E` by `settleForm`, `X∧A`'s interval is `[0, 1]` before and after (the A4(b) bound attained
with widening `0`; the port-only rule would pin it to `0`), `Z`'s interval is `[1/2, 1]` at
every date, the enforcer's bankroll is `−3ρ(2 + ρ) = −72` and the conditional Normative
Inductor composes, the record is neither injective nor constant and mediates the docket, and
the hull mass runs `1/2, 5/12, 5/6, 1/2` with one reopening and is constant from `n_E`.

## The five questions

1. **Does `netWorth_ge_neg_odds` survive `settleForm` unchanged?** Yes, verbatim: it is about
   the rows a schedule holds. What changed is what it is *applied to*: across a reopening the
   slack witness changes, and the applicable statement is the two-witness
   `netWorth_ge_neg_odds_reopened` with bound `3ρ(2 + ρ)`; before the reopening the old bound
   `3ρ` applies with the old witness.
2. **By how much can one reopening widen a forced interval, and is the bound attained?** By
   at most the width the removed rows had been forcing off the kept rows' pre-step interval:
   both the pre- and post-step settled regions lie inside `regionOn (survivors F') F`
   (`settledRegion_subset_kept`, `reopening_bound`). On the fixture the removed strength row
   forced nothing on `X∧A` at the pre-step settlement, the allowed widening is `0`, the actual
   widening is `0`: attained with equality. The rule's effect on the fixture is to prevent the
   contraction to `[0, 0]`, not to widen.
3. **Did the run reach `n_E` with every stage holding?** Yes, and beyond: C1–C7 hold as
   theorems at every date; C8 is `Run.witness`. The one place the run differs from the
   dispatch's picture is the bankroll constant (`72`, not `12`) and the bound on `Y` (on
   `X∧A∧Y`, correction 5).
4. **What did the branches contain that was not landed, and what does the next instance of
   item 35 need?** Not landed: confinement (§7), transport (§9), non-dogmatism (§11) of the
   seed round; the discord certificate (§5), hull-mass convergence (§6) and the pinned
   fragment (§7) of the convergence round; both rounds' `DECISIONS.md` entries. A
   *two-reasoner* instance needs confinement and the discord certificate; the limit statement
   of P2 needs §6; a fragment that changes between dates needs transport, with its negated-form
   drop fixed (item 122). The first instance needed none of them.
5. **Reserved to the maintainer.** Below.

## Verification

Run on 2026-10-21 in the worktree, `lean/.lake` linked to a populated cache (the memory note
on local Lean setup applies).

```
$ ~/.claude/scripts/safe-lake.sh build          # the whole Workspace library
Build completed successfully (4090 jobs).
```

Per-file axiom audit (`lake env lean` on each file, every `#print axioms` line parsed):

```
SeedStatics.lean         133 declarations audited, disallowed: {}
ConvergenceMeasure.lean   55 declarations audited, disallowed: {}
WarrantEntitlement.lean  272 declarations audited (273 lines; one name with an apostrophe
                             the parser skips), disallowed: {}
EndToEndWitness.lean     121 declarations audited, disallowed: {}
```

The repository audit, re-elaborating every file:

```
$ python3 tests/audit_axioms.py
AXIOM AUDIT: 3017 results across 103 files, all within ['Classical.choice', 'Quot.sound', 'propext']
```

The repository runner (`lean/.lake` set aside for the run, as the untracked-pointers gate requires):

```
$ python3 tests/run.py
WIKI LINKS: clean over 32 page(s) (links resolve; repository links are commit-pinned)
WIKI STATE BINDINGS: clean over 34 page(s); 3 binding(s) verified against the state emission
Ran 68 tests in 5.522s  OK
GATE COVERAGE: 11 gate scripts, all invoked (5 self-test only — no local form)
LEAN SORRY GATE: clean over 103 files
LEAN AXIOM DISCIPLINE: every file carries `#print axioms`
ALL GREEN (78 project(s))
$ python3 -m checkers.run
REGISTRY projects/deference/CLAIMS.md:   registry schema: ok   105 entries, 0 adjudicated here
REGISTRY projects/normativity/CLAIMS.md: registry schema: ok   66 entries, 1 adjudicated here
```

The elimination, executed (`#eval` in `EndToEndWitness.lean`, from the build log):

```
intervalAt 0 XAY  = (2/5, 1)        intervalAt n₀ XA  = (0, 1)
intervalAt 0 Z    = (1/2, 1)        intervalAt nE XA  = (0, 1)
intervalAt n₁ XAY = (1/2, 1)        intervalAt nE XAY = (0, 0)
intervalAt nE Z   = (1/2, 1)        survivors at nE   = [1, 4]
decideLicensed … XAY certXAY 7 = true;  decideLicensed … Z (certZ 0) 7 = true
```

Round runners:

```
$ python3 projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/tests/run.py
Ran 19 tests … OK
$ python3 projects/normativity/seed/rounds/2026-09-16-seed-statics/tests/run.py
Ran 28 tests in 12.179s  OK
$ python3 projects/normativity/seed/rounds/2026-09-17-convergence-measure/tests/run.py
Ran 20 tests in 55.916s  OK
```

## What this round does not establish

- The cushion exhibit (`24 > 12`) is `test-supported`: two single-coordinate phases with a
  maker that zeroes the aggregate, not the pinned `MarketMaker`; the Lean proves the upper
  bound `3ρ(2 + ρ)` and does not prove that `3ρ` fails. Item 123.
- Retirement propagation is one step along `cites`; the fixtures rely on closed settlements.
  Item 121.
- The witness holds the computable-market and uptake hypotheses as hypotheses, does not run
  the market maker, and does not evaluate the elimination in the kernel (correction 6).
- `Licensed` and the record are still the warrant round's objects on the port-only bundle;
  their settled-bundle form is item 115's.
- The landed branch documents cite declarations not on `main` (listed in each `ORIGIN.md`).
- The two reasoners' results of `ConvergenceMeasure` §1–4 are landed and unused by the
  witness, which reports `ι = Unit`.

## Items filed

117–120 (the branch items, re-filed, content unchanged), 121 (transitive retirement and the
closure requirement), 122 (the transport's negated-form drop), 123 (the reopened bankroll's
sharp form and the cushion exploit against the pinned maker). Narrowed: 35 (first instance
landed), 39 (geometric half registered), 112 (the orphan cannot form under the rule), 113
(answered by the rule).

## Registrations

As the dispatch lists, `lean-proved`: `rebuttal.settleform-sound` (`settleForm_eq_some_iff`),
`rebuttal.liability-rebutted` (`Fixture.liability_rebutted`) against item 113;
`seed.forced-interval-spec`, `seed.forced-interval-bounds` against item 39;
`seed.independence-strict`, `seed.eventually-const` against item 117 (the re-filed seed items);
`convergence.hull-mass-anti`, `convergence.discord-persists`, `convergence.discord-pairwise`
against item 119. Listed and not registered: every other Part A and Part B theorem named in
`REBUTTAL.md` and `LANDING.md`, and all of Part C.

## Names, provisional

*rebutted*, *vacuous*, *retired* (the three removing outcomes of `settleForm`), *reopening*
(a settlement step that removes rows), *end-to-end witness* (P3); and *survivors*, *settled
region*, *reopened mass*, *cushion exhibit*.

## Outstanding maintainer actions

1. **Confirm or strike the landed 2026-08-08/09 rulings** (M5) — `DECISIONS.md`, *Awaiting the
   author*, the 2026-10-21 entry.
2. **Close PR #102 and PR #103** with a pointer to `LANDING.md` (M6).
3. **Rule on the reopened bankroll** — whether `3ρ(2 + ρ)` is accepted as the entitlement
   across a reopening or the rule is to be tightened so that a rebutted row's counterparty
   gains do not cushion later selling (e.g. settlement-time accounting of the reopened mass);
   queued as the second 2026-10-21 entry.
4. **Merge PR #129**, which now carries both rounds; reserved on the pull request.
