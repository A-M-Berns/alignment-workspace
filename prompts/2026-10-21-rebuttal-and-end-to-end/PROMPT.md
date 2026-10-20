# Prompt — rebuttal by settlement, the seed landing, and the first end-to-end run (2026-10-21)

You are working in the `alignment-workspace` repository, on `main` **after the merge of
PR #129** (the warrant-enforcement-semantics round). If
`lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean` is not on `main`, stop and
report. Do not stack this round on an unmerged branch. Two unmerged branches are
*sources* for Part B; they are not bases.

Round directory: `projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/`.
The prompt goes verbatim in `prompts/2026-10-21-rebuttal-and-end-to-end/PROMPT.md`.
New priority items start at 117.

## What this round is for

PR #129 found that a linear strength row contraposes under settlement and that the
contraposition is exploitable (item 113, the orphan pin of item 112). The maintainer has
ruled on the repair (M1–M4 below). This round lands the rule, re-proves the affected
statements under it, lands the seed-statics and convergence material the end-to-end
construction needs, and runs the pipeline end to end once on one fixture — item 35,
specified here for the first time. The witness is small on purpose. Its value is that
every stage exists on `main` and is exercised in sequence by one run.

Be skeptical. The rule's interaction with the ported monotonicity theorems was argued
in conversation, not proved. A part that fails ships its obstruction with a fixture and
does not block the others, except that Part C depends on Part A.

Every declaration named below was read from `main`, from PR #129's branch, or from the
two source branches. Confirm each exists before relying on it, and correct this prompt
in the report where it is wrong.

## Maintainer rulings

Record each as a dated `DECISIONS.md` entry as the round's first commit.

**M1. Rebuttal by settlement.** A `strength` or `applicability` form whose consequent
coordinate is pinned false by settlement is *rebutted*: its row leaves the region. The
warrant said "X∧A makes Y likely"; it does not say "¬Y, so not X∧A". A linear row that
contraposes says more than the warrant did, and the market pays for the difference.

**M2. Vacuity and retirement.** A `strength` or `applicability` form whose antecedent
coordinate is pinned false is *vacuous* and leaves. A `premise` form whose sentence is
pinned false *retires its occurrence*: every row of that occurrence leaves. A refuted
premise is a case that did not arise, not an inconsistency; it must not empty the joint
region and withhold force on unrelated warrants.

**M3. No discount on applicability.** A rebuttal does not lower the applicability claim.
Undercut attacks `A_ρ(n)`; rebuttal attacks the conclusion; they stay distinct. (This
closes the gap left since the August defeat exposition, where rebuttal had no mechanism
in the statics.)

**M4. Monotonicity is traded for reopening.** Under M1–M2, settlement can widen a forced
interval. That is accepted: a rebuttal is a *reopening* in the sense of the convergence
branch (summable reopenings converge), and the global monotonicity of
`IsForcedInterval.mono` is replaced by monotonicity on the coordinates settlement pins
plus a reopening account.

**M5. [MAINTAINER: land or strike.]** The Aug 8 ruling (mechanically filed past-self
charges burn) and the Aug 9 ruling (strength selection is locked selection, with the
moral reading's objection noted) are not in `DECISIONS.md`. PR #102's report cites them
from conversation. Land them here as dated entries, or strike this item and the round
treats them as unruled.

**M6. One copy.** The seed declarations ported into `WarrantEntitlement.lean` by #129 and
the branch's `SeedStatics.lean` become one file, `SeedStatics.lean`, on `main`;
`WarrantEntitlement.lean` imports it. PR #102 and PR #103 are superseded by this
round's Part B and are not merged; the maintainer closes them with a pointer.

## Proposals from the prompt's author

Not ruled on. Adopt as agent-decided, reversible, where the mathematics supports them.

**P1. The rule as a specialization step.** `specialize` (settled values substituted into
a row) already exists. State M1–M2 as a function `settleForm : Settlement → Occurrence →
Option (List Row)` on the *form*, not on the specialized row: the form knows which
coordinate is antecedent and which consequent; the row does not. Then prove that the
rows it keeps are exactly the specialized rows that do not have the contraposing shape.

**P2. Reopening account.** Define, per settlement step, the reopening as the set of
occurrences rebutted or retired, and state the convergence branch's `hullMass_anti`
in the form: hull mass is nonincreasing between reopenings and the total reopened mass
is what `tendsto_of_summable_drops` consumes.

**P3. Names, provisional:** *rebutted*, *vacuous*, *retired* for the three outcomes of
`settleForm`; *reopening* for a settlement step that removes rows; *end-to-end witness*
for Part C's object.

## Part A — the rule, and what it changes

**A1.** `settleForm` per P1, on `Form` and the typed `Occurrence` of #129. Decidable.

**A2. The orphan cannot form.** On #129's `Fixture` (`X, X∧A, X∧A∧Y, Y`; `c_P, c_A,
c_S` in `(0,1)`; applicability port defeated at `n₀`; `Y` refuted at `n_E`): under
`settleForm`, the strength row leaves at `n_E`, the region after `n_E` has a slack world
(`X` true, `A` open), and `liability_of_odds` applies with the same `3ρ`. State this as
`Fixture.liability_rebutted`. Then show `harmonic_buyer_run` (`src/fixture.py`) has
nothing to buy against: the enforcer holds no row in `X∧A` after `n_E`. Exact rationals;
Lean for the liability, the fixture test for the buyer.

**A3. The premise guard retired.** Under M2, refuting `X` retires the occurrence and
the region is the one the *other* warrants force. Show on a two-warrant fixture (the
second warrant on disjoint sentences) that refuting the first's premise leaves the
second enforced. Under #129's rule it emptied the region and withheld both — exhibit
that as the countermodel.

**A4. Monotonicity restated.** `IsForcedInterval.mono` and `forcedInterval_mono` (branch
§6) are false under M1–M2 in their current form. Prove the replacements: (a) for a
settlement step that pins a coordinate and rebuts or retires nothing, the forced
interval on every coordinate is nested as before; (b) for a reopening step, the interval
on a coordinate can widen by at most the width the removed rows had forced, stated
exactly. Record the old statements as superseded in the registry if they were
registered (they were not, as of #129; confirm).

**A5. Re-verify #129.** Every theorem in `WarrantEntitlement.lean` whose hypotheses
mention a schedule or region: state whether it is unchanged, strengthened, or needs
restating under `settleForm`. `netWorth_ge_neg_odds` should be unchanged (it is about
rows, not about where they came from); `Fixture.disagree_region_empty` becomes false and
is replaced by A2; `orphan_region_nonempty`/`orphan_no_slack` become the countermodel
to the *old* rule and are kept as such.

## Part B — the seed and convergence landing

Sources: `round/2026-09-16-seed-statics` (`SeedStatics.lean` and
`projects/normativity/seed/`) and `round/2026-09-17-convergence-measure`
(`ConvergenceMeasure.lean`). Both are 96+ commits behind `main`; port, do not merge.

**B1. One `SeedStatics.lean` on `main`** (M6): the declarations #129 ported, moved out
of `WarrantEntitlement.lean`, plus from the branch's §6 the elimination machinery and
`forcedInterval`, `forcedInterval_spec`, `forcedInterval_bounds` (the `mono` per A4);
from §5 `SureLoss`, `sureLoss_of_cert`, `FarkasCert.support_sound`,
`MinimalInfeasible`; `Pins`, `Refuted`, `leverage`; from §8 `seed_independence_strict`
with its `c3_refuted` countermodel and `sandwichSeed_humble`; from §10
`eventually_const_of_finite`, `eventually_const_of_monotone`,
`tendsto_of_summable_drops`. Not ported: §7 confinement, §9 transport (its negated-form
drop is a known defect — file it, do not fix it here), §11 non-dogmatism. Say what was
left and why in one table.

**B2. The seed subproject.** `projects/normativity/seed/` as the branch lays it out,
with the branch round's documents (`SEED.md`, `STATICS.md`, `CRITERION.md`,
`STABILIZATION.md`, `COUNTERMODELS.md`, `FIXTURES.md`, `REPORT.md`) landed under
`projects/normativity/seed/rounds/2026-09-16-seed-statics/` verbatim with an `ORIGIN.md`
saying they are a branch round landed by this one. Same for the convergence round under
`projects/normativity/seed/rounds/2026-09-17-convergence-measure/`. Confirm
`checkers.workspace_state --check` sees the subproject.

**B3. The interval-data layer** from `ConvergenceMeasure.lean` §1–§3: `IntervalData`,
`Valid`, the hull/common/discord definitions, `hullMass`, `overlapMass`,
`discordMass`, their bounds, `Nested`, `hullMass_anti`, `discord_persists`,
`discord_iff_pair`, `forcedRegionR_anti_warrants`. The single-reasoner case
(`ι = Unit`) is what Part C reports; the two-reasoner results land because they are
cheap and the convergence round's items need them.

**B4. Items from the two branch rounds.** PR #102 filed items as 93–94 and #103 as 95–96;
those numbers are taken on `main`. Re-file them from 117 with their content unchanged
and a line saying which branch item each was. (The branch's item 93 collides with
#101's item 93; the branch's is the one re-filed.)

## Part C — the end-to-end witness (item 35)

One run, one fixture, every stage. The fixture is #129's four-sentence fragment
extended by one sentence `Z` and a second warrant, so that there is something left
standing after the first is rebutted.

**C1. Seed.** A `Seed` with one substantive item (the first warrant, strength `< 1`),
one structural item (coherence of `X∧A ≤ X`, strength 1), and the constitutive layer
empty. `HumbleItems` holds.

**C2. Entry.** Both warrants entered as `Occurrence`s with provenance; `VerdictCert`s
issued for the bound on `Y` and on `Z`; `Licensed` holds for both at entry
(`decideLicensed_iff`).

**C3. Compile and enforce.** `forcedInterval` computed by elimination (not by hand) for
`Y` and `Z` at entry; the force presentation built by `toForceRow`; `liability_of_odds`
instantiated with the fixture's `ρ`.

**C4. Settlement.** `X` settles true at `n₁`. Intervals recomputed; nested per A4(a).

**C5. Undercut.** The first warrant's applicability port defeated at `n₀`
(`defeat_widens`); the certificate citing it fails `Supported`
(`admissible_not_supported`); a fresh certificate on the second warrant still holds.

**C6. Rebuttal.** `Y` refuted at `n_E`. `settleForm` removes the strength row; the
reopening is recorded; the interval on `X∧A` widens by exactly what A4(b) allows; the
second warrant's interval on `Z` is unchanged; `liability_rebutted` holds; no orphan.

**C7. Where it ends.** After `n_E` nothing further settles. Show the interval data is
eventually constant (`eventually_const_of_finite` on the finite docket), report the
final `forcedInterval` on `Z`, the hull mass of the run as a sequence with its one
reopening, and the `trace` of the run (`MarketRun → Record`) with `docket_mediated`
holding at every step.

**C8. The witness statement.** One Lean theorem, `EndToEnd.witness`, whose hypotheses
are the fixture's declared quantities and whose conclusion conjoins: the seed is humble;
both entries licensed; `IsLogicalInductor` for the augmented market under the odds
bankroll (via `warrant_normative_inductor`, keeping `computableMarket` and the uptake
certificate as hypotheses exactly as it does); the interval on `Z` after `n_E` equals
the value elimination computes; the run's record is neither injective nor constant.
`#print axioms`. This is not registered; it is the object item 35 asked for, and the
report says what it does and does not show.

## What this round is told not to do

- No change to the force layer, the Normative Inductor architecture, or legitimacy.
- Do not port confinement or transport; do not attempt two-reasoner convergence beyond
  what B3 lands.
- Do not define the baseline `B` (item 110); do not touch the deference line's Lean.
- Do not re-derive #129's bankroll theorem; cite it.
- Do not cite any ruling not in `DECISIONS.md` after the round's first commit; M5 is the
  only chat-sourced material here and it is marked.
- Register nothing from Part C. Register from Parts A–B only what is `lean-proved` and
  listed in the output section.

## Lean / formalization target

`SeedStatics.lean` (one copy, M6); `WarrantEntitlement.lean` importing it, with A1–A5;
`ConvergenceMeasure.lean` (B3); `EndToEndWitness.lean` (Part C). Sorry-free, three
allowed axioms, nonvacuity witnesses for every structure, `#print axioms` on every
declaration. The report includes `lake build` output, the axiom audit line, and
`tests/run.py` output — #129's report omitted all three and the registry carried five
`lean-proved` entries on its word; do not repeat that.

## Output

In the round directory: `REPORT.md` with a verification section; `REBUTTAL.md` (Part
A); `LANDING.md` (Part B, with the ported/not-ported table and the item renumbering
map); `WITNESS.md` (Part C, the run as a dated table: date, event, intervals on `Y` and
`Z`, enforcer position, reopening, licence status of each certificate); `src/` with the
fixture and the run; `PROVENANCE.md`. A wiki page `wiki/Seed-Theory.md` (the branch
rounds never got one), and the `Normativity.md` and `Theorem-Spine.md` entries it
needs.

Registration candidates, `lean-proved` only, against the items named:
`settleForm` soundness and `Fixture.liability_rebutted` (item 113);
`forcedInterval_spec`, `forcedInterval_bounds` (item 39's geometric half);
`seed_independence_strict` and `eventually_const_of_finite` (the re-filed seed items);
`hullMass_anti`, `discord_persists`, `discord_iff_pair` (the re-filed convergence
items). List the rest, do not register.

## Final questions the report must answer

1. Does `netWorth_ge_neg_odds` survive `settleForm` unchanged? If not, exactly what
   changed.
2. By how much can one reopening widen a forced interval, and is that bound attained
   on the fixture?
3. Did the end-to-end run reach `n_E` with every stage's statement holding, or where
   did it stop?
4. What did the two branches contain that this round did not land, and which of it
   does item 35's next instance need?
5. What is reserved to the maintainer.
