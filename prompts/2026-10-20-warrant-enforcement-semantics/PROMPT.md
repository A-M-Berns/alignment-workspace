# Prompt — what entitles a market to enforce a warrant (2026-10-20)

You are working in the `alignment-workspace` repository, on `main` after the merge of
PR #128. Do not stack this round on an unmerged branch. One unmerged branch is a
*source* for this round (Part 0); it is not a base.

The round directory is `projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/`.
The prompt goes verbatim in `prompts/2026-10-20-warrant-enforcement-semantics/PROMPT.md`.
New priority items start at 112.

## What this round is for

Item 39 asks whether normative statics produce a credal constraint or only a price
demand, and says in its own text that producing the region is half the item: the source
must also supply a certificate that cumulative enforcement liability over the assessed
worlds is bounded. The geometric half now exists (a warrant compiles to rows; rows force a
region). The liability half has never been attempted for a genuinely normative row. This
round attempts it, as a fork over what the enforced security settles against, and reports
which readings of "a reason" the market can afford. The deliverable is a finding, not a
design.

Be skeptical. The three semantics below and the licence chain were worked out in
conversation and checked on no example. Treat each as a conjecture. A part that fails
ships its exact obstruction with a fixture.

Every declaration named below was read from `main` at #128 or from the named branch.
Confirm each exists before relying on it, and correct this prompt in the report where it
is wrong.

## Maintainer rulings

Record each as a dated `DECISIONS.md` entry as the round's first commit. Where the
maintainer has struck one, omit it.

**M1. [MAINTAINER: confirm, amend, or strike.]** Normative content enters the market in
two forms: obligations as credal constraints on priced sentences; values as securities
traded directly. (Stated in conversation on 2026-08-23; not in `DECISIONS.md`. If struck,
Part B's semantics (iii) is the only one that survives as a reading of obligations, and
the round says so.)

**M2.** The question of what a warrant's security settles against is not ruled. This
round runs it as a fork (Part B) and reports; the maintainer rules on the result.

**M3.** Nothing in this round redefines legitimacy, the Normative Inductor architecture,
or the force layer. Those are consumed, not revised.

## Proposals from the prompt's author

Not ruled on. Where the mathematics supports one, adopt it as agent-decided, reversible,
naming the rejected alternative.

**P1. Licence is three-level, with no converses.** For a verdict `v`, a certificate `c`,
grounds `G` and a record `R`:

- `Admissible(v, G)`: the region compiled from `G` contains `v`;
- `Supported(v, c, G)`: `c` certifies `v` from admitted grounds — its positive
  multipliers name occurrences in `G`;
- `Licensed(v, c, R)`: every occurrence `c` cites is live in `R` at the step, and the
  event that issued and selected `c` is itself an authorized record event.

Conjecture: `Licensed ⇒ Supported ⇒ Admissible`, and both converses fail. The compiler
decides the first two; the record decides the third. This is the shape proposed for item
56; this round proves the chain and the two countermodels and files the rest of 56
against it.

**P2. The conclusion of enforcement is defect, not membership.** What affordable
enforcement delivers is a bounded public defect `d_s = dist_∞(b_s, K_s)` at a declared
tolerance, never `P_t ∈ K_t`. State every result in that form.

**P3. The record of a market run is an additional object.** Price history is not reason
history. Part C defines the minimum such object and shows it is neither over-rich nor
under-rich in the sense of `ReasonMediatedAuthorship`.

**P4. Names, provisional:** *settlement semantics* for the fork's parameter; *bankroll
schedule* for the constructed `B`; *entitlement* for "the row may be enforced at bounded
liability".

## Part 0 — port the seed statics (bounded)

Branch `round/2026-09-16-seed-statics` holds
`lean/Workspace/Normativity/Contrib/SeedStatics.lean`, 96 commits behind `main`. Port
onto this round's branch the declarations this round consumes — `Form`, `Form.row`,
`Settlement`, `SubItem`, `StrItem`, `Seed`, `DocketState`, `forcedBundle`,
`forcedRegion`, `IsForcedInterval`, `BoundCert`, `defeat_widens` — against current `main`
(`Bundle.Region` and `FarkasCert` in `NormativeInductorComposition.lean` are the targets
they compile to). Do not merge the branch; do not port the convergence branch; do not
port the fixtures or the criterion material. If the port does not build within a bounded
effort, port only `Form`/`Form.row`/`BoundCert` and file the rest as an item. Say in the
report what was ported and what was left.

## Part A — the warrant as a provenance-carrying market object

**A1. The typed warrant.** A warrant occurrence is a `Form` together with: an occurrence
identity; the applicability claim it cites (an occurrence, or a settled sentence); a
source (a party or a settlement event); and a defeat condition (which occurrences, if
live, undercut it). The three forms stay as on the branch: `premise X c`,
`applicability X XA c`, `strength XA XAY c`, each compiling by `Form.row`.

**A2. The chain.** Lean. State `Admissible`, `Supported`, `Licensed` per P1, with
`Supported` carried by a `BoundCert` whose positive-multiplier rows are indexed by
occurrences. Prove `Licensed → Supported → Admissible`.

**A3. Countermodel to `Admissible → Supported`, and to transport.** Two occurrences `r₁`,
`r₂`, distinct, each independently supporting the same bound on `φ`. A certificate citing
`r₁`. Defeat `r₁`; `r₂` stays live. Show: the forced region is unchanged; the certificate
no longer satisfies `Supported`; a fresh certificate citing `r₂` does. Exact fixture, and
Lean if cheap. This is the countermodel to any licence that depends only on the region.

**A4. Countermodel to `Supported → Licensed`.** A region `[a, b]` with `a < b` on `φ`,
two licensed verdicts inside it, and a selection by a non-principal party that lands on
one. Admissible and supported; whether it is licensed is a transparency question on the
record. Do not re-prove `tiebreak_transparency` (`GateIsLegitimacy`); cite it and show
the fixture is an instance.

## Part B — the fork: what the security settles against

The hypothesis to discharge is `liability` in `conditional_normative_inductor`
(`NormativeInductionInterface.lean`): for every `n` and every live world `v`,
`−B ≤ (realizedEnforcer L enforcer).netWorth (history L enforcer) v n`. The enforcer is
the force layer's compiled position (`TRADERIZED_FORCE_INTERFACE.md`); the assessment
process is `Assessment` (`AssessmentProcess.lean`).

**The fixture, used throughout B.** A fragment of four sentences `X, X∧A, X∧A∧Y, Y`; one
warrant occurrence with strengths `c_P, c_A, c_S` all strictly between 0 and 1; one
defeater of its applicability claim that arrives at a known date `n₀`; a deductive
process that settles `X` true at some `n₁`. Exact rationals.

For each of the three settlement semantics, either **construct** a bankroll schedule `B`
(as a function of the fixture's declared quantities) under which the `liability`
hypothesis holds, or **exhibit** an efficiently computable trader that drives the
enforcer's net worth below every bound. Both outcomes are results.

**B(i) — deductive settlement.** The rows are admissible in every plausible world (the
hypothesis of `deductive_end_to_end`, `DeductiveEffective.lean`). Expected: zero
liability, and the warrant was a logical fact wearing a strength. Confirm, and state
exactly which hypothesis of `deductive_end_to_end` a genuine warrant fails — that is the
boundary of the deductive case.

**B(ii) — evaluation settlement.** The sentence `Y` is settled by a later legitimate
evaluation: `Y`'s payoff in a live world is that world's evaluation at a declared date,
and the evaluation is a typed input of the fixture. Liability is then the enforcer's
exposure on the event that the evaluation disagrees with the warrant. Construct `B` as a
function of the declared disagreement mass if one exists; show it is unbounded if the
evaluation is unconstrained by the warrant. This is the reading under which enforcement
"assumes the normative conclusion" — say precisely whether it does, i.e. whether the
only `B` that works presupposes the evaluation satisfies the row.

**B(iii) — pegged, no settlement.** `Y` has no payoff event; the row is held by the
enforcer against its own account and the enforcer is settled on nothing. Determine which
of the criterion's clauses survive: is the augmented market still a logical inductor
relative to `Assessment` when one trader's securities never settle? If yes, with what
`B`; if no, which clause fails and on which trader.

**B(iv) — the defeater.** For whichever semantics admit a `B`, show what happens at `n₀`
when the applicability claim is undercut: the row leaves the region (`defeat_widens`), the
enforcer's position unwinds, and the liability incurred between the warrant's entry and
`n₀` is either recovered, absorbed by `B`, or not — state which, exactly.

**B(v) — answer item 39 in its own terms.** Strong (a semantic credal constraint `C_t`
with live worlds following) or weak (a price demand `K_t` only), per semantics. If weak
for all three, exhibit the two credal sets with the same projection and different live
worlds that the item asks for.

## Part C — the record of a market run (bounded)

Define `trace : MarketRun → Record` where the record carries, per date: warrant
occurrences entered (with A1's provenance), certificates issued and selected, docket
transitions (entry, defeat, withdrawal), and the enforcer's position. Prices are *not*
in the record. Prove on the Part B fixture that the record is neither injective in the
market run (the over-rich end, `reasonMediated_of_injOn`) nor constant (the under-rich
end, `reasonMediated_const_iff`), and that `Licensed` from A2 is decidable from the
record alone. Stop there: do not attempt authorship, transparency, or the inductor-as-
principal question; file what Part C makes visible as items.

## What this round is told not to do

- No architecture pass over legitimacy or the Normative Inductor.
- Do not define the baseline `B` of the thin specification (item 110) — a different `B`.
- Do not merge or port the convergence branch.
- Do not touch the deference line's Lean except to cite it.
- Do not cite any ruling not in `DECISIONS.md`; M1 is the only chat-sourced position
  here and it is marked for the maintainer.
- Do not register any Part B result above `test-supported` unless the construction is
  in Lean against `conditional_normative_inductor`'s actual signature.

## Lean / formalization target

`lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean` (name provisional): the
ported seed declarations, A1–A2, A3 if cheap, the B constructions that go through, and
the Part C record with its two non-vacuity lemmas. Sorry-free, three allowed axioms,
nonvacuity witnesses for every structure. `#print axioms` on every declaration.

## Output

In the round directory: `REPORT.md`; `LICENCE_CHAIN.md` (Part A); `SETTLEMENT_FORK.md`
(Part B, one section per semantics, with the fixture's numbers); `RECORD.md` (Part C);
`COUNTERMODELS.md`; `src/` with the exact-rational fixture and the trader-exploitation
search for any semantics that failed; `PROVENANCE.md`. Items filed from 112. Candidate
registrations listed, not registered, except Lean-proved chain lemmas against item 56.

## Final questions the report must answer

1. Under which settlement semantics does a bankroll schedule exist for one defeasible
   warrant, and as a function of what?
2. Under evaluation settlement, does the only working `B` presuppose the evaluation
   satisfies the row? Yes or no, with the construction.
3. Is item 39 strong or weak, per semantics?
4. What does `Licensed` need from the record that the region cannot supply? State it as
   the content of item 56.
5. Which of M1's two forms (constraint, security) does each semantics realize, and is
   there a semantics under which "obligation to respond" is the only coherent reading?
6. What is reserved to the maintainer.
