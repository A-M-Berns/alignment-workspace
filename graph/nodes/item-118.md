---
id: item-118
kind: leaf
leaf_kind: task
action: "Execute item 118 per its deliverable shape and acceptance check: Rational attainment and certificate completeness for the computed forced interval."
who: agent
item: "118"
title: "Rational attainment and certificate completeness for the computed forced interval"
section: "Deference line — second wave"
maintainer_order: 111
difficulty: "open"
heading_notes: " — *narrowed 2026-10-22: completeness is also what decides whether an adapter's `Excludes`/`Margins` certificates exist whenever the region excludes or marks (`WarrantInductor.Problem`)* — *bears on it 2026-11-08: both theorems are proved and registered — every valid bound on a forced region has a bound certificate over the forced bundle's allowed rows (`IncompatibilitySemantics.lowerBound_certified`, `upperBound_certified`, registered `seed.bound-certified`), and the computed interval inhabits `IsForcedInterval` at rational points (`forcedInterval_isForcedInterval`, registered `seed.forced-interval-rational`), by the rational alternative read in from the pinned `EconCSLib` (`RowAlternative.alternative`, `entails_iff`, `exists_rat_of_real`); incompatibility entailment coincides with certificate entailment (`rows.incompatibility-entailment`). Not derived: the existence of an adapter's `Excludes`/`Margins` certificates, noted on item 79. The item's status is the maintainer's word*"
project: normativity.seed
dispatchable: true
item_status: open
deliverable: "`IsForcedInterval S W st F φ lo hi` inhabited by `forcedInterval`, and `∀ c, LowerBound … c → ∃ cert, −cert.value ≥ c` (or the statement that fails, with its witness)."
acceptance: "the Lean audits clean."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}
  - {kind: decision, ref: 2026-11-08--content-is-role-among-rows-expresses-demands-no-more}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 189 words"
version: 1
---
## Statement
A solution to item 118 ships the two theorems.

## Source
ATTENTION.md, item 118 (Rational attainment and certificate completeness for the computed forced interval); its context: `STATICS.md` §§2, 5 of the seed-statics round; `FourierMotzkin.lean`'s header on why satisfaction lives in `ℝ`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into ATTENTION.md by checkers/attention_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
*Re-filed 2026-10-21 by the rebuttal-and-end-to-end round from branch `round/2026-09-16-seed-statics`, where it was item 94; content unchanged; the branch round is landed under `projects/normativity/seed/rounds/2026-09-16-seed-statics/`.*

`SeedStatics.forcedInterval_spec` proves the computed endpoints valid and attained at
*real* points, because `FourierMotzkin` states satisfaction over `ℝ`; attainment at a
rational point — the fact that a rational system feasible over `ℝ` is feasible over `ℚ`
— is not in the repository, so the rational predicate `IsForcedInterval` is not
inhabited by the computed pair.  Separately, `BoundCert.sound` gives soundness of
endpoint certificates and nothing gives tightness (LP duality).  Either transfer the
elimination's completeness direction to `ℚ` or give the vertex argument, and prove that
every valid bound is certified.  This is the duality half of item 79's completeness.

*Deliverable shape:* `IsForcedInterval S W st F φ lo hi` inhabited by
`forcedInterval`, and `∀ c, LowerBound … c → ∃ cert, −cert.value ≥ c` (or the
statement that fails, with its witness).
*Acceptance check:* the Lean audits clean.

*Context:* `STATICS.md` §§2, 5 of the seed-statics round; `FourierMotzkin.lean`'s
header on why satisfaction lives in `ℝ`.
*Consumed by:* item 79; any registration of `forcedInterval_spec`.
*A solution ships:* the two theorems.
