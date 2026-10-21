# Report

Verdict: `README.md`.  Lean: `lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean`,
23 audited declarations on `[propext, Classical.choice, Quot.sound]`, importing
`SeedStatics.lean` unchanged.  Fixtures: 20 tests, `python3 tests/run.py`, loading the
seed round's `src/` by path without modifying it.  Nothing registered; every name
provisional.

## What was shown

| objective | result | where |
|---|---|---|
| 1 measure | profile on interval data with declared `Φ` and positive weights; `Ovl ≤ Hull ≤ 1`; `Disc = 0 ↔` no declared discord; `Disc = 0 → Ovl > 0` refuted; discord certificate by merging two bound certificates; pinned fragment lifted to `n` reasoners; exact two-reasoner relation to seed leverage | `MEASURE.md`; Lean §§1, 5, 7 |
| 2 gameability | four attacks succeed against a naive reading and are blocked (dilution, splitting, hiding, weight capture); hidden discord is not blocked | `GAMEABILITY.md`; Lean §2 |
| 3 dynamics | H1 proved on interval data and connected to regions; private narrowing creates discord and sharing cannot dissolve it; H2 proved; H3 in corrected form; five pressure tests | `DYNAMICS.md`; Lean §§3, 4, 6 |
| 4 many | Helly: discord is pairwise; merged feasibility is not; hidden two- and three-way discord | `MANY.md` |
| 5, 6 | overlapping consensus stated; LI comparison by declaration | `CONSENSUS.md`, `LI_COMPARISON.md` |
| fixtures | moral: aggregation disagreement is discord naming the two items; population: private learning creates discord; legal: lock is certified discord, hull eventually constant | `FIXTURES.md` |

## The twelve questions

1. **Well-defined, Lean-stated; which attacks succeeded?**  Yes.  Against the naive
   reading all of dilution, splitting (on `Disc`), hiding and weight capture succeed;
   blocked respectively by `blockedHull_insert_pinned`, pull-back through `τ`, the
   product order on `(Hull, Disc)`, and `Weights` with `discordMass_eq_zero_iff`.
   Unblockable: hidden discord (`MANY.md` §2).
2. **H1?**  Holds: `hullMass_anti` under every nesting, `hullMass_mono` under
   reopening, with the region inclusions `forcedRegionR_anti_warrants`,
   `forcedRegionR_anti_defeat` and `forcedInterval_nest_of_subset`.  Private narrowing
   raises `Disc` (`private_learning`: `0 → 1`).  The mechanism is exhibited both ways
   with a correction: discord is removed by defeat, not by sharing — sharing refutes
   the receiver (`discord_persists`).
3. **H2?**  Holds, `hullMass_tendsto_of_summable`.  `Hull_∞`: moral `7/12` at the last
   step against reference `43/60`; legal `13/20`; consensus `1/3`; the oscillation
   witness has no limit.
4. **H3?**  Holds under exhaustive sharing read as equal live sets, with a finite
   discovery class: `Disc_t` eventually constant, every persistent discord certified
   between substantive items.  The dispatch's limit is corrected to one direction:
   `Δ_∞ ≠ ∅` implies merged infeasibility, not conversely.
5. **Convergence without reason convergence?**  Exhibited (`consensus`: disjoint dockets,
   `(1/3, 1/3, 0)`); one one-sided defeater takes the hull to `1`.
6. **Lock?**  Does not break convergence; sits as width against a shared presumption
   (`(3/20, 1/20, 0)`) and as certified discord against an opposing item, the certificate
   naming the lock (`legal_two`, `lock.opposed`).
7. **`n` reasoners?**  Pairwise suffices for coordinate discord (`discord_iff_pair`,
   Helly); it does not suffice for merged feasibility (three reasoners pairwise
   compatible, jointly infeasible, no coordinate discord).
8. **Hull mass and seed leverage?**  `Hull = (1 − Lev¹_w) + (1 − Lev²_w) − Ovl + Gap`,
   exactly, for two reasoners; for more, no function of the leverages (`MEASURE.md` §5).
9. **Moral fixture?**  Discord, gap `3/5` on `r(a,c)`, certificate items exactly
   `{prioritarian ¬r(a,c), sum r(a,c)}`; impartiality carries the discord to `r(b,c)`.
10. **LI comparison?**  `lic_price_convergesTo`, `lic_limitCoherence`,
    `lic_limitingBelief_theorem`, `lic_disprovable_tendsto_zero`, `lic_limit_pos`,
    `lic_limit_lt_one`: agreement on what settles, nothing on what does not.  The one
    sentence is at the end of `LI_COMPARISON.md`.
11. **Names.**  Provisional: hull mass, overlap mass, discord set/mass, discord
    certificate, convergence profile, shared/private narrowing, exhaustive sharing,
    discord graph, overlapping consensus, hidden discord, blocked hull, nesting.  Reused
    unchanged: everything in `SeedStatics.lean` and the seed round's `src/`.  Corrected
    twin: `transport_seed_keeping_forms` — the seed round's `transport_seed` rebuilds
    every form as a plain `Form` and drops the negated forms its own fixtures use.
12. **Wanted and could not.**  A Lean H3: the exhaustive-sharing condition is stated on
    live row sets in prose and the eventual constancy composed from the seed round's
    `eventually_const_of_finite`, not proved as one theorem (item 96).  Existence of the
    endpoint certificates (item 94).  A region-level measure that sees hidden discord
    (item 95).

## Deviations and prompt corrections

- The branch is off `round/2026-09-16-seed-statics` (PR #102, not on `main`).
- `Disc = 0 → Ovl > 0` is refuted, not proved.
- "Dissolved by sharing" is refuted; the pressure test's second half is "removed by
  defeat or refutation".
- H3's limit is one-directional; "the set of sentences on which the merged bundle is
  infeasible" is not a set of sentences.
- `Disc = 0 ↔ merged bundle feasible on Φ` holds only right-to-left.
- The moral fixture's welfare levels are settled by activating the specialized valence
  rows rather than by carrying antecedent coordinates (equivalent on intervals; §1 of
  `FIXTURES.md` says why); four outcomes so that the chain changes something.
- New priority numbers assumed: 95 and 96.

## What is not established

- LP duality: that the two endpoint certificates exist whenever `φ ∈ Δ`; the merge is
  proved, the existence is item 94, and the fixtures compute them.
- H3 as a single Lean theorem on the docket types; the exchange protocol that equalizes
  live sets on `DefeatTrace` (item 96).
- Interval invariance of the disjunction coordinate under fresh refinements (the
  splitting block), computed on one fixture and argued.
- The inclusion–exclusion identity, computed and argued, not Lean-stated.
- Any block for hidden discord; any ranking of reference closed layers.
- Anything about an inductor's prices reaching the intervals.

## Proposed priority changes

- **New item 95**: hidden discord — a region-level component of the profile.
- **New item 96**: exhaustive sharing on trace-constitutive dockets — the exchange
  protocol that equalizes live sets, and H3 in Lean against it.

## Outstanding maintainer actions

1. None reserved.  Two agent-decided entries are in `DECISIONS.md` (the profile as the
   position on convergence, with sharing not dissolving discord; exhaustive sharing as
   equal live sets).  Reverse by re-ruling.
2. Registration at merge: none proposed; candidates `discord_persists`,
   `hullMass_anti`, `discord_certificate`, `hullMass_tendsto_of_summable`,
   `discord_iff_pair`.
3. The seed round's `transport_seed` drops negated forms; it is not edited here
   (the seed round's own fixtures never transport them).  Decide whether to fix it
   there at merge of PR #102.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-17-convergence-measure/PROMPT.md`.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-17.
