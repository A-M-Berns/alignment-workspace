# Report

Verdict: `README.md`.  Lean: `lean/Workspace/Normativity/Contrib/SeedStatics.lean`, 42
audited declarations on `[propext, Classical.choice, Quot.sound]`.  Fixtures: 28 tests,
`python3 tests/run.py`.  Nothing registered; every name provisional.

## What was shown

| objective | result | where |
|---|---|---|
| 1 seed | typed object, three layers, two `rfl`-separate withdrawal channels; item-level humility decidable; level neutrality as the checkable half of non-dogmatism; transport exact | `SEED.md`; Lean §§1–2, 9, 11 |
| 2 statics | forced region = `Bundle.Region`, decided by `checkCompiled`; forced interval computed by the existing elimination, correct and attained; sure loss by `FarkasCert`, support infeasible; monotone under settlement, widened by defeat | `STATICS.md`; Lean §§3–6 |
| 3 confinement | C1 holds as a hull bound, false as a union length; common region = merged seed; C2 is not a theorem of the landed calculus (trace discipline, no extension); C3 refuted under item humility, proved under strict humility | `CONFINEMENT.md`; Lean §§7–8 |
| 4 stabilization | S1 for finite discovery classes; oscillation witness; summable reopenings converge (S2); hysteresis and its canonical-rule repair | `STABILIZATION.md`; Lean §10 |
| 5 criterion | fused candidate stated; obstruction at the adapter's lack of price authority and the enforcer's absence from every criterion; construction-relative | `CRITERION.md` |
| fixtures | moral: forced at strength, open axis, no additivity; population: certificate and minimal subset; legal: validity `[0, 1/5]`, amendment ≠ defeat, open residual power | `FIXTURES.md` |

## The fourteen questions

1. **Well-typed, checkable humility, disguise caught?**  Yes; yes for item-level
   humility (decidable) and level neutrality (two LPs per coordinate, a bound certificate
   as witness); the level disguise `P(φ) = P(¬φ)` is caught (`disguise_caught`).  A
   relational disguise is caught only against a declared symmetry, and the declaration
   itself is not checkable (`SEED.md` §3).
2. **Computable on the existing compiler; monotone under settlement?**  Yes and yes:
   `forcedRegion_iff_check`, `forcedInterval_spec` (elimination, no LP hypothesis),
   `forcedRegion_anti`, `forcedInterval_mono`.
3. **C1?**  Holds and is trivial *as a hull bound* (`confinement`).  The prompt's
   `|I¹ ∪ I²|` read as a length is false on disjoint intervals
   (`measure_form_refuted`); disjointness is joint infeasibility on `φ`.
4. **Grounded extension?**  No.  The landed calculus fixes the live docket per trace and
   conserves load; admissibility needs available grounds, not vindicated ones, so
   exhaustive exchange leaves the live set trace-dependent.  C2 becomes: the grounded
   extension is a *conformance hypothesis* on a trace, definable on top (computed and
   unique in the fixture), not a consequence of the calculus (`CONFINEMENT.md` §2).
5. **C3 under humility?**  False: `{P(φ) ≥ 1/2, P(¬φ) ≥ 1/2}` pins `1/2` (`c3_refuted`).
   Tests 1, 2, 3 break it (dogmatic item; hysteresis; narrowing transport); 4 and 5 do
   not.  C3′ holds under strict humility (`seed_independence_strict`): a humble seed
   narrows or breaks and never pins.
6. **Hysteresis?**  Occurs (`[9/10, 19/20]` versus `[3/10, 1/2]`).  Reopening alone does
   not kill it (both outcomes are maximal); reopening under a canonical joint rule does.
   For the burn ruling: a re-selection must not count as a mechanically filed past-self
   charge — filed below, not amended.
7. **Stabilization?**  Finite `𝒟`: eventually constant (`eventually_const_of_finite`).
   Infinite: fresh warrant and undercut alternating, no limit.  Restored by summable
   reopenings (`tendsto_of_summable_drops`); finite reopenings and finite *row* sets
   also suffice; bounded depth and finite chains do not.
8. **Moral fixture?**  Forced: `r(e,·) ∈ [4/5, 1]`, `r(a,b) = r(b,a) ∈ [1/2, 1]`.  Open:
   the seven cross pairs at `[0, 1]`, `r(a,c)` the comparability axis.  Infeasible: the
   population cluster, certificate with five unit multipliers, minimal subset of four.
   Distinguished by certificate type (`FIXTURES.md` §3).
9. **Legal fixture?**  Instantiated: validity `[0, 1/5]`, amendment pins `V = 1` with
   the right untouched, defeat widens instead, `V₂` open.  Could not express: standing
   (declared, unread), court hierarchy (settlement cannot retract), precedent (no lock on
   a selection) — filed as item 93.
10. **Fused criterion?**  Stated exactly; construction-relative.  The obstruction: the
    adapter has no price authority and the enforcer is outside every criterion.
11. **Item 79?**  Supplied: the class (finitely many rational rows, into which every
    layer and the settlement compile) and computed completeness of intervals.  Remains:
    the map from `Protocol.Evidence` types to rows, LP duality for certificates, joint
    feasibility, affordability.  Not closed.
12. **Deference coincidences?**  `S_con` / protected concern; `𝒟` / reason-supply
    channel with stabilization / liveness residual — both as conjectures
    (`ALIGNMENT_READING.md`).
13. **Names.**  Provisional: seed, substantive/structural/constitutive layer, transport
    rule, humility (item-level, level-neutral, strict), forced region, forced interval,
    seed leverage, confinement, seed-independence, discovery class, reopening,
    grounded-conformant trace, level neutrality, symmetry generation, canonical joint
    selection, lock (a sealed selection).  Reused with their meanings: row, bundle,
    region, `checkCompiled`, `FarkasCert`, allowed row, settlement, docket, port,
    surface-change occurrence, answer/dispose/settle, grounded/available, standing,
    protected concern, leverage (the wiki's, kept distinct).
14. **Wanted and could not.**  Rational attainment of the computed endpoints: the
    elimination file states satisfaction over `ℝ` and the ℚ/ℝ transfer is not in the
    repository (`STATICS.md` §2).  A necessary-and-sufficient condition on `𝒟` for
    convergence: convergence is a property of the endpoint sequences, not of `𝒟`
    (`STABILIZATION.md` §3).  A criterion-level non-dogmatism check for symmetry
    declarations: it is where the content sits.

## Deviations and prompt corrections

- `DECISIONS.md` on `main` contains no 2026-08-08 entries (past-self charges burn; seam
  ordering) and no 2026-08-09 entry on strength selection; nothing in the repository
  matched either.  The round uses the rulings as the prompt states them and cites the
  prompt, not the ledger (standard 7).
- C1 is proved in the hull form; the union-length form the prompt wrote is refuted
  rather than proved.
- C3 is refuted under the prompt's humility and proved under a hypothesis (strictness)
  the prompt did not state.
- C2 is not proved against a grounded notion because the landed calculus has none;
  the report states what it determines instead.
- The forced interval is stated over the whole fragment with pinned coordinates, not
  over the unsettled coordinates alone; the two agree up to projection.
- The seed's warrant set `W` is unfiltered by the docket (it is the *live* set); the
  stabilization fixtures therefore place raised warrants in the substantive layer.
- The moral fixture's warrant triples are canonicalized: with premise and applicability
  settled true, the strength row is `P(Y) ≥ c` directly.
- The round directory sits under `projects/normativity/seed/` as asked, indexed under
  project id `normativity`; no `normativity.seed` entry was added to
  `state/projects.json`.
- New priority numbers assumed: 93 and 94, after PR #101's item 92.

## What is not established

- Attainment of the computed endpoints at a rational point; LP duality (that the best
  bound certificate equals the endpoint).
- Any statement about the enforcer reaching the forced region; the round runs nothing.
- The grounded extension as anything but a definable hypothesis; uniqueness is computed
  on the fixture, not proved in Lean.
- That the non-dogmatism criterion catches a contestable symmetry declaration; it does
  not, and this is recorded.
- Which surface-change occurrences are licensed, and who declares a refinement map.
- The conjectured identity of discovery class and reason-supply channel.
- That a non-affine requirement lies outside the row class is stated by example, not
  proved.

## Proposed priority changes

- **Item 79**: dated note — the class and computed completeness are supplied by this
  round; the `Protocol.Evidence` map and duality remain.
- **New item 93**: the selection lock — a canonical joint rule for strength selection
  that removes hysteresis, and a *locked* selection the docket state can carry, which
  binding precedent needs and the moral reading forbids.
- **New item 94**: rational attainment and certificate completeness for the computed
  forced interval (the duality half of item 79's completeness), via a ℚ/ℝ transfer for
  the elimination file or a vertex argument.
- **Workspace friction F9**: rulings the program relies on (2026-08-08 past-self burn and
  seam ordering; 2026-08-09 strength selection) have no dated `DECISIONS.md` entry and
  cannot be cited.

## Outstanding maintainer actions

1. **The past-self-burn ruling.**  Decide whether a re-selection of a warrant strength
   under a canonical joint rule is a mechanically filed past-self charge (burns, so
   hysteresis stands without an external challenger) or recomputed state (does not burn).
   Queued in `DECISIONS.md`, *Awaiting the author*; not amended here.
2. **Land the 2026-08-08 and 2026-08-09 rulings as dated entries**, or say where they
   live, so a round can cite them (friction F9).
3. **Placement.**  Keep `projects/normativity/seed/` or rename under `legitimacy/`; if
   kept, add a `normativity.seed` subproject to `state/projects.json`.
4. **Registration at merge**: none proposed by the round; candidates are
   `forcedRegion_iff_check`, `forcedInterval_spec`, `forcedRegion_anti`, `confinement`,
   `seed_independence_strict`, `eventually_const_of_finite`.

## Deference-side pointers (no cross-edit)

`ALIGNMENT_READING.md`: `S_con` as a protected concern (`wiki/Corrigibility.md` §1);
`𝒟` as the reason-supply channel against item 87 clause 5 and PR #101's item 92;
pressure test 4 as the price-side analogue of `Corrigible ∧ ¬Authored`.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-16-seed-statics/PROMPT.md`.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-16.
