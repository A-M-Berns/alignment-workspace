# Prompt — 2026-09-17 convergence-measure

Relayed verbatim from the maintainer, 2026-09-17.  Executor: (fill in).

---

Work in `A-M-Berns/alignment-workspace`, on a new branch `round/2026-09-17-convergence-measure`, branched from `round/2026-09-16-seed-statics` (PR #102) if it is not yet on `main`, otherwise from `main`.

This round follows the seed-statics round.  That round showed that a humble substantive seed narrows or breaks and never pins (`seed_independence_strict`), that confinement between two reasoners is a hull bound (`confinement`), and that disjoint forced intervals on a sentence are joint infeasibility with a Farkas certificate.  The consequence we now take as the program's position: **convergence between normative reasoners is not agreement on a point; it is a measure**, living on the unpinned fragment, with two components that fail in different ways — *not narrowed yet* and *contradicted*.

Your task is to define that measure exactly, prove its dynamics on the existing statics, state and prove (or break) the interval-convergence theorem that replaces the seed-statics round's C2/C3, and show on the two fixtures that reasoners with different histories and different live dockets can converge in the measure without converging in reasons.

This is a theorem-discovery round.  The central question is:

> For reasoners sharing a structural layer and a settled fragment, with humble substantive seeds and live warrant sets that may differ, define hull mass and discord mass on a declared fragment; show hull mass is nonincreasing under settlement and shared narrowing and nondecreasing under reopening, and converges under summable reopenings; show discord is certified; and show that convergence in the measure neither requires nor implies convergence of the live dockets.

Do not assume the candidate theorems are true.  Try to break each of them; the measure in particular should be attacked for gameability.

## Separation

PR #101 (deference, non-capture compilation) and PR #102 (seed statics) may both be in flight.

* Do not edit files reserved to PR #101 (`wiki/Roadmap.md`, `wiki/Theorem-Spine.md`, `wiki/Corrigibility.md`, `wiki/Deference.md`, `projects/deference/`, `lean/Workspace/Deference/`).
* Consume PR #102's objects unchanged: `SeedStatics.lean` (the seed, `forcedRegion`, `forcedInterval`, `forcedInterval_mono`, `confinement`, `measure_form_refuted`, `seed_independence_strict`, `tendsto_of_summable_drops`), `src/fm.py`, and the two fixtures.  Add; do not rewrite.  If a definition there is wrong for this round's purpose, say so in the report and define the corrected object under a new name.
* Do not touch items 79, 93, 94.  File new items from 95, and state the assumption.
* No criterion work (the seed-statics round's fifth objective is closed as construction-relative; do not reopen it).

## Context to inspect first

* `projects/normativity/seed/rounds/2026-09-16-seed-statics/` in full — `SEED.md`, `STATICS.md`, `CONFINEMENT.md` (especially §§3–4 and the five pressure tests), `STABILIZATION.md` (S1, the oscillation witness, S2), `FIXTURES.md`, `COUNTERMODELS.md`;
* `lean/Workspace/Normativity/Contrib/SeedStatics.lean`, all 42 declarations, before writing any new one;
* `lean/Workspace/Normativity/Contrib/NormativeInductorComposition.lean` (`FarkasCert`, `conflict_sound`) and `FourierMotzkin.lean`;
* the defeat landing (`projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/`) for what the calculus determines — the seed-statics round's finding that it fixes the live docket per trace and computes no extension is a premise of this round, not something to relitigate;
* `wiki/Normativity.md` for the reserved meaning of *leverage* (keep the seed round's *seed leverage* distinct, as it did);
* for the LI comparison in the sixth objective: the formalized convergence statements in the FAF interface the repository pins (cite exact declarations; no paraphrase);
* `AGENTS.md`, all standards.

## The setting

As in the seed-statics round: a language with finite date-fragments, rational prices, a settled fragment `F`, a seed with substantive (strict, strength `< 1`), structural (strength `1`) and constitutive layers, warrants and defeaters as landed.  A **declared fragment** `Φ ⊆ 𝒧_t` is the set of sentences the measure is taken over; it is an input, never chosen by the round to make a number look good.  Optional **weights** `w : Φ → ℚ_{>0}` with `Σ w = 1`; default uniform.

Reasoners `R¹, …, Rⁿ` share the structural and constitutive layers and `F`.  Each has a humble substantive seed `Sⁱ_sub` and a live warrant set `Wⁱ` (its own trace's live docket — not assumed equal).  `Kⁱ = K(Sⁱ ∪ Wⁱ, F)`, `Iⁱ_φ` the forced interval.

## The measure (first objective)

Define, in Lean, on `Φ` with weights `w`:

* **hull** `H_φ := conv(⋃ᵢ Iⁱ_φ)`, an interval; **hull mass** `Hull(Φ) := Σ_φ w_φ · |H_φ|`;
* **common interval** `C_φ := ⋂ᵢ Iⁱ_φ` (possibly empty); **overlap mass** `Ovl(Φ) := Σ_φ w_φ · |C_φ|`;
* **discord set** `Δ(Φ) := { φ : C_φ = ∅ }`; **discord mass** `Disc(Φ) := Σ_{φ ∈ Δ} w_φ`;
* for each `φ ∈ Δ`, the **discord certificate**: a `FarkasCert` for the merged bundle restricted to the coordinate `φ` together with the minimal infeasible subset of `⋃ᵢ (Sⁱ_sub ∪ Wⁱ)` it names — i.e. what some reasoner would have to give up for `φ` to leave `Δ`.  Show this certificate exists whenever `φ ∈ Δ` (two-reasoner case first; `n` reasoners by the same argument or a counterexample);
* the **convergence profile** `(Hull, Ovl, Disc)`.  State exactly which orderings on profiles you will use and why (Hull down and Disc down is "better"; Ovl is diagnostic, not a target — argue this or replace it).

Prove the obvious inequalities (`Ovl ≤ Hull`; `Disc = 0 → Ovl > 0` on nontrivial `Φ`; `Hull ≤ 1`) and the relation to the seed-statics quantities: on the pinned fragment of the closed layer, `H_φ` is a point for every humble seed (`seed_independence_strict` lifted to `n` reasoners), so the profile lives on the unpinned fragment; and `Hull(Φ) = 1 − (shared narrowing)`, made exact in terms of the seed round's *seed leverage* — say precisely how two-reasoner leverage relates to hull mass, or that it does not.

## Gameability (second objective — do this before the dynamics)

The measure is only worth having if it cannot be made to look good by construction.  Attack it:

1. **Fragment dilution.**  Adding vacuous or trivially-pinned sentences to `Φ` drives `Hull` down.  Show this happens under uniform weights; state the rule that blocks it (declared `Φ`; or weights that give pinned coordinates zero mass; or normalizing by the unpinned fragment only) and prove the blocked version is invariant under adding pinned coordinates.
2. **Coordinate splitting.**  Refining `φ` into `φ₁, φ₂` under the transport rule changes the count.  Show whether `Hull` is transport-invariant under conservative transport with inherited weights; if not, define the transport-invariant version.
3. **Agreement by vacuity.**  Two reasoners with empty substantive seeds have `Hull = ` (whatever the closed layer leaves) and `Disc = 0`.  This is correct and uninteresting; make sure the report says the measure is *relative to the closed layer*, and give the reference profile `Hull(∅-seeds)` so that a reasoner pair is scored against it.
4. **Discord hiding.**  A reasoner can avoid discord by holding only wide intervals.  Show that `Disc` and `Hull` trade off and that neither alone is a target; the profile is.
5. **Weight capture.**  If weights are chosen by a reasoner, it can zero out its own discord.  Weights are constitutive-layer declarations; say so and show the measure is not defined for reasoner-chosen weights.

Any attack that succeeds and cannot be blocked by a declaration goes in `COUNTERMODELS.md` and into the report's "what is not established."

## Dynamics (third objective)

Along a chain `F_0 ⊆ F_1 ⊆ …` and docket events (shared warrant landing, private warrant landing, reopening/defeat), for fixed `Φ` and `w`:

**Candidate Theorem H1 (monotonicity).**  `Hull` is nonincreasing under settlement (from `forcedInterval_mono` applied to each `Iⁱ`) and under **shared** narrowing (a warrant landing in every `Wⁱ`); nondecreasing under reopening.  Private narrowing (a warrant landing in one `Wⁱ` only) — determine its effect on `Hull` and on `Disc` exactly: it cannot raise `Hull`; can it raise `Disc`?  (Expected: yes; exhibit it.  This is the mechanism by which one reasoner learning something *creates* discord — the world is where the reasoners meet, so a one-sided discovery is a disagreement until shared.)

**Candidate Theorem H2 (convergence).**  Under summable reopenings (the seed round's S2 hypothesis, applied to the hull endpoint sequences), `Hull_t` converges.  Also under a finite discovery class (S1).  State the limit `Hull_∞` as the measure of what seeds, world, and exchange left open.

**Candidate Theorem H3 (discord resolution).**  If exchange is such that every private warrant is eventually shared (an *exhaustive-sharing* condition, weaker than the seed round's exhaustive exchange because it does not require a unique extension), then `Disc_t` is eventually constant, and its limit is exactly the set of sentences on which the merged closed-and-substantive bundle is infeasible — with certificates.  Persistent discord is certified incompatibility, never an artifact of order.

**Pressure tests**, each with an exact fixture:

1. Hull oscillation under an infinite discovery class (lift the seed round's witness to two reasoners).
2. Discord created by private learning and dissolved by sharing (H1's mechanism, both halves).
3. Persistent discord with certificate: two humble seeds whose merge is infeasible on one sentence under every `F` — show the certificate is stable along the chain.
4. Locked selections (law): one reasoner carries a locked strength selection (the seed round's item-93 object, as a hypothesis only); show `Hull` still converges and what the lock does to `Disc`.  The point: convergence in the measure does not require unlocking history.
5. **Convergence without reason convergence.**  Two reasoners with disjoint live dockets and `Hull_∞ = Ovl_∞ = ` (narrow), `Disc_∞ = 0`.  This is the seed round's pressure test 4 promoted from caveat to theorem: the profile converges while the reasons do not.  Name the phenomenon provisionally *overlapping consensus* and state exactly what it is and is not (it is price agreement on `Φ`; it is not agreement about why, and it is not stability under a new defeater that attacks one docket and not the other — exhibit that fragility).

## Many reasoners (fourth objective)

Generalize the profile to `n` reasoners: `H_φ` is the hull of all; `Δ` is where the common intersection is empty.  Define the **discord graph** on reasoners (an edge where two forced intervals miss on some `φ ∈ Φ`) and show: `Disc = 0` iff the graph is empty iff the merged bundle is feasible on `Φ`; and the certificate for an `n`-way discord names a minimal subset that may involve more than two reasoners (exhibit a three-reasoner discord with no pairwise discord if one exists, or prove pairwise suffices — the intersection of intervals on a line is pairwise-determined by Helly in dimension one, so state what that gives and what it does not).

## The overlapping-consensus reading (fifth objective — short)

One section, no theorems beyond those above.  Say what the results mean for the program's position on convergence:

* convergence is `Hull → small` with `Disc → 0` on a declared `Φ`, relative to the closed layer;
* it is compatible with trace-constitutive dockets and with locks — the fork between grounded conformance and trace-dependence bears on *reason* convergence only;
* persistent discord is certified and points at what must be given up;
* one-sided learning creates discord until shared: the world reconciles only what is shared.

No sentence may claim two reasoners "end up in the same place."  They end up within a hull, and the hull is the result.

## The LI comparison (sixth objective — short, exact)

State, citing the formalized declarations, what Logical Induction gives across two inductors: agreement in the limit on what settles, and nothing on what does not.  Then state what this round gives: on the unsettled normative fragment, `Hull` narrowing and `Disc` resolving under shared structure and exhaustive sharing — a cross-reasoner property LI does not have, obtained from mechanisms (shared structural layer, exchange) LI does not have.  Do not overstate: the property is relative to the closed layer and to `Φ`, and it is a statement about forced intervals, not about any inductor's prices reaching them.  This section exists so that the claim to Abram is exact.

## Fixtures

Extend both seed-round fixtures in place under this round's `src/`; do not modify the seed round's files.

**Moral.**  Two reasoners: both with valence, dominance, impartiality, conservative transport; `R¹` additionally holds a humble prioritarian item, `R²` a humble sum item (both strength `< 1`, on the same pair of outcome-ranking sentences).  Run a settlement chain that pins the welfare levels; compute the profile at each step; show whether the aggregation disagreement ends as hull width or as discord, with certificate if discord.  Then share one warrant and recompute.  Then add the population axioms to `R¹` only and show discord created by private learning.

**Legal.**  Two courts: same constitution, different traces (one has a locked selection for the substantive right's strength, per item 93 as a hypothesis).  Compute the profile on `Φ = {validity of statute, scope of enumerated power}`.  Show the hull converges and where the lock sits in the profile.  The fixture is allowed to fail on standing and hierarchy exactly as before; do not attempt those.

## What this round is told not to do

* No criterion work; no inductor run; no enforcer claims.
* No rewriting of `SeedStatics.lean` or the seed round's fixtures.
* No import of LI theorems by paraphrase.
* No `Φ` or `w` chosen to improve a number; both are inputs and the report says where they came from.
* No claim of convergence without `Φ`, `w`, `F`-chain, and the sharing condition named.
* Names provisional (standard 6): *hull mass*, *overlap mass*, *discord set/mass*, *discord certificate*, *convergence profile*, *shared/private narrowing*, *exhaustive sharing*, *discord graph*, *overlapping consensus*.

## Lean / formalization target

`lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean`, importing `SeedStatics`, sorry-free, auditing to `[propext, Classical.choice, Quot.sound]`:

* `hull`, `commonInterval`, `discord`, `hullMass`, `overlapMass`, `discordMass` on a finite `Φ` with weights;
* the basic inequalities; invariance of the blocked `Hull` under adding pinned coordinates;
* H1 (monotonicity under settlement and shared narrowing; nondecrease under reopening; private narrowing cannot raise `Hull`);
* H2 via `tendsto_of_summable_drops` on the hull endpoints;
* H3 if the exhaustive-sharing condition can be stated on the existing docket types; otherwise its exact statement and the obstruction;
* the two-reasoner discord certificate from `FarkasCert`; the `n`-reasoner Helly statement;
* nothing for the fifth and sixth objectives.

Register nothing.  `PROVENANCE.md` lists every declaration with status.

## Output

Directory: `projects/normativity/seed/rounds/2026-09-17-convergence-measure/`:

* `README.md` — one-line verdict in the repository's style;
* `MEASURE.md` — definitions, inequalities, relation to seed leverage;
* `GAMEABILITY.md` — the five attacks and what blocks each;
* `DYNAMICS.md` — H1–H3 with proofs or obstructions, and the five pressure tests;
* `MANY.md` — the `n`-reasoner profile and discord graph;
* `CONSENSUS.md` — the fifth objective;
* `LI_COMPARISON.md` — the sixth objective;
* `COUNTERMODELS.md`, `FIXTURES.md`, `REPORT.md`, `PROVENANCE.md`, `src/`, `tests/run.py`.

Mirror at `prompts/2026-09-17-convergence-measure/PROMPT.md` and `REPORT.md`; add to `state/rounds.json`.  Do not merge.

## Final questions the report must answer

1. Is the profile well-defined and Lean-stated, and which of the five gameability attacks succeeded against the naive definition?  Which declaration blocks each, and is any unblockable?
2. Does H1 hold as stated?  Does private narrowing raise `Disc`, and is the mechanism exhibited both ways?
3. Does `Hull_t` converge under summable reopenings, and what is `Hull_∞` on each fixture?
4. Does H3 hold under exhaustive sharing, and is persistent discord always certified?
5. Is convergence without reason convergence exhibited, and how fragile is it to a one-sided defeater?
6. Does a lock break convergence in the measure?  (Expected: no.)  Where does it sit in the profile?
7. For `n` reasoners: does pairwise discord suffice, and what does Helly give and not give?
8. Exactly how does two-reasoner hull mass relate to the seed round's seed leverage?
9. On the moral fixture, does the prioritarian/sum disagreement end as width or as discord, and what does the certificate name?
10. What is the exact LI comparison, with declarations cited, and what is the one-sentence claim it licenses?
11. Which names are provisional; which seed-round objects were reused unchanged; did any need a corrected twin?
12. What would you have wanted to prove and could not, and where exactly did it stop?
