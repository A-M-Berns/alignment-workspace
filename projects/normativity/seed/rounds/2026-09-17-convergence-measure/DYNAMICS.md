# Dynamics

Lean: `ConvergenceMeasure.lean` §§3, 4, 6.  Fixtures: `src/fixtures.py`,
`tests/test_measure.py`.

## 1. H1 — monotonicity: holds, with one correction to the expected mechanism

**Nesting.**  `Nested I I'` says every reasoner's interval shrank or stayed.  Then
(`hullLo_mono`, `hullHi_anti`, `hullWidth_anti`, `hullMass_anti`) hull mass is
nonincreasing, overlap mass is nonincreasing (`overlapMass_anti`), and discord persists
(`discord_persists`), so discord mass is nondecreasing (`discordMass_mono`).  Reopening is
nesting in the other direction: `hullMass_mono`.

**Which events nest.**  At the region level, with dimension `m + 1` and nonempty
regions:

| event | region inclusion | intervals |
|---|---|---|
| settlement `F ⊆ F'` | `forcedRegionR_anti` (seed round) | `forcedInterval_mono` |
| warrant landing, in one or every `Wⁱ` | `forcedRegionR_anti_warrants` | `forcedInterval_nest_of_subset` |
| defeat landing (reopening) | `forcedRegionR_anti_defeat`, reversed | `forcedInterval_nest_of_subset`, reversed |

Settlement and shared narrowing nest every reasoner; private narrowing nests one and
leaves the rest (`Nested.ofPrivate`); all three lower `Hull`.  Private narrowing
**cannot raise `Hull`** and **can raise `Disc`**: fixture `private_learning`,
`[0, 2/5]` against `[3/10, 1]` (profile `(1, 1/10, 0)`); reasoner 2 privately learns
`P(φ) ≥ 3/5` and the profile becomes `(1, 0, 1)` with certificate gap `1/5` naming
`P(φ) ≤ 2/5` and the new warrant.

**The correction.**  The dispatch expected the discord to be *dissolved by sharing*.
It is not, and cannot be: sharing a warrant narrows the receiver (`Nested`), and
`discord_persists` says a nesting never removes discord.  Sharing the private warrant
with reasoner 1 makes reasoner 1's bundle `{P(φ) ≤ 2/5, P(φ) ≥ 3/5}` infeasible —
reasoner 1 is **refuted**, not reconciled (fixture: `shared.refuted = [R1]`).  The
discord dissolves only by reopening: defeating the warrant on reasoner 2's docket returns
the profile to `(1, 1/10, 0)`.  So the mechanism has one half as expected (private
learning creates discord) and the other half replaced: **discord is removed by defeat
or by refutation, never by sharing.**  Both halves are on the fixture.

## 2. H2 — convergence: holds

`hullMass_tendsto_of_summable`: along a chain of valid interval data, if for every
declared coordinate the downward steps of the hull's lower endpoint and the upward steps
of its upper endpoint are summable, hull mass converges.  The proof applies the seed
round's `tendsto_of_summable_drops` to each lower endpoint (bounded by `1`) and to the
negated upper endpoint (bounded by `0`; `tendsto_of_summable_rises`), and sums over `Φ`
(`tendsto_finsetSum`).  `hullMass_tendsto_of_summable_rises`: summable upward steps of
the mass itself suffice.

Under a finite discovery class the interval data is eventually constant (seed round's
`eventually_const_of_finite`, applied to each reasoner's raised set and the shared
settlement), so `Hull_t` is eventually constant.

**`Hull_∞`** is what seeds, world and exchange left open: the weighted width of the
limit hulls, read against `Hull(∅‑seeds)_∞`.  On the fixtures: moral, `7/12` at the last
settlement step with `Disc = 1/6` (`FIXTURES.md` §1); legal, `13/20` once the conflict
and the power are settled, `Disc = 1/2` (§3); `consensus`, `1/3` with `Disc = 0`.

**Oscillation (pressure test 1).**  `oscillation_two`: reasoner 1 runs the seed round's
witness (fresh `P(φ) ≥ 1/2` at odd dates, its undercut at even dates) while reasoner 2
holds `P(φ) ≥ 3/10`.  Hull width alternates `7/10, 1, 7/10, 1, …`; reopenings of `3/10`
are not summable; no limit.  H2's hypothesis is exactly what fails.

## 3. H3 — discord resolution: holds in a corrected form

**Exhaustive sharing**, stated on the existing docket types: there is `T` such that for
`t ≥ T` every reasoner's live substantive-and-warrant row set is the same
(`liveSub Sⁱ stⁱ_t ++ Wⁱ_t` agree up to the rows they contribute).  This is weaker than the
seed round's exhaustive exchange (no extension is required) and stronger than "every
private warrant is eventually shared": sharing warrants without sharing *defeats* does
not equalize the live sets, and a warrant defeated on one docket and live on another is
exactly the one-sided defeater of pressure test 5.  The condition is on live sets, and
the round could not state a weaker one that gives the conclusion.

**Under it**, for `t ≥ T` the reasoners differ only in their substantive seeds.  With a
finite discovery class and monotone settlement, `Disc_t` is eventually constant
(`eventually_const_of_finite` per reasoner); its limit set `Δ_∞` is
`{φ ∈ Φ : ⋂ᵢ Iⁱ_φ = ∅}` at the limit bundles, and each `φ ∈ Δ_∞` has a certificate
(`discord_iff_pair` picks the pair, `discord_certificate` merges their bound
certificates).  Persistent discord is certified incompatibility between substantive
items over the shared closed layer, never an artifact of order: with equal live sets the
intervals are a function of the bundles, not of the traces — **unless** a strength
selection was locked (pressure test 4), in which case the lock is a row and the discord
it causes is certified against the lock by name.

**The correction.**  The dispatch's limit — "the set of sentences on which the merged
bundle is infeasible" — is not a set of sentences: merged infeasibility is global, and
`Δ_∞` can be empty while the merged bundle is infeasible (`MANY.md` §2, hidden discord).
What holds is `Δ_∞ ≠ ∅ → merged infeasible` and every `φ ∈ Δ_∞` certified; the
converse fails.

## 4. The five pressure tests

| # | fixture | result |
|---|---|---|
| 1 oscillation | `oscillation_two` | hull width `7/10, 1, 7/10, 1, …`; no limit |
| 2 private learning | `private_learning` | created: `(1, 1/10, 0) → (1, 0, 1)`; **not** dissolved by sharing (receiver refuted); dissolved by defeat |
| 3 persistent discord | `persistent_discord` | `Δ = {φ}` at both chain steps, gap `2/5`, certificate `{P(φ) ≥ 4/5, P(φ) ≤ 2/5}` unchanged while `ψ` settles and `Hull` falls `1 → 1/2` |
| 4 lock | `lock` | reasoner 1 locked at `9/10`, reasoner 2 selects `4/5`; profile `(3/20, 1/20, 0)` at both chain steps — the lock is width (reasoner 1's `R ∈ [9/10, 19/20]` inside the hull `[4/5, 19/20]`); against an opposing presumption it is discord `(2/5, 0, 1)` with certificate `{locked right 9/10, presumption 3/10}` and the supremacy row |
| 5 consensus without reasons | `consensus` | disjoint dockets, `I¹_φ = I²_φ = [2/3, 1]`, profile `(1/3, 1/3, 0)`; one defeater on reasoner 1's docket: `(1, 1/3, 0)` |

Test 5 is the seed round's pressure test 4 as a theorem: the profile is a function of
interval data (`hullMass`, `discordMass` are defined on `IntervalData`), and two
reasoners with disjoint live sets can present the same data.  Its fragility is
`hullMass_mono`: a one-sided defeat is a reopening of one reasoner, and the hull follows
the wider one.
