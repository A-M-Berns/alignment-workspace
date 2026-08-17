# Report — traderized enforcement, second pass

**Prompt author model:** GPT-5.6 Sol (OpenAI). **Executor model:** Claude Opus 5
(Anthropic). **Dates:** 2026-08-16 to 2026-08-17. Dispatch: `PROMPT-follow-up.md`.

Nothing from the first pass is deleted or weakened. What changes is the question
the results are read against, and three of the answers.

## Force-story verdict

**Yes.** Traderization can serve as the general mechanism by which a validated
admissibility constraint acquires operative force, and the argument for it is
stronger than a preference.

The market maker of Logical Induction is a total function: `lem:fpl` supplies a
fixed point for whatever aggregate it is handed and the acceptance search
terminates. Adding a strategy to the priced aggregate changes only that
function's input, so existence, `lem:mm`, `lem:tfdom` and the shape of `thm:lia`
all survive. **A market maker additionally required to display a price inside
`K_t` is not known to be total, and there is a date where it is not**: one priced
sentence, `K = {P ≤ 1/2}`, an ordinary aggregate buying one share flat — the
contract forces `P = 1`, the region forbids it, and no price satisfies both.

## Constrained-market-maker verdict

**Retired for the enforcement column, and for nothing else.** The first pass's
answer conflated two replacements, and the follow-up is right that this was the
error. Traderization does not replace the settlement interface: reports, timing,
persistence, grounding, feasibility, the breach stack and answerability stay
upstream, and `FORCE_INTERFACE.md` §3 assigns each of them to a layer.

What it does replace is `P1`, and that is now demonstrated rather than deferred.
The interface's own `NL-SI-A2` proves the `theta`-admissible references form a
polytope with one rational row per endorsement, and a rational row is what the
compiler consumes. `CORE_CONDITION.md` walks the compilation on the interface's
displayed instance: the maximal coefficient recomputes to `1/2`, matching
`NL-SI-A5`; at `theta = 1/4` the row is `P(A) ≥ 2/3`; at the maximum exactly one
price survives and it is the reference `NL-SI-A5` says attains it. Every
contract-feasible price is checked against the *definition* of the core
condition, walking each shrunk vertex, not against the row that produced it.

The compilation has one precondition the round discovered rather than assumed:
the endorsement must be **priceable** — its coefficient vector over worlds must
be a combination of priced sentence indicators. Unpriceable endorsements are
detected and refused rather than approximated.

## Exactness verdict

**Resolved into cases, and the fork's branches are all inhabited.**

- **A, for regions with an interior.** An interior-anchored position — the
  Minkowski gauge of the region about a strictly interior anchor, times the
  displacement toward it — is legal, expressible, and enforces membership exactly
  against every disturbance of declared mass. Verified in one and two dimensions.
  The violation-proportional compiler cannot, because it vanishes as the
  violation does and a bounded disturbance cancels it near the boundary.
- **B, for regions without an interior.** No continuous strategy achieves
  exactness against any positive disturbance budget. Excluding the cube corners
  forces opposite signs at the two ends; the intermediate value theorem then puts
  a zero in between; and continuity puts a whole interval of cancellable prices
  around it, which a region with empty interior cannot contain.
- **C, as the asymptotics of B.** For `ζ_E(P) = s(c − P)` the cancellable
  interval has width exactly `2C/s` — positive at every finite intensity,
  shrinking without limit.

**Regions without an interior are the normal case, not the exotic one.** Every
settlement equality is one. So is every coherence polytope over a fragment
carrying a propositional relation. The first pass's exact-enforcement theorem is
therefore the disturbance-free case `C = 0`, and it is labelled as such.

**And exactness costs the safety property.** This is the pass's worst finding and
it is the round's own. The interior-anchored position does not vanish on the
region, so the enforcement inequality's nonnegativity reading does not apply to
it. On a world-inclusive full-dimensional region where the violation-proportional
position never loses in a plausible world, the interior-anchored one is worth
`−1/2` — at a price **inside** the region, with every row violation zero. The two
compilers are not ordered. Whether one is both exact and safe is open.

## Tolerance verdict

**Sufficient, and the measure gap is closed.** `T1` exists precisely for engines
whose prices are only approximately coherent, and asks for a declared schedule;
`D3(a)` asks for a computable one with per-date conformance. The round's modulus
delivers that: intensity `(ε_t + C_t)/δ_t²` buys row violations at most `δ_t`,
with `C_t` available before the price is set.

What was missing was the conversion from row violations to the incoherence
functional the clause measures. By duality the incoherence *is* the largest row
violation over signed weight vectors of total mass at most one, so a rational net
of those rows converts one to the other up to the net's resolution. On `NL-SI-C5`
the net at denominator three recovers `4/15` exactly — the interface's own number,
recomputed here independently from credal states — and nets at denominators one
and two report nothing at all. Resolution is a presentation choice, and it decides
how much incoherence any mechanism can see.

## Safety verdict

**Bounded cumulative enforcement liability, with world-inclusiveness demoted to
its `B = 0` case.** The follow-up was right that the first pass over-stated this.

The liability identity gives more than the `d ≡ 0` corollary read off it. The
enforcement position's value in a world is at least
`∑_j β_j g_j² − ∑_j β_j g_j d_j(W)`, where `d_j(W)` is how far row `j` excludes
`W`, so **both factors are needed on one row** for a date to cost anything: a
live violation, and a right-hand side that excludes the world. Kernel-checked as
`weighted_square_sub_deficit_le_pair`, with an inhabitation witness at nonzero
deficit.

Under the certified declaration the per-date ceiling is `C_t · max_j d_j(W)` —
**the intensities cancel**. A mechanism cannot lower its liability by enforcing
gently or raise it by enforcing hard. This corrects the first pass, which read a
fixture's rising per-date losses as sharper enforcement costing more; they rise
*towards* the ceiling and stop.

So the condition is `∑_t C_t · max_j d_j(W) < ∞`, and it is strictly weaker than
world-inclusiveness. **A region excluding a live world at every date can be
enforced forever, safely.** The witness: one sentence settled true, a source
reserving against full certainty with `K_t = {P ≤ 1 − 2^{-t}}`, ordinary volume
`t`, promised tolerance `1/10`. Conformance holds at every date, every date shows
a real plausible loss, no date is world-inclusive, and the cumulative liability is
bounded by `∑_t t·2^{-t} = 2`. The contrast case holds the depth fixed and the
bound diverges.

The reading: a source may permanently exclude states deduction permits — which is
what a normative constraint is for — provided the depth of exclusion decays
against the growth in ordinary volume. Not agreement with deduction; convergence
on it, at a rate.

## Constitution boundary

Not traderized, and explicitly upstream: construction of `K_t`; legitimacy of the
source; priceability; effective presentation as rational rows; nonemptiness and
the quarantine on failure; persistence of a positive coefficient (`D1`); the
depth of any exclusion; settlement's reports, timing and persistence; and
learning among licensed responses.

Two reassignments the follow-up asked for and the mathematics supports.
**Nonemptiness is the feasibility adapter's** — a constrained maker cannot display
a price in an empty region either, and `NL-SI-A3` already decides it by one linear
program and declares quarantine. **Bounded liability is the source's** — the
ceiling depends on nothing the mechanism chooses.

## The attribution objection, withdrawn

The first pass held that `∑_j β_j g_j² ≤ ε_t + C_t` makes ordinary traders partly
responsible for a violation, breaking `NL-SI-T4`'s total-and-exclusive
attribution. That was wrong. `C_t` is a declared assumption, not a suffered cause,
and the trading-firm construction computes a bound on its own volume from the
belief history. Volume within `C_t` and a price outside `δ_t` is the
implementation's failure; volume above `C_t` is a false declaration; a conforming
price the docket cannot certify is `T1`'s sound-but-not-working case. Three cases,
one respondent each — the same partition `T4` already runs.

## What remains conjectural

That the interior-anchored construction generalises beyond the two dimensions
tested. That unbounded liability *always* yields an exploiting trader. That
`C_t · max_j d_j` is the tightest ceiling. That the modified algorithm is a
computable belief sequence for every effectively presented region. That a
compiler exists which is both exact and safe.

## What the second pass refuted in the first

**That world-inclusiveness is the safety dividing line.** It is the `d ≡ 0` case,
and a permanently non-world-inclusive region can be safe.

**That sharper enforcement costs more.** The ceiling is intensity-free.

**That ordinary trader volume is an unattributable third cause.** It is a declared
assumption.

**That traderization is "a second engine to audit alongside" the constrained
maker.** The constrained maker has no existence theorem; the comparison is not
symmetric.

**That the exactness question was open.** It is answered, in cases, with the
answer depending on whether the region has an interior — and with a cost the
first pass did not anticipate.

## Deviations from the dispatch

**No `RELATED_WORK.md`.** Unchanged; the record is `SOURCE_AUDIT.md` §8, and the
second pass added no sources.

**No living specification note.** `FORCE_INTERFACE.md` is written as a proposal
for one — the force contract, the two implementations, the responsibility table —
but it is not installed under `notes/`. The exactness/safety trade-off means the
compiler choice is not settled, and a living note naming one would fossilise a
decision the round did not earn.

**Item 40 sharpened rather than closed.** The dispatch asks not to duplicate stale
priorities. Item 40 asked whether unbounded liability always yields an exploiting
trader; it is now restated around the summability condition rather than around
world-inclusiveness, since the earlier framing was the one this pass refuted.

## What this pass does not establish

That the force contract is the right factorization — it is a proposal, tested
against two implementations and one interface clause, not against the whole
settlement interface. That the round's `P1` implementation satisfies `P1` as the
interface means it: the interface certifies `theta_min` *of an engine*, and here
it would be certified of a declaration, which is a change of respondent and is
reserved. That the endorsements a normative practice produces are priceable — the
failure mode is exhibited, its frequency is not.

## Outstanding maintainer actions

Carried forward from the first pass, with one added:

4. **Rule on whether `P1` should be restated as a demand on a force
   implementation rather than on a market maker.** `CORE_CONDITION.md` §3 proposes
   it and shows the compilation; the frozen consolidation is not edited. *Doing
   it* is deciding whether the clause names a mechanism or an obligation.
   *Waiting* leaves the round's `P1` result readable but unadopted.

Appended to `DECISIONS.md`'s *Awaiting the author*.
