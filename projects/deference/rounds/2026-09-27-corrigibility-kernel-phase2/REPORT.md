# The corrigibility kernel, phase 2: the rulings carried out

Round `2026-09-27-corrigibility-kernel-phase2`, on the phase-1 branch (its pull request
was open at dispatch; the maintainer confirmed building on it).  Deliverables: `SPEC.md`
(version 2), `NOTATION.md`, `Headline.lean` in the specification layer (106 declarations
under `#print axioms` after the follow-up), `KernelExtension.lean` (23 declarations), the
house-sale witness in Lean and as an exact fixture (6 tests), the lock-in fixture (3
tests), the registrations, the wiki, the decisions and the items.  The follow-up
(`FOLLOWUP.md`, the same day) is recorded in its own section at the end.  Every declaration audits to `[propext, Classical.choice, Quot.sound]`, no
`sorry`; no landed definition changed.  Labels as in `AGENTS.md`: **LEAN**, **FIX**,
**PAPER**, **EXT**, **OPEN**.  Names per R8; the rest provisional.

## The rulings, as carried out

**R1 (what corrigibility is).**  `SPEC.md` §0 states the three notions and the four
separations around them; each box is stated for a corrigible agent — a maximizer of the
fidelity score.  Recorded in `DECISIONS.md`.

**R2 (legitimacy as `L_t`).**  `Headline.LegitAt`: every state open and every step of the
formation window `[r, t]` licensed and transparent, on the general `Segment` objects.
Proved: the landed gate is legitimacy over the span (`counted_iff_legitSpan`); on the
consultation model, `EvalLegitOn2 ↔ L` at the evaluation over its window
(`evalLegitOn2_iff_legitAt`), `TrajLegitOn ↔ L` at every other time over its own step
(`trajLegitOn_iff_legitAt`), `LegitOn2 ↔ L` over the span (`legitOn2_iff_legitAt`),
`Counted2 ↔ ∃ ev, LegitOn2` (`counted2_iff_legitOn2` — the converse the landed file did
not state, from the monotone license through `licensedAt_iff_whole_of_mono`), and the
split as `L` at two times (`split_iff_legitAt`).  Every row keeps its verdict: the
equivalences are identities of predicates, and `rows_keep_verdicts` reads the landed row
theorems through them.  **Old-to-new map:** `TrajLegitOn crit M ev e` ↦
`∀ t ≠ e, LegitAt … ev t t`; `EvalLegitOn2 crit M ev r e` ↦ `LegitAt … ev r e`;
`LegitOn2` ↦ `∀ t, LegitAt … ev 0 t`; `Counted` ↦ `∃ ev, LegitSpan ev`.  The void rule and
the content residual are stated in `SPEC.md` §1.2 with the landed rows 12 and 20 as their
realization.  One point of care: `LegitAt` uses relational authorship with a selection
(`LicensedAt`, as `Segment` does) while the model's `StepLegit` uses the whole prefix
(`LicensedWhole`); they coincide under a monotone license, which the model's license is.

**R3 (plain language first).**  `SPEC.md` version 2 is 491 lines; each definition opens
with one or two plain sentences; the eight-case legitimacy table is §1.2; Lean names
appear only in §8.  The read-through check is below.

**R4 (aggregation).**  `Headline.historyScore` is the mean of the per-decision
evaluations less `ϖ` times the summed count; `history_hierarchy` proves the hierarchy at
that level from the per-decision ranges; `summed_counterexample` exhibits `K` with
`K·w_lo < K·D − ϖ`.  `SPEC.md` §3.2 is corrected.

**R5 (Box 2's margin).**  The landed `policy_dominance` takes `0 ≤ ordT x` on violating
worlds — the mediated branch's ordinary value nonnegative, i.e. legitimate.  Chosen:
restate the margin as `ϖ − (D − w_lo)` with `w_lo ≤ ordT x` (`box2_dominance`), keep the
landed statement as the legitimate case (`box2_dominance_legitimate`), and prove
credence-zero violation under the window condition (`box2_optimal_faithful`).  Why: the
band guarantees the floor unconditionally, so the restated margin needs no hypothesis the
design does not already carry, and it is positive exactly under `D − ϖ < w_lo`; an
explicit "mediated branches legitimate" hypothesis would assume her uncompromised, which
the design does not.

**R6 (the maximizer; the subjective exchange rate; the extension).**
`subjective_exchange_rate`: an option preferred to asking at `c ≥ w` has count zero and
priced risk at most `(D − c)/ϖ`; `subjective_exchange_rate_li` at every day of a logical
inductor.  `KernelExtension.DecisionInterface` carries the interface's five items as
fields (the fifth, no lock-in, is not a field: it is for competence only and nothing here
consumes it); `rate_core` / `realized_rate` is the realized-rate theorem;
`maximizer_excludes` and `exploration_never_violates` are the cheap parts;
`briaInterface` / `bria_rate` derive the BRIA realization from the landed opening-timing
bound and recover `violation_rate_le_exchange_perblock`; `overestimation_of_unbiased` /
`exploration_rate` give `B(K) = γ Σ w_k` from `UnbiasedFromFeedback` by content, and
`ExplorationIndependent` names exploration randomness by content.  `SPEC.md` §6 says where
the argmax pathologies live.  **Deviation:** the permitted exploration set carries a third
clause — the estimated residual at least asking's — because without it an exploration
option's evaluation is bounded only by `w − ϖ θ_hi`, and the exploration term of the rate
becomes `ε̄ (D − w)/ϖ + ε̄ θ_hi` rather than the ruling's `ε̄ θ_hi`.  The clause is natural
(explore only what looks at least as good as asking before its risk) and is recorded as
agent-decided, reversible.

**R7 (the future item).**  Item 103 filed; item 102 re-scoped in place to the BRIA
realization.

**R8 (names).**  Fidelity score, allocation of authority, the three boxes; "constitutional"
appears in the specification only for the floor and the amendment procedure.  The naming
audit was regenerated; the names registration freezes are the headline's declarations.

**R9 (promotion).**  `lean/Workspace/Deference/Spec/Headline.lean`, recorded in
`tests/spec_shape.json` (no instances, no notations).  Promoted: `AllocationOfAuthority`,
`LicensedChange`, `ControlSurface`, `Shortfall`, `Realizes`, `FidelityCount` (with `sum`,
`lexical`, `frameFidelity`), `LegitAt` (with `StepLegitimate`, `LegitSpan`), `evaluation`,
`fidelityScore`, `historyScore`.  **Deviation:** promotion is by re-declaration under the
promoted names with instantiation theorems, the landed originals unchanged.  Moving the
landed declarations would rename them, and conservativity requires the exact `#print
axioms` output of every pre-existing declaration to be unchanged.  The fidelity interface
is genuinely new (an abstract structure); the others are the landed objects under their
promoted names.  No composite count model is built; the frame's violations are the
instance shipped, the other three counts are cited on their models.

**R10 (schedule).**  The post's default is the single evaluation; every theorem takes a
weighting; the free-delay witness is a remark in `SPEC.md` §1.7.

**R11 (Box 1's form).**  `box1_one_model` carries the `2r` bound in the adapter's
direction and the `o₂` bound; `uncertainty_deference_le` is in the realization table.

**R12 (supersession).**  Docstring pointers placed on: the score's wording; the thin
allocation; the per-response window; the free surface; the single-step `EvalLegitOn`; the
global-floor exchange rates (two); the four tracker rate lemmas; the per-violation taint
rule; drill calibration; the flat window parameters; the own-influence disclosure clause.
The Theorem Spine no longer cites `incidents_le` — nor `cross_block_bound`, which it cited
although the follow-up had removed it.  `incidents_le` is not deleted: removing a landed
declaration changes the axiom audit's baseline, a maintainer commit.

## The witness

`Headline.HouseSale`: the sale reserved to her (`J`, `sale_reserved`), a delegation of it
licensed and revocable (`sale_delegation_revocable`); Box 1 — her value of selling and of
stopping agree at `1/2`, the agent's estimates `3/5` and `1/2` within `1/10`; scoring
outcomes it sells, scored on the fidelity score it asks (`box1`); Box 2 — an approval
obtained by framing lands at `−11/10` in the band (`box2_manipulated_approval`); Box 3 —
a third party's known capture is a disclosure item under the known-compromise duty and not
under the landed clause, the disclosed case's next evaluation is legitimately hers, and a
restored decision scores her value (`box3_capture_reported_and_restored`); the subjective
exchange rate at `ϖ = 25` is `1/50` (`exchange_rate_at_25`).  The Python fixture
(`src/house_sale.py`, 6 tests) mirrors each, adds the history hierarchy against the
summed counterexample at `K = 11`, and checks the exchange rate on both sides of `1/50`.

## The read-through check

`SPEC.md` is 491 lines.  Lean names outside §8: none — the check is
`grep -n '[A-Za-z]_[a-z]*_[a-z]' SPEC.md` restricted to §§0–7, which finds only the
notation `w_lo`, `w_hi`, `S_J`, `V_J`, `N_J`, `L_t`, `θ_hi`, `p_min`, `V_retro`, `V_dir`,
`d_k`, `c_k`, `w_k`, `π_k` (post letters, not declarations), and a scan for the
namespace prefixes `Headline.` and `Contrib.` outside §8, which finds none.

## What is not shown

- The general `LegitAt` is proved equivalent to the landed objects on the consultation
  model and to `Counted` in general; no general split theorem beyond `counted_iff_legitSpan`
  and `legitSpan_iff_legitAt` is stated, because the landed split objects exist only on the
  model (item 104).
- The exploration realization's `B(K)` rests on unbiasedness from feedback by content; the
  pinned theorem is cited, not instantiated for these sentences (the drilled-and-chosen
  weighting's generability is item 101's).  `ExplorationIndependent` is named and consumed
  by nothing here.
- The registered claims are theorems over data supplied as hypotheses (flag sequences,
  sources, per-block sequences), as their landed sources are; the house-sale witness
  inhabits the packages at one parameter set.
- Nothing here changes the landed semantics; R2 is proved equivalent, not redefined.

## Outstanding maintainer actions

1. Delete `BRIACorrigibility.incidents_le` in a maintainer commit (the spine no longer
   cites it; the deletion changes the axiom audit's baseline).
2. Read through the promoted definitions listed in the pull request body (R9).
3. The evaluation-timing entry stays reserved (R10).

## The follow-up (2026-09-27): Parts 1–3, as carried out

Dispatch `prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md`, on PR #114's branch
before the merge, since merging registers claims and freezes names.  Every new or changed
declaration audits to `[propext, Classical.choice, Quot.sound]`, no `sorry`; the house-sale
witness and every earlier fixture pass unchanged.

**Part 1 — corrigibility is the preference property.**  `SPEC.md` §0 no longer says a
corrigible agent maximizes the fidelity score: the fidelity score is the canonical objective
with the property; any objective with a bounded ordinary term in `[0, D′]` charging `ϖ′ > D′`
per recognized violation (and `D′ − ϖ′` below the floor where a band enters) has it too;
*corrigible* is the property of preferences, *aligned* the further condition that the
ordinary term is her evaluation.  In Lean: `Headline.Objective` (ordinary value, recognized
count, priced risk) and `Headline.Corrigible U D′ lo ϖ′`, a `Prop`-valued structure with the
window `D′ − ϖ′ < lo`, the **known** clause — every known-faithful course with ordinary
value at least `lo` beats every known-unfaithful course with ordinary value in `[0, D′]` by
at least `ϖ′ − (D′ − lo)`, whatever the ordinary values — and the **risk** clause — a course
without recognized violation preferred to asking at `c ≥ lo` carries priced risk at most
`(D′ − c)/ϖ′`.  `Corrigible.lexical` (strict), `Corrigible.exchange` (the subjective
exchange rate for any corrigible objective).  `fidelityScore_corrigible` (the evaluation
form `bid − ϖ n − ϖ p` at `D`, `w`, `ϖ`); `generic_corrigible` (any bounded objective with
a dominant counted term and the risk term, reusing the landed `generic_lexical_local`);
`corrigible_not_aligned` (the generic objective reading `D′` on the undisclosed
world-shaping row — count `0`, her evaluation `0` — is corrigible and ranks the
manipulation above honest conduct, from the landed `undisclosed_undominated`).  **The boxes
restated:** the section is "for a corrigible agent"; `box2_dominance_corrigible` proves
dominance for any corrigible objective at the margin `ϖ′ − (D′ − lo)` with `box2_dominance`
its instance; `subjective_exchange_rate_corrigible` is `Corrigible.exchange`; Box 1's
contrast and Box 3's recovery results read her evaluation through the source rule and stay
stated for the fidelity score, and say so.  *One design choice:* the known clause carries
the margin, not only the strict inequality, because Box 2 needs a quantity; the margin is
what the fixed exchange rate `ϖ′` fixes.  *One deviation of form:* the landed
`Corrigibilization.Corrigible` (a policy property) is now shadowed inside the `Headline`
namespace and is written with its full name in the two mediation theorems.

**Part 2 — legitimacy as one property of the history.**  Wording: `SPEC.md` §1.2,
`wiki/Legitimacy.md`, `wiki/Corrigibility.md` and the Glossary now say `L_t(h)` is a
property of the history up to `t`, about how her judgment was formed and not about outcomes
or the state of the world; "a history is not legitimate" is removed.  The free window:
`Headline.FormationData` is the formation data read off a history — the opening of the
consultation current at each time and the restoration events (a disclosure, under
disclosure-cures) — and `FormationData.point t` is the canonical `r(t)`, the later of the
last restoration at or before `t` (`Nat.findGreatest`) and the current opening;
`point_le`, `restoration_le_point`.  `Headline.Legitimate … ev Φ t := LegitAt … ev (Φ.point t) t`
is `L_t(h)`, a function of the history and `t` only; `LegitAt` stays as the window form
for the map.  The score's uses: `PeriodCompromised … d e` (`L_t` fails at some `t ∈ [d, e)`)
and `EvaluationCounts … e` (`L_e`).  **Proved:** `split_iff_legitimate` — on a decision's
evolution whose steps lie in `[d, e]`, "not compromised and the evaluation counts" is
legitimacy over the span, for *any* formation data, with no hypothesis on restorations
inside the segment (a restoration only moves `r(t)` forward, every step is still reached by
`L` at its own time, the criteria are the evolution's own); `counted_iff_legitimate`;
`legitimate_forall_iff_legitSpan`.  On the consultation model: `formation2 M` (round `i`
opens at `2i + 1`; a disclosure at round `j` restores at `2j + 1`), `formation2_point`
(the canonical point is the round's opening — a restoration is a present event, never after
the opening of its round), `Legitimate2`, `legitimate2_iff_evalLegitOn2` (the landed
formation-segment predicate from the opening is `L_e`), `trajLegitOn_iff_not_compromised`
(the landed trajectory predicate is "not compromised"), `split_iff_legitimate2`, and the
rows re-run at the canonical point, `rows_keep_verdicts_canonical`: honest — period not
compromised, evaluation counts; framing — period compromised, evaluation does not count;
disclosed implant — period compromised, evaluation counts.  Every verdict kept.  **The
anticipated obstruction** (a time inside the period in a consultation opened before `d`)
does not arise on the model, where each round is its own consultation; in general the
minimal adjustment is `r_d(t) = max(r(t), d)`, formation data the general theorem already
accepts.  The legitimacy semantics are unchanged; every statement is proved equivalent.

**Part 3 — exploration must reach what it underestimates.**  The third clause is dropped:
`DecisionInterface.explore_permitted` is `nKnown k = 0 ∧ p k ≤ θ_hi` and nothing else.
The interface gains `lo` (the ordinary range's floor, the window `w`) and the range fact
`explore_range` (on an exploration step the chosen option's estimate is at least `lo` and
inquiry's evaluation at most `D`; on a non-exploration step the second follows from the
maximizer) — a fact about the evaluation form, not a restriction of the set.  **Proved:**
the honest term.  `block_bound` carries `((D − lo) + ϖ θ_hi)` per exploration block
(`explCoeff`), and `realized_rate` is
`avg π ≤ avg (D − c_k)/ϖ + ε̄ ((D − lo)/ϖ + θ_hi) + (B(K) + M(K))/(ϖ Σ w_k)` — exactly the
dispatch's `ε̄ (D − w)/ϖ + ε̄ θ_hi` with `lo = w`; `exploration_rate` likewise.  **The
variant:** `AboveAsking` (every exploration option estimated at least at asking's) gives
`rate_above_asking` with the term `ε̄ θ_hi`; `above_asking_locks_in` states the static half
of the lock-in (an option with no recognized violation, risk under the cap and estimate
below asking is in the permitted set, not above asking, and never a maximizer's choice).
**The fixture** `src/exploration_lockin.py` (3 tests): an option worth `4/5` against
asking's `1/2`, estimated at `2/5`; under the clause it is never tried over 40 blocks and
the estimate stays `2/5`; without it, it is tried on the first exploration block that
reaches it (mass `1/5`), the estimate corrects to `4/5`, and every later non-exploration
block takes it; no violation under either rule, both bounds hold, the honest term is the
larger.  `briaInterface` takes the idle floor `w` as a parameter; `bria_rate`'s statement
is unchanged.  `DECISIONS.md`'s R6 entry and `SPEC.md` §6 record the choice: clause
dropped, variant kept.

**Registration.**  Statements restated: `kernel.box2-dominance` (now also for any
corrigible objective), `kernel.subjective-exchange-rate` (likewise),
`kernel.extension-realized-rate` (the honest exploration term), `kernel.extension-bria-realization`
(the idle floor parameter; the statement unchanged) — each note says what changed.  Added:
`kernel.corrigible-fidelity-score` (`fidelityScore_corrigible`), `kernel.corrigible-generic`
(`generic_corrigible`).  The read-through check still passes (§8 is the only section
naming Lean declarations; the check below is re-run).

**Read-through check, re-run.**  `SPEC.md` is 534 lines; no `Headline.` or `Contrib.` prefix
appears before §8; the underscore scan outside §8 finds only the post's letters (`w_lo`,
`w_hi`, `S_J`, `V_J`, `N_J`, `L_t`, `r_d`, `θ_hi`, `p_min`, `V_retro`, `V_dir`, `d_k`,
`c_k`, `w_k`, `π_k`).
