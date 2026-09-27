# The corrigibility kernel, phase 2: the rulings carried out

Round `2026-09-27-corrigibility-kernel-phase2`, on the phase-1 branch (its pull request
was open at dispatch; the maintainer confirmed building on it).  Deliverables: `SPEC.md`
(version 2), `NOTATION.md`, `Headline.lean` in the specification layer (71 declarations
under `#print axioms`), `KernelExtension.lean` (17 declarations), the house-sale witness
in Lean and as an exact fixture (6 tests), the registrations, the wiki, the decisions and
the items.  Every declaration audits to `[propext, Classical.choice, Quot.sound]`, no
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
