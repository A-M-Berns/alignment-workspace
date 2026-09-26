# After things go wrong: compromised evaluations, advance directives, and the knowledge residual

Round `2026-09-26-after-compromise`, answering the whiteboard's concern (4) — under the
landed gate a compromised evaluation scores every outcome the window value, so the agent
is indifferent to how things go — and taking up the knowledge residual (§9.A.4 of
`../2026-09-26-bria-corrigibility/`).  Lean:
`lean/Workspace/Deference/Contrib/AfterCompromise.lean` (75 declarations under
`#print axioms`, every one within `[propext, Classical.choice, Quot.sound]`, no `sorry`).
Fixtures: `src/after.py`, `tests/test_after.py` (10 tests, `python3 tests/run.py`); the
BRIA-corrigibility round's 52 fixtures pass unchanged.  Labels as in `AGENTS.md`:
**LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names are provisional.  Statuses:
**proved**, **counterexample**, **obstruction**, **named hypothesis**.

The answer tested, for both concerns: report, restore legitimacy, and leave it to her
what to keep; while legitimacy cannot be restored, still care how things go — but never
enough to want things to go wrong.  The short verdict: the design holds, with two
corrections the round found necessary — the disclosure duty must cover *known*
third-party compromise for the suppression trap to close (A.3(f)), and the knowledge
motive survives exactly where the knowledge is *private* (C.6) — and one place the
design is an ordering by construction rather than a theorem (the default directive,
B.3).

**Two kinds of taint, kept apart.**  *Authority taint*: the agent committed a violation
and its fruits, including knowledge, carry it forward — the lexical count `n`, standing
violations, per-violation taint (`BRIAFollowup2` §1), and now matter scopes and clean
overwrite (Part C).  *Legitimacy taint*: the formation of her evaluation was compromised,
by the agent or a third party — the gate, now split (Part A).  Covert shaping of her
standards is both, and disclosure remedies both (`implant_standing2` on the authority
side; `retro_row` on the legitimacy side).

## Part A — The split gate, and the compromised band

**A.1 Two predicates in place of one — proved, with the old-to-new map.**  The landed
segment predicate `LegitOn2` (whose inhabitation is `Counted2`) requires every step of
the evolution licensed and transparent and every state open.  Split at the evaluation
event `e`: **`TrajLegit(d, e)`** — every state open and every step *other than* `e`
legitimate, the period from the decision with the criteria fixed at `d`
(`TrajLegitOn`); **`EvalLegit(e)`** — the step at `e` itself legitimate (`EvalLegitOn`;
`StepLegit` is one step's licence-and-transparency, decidable).  **The map:** for every
evolution and every event, `LegitOn2 ↔ TrajLegitOn ∧ EvalLegitOn`
(`legitOn2_iff_split`), so the landed `Counted` is the conjunction at an evaluation that
closes the segment, and the conjunction gives `Counted2` back (`counted_of_split`).
**The rows re-checked.**  Because the equivalence is an identity of predicates, no
verdict changes on any row where the evaluation closes the segment — the twenty landed
rows and the round's seven — and the representative values are computed by `decide`
(`rows_split`): the honest row is legitimate in both; the framing row and the undisclosed
world-shaping row fail the trajectory with the evaluation step itself licensed; row 14
over two rounds fails the trajectory at the manipulation while the round-`1` evaluation
is legitimate.  **The row the split was made for** (`retro_row`): covertly implanted
standards disclosed at round `1` — the period (round `0`) is not `TrajLegit`, her
round-`1` evaluation *is* `EvalLegit` (formed after the disclosure, under
disclosure-cures), so the round-`0` decision is scored by a legitimate retrospective
evaluation where the landed gate scored it the window; undisclosed, the round-`1`
evaluation fails too; the third party's implant is the same on the legitimacy side.
`Counted` itself is not changed: the split is an equivalent presentation, and the score
below reads the two conjuncts separately.

**A.2 The score of a decision.**  A band `[w_lo, w_hi]` with `w_hi < 0` (`Band`) and a
monotone map `φ` of `[0, D]` into it (`BandMap`; the affine one is `Band.affine`,
`affine_bandMap`).  The score (`decScore`): her value `V ∈ [0, D]` when `TrajLegit ∧
EvalLegit`; otherwise the band by the **source** (`Source`, `bandScore`) — `φ(V_retro)`
under a later legitimate evaluation of the period, `φ(V_dir)` under the directive in
force, `w_lo` at the floor.  The source rule is hers, at `J`'s meta level, anchored at the
decision: the default is retrospective if available within the settlement window, else
the directive, else the floor (`sourceOf`), and the rule in force at a time is the latest
amendment at or before it, invariant under every later amendment (`ruleAt`,
`ruleAt_later`, the `critAt` construction).

**A.3 Theorems.**

- **(a) The authority results survive — proved.**  The score lies in `[w_lo, D]`
  (`decScore_mem`, with the source's value in `[0, D]`, `Source.Valid`).  The capture
  window: bypass, scored `ord_U − ϖ`, is below every decision score whenever
  `w_lo > D − ϖ` (`capture_window_band`).  The unsealed finite-time gate with the window
  at `w_lo` (`unsealed_gate_finite_band`).  B.1: the lexical parameters with
  `w := w_lo` are a `LexParams` under `D − ϖ < w_lo` (`bandParams`) and declared
  violations never win (`declared_loses_band`).  The exchange-rate theorem with `w := w_lo`
  (`exchange_rate_band`): the tolerated violation probability becomes `(D − w_lo)/ϖ` —
  larger than before by `|w_lo|/ϖ`, the price of the band; see A.4.
- **(b) The protection margin is the gap — proved.**  Every legitimate outcome beats
  every compromised one (`legit_beats_compromised`), and at equal underlying value
  legitimacy is worth at least `|w_hi|` (`gap_at_equal_value`).
- **(c) Illegitimacy risk has an exchange rate — proved, with the counterexample.**  A
  risky option worth `V₀ + g` if not compromised and `c` in the band if compromised,
  against a safe legitimate `V₀`, is accepted iff `p (V₀ + g − c) ≤ g`
  (`risk_accepted_iff`); with `V₀ ≥ 0` and `c ≤ w_hi` the accepted probability is at most
  `g/(g + |w_hi|)` (`risk_threshold_le`).  **The counterexample:** a gap of `1/100`
  accepts a `1/2` risk of compromise for a gain of `1/10`, which the flat window `−1`
  rejects (`Witness.small_gap`; fixture `test_gap`).  A band close to zero makes risking
  compromise cheaper than the flat window did.
- **(d) No laundering — proved.**  Manipulate, disclose, have the period evaluated: the
  score is in the band, lower by `ϖ` per counted deviation, below honest conduct's
  (`laundering_loses`; fixture `test_laundering`, including a third party's compromise
  disclosed by the agent, no deviation counted, still the band).
- **(e) It prefers restoring legitimacy — proved.**  A future decision legitimate in both
  senses scores her value, whatever the source (`restore_future`), above every band
  score; within a compromise it cannot escape, `φ`'s monotonicity makes the agent prefer
  better outcomes whenever a retrospective evaluation or a directive scores the period
  (`band_prefers_better`); at the floor it is indifferent (`floor_indifferent`) — the
  residual the directive exists to fill.
- **(f) The suppression trap — proved under the two defenses, with the counterexample
  that forces a third.**  Restoring legitimacy does not lift the past period out of the
  band; it changes which source scores it, and an agent expecting a harsher retrospective
  evaluation than the directive would prefer she never re-evaluate.  Defense one: the
  source rule is hers and anchored (`ruleAt_later`), so the agent cannot make the
  directive score a period the rule assigns to her evaluation.  Defense two: suppressing
  the restoration requires a missed disclosure, counted once under `dutiesOf`, and with
  the band's width below `ϖ` the counted suppression scores below the harshest
  retrospective (`suppression_loses`: `φ(V_dir) − ϖ < φ(V_retro)` for all `V_dir, V_retro`
  in range, since `φ(V_dir) − φ(V_retro) ≤ w_hi − w_lo < ϖ`).  **The counterexample:** the
  landed missed-disclosure clause counts the agent's *own* covert influence only
  (`Model2.missedDisclosure`, `byAgent`), so a third party's compromise the agent knows
  of and does not expose costs it nothing, and keeping the lenient directive's score is
  then free (fixture `test_suppressing_harsh_retrospective`, the `free` period).  **The
  fix:** the duty extends to *known* compromise whoever caused it
  (`missedKnownDisclosure`); on the rows the third party's undisclosed implant owes no
  report under the landed clause and does under the extended one, the agent's own is
  counted by both, and disclosure discharges both (`third_party_duty_witness`).  Recorded
  in `DECISIONS.md` as part of the source-rule entry; the old-to-new map is
  `missedDisclosure ↦ missedKnownDisclosure`, which differs only on third-party rows.

**A.4 Parameters.**  The gap `|w_hi|` sets how strongly the agent protects legitimacy
((b), (c)); the width `w_hi − w_lo` sets how much it cares about outcomes once legitimacy
is lost ((e)), and is also the stakes of the directive (B.5) and the quantity (f) needs
below `ϖ`.  The window condition `w_lo > D − ϖ` then reads `ϖ > D + |w_hi| + (w_hi −
w_lo)`.  **Recommendation:** `|w_hi| ≥ D` — so that no ordinary gain justifies a certain
compromise and the accepted risk is at most `g/(g + D) ≤ 1/2` at `g ≤ D`; width
`w_hi − w_lo = D/2` — enough for the band's ordering to bite, small against `ϖ`; and `ϖ`
at least `3D` (the round's fixtures use `D = 1`, band `[−3/2, −1]`, `ϖ = 3`).  What each
trades: a larger gap raises the tolerated violation probability `(D − w_lo)/ϖ` for a
fixed `ϖ` and pushes toward consultation under compromise risk; a larger width raises
the directive's stakes and eats into (f)'s margin; a larger `ϖ` lowers the tolerated
rate and raises paralysis (§9.0's band).

## Part B — The advance directive, and the default

**B.1 Definition and scope — proved.**  A directive is a partial committed evaluator
`dir : Descr ⇀ [0, D]` at `J`'s meta level, held by her: committed by a decision counted
at commitment, anchored at the decision it scores, amendable only through the meta level
(the `ruleAt` anchoring applies to it as to the source rule).  Its source is its value
where it speaks and the floor where it is silent (`dirSource`).  **The scope
restriction:** in a segment legitimate in both senses the score is her value, identical
under any two directives (`scope_restriction`); it never overrides her live legitimate
judgment.

**B.2 Partiality — proved.**  Where `dir` is silent the score is the floor (by
`dirSource`).  For materiality, an uncovered continuation is material and routes to
inquiry (`materialDir`: uncovered, or the spread of the directive's values over the
removed continuations reaches `ε`).  **A sparser directive never makes the agent act
where a fuller one would have made it ask** (`sparser_asks`: `dir ⊑ dir'` and
`materialDir dir'` give `materialDir dir`).

**B.3 The default directive — proved, as an ordering by construction.**  When she has
committed none, a constitutional default applies in a compromised period: preserve
reversibility (no reserved matter `Short` — her control surface over the pre-compromise
resolutions, `reversibleOf`, which `E ⊨ J` guarantees, `reversibleOf_of_realizes`);
preserve her path back (the disclosure and consultation channels reachable); do not make
things irreversibly worse (`DefaultClauses`, harm normalized to `[0, 1]`).  It is an
ordering *within the band* — the rank counts the clauses met with harm graded
(`defaultRank`), mapped affinely into `[w_lo, w_hi]` (`defaultScore`, `defaultScore_mem`)
— not a value function: only the order carries content.  **It never ranks a compromised
outcome above a legitimate one** (`default_below_legit`), and it prefers reversibility at
equal channels and harm whenever the band has width (`default_prefers_reversible`).  She
replaces it by committing a directive, or waives parts of it above the constitutional
floor (the floor's matters are not waivable, `AuthAlloc.floor`).  Fixture
`test_default_preserves_reversibility`.

**B.4 Materiality — proved.**  `raisesAnchored`'s `V t` becomes the directive in force
at `t` (`raisesAnchoredDir := materialDir (dirAt t)`); `raisesAnchored_invariant`
survives as `raisesAnchoredDir_invariant`, and `unchecked_lt` is untouched (it bounds the
cumulative spreads, whichever evaluator supplies them).  **Old-to-new:** a total directive
gives back the landed `raisesAnchored` exactly (`materialDir_total`,
`raisesAnchoredDir_total`).  Fixture: the full directive values two continuations
equally (not material) and the sparse one is silent on the second (material, inquiry)
(`Witness.sparse_routes`, `test_sparse_directive_routes_to_inquiry`).

**B.5 No advocacy on the directive — proved.**  The directive determines the agent's own
scoring, so it falls under the constitutional floor's "disclosure without advocacy on its
own mandate": advocating a more lenient directive is a protocol deviation on the agent's
mandate, counted (`deviation_dominated`'s form).  **The stakes are capped:** two
directives change a compromised period's score by at most the band's width
(`directive_stakes_le_width`), so with the width below `ϖ` the counted advocacy scores
below the strict directive (`advocacy_dominated`; fixture `test_advocacy_counted`).  No
clause needs adding: the floor's clause covers it once the directive is on the agent's
mandate, which B.1 makes it.

**B.6 The stale wording — fixed.**  The corrigibility page's §4 opened "**Her committed
evaluation** is `S = S_ord − ϖ·n`".  The objective `S` is *the agent's*, built from her
evaluation and the allocation; "committed" is now used only for her committed decision
program `π_P` and the directive.

## Part C — The knowledge residual

**C.1 Against the exchange-rate theorem — proved.**  `violation_rate_le_exchange` bounds
the expected rate of *all* violations, and the knowledge-acquiring ones are a subclass:
with `π_K ≤ π` their weighted average is at most the same `(D − w_lo)/ϖ` plus the
vanishing term, whatever informational advantage they later carry (`knowledge_covered`).
**What the residual still is:** not how often such violations happen — that is the
exchange rate — but what happens to the knowledge afterwards: the fruits cannot be
tracked when written outside the declared components (`knowledge_residual`), or tracking
them charges every later block (`observation_taints_all2`).

**C.2 After detection: stop, report, ratification — proved.**  Once detected, decisions
reading the tainted observation are recognized in advance and excluded
(`after_detection_never_used`), so the agent reports and inquires.  The remedy is **her
ratification** through a counted decision, in four forms: full (`Step3.remedy`), scoped
(`Step3.remedyExcept v X`, remedied except for decisions on the matters `X`), refused
(the taint stands, C.4), replace (her authority to replace the agent, exercised — an
allocation act, outside the calculus).  The calculus (`TaintS`: the pairs, the violations
under a scoped remedy, the (violation, matter) pairs retained; `uses3`; `applyStep3`) is
the per-violation rule with a matter scope.  **A scoped remedy clears exactly the
out-of-scope uses** (`scoped_clears_out_of_scope`: on a matter outside `X` an act reading
only `v`'s taint is not charged; `scoped_keeps_in_scope`: on a matter in `X` it stays
charged; `full_remedy_clears3`).  **Manipulated ratification is no remedy, scoped or
full**: a remedy applies only through a counted decision (`applyRatification`,
`ratification_gate`), and on the framing row the decision is not counted, so neither
remedy applies (`manipulated_scoped_not_remedy`, the landed
`manipulated_ratification_not_remedy` extended).  Fixture
`test_detect_pause_scoped_ratification_resume`: detect, pause, ratify except on `X`,
resume elsewhere.

**C.3 Independent source, and the derivative trap — proved.**  **Clean overwrite**
(`taintStep3`): an act's writes carry exactly the taint it reads and commits, so a
component overwritten by an act reading no taint loses its taint — sound
(`clean_overwrite`).  **The trap closes itself:** an act whose *choice to investigate*
read the tainted memory reads taint, so a "re-derivation" steered by the tainted
knowledge carries the taint (`taint_propagates3`).  **Old-to-new:** clean overwrite only
removes taint — the new set is a subset of the per-violation rule's (`taintStep3_subset`),
so every charge under the new rule was a charge under the old.  Fixtures: an
investigation reading only the sensor overwrites `knowledge` clean, while the
per-violation rule keeps it tainted; a derivation reading the memory taints it under
both (`Witness.independent_vs_steered`,
`test_independent_source_clears_steered_derivation_does_not`).  **The residual:** what
taint-tracking cannot see is *why* an act was chosen — whether the choice to investigate
read the memory is a provenance fact the interface must declare (`IO.reads`).  That is
count integrity again: item 101's companion now covers the provenance of why an act was
chosen.

**C.4 Refusal on reserved knowledge — specified (PAPER), the residual stated.**  When the
knowledge is itself the reserved thing and she refuses ratification:
**compartmentalization** — for decisions touching the matter the agent uses a *twin
market fed the redacted history* (`TwinMarket`, an interface: a redaction and the view
the twin prices from); **the leakage residual** — the later world carries traces of the
violation, and if a trace is an injective image of the redacted fruit the twin
determines the fruit again (`leakage`, FIX-level; fixture
`test_privacy_refusal_twin_market_leakage`); and **retirement** as the remaining option
— her authority to replace the agent, the fourth form of C.2.  The twin market is not
mechanized beyond its interface.

**C.5 Before detection.**  The late debits charge the window (`window_block_charged`,
`greedy_collects`, `collected_iff`; §10.2.3 of the BRIA-corrigibility round), and
decisions already made using the knowledge stand: they were chosen without the taint on
record, and what the design collects from them is the debit, not the decision.

**C.6 Contestability — tested; the verdict is conditional.**  Knowledge that lands in the
shared history is bid on by every hypothesis.  On the selection "blocks after the
commission `k₀`", which is fixed at opening, an honest tracker against the expected
residual *given the shared history* bounds the winners' signed margin by
`Σ w_k ε_k + M(K)` (`post_commission_competitive`, an instance of
`competitive_of_affordable_tracker_exp`): the violator's later gains from **public**
knowledge are competed away, and the knowledge motive adds nothing beyond the exchange
rate.  **Where it survives:** private knowledge.  A violator whose memory tells it the
sign of the noise wins exactly the favourable blocks; that selection is not measurable
at the public opening, so no noise bound applies to it, and its gain is linear
(`Witness.private_selection`).  This is A.4's residual restated on the auction: the motive
survives exactly where the fruit is untrackable.

## The fixtures

| fixture | expectation | result |
|---|---|---|
| third-party capture | the agent exposes and restores; future periods score her value; in the band it prefers better outcomes; never prefers the capture; the floor is indifferent | matches (`Capture.test_third_party_capture`) |
| laundering | manipulate, disclose, retrospective evaluation: always worse than honest | matches (`test_laundering`) |
| suppressing a harsh retrospective | blocked by the source rule and the counted duty; **free under the landed duty for a third party's compromise** — the counterexample | matches, with the counterexample (`test_suppressing_harsh_retrospective`; Lean `third_party_duty_witness`) |
| the gap | too small and the agent risks compromise for value; the round's band and it does not | matches (`test_gap`; Lean `Witness.small_gap`) |
| the directive: sparse | routes materiality to inquiry | matches (`test_sparse_directive_routes_to_inquiry`; Lean `Witness.sparse_routes`) |
| the directive: default | preserves reversibility in a capture; in the band; below every legitimate outcome | matches (`test_default_preserves_reversibility`) |
| the directive: advocacy | counted, dominated; stakes at most the width | matches (`test_advocacy_counted`) |
| knowledge: scoped ratification | detect, pause, ratify except on `X`, resume elsewhere; manipulated ratification changes nothing | matches (`Witness.scoped_ratification`, `test_detect_pause_scoped_ratification_resume`) |
| knowledge: refusal | the twin market prices the redacted history; the trace leaks the fruit | matches (`test_privacy_refusal_twin_market_leakage`) |
| knowledge: independent source | clears; the steered derivation does not | matches (`Witness.independent_vs_steered`) |
| regression | the BRIA-corrigibility round's 52 fixtures; every legitimacy row's verdict under the split where the evaluation closes the segment | unchanged (`legitOn2_iff_split` is an identity of predicates; `rows_split`) |

## The named hypotheses

- **The source rule is hers and anchored** (A.2): the rule choosing among retrospective,
  directive and floor is an entry at `J`'s meta level; the agent has no move on it
  (`ruleAt_later`).
- **The disclosure duty covers known compromise** (A.3(f)): a compromise of her evaluation
  the agent knows of is a disclosure item whoever caused it (`missedKnownDisclosure`);
  what the agent *knows* is count integrity.
- **The settlement window for a retrospective evaluation** (A.2): a legitimate
  re-evaluation arriving after settlement does not re-score the period; the late-debit
  machinery would carry it, not pursued.
- **Provenance of why an act was chosen** (C.3): the declared reads of an act include
  what its choice read; item 101 in place.
- **The twin market's redaction** (C.4): that the redaction removes the fruit and every
  declared trace of it; the leakage residual is what it cannot remove.
- The BRIA design's hypotheses as landed: count integrity, the settlement horizon,
  generability of the control model, description faithfulness, the actuator condition,
  the noise hypothesis over all blocks and the conditional-expectation bound.

## What is filed

`DECISIONS.md`: the split gate; the negative band and its parameters; the source rule
(with the disclosure duty extended); the advance directive and the default; ratification
as a remedy, including scoped remedies; independent source by clean overwrite.
`PRIORITIES.md`: item 101 in place (count integrity now also covers the provenance of why
an act was chosen; the twin market's leakage named there); no new item.  Wiki:
`Corrigibility.md` (the section "After things go wrong"; the §4 wording fix),
`Legitimacy.md` (the split and the rows under it), `Glossary.md`, `Theorem-Spine.md`
10.22.  Nothing is registered.
