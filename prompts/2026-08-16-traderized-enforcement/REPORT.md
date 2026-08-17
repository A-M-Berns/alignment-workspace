# Report — traderized enforcement

**Prompt author model:** GPT-5.6 Sol (OpenAI). **Executor model:** Claude Opus 5
(Anthropic). **Dates:** 2026-08-16.

Round directory: `projects/normativity/rounds/2026-08-16-traderized-enforcement/`.
Lean: `lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean`.

## Strongest positive result

Compiling a row presentation of an admissible region into one violation-weighted
day-`n` trading strategy gives that region operative force, and the whole of it
follows from one inequality: for every point `x` meeting every row,

    ⟪ ζ_E(P), x - P ⟫  ≥  ∑_j β_j g_j(P)² .

Kernel-checked as `weighted_square_le_pair`, with an inhabitation witness. Three
readings, all kernel-checked: exact finite-time enforcement under an exact
market-maker contract, at every positive intensity including arbitrarily small
ones; a computable violation modulus `∑_j β_j g_j² ≤ ε_n + M_n` under the
algorithm's actual contract; and — the one that matters for safety — the
enforcement position is worth at least zero in **every world the region
contains**, with no hypothesis about the market, the ordinary traders, or the
funding.

That last reading is what makes the mechanism viable. Composed with the
market-maker lemma and trading-firm dominance it gives: if the region contains
every world the deductive process has not yet ruled out, the modified market
satisfies the Logical Induction Criterion with the unmodified bound, and
enforcement costs the criterion nothing.

## Strongest negative result

Two, and the second is more interesting than the first.

**Exact finite-time enforcement is false under the algorithm's actual contract.**
The market maker returns a rational approximation with slack `2^-n`, and at slack
`1/8` against `K = [1/2, 3/4]` the price `1/3` violates by `1/6` and still meets
the contract. Opposing ordinary volume defeats exactness even at slack zero: the
equilibrium violation is exactly `M/β`.

**Losing region-plausibility containment is not a lost bound but an actual
exploitation.** With `φ` settled true, a source demanding `p(φ) ≤ 1/2`, and
opposing mass `1/2`, sharper enforcement costs strictly more — the enforcement
trader's plausible loss per date is `9/40`, `99/400`, `999/4000` at intensity
`10`, `100`, `1000` — and the trader that buys one share of `φ` per date reaches
plausible net worth `18/5` over eight dates against the safety theorem's bound of
`14/5`. It exploits.

## The five statuses the dispatch asks for

**Exact enforcement:** proved under an exact contract (`le_pair_of_contract_zero`,
kernel-checked); **false** under positive slack, with the smallest counterexample
displayed.

**Anti-exploitation:** proved conditional on bounded enforcement liability, with
explicit bound `1 + B`; unconditional (`B = 0`) for regions containing every
still-plausible world. The converse is a witness in one shape, not a theorem, and
is known to fail in the other direction — weak enforcement has zero liability
without containing the plausible worlds.

**Deduction special case:** an addition, not a replacement. Enforcing the
coherence polytope of the deductive stage supplies a finite-date coherence
guarantee a logical inductor does not have, at zero plausible cost and with no
subsidy. It removes the deductive process from neither the criterion nor the
construction.

**Relation to the settlement interface:** traderization supplies the enforcement
column and neither reports nor timing. It writes nothing into the record and
leaves no residue at the next date when the source withdraws a row, where a
settlement cannot be withdrawn and stays exploitable if mispriced. It is a
candidate route to the interface's open sub-problem `D3(a)` — Theorem 4 yields a
computable conformance schedule — and is filed as one rather than claimed.

**Relation to `Due/Licensed/Loss`:** orthogonal. Different spaces, different
quantifiers, no shared object. The reading under which traderization *implements*
the normative statics is open and blocked on an object the workspace does not
have: a map from a normative record to an admissible region in price space. Filed
as an item. `world-inclusive region` is **not** identified with `coverage(Due)`.

**Relation to Legitimacy:** a separation, stated as an architectural finding and
not a legitimacy theorem. Operative force is cheap — any nonempty region with a
computable rational row presentation gets it at any positive intensity — so a
constraint being operative is no evidence it is legitimate. The mechanism makes
manipulation *easier*: at slack zero a singleton region determines the displayed
price exactly, so control of the constraint source is complete control of the
credal state. The one thing the market itself checks about a source is that it
does not contradict what deduction has settled.

**Relation to Deference:** downstream. A trusted-process constraint can be made
operative whenever it is presentable as a computable rational row system, and
that supplies none of authorization, principal-exclusive corrective control, or
advisor-robust futurity. The workspace's own `value_eq_of_price_realization_eq`
says why: the enforcement trader reads only prices and acts only on prices, so it
factors through the static view and cannot distinguish jurisdiction. No
corrigibility claim.

## What remains conjectural

That unbounded enforcement liability *always* produces an exploiting efficiently
computable trader — only one shape is witnessed. That the modified algorithm is a
computable belief sequence for every effectively presented region — argued from
the strategy's expressibility, not proved. That the enforcement trader's addition
preserves the market maker's own termination argument — inherited from continuity,
not rechecked against the formalization's search.

## What was believed at the start and refuted

**That funding is the scarce resource.** It is not. Logical Induction imposes no
budget, collateral, or bounded-downside requirement on traders, so growing
external credit is free and an unboundedly-losing trader is an ordinary object of
the theory. The scarce thing is showing a loss in a world that is still
plausible. The dispatch's funding model — finite at each date, unbounded over
dates — is correct as a description and turns out not to be a constraint the
framework imposes; `FundingLedger` still tracks it, separately from the quantity
the criterion sees.

**That the intensity has to be large.** Under an exact contract the
contract-feasible set is *identical* across intensities spanning three orders of
magnitude, and in the adversarial fixture the realised position size is identical
across `β ∈ {10, 100, 1000}` — set entirely by the opposing volume. Intensity buys
precision under slack and nothing else.

**That the market maker's fixed point projects onto the region.** It does not. It
pins prices to cube extremes in the direction of net demand, which is why a single
separating hyperplane overshoots and admits `{5/6, 11/12, 1}` on a region that
ends at `3/4`. The construction that works uses the whole row system, and the
naive one is kept in the source as the displayed failure.

**That "traderize deduction" names one construction.** It names at least two.
Enforcing the affine relations among priced sentences is cheap and enforces
strictly less than coherence — 24 incoherent grid points survive on a
four-sentence Boolean fragment, including one pricing a conjunction above a
conjunct. Enforcing coherence needs the facet system of the convex hull of the
plausible worlds, which is computable and not efficiently computable.

**That the enforcement trader holds nothing when enforcement succeeds.** True
only when no ordinary trader is pushing the other way. With opposing demand the
enforcement position is exactly the offset, and its plausible loss is exactly the
opposing traders' plausible gain. This was believed for part of the round and the
fixtures corrected it.

## Deviations from the dispatch

**No `RELATED_WORK.md`.** The dispatch permits the literature record in
`SOURCE_AUDIT.md` and it is there, §8, three items with their exact influence.

**No wiki page beyond a research-direction section.** The dispatch conditions
wiki material on the architecture becoming clear enough and otherwise prefers a
small treatment; the formulation is not stable — the constraint-source-to-region
map is absent and the necessity direction is a witness — so `wiki/Normativity.md`
gains one section and no page is created.

**No living Normativity note.** Same condition, same reason. The dispatch's own
fallback applies.

**The Lean port is the algebra, not the mechanism.** The dispatch asks for the
load-bearing algebraic lemma if it is short and clean, and for the exact future
port target named otherwise. Both were done: four inequalities are kernel-checked,
and the composition that is *not* in Lean — the safety theorem against the
dependency's own `Trader`, `MarketMaker` and `TradingFirm` — is named with the
line the modification breaks.

**Prompt correction.** §XI's artifact list is followed exactly. §0's orientation
list is complete as given; `state/foundations.json`, `state/rounds.json` and
`state/vocabulary.json` were additionally read because the round updates two of
them.

## What this round does not establish

That any market maker realises the contract every theorem here is stated over. It
is read off the paper's `def:markemaker` and the formalization's
`MarketMakerAccepts` in `SOURCE_AUDIT.md` §2, and it enters as a hypothesis. A
reader who rejects that reading keeps the algebra and loses the application.

That the enforced region is the right one. Enforcement is indifferent to the
content of the constraint and will hold a singleton as readily as a defensible
region.

That `M_n = C_n` is tight. It is the bound the source construction already
computes.

That the fixtures generalise. They are exact-rational finite models over stated
domains, at dimensions one to four and grid denominators up to twenty-four
(two thousand at the largest intensity); a passing sweep says nothing about points
outside the grid it enumerated.

## Structural defects found

No new one. Filed item `F7` bit this round: adding a round to `state/rounds.json`
made `prompts/2026-08-13-wikification-and-normativity/VERDICT_STATUS_INVENTORY.md`
stale, so a completed round's directory had to be rewritten by
`--write-handoff` to keep the state check green. That is the item's own
description and it is not re-filed.

## Outstanding maintainer actions

1. **Rule on the nine provisional names** listed in the round `README.md` and in
   the pull request. They are **not** in `state/vocabulary.json`: that file
   generates a sheet headed *canonical*, and a proposal does not belong in it.
   Deciding costs one reading of `MODEL.md` §§4–6, and the names then enter the
   sheet.
2. **Decide whether `world-inclusive region` and `coverage(Due)` are related.**
   The round asserts they are not and exhibits no map. If they are, the arrow
   belongs in `state/theorem_interface.json` and this round did not put it there.
3. **Decide whether any of results 2, 3, 4 or 8 is worth registering.** All four
   are kernel-checked and axiom-clean and none answers a filed item; registering
   any requires a `PRIORITIES.md` item first. The round filed items 39–42 within
   its scope but did not file one whose answer is these inequalities, because
   registering an inequality about an abstract pairing would register something
   whose connection to Logical Induction is a reading.

Each is appended to `DECISIONS.md`'s *Awaiting the author*.
