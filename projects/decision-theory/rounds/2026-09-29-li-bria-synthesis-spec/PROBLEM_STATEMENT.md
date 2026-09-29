# The LI/BRIA synthesis: the destination, and how to recognize it

Labels: **PAPER** (a theorem of arXiv:1609.03543 v5 or of TARK 2023 EPTCS 379 pp.
421–440, cited at its statement), **DERIVED** (follows from cited results by an argument
given here, hypotheses named), **FIX** (exact fixture in `tests/`, run by `tests/run.py`;
a finite prefix check against fixed bidders or fixed agents, never a proof of a
quantified statement), **CONJ** (conjectured), **EXT** (a contract named and not paid),
**OPEN**.  Names are provisional: *supporting milestone*, *successful endpoint*, *ideal
extension*, *witness estimates*, *market-relative hypothesis class*, *recovery domain*,
*belief–decision compatibility*, *realized-feedback register*.

## 0. The acceptance statement

> A candidate counts as a **successful outcome** if it establishes the **supporting
> milestones** — computable existence with named comparison classes (M1), logical
> induction on the active trajectory (M2), bounded-inductive-rationality recovery on a
> declared recovery domain (M3), and coverage as accountability with menu safety named
> (M4) — **and** an **integration result** of the form of §3, which is at least
> achievement I1 (market information provably improves decision performance, T10 under
> its stated accounting) **and** achievement I3 (decision accountability provably
> excludes the belief–action self-confirmation of A1), with achievement I2 (a
> compatibility relation) stated at least in its established form W1; **and** passes
> the recovery and integration rows of `TEST_SUITE.md` under their stated assumptions;
> **and** demonstrates **one substantive advance** on a recognized obstruction of
> logical-induction decision theory, under the matched environment and information
> structure of a well-posed diagnostic of §7 (A1 counts, and is also I3).
> **Updatelessness is an additional ideal target**: policy-level guarantees on
> environments where the agent's rewards depend on its policy rather than on its
> history and current choice (§7, A2), with a recovery domain that is not yet defined
> (§2, M3).  A candidate meeting the milestones and I1 alone has a publishable
> integration theorem and is not yet the endpoint.

*Logical structure.*  A1 is at present the only well-posed advance diagnostic; a
candidate claiming a different advance first states it to the standard of §7.  All of
M1–M4 are required.  I1 and I3 are both required; I2 is
required only in its established form, its strong form being a further target.  The
advance is required, and A1 satisfies it together with I3.  A2 is an extension.
*What no open choice prevents.*  The judgments "milestones met", "I1 met", "I3 met",
"A1 met" can each be made now under the assumptions their rows state.  *What the open
choices prevent* (§2 M3, `AUDIT.md` §3): the judgment that an updateless candidate has
"recovered BRIA where it should", because the maximal recovery domain for the extension
is undefined; and the judgment that a channel-dependent verdict (T4(i), T6(iii), T7) is
an advance rather than a conditional result, which depends on which commitment source
the maintainer holds candidates to.

The rest of this document defines the terms of the statement and gives the boundary
results that shaped them.

## 1. The objective and the two components

> What criterion, or small collection of criteria, should a computable agent combining
> logical induction and bounded inductive rationality satisfy, such that satisfying
> them would constitute a substantive advance in logical-induction-based decision
> theory?

A logical inductor is a computable market `P̄` over sentences of a theory `Γ` with a
computable deductive process `D̄` such that no efficiently computable (e.c.,
polynomial-time) trader exploits it (**PAPER**, Def. 3.0.1).  A boundedly rational
inductive agent is a sequence `ᾱ = (α^c_t ∈ DP_t, α^e_t ∈ [0,1])` of choices from finite
menus and estimates, facing rewards `r_t ∈ [0,1]` of the chosen option only, such that
(**PAPER**, Defs. 1–7) *no overestimation* `limsup_T (1/T) Σ_{t≤T} (α^e_t − r_t) ≤ 0` and
*coverage*: for every hypothesis `h` in a class `H` of e.c. maps `(history) ↦ (option,
promise)`, either `h` outpromises `ᾱ` (`h^e_t > α^e_t`) at finitely many `t`, or along the
rejection times the record `Σ_{t∈M, t≤T} (r_t − h^e_t)` on a test set `M` (rounds where
`α^c_t = h^c_t`, chosen by the agent) tends to `−∞`.  Counterfactual rewards are
undefined; the menu may depend on past choices; the criterion is myopic by design.
The agent may choose any subset of the matching rounds as the test set, so the record
most favourable to coverage keeps only the matching rounds where the reward falls short
of the promise; coverage quantifies over *every* e.c. hypothesis, adaptive and
time-varying promises included, so a check against fixed bidders never establishes it.

**Three registers.**  (i) *Learning from realized feedback*: claims about executed
options, settled by observation.  (ii) *Honoring a commitment*: a selection, once made,
is executed for its term.  (iii) *Evaluating a policy under logical or counterfactual
dependence*: a value assigned to an option not executed.  BRIA lives in (i); neither
component supplies (iii); (ii) comes from whatever commitment source a candidate
declares (§2, M3 and §6).  A result in one register is not a result in another.

**Architecture is not specified.**  A candidate has a belief component that publishes
a market and a decision component that chooses from a finite menu and observes the
realized score of its choice.  One market or two, one budget, an auction, published
claims, blocks, a particular commitment mechanism: none is required unless a
requirement below independently needs it, and a modular implementation whose prices
materially inform its decision learner can qualify.

## 2. Supporting milestones

### M1. Computable existence

`A` is computable and satisfies M2–M4 on every environment in a declared class `E`,
with the comparison classes named: e.c. traders for the market; the hypothesis class
`H` for the decision component — the e.c. maps of the history, and *market-relative*
(`H^P`: e.c. maps of the history and the published prices) where I1 is claimed.
*Assumptions.*  No `O(g)`-computable agent covers the `O(g)`-computable class (**PAPER**,
Thm 2) — a worst-case statement about the agent as a whole, which says nothing about its
runtime on a particular benchmark sequence (§7, provisional D3).  The market relative to
an observation stream is the oracle-relativized inductor, `PRIORITIES.md` item 91
(**EXT**).  *Compatibility.*  A logical inductor beside the paper's auction with a blind
class satisfies M1–M4 at once; §3 is what separates that from a synthesis.

### M2. LI recovery

(a) *Compatible component* — some logical inductor's prices are consistent with `A`'s
behaviour: **rejected**, vacuous.  (b) *Passive implication* — on `|C_k| = 1` for all
`k`, `P̄` satisfies the LI criterion relative to `D̄`.  (c) *Active implication* — on
every environment in `E`, `P̄` satisfies the LI criterion relative to `D̄` and the
observation stream, traders being allowed to bet on sentences about realized scores.
**Required in grade (c)**, (b) the declared fallback (relativization is item 91).

### M3. BRIA recovery, with its domains

*Statement.*  There are **witness estimates** `e_k` — internal, or merely a
mathematical object exhibited in the proof, public only where the candidate says so —
such that `(c_k, e_k)` satisfies Defs. 1–7 with respect to `H` on the **recovery
domain** `E_rec ⊆ E`, at the candidate's declared **scored unit** (a single action, or
an executed continuation).  Acceptance tests are the paper's consequences on `E_rec`:
the guaranteed-option theorem (**PAPER**, Thm 3), the random-reward theorem (**PAPER**,
Thm 4), and for continuations the block form of Thm 3 (`wiki/Continuation-BRIA.md` §6
under the bounded-record hypothesis).

*The four domains a candidate states.*

1. **`E`, the general class** on which the candidate's own criterion is defined and
   M1, M2, M4 hold.  The BRIA criterion itself is defined for every reward sequence
   (**PAPER** §2), so nothing forces `E` below "all sequences".
2. **`E_rec`, the recovery domain.**  For the **updateful endpoint** the recommended
   choice is `E_rec = E` at the declared unit: action-level (or unit-level) BRIA
   recovery everywhere, with the boundary results of §4 as its known costs — in
   particular P1′, which shows that unit-level recovery on the full class forbids
   paying in per-round counterfactual mugging.  A candidate that behaves differently
   on such environments has, by P1′, restricted `E_rec`, and says on which environments
   and by what rule.
3. **The continuation or block specialization**, if used (§6): the unit is a block,
   `E_rec` is stated at block granularity, and the commitment source is an external
   execution contract.
4. **The updateless extension's recovery restriction** (§7, A2).  An agent with
   policy-level guarantees cannot be a BRIA at unit level on the environments P1′
   covers.  The domain on which it *should* recover BRIA — where the local and the
   policy-level demands coincide — is **not defined here, and its definition is a
   specification question this round records rather than answers**.  Two candidate
   definitions are rejected with witnesses: "rewards independent of the agent's
   choices" is too small (it excludes every decision problem); "rewards a function of
   the history and the current choice only" (`E_hist`) is too large — per-round
   counterfactual mugging with a frequency predictor lies in `E_hist`, and there P1′
   forces refusal while paying is policy-optimal, so `E_hist` does not make the two
   demands coincide.  The missing object is a property of the reward process that
   makes myopic optimality and policy optimality agree, stated without reference to the
   candidate.  Until it exists, an updateless candidate's recovery claim cannot be
   judged as "recovered BRIA where it should" — only as "recovered BRIA on the domain
   it declares".

*What the criterion does and does not force* (**FIX** `test_cm`).  Global
no-overestimation *alone* permits cross-subsidy (§4); coverage over the full class
removes it where the subsidizing reward is efficiently trackable (P1′).  Coverage does
**not** by itself require adaptive testing (§4, the fixed-schedule result is
conditional).

**Required**, with all four domains stated.

### M4. Accountability for unchosen alternatives

Coverage read as an obligation: every `h ∈ H` that outpromises infinitely often is
executed on a test set along which its record diverges.  It is defensible without
assuming exploration is safe or informative: a test is the chosen option, not an
exploration step distinct from choice (a predictor reading the agent's choices sees a
choice; a predictor with another access model is a different environment); a test is
informative by construction (the claim is about the executed option from the actual
history, `CONTINUATION_HYPOTHESES.md` §3 of the continuation-BRIA round); and a test is
only as safe as the menu — the named assumption is **no traps in the menu** (**EXT**;
Kosoy's trap problem is placed, not solved).  It does not deliver any improvement no
hypothesis in `H` can claim.  **Required**, with the menu assumption named.

### M5. Temporally extended decisions and the commitment source

Three sources of commitment, which a candidate declares because a benchmark verdict
depends on which is in force: an **external execution contract** (the environment
executes the selected continuation for a term; the specialization's source), a
**self-entered contract** (entering such a contract is itself a scored option; in the
specialization, bidder-chosen horizons, **OPEN**), and **self-stability without
enforcement** (the agent's future decisions keep the plan with nothing holding them;
nothing in M1–M4 delivers it; the Bayesian tiling theorems for updateless agents,
Demski 2025, are the nearest results with no bounded analogue, **OPEN**).  Under an
external contract, M3–M4 at the contract's granularity give continuation competence;
regret decomposes as `SHIFT + SLACK + LEARN` with only `LEARN` the criterion's
(`wiki/Continuation-BRIA.md` §7); regret against all legitimate policies is false.
**Required only as a declaration** for the endpoint; the guarantees are the
specialization's.

### M6. Logical learning

(i) A stronger deductive process or a longer market run reaches the decision component
without changing `H`, which is what `H^P` gives; (ii) the market's prices on the
settled scores of the active trajectory obey LI's guarantees (M2(c)).  A score for an
earlier decision in the light of a later fact needs register (iii) and is not
required.  **Required as design choices (i), (ii).**

## 3. Integration: the obligation against split-brainness

The central ambition is that the agent's logical assessments and the reasoning
governing its choices form one jointly accountable process.  This is not the demand
that every estimate equal an LI expectation; the quantities have different roles and
timing.  A candidate exhibits five things and proves at least the results the
acceptance statement names.

**What a candidate exhibits.**

1. *Semantics and timing* of every forecast, estimate and decision assessment it uses,
   in the order of §5: pre-selection forecasts `F_k(c)` (guide selection), witness
   estimates `e_k` (held to no overestimation), any post-selection forecast `F⁺_k`
   (about a variable that will settle), and which are public.
2. *The channel by which logical information enters decisions*: for a market-relative
   class, hypotheses read prices; for another architecture, the stated map from
   `P̄` to the decision component's inputs.
3. *How claims about decisions are held accountable when the agent controls which
   decisions occur*: which test sets are used, whether they are recognizable from
   public data, and which feedback theorem, under which timing and generability
   assumptions (§5), applies to them.
4. *A formal interaction result* — one of I1–I3 below, proved.
5. *Why this is more than two components side by side*: which of I1–I3 the
   side-by-side witness of M1 fails, and why.

**Three achievements, not interchangeable.**

- **I1 — market information improves decision performance.**  A theorem: on a stated
  environment class, M3 over `H^P` yields an average score that M3 over any blind class
  of the same decision-component runtime cannot, with explicit accounting of the
  computation each side spends (T10).  *Necessary strength*: proved, with the
  deductive process deciding the relevant sentences before the decision and the
  separation stated against the decision component's runtime, not the agent's.
  *Does not establish*: any relation between estimates and forecasts, nor the exclusion
  of any self-confirming failure.  **Required.**
- **I2 — belief and decision assessments satisfy a compatibility relation.**  In its
  **established** form W1 (§5): whole-sequence claims do not on average exceed
  post-selection forecasts.  In its **strong** form (§5): agreement on every
  `P`-generable weighting.  *Does not establish*: performance — a compatible pair can
  agree on a poor score.  **Required in the W1 form; the strong form is a further
  target and does not monopolize integration.**
- **I3 — decision accountability prevents a specified self-confirming belief–action
  failure.**  On the belief-disagreement environment A1 (§7), where the outcome of a
  choice depends on the agent's own published forecasts about it, the candidate provably
  reaches the good fixed point from every belief state consistent with M2.  *Necessary
  strength*: for every satisfying agent, or for the designated construction with the
  criterion refinement stated.  *Does not establish*: I1 or I2.  **Required**, and it
  is the advance A1.

**What is dissolved.**  Self-confirming pessimism about a *claimable* option — an
option `b` some e.c. hypothesis promotes — is already excluded by M4 on the full class:
the constant bidder `(b, 1)` is in `H` whether or not anything knows its promise is
right, it outpromises until tested, and its tests refute the pessimism (T2).  The first
pass's D1, which assumed no hypothesis promotes `b`, contradicted the class and is
withdrawn as a diagnostic; the surviving forms of the belief–action failure are the
identification problem (I1: which of many options is good is hard to compute) and the
self-referential one (I3: the outcome depends on the agent's forecast of it).

## 4. Boundary results

Stated at the strength proved; each shaped a requirement above.

**P1′** (**DERIVED** from **PAPER** Defs. 1–7; **FIX** `test_cm`).  Per-round
counterfactual mugging: heads rounds have a single option paying `1` iff the predictor
predicts paying; tails rounds offer `pay` at `0` and `refuse` at `1/2`.  *Hypothesis*:
the heads reward is an e.c. function of the history (true for a predictor reading the
past paying frequency; true for a predictor reading the agent's policy when its
prediction is eventually constant).  *Conclusion*: every BRIA covering the e.c. class
pays on a density-zero set of tails rounds.  *Proof*: the tracker `h₁ = (noop, ρ_t)` on
heads, `ρ_t` the heads reward, `(pay, 0)` on tails, has a nonnegative record on every
test set, so coverage forces `α^e_t ≥ ρ_t = r_t` on all but finitely many heads rounds;
the refuser `h₂ = (refuse, 1/2)` on tails, `(noop, 0)` on heads, likewise forces
`α^e_t ≥ 1/2` on all but finitely many tails rounds; no overestimation then gives
`(1/2)·#{paying tails rounds ≤ T} ≤ o(T)`.  ∎  *Strength*: the hypothesis is
sufficient, not shown necessary — where the heads reward is not e.c.-trackable, `h₁`'s
record diverges on its tests and the argument fails, and whether some other e.c.
hypothesis excludes the cross-subsidy there is **OPEN**.  *Scope*: one environment
family; it does not establish a universal obstruction for every cross-round commitment.
*What it shows*: unit-level BRIA recovery on the full class and paying in this
environment are incompatible, so an agent that pays has restricted `E_rec` (M3).

**The cross-subsidy witness** (**FIX** `CrossSubsidy_NoOverestimationOnly`).  The agent
that pays on all but a density-zero set of tails rounds, estimating `1/2` on tails and
`0` on heads, has cumulative overestimation `≤ 0` on every prefix and is refuted by
`h₁` (least record `0`, outpromised on every heads round).  Content: global
no-overestimation is a whole-sequence average and permits cross-subsidy; coverage of an
e.c. tracker is what localizes it.

**The conditional fixed-schedule obstruction** (**DERIVED**; **FIX** `FixedSchedules`,
`test_two_boxing_agent_with_a_fixed_schedule_is_not_a_bria`).  Let an agent take option
`b` only on an e.c.-recognizable schedule `S`, and let its estimate be below `1` on
infinitely many rounds outside `S`.  Then it is not a BRIA: the hypothesis promising `1`
for `b` off `S` and `0` for an option the agent does not take on `S` is never matched,
has record `0` on every test set, and outpromises on every off-`S` round where the
estimate is below `1`.  Contrapositive: a fixed-schedule agent is a BRIA only if its
estimate is `1` on all but finitely many off-schedule rounds — and then, by no
overestimation, its realized reward averages `1` there.  *Withdrawn*: "fixed test
schedules are never BRIAs" (an environment where every option pays `1` and the agent
estimates `1` is the counterexample, **FIX** `test_estimate_one_everywhere_is_not_attacked`)
and "all valid testing must be adaptive" (not proved; the paper's auction is adaptive
and sufficient, which is all that is known).

**The tentative-troll construction result** (**FIX** `TentativeTroll`).  A troll that
fires iff a published estimate on a crossing round is below `1`: the paper's auction
is a BRIA on every reward sequence (**PAPER** Thm 1) and is stuck at `1/2`; the agent
that always crosses at estimate `1` is a BRIA at `1`; a full-confidence bidding rule
crosses.  Applies only to candidates that publish estimates; the criterion is silent
(no option guarantees a reward, so Thm 3 does not apply).

## 5. Belief–decision compatibility: status

**Timing.**  Within a decision: (1) the market publishes prices, including forecasts
`F_k(c)` for each option; (2) hypotheses read them and emit `(recommendation, promise)`;
(3) the decision component selects `c_k`, with `e_k` its witness estimate; (4)
optionally a later market state publishes a post-selection forecast `F⁺_k` of the
realized score of the selected option, the selection being by then in the stream; (5)
execution; (6) settlement of `Ĝ_k`.  A forecast at (1) guides selection; a forecast at
(4) is about a variable that will settle, formed after learning the selection.

**Semantics.**  `Ĝ_k` is the realized score of the selected option.  For an option `c`
not selected at `k` there is no settlement; the only settling variable indexed by `c`
is `X^c_k := Ĝ_k` on decisions where `c_k = c`, undefined elsewhere.  A forecast `F_k(c)`
on a decision where `c` is not selected is held to nothing by any feedback theorem.

**Feedback theorems, when they apply.**  `thm:wubaff`/`thm:wubexp` (**PAPER**, with the
deferral condition the pinned formalization records) control the market's expectation
of a variable, weighted by a `P`-generable weighting `w̄`, against the settled values.
The weighting is used by a trader at the time of the forecast, so it must be an e.c.
function of what the market has published *by then*.  Consequences: (a) a weighting
built from the selection at `k` is available for forecasts made after the selection is
in the stream (`F⁺_k`), and for a forecast made before it (`F_k(c)`) only if the
selection is predictable from the market state at forecast time; (b) publicity of the
selection makes "c selected at k" recognizable, but an *internal* test set `M_h ⊆`
matching rounds is recognizable only if the candidate publishes its membership or uses
the maximal matching set; (c) the settled value must be computable within a deferral
`f` from the decision, which the scored unit's end supplies.  A candidate names, for
each feedback theorem it invokes, the forecast's timing, the weighting's generability,
and the deferral.

**W1 — established** (**DERIVED**).  Under M2(c) relative to the stream, a
post-selection forecast `F⁺_k` published as a market state after the selection, and
settlement within a computable deferral: `limsup_K (1/K) Σ_{k≤K} (e_k − F⁺_k) ≤ 0`, from
no overestimation and `thm:wubaff` on the trivial weighting.  One-sided, unweighted.

**The strong form — proposed.**  For every `P`-generable divergent weighting `w̄`,
`Σ_k w_k (e_k − F⁺_k) / Σ_k w_k → 0`.

**Status of the implication "M2(c) and M3 imply the strong form": unresolved.**  The
first pass's derivation is invalid: its upper half needs no-overestimation on the
weighting (global no-overestimation gives none — the cross-subsidy witness), its lower
half used bidders promising the market's forecast, which are refuted when the forecast's
errors on their tests have vanishing average but divergent sum (repaired by the
`ε`-shifted bidders of **PAPER** Thm 4), assumed the tests recognizable from the prices
(only under the publicity conditions above), and used a forecast for an unselected
option as if it settled (it does not: this is the first obstacle of Garrabrant 2017,
untaken actions unobservable, relocated to option forecasts).  No countermodel to the
implication has been exhibited; a candidate may still prove it under added hypotheses
(weighted no-overestimation; a sound market-reading bidder for the selected option on a
recognizable test set), and item 105 asks for either the proof or the countermodel.
**Three statements, separated**: the strong form as a proposed requirement; the
implication as an unproved conjecture with a failed derivation; W1 as what is
established.

## 6. The continuation-BRIA specialization

One route through §2, not the target.  At block `k` of a *system-supplied* schedule the
agent publishes `P_k` and selects from a finite menu of continuations a pair
`(c_k, e_k)`; the system executes `c_k` for `m_k` steps through the constitutional
wrapper; `G_k` is the realized block score (`wiki/Continuation-BRIA.md` §2).  M3
instantiated: the duration-weighted criterion of §4 there over `H^P`, with existence
under negligible subsidy iff the schedule is non-dominant (`m_K / Σ_{k≤K} m_k → 0`,
**DERIVED** there); with `m_k ≡ 1` it is Defs. 1–7 verbatim.  M5 instantiated: an
external execution contract; continuation competence at system-scheduled horizons;
bidder-chosen horizons **OPEN**.  Choices it makes that §2 does not: system-scheduled
blocks; a **published** estimate (with the tentative-troll cost); the opening-subsidy
auction; the gate as the menu.  A candidate may reject any of them.

## 7. Advance diagnostics

An **advance** is a result on a recognized obstruction of logical-induction decision
theory under a matched environment and information structure: the same predictor
access, the same menu, no new oracle, no externally supplied commitment channel, no
restriction of the comparison class beyond what the original allowed.  A supplied
channel, contract, oracle or restricted menu can support a legitimate conditional
result and is stated as one; it is not an advance.  One-shot success is not required
where a repeated setting preserves the obstruction and the guarantee can see the
improvement.

### Well-posed

**A1 — the belief-disagreement troll (I3).**  *Obstruction matched*: Troll Bridge's
"punished for the reason", with the reason the realized register can see — acting
against one's own published forecasts (Demski 2019; the LIDT variant, where the troll
reads which clause fired).  *Environment*: options `stay` (`1/2`), `cross` (`1` unless
the troll fires, then `0`); the troll fires iff the action differs from the argmax of
the market's published pre-selection forecasts `F_k(cross)`, `F_k(stay)`.  *Access*: the
troll reads the action and the prices the belief component publishes anyway by M2's
type — no new channel.  *Timing*: forecasts published, choice, outcome.  *Comparison
class*: the full e.c. class, market-relative.  *Success condition*: crossing with
density `1` from **every** initial market state consistent with M2 (including one that
forecasts crossing below staying).  *Mode*: asymptotic density, sure.  *For whom*: every
satisfying agent, or the designated construction with the criterion refinement stated.
*Why not delivered*: two fixed points satisfy M1–M4 — crossing with the market
forecasting `1` for it, and staying with the market forecasting `0` for crossing, the
latter self-consistent because every test of crossing happens while the forecast is
low, the troll fires, and the market's forecast on tested rounds is confirmed at `0`
(**FIX**-shape as T3(e); the fixture does not simulate a market).  *Negative control*: a
troll reading the action only (T3(b)), where coverage crosses.  *Status*: proposed
acceptance target; nothing here passes it.

**A2 — per-round counterfactual mugging under the policy predictor (ideal
extension).**  *Obstruction matched*: no logical updatelessness (Garrabrant 2017,
obstacle 2), in the repeated realized-feedback setting with the original access — the
predictor reads the agent's policy, unit scoring, no channel.  *Environment*: T6 per
round with access (i).  *Success condition*: paying with density `1` **and** BRIA
recovery on the candidate's declared recovery domain (M3, domain 4), which by P1′
excludes this environment.  *Mode*: asymptotic density, sure.  *For whom*: the
designated construction under its stated criterion.  *Why not delivered*: P1′ — every
BRIA on the full class refuses; policy selection over LI (Demski 2017) claims it with
no theorem.  *Status*: proposed target, **blocked as an acceptance judgment** by the
undefined recovery domain (§2, M3): a candidate can be scored on this row but cannot
yet be certified as having recovered BRIA "where it should".

### Provisional (not acceptance tests)

- **D3 — bounded-simulation Newcomb.**  The predictor simulates the agent's algorithm
  for `g(n)` steps and defaults to two-boxing.  Distinct from Agent Simulates Predictor
  (Slepnev 2011, credited to Drescher: a proof-bounded predictor reasoning about the
  agent's procedure; the agent can simulate the predictor); equivalence or preservation
  of its decisive obstruction is **not** established, and the first two passes'
  inference that the synthesis two-boxes because its decision is above `O(g)` is
  withdrawn — Thm 2 is a worst-case statement and says nothing about the agent's actual
  runtime on the benchmark sequence or the frequency with which the simulation
  finishes.  A success condition that is meaningful: the predictor predicts one-boxing
  **and** the agent one-boxes, jointly with density `1`, under the assumption that the
  simulation, when it finishes, is faithful; one-boxing frequency alone is not it (the
  predictor can default and leave the box empty).  Missing: the accounting of the
  agent's per-round runtime on the benchmark against `g(n)`.
- **D2 — the tentative troll as a criterion refinement.**  Applies only to candidates
  that publish estimates (§4); a refinement forcing crossing, with its cost in
  competence, would be a construction-level result.
- **The identification form of the untested-option failure**: subsumed by I1 (T10) and
  not a separate obstruction.

**Stronger ambitions** beyond both: S1 policy regret against recognizable, joinable
policies (item 86); S2 the counterfactual-dependence register; S3 randomization as a
menu option with a private source; S4 self-stability without enforcement; S5 an
exploration-safety certificate.

## 8. Registers of the requirements

| requirement | register | what is held fixed |
|---|---|---|
| M2, M6(ii) | epistemic (LI) | `D̄`, the stream |
| M3, M4, I1–I3, A1 | (i) realized feedback | the scored unit, the selection |
| M5 (external contract) | (ii) commitment | the selection, for the term |
| M5 (self-entered, self-stability), A2, S1 (`SHIFT`), S2 | (ii) across units / (iii) | a rollout evaluator, not supplied |

## 9. The acceptance checklist

1. **Type and declarations.**  A published market; a decision component with a finite
   menu and realized feedback; witness estimates exhibited (public or not, stated
   which); the scored unit; the commitment source (M5); the four domains of M3.
2. **M1** existence with `E` and both comparison classes stated.
3. **M2(c)** relative to the stream, or M2(b) declared, and T0 passed.
4. **M3** on `E_rec` at the unit; Thm 3/Thm 4-form consequences; the boundary results
   of §4 respected (no unconditional adaptivity claim; the fixed-schedule condition).
5. **M4** with the menu-safety assumption named.
6. **Integration** (§3): the five exhibits; I1 proved on a stated class with its
   accounting; I3 proved on A1; I2 at least as W1, the strong form only if proved with
   §5's timing and generability conditions.
7. **The suite**: recovery and integration rows passed under their assumptions;
   construction-level rows reported; every negative control reported; for each row the
   access model, the scored unit and any supplied channel, contract, oracle or menu
   restriction stated against the primary source.
8. **The advance**: which well-posed diagnostic, under the matched environment, and
   why the existing guarantees did not already deliver it.
9. **The extension, if claimed**: A2 with the declared recovery domain, and the
   statement that the domain question of M3 is open.
10. **Not shown**: the candidate's own list against §0, with the registers of §8.
