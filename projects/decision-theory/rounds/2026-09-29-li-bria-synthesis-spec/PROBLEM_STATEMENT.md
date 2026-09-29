# The LI/BRIA synthesis: objective, requirements, acceptance criteria

Labels: **PAPER** (a theorem of arXiv:1609.03543 v5 or of TARK 2023 EPTCS 379 pp.
421–440, cited at its statement), **DERIVED** (follows from cited results by an argument
given here, hypotheses named), **FIX** (exact fixture in `tests/`, run by `tests/run.py`;
a finite prefix check against fixed bidders, never a proof of a quantified statement),
**CONJ** (conjectured), **EXT** (a contract the specification names and does not pay),
**OPEN**.  Names are provisional: *minimum credible synthesis*, *market-relative
hypothesis class*, *belief–decision compatibility*, *scoring granularity*, *lease
publicity*, *realized-feedback register*, *witness estimates*.

## 1. The objective

> What criterion, or small collection of criteria, should a computable agent combining
> logical induction and bounded inductive rationality satisfy, such that satisfying
> them would constitute a substantive advance in logical-induction-based decision
> theory?

**The two components at their exact statements.**  A logical inductor is a computable
market `P̄` over sentences of a theory `Γ` with a computable deductive process `D̄` such
that no efficiently computable (e.c., polynomial-time) trader exploits it (**PAPER**,
Def. 3.0.1).  A boundedly rational inductive agent is a sequence `ᾱ = (α^c_t ∈ DP_t,
α^e_t ∈ [0,1])` of choices from finite menus and estimates, facing rewards `r_t ∈ [0,1]`
of the chosen option only, such that (**PAPER**, Defs. 1–7) *no overestimation*
`limsup_T (1/T) Σ_{t≤T} (α^e_t − r_t) ≤ 0` and *coverage*: for every hypothesis `h` in a
class `H` of e.c. maps `(history) ↦ (option, promise)`, either `h` outpromises `ᾱ`
(`h^e_t > α^e_t`) at finitely many `t`, or along the rejection times the record
`Σ_{t∈M, t≤T} (r_t − h^e_t)` on a test set `M` (rounds where `α^c_t = h^c_t`, chosen
by the agent) tends to `−∞`.  Counterfactual rewards are undefined; the menu may depend
on past choices; the criterion is myopic by design (§2, §7 of the paper).  Two
consequences of the definition used throughout: the agent may choose any subset of the
matching rounds as the test set, so the record most favourable to coverage keeps only
the matching rounds where the reward falls short of the promise; and coverage quantifies
over *every* e.c. hypothesis, adaptive and time-varying promises included, so a check
against fixed bidders never establishes it.

**Three registers, kept apart throughout.**  (i) *Learning from realized feedback*:
claims about executed options, settled by observation.  (ii) *Honoring a commitment*:
a selection, once made, is executed for its term.  (iii) *Evaluating a policy under
logical or counterfactual dependence*: a value assigned to an option that is not
executed.  BRIA lives in (i); nothing in either component supplies (iii); (ii) is
supplied by whatever commitment source the specialization declares (§4).  A result in
one register is not a result in another.

## 2. General acceptance requirements

These are stated for any computable agent `A` with a *belief component* — a published
market `P̄` — and a *decision component* that chooses `c_k` from a finite menu `C_k` at
each decision `k` and observes the realized score `G_k ∈ [0,1]` of its choice.  A
decision may be a single action or an executed continuation; the requirements do not
fix which, and they do not require the agent to publish any number beyond its prices.
Estimates enter as **witness estimates**: a sequence `e_k` that may be internal, or
merely a mathematical object exhibited in the proof of G3, and is public only where the
specialization says so.

### G1. Computable existence

*Statement.*  `A` is computable and satisfies G2–G5 on every environment in a declared
class `E`, with the comparison classes named: e.c. traders for the market, and the
hypothesis class `H` for the decision component — at least the e.c. maps of the history,
and *market-relative* (`H^P`: e.c. maps of the history and the published prices) where
G4(a) is claimed.

*Excludes.*  Criteria met only by uncomputable agents.  *Assumptions.*  No
`O(g)`-computable agent covers the `O(g)`-computable class (**PAPER**, Thm 2); the market
relative to an observation stream is the oracle-relativized inductor, `PRIORITIES.md`
item 91 (**EXT**).  *Compatibility.*  A logical inductor beside the paper's auction with
a blind class satisfies G1, G2, G3, G5 at once; only G4 separates that from a
synthesis.  **Core.**

### G2. LI recovery

*Grades.*  (a) *Compatible component* — some logical inductor's prices are consistent
with `A`'s behaviour: **rejected**, vacuous.  (b) *Passive implication* — on `|C_k| = 1`
for all `k`, `P̄` satisfies the LI criterion relative to `D̄`.  (c) *Active implication* —
on every environment in `E`, `P̄` satisfies the LI criterion relative to `D̄` and the
observation stream, traders being allowed to bet on sentences about realized scores.
*Excludes.*  A market exploitable once decisions are in play.  *Standpoint.*  (c) is
relative to the stream through the relativized deductive process (item 91).
**Core in grade (c)**, (b) the declared fallback.

### G3. BRIA recovery

*Statement.*  There are witness estimates `e_k` such that `(c_k, e_k)` satisfies Defs.
1–7 with respect to `H` on every environment in `E`: no overestimation and coverage of
every `h ∈ H`, with the quantifiers of §1.  Acceptance tests are the paper's
consequences: the guaranteed-option theorem (**PAPER**, Thm 3), the random-reward
theorem (**PAPER**, Thm 4), and for continuations the block form of Thm 3
(`wiki/Continuation-BRIA.md` §6 under the bounded-record hypothesis).

*Excludes.*  Persistently claiming more than is realized; ignoring an e.c. hypothesis
that keeps promising more.  And, by a direct argument (§3), cross-round commitment at
the criterion's own granularity whenever the subsidizing reward is efficiently
trackable.

*What the criterion does and does not force* (**FIX** `test_cm`).  Global
no-overestimation *alone* permits cross-subsidy: the agent that pays on all but a
density-zero set of tails rounds, estimating `1/2` on tails and `0` on heads, has
cumulative overestimation `≤ 0` on every prefix.  Coverage over the full class removes
the permission: the hypothesis `(noop, 1)` on heads, `(pay, 0)` on tails outpromises it
on every heads round with a least record of exactly `0`, so it is not a BRIA
(`test_heads_tracker_breaks_coverage`, the regression for the first pass's error, which
checked two refusing bidders and no heads bidder).  Fixed test schedules are never BRIAs
(**DERIVED**, **FIX** `FixedSchedules`): against an agent that tests option `b` only on
an e.c.-recognizable schedule, the hypothesis promising `1` for `b` off the schedule
and `0` for the agent's option on it is never matched, has record `0`, and outpromises
forever.  Test sets must respond to outpromising, which is what the paper's auction
does.

**Core**, with the class named.

### G4. Interaction

The requirement that separates a synthesis from two components side by side.  Two
forms, either sufficient, both stated so that what is claimed is a theorem and not an
architecture.

(a) **Market-informed decision guarantee.**  G3 holds with the market-relative class
`H^P`, and there is an environment class in `E` on which G3 over `H^P` yields an average
score that G3 over any blind class of the same runtime cannot — a theorem, not a
fixture (T10 in `TEST_SUITE.md` states what it must be).  This is satisfied by a
modular architecture whose prices materially inform its decision learner; modularity is
not what is excluded.

(b) **Belief–decision compatibility** (R4 of the first pass), audited in §5.  Its
established form is weak and one-sided (§5, W1); its strong form is a proposed
requirement whose derivability from G2–G3 fails on the stated gaps.  A candidate
claiming (b) proves the strong form for its construction; a countermodel to
derivability is information about the specification, not a passing synthesis.

**Core** in the form: at least one of (a), (b) proved for the candidate.

### G5. Accountability for unchosen alternatives

*Statement.*  Coverage read as an obligation: every `h ∈ H` that outpromises infinitely
often is executed on an infinite test set along which its record diverges — tests
chosen in response to outpromising, by §2 G3's fixed-schedule lemma.

*Defensible without assuming exploration is safe or informative.*  A test is the
chosen option, not an exploration step distinct from choice, so a predictor reading the
agent's public choices sees a choice and not a flag (the explored-versus-deliberate
distinction of Garrabrant 2017 does not arise *for that access model*; a predictor with
another access model, T3(d), is a different environment).  A test is informative by
construction: the claim is about the executed option from the actual history
(`CONTINUATION_HYPOTHESES.md` §3 of the continuation-BRIA round).  A test is only as
safe as the menu: the named assumption is **no traps in the menu**; a trap promoted by
some hypothesis is tested at least once (**EXT**; Kosoy's trap problem is placed, not
solved).

*What it does not deliver.*  Any improvement that no hypothesis in `H` can claim —
counterfactual improvements (register (iii)), and improvements recognizable only by
computations above the class.  **Core** (it is G3's coverage clause with the menu
assumption named).

### G6. Temporally extended decisions and commitment

Three sources of commitment, kept apart because a benchmark verdict depends on which is
in force:

- **External execution contract.**  The environment or system executes the selected
  continuation for a term; the agent's choice is the selection.  This is what the
  specialization of §4 supplies, and what T6/T7's block verdicts assume.
- **Self-entered contract.**  The agent chooses, among its options, to enter such a
  contract; the contract is then external but the entry is a decision the criterion
  scores.  Representable in the specialization as an option whose execution is a
  longer continuation, subject to the schedule (§4, open).
- **Self-stability without enforcement.**  The agent's own future decisions keep the
  earlier plan with nothing holding them to it.  Nothing in G1–G5 delivers this; the
  Bayesian tiling theorems for updateless agents (Demski 2025) are the nearest results
  and have no bounded-agent analogue (**OPEN**).

*Statement.*  Where an external contract is in force, the requirements G3–G5 apply at
the contract's granularity and yield continuation competence; regret against a
comparator class decomposes as `SHIFT + SLACK + LEARN` with only `LEARN` the
criterion's (`wiki/Continuation-BRIA.md` §7); regret against all legitimate policies is
false.  **Core** for the first source at the declared granularity; **unresolved** for the
second (the allocation of duration); **open** for the third.

### G7. Logical learning

*Statement.*  (i) A stronger deductive process or a longer market run reaches the
decision component without changing `H`, which is what `H^P` gives; (ii) the market's
prices on the settled scores of the active trajectory obey LI's guarantees (G2(c)), so
a fact discovered late moves every later market-reading claim.  *Missing.*  A score for
an earlier decision in the light of a later fact needs a value for the option not taken
at that decision — register (iii), no definition here.  **(i), (ii) core as design
choices; the hindsight form unresolved**, with the missing object named.

## 3. The conflict: action-level BRIA against binding policy commitments

At the paper's granularity (unit rounds), in repeated counterfactual mugging (heads:
single option paying `1` iff the predictor predicts paying; tails: `pay` at `0`,
`refuse` at `1/2`).

**Proposition P1′** (**DERIVED** from **PAPER** Defs. 1–7; **FIX** `test_cm`).  Suppose
the heads reward is an e.c. function of the history (true for a predictor reading the
past paying frequency; true for a predictor reading the agent's policy when the
prediction is eventually constant).  Then every BRIA covering the e.c. class pays on a
density-zero set of tails rounds.  Proof.  The tracker `h₁ = (noop, ρ_t)` on heads with
`ρ_t` the heads reward and `(pay, 0)` on tails has a nonnegative record on every test
set, so coverage forces `α^e_t ≥ ρ_t = r_t` on all but finitely many heads rounds.  The
refuser `h₂ = (refuse, 1/2)` on tails, `(noop, 0)` on heads, has a nonnegative record
on every test set, so coverage forces `α^e_t ≥ 1/2` on all but finitely many tails
rounds.  No overestimation then gives `Σ_{t≤T} (α^e_t − r_t) ≥ (1/2)·#{paying tails
rounds ≤ T} − O(1) ≤ o(T)`.  ∎  The same argument with Thm 3 (option `(noop, refuse)`,
lower bound `(ρ_t, 1/2)`) gives the average form.  Paying is better on average (`1/2`
against `1/4` when the predictor reads the policy), and the criterion excludes it
**by itself**: no compatibility requirement is used.

**What P2 showed, corrected.**  The cross-subsidy witness of the first pass satisfies
global no-overestimation and is refuted by `h₁`.  Its residual content: no
overestimation *alone* is a global average and cannot see a subsequence; coverage over
trackers is what localizes it.  Where the subsidizing reward is **not** e.c.-trackable —
a heads reward that flips unpredictably for every e.c. function of the history — `h₁`'s
record diverges on its tests, coverage is satisfied by refutation, and no fixed bidder
excludes the cross-subsidy; whether some adaptive e.c. hypothesis does is **OPEN**.  So
the per-round obstruction follows from BRIA itself exactly on the environments where the
cross-round payoff is efficiently trackable, which includes every predictor in
`TEST_SUITE.md` T6.

**The first pass's conclusion is retracted.**  The conflict is not "exactly between
belief–decision compatibility and commitment"; it is between action-level coverage of
the full class and any commitment whose payoff accrues outside the scored unit.

**Resolution, declared.**  Score at the granularity at which the commitment pays: a
unit containing both branches, with the predictor reading the unit's published
continuation (**FIX** `BlockScoring.test_lease_predictor_pays`: the paying
continuation's claim `1/2` is sound, refusing's is `1/4`).  This changes the scored unit
and the information held fixed — the contract and the published selection — and says
so; the comparator class is unchanged.  It leaves out commitments paying outside any
unit — the one-shot problem, and a predictor reading only past units (**FIX**
`test_lagging_predictor_refuses`).  Those are registers (iii) and (ii)-across-units.

## 4. The continuation-BRIA specialization

The instantiation the repository already has, marked as one way to meet §2 and not as
the definition of the target.

- **Type.**  At block `k` of a *system-supplied* schedule the agent publishes `P_k` and
  selects from a finite menu of continuations a pair `(c_k, e_k)`; the system executes
  `c_k` for `m_k` steps through the constitutional wrapper; `G_k` is the realized
  block score (`wiki/Continuation-BRIA.md` §2).  The estimate is **published** — a
  modelling choice with a known cost (T3(d)) — and the commitment source is the
  **external execution contract** of G6.
- **G3 instantiated.**  The duration-weighted criterion of `wiki/Continuation-BRIA.md`
  §4 over `H^P`; with `m_k ≡ 1` it is Defs. 1–7 verbatim.  Existence with negligible
  subsidy iff the schedule is non-dominant, `m_K / Σ_{k≤K} m_k → 0` (**DERIVED** there).
- **G4 instantiated.**  (a) with the class `H^P`; (b) in the form of §5 with the
  post-selection forecast.
- **G6 instantiated.**  Continuation competence at system-scheduled horizons; the
  self-entered contract is bidder-chosen horizons (**OPEN**, §9 there).
- **What the specialization fixes that the general target does not.**  System-scheduled
  blocks; published claims; the auction's opening-subsidy timing; the gate as the menu.
  A candidate may reject any of these and still meet §2.

## 5. Belief–decision compatibility, audited

**Timing.**  The order within a decision: (1) the market publishes prices, including
forecasts `F_k(c)` for each option `c ∈ C_k`; (2) hypotheses read them and emit
`(recommendation, promise)`; (3) the decision component selects `c_k` (and, in the
specialization, publishes `e_k`); (4) optionally the market publishes a post-selection
forecast `F⁺_k := E_k(Ĝ_k | c_k)` of the realized score of the selected option; (5)
execution; (6) settlement of `Ĝ_k`.  A forecast at (1) guides selection; a forecast at
(4) is about a variable that will settle.  Compatibility compares claims with (4).

**Semantics.**  `Ĝ_k` is the realized score of the selected option, settled at (6).  For
an option `c` not selected at `k`, "its score at `k`" has no settlement; the first pass
wrote `Ĝ_k(c)` for it and thereby assumed the counterfactual semantics the register
distinction forbids.  The only settling variable indexed by `c` is `X^c_k := Ĝ_k` on the
decisions where `c_k = c`, undefined elsewhere; a forecast `F_k(c)` on a decision where
`c` is not selected is held to nothing by any feedback theorem.

**R4, strong form (proposed requirement).**  For every `P`-generable divergent
weighting `w̄`, `Σ_k w_k (e_k − F⁺_k) / Σ_k w_k → 0`, both sides being about the
selected option after selection.

**The five gaps in the first pass's derivation, and their status.**

1. *Subsequence gap.*  Global no-overestimation bounds the whole-sequence average of
   `e_k − Ĝ_k`; on a `P`-generable weighting it bounds nothing (the cross-subsidy is the
   witness).  What would establish weighted no-overestimation: coverage of a tracker
   whose promise equals the realized score of the agent's *own* choice on that
   weighting — available exactly when that score is an e.c. function of public data
   (single-option rounds; trackable predictors), as in P1′.  In general **OPEN**, and a
   candidate that needs it states it as a hypothesis ("weighted no-overestimation").
2. *Cumulative-loss gap.*  A bidder promising the market's forecast is refuted when the
   forecast's errors on its tests have vanishing average but divergent sum (errors of
   order `−1/√k`).  Repair: the `ε`-shifted bidders `(c, F_k(c) − ε)` for rational `ε`,
   whose record is `Σ (Ĝ − F + ε) ≥ ε·#tests − o(#tests)` under average unbiasedness on
   the tests — the device of **PAPER** Thm 4.  The repaired conclusion is a `−ε` bound,
   not equality.
3. *Computational-access gap.*  The auction's round is `O(g q)`-computable, above the
   e.c. class and above the traders, so its selection, test sets and rejection sets are
   not e.c. functions of the prices.  Repair: **publicity** — the selection is an
   observation, so "c selected at k" is an e.c. function of the stream and every
   weighting built from it is `P`-generable relative to the stream, given the
   stream-relative inductor (item 91).  Without publicity, no feedback theorem applies to
   the tests, and the gap stands.
4. *Semantic gap.*  The lower half used a sound promise for every e.c. selector `c`
   from the market's forecast `F_k(c)`.  On decisions where `c` is not selected, `F_k(c)`
   settles against nothing, so `(c, F_k(c) − ε)` is sound on its tests and yet may
   outpromise on every decision where `c` is not selected while its record stays
   bounded (it has no tests there).  Coverage then forces the claim `e_k ≥ F_k(c) − ε`
   cofinitely — or forces the agent to select `c` until its forecast is corrected — but
   the market may forecast `c` highly on exactly the decisions where it is not selected,
   since the selection follows the forecast: this is Garrabrant's first obstacle
   (untaken actions are not observable) relocated from conditional expectations to
   option forecasts, and G5 does not remove it because the bidder's promise on untested
   decisions is held to nothing.  **Not derivable** as stated; the strong lower half is
   a proposed requirement.
5. *Timing gap.*  Resolved by the order above: the strong form is about `F⁺_k`; the
   guiding forecasts `F_k(c)` are what hypotheses read.

**Three statements, separated.**

1. *R4 as an independently proposed requirement*: the strong form above.  **Stronger
   optional target**, with the semantics of this section.
2. *R4 as a conjectured consequence of G2(c) and G3*: **refuted as a derivation** by gaps
   1, 3 and 4; **CONJ** only under the added hypotheses weighted no-overestimation,
   publicity with the stream-relative inductor, and a sound market-reading bidder for
   the selected option — the last being what the obstacle denies in general.
3. *What is established* (**DERIVED**, hypotheses named).  **W1**: under G2(c) relative
   to the stream, the post-selection forecast `F⁺_k` published as an observation, and
   `Ĝ_k` settling within a computable deferral, the *whole-sequence* averages satisfy
   `limsup (1/K) Σ_{k≤K} (e_k − F⁺_k) ≤ 0` — from no overestimation and unbiasedness
   from feedback (**PAPER** `thm:wubaff` with the deferral condition the pinned
   formalization records) on the trivial weighting.  One-sided, unweighted; it says the
   agent's claims do not on average exceed its own market's post-selection forecasts,
   and nothing about subsequences or about the lower direction.

**Consequence for the acceptance checklist.**  A candidate claiming G4(b) proves the
strong form for its construction (with the timing and semantics of this section); a
candidate claiming only W1 has met a weaker statement and says so; a countermodel to
derivability revises this section and passes nothing.

## 6. Two levels of achievement, and the minimum credible synthesis

**Level 1 — a substantive synthesis theorem.**  A computable agent for which G1, G2(c)
(or (b) declared), G3 with its class named, G5 with menu safety named, and at least one
of G4(a) as a theorem or G4(b) in its strong form are proved, with the criterion-level
rows of `TEST_SUITE.md` passed and the construction-level rows reported.  This is the
**minimum credible synthesis**.  It establishes one computable agent whose beliefs are
a logical inductor on the active trajectory, whose realized-score learning is bounded
inductively rational against the full efficiently computable class, and in which the
market's information provably changes what the decision learner achieves.  It leaves
open every one-shot verdict; logical counterfactuals; commitment outside the scored
unit; `SHIFT` and `SLACK`; exploration safety beyond the menu; randomization against
adversarial predictors; equilibrium selection (T3(e), T9); rates.

**Level 2 — an advance on a recognized LI decision-theory obstacle.**  A result that
addresses one existing difficulty *under a matched environment and information
structure* — the same predictor access, the same menu, no new oracle, no externally
supplied commitment channel, no restriction of the comparison class beyond what the
original allowed — and whose improvement is visible to the proposed guarantee.  Level 2
is not required for Level 1 and is what would make the synthesis an advance in decision
theory rather than a synthesis theorem.  Candidate diagnostics, each with its success
condition and why existing guarantees do not deliver it:

- **D1 — untested optimism (Garrabrant's obstacle 1, block form).**  Environment: an
  option `b` whose value is decided by logic (T10's shape) and a market whose forecast
  for `b` is low on decisions where `b` is not selected; no blind hypothesis promotes
  `b`.  Success: average → the optimum for every logical inductor as belief component,
  including adversarially initialized ones.  Why not delivered: LI allows a persistent
  forecast on an unsettled variable; BRIA covers only hypotheses that promise, and the
  market-reading promoter of `b` promises the low forecast.  Matched: the predictor,
  menu and class are the original's.
- **D2 — the tentative troll (T3(d)) as a criterion refinement.**  Environment: the
  troll reads the published estimate.  Success: crossing with density 1 forced by a
  stated refinement of the criterion, with the loss of competence it costs quantified.
  Why not delivered: the criterion is satisfied by the stuck auction (Thm 1) and by the
  confident agent alike; Thm 3 does not apply.  Matched only for specializations that
  publish estimates; for one that does not, the environment is different and the row
  says so.
- **D3 — Agent Simulates Predictor with simulation access (T8(b)).**  Environment: the
  predictor simulates the agent's algorithm for `g(n) < n` steps and defaults to
  two-box; no commitment channel.  Success: one-boxing with density 1.  Why not
  delivered: the agent's decision is `O(g q)`-computable (Thm 2), the simulation does
  not finish, two-boxing is the sound higher claim, and the criterion settles there —
  the original obstruction (the more capable agent loses) preserved.  A solution changes
  the agent's decision cost for that decision without giving up coverage, or proves it
  cannot.
- **D4 — per-round counterfactual mugging (T6 per round, policy predictor).**
  Environment: the original access, unit scoring.  Success: paying with density 1 while
  G3 still holds on the subclass of environments without cross-round dependence.  Why
  not delivered: P1′ — BRIA over the full class excludes it; policy selection over LI
  claims it with no theorem.  A solution is a criterion, not a re-scoring.

**Stronger ambitions** (independent targets beyond both levels): S1 policy regret
against recognizable, joinable policies (item 86); S2 the counterfactual-dependence
register; S3 randomization as a menu option with a private source; S4 self-stability
without enforcement (G6's third source); S5 an exploration-safety certificate.

## 7. Registers of the requirements

| requirement | register | what is held fixed |
|---|---|---|
| G2, G7(ii) | epistemic (LI) | `D̄`, the stream |
| G3, G4, G5, G6 (competence), G7(i) | (i) realized feedback | the scored unit, the selection |
| G6 (external contract) | (ii) commitment | the selection, for the term |
| G6 (self-entered), S1 (`SHIFT`), S2, G7 (hindsight), D4 | (ii) across units / (iii) | a rollout evaluator, not supplied |

## 8. The acceptance checklist

If a candidate synthesis is proposed, these are checked or proved before it is called an
advance.

1. **Type.**  A belief component that publishes a market; a decision component with a
   finite menu and realized feedback; the witness estimates of G3 exhibited (published
   or not, stated which); the commitment source of G6 declared.
2. **Existence** (G1): a computable construction, with `E` and the comparison classes
   stated.
3. **LI on the active trajectory** (G2(c)), relative to the stream; or G2(b) declared
   and T0 passed.
4. **The BRIA criterion** (G3) over the named class, with the fixed-schedule lemma
   respected (tests respond to outpromising); Thm 3/Thm 4-form consequences.
5. **Interaction** (G4): (a) proved as a theorem on a stated environment class, or (b)
   proved in its strong form with §5's timing and semantics.  W1 alone is not (b).
6. **Accountability** (G5) with the menu-safety assumption named.
7. **Declared choices** (`AUDIT.md` §3): scored unit and who sets it; publicity of the
   selection and of any estimate; randomization; the commitment source; the scope of
   register (iii).  A benchmark answered by changing one of these silently is not
   answered.
8. **The test suite**: criterion-level rows passed; construction-level rows reported;
   negative controls reported; for every row, the access model and scored unit stated
   against the benchmark's primary-source formulation.
9. **Level 2, if claimed**: which of D1–D4, under the matched environment, and why the
   existing guarantees did not already deliver it.
10. **Not shown**: the candidate's own list against §6, with the registers of §7.
