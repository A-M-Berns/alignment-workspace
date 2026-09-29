# The LI/BRIA synthesis: objective, requirements, acceptance criteria

Labels: **PAPER** (a theorem of arXiv:1609.03543 v5 or of TARK 2023 EPTCS 379 pp.
421–440, cited at its statement), **DERIVED** (follows from cited results by an argument
given here), **FIX** (exact fixture in `tests/`, run by `tests/run.py`), **EXT** (a
contract the specification names and does not pay), **OPEN**.  Names are provisional:
*minimum credible synthesis*, *market-relative hypothesis class*, *belief–decision
compatibility*, *scoring granularity*, *lease publicity*, *realized-feedback register*.

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
`Σ_{t∈M, t≤T} (r_t − h^e_t)` on a test set `M` (rounds where `α^c_t = h^c_t`) tends to
`−∞`.  Counterfactual rewards are undefined; the menu may depend on past choices; the
criterion is myopic by design (§2, §7 of the paper).

**The type of a candidate.**  A synthesis is a computable agent `A` that, at each block
`k` of a system-supplied schedule, publishes a market `P_k`, and selects from a finite
menu `C_k` of continuations a pair `(c_k, e_k)` — a continuation to execute for the block
and an accountable claim about its realized block score `G_k ∈ [0,1]` — observing `G_k`
at the block's end.  With `m_k ≡ 1` and one-step continuations this is the paper's
setting; the block form is `wiki/Continuation-BRIA.md` §2, with the score `R_k` and the
execution wrapper supplied by the system.  Nothing in the type fixes a shared market, a
single budget, an auction, bundles or a commitment mechanism; those are constructions.
In particular the type admits both a separate choice learner beside the market and a
single learner inside it — the direction the corrigibility-kernel phase-2 round's
priority item names (claims "if chosen, this option scores `x`" as securities of the
inductor, settled when the option is chosen, with a choice rule that forces tests);
this specification is what either would have to satisfy.

**Three registers, kept apart throughout.**  (i) *Learning from realized feedback*:
claims about executed continuations, settled by observation.  (ii) *Honoring a
commitment*: a selection, once published, is executed for its block.  (iii)
*Evaluating a policy under logical or counterfactual dependence*: a value assigned to a
continuation that is not executed.  BRIA lives in (i); the block contract supplies (ii)
at block granularity; nothing in either component supplies (iii).  A result in one
register is not a result in another, and §5 says which register each requirement
occupies.

## 2. The eight candidate requirements, examined

Each requirement is stated, then: the failure it excludes; its assumptions and
evaluation standpoint; compatibility; classification (**core**, **stronger**,
**unresolved**, **rejected**).

### R1. Computable existence

*Statement.*  There is a computable `A` such that for every environment in a declared
class `E` — every computable `D̄`, every observation stream, every block schedule
satisfying non-dominance `m_K / Σ_{k≤K} m_k → 0`, every menu and score process — `A`
satisfies the criterion, with the comparison classes named: e.c. traders for the
market, and the *market-relative* e.c. hypothesis class `H^P` for the decision layer —
`O(g(t))`-computable maps from the history *and the published prices* to
`(continuation, claim)`.

*Excludes.*  Criteria met only by uncomputable agents (proof-based decision theory with a
halting oracle; Bayesian updatelessness over an uncomputable prior).

*Assumptions.*  `A` is computable, not e.c.: no `O(g)`-computable agent covers the
`O(g)`-computable class (**PAPER**, Thm 2), so the comparison class is strictly below the
agent.  The market's computability relative to an observation stream is the
oracle-relativized inductor, `PRIORITIES.md` item 91 (**EXT**).

*Compatibility.*  The trivial witness — run a logical inductor and the paper's auction
side by side, with a hypothesis class that cannot read the market — satisfies R1, R2,
R3 and R5 at once.  That is why R4 and the interaction diagnostics of
`TEST_SUITE.md` (T10, T11) are part of the minimum: existence is cheap, integration is
not.  **Core.**

### R2. LI recovery

*Statement, three grades.*  (a) *Compatible component*: some logical inductor's prices
are consistent with `A`'s behaviour.  (b) *Passive implication*: on the passive
restriction `|C_k| = 1` for all `k`, the published `P̄` satisfies the LI criterion
relative to `D̄`.  (c) *Active implication*: on every environment in `E`, `P̄`
satisfies the LI criterion relative to `D̄` and the observation stream, the traders
being allowed to bet on sentences about realized scores.

*Excludes.*  A market that is exploitable once decisions are in play — for instance one
whose prices on the block-score variables are moved by the decision layer's wealth
rather than by evidence.

*Standpoint.*  (c) is stated relative to the stream; the sentences about realized
outcomes are empirical and enter through the relativized deductive process (item 91),
not as theorems of `Γ`.

*Compatibility.*  (a) is satisfied by the side-by-side witness and says nothing.  (b) is
implied by (c).  (c) is what R4 consumes: LI's unbiasedness from feedback on
`P`-generable weightings (**PAPER**, `thm:wubaff`/`thm:wubexp`, with the deferral
condition the pinned formalization records) is the theorem that makes the market's
expectation of a block score track the realized score on the tested subsequence.
**Core in grade (c)**; (b) is the fallback if relativization fails and is then a
weakening to be declared; (a) **rejected**.

### R3. BRIA recovery

*Statement.*  On every environment in `E`, the sequence `(c_k, e_k)` satisfies the
duration-weighted criterion of `wiki/Continuation-BRIA.md` §4 with respect to `H^P`:

```
no overestimation   limsup_K  Σ_{k≤K} m_k (e_k − G_k) / S_K  ≤ 0,   S_K = Σ_{k≤K} m_k
coverage            ∀ h ∈ H^P:  B_h finite,  or  ℓ^h_K = Σ_{k∈M_h, k≤K} m_k (G_k − e_{h,k}) → −∞ along B_h
```

with `B_h` the blocks at which `h` outpromises `A` and `M_h` the blocks at which `h`'s
continuation was executed.  With `m_k ≡ 1` this is Defs. 1–7 verbatim, and the paper's
consequences are the acceptance tests: the guaranteed-option theorem (**PAPER**, Thm 3:
if an efficiently identifiable option guarantees an e.c. lower bound `L̄` then
`liminf (1/T) Σ (r_t − L_t) ≥ 0`), its block form *continuation competence*
(`wiki/Continuation-BRIA.md` §6, under the bounded-record hypothesis (BR)), and the
random-reward form (**PAPER**, Thm 4: rewards boundedly vMWC-random with e.c. means are
attained on average).

*Excludes.*  Two things, and the slogan "no missed opportunities" is neither.  First,
persistently claiming more than is realized.  Second, ignoring an e.c. hypothesis that
keeps promising more: coverage forces a test, and forces the estimate up once the
promise survives its tests.

*What the criterion does not force* (**FIX** `test_cm.P2_CrossSubsidyIsABRIA`).  The
estimates are not beliefs.  In repeated counterfactual mugging with per-round scoring
(`src/cm.py`), the agent that pays on every tails round but a density-zero set,
estimating `1/2` on tails and `0` on heads, has cumulative overestimation `≤ 0` on every
prefix and covers every refusing hypothesis: the one promising exactly `1/2` never
outpromises it, and one promising `1/2 + δ` is rejected at every tails round while its
record on the sparse tests falls by `δ` per test.  So a BRIA may pay in counterfactual
mugging, funding the estimate on the losing rounds with underestimation on the winning
ones.  The paper's auction does not do this — it is the criterion, not the construction,
that permits it — and R4 is what removes the permission.

*Standpoint.*  Realized feedback only; the comparator is a hypothesis's claim at the
same block contract, and what is held fixed is the contract and the published
selection.

*Compatibility.*  With R4, see §3.  With R6/R7 the block contract is the whole
interface.  **Core**, at block granularity, with the class `H^P`.

### R4. Belief–decision compatibility

*Statement.*  Let `Ĝ_k` be the bounded variable "the realized score of the selected
continuation of block `k`", settled by observation at the block's end, and `E_k(Ĝ_k)`
the market's expectation of it at the block's opening, after the selection is
published.  For every `P`-generable divergent weighting `w̄` (**PAPER** §4.3 sense, with
`P` the published market),

```
Σ_{k≤K} w_k m_k (e_k − E_k(Ĝ_k)) / Σ_{k≤K} w_k m_k  →  0 .
```

Same quantity, same conditions: the claim and the expectation are both about the
executed continuation from the actual start history, both formed at the opening after
the selection.  The ex ante value of a *policy* is a different quantity from the value
of the *action conditional on later information* — in counterfactual mugging the paying
policy is worth `1/2` ex ante and paying is worth `0` given tails — and the statement
compares neither of those with the other.

*Excludes.*  The cross-subsidy of R3 (**FIX** `test_cm.P1`: with claims at the market's
limit on the tails subsequence — the realized reward of the chosen option — the
exact-promise refuser outpromises at every paying tails round while its record on the
tests stays at `0`, so coverage fails; the agent must refuse on all but a density-zero
set).  And, in the other direction, a market that keeps expecting more of the chosen
continuation than the decision layer claims.

*Derivation* (**DERIVED**, hypotheses named).  The upper half `e_k ≲ E_k(Ĝ_k)` on `w̄`
follows from no overestimation and the market's unbiasedness from feedback on `w̄`
(R2(c); needs the settlement of `Ĝ_k` to be computable within a deferral, which the
block's end supplies, and `w̄` `P`-generable).  The lower half follows from coverage with
the market-reading hypotheses `h_c = (c, E_k(Ĝ(c)))` for e.c. selectors `c` — a sound
promise wherever the market is unbiased on `c`'s tests — so the claim cannot lag any
e.c. option's market value, hence not the chosen one's.  Both halves need the test sets
and rejection sets of the construction to be `P`-generable, which for the paper's
auction they are (the round is `O(g q)`-computable from the published prices).  So R4 is
a **theorem target**, not an axiom: for a candidate it is proved from R2(c) and R3 with
the class `H^P`, or a countermodel is exhibited.  A candidate whose class cannot read
the market fails it by the cross-subsidy.

*Consequence.*  Under R2(c)+R3+R4 the agent's claim is asymptotically the market's
expectation of the chosen continuation and at least the market's expectation of every
e.c. selector: the "argmax of the market's expectations" that logical-inductor decision
theory wanted, obtained through accountable claims rather than through conditional
expectations of untaken actions.  **Core**, as the interaction requirement.

### R5. Accountability for unchosen alternatives

*Statement.*  Coverage, read as an obligation: for every `h ∈ H^P` that outpromises `A`
infinitely often, `A` executes `h`'s continuation on an infinite test set along which
`h`'s record diverges to `−∞`.  Nothing weaker survives: with finitely many tests the
record is bounded and coverage fails; with tests whose record stays bounded the
hypothesis was right.

*Excludes.*  Self-confirming pessimism about an option some e.c. hypothesis promotes
(**FIX** `test_troll.SafeBridge`, `test_interaction`): the agent cannot decline forever
an option whose promise it has never refuted.

*Why it is defensible without assuming exploration is safe or informative.*  A test is
not an exploration step distinct from choice: it *is* the choice, the executed
continuation of the winning claim, so a predictor reading the public state sees a
choice and not a flag (Garrabrant's 2017 obstacle — that explored and deliberate
actions differ for a predictor — has no purchase; `AUDIT.md` §1).  A test is informative
by construction: the claim is about the executed continuation from the actual history
(`CONTINUATION_HYPOTHESES.md` §3 of the continuation-BRIA round on biased testing).  And
a test is only as safe as the menu: the menu is the admissible set, so an option outside
it is neither testable nor claimable.  What the requirement therefore assumes, and names:
**no traps in the menu** — an outpromising hypothesis whose continuation forecloses is
tested at least once.  Kosoy's trap problem is not solved here; it is placed at the
gate (**EXT**).  A stronger target is an exploration-safety certificate (§4, S5).

*Compatibility.*  R5 is R3's coverage clause; it conflicts with nothing in the list and
with the auction's finite-time behaviour only where the environment reads unpublished
internals (T3 in `TEST_SUITE.md`).  **Core** (as the coverage clause with the menu
assumption named).

### R6. Temporally extended decision adequacy

*Statement.*  On block-scored environments, the weighted criterion of R3 and hence
continuation competence: for a covered hypothesis with bounded record, the learner's
`m`-weighted average is asymptotically at least the average of its claims
(`wiki/Continuation-BRIA.md` §6, **DERIVED** there on the Lean algebra).  Policy regret
against a comparator class `Π` decomposes exactly as `SHIFT + SLACK + LEARN` (§7 there,
**LEAN** `regret_decomposition`), and only `LEARN` is the criterion's; regret against
all legitimate policies is false (the irreversible-branch witness, `COUNTERMODELS.md`
of that round).

*Excludes.*  Myopia with respect to investments that pay within a block: the one-step
criterion forces testing, not adoption; a sound claim about the whole investment forces
adoption (`PRIORITIES.md` item 86).

*Standpoint.*  What is held fixed is the block contract; the comparator is a claim at
that contract; the schedule is the system's and non-dominant.

*Compatibility.*  With R7 (below).  **Core** for continuation competence at system
scheduled horizons; **stronger** for policy regret against recognizable, joinable
policies (item 86's three parts).

### R7. Commitment and reflection

Four notions, each precise, and their compatibility.

(a) *Commitment consistency* = honoring the lease: the published selection is executed
for its block whatever the market comes to believe inside the block.  Definitional in
the block contract; the continuation stays causal and the exterior live.  **Core**.

(b) *Beneficial revision* = coverage between blocks: at the next contract the selection
is open to any hypothesis whose claim survives.  **Core**; it is R3.

(c) *Cross-block commitment*: a commitment whose value depends on not being revised
across blocks is representable only as a continuation of a longer block.  Under a
non-dominant system schedule of growing blocks every finite commitment length is
eventually available, but *choosing* to commit longer is not the agent's: bidder-chosen
horizons are **OPEN** (`wiki/Continuation-BRIA.md` §9).  The missing definition is the
allocation rule for duration.  **Unresolved.**

(d) *Reflective stability*: no e.c. rival decision rule, run as a hypothesis on the
same contracts, asymptotically beats the agent's realized scores on its sound claims.
This is coverage again, because a rival rule *is* a hypothesis in `H^P`; it covers
exactly the advantages a rival realizes within blocks.  Advantages that need a
different history (foreclosure, self-modification with cross-block payoff) are `SHIFT`
and not delivered.  **Core** in the within-block form as a consequence of R3;
**stronger** for the market's self-trust form `E_n(score | keep) ≥ E_n(score |
replace by X) − o(1)`, which the Bayesian tiling theorems for updateless agents (Demski
2025, `AUDIT.md` §1) prove under a fairness hypothesis and no bounded-agent analogue
has.

### R8. Logical learning

*Statement.*  Two parts.  (i) The hypothesis class reads the published prices (`H^P`),
so an improvement in reasoning power — a stronger `D̄`, a longer run of the market —
reaches the decision layer through the market without changing the class; R2(c) gives
timely learning on the price side (**PAPER** §4.2).  (ii) The market's prices on the
block-score variables of the *active* trajectory obey LI's guarantees (R2(c)), so a
fact discovered late about an earlier block's score moves the market's retrospective
expectation and every later claim that reads it.

*Excludes.*  A decision layer insulated from the market: on rewards decided by logic the
market learns and a blind class cannot (**FIX** `test_interaction`: each blind predictor
is wrong on its own residue class of a diagonal truth sequence; the blind auction's
average stays below `9/10`; the market-reading auction's exceeds `99/100`).

*What is missing.*  A score for an earlier decision in the light of a later fact — a
hindsight regret — needs a value for continuations that were not executed at that
block, i.e. the rollout evaluator `Ĝ_k(π; H)` of the policy frontier, which is register
(iii).  No definition in the realized-feedback register supplies it, and the requirement
should not pretend to.  **(i), (ii) core as design choices; the hindsight form
unresolved**, with the missing object named.

## 3. The conflict: action-level BRIA against binding policy commitments

Stated at the paper's granularity, `m_k ≡ 1`, with R4 in force per round.

**Proposition P1** (**DERIVED**, **FIX** `test_cm.P1`).  In repeated counterfactual
mugging with per-round scoring, a predictor that reads the agent's policy, and rounds
alternating heads (single option, paying `1` iff the predictor predicts paying) and
tails (`pay` at `0`, `refuse` at `1/2`): no agent satisfying R2(c), R3 and R4 per round
pays on a positive-density set of tails rounds.  Proof: R2(c) and R4 force the claim on
paying tails rounds to the market's expectation of the realized reward of paying, which
unbiasedness on that `P`-generable subsequence drives to `0`; the hypothesis
`(refuse, 1/2)` then outpromises on every such round with a record of `0` on any test
set; coverage forbids that unless the paying rounds have density zero.  The paying
agent is better on average (`1/2` against `1/4`), and the criterion excludes it.

**Proposition P2** (**FIX** `test_cm.P2`).  Dropping R4 restores the paying agent, by the
cross-subsidy of §2 R3.  So the conflict is exactly between per-round belief–decision
compatibility and cross-round commitment, not between BRIA and commitment as such.

**Resolution, declared.**  Score at the granularity at which the commitment pays: a
block containing both branches, with the predictor reading the block's published
continuation.  Then the paying continuation's claim `1/2` is sound, refusing's is `1/4`,
coverage settles on paying, and R4 holds at block granularity (**FIX**
`test_cm.BlockScoring.test_lease_predictor_pays`).  This changes the *scoring
granularity* and the *information held fixed* (the block contract and the published
selection) and says so; it does not change the comparator class — hypotheses are still
all of `H^P` — and it does not change the information the predictor has beyond what
the lease publicity choice (§6) declares.  **What it leaves out**: commitments whose
payoff accrues outside any block — the one-shot problem, and a predictor that reads
only past blocks (**FIX** `test_lagging_predictor_refuses`: the criterion then settles on
refusing, at `1/4`).  Those are register (iii) and register (ii) across blocks
respectively, and the minimum synthesis does not claim them.

## 4. The minimum credible synthesis, and what is stronger

**Minimum credible synthesis (MCS).**  A computable agent of the type in §1 for which
the following are proved, each with its hypotheses stated:

1. R1 — existence on `E`, with the comparison classes named (e.c. traders; `H^P`).
2. R2(c) — the LI criterion relative to `D̄` and the observation stream on every
   environment in `E` (or R2(b) with the weakening declared).
3. R3 — the weighted BRIA criterion with respect to `H^P` at the system's non-dominant
   schedule, hence Thm 3/Thm 4-form competence and continuation competence.
4. R4 — belief–decision compatibility, as a theorem from 2 and 3 or with its
   countermodel; and the interaction diagnostics T10, T11 passed at criterion level.
5. R5 — coverage as the accountability clause, with the menu-safety assumption named.
6. R7(a),(b),(d-within-block) — which are 3 restated, and R8(i),(ii).
7. The criterion-level rows of `TEST_SUITE.md` passed, and the construction-level rows
   reported either way.

*What satisfying the minimum establishes.*  One computable agent whose beliefs are a
logical inductor on the active trajectory, whose realized-score learning is bounded
inductively rational at block granularity against every efficiently computable
market-reading hypothesis, and whose claims agree with its own market's expectations of
the same quantity — so that side-by-side LI and BRIA are excluded, spurious beliefs
about untested options cannot block a test, and within-block commitments (Newcomb with
a lease-reading predictor, counterfactual mugging with both branches in the block,
Parfit's hitchhiker as a two-stage block) are handled in the realized-feedback register.

*What it leaves open.*  Every one-shot verdict; logical counterfactuals; commitments
that pay across blocks; policy regret's `SHIFT` and `SLACK`; exploration safety beyond
the gate; randomization against adversarial predictors (BRIA's Thm 5 needs a random
source the criterion does not require); equilibrium selection among self-consistent
belief–action pairs (T3(e), T9); rates (every guarantee is asymptotic).

**Stronger decision-theoretic ambitions**, each an independent target:

- **S1** Policy regret `≤ o(T)` against recognizable, joinable legitimate policies (item
  86's certificate pair).
- **S2** The counterfactual-dependence register: a principled value for unexecuted
  continuations that agrees with realized feedback wherever both apply, delivering
  one-shot verdicts (transparent Newcomb, XOR blackmail, Parfit one-shot).  No candidate
  in the audit has it; the FDT paper calls it its largest open problem.
- **S3** Randomization as a menu option with a private source, and the criterion's
  random-reward clause made sufficient for Death in Damascus.
- **S4** Cross-block reflective stability: self-trust of the market about the agent's
  own future scores, the bounded analogue of the 2025 UDT tiling theorems.
- **S5** An exploration-safety certificate: coverage restricted so that a foreclosing
  test is never forced, with the loss of competence that costs, stated.

## 5. Registers of the requirements

| requirement | register | what is held fixed |
|---|---|---|
| R2, R8(ii) | epistemic (LI) | `D̄`, the stream |
| R3, R4, R5, R6 (competence), R7(b),(d) | (i) realized feedback | the block contract, the published selection |
| R7(a) | (ii) commitment | the selection, for the block |
| R7(c), S1 (`SHIFT`), S2, R8 (hindsight) | (iii) counterfactual dependence | a rollout evaluator, not supplied |

## 6. The acceptance checklist

If a candidate synthesis is proposed, these are checked or proved before it is called an
advance.

1. **Type.**  It publishes a market and selects `(continuation, claim)` at a block
   contract; if it does not publish claims, it cannot be held to R3 and is not a
   candidate for this specification.
2. **Existence** (R1): a computable construction, with `E` and the two comparison
   classes stated; the class `H^P` reads the published prices.
3. **LI on the active trajectory** (R2(c)), relative to the stream; or R2(b) with the
   weakening declared and T0 passed.
4. **The weighted criterion** (R3) at the system schedule, with the non-dominance
   condition stated; Thm 3/Thm 4-form consequences and continuation competence.
5. **Compatibility** (R4): the theorem from 3 and 4, or the countermodel; T11.
6. **Interaction** (T10): the candidate reaches what the blind class cannot.
7. **Declared choices** (`AUDIT.md` §3): scoring granularity and who sets the schedule;
   lease publicity — what predictors may read; randomization; the scope of register
   (iii).  A candidate that answers a benchmark by changing one of these silently has not
   answered it.
8. **The test suite**: every criterion-level row passed; every construction-level row
   reported; every negative control reported.
9. **Not shown**: the candidate's own list of what it leaves open against §4, with the
   registers of §5.
