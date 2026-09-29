# The diagnostic test suite

Labels as in `PROBLEM_STATEMENT.md`; requirement codes G1–G7 are its §2.  Every
benchmark carries the same ten fields.  *Level* says whether every agent satisfying the
minimum credible synthesis must pass (**criterion**), whether the criterion is silent
and the row diagnoses a designated construction (**construction**), or whether the
guarantee cannot see the distinction (**invisible**, kept only to say so).  Rewards are
in `[0, 1]`.  "Lease" means a published selection read through a channel the environment
supplies; a row using it says so, because a predictor reading such a channel is a
different environment from the benchmark's primary-source formulation.  The fixtures
named are in `src/`, run by `tests/run.py` on the paper's first-price auction with unit
rounds or on fixed agents; every fixture is a finite prefix check against fixed bidders
and never a proof of a quantified statement.

**Reading a row.**  Each verdict is a claim about a *specified* environment.  A
familiar name fixes neither the predictor's access, nor the scored unit, nor whether
randomization is available, nor whether the problem is one-shot; each flips at least
one verdict below, and a row that changes one of them says which and does not count the
result as solving the original.

## T0. Passive logical reasoning

- *Environment.*  `|C_k| = 1` for all `k`; a computable deductive process `D̄`; scores
  constant.
- *Timeline.*  Prices published at each decision; nothing to choose.
- *Access.*  Traders read the published prices and `D̄`.
- *Held fixed.*  `D̄`.
- *Desired.*  The market satisfies the LI criterion relative to `D̄` (G2(b)); under
  G2(c) the same with the stream.
- *Form.*  Asymptotic; sure.
- *Assumptions.*  `D̄` computable.
- *Level.*  Criterion.
- *Negative control.*  A market with a fixed exploitable pattern (constant prices on an
  e.c. sequence of theorems): fails.
- *Diagnoses.*  G2.  It cannot see G2(c)'s active clause.

## T1. Transparent repeated choice: 5-and-10

- *Environment.*  Menu `{5, 10}` every round, rewards `1/2` and `1`, no predictor.
- *Timeline.*  Choose, observe.  *Access.*  None.  *Held fixed.*  The round.
- *Desired.*  Average reward `→ 1` (**PAPER** Thm 3 with `L_t = 1` on `10`).  The
  proof-based pathology — a spurious proof that `10` yields less — has no purchase
  because no proof about the untaken option enters any claim's settlement.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  The constant hypothesis `(10, 1)` is in the class.
- *Level.*  Criterion.
- *Negative control.*  The adversarial offer (Oesterheld and Conitzer 2021): two boxes
  at cost `1`, each holding `3` iff the seller, at accuracy `3/4`, predicted the buyer
  would not take it; no randomization.  Abstaining is the sound higher claim; a design
  that learns "the expected content of a box" as a conditional expectation of an
  untaken option buys and loses.  The reward now depends on the policy.
- *Diagnoses.*  G3 (Thm 3 form); the control diagnoses register (i) against conditional
  expectations of untaken actions.

## T2. Self-confirming pessimism

- *Environment.*  Options `A` (reward `1/2`) and `B` (reward `1`); the agent starts with
  prices or initial claims that put `B`'s reward at `0`.
- *Timeline.*  Choose, observe.  *Access.*  None.  *Held fixed.*  The round.
- *Desired.*  Average `→ 1`: `(B, 1)` outpromises until tested and its tests refute the
  pessimism (G5).  Coverage does not consult the market's price of the untested option.
- *Form.*  Asymptotic; sure.  *Assumptions.*  `B` in the menu; no trap.
- *Level.*  Criterion.
- *Negative control.*  `B` pays `0`: the pessimism is correct, `(B, 1)`'s record
  diverges, the agent stays on `A` with sparse re-tests (**FIX** `test_troll.AlwaysBlown`,
  the same shape).  A second control is T3(d), where pessimism becomes self-confirming
  through the agent's own public estimate; a third is D1 of `PROBLEM_STATEMENT.md` §6,
  where no blind hypothesis promotes `B` and the market's forecast is the pessimism.
- *Diagnoses.*  G5; with the controls, the boundary between G5 and construction
  behaviour, and the untested-optimism obstacle.

## T3. The Troll Bridge family

Options `stay` (`1/2`) and `cross` (`1` unless the troll fires, then `0`).  Each variant
is the troll's condition, a function of a named part of the state (**FIX** `src/troll.py`).
The primary source (Demski 2019, results due to Eisenstat) is one-shot and proof-based,
with the troll reading the consistency of the agent's theory; every repeated variant
below changes both the register and the troll's access and says so.

- **(a) Löbian, one-shot, proof-based.**  *Level: invisible.*  The realized-feedback
  guarantee says nothing about a single decision, and the synthesis makes no proof about
  its own action; the row is kept to record that passing (b)–(f) is not passing (a).
- **(b) Action-only troll**: fires always, or never.  *Desired:* average `→ 1` when
  never, `→ 1/2` with sparse tests when always (**FIX** `SafeBridge`, `AlwaysBlown`).
  *Level: criterion.*  Diagnoses G3/G5.
- **(c) Exploration-flag troll**: fires iff the crossing was an exploration step.  For
  a design with an exploration mechanism distinct from choice the flag is public state
  and the design never learns crossing's value (Demski 2019; Diffractor 2018).  For a
  synthesis whose tests are choices there is no flag.  *Level: construction*; it
  discriminates designs with a flag from claim-driven testing, and a synthesis that
  passes has changed what the troll can read, not solved (a).
- **(d) Tentative troll**: fires iff a published estimate on a crossing round is below
  `1`.  Applies only to specializations that publish estimates.  The paper's auction
  tests `cross` only at a wealth-capped bid, is blown up every time, and stays forever
  with sparse losing tests while being a BRIA (**PAPER** Thm 1 holds for every reward
  sequence); the agent that always crosses at estimate `1` is a BRIA and gets `1`; the
  variant auction that bids only at full confidence crosses (**FIX** `TentativeTroll`).
  *Level: construction*: Thm 3 does not apply because no option guarantees a reward.
  Diagnoses estimate publicity and a construction's test timing; D2 is the level-2 form.
- **(e) Belief-disagreement troll**: fires iff the action differs from the argmax of
  the published market's forecasts.  Two self-consistent pairs exist and the criterion
  does not select.  *Level: construction* (equilibrium selection).  Diagnoses the limit
  of G4(b): agreement between belief and choice does not say which agreeing pair is
  reached.
- **(f) Consistency troll**: fires iff `Γ` is inconsistent.  In the repeated register
  the condition is a fixed fact, the sound hypothesis `(cross, 1)` exists iff `Γ` is
  consistent, and coverage adopts it whatever the market's Löbian prices.  *Level:
  criterion*, and a caution that this says nothing about (a).

Fields common to (b)–(f): timeline choose–observe; the troll reads the named public
state and nothing else; the round is held fixed; asymptotic average, sure; the
constant crossing hypothesis in the class; negative controls are the sibling variants.

## T4. Prediction-sensitive choice: Newcomb with realized feedback

- *Environment.*  Options `one`, `two`; if the predictor predicts `one`: `999/1000` and
  `1`; if `two`: `0` and `1/1000` (**FIX** `src/newcomb.py`).  The primary-source
  problem is one-shot with a predictor of unspecified mechanism; every row here is
  repeated with realized feedback and a named mechanism.
- *Timeline.*  Per round: predict, choose, observe.  Block: one continuation for `m`
  rounds.
- *Access.*  (i) *Lease*: the predictor reads the selection of the current round or
  block through a supplied channel — an environment with a commitment channel, not the
  original.  (ii) *Frequency*: predicts `one` iff a strict majority of past rounds
  one-boxed; reads nothing of the current round — a statistical predictor within the
  original's information structure.  (iii) *Imperfect lease*: (i) at accuracy `p`.
  (iv) *Simulation with a runtime bound*: T8.
- *Held fixed.*  The predictor's rule; per round, the round; block, the contract.
- *Desired.*  (i) one-box, average `→ 999/1000` per round and per block (**FIX**
  `LeasePredictor`): `(two, 1)` is refuted, `(one, 999/1000)` is sound.  (ii) per round:
  two-box is what the criterion settles on — the one-boxing agent fails coverage
  against the sound contextual two-boxer (**FIX**); the two-boxing agent covers the two
  fixed bidders checked, and *with a fixed sparse test schedule is not a BRIA* against
  the off-schedule attacker (**FIX** `test_two_boxing_agent_with_a_fixed_schedule_is_not_a_bria`);
  full-class coverage needs adaptive tests, which the auction has.  Block with
  within-block memory: one-box, `(m−1)/m · 999/1000` (**FIX** `FrequencyPredictorBlock`).
  (iii) the sound claims order by `p`: one-box iff `(999/1000)·p > (1−p) + p/1000`, i.e.
  `p > 500/999`.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  The predictor's rule is a function of the named public state.
- *Level.*  Criterion for the exclusions in (i)–(iii); the paper's auction under (ii)
  per round cycles at every finite horizon the fixtures afford (**FIX**
  `test_auction_cycles_at_finite_horizon`), the shape of the non-convergence of
  value-based learners in Newcomblike environments (Bell et al. 2021).
- *Negative control.*  (ii) per round against (ii) per block: the same predictor and
  rewards, opposite verdicts, by the scored unit alone.
- *Diagnoses.*  G3, G6, the scored unit, the access model.  (i) and its block form are
  conditional results under a supplied channel and are not the original problem.

## T5. Adversarial prediction and randomization: Death in Damascus

- *Environment.*  Options `stay`, `flee`; Death predicts the option and is there; the
  matched option pays `0`, the unmatched `1`; optionally a third option `coin` choosing
  by a private random bit.
- *Timeline.*  Predict, choose, observe.  *Access.*  Death reads the choice; in the
  control, also the bit.  *Held fixed.*  Death's rule.
- *Desired.*  Without `coin`: no pure option guarantees anything; the criterion is
  satisfied by estimates `0`, average `0`.  With `coin` and Death blind to the bit:
  rewards on `coin`'s rounds are boundedly random with mean `1/2`, so **PAPER** Thm 4
  gives average `≥ 1/2`; the criterion itself does not require a random source (Thm 5
  uses one in its construction).
- *Form.*  Asymptotic average; almost sure over the bits.
- *Assumptions.*  `coin` in the menu; the bit private and vMWC-random relative to the
  class.
- *Level.*  Criterion, given `coin`.  Adding `coin` is a change of menu and is stated
  as one.
- *Negative control.*  Death reads the bit: `coin` pays `0`.
- *Diagnoses.*  Whether randomization is a menu option (`AUDIT.md` §3) and G3's
  random-reward clause.  A design that stipulates mental randomization unpredictable
  answers a different environment.

## T6. Policy-level against locally conditional improvement: repeated counterfactual mugging

- *Environment.*  Heads rounds (single option; `1` iff the predictor predicts paying)
  alternate with tails rounds (`pay` at `0`, `refuse` at `1/2`) (**FIX** `src/cm.py`).
- *Timeline.*  Three scorings: per round; per block of one heads and one tails round;
  one-shot.
- *Access.*  (i) *Policy*: the predictor reads the agent's limiting tails choice (the
  primary source's Omega, in the repeated setting).  (ii) *Frequency*: predicts paying
  iff the agent has paid more often than refused — within the original information
  structure.  (iii) *Lease*: the block continuation through a supplied channel.  (iv)
  *Lagging*: the previous block's realized tails choice.
- *Held fixed.*  Per round, the round; per block, the contract.
- *Desired.*  Per round with (i) or (ii): every BRIA covering the e.c. class pays on a
  density-zero set — `PROBLEM_STATEMENT.md` P1′, by the heads tracker and the exact
  refuser, no compatibility requirement used (**FIX** `PerRoundBRIAExcludesPaying`,
  `CrossSubsidy_NoOverestimationOnly`); the paper's auction under (ii) settles on
  refusing with sparse paying tests and heads paying `0` (**FIX** `PerRoundAuction`).
  Paying averages `1/2` against `1/4` under (i).  Per block with (iii): pay, average
  `→ 1/2` (**FIX** `BlockScoring`) — a conditional result under a supplied channel and
  a changed scored unit.  One-shot: register (iii), invisible.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  The heads reward e.c.-trackable from the history (true for (i), (ii),
  (iv)); for a non-trackable predictor the exclusion is open (`PROBLEM_STATEMENT.md` §3).
- *Level.*  Criterion for the per-round exclusion and the block verdict.
- *Negative control.*  Per block with (iv): refusing's contextual claim `3/4` after a
  paying block is sound and higher, the auction settles on refusing, the average is
  `1/4` plus the sparse re-tests (**FIX** `test_lagging_predictor_refuses`).  Same
  rewards, same block, opposite verdict, by what the predictor reads.
- *Diagnoses.*  The conflict of `PROBLEM_STATEMENT.md` §3 exactly: action-level coverage
  of the full class against a commitment paying outside the scored unit; the declared
  resolution and its residue; D4 is the level-2 form under the original access.

## T7. Commitment timing and revision

Three problems with the same shape: a first stage in which a predictor reads what the
agent will do at a second stage, and a second stage at which reneging is locally
better.  In their primary sources the predictor reads the agent's disposition, not a
channel; every block verdict below supplies an execution contract and a channel and is
a conditional result.

- *Parfit's hitchhiker.*  Block = (desert, town).  The driver reads the block
  continuation; rescued iff it pays; block score `= rescued − payment`.  *Desired:* the
  paying continuation's claim is sound and higher; selected (**criterion**, T6's block
  shape).  *Negative control:* the town stage is a new block with its own contract and
  the driver predicts that fresh block: reneging is the sound higher claim, the driver
  predicts it, the agent is left.  The contract boundary is the commitment boundary; a
  candidate says where its units end and which of G6's three commitment sources it
  relies on.
- *Transparent Newcomb.*  Block = (predictor fills, agent sees, agent chooses); the
  predictor reads the continuation "one-box on seeing both full".  Same verdict and
  control.
- *XOR blackmail.*  Block = (termite state drawn, letter iff exactly one of termites /
  would-pay, agent chooses).  The blackmailer reads the continuation.  Refusing's block
  value exceeds paying's by `(1−p)·payment`; refuse (**criterion**).  *Control:* a
  blackmailer that reads nothing: the letter is evidence and paying is worse still; the
  row does not separate EDT from the synthesis.
- *Fields.*  Timeline as stated; access = the continuation through a channel; held
  fixed = the contract; asymptotic average over repeated blocks, sure; assumption = the
  predictor is a function of the published continuation.
- *Diagnoses.*  G6 (external contract), the self-entered contract (a commitment longer
  than a block is not representable), publicity.  One-shot versions: register (iii).

## T8. Changes in available reasoning: Agent Simulates Predictor

- *Primary source.*  Slepnev 2011 (credited to Drescher 2010): the predictor does not
  simulate the agent; it reasons about the agent's decision procedure with a proof
  bound `N` below the agent's `M`, and knows the agent's proof system is consistent; the
  agent can simulate the predictor.  A proof-based one-boxer would need a proof that
  one-boxing yields more than two-boxing, which the predictor sees would make the
  agent's system inconsistent, so it predicts two-boxing and the agent gets the small
  prize.  The obstruction: the more capable reasoner loses.
- *Environment here.*  Newcomb rewards; the predictor has runtime bound `g(n)` below the
  agent's `n`.
- *Access, two cases.*  (a) The predictor reads the selection through a supplied
  channel.  **This is not the original**: the original has no channel, and a predictor
  that can read a commitment is a different environment; (a) is a conditional result
  and no equivalence with the original is claimed.  (b) The predictor simulates the
  agent's algorithm for `g(n)` steps and predicts `two` when the simulation does not
  finish: the original's information structure (reasoning about the agent's procedure
  with fewer resources), realized as bounded simulation instead of bounded proof.
- *Held fixed.*  The predictor's rule and bound.
- *Desired.*  (a) one-box, as T4(i).  (b) the agent's decision is `O(g q)`-computable
  and above `O(g)` (**PAPER** Thm 2), so the simulation is unfinished, one-boxing pays
  `0`, `(one, 999/1000)` is refuted, two-boxing is the sound higher claim and the
  criterion settles there: the original obstruction is **preserved** — the synthesis
  two-boxes for the same structural reason the proof-based agent does (it is the more
  expensive reasoner), though by a different mechanism (no proof is made about the
  predictor).  What the agent's beliefs about the predictor say (the logical-time
  ordering of Demski 2018) plays no role in the realized register.
- *Form.*  Asymptotic; sure.
- *Assumptions.*  `g(n) < n` and the predictor's default named.
- *Level.*  Criterion under each access rule; (b) is a **negative** criterion-level
  result and D3 of `PROBLEM_STATEMENT.md` §6 is its success condition.
- *Negative control.*  (a) against (b): the same rewards, opposite verdicts, by the
  channel alone — which is why (a) does not count as solving ASP.
- *Diagnoses.*  G7(i); that reasoning-power asymmetry enters only through what the
  predictor can compute or read; the cost of full-class coverage (Thm 2) as the
  obstruction's carrier.

## T9. Copies and related agents

- *Environment.*  Two syntheses in a repeated prisoner's dilemma, each reading the
  other's realized past play.
- *Desired.*  None at criterion level: **PAPER** Thm 5 — for any strictly individually
  rational correlated profile there are BRIAs whose play converges to it, and BRIAs
  covering the constant hypotheses obtain at least maximin.
- *Level.*  Construction only.  Kept because the criterion is provably silent by a
  published theorem; a candidate claiming cooperation claims it for its construction,
  against the modal-agent results (Barasz et al. 2014).
- *Diagnoses.*  Nothing in G1–G7; it bounds what the specification asks.

## T10. Interaction: rewards decided by logic

- *Environment.*  Options `A`, `B`; `A` pays `1` iff `φ_k` is true, `B` iff false; `φ_k`
  is an e.c. sequence of sentences each decided by `D̄` *before* decision `k` (`φ_k` or
  `¬φ_k ∈ D_k`), at a deductive cost above the decision component's runtime.
- *Timeline.*  Market published (its price of `φ_k` already informed by `D_k`), choose,
  observe.  The timing matters: a sentence settled by `D̄` *after* the decision gives the
  market no advantage before it, and eventual settlement is not a forecast.
- *Access.*  Hypotheses read the history; in the synthesis, also the published prices.
- *Held fixed.*  `D̄` and its timing relative to decisions.
- *Desired.*  The synthesis's average `→ 1`.  The theorem this needs, in two halves,
  neither supplied by the fixture: (1) *the market side* — for the e.c. sequence
  `φ_k` decided by `D_k`, the market's price is unbiased on every `P`-generable weighting
  (**PAPER** `thm:wubaff` with the deferral condition), so the market-reading hypothesis
  `(A iff P_k(φ_k) > 1/2, 1)` is wrong on a density-zero set and coverage adopts it —
  the decision component is right with density `1` while spending only e.c. time on
  top of the market; (2) *the blind side* — a truth sequence on which every predictor
  computable in time below the deductive cost, **including any adaptive combination
  such as the blind auction as a whole**, errs with density bounded away from `0`: the
  diagonal against all clocked machines of the bounded runtime, each machine `j`
  contradicted on a residue class of density `2^{-j}`, which is computable in slightly
  more time and makes every such machine err with density `≥ 2^{-j}`.  The separation
  is by *runtime of the decision component against the deductive process*, and a blind
  decision component with runtime above the deductive cost is not separated.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  `D̄` decides `φ_k` before `k`; the blind class's runtime below the
  deductive cost; the diagonal sequence as stated.
- *Level.*  Criterion for the class `H^P`, **once the two halves are proved**; until
  then the row is a stated theorem target, G4(a).
- *The fixture* (**FIX** `test_interaction`, `src/logic_rewards.py`).  Three fixed
  blind predictors, a truth sequence diagonal against those three, and a market modelled
  as an oracle publishing the truth value after a warm-up: the blind auction over the
  three stays below `9/10`, the market-reading auction exceeds `99/100`.  This is an
  **interface illustration**: it does not simulate a logical inductor, it does not
  diagonalize against adaptive combinations (the full e.c. class can approach the
  diagonal's accuracy by simulating the contradicted predictor), and it is not a
  separation theorem.
- *Negative control.*  `φ_k` decided by `D̄` only after decision `k`, or undecided: the
  market has no advantage before the decision, both classes are at chance, the row is
  silent.
- *Diagnoses.*  G4(a), G7(i), G1's class choice.  A side-by-side LI and BRIA fails the
  proved form at criterion level; the fixture cannot show that.

## T11. Interaction: belief–claim compatibility

- *Environment.*  T6 per round with the frequency predictor; the candidate's witness
  estimates and its market's post-selection forecasts are recorded on the paying tails
  subsequence and on the whole sequence.
- *Desired.*  W1 (`PROBLEM_STATEMENT.md` §5): the whole-sequence average of
  `e_k − F⁺_k` has nonpositive limsup — criterion-level for any candidate with G2(c) and
  G3 and a published post-selection forecast.  The strong form on the tails weighting is
  G4(b)'s proposed requirement and is checked only for a candidate that claims it.
- *What the fixture shows* (**FIX** `CrossSubsidy_NoOverestimationOnly`).  The
  cross-subsidy agent's estimates sit `1/2` above any unbiased forecast on the paying
  tails subsequence while its whole-sequence overestimation is `≤ 0`: W1 can hold where
  the strong form fails, which is why the two are separated; and the same agent is not
  a BRIA (the heads tracker), so on this environment G3 already excludes it and the
  strong form is not what does the work.
- *Form.*  Asymptotic averages; sure.
- *Level.*  Criterion for W1; proposed for the strong form.
- *Negative control.*  The block-scored T6 with the lease predictor: claims and
  forecasts agree at `1/2`; the strong form holds at that granularity for the auction.
- *Diagnoses.*  G4(b) and its status; together with T10 the interaction diagnostic.

## Pruned

- *Smoking lesion*: the FDT paper's own verdict is that the problem is badly confused
  once the agent's population is asked to make the predictor accurate; in the realized
  register it is T4(ii) with a different story.
- *Absent-minded driver*: imperfect recall; the continuation has its unit's history.
- *Mechanical blackmail, Death on Olympus, the random-coin variant*: instances of T5 and
  T7 with parameters; recorded in `AUDIT.md`.
- *One-shot versions of every row*: register (iii), invisible; listed once in T3(a) and
  T7.

## The most discriminating rows

T6 (per round the criterion excludes paying by itself; per block with a channel it
selects paying; per block with a lagging predictor it selects refusing), T4(ii) (same
predictor, the scored unit flips the verdict; fixed schedules fail the full class),
T3(d) and T3(e) (criterion silent, construction decides), T8(b) (the original
obstruction preserved at criterion level), T10 (the interaction theorem target, with its
fixture marked as an illustration).  The level-2 diagnostics D1–D4 are
`PROBLEM_STATEMENT.md` §6.
