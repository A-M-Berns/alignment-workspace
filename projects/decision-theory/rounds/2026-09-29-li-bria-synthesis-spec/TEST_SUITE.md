# The diagnostic test suite

Labels as in `PROBLEM_STATEMENT.md`.  Every benchmark carries the same ten fields.
*Level* says whether every agent satisfying the minimum credible synthesis (MCS) must
pass (**criterion**), or whether the criterion is silent and the row diagnoses a
designated construction (**construction**), or whether the guarantee cannot see the
distinction at all (**invisible**, kept only to say so).  Rewards are in `[0, 1]`;
"lease" means the published selection of the current block; the fixtures named are in
`src/` and run by `tests/run.py` on the paper's first-price auction with unit blocks,
which stands in for "a designated construction" wherever one is needed.

A row's verdict is a claim about a *specified* environment.  A familiar name does not
fix the predictor's access, the scoring granularity, whether randomization is available
or whether the problem is one-shot, and each of those flips at least one verdict below.

## T0. Passive logical reasoning

- *Environment.*  `|C_k| = 1` for all `k`; a computable deductive process `D̄` over `Γ`;
  scores constant.
- *Timeline.*  Prices published at each block; nothing to choose.
- *Access.*  Traders read the published prices and `D̄`.
- *Held fixed.*  `D̄`.
- *Desired.*  The published market satisfies the LI criterion relative to `D̄` (R2(b));
  under R2(c) the same with the stream.  Justification: on the passive restriction the
  synthesis *is* its market.
- *Form.*  Asymptotic; sure.
- *Assumptions.*  `D̄` computable.
- *Level.*  Criterion.
- *Negative control.*  A market with a fixed exploitable pattern (constant prices on an
  e.c. sequence of theorems): fails; the row is not vacuous.
- *Diagnoses.*  R2.  It cannot see R2(c)'s active clause; T10/T11 do.

## T1. Transparent repeated choice: 5-and-10

- *Environment.*  Menu `{5, 10}` every round, rewards `1/2` and `1`, no predictor.
- *Timeline.*  Choose, observe.
- *Access.*  None.
- *Held fixed.*  Nothing beyond the round.
- *Desired.*  Average reward `→ 1` (**PAPER** Thm 3 with `L_t = 1` on `10`).  The
  proof-based pathology — a spurious proof that taking `10` yields less — has no
  purchase because no proof about the untaken option enters any claim's settlement.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  The e.c. hypothesis `(10, 1)` is in the class (it is constant).
- *Level.*  Criterion.
- *Negative control.*  The adversarial offer (Oesterheld and Conitzer 2021): two boxes at
  cost `1`, each holding `3` iff the seller, at accuracy `3/4`, predicted the buyer would
  not take it; no randomization.  Abstaining is the sound higher claim; a design that
  learns "the expected content of a box" as a conditional expectation of an untaken
  option buys and loses.  Verdict flips because the reward now depends on the policy.
- *Diagnoses.*  R3 (Thm 3 form); the control diagnoses register (i) against conditional
  expectations of untaken actions.

## T2. Self-confirming pessimism

- *Environment.*  Options `A` (reward `1/2`) and `B` (reward `1`); the agent starts with
  prices or initial claims that put `B`'s reward at `0`.
- *Timeline.*  Choose, observe.
- *Access.*  None.
- *Held fixed.*  The round.
- *Desired.*  Average `→ 1`: the hypothesis `(B, 1)` outpromises until tested, and its
  tests refute the pessimism (R5).  Justification: coverage does not consult the market's
  price of the untested option.
- *Form.*  Asymptotic; sure.
- *Assumptions.*  `B` in the menu; no trap.
- *Level.*  Criterion.
- *Negative control.*  `B` pays `0`: the pessimism is correct, `(B, 1)`'s record diverges,
  and the agent stays on `A` with sparse re-tests (**FIX** `test_troll.AlwaysBlown`, the
  same shape).  A second control is T3(d), where pessimism becomes self-confirming
  through the agent's own public estimate.
- *Diagnoses.*  R5; with the second control, the boundary between R5 and construction
  behaviour.

## T3. The Troll Bridge family

Options `stay` (`1/2`) and `cross` (`1` unless the troll fires, then `0`).  Each variant
is the troll's condition, a function of a named part of the state (**FIX** `src/troll.py`).

- **(a) Löbian, one-shot, proof-based** (Demski 2019, results due to Eisenstat).  The
  troll reads the consistency of the agent's theory; the agent proves `cross → −10` by
  Löb and stays.  *Level: invisible.*  The realized-feedback guarantee says nothing
  about a single decision, and the synthesis makes no proof about its own action; the
  row is kept to record that passing (b)–(f) is not passing (a).  Register (iii).
- **(b) Action-only troll**: fires always, or never.  *Desired:* average `→ 1` when
  never, `→ 1/2` with sparse tests when always (**FIX** `SafeBridge`, `AlwaysBlown`).
  *Level: criterion.*  Diagnoses R3/R5.
- **(c) Exploration-flag troll**: fires iff the crossing was an exploration step.  For a
  design with an exploration mechanism distinct from choice — ε-exploration on an LI
  argmax — the flag is public state and the design never learns crossing's value
  (Demski 2019; Diffractor 2018).  For the synthesis there is no flag: a test is the
  winning claim's execution.  *Level: construction* — it discriminates designs with an
  exploration flag from claim-driven testing.  Diagnoses R5's "test is choice" clause.
- **(d) Tentative troll**: fires iff the published estimate on a crossing round is below
  `1`.  The paper's auction tests `cross` only at a wealth-capped bid, is blown up every
  time, and stays forever with sparse losing tests, while satisfying both BRIA
  conditions on every prefix; the agent that always crosses at estimate `1` satisfies
  the criterion and gets `1`; the variant auction that bids only at full confidence
  crosses (**FIX** `TentativeTroll`, three tests).  *Level: construction*: Thm 3 does not
  apply because no option *guarantees* a reward, so the criterion is silent and the
  outcome is the auction format's.  Diagnoses lease publicity (the estimate is public
  state) and the test-timing of a construction.
- **(e) Belief-disagreement troll**: fires iff the action differs from the argmax of the
  published market's expectations.  Two self-consistent pairs exist — cross with the
  market expecting `1`, stay with the market expecting `0` for crossing — and R2–R4 hold
  in both; the criterion does not select.  *Level: construction* (equilibrium
  selection).  Diagnoses the limit of R4: agreement between belief and choice does not
  say which agreeing pair is reached.
- **(f) Consistency troll**: fires iff `Γ` is inconsistent.  In the repeated register
  the troll's condition is a fixed fact, the sound hypothesis `(cross, 1)` exists iff
  `Γ` is consistent, and coverage adopts it whatever the market's Löbian prices; passing
  says nothing about (a).  *Level: criterion*, and a caution.

Fields common to (b)–(f): timeline choose–observe; the troll reads the named public
state and nothing else; the round is held fixed; asymptotic average, sure; assumptions
as in T1; negative controls are the sibling variants.

## T4. Prediction-sensitive choice: Newcomb with realized feedback

- *Environment.*  Options `one`, `two`; if the predictor predicts `one`: `999/1000` and
  `1`; if `two`: `0` and `1/1000` (**FIX** `src/newcomb.py`).
- *Timeline.*  Per-round: predict, choose, observe.  Block: one continuation for `m`
  rounds.
- *Access, four cases.*  (i) *Lease*: the predictor reads the published selection of the
  round or block.  (ii) *Frequency*: it predicts `one` iff a strict majority of past
  rounds one-boxed, never reading the current round.  (iii) *Imperfect lease*: (i) with
  accuracy `p`.  (iv) *Simulation with a runtime bound*: T8.
- *Held fixed.*  The predictor's rule; per-round, the round; block, the contract.
- *Desired.*  (i) one-box, average `→ 999/1000`, per round and per block (**FIX**
  `LeasePredictor`): `(two, 1)` is refuted, `(one, 999/1000)` is sound.  (ii) per-round:
  two-box is what the criterion settles on — the one-boxing agent fails coverage against
  the sound contextual two-boxer, the two-boxing agent with sparse one-box tests is
  covered (**FIX** `FrequencyPredictorPerRound`); block with within-block memory:
  one-box, `(m−1)/m · 999/1000` (**FIX** `FrequencyPredictorBlock`).  (iii) the sound
  claims order by `p`: one-box iff `(999/1000)·p > (1−p) + p/1000`, i.e. `p > 500/999`.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  The predictor's rule is a function of the named public state.
- *Level.*  Criterion for (i), (ii), (iii).  The paper's auction under (ii) per round
  cycles at every finite horizon the fixtures can afford (**FIX**
  `test_auction_cycles_at_finite_horizon`): both options win with positive frequency
  over 400 rounds, the shape of the non-convergence of value-based learners in
  Newcomblike environments (Bell et al. 2021, `AUDIT.md`).
- *Negative control.*  (ii) per round against (ii) per block: the same predictor, the
  same rewards, opposite verdicts, by scoring granularity alone.
- *Diagnoses.*  R3, R6, the granularity choice, lease publicity.

## T5. Adversarial prediction and randomization: Death in Damascus

- *Environment.*  Options `stay`, `flee`; Death predicts the option and is there; the
  matched option pays `0`, the unmatched `1`; optionally a third option `coin` that
  chooses by a private random bit.
- *Timeline.*  Predict, choose, observe.
- *Access.*  Death reads the lease; in the control, also the random bit.
- *Held fixed.*  Death's rule.
- *Desired.*  Without `coin`: no pure option guarantees anything; the criterion is
  satisfied by estimates `0`, average `0`.  With `coin` and Death blind to the bit: the
  rewards on `coin`'s rounds are boundedly random with mean `1/2`, so **PAPER** Thm 4
  (random-reward form) gives average `≥ 1/2`; Thm 5's folk-theorem construction shows
  the criterion itself does not require a random source.
- *Form.*  Asymptotic average; almost sure over the bits.
- *Assumptions.*  `coin` in the menu; the bit private and unpredictable in the paper's
  vMWC sense relative to the class.
- *Level.*  Criterion, given `coin`.
- *Negative control.*  Death reads the bit: `coin` pays `0`, and nothing in the menu is
  worth more than `0`.
- *Diagnoses.*  Whether randomization is a menu option (declared choice, `AUDIT.md` §3)
  and R3's random-reward clause.  A design that treats mental randomization as
  unpredictable by stipulation is answering a different environment.

## T6. Policy-level against locally conditional improvement: repeated counterfactual mugging

- *Environment.*  Heads rounds (single option; `1` iff the predictor predicts paying)
  alternate with tails rounds (`pay` at `0`, `refuse` at `1/2`) (**FIX** `src/cm.py`).
- *Timeline.*  Three scorings: per round; per block of one heads and one tails round;
  one-shot.
- *Access.*  (i) *Policy*: the predictor reads the agent's limiting tails choice.  (ii)
  *Lease*: the block continuation.  (iii) *Lagging*: the previous block's realized tails
  choice.
- *Held fixed.*  Per round, the round; per block, the contract.
- *Desired.*  Per round with (i): every agent satisfying R2(c), R3 and R4 per round
  refuses on all but a density-zero set (`PROBLEM_STATEMENT.md` P1, **FIX**
  `test_cm.P1`), though paying averages `1/2` against `1/4`; without R4 a paying BRIA
  exists (P2, **FIX** `test_cm.P2`).  Per block with (ii): pay, average `→ 1/2` (**FIX**
  `BlockScoring`).  One-shot: register (iii), invisible.
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  The predictor's rule as named.
- *Level.*  Criterion for the per-round exclusion and the block verdict.
- *Negative control.*  Per block with (iii): refusing's contextual claim `3/4` after a
  paying block is sound and higher, coverage settles on refusing, the average is `1/4`
  plus the sparse re-tests (**FIX** `test_lagging_predictor_refuses`).  Same rewards,
  same block, opposite verdict, by what the predictor reads.
- *Diagnoses.*  The conflict of `PROBLEM_STATEMENT.md` §3 exactly: R3 with R4 at one
  granularity against commitment at another; the declared resolution and its residue.

## T7. Commitment timing and revision

Three problems with the same shape: a first stage in which a predictor reads what the
agent will do at a second stage, and a second stage at which reneging is locally better.

- *Parfit's hitchhiker.*  Block = (desert, town).  Driver reads the block continuation;
  rescued iff it pays; block score `= rescued − payment` in `[0,1]` units.  *Desired:*
  the paying continuation's claim is sound and higher; selected (**criterion**, the
  same shape as T6 per block).  *Negative control:* the town stage is a new block with
  its own contract, and the driver predicts that fresh block: reneging is then the
  sound higher claim at town, the driver predicts it, and the agent is left.  The lease
  boundary is the commitment boundary; a candidate must say where its blocks end.
- *Transparent Newcomb.*  Block = (predictor fills, agent sees, agent chooses); the
  predictor reads the continuation "one-box on seeing both full".  Same verdict and
  control as Parfit.
- *XOR blackmail.*  Block = (termite state drawn, letter sent iff exactly one of
  termites / would-pay, agent chooses).  Blackmailer reads the continuation.  Refusing's
  block value exceeds paying's by `(1−p)·payment`; refuse (**criterion**).  *Control:*
  the letter's arrival is exogenous to the continuation (a blackmailer that reads
  nothing): the letter carries evidence and paying is worse still; the row does not
  separate EDT from the synthesis, and is kept only for its control.
- *Fields.*  Timeline as stated; access = the block continuation; held fixed = the
  contract; asymptotic average over repeated blocks, sure; assumption = the predictor is
  a function of the published continuation.
- *Diagnoses.*  R7(a) (the lease is the commitment), R7(c) (a commitment longer than a
  block is not representable), lease publicity.  One-shot versions: register (iii).

## T8. Changes in available reasoning: Agent Simulates Predictor

- *Environment.*  Newcomb rewards; the predictor has runtime bound `g(n)` below the
  agent's `n`.
- *Timeline.*  Predict, choose, observe; per round or per block.
- *Access, two cases.*  (a) The predictor reads the published lease.  (b) The predictor
  simulates the agent for `g(n)` steps, and predicts `two` when the simulation does not
  finish.
- *Held fixed.*  The predictor's rule and bound.
- *Desired.*  (a) one-box, as T4(i).  (b) one-boxing pays `0` whenever the simulation
  is unfinished, so `(one, 999/1000)` is refuted and the criterion settles on two-box; a
  cheaply verifiable commitment helps only if the predictor can read it, which is (a).
  So the verdict is the publicity choice: a synthesis passes ASP iff its selection is
  public before the predictor commits, and the market's beliefs about the predictor's
  output (the logical-time ordering of Demski 2018) play no role in the realized register.
- *Form.*  Asymptotic; sure.
- *Assumptions.*  `g(n) < n` and the predictor's default named.
- *Level.*  Criterion under each access rule; the *choice* of rule is declared.
- *Negative control.*  (a) against (b).
- *Diagnoses.*  R8(i), lease publicity; that reasoning-power asymmetry enters only
  through what is published.

## T9. Copies and related agents

- *Environment.*  Two syntheses in a repeated prisoner's dilemma, block-scored, each
  reading the other's published lease.
- *Desired.*  None at criterion level: **PAPER** Thm 5 — for any strictly individually
  rational correlated profile there are BRIAs whose play converges to it, and BRIAs
  covering the constant hypotheses obtain at least maximin.  The criterion does not
  select cooperation.
- *Level.*  Construction only.  Kept because it is the one row where the criterion is
  provably silent by a published theorem; a candidate that claims cooperation claims it
  for its construction, and the modal-agent results (Barasz et al. 2014) are the
  comparison.
- *Diagnoses.*  Nothing in R1–R8; it bounds what the specification asks.

## T10. Interaction: rewards decided by logic

- *Environment.*  Options `A`, `B`; `A` pays `1` iff `φ_k` is true, `B` iff false; the
  truth values are a diagonal sequence against every predictor in a finite blind class,
  decided by `D̄` within a deferral (**FIX** `src/logic_rewards.py`, the market modelled
  as an oracle publishing the truth value after the deferral).
- *Timeline.*  Market published, choose, observe.
- *Access.*  Hypotheses read the history; in the synthesis, also the published prices.
- *Held fixed.*  `D̄`.
- *Desired.*  The synthesis's average `→ 1`: the market-reading hypothesis
  `(A iff P_k(φ_k) > 1/2, 1)` is e.c. relative to the prices and sound after the deferral
  (unbiasedness from feedback, or provability induction on the decided sequence), and
  coverage adopts it.  A class without the market has no hypothesis sound cofinitely,
  and its average stays below `9/10` on the fixture (**FIX** `test_interaction`).
- *Form.*  Asymptotic average; sure.
- *Assumptions.*  A truth sequence not predictable with vanishing error by any
  `O(g)`-computable function of the history — a diagonalization against the class, the
  fixture's finite instance being three blind predictors each wrong on its residue
  class — decided by `D̄` within a computable deferral.
- *Level.*  Criterion, for the class `H^P`.
- *Negative control.*  `φ_k` undecided by `D̄`: the market cannot help, both classes are
  at chance, and the row is silent.
- *Diagnoses.*  R8(i), R1's class choice: a side-by-side LI and BRIA fails here at
  criterion level.

## T11. Interaction: belief–claim persistence

- *Environment.*  T6 per round with the policy predictor; a candidate's claims and its
  market's expectations are recorded on the paying tails subsequence.
- *Desired.*  R4 on that `P`-generable weighting: the weighted mean of
  `e_k − E_k(Ĝ_k)` tends to `0`.  The cross-subsidy agent of P2 is a BRIA whose claims
  sit `1/2` above its market's expectation on that subsequence forever: it fails.  A
  candidate whose claim is the market's expectation of the *best* option rather than the
  *chosen* one fails the same-quantity clause on any environment where the two differ.
- *Form.*  Asymptotic weighted mean; sure.
- *Level.*  Criterion.
- *Negative control.*  The block-scored T6 with the lease predictor: claims and
  expectations agree at `1/2`, and the same candidate passes — so the row measures
  compatibility at the declared granularity, not a fixed verdict.
- *Diagnoses.*  R4; T10 and T11 together are the interaction diagnostic of
  `PROBLEM_STATEMENT.md` §4.

## Pruned

- *Smoking lesion*: the FDT paper's own verdict is that the problem is badly confused
  once the agent's population is asked to make the predictor accurate; in the realized
  register it is T4(ii) with a different story.  Dropped.
- *Absent-minded driver*: imperfect recall; the block contract gives the continuation
  the block's history.  Dropped as not in the type.
- *Mechanical blackmail, Death on Olympus, the random-coin variant*: instances of T5 and
  T7 with parameters; recorded in `AUDIT.md`, not separate rows.
- *One-shot versions of every row*: register (iii), invisible to every guarantee here;
  listed once in T3(a) and T7 rather than per row.

## The most discriminating rows

T6 (three scorings, three predictors), T3(d) and T3(e) (criterion silent, construction
decides), T4(ii) (same predictor, granularity flips the verdict), T8 (publicity decides),
T10 (side-by-side fails at criterion level).
