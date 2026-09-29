# The diagnostic test suite

Labels as in `PROBLEM_STATEMENT.md`; M1–M6, I1–I3, A1–A2 are its §2, §3, §7.  Every
retained test carries the same fields: environment; timing (observation, prediction,
decision, settlement); predictor access and computational restrictions; the comparison
class and what its members see; the success condition; mode and quantifiers; for whom
(every satisfying agent, or a designated construction); negative control or necessity
witness; **role** (recovery test, integration test, updateful advance test, ideal
updateless extension); **status** (established consequence, proposed acceptance
target, incomplete diagnostic); and **supplied structure** — any external commitment
contract, communication channel, oracle or menu restriction the row adds to the
primary-source problem, which makes its verdict a conditional result and never
progress on the problem without it.  Rewards are in `[0, 1]`.  The fixtures named are
in `src/`, run by `tests/run.py`; each is a finite prefix check against fixed bidders or
fixed agents on the paper's first-price auction, and none is evidence for a quantified
statement.

## T0. Passive logical reasoning

- *Environment.*  `|C_k| = 1` for all `k`; computable `D̄`; constant scores.
- *Timing.*  Prices at each decision; nothing to choose.
- *Access.*  Traders read prices and `D̄`; polynomial time.
- *Class.*  E.c. traders.
- *Success.*  The LI criterion relative to `D̄` (M2(b), a supporting milestone); for
  the endpoint, relative to the stream (M2(c)), which this row cannot see.  *Mode.*  Asymptotic; sure.  *For whom.*  Every satisfying agent.
- *Control.*  Constant prices on an e.c. sequence of theorems: exploited.
- *Role / status / supplied.*  Recovery / established consequence of M2 / none.
- *Why this condition.*  On the passive restriction the candidate is its market.

## T1. Transparent repeated choice: 5-and-10

- *Environment.*  Menu `{5, 10}`, rewards `1/2`, `1`; no predictor.
- *Timing.*  Choose, observe.  *Access.*  None.  *Class.*  E.c. hypotheses of the
  history; the constant `(10, 1)` is in it.
- *Success.*  Average `→ 1` (**PAPER** Thm 3).  *Mode.*  Asymptotic average; sure.
  *For whom.*  Every satisfying agent.
- *Control.*  The adversarial offer (Oesterheld and Conitzer 2021): boxes at cost `1`
  holding `3` iff the seller, at accuracy `3/4`, predicted the buyer would not take
  them; no randomization.  Abstaining is the sound higher claim; a design that learns
  a conditional expectation of an untaken option buys and loses.
- *Role / status / supplied.*  Recovery / established / none.
- *Why.*  The proof-based spurious-proof failure cannot arise: no proof about the
  untaken option enters a claim's settlement.

## T2. Self-confirming pessimism about a claimable option

- *Environment.*  Options `A` (`1/2`), `B` (`1`); initial prices or claims put `B` at
  `0`.
- *Timing.*  Choose, observe.  *Access.*  None.  *Class.*  Full e.c. class; the
  constant `(B, 1)` is in it whether or not anything knows it is right.
- *Success.*  Average `→ 1`.  *Mode.*  Asymptotic; sure.  *For whom.*  Every
  satisfying agent (M4: `(B, 1)` outpromises until tested and its tests refute the
  pessimism; the market's price of `B` is not consulted).
- *Control.*  `B` pays `0`: `(B, 1)`'s record diverges, the agent stays on `A` with
  sparse re-tests (**FIX** `test_troll.AlwaysBlown`, the same shape).
- *Role / status / supplied.*  Recovery / established consequence of M4 / none.
- *Why.*  It records that self-confirming pessimism about a *claimable* option is not
  a live obstruction for a BRIA on the full class; the live forms are T10 (the option is
  hard to identify) and A1 (the outcome depends on the forecast).

## T3. The Troll Bridge family

Options `stay` (`1/2`), `cross` (`1` unless the troll fires, then `0`); each variant is
the troll's condition (**FIX** `src/troll.py`).  Primary source: Demski 2019, results due
to Eisenstat — one-shot, proof-based, the troll reading the consistency of the agent's
theory; every repeated variant changes the register and the troll's access.

- **(a) Löbian one-shot.**  *Status: invisible* to every guarantee here; kept to say
  that passing (b)–(f) is not passing (a).  Register (iii).
- **(b) Action-only troll** (always / never).  *Success:* `→ 1` when never; `→ 1/2` with
  sparse tests when always (**FIX** `SafeBridge`, `AlwaysBlown`).  *For whom:* every
  satisfying agent.  *Role / status / supplied:* recovery / established / the troll's
  access changed from the theory's consistency to the action.
- **(c) Exploration-flag troll.**  A design with an exploration step distinct from
  choice exposes the flag and never learns crossing's value; a candidate whose tests
  are choices exposes no flag.  *Role / status / supplied:* construction-level
  diagnostic / established for the auction / the troll's access changed; passing is
  not passing (a).
- **(d) Tentative troll** (fires iff a published estimate on a crossing round is below
  `1`).  The paper's auction is a BRIA on every reward sequence (**PAPER** Thm 1) and is
  stuck at `1/2`; the always-cross agent at estimate `1` is a BRIA at `1`; the
  full-confidence bidding rule crosses (**FIX** `TentativeTroll`).  *For whom:* a
  designated construction only; the criterion is silent (no option guarantees a
  reward).  *Role / status / supplied:* construction-level / established for these
  constructions / applies only to candidates that publish estimates.  Provisional D2 is
  its refinement.
- **(e) Belief-disagreement troll** (fires iff the action differs from the argmax of
  the published pre-selection forecasts).  Two self-consistent fixed points; the
  criterion does not select.  *This is A1*, `PROBLEM_STATEMENT.md` §7, with its success
  condition (crossing with density `1` from every M2-consistent initial market).
  *Role / status / supplied:* proposed instance of I3 and of the advance /
  **provisional** — the semantics of the pre-selection forecast the troll reads is
  undefined, the two configurations are proposed failure configurations not checked
  against M1–M4, and a favourable report changes the environment / the troll reads
  prices the belief component publishes anyway — no new channel, once those prices are
  defined.  The fixture does not simulate a market and does not score this row.
- **(f) Consistency troll** (fires iff `Γ` is inconsistent).  A fixed fact; `(cross, 1)`
  is sound iff `Γ` is consistent and coverage adopts it whatever the Löbian prices.
  *Role / status:* recovery / established; a caution that it says nothing about (a).

Common fields: timing choose–observe; the troll reads the named public state and
nothing else; the full e.c. class with the constant crossing hypothesis; asymptotic
average, sure; negative controls are the sibling variants.

## T4. Prediction-sensitive choice: Newcomb with realized feedback

- *Environment.*  Options `one`, `two`; predicted `one`: `999/1000`, `1`; predicted
  `two`: `0`, `1/1000` (**FIX** `src/newcomb.py`).  Primary source: one-shot, predictor
  mechanism unspecified; every row here is repeated with a named mechanism.
- *Timing.*  Per round: predict, choose, observe.  Block: one continuation for `m`
  rounds.
- *Access.*  (i) *Lease*: the predictor reads the selection through a **supplied
  channel**.  (ii) *Frequency*: predicts `one` iff a strict majority of past rounds
  one-boxed; reads nothing of the current round.  (iii) (i) at accuracy `p`.
- *Class.*  Full e.c. class of the history (the contextual two-boxer and the
  constant one-boxer are in it).
- *Success.*  (i) one-box, `→ 999/1000` per round and per block (**FIX**
  `LeasePredictor`).  (ii) per round: two-box is what M3 settles on — the one-boxing
  agent fails coverage against the sound contextual two-boxer (**FIX**); the two-boxing
  agent covers the two fixed bidders checked, and with a fixed sparse test schedule and
  estimate `1/1000` off it is refuted by the off-schedule attacker (**FIX**; the
  conditional obstruction of §4).  Block with within-block memory: one-box at
  `(m−1)/m · 999/1000` (**FIX** `FrequencyPredictorBlock`).  (iii) one-box iff
  `(999/1000)·p > (1−p) + p/1000`, i.e. `p > 500/999`.
- *Mode.*  Asymptotic average; sure.  *For whom.*  Every satisfying agent for the
  exclusions; the auction under (ii) per round cycles at every finite horizon the
  fixtures afford (**FIX** `test_auction_cycles_at_finite_horizon`; Bell et al. 2021).
- *Control.*  (ii) per round against (ii) per block: the scored unit flips the verdict.
- *Role / status / supplied.*  (ii): recovery / established consequence of M3 / none.
  (i), (iii): conditional results / established for the auction / a commitment channel
  and, for the block rows, an execution contract — not the primary-source problem.

## T5. Adversarial prediction and randomization: Death in Damascus

- *Environment.*  `stay`, `flee`; Death predicts the option and is there; matched pays
  `0`, unmatched `1`; optionally `coin`, choosing by a private random bit.
- *Timing.*  Predict, choose, observe.  *Access.*  Death reads the choice; in the
  control, the bit.  *Class.*  Full e.c. class.
- *Success.*  Without `coin`: estimates `0`, average `0` (nothing guarantees anything).
  With `coin` and Death blind to the bit: average `≥ 1/2` (**PAPER** Thm 4).  *Mode.*
  Asymptotic average; almost sure over the bits.  *For whom.*  Every satisfying agent,
  given `coin`.
- *Control.*  Death reads the bit: `coin` pays `0`.
- *Role / status / supplied.*  Recovery / established / **a menu restriction lifted**
  (`coin` added) — a declared change, `AUDIT.md` §3.

## T6. Policy-level against locally conditional improvement: repeated counterfactual mugging

- *Environment.*  Heads rounds (single option; `1` iff the predictor predicts paying)
  alternate with tails rounds (`pay` at `0`, `refuse` at `1/2`) (**FIX** `src/cm.py`).
- *Timing.*  Three scorings: per round; per block of one heads and one tails round;
  one-shot.
- *Access.*  (i) *Policy*: the predictor reads the agent's limiting tails choice (the
  original Omega, repeated).  (ii) *Frequency*: predicts paying iff the agent has paid
  more often than refused.  (iii) *Lease*: the block continuation through a **supplied
  channel**.  (iv) *Lagging*: the previous block's realized tails choice.
- *Class.*  Full e.c. class of the history; the heads tracker and the exact refuser are
  in it.
- *Success.*  Per round with (i) or (ii): every BRIA on the full class pays on a
  density-zero set (P1′; **FIX** `PerRoundBRIAExcludesPaying`,
  `CrossSubsidy_NoOverestimationOnly`); the auction under (ii) settles on refusing
  with sparse paying tests and heads at `0` (**FIX** `PerRoundAuction`).  Per block
  with (iii): pay, `→ 1/2` (**FIX** `BlockScoring`).  One-shot: register (iii),
  invisible.
- *Mode.*  Asymptotic average; sure.  *For whom.*  Every satisfying agent for the
  per-round exclusion (under P1′'s trackability hypothesis, which (i), (ii), (iv)
  meet); the auction for the block verdict.
- *Control.*  Per block with (iv): refusing's contextual claim `3/4` after a paying
  block is sound and higher; the auction refuses at `1/4` plus sparse re-tests (**FIX**
  `test_lagging_predictor_refuses`).
- *Role / status / supplied.*  Per round (i)/(ii): recovery boundary / established
  (P1′) / none — and the ideal-extension row **A2** scores the same environment with
  the opposite success condition.  Per block (iii): conditional result / established
  for the auction / an execution contract and a channel.
- *Why.*  It is the exact boundary between unit-level recovery on the full class and
  cross-unit commitment, and the place where the updateless extension's recovery
  domain is undefined (`PROBLEM_STATEMENT.md` §2 M3).

## T7. Commitment timing and revision

Parfit's hitchhiker, transparent Newcomb, XOR blackmail as two-stage blocks with the
predictor reading the block continuation through a **supplied channel** under an
**execution contract**.  *Success.*  The committing continuation's claim is sound and
higher and is selected; for XOR blackmail, refusing's block value exceeds paying's by
`(1−p)·payment`.  *Controls.*  The second stage as a fresh block predicted afresh:
reneging is the sound higher claim and the agent is left; a blackmailer that reads
nothing: the letter is evidence and paying is worse still.  *Mode.*  Asymptotic
average over repeated blocks; sure.  *For whom.*  Every satisfying agent at block
granularity.  *Role / status / supplied.*  Conditional results on the external-contract
source of M5 / established for the block form / contract and channel — a candidate
says which of M5's three commitment sources it relies on, and none of these rows is
progress on the primary-source one-shot problems.

## T8. Changes in available reasoning: bounded-simulation Newcomb

- *Primary source.*  Agent Simulates Predictor (Slepnev 2011, credited to Drescher
  2010): a proof-bounded predictor reasoning about the agent's procedure, knowing the
  agent's system consistent; the agent can simulate the predictor; a proof-based
  one-boxer two-boxes and gets the small prize.  Obstruction: the more capable
  reasoner loses.
- *Environment here.*  Newcomb rewards; the predictor has runtime bound `g(n)` below
  the agent's per-round budget.  Two access rules: (a) reads the selection through a
  **supplied channel** — not the original; (b) simulates the agent's algorithm for
  `g(n)` steps and defaults to two-boxing when unfinished — a bounded-simulation
  variant whose equivalence to, or preservation of, the original's obstruction is
  **not established**.
- *Success.*  (a) one-box (T4(i)).  (b) the predictor predicts one-boxing **and** the
  agent one-boxes, jointly with density `1`, under the assumption that a finished
  simulation is faithful; one-boxing frequency alone is not the condition, since a
  defaulting predictor leaves the box empty.
- *What is not claimed.*  That the synthesis two-boxes under (b): the first two passes
  inferred it from Thm 2 (no `O(g)` agent covers the `O(g)` class), which is a worst-case
  statement about the agent and says nothing about its actual per-round runtime on this
  sequence or the frequency with which the simulation finishes.  The row's verdict under
  (b) depends on that accounting, which no candidate has supplied.
- *Mode.*  Asymptotic density; sure.  *For whom.*  A designated construction.
- *Control.*  (a) against (b): the channel alone changes the verdict, which is why (a)
  is not ASP.
- *Role / status / supplied.*  (a): conditional / established for the auction /
  channel.  (b): incomplete diagnostic (provisional D3) / the runtime accounting
  missing / none.

## T9. Copies and related agents

Two candidates in a repeated prisoner's dilemma reading each other's realized past
play.  *Success.*  None at criterion level: **PAPER** Thm 5 — any strictly
individually rational correlated profile is the limit play of some BRIAs.  *Role /
status.*  Construction-level / established silence.  Kept because the criterion is
provably silent by a published theorem.

## T10. Integration: rewards decided by logic (I1)

- *Environment.*  Options `A`, `B`; `A` pays `1` iff `φ_k` is true, `B` iff false; `φ_k`
  an e.c. sequence of sentences each decided by `D̄` **before** decision `k` (`φ_k` or
  `¬φ_k ∈ D_k`), the deciding computation costing `T(k)`.
- *Timing.*  `D_k` formed; market published (its price of `φ_k` informed by `D_k`);
  hypotheses read prices; choose; observe.  Eventual settlement is not pre-decision
  predictability: the deduction argument below needs `φ_k` decided before `k`.
- *Access and computation, both sides.*  Both decision components see the history
  (past rewards reveal past truth values) and run in time `t(k)` per round.  The
  synthesis's decision component additionally reads the published prices; the market's
  own cost, at least `T(k)`, is accounted to the belief component and is the point: the
  expensive deduction lives there and the decision component consumes it cheaply.
- *Class.*  Blind side: predictors computable in time `t(k)` with the history
  (including any adaptive combination — the blind auction as a whole is one such
  predictor, of a fixed index).  Synthesis side: `H^P`.
- *Success.*  The synthesis's average `→ 1` while every blind predictor's is `≤ 1 − δ`
  for a `δ > 0` depending on the predictor.
- *The theorem target, in its distinct parts* (none supplied here; each named so that
  no step is taken without proof):
  1. *Pre-decision accuracy.*  For an e.c. sequence of sentences each in `D_k` at
     decision `k`, the market's price `P_k(φ_k)` converges pointwise to the truth value
     — a timely-learning property of the pinned formalization, to be cited at its exact
     label (the provability-induction theorem gives it for e.c. sequences of theorems;
     the form for `D̄`-decided sentences is to be verified, not assumed).  Pointwise
     convergence, not vanishing average error, is what step 3 needs.
  2. *The market-reading bidder.*  `(A iff P_k(φ_k) > 1/2, promise 1 − ε)`, e.c. relative
     to the prices.  With step 1 it is wrong finitely often, so its record on **any**
     test set is bounded below by `ε·#tests − O(1)`: resistance to refutation without
     any assumption on the endogenous test set.  (With only vanishing average error
     this fails — the cumulative-loss gap of §5 — which is why step 1 must be pointwise.)
  3. *Adoption.*  Coverage then forces the estimate `≥ 1 − ε` cofinitely; no
     overestimation forces the average `≥ 1 − ε`; `ε → 0`.
  4. *The blind lower bound.*  A truth sequence, computable in time `T(k)` and hence
     decidable by `D̄` before `k`, on which every predictor of runtime `t(k) ≪ T(k)` —
     each clocked machine `j` contradicted on a residue class of density `2^{-j}` —
     errs with density `≥ 2^{-j}`.  Every blind decision component is one such
     machine, of a fixed index; the density bound is per predictor and is not a bound
     on the best of a sequence of predictors of growing index.
- *Mode.*  Asymptotic average; sure.  *For whom.*  Every satisfying agent with class
  `H^P`, once steps 1–4 are proved.
- *Control.*  `φ_k` decided only after `k`: the stated pre-decision deduction argument
  no longer guarantees an advantage.  It does not follow that the market is at chance —
  a market may predict a sentence before its deductive settlement from other patterns
  or arguments — so no chance-performance control is claimed without an explicit
  unpredictability assumption on the sequence, which this row does not supply.
- *The fixture* (**FIX** `test_interaction`, `src/logic_rewards.py`): three fixed blind
  predictors, a truth sequence diagonal against those three, a market modelled as an
  oracle publishing the truth after a warm-up; the blind auction over the three stays
  below `9/10`, the market-reading auction exceeds `99/100`.  An **interface
  illustration**: no logical inductor is simulated, no adaptive combination is
  diagonalized against, no step above is evidenced.
- *Role / status / supplied.*  Integration (I1) / proposed acceptance target with the
  four steps unproved / the market's deductive cost, accounted explicitly.

## T11. Integration: belief–claim compatibility (I2)

- *Environment.*  T6 per round with the frequency predictor; the candidate's witness
  estimates and its post-selection forecasts recorded on the whole sequence and on the
  paying tails subsequence.
- *Success.*  W1: whole-sequence `limsup (1/K) Σ (e_k − F⁺_k) ≤ 0` — for any candidate
  with M2(c), M3 and a post-selection forecast published after the selection.  The
  strong form on the tails weighting is the proposed requirement of §5, checked only
  for a candidate that claims it, with the timing and generability conditions there.
- *What the fixture shows* (**FIX** `CrossSubsidy_NoOverestimationOnly`).  The
  cross-subsidy agent's estimates sit `1/2` above any unbiased post-selection forecast
  on the paying tails subsequence while its whole-sequence overestimation is `≤ 0`: W1
  can hold where the strong form fails.  The same agent is not a BRIA (the heads
  tracker), so on this environment M3 does the excluding and the strong form is not
  what does the work.
- *Mode.*  Asymptotic averages; sure.  *For whom.*  Every satisfying agent for W1.
- *Control.*  Block-scored T6 with the lease predictor: claims and forecasts agree at
  `1/2` for the auction.
- *Role / status / supplied.*  Integration (I2) / W1 established, strong form proposed
  / none.

## Pruned

Smoking lesion (the FDT paper calls it confused; in the realized register it is T4(ii));
absent-minded driver (imperfect recall; the continuation has its unit's history);
mechanical blackmail, Death on Olympus, the random coin (parameters of T5 and T7);
one-shot versions of every row (register (iii), invisible).

## The most discriminating rows

T6 per round (the recovery boundary; the same environment is A2's target with the
opposite success condition), T4(ii) (the scored unit flips the verdict; the conditional
fixed-schedule obstruction), T3(e) = A1 (a proposed failure configuration, provisional
until its forecast semantics is fixed), T10 (the integration theorem, with four unproved steps named
and its fixture marked as an illustration), T8(b) (an incomplete diagnostic whose
verdict waits on a runtime accounting).
