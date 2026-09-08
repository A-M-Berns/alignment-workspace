# Report

Five passes on one round.  The first pass's verdict was
`GROWING-HORIZON-CONTINUATION-BRIA-SURVIVES-UNDER-NON-DOMINANCE-POLICY-REGRET-NEEDS-RECOVERABILITY`;
the pressure pass superseded it with `CONTINUATION-BRIA-READY-NONDOMINANCE-IFF-REPAIRED`;
the final correctness pass with `CONTINUATION-BRIA-READY-AFTER-FINAL-CORRECTNESS-PASS`;
the allowance-timing audit with `CONTINUATION-BRIA-READY-TIMING-ALIGNED`; the closing pass
(`PRESSURE_PASS.md` §14) canonicalised and merged.  Verdict:
**CONTINUATION-BRIA-CANONICALIZED-AND-MERGED.**

## Allowance-timing audit (fourth dispatch) — what changed

| earlier claim | finding | repair |
|---|---|---|
| the Python weighted auction is "the paper's construction" | Python credited the round's allowance *before* bids (opening timing); the paper and the old Lean credit it *after* (settlement timing) | one timeline (`WEIGHTED_BRIA.md` §3); the weighted construction is the paper's auction with opening subsidy — DERIVED, named as a modification; bid-for-bid the paper's auction under a reindexed allowance with an initial endowment (`test_timing.Reindexing`) |
| the prefix rule works under the stated (settlement) timing | false: on a spiky non-dominant schedule the current `ΔM_k` arrives one block late and a spike-only liar is never tested (`test_timing.SurpriseSpike`); for every prefix-online rule under settlement timing there is such a schedule (III′) | opening timing; `Feasible` (source) and `FeasibleOpening` (weighted) in Lean, sharing the recursion |
| capital adequacy `A_i(K) − m_K → ∞` with `A_i` before the round | under opening timing the current subsidy is bid capital | `A_i(K) − w_K → ∞` with `A_i` through `K` inclusive (Lean `record_succ_lt_of_rejected_opening`, the claim cancelling at a wealth-constrained win); the fourth pass's interim factor 2 was removed by the closing pass |
| attention bound over allowance before the round | the opening subsidy is capital available for the test | bound over the subsidy through `K` inclusive (Lean `chargedRecord_ge_neg_allowance`, `test_timing.Bounds`) |


## Final correctness pass (third dispatch) — what changed

| pressure-pass claim | finding | repair |
|---|---|---|
| condition (R): `ℓ ≥ −C` at infinitely many rejection rounds | asserts `B_h` infinite, which coverage then contradicts: vacuous | (BR) `inf_K ℓ^h_K > −∞`; hierarchy sound ⇒ finite wrong tests ⇒ finite tested overpromise ⇒ (BR) (LEAN `record_ge_neg_overpromise`); fixture `test_final.A` |
| "a BRIA cannot remain at `base` on a set of positive density" | false on the revocable variant: coverage needs infinitely many tests of any density | the sparse-test agent is a BRIA and asymptotically myopic (`test_final.B`, proof in `FIXED_HORIZON.md` §4A); the exact original fixture is *sticky* and there every BRIA is competent; the auction keeps the benefit on both (`test_final.C`) |
| "only `s(k)` hypotheses need to be simulated" | an activated hypothesis outside the current support still bids with its wealth | bidders = frontier `s*(k) = max_{j≤k} s(j)`, allowance on `s(k)`; runtime `O(s*(k) g(k) + m_k·exec)`; `Enumerated` in `src/bria.py`; `test_final.D` |
| "an irreversible amendment has no finite catch-up cost" | the sticky amendment is irreversible and joinable at cost `d` | bounded catch-up / joinability versus **foreclosure** (`test_final.E`, `F`); prose repaired in every document and in item 86 |


## Pressure pass (second dispatch) — what changed

`PRESSURE_PASS.md` is the register.  In one table:

| first-pass claim | finding | repair |
|---|---|---|
| a computable weighted BRIA exists iff `m_K/S_K → 0`, via a computable majorant `ρ̄` of the convergence | the majorant is a modulus a computable convergent sequence need not have | the prefix constructor `s(k) = ⌊√(S_k/M_k)⌋`, `a_k = ΔM_k + 1/k`, reading only `(S_k, M_k)`; bound `𝒜_K ≤ 2√(S_K M_K) + √S_K(1+ln K)` from `Σ ΔM/√M ≤ 2√M` (LEAN); the iff holds with a uniform online witness and no effectivity assumption |
| necessity via `D = {K : m_K ≥ (c/2) S_K}`, `c` the limsup | `c` is not computable; `D` was called computable | a rational `q` below the limsup; `D_q` decidable; the adversarial hypotheses e.c. whenever the schedule is; existential in `q`, uniform given `q`, criterion-level |
| "the learner cannot underperform any hypothesis whose promises are sound" | true of promises, read as true of the controller's value | three theorems: promise competence (Theorem 1, condition (BR) after the final pass), actual-history (add `SLACK ≤ o(T)`), own-trajectory (add `SHIFT ≤ o(T)`); fixture D shows value 1 / promise 0 gives nothing |
| `G_k(π\|H^α)` "realized when tested, undefined otherwise", then summed over every block | observed and external returns conflated | `G^obs` (the only feedback) versus the external evaluator `Ĝ`; the identity retyped (LEAN `regret_decomposition`, `regret_le_of_bounds`); fixture H |
| an estimate that is not a lower bound "buys nothing" | false; the source construction runs on hypotheses being wrong | generic claim; soundness variants are theorem hypotheses; the hypothesis consumed is (BR); hierarchy with the sublinear-overpromise negative (fixture G) |
| the whole-block lease is "the weakest useful lease" | overstated; what necessity shows is that an outcome of one continuation is no test of a claim about another | test validity as realized execution of the named continuation (fixtures I, J); the closing pass then demoted the interim `(q, τ)` component to an explanatory factorization |
| "every one-step BRIA invests infinitely often" | unquantified; a BRIA that leaves `base` for good need not | replaced by "a BRIA cannot remain at `base` on a set of positive density", itself withdrawn by the final pass: the criterion forces testing, not adoption |
| discounted returns "reduce" to bounded weight | true for finite truncated leases only | infinite-horizon discounted claims need a settlement mechanism: OPEN (fixtures K, L) |
| "easy policy, hard value" | no resource separation was proved | reduced to the type distinction; the recognizability limit is the paper's Theorem 2 diagonal |
| item 86 asked how a promise is produced "from the constitution's own certificates" | legitimacy does not certify task value | item 86: recoverability (catch-up cost) + performance recognizability + composition |

Fixtures added: `test_pressure.py` A–N (16).  Lean added: `regret_le_of_bounds`, the
typed `learnErr`/`slack`/`shift`, `jump_div_sqrt_le`, `sum_jump_div_sqrt_le`,
`sum_support_jump_le`; the final pass adds `record_ge_neg_overpromise` and
`test_final.py` (9).  All 20 declarations audit clean.


## The two questions of §21

**What does bounded inductive rationality require of the claim "from the state you are
in, give me the advisor-side continuation for long enough, under the constitution, and I
deliver at least `L`"?**  Exactly what it requires of a one-step claim, retyped: the claim
is a continuation hypothesis `(c, L)` at the block contract — a causal advisor
continuation for the system-scheduled block and an accountable claim that may be wrong;
if it keeps outpromising the learner's estimate it must be tested, and a test is the
execution of `c` through the gate with the exterior live; on its
tests it is scored by the realized gated block average against `L`; it may be ignored
only once its `m`-weighted record on those tests has diverged.  The learner's own
estimates must not, in `m`-weighted primitive-time average, exceed what it obtains.  A
learner meeting this has learning error `Σ m_k (L_k − G^obs_k) ≤ o(T)` against every such
claim whose tested record is bounded below (`GROWING_HORIZON.md` §1, (BR)) — competence
against *claims*, not against the controller's value.  A computable such learner exists
for every declared schedule in which no block is a fixed fraction of all time so far,
uniformly and online from the schedule's prefix, and for no other
(`WEIGHTED_BRIA.md` §4).

**Under what additional assumptions does that imply "nearly as well as the best legitimate
continuation policy on its own trajectory"?**  Two: the policy has an efficiently
computable contextual claim with vanishing slack, `SLACK_T(π) ≤ o(T)`, and its history
shift `SHIFT_T(π) = Σ_k m_k (Ĝ_k(π; H^π) − Ĝ_k(π; H^α)) ≤ o(T)` — supplied by uniform block
recovery (reset, mixing, bounded memory, bounded catch-up of a joinable amendment) with
average block length growing, and not by anything the learning theory controls.  Fixture
D shows the first cannot be dropped, the foreclosing branch the second
(`POLICY_REGRET_FRONTIER.md`).  The two questions are kept apart throughout.

## What ports from the paper unchanged

The fixed-horizon case is the paper's setting (`FIXED_HORIZON.md` §2): finite menus of
`m`-step contingent controllers, one block average as the reward, `DP'_{k+1}` depending on
earlier controllers as §2 of the paper already allows.  Definitions 1–7, Lemma 6, Theorems
1–3 apply verbatim.  Fixed-Horizon Continuation Competence is Theorem 3 on the macro
process plus the equal-block average identity (LEAN `blockAverage_eq`).  Endogenous
admissibility is not what the criterion lacked; credit for a reward after its cause's
round is.

## What is genuinely new

1. **The weighted criterion and its construction** (`WEIGHTED_BRIA.md`).  Variable
   horizons separate macro-round and primitive-time averages; bounded horizons rescale
   back to the paper, unbounded ones do not.  The auction in total-reward units with
   wealth-bounded per-unit bids satisfies the wealth identity (LEAN `wealth_sum_eq`),
   weighted no overestimation from `𝒜_K/S_K → 0` (LEAN `overestimation_le_allowance`),
   and coverage from the **capital-adequacy** condition `A_i(K) − m_K → ∞` under
   opening-subsidy timing (LEAN `record_succ_lt_of_rejected_opening`,
   `wealth_ge_of_no_win`), which replaces `Σ_n A(n,i) = ∞`.  The weighted auction is the
   paper's with the round's subsidy credited at its opening — a modification, not the
   paper's construction.
2. **Existence theorem, sharp, with the quantifiers of the pressure pass.**  Allowances
   with capital adequacy and negligible subsidy exist iff `m_K / S_K → 0`
   (**non-dominance**); the prefix rule `s(k) = ⌊√(S_k/M_k)⌋`,
   `A(k,i) = (M_k − M_{k−1}) + 1/k`, credited at the opening of the block just
   revealed, is a uniform online witness needing no effectivity assumption, and no
   prefix-online rule works under the paper's settlement timing; `m_k = ⌊log₂k⌋+1` with `A = i^{-2}⌊√k⌋^{-1}` is an explicit schedule; the
   obstruction is a liar that promises only on the blocks above a rational threshold
   (LEAN `dominant_block_lower_bound`), criterion-level.
3. **The attention bound** `Σ_{wins} m_k (b_k − G_k) ≤ A_i(K)`: wealth is a claim on
   execution time.  Its two faces: without it (unweighted charge on variable blocks) a
   refuted hypothesis of a legitimate macro-BRIA can hold most of primitive time
   (fixture I); with it the one-step auction is provably myopic on a renewable
   investment (fixture A).
4. **Realized execution as the test** of a temporally extended claim: an outcome of one
   continuation is no test of a claim about another (fixtures D/I/J), the gate composed
   by transparency (LEAN `trajGated_eq_traj_of_admitted`), and the biased-testing
   argument in dynamic form (G/H).
5. **The frontier.**  Continuation competence does not imply policy regret (fixture L);
   the exact decomposition `Regret = SHIFT + SLACK + LEARN` with observed and external
   returns separately typed (LEAN `regret_decomposition`, `regret_le_of_bounds`); the
   three-bridge theorem; `SHIFT ≤ o(T)` one-sided as the consumer condition, uniform
   block recovery and the catch-up cost as checkable schemas.

## Strongest theorem

Continuation-promise competence with the Existence Theorem: for any non-dominant
schedule there is a learner, computable uniformly and online from the schedule's prefix,
whose learning error `Σ_k m_k (e_{h,k} − G^obs_k)` is `o(T)` against every e.c.
continuation hypothesis whose tested record is bounded below; with vanishing promise
slack this is competence against the controller's actual-history value, and every fixed
finite investment delay, persistent or renewable, is learned (Corollary B).

## Strongest impossibility

Three.  Under a dominant schedule no weighted BRIA covering the e.c. class exists.  In
the foreclosing-branch environment no learner has sublinear regret against the
unrestricted legitimate policy class while continuation competence holds exactly.  And
the one-step criterion permits an asymptotically myopic BRIA on the revocable amendment.

## Corrections to the dispatch's premises

- "Ordinary one-step gated BRIA can rationally remain myopic": on the exact existing
  fixture, which keeps `expanded` under `work`, no — every BRIA is competent there,
  because one forced test is absorbing; on the revocable variant, yes — the sparse-test
  agent is a BRIA and asymptotically myopic.  The *construction* keeps the benefit on
  both.  The learner that lost `2H−3` is not a BRIA (it never tests a hypothesis that
  outpromises it forever).  Item 86's premise that
  "the myopic gated learner is itself legitimate and loses linearly" stands as a fact
  about that learner, not about bounded inductive rationality.
- The candidate condition `A_i(K)/m_K → ∞` is stronger than needed; the proof uses the
  difference.
- The paper's own allowance fails capital adequacy for every unbounded schedule, even
  logarithmic.
- "Combinatorial auctions solve cross-decision optimization" is a footnote; not used.
- Theorem 4 does not port to weights without a weighted randomness notion; left open.

## Downstream implication for item 86

Refined in place twice.  The item's fixture is answered by the paper's own construction
(the witness at `m = 2` and at every growing schedule); the item's "bounded task regret
against `Π_leg`" is false for the unrestricted class by fixture L and is replaced by:
learning error controlled against accountable continuation claims (this round, done,
unregistered), plus a recoverability certificate for legitimate slow-lane continuations
(catch-up cost), plus a performance-recognizability interface for the values one wants to
compete on — which is not legitimacy's duty — plus their composition.
`CORRIGIBILITY_COMPOSITION.md` §6.

## Dependencies

Takes as hypotheses `2026-09-06-decision-theory-bill` (the fixture, the gate, the
open problem) and, for the value interface only, `2026-09-08-legitimate-deference-consolidation`.
The BRIA paper for its definitions and Theorems 1–4, cited and audited
(`BRIA_SOURCE_AUDIT.md`), not re-proved.  The phi-regret-bridge and local-regret rounds
for the replay-versus-local divergence that the history-shift term specialises.

## Deviations and prompt corrections

- The dispatch's fixture family was extended by an investment length `d` and an expiry
  `e`, because on the exact existing fixture (`d = 1`, persistent) the myopic failure it
  asks for does not occur for a BRIA.  The existing fixture is the `d = 1` case and is run.
- The Lean scope is the algebraic cores listed in the module header; no MDP library, no
  criterion, no policy regret.  The asymptotic conditions (i″), (ii) and the schedule's
  asymptotics are proved in prose and checked at finite points.
- The sparse-test agent that shows the criterion permits myopia is implemented
  (`test_final.B`); its BRIA-ness against the full e.c. class is a prose theorem from the
  paper's Theorem 1, not mechanically checked.
- Section 14 ends open on certifying `B_T(π)` from inside, as the dispatch allows.
- The first four passes made no wiki edit.  The closing pass promoted the result to
  `wiki/Continuation-BRIA.md` and, on the maintainer's two mid-turn additions, removed
  the "paused" status of the deference line from every page that carried it and wrote
  `wiki/Theorem-Spine.md`, a theorem-level statement of the program's mature results
  across the legitimacy spine, Progress, the conditional Normative Inductor, the
  fixed-era layer, legitimate deference, corrigibility and continuation BRIA, each
  labelled by strength (registered / LEAN / FIX / paper-derived / PAPER / conditional /
  EXT / OPEN).  `Deference.md` now records the withdrawal of the one-sided completion
  interval, which the wiki had not stated before.  Nothing is registered.

## What this does not establish

- Any rate; every guarantee is a limit.
- A weighted Theorem 4; the sharpness of capital adequacy per hypothesis.
- Any own-trajectory statement without the recoverability condition; any certificate of
  that condition from realized data.
- Adaptive or hypothesis-requested lease lengths; the schedule is declared.
- That a legitimate policy in `Π_leg` has an e.c. sound promise; the comparator class is
  hypotheses, argued to be the right class and not proved to exhaust `Π_leg`.
- Anything about the value interface beyond typing `G_k` as a generic bounded realized
  return.

## Outstanding maintainer actions

1. Whether `Auction.wealth_sum_eq` / `overestimation_le_allowance` /
   `sum_support_jump_le` / the Existence Theorem should be registered as statements of
   record; no filed item is answered at the strength registration needs, so nothing is
   registered here.
2. Item 86 is refined, not closed; the refined text names the three remaining objects.

## New names introduced (provisional)

block contract; continuation; continuation hypothesis `(continuation, claim)`;
accountable contextual claim; realized test; transparent gate; weighted BRIA; opening
subsidy / opening capital; capital adequacy `A_i(K) − m_K → ∞`;
non-dominance `m_K/S_K → 0`; prefix constructor; attention bound; continuation-promise /
actual-history / own-trajectory competence; tested overpromise; condition (BR);
horizon-stable promise; `m`-detectable advantage; history-shift discrepancy `SHIFT_T(π)`;
three-bridge theorem; uniform block recovery; bounded catch-up (joinability);
foreclosure; `Π_rec,prom`; sticky / revocable amendment.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-08-continuation-bria/PROMPT.md`.
- Executor: Claude Fable 5.1 (Anthropic).
- Dates: 2026-09-08 (first pass, pressure pass, final correctness pass, allowance-timing
  audit and closing pass: five dispatches).
