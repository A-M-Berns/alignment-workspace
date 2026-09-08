# Report

Verdict: **GROWING-HORIZON-CONTINUATION-BRIA-SURVIVES-UNDER-NON-DOMINANCE-POLICY-REGRET-NEEDS-RECOVERABILITY.**

Outcome A of the dispatch's decision tree, with the weighted construction's existence
condition carried in the verdict because it is sharp; outcome D's content is the last
clause.

## The two questions of §21

**What does bounded inductive rationality require of the claim "from the state you are
in, give me the advisor-side continuation for long enough, under the constitution, and I
deliver at least `L`"?**  Exactly what it requires of a one-step claim, retyped: the claim
is a continuation hypothesis `(q, L)` at the actual history; if it keeps outpromising
the learner's estimate it must be tested, and a test is an execution lease — the
learner's selection committed to `q` for the block, every step through the gate, the
exterior live; on its tests it is scored by the realized gated block average against
`L`; it may be ignored only once its `m`-weighted record on those tests has diverged.
The learner's own estimates must not, in `m`-weighted primitive-time average, exceed
what it obtains.  A learner meeting this cannot asymptotically underperform any such
claim that is sound on the leases it is granted (`GROWING_HORIZON.md` §1).  A computable
such learner exists for every declared schedule in which no block is a fixed fraction of
all time so far, and for no other (`WEIGHTED_BRIA.md` §4).

**Under what additional assumptions does that imply "nearly as well as the best legitimate
continuation policy on its own trajectory"?**  Two: the policy has an efficiently
computable contextual promise with vanishing slack, and the history-shift discrepancy
`Δ_T(π) = Σ_k m_k (G_k(π|H^π) − G_k(π|H^α))` is `o(T)` — supplied by uniform block
recovery (reset, mixing, bounded memory, reversible amendments) with average block length
growing, and not by anything the learning theory controls.  The irreversible-branch
fixture shows the second cannot be dropped (`POLICY_REGRET_FRONTIER.md`).  The two
questions are kept apart throughout.

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
   and coverage from the **capital-adequacy** condition `A_i(K) − m_K → ∞` (LEAN
   `record_lt_of_rejected'`, `wealth_ge_of_no_win`), which replaces `Σ_n A(n,i) = ∞`.
2. **Existence theorem, sharp.**  A computable weighted BRIA covering the e.c. class
   exists for a schedule iff `m_K / S_K → 0` (**non-dominance**); the replenishing
   allowance `a_k = (M_k − M_{k−1}) + 1/k` with a slowly growing support is the witness,
   `m_k = ⌊log₂k⌋+1` with `A = i^{-2}⌊√k⌋^{-1}` the exact schedule; the obstruction is a
   liar that promises only on dominant blocks (LEAN `dominant_block_lower_bound`).
3. **The attention bound** `Σ_{wins} m_k (b_k − G_k) ≤ A_i(K)`: wealth is a claim on
   execution time.  Its two faces: without it (unweighted charge on variable blocks) a
   refuted hypothesis of a legitimate macro-BRIA can hold most of primitive time
   (fixture I); with it the one-step auction is provably myopic on a renewable
   investment (fixture A).
4. **The lease** as the weakest test semantics for a temporally extended promise, with
   necessity by fixture D and the gate composed by transparency (LEAN
   `trajGated_eq_traj_of_admitted`), plus the biased-testing argument in dynamic form
   (G/H).
5. **The frontier.**  Continuation competence does not imply policy regret (fixture L);
   the exact decomposition `regret = history-shift + slack + learning` (LEAN
   `regret_decomposition`); uniform block recovery as the single consumer condition.

## Strongest theorem

Growing-Horizon Continuation Competence with the Existence Theorem: for any non-dominant
schedule there is a computable learner that cannot asymptotically underperform, in
`m`-weighted primitive-time average, any e.c. continuation hypothesis whose contextual
promises are sound on the constitutional leases it is granted from the learner's actual
histories; hence every fixed finite investment delay, persistent or renewable, is learned
(Corollary B).

## Strongest impossibility

Two.  Under a dominant schedule no weighted BRIA covering the e.c. class exists.  And in
the irreversible-branch environment no learner has sublinear regret against the
unrestricted legitimate policy class while continuation competence holds exactly.

## Corrections to the dispatch's premises

- "Ordinary one-step gated BRIA can rationally remain myopic" on the exact existing
  fixture: the *criterion* permits it; the *construction* does not do it, and every BRIA
  is forced to try the investment infinitely often.  The learner that lost `2H−3` is not a
  BRIA (it never tests a hypothesis that outpromises it forever).  Item 86's premise that
  "the myopic gated learner is itself legitimate and loses linearly" stands as a fact
  about that learner, not about bounded inductive rationality.
- The candidate condition `A_i(K)/m_K → ∞` is stronger than needed; the proof uses the
  difference.
- The paper's own allowance fails capital adequacy for every unbounded schedule, even
  logarithmic.
- "Combinatorial auctions solve cross-decision optimization" is a footnote; not used.
- Theorem 4 does not port to weights without a weighted randomness notion; left open.

## Downstream implication for item 86

Refined in place.  The item's fixture is answered by the paper's own construction (the
witness at `m = 2` and at every growing schedule); the item's "bounded task regret against
`Π_leg`" is false for the unrestricted class by fixture L and is replaced by: competence
against e.c. continuation hypotheses (this round, done, unregistered), plus a
recoverability certificate for the slow lane and a promise class for `Π_leg`, which is
what remains open.  `CORRIGIBILITY_COMPOSITION.md` §5.

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
  criterion, no policy regret.  The asymptotic conditions (i′), (ii) and the schedule's
  asymptotics are proved in prose and checked at finite points.
- The sparse-excursion BRIA that shows the criterion permits myopia is stated, not
  implemented.
- Section 14 ends open on certifying `B_T(π)` from inside, as the dispatch allows.
- No wiki edit: nothing registered, no theorem-level correction to a canonical page;
  `Corrigibility`'s dynamic-admissibility paragraph is refined through item 86 only.

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

1. Whether `Auction.wealth_sum_eq` / `overestimation_le_allowance` / the Existence Theorem
   should be registered as statements of record; no filed item is answered at the
   strength registration needs, so nothing is registered here.
2. Item 86 is refined, not closed; the refined text names the two remaining objects.

## New names introduced (provisional)

continuation hypothesis; execution lease; transparent gate; weighted BRIA; capital
adequacy `A_i(K) − m_K → ∞`; non-dominance `m_K/S_K → 0`; attention bound;
horizon-stable promise; `m`-detectable advantage; history-shift discrepancy `Δ_T(π)`;
uniform block recovery.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-08-continuation-bria/PROMPT.md`.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-08.
