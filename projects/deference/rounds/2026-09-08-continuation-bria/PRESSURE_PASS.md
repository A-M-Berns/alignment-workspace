# Pressure pass (2026-09-08, second dispatch on PR #95), final correctness pass (third) and allowance-timing audit (fourth)

Verdicts in order: `CONTINUATION-BRIA-READY-NONDOMINANCE-IFF-REPAIRED` (second),
`CONTINUATION-BRIA-READY-AFTER-FINAL-CORRECTNESS-PASS` (third), and, after the timing
audit of §13, **CONTINUATION-BRIA-READY-TIMING-ALIGNED.**  Every document marked
*[repaired by the pressure pass]*, *[final correctness pass]* or *[timing aligned in the
fourth pass]* carries its corrections in place; `test_pressure.py` (16 fixtures),
`test_final.py` (9) and `test_timing.py` (5) are the evidence added.  Sections 1–12 are
the earlier registers, corrected in place where a later pass found them wrong.

## 1. Strongest true existence theorem

For a schedule `(m_k)` revealed block by block, `S_K = Σ_{k≤K} m_k`, `M_K = max_{k≤K} m_k`,
the following are equivalent: `m_K/S_K → 0`; opening subsidies with capital adequacy
`A_i(K) − m_K → ∞` (every `i`, `A_i` through `K` inclusive) and negligible subsidy
`𝒜_K/S_K → 0` exist; the prefix rule `s(k) = ⌊√(S_k/M_k)⌋`, `A(k,i) = (M_k − M_{k−1}) + 1/k`
on `i ≤ s(k)`, credited at
the opening of block `k`, makes the weighted auction a weighted BRIA covering every c.e.
class of e.c. continuation hypotheses.  *[Timing from §13; coefficient sharpened in §14.]*  If
`limsup m_K/S_K > 0`, some rational `q` has `{K : m_K ≥ q S_K}` infinite and the two e.c.
hypotheses `(good, γ)`, `(liar, 1 on that set)` in the constant-reward environment defeat
every estimating agent.  (`WEIGHTED_BRIA.md` §4.1; LEAN `sum_support_jump_le`,
`sum_jump_div_sqrt_le`, `jump_div_sqrt_le`, `dominant_block_lower_bound`; FIX
`test_pressure.A`, `B`, `test_weighted.Dominance`, `J`, `K`.)

## 2. Exact effectivity assumptions

Sufficiency: **none beyond mathematical non-dominance**, given opening timing.  The rule
reads only the prefix `(S_k, M_k)` once `m_k` is revealed; the bound
`𝒜_K ≤ 2√(S_K M_K) + √S_K (1 + ln K)` is proved from `Σ_k (M_k − M_{k−1})/√M_k ≤ 2√M_K`; no
modulus, majorant, code for the schedule, or information about `m_{k+1}, …` is used.
Under the source paper's settlement timing no prefix-online rule works (§13).  The first pass's `ρ̄`-majorant argument is withdrawn.  The learner is computable
uniformly in the schedule when the schedule is computable, and runs relative to an
online presentation otherwise.  Necessity: existential in the rational threshold `q`
(the limsup is not computable from a code); given `q`, uniform; the adversarial
hypotheses are e.c. whenever the schedule is; criterion-level, for any class containing
those two hypotheses.  Layers I (criterion impossibility), II (auction sufficiency under
(i″)+(ii)) and III (allowance existence iff non-dominance, with the uniform witness) are
stated separately and the "iff" is their conjunction with the quantifiers above; III′
is the settlement-timing negative.

## 3. Strongest continuation-BRIA theorem

**Theorem 1 (continuation-promise competence).**  For a covered hypothesis `h` with
the record bounded below, (BR) `inf_K ℓ^h_K > −∞`,
`LEARN_T(h) = Σ_k m_k (e_{h,k} − G^obs_k(α)) ≤ o(T)`.  **Theorem 2
(actual-history).**  Add `SLACK_T(h) ≤ o(T)`: `Σ_k m_k (Ĝ_k(q; H^α) − G^obs_k(α)) ≤ o(T)`.
**Theorem 3 (own-trajectory).**  Add `SHIFT_T ≤ o(T)`.  (`GROWING_HORIZON.md` §1–2.)  The
first pass's conclusion "cannot underperform a hypothesis whose promises are sound" is
Theorem 1 and is a statement about *promises*; every reading of it as a statement about a
controller's value is withdrawn (FIX `D_PromiseVersusValue`: value 1, promise 0, no
competence against 1).

## 4. Exact promise condition consumed

(BR): the weighted record `ℓ^h_K = Σ_{tests ≤ K} m_k (G^obs_k − e_{h,k})` on the learner's
test set is bounded below, `inf_K ℓ^h_K > −∞`.  *[The pressure pass wrote "≥ −C at
infinitely many rejection rounds", which asserts infinitely many rejections and is
contradicted by coverage: vacuous; withdrawn in §12.]*  Sufficient for (BR): finite
total tested overpromise `Σ_{tests} m_k (e − G^obs)_+ < ∞` (LEAN
`record_ge_neg_overpromise`); wrong on finitely many tests with bounded total (FIX `F`);
sound on every test.  **Not sufficient:** sublinear but divergent tested overpromise
(FIX `G`): the criterion lets a BRIA reject such a hypothesis forever while testing it on
a density-zero set.  A generic continuation hypothesis is `(continuation, claim)` and the
claim is not by definition a lower bound (`CONTINUATION_HYPOTHESES.md` §1).

## 5. Exact external policy-regret decomposition

With `G^obs` the learner's observed return (the only feedback) and `Ĝ` an external
rollout evaluator (unobserved except on tested blocks; FIX `H_CounterfactualTyping`), at
block boundaries

```
Regret_T(α, π) = SHIFT_T(π) + SLACK_T(π) + LEARN_T(π),
SHIFT = Σ m_k (Ĝ(π; H^π) − Ĝ(π; H^α)),  SLACK = Σ m_k (Ĝ(π; H^α) − L),  LEARN = Σ m_k (L − G^obs(α)),
```
plus a boundary term below `M_{K+1}` off boundaries.  LEAN `regret_decomposition`,
`regret_le_of_bounds`.  **Continuation-BRIA never consumes counterfactual rewards; the
policy-regret theorem does.**

## 6. Weakest policy-regret consumer assumptions

`LEARN ≤ o(T)` (Theorem 1, needs (BR)); `SLACK ≤ o(T)` (promise recognizability;
one-sided, overpromising on untested blocks only helps); `SHIFT ≤ o(T)` (recoverability;
one-sided, along the learner's actual block starts, per policy).  Uniform block recovery
`m (Ĝ_m(π; H^π) − Ĝ_m(π; H)) ≤ φ(m)`, `φ(m)/m → 0`, is one checkable sufficient schema;
its corrigibility instance is **bounded catch-up (joinability)** of an authorized
amendment (per-block shift exactly `d`, FIX `M_RecoverableAmendment`,
`test_final.E`), which does not need reversibility; the excluded case is **foreclosure**
(`test_final.F`), not irreversibility.  The regret class is
`Π_rec,prom = {legitimate π : covered h_π with (BR), SLACK ≤ o(T), SHIFT ≤ o(T)}`.

## 7. What the constitution supplies

`Exec^G` (safe primitive execution: only admitted proposals run, refusals become `⊥`) and
the comparator class of gate-transparent continuations; through joinability of the slow
lane's transitions from a lagging history, the catch-up cost that bounds `SHIFT` for
policies differing by an authorized amendment.

## 8. What it does not supply

Task-value or future-principal-value claims about any controller (`SLACK` is a
performance-recognizability interface, not a legitimacy certificate); recoverability
across foreclosing choices (those policies fall outside `Π_rec,prom`); any certificate
of `SHIFT` from realized data; a settlement mechanism for infinite-horizon discounted
claims (OPEN, FIX `L_InfiniteDiscountedClaim`).

## 9. Remaining open problem

Item 86 as refined: the recoverability certificate for legitimate slow-lane
continuations (catch-up cost as the theorem shape), the promise-recognizability
interface for the values one wants to compete on, and their composition on the round's
two-state process.  Side questions: a weighted Theorem 4; the construction's tolerance
of slowly diverging records (not a criterion property); hypothesis-requested lease
lengths.

## 10. Other repairs in this pass

- Criterion, construction and fixture separated on the one-step amendment; "every BRIA
  invests infinitely often" replaced by "a BRIA cannot remain at `base` on a set of
  positive density" (`FIXED_HORIZON.md` §4A; FIX `C_CriterionVersusConstruction`).
  *[Withdrawn in §12: that replacement was also wrong on the revocable variant.]*
- Test validity restated: data is evidence about a continuation claim only when
  generated by executing that continuation (FIX `I`, `J`); continuations are
  advisor-side only, so no "absent intervention" counterfactual enters a score.  *[The
  pressure pass phrased this with a "treatment" component `τ`; the closing pass demoted
  `τ` to an explanatory factorization, `CONTINUATION_HYPOTHESES.md` §2.]*
- Discounted returns: finite truncated leases rescale; infinite-horizon claims OPEN
  (FIX `K`, `L`).
- "Easy policy, hard value" reduced to the type distinction; no complexity separation
  claimed (`GROWING_HORIZON.md` §5).
- Item 86 rewritten: recoverability + performance recognizability + composition; no
  duty on legitimacy to certify task value.

## 11. The two sentences

*What continuation-BRIA has solved:* bounded learning against empirically accountable,
temporally extended continuation claims on the histories the learner actually reaches —
for every non-dominant schedule, by a learner computable uniformly and online from the
schedule's prefix.

*What remains before corrigible policy regret:* a policy must additionally have a
computationally accessible near-tight claim (`SLACK ≤ o(T)`), and its own induced history
must be recoverable, in value, from the histories on which the learner can actually test
it (`SHIFT ≤ o(T)`).

## 12. Final correctness pass (third dispatch)

Four residual issues, each repaired exactly.

**(1) Condition (R) was vacuous.**  It asserted `ℓ ≥ −C` at infinitely many rejection
rounds; coverage then forces `ℓ → −∞` along those rounds.  Replaced by **(BR)**
`inf_K ℓ^h_K > −∞`, nonvacuous (a sound hypothesis has `ℓ ≡ 0` and, once followed, no
rejection round at all — FIX `test_final.A`).  Hierarchy: sound ⇒ finitely many wrong
tests with bounded total ⇒ finite total tested overpromise ⇒ (BR) ⇒ Theorem 1 (LEAN
`record_ge_neg_overpromise` for the third arrow); sublinear-but-divergent overpromise
remains insufficient (FIX `test_pressure.G`).  The logically weakest hypothesis — "if
`B_h` is infinite, `ℓ` does not tend to `−∞` along it" — is recorded and not used.

**(2) The one-step criterion permits asymptotic myopia.**  The pressure pass's "a BRIA
cannot remain at `base` on a set of positive density" was wrong: coverage needs only
infinitely many tests with divergent record, of any density.  On the *revocable* variant
(`work` at `expanded` returns to `base`) the agent that runs the published auction on
`base` rounds and forces `work` with estimate 1 at `expanded` is a BRIA — proof from the
paper's Theorem 1 on the `base` subsequence plus the attention bound for the density of
excursions (`FIXED_HORIZON.md` §4A) — and is asymptotically myopic (FIX `test_final.B`:
92 sparse tests, record `−92`, `base` density `0.977`, overestimation `0.023`, average
`0.326`).  On the *exact original* fixture, which keeps `expanded` under `work`, every
BRIA is competent: one forced test is absorbing and the sound `stay` claim then forces
`α^e ≥ 1`.  The construction keeps the benefit on both variants (FIX `test_final.C`).
So: the one-step criterion is already too weak for dynamic competence; the multi-step and
renewable fixtures show the *construction's* credit-assignment failure more robustly;
and a sound macro claim about the whole investment is what forces investment at the
criterion level.  Every "genuine failure needs a multi-step or renewable investment"
sentence is repaired to this.

**(3) Bidders are the frontier, not the current support.**  Allowance goes to
`i ≤ s(k)`; the auction simulates every activated hypothesis `i ≤ s*(k) := max_{j≤k} s(j)`,
finite, nondecreasing and prefix-computable; an activated hypothesis outside the current
support keeps its wealth and bids.  Subsidy still counts `s(k)` only; capital adequacy
uses only that allowance arrives at all large `k` and wealth never falls between wins;
runtime `O(s*(k) g(k) + m_k · exec)`.  `src/bria.py` gains `Enumerated` (lazy activation)
and FIX `test_final.D` exhibits a spike that drops `s` from 3 to 1 while hypothesis 3
still bids and wins.  The existence theorem is otherwise unchanged (§6 checks in
`WEIGHTED_BRIA.md` §4.1).

**(4) Joinability, not reversibility.**  The sticky amendment `base → expanded` is
irreversible and joinable at cost `d` (FIX `test_final.E`, per-block shift exactly `d`);
the branch is foreclosing (FIX `test_final.F`, shift `(2/3)m`).  The theorem-facing
concept is **bounded catch-up**: from every learner-reached block start some legitimate
continuation reaches, within `d` steps, a state value-equivalent for `π` to `π`'s own.
"An irreversible amendment has no finite catch-up cost" is withdrawn everywhere.

**The eight answers.**

1. *What the BRIA criterion forces about long-term plans:* only that a claim which keeps
   outpromising the learner's estimate is tested infinitely often, on a set of any
   density, with its tested record diverging; nothing about adoption.  A one-step claim
   about the first step of an investment is refuted by every test, so the one-step
   criterion permits asymptotic myopia wherever the investment can be revoked; a sound
   claim about the whole investment (a macro claim) forces its adoption on all but a
   density-zero set of block starts.
2. *What comes only from the wealth auction:* keeping the persistent benefit on the
   one-step fixture (a sound `stay` claim accumulates wealth), and the failure on
   multi-step and renewable investments (one-step tests drain a continuation claim's
   capital; the attention bound caps investing actions at `3𝒜_K + O(1)`).
3. *The hypothesis replacing (R):* (BR) `inf_K ℓ^h_K > −∞` on the learner's test set.
4. *Schedules with a computable weighted learner, corrected semantics:* exactly the
   non-dominant ones, `m_K/S_K → 0`, by the prefix constructor with bidders the frontier
   `s*(k)` and allowance on `s(k)`; under dominance no estimating agent covers the
   two e.c. hypotheses of the rational-threshold obstruction.
5. *What continuation-BRIA controls:* `LEARN_T(h) = Σ m_k (e_{h,k} − G^obs_k) ≤ o(T)` for
   every covered claim with (BR) — learning error against claims, from realized data.
6. *What promise recognizability adds:* `SLACK ≤ o(T)`, so the claims are close enough to
   the controller's actual-history value that Theorem 1 becomes competence against that
   value.
7. *What history recoverability adds:* `SHIFT ≤ o(T)`, so the actual-history value is
   close enough to the policy's own-trajectory value that the comparison is with the
   policy itself.
8. *Catch-up versus foreclosure:* "not amended yet but can still catch up" means some
   legitimate continuation from the learner's history reaches, at bounded cost, a state
   value-equivalent for `π` to `π`'s own — joinability, which an irreversible transition
   can have; "chose a branch that foreclosed the comparator's" means no legitimate
   continuation reaches or matches that state at any cost, so the per-block shift is a
   fixed fraction.

## 13. Allowance-timing audit (fourth dispatch)

1. **Source paper's timing.**  Theorem 1: the bid at `t` is `min(h^e_{i,t}, w_t(i))` with
   `w_t` the wealth carried in; `w_{t+1}(i) = w_t(i) + A(t,i) [+ r_t − e*_t]`.  The
   allowance of round `t` is credited *after* round `t`, and `A` is a fixed function of
   `(t, i)`.
2. **Old Lean timing.**  The same: `Feasible` bounds `w_k b_k` by `W k`, and `A k` enters
   `W (k+1)`.  Source-faithful; it was not the construction Python ran.
3. **Old Python timing.**  `h.wealth += A(k,i)` before bids: the round's allowance funds
   the round's bid.  Opening (prefunded) timing.
4. **Why it matters.**  The prefix rule's `ΔM_k = M_k − M_{k−1}` term is the capital meant
   for a block just revealed as a new maximum.  Under settlement timing it arrives one
   block late.  On a non-dominant schedule whose spikes dwarf every earlier maximum, a
   hypothesis that promises only at spikes carries at most the previous maximum plus a
   harmonic sum into each spike, bids a vanishing fraction of the block, loses to any
   competitor with a positive floor, and is never tested while outpromising infinitely
   often: coverage fails.  FIX `test_timing.SurpriseSpike`: on the fixture-A schedule the
   spike liar bids at most `0.30` at every spike under settlement timing and wins none;
   under opening timing it is tested at spike 256 and rejected at 1024 with the sharp
   record bound holding there.  The general impossibility, for every prefix-online rule with negligible
   subsidy under settlement timing, is `WEIGHTED_BRIA.md` §4.1 III′ (an adversarial
   schedule built stage by stage against the rule).
5. **Chosen weighted timing: opening subsidy.**  `m_k` is revealed; hypotheses are
   activated; `A(k,i)` is credited to `i ≤ s(k)`; hypotheses emit claims; bids are
   bounded by the opening capital; winner; execution; observation; settlement.  Nothing
   about `m_{k+1}, …` is needed: the headline "uniform online" theorem means exactly
   that the rule reads `(S_k, M_k)` after `m_k` is revealed and before bids.
6. **Exact wealth recursion.**  `W_1 = 0`; `B_k(i) = W_k(i) + A(k,i)`;
   `b_{i,k} = min(e_{i,k}, B_k(i)/w_k)`; `W_{k+1}(i) = B_k(i) + 1[i = i*_k] w_k (G_k − b*_k)`.
   As a sequence of bids it is the paper's auction under `A'(k) = A(k+1)` with initial
   endowment `A(1,i)` (FIX `test_timing.Reindexing`, bid-for-bid equality); the
   modification is that the subsidy funding block `k` may read `m_k`.  In Lean the two
   timings share `Auction.W` and differ in `Feasible` versus `FeasibleOpening`.
7. **Exact capital-adequacy condition.**  `A_i(K) − w_K → ∞` with `A_i(K)` the subsidy
   through `K` inclusive.  Derivation: at a rejection `K`, `B_K(i) < w_K e_{i,K}` and
   `B_K(i) = A_i(K) + chargedRecord_i(K−1)`, so the record over tests before `K` is
   `< w_K e − A_i(K)` (LEAN `record_lt_of_rejected_opening`); if `i` is itself the
   wealth-constrained winner at `K` the inclusive record gains exactly `w_K (G_K − e)`
   and `e` cancels, giving `ℓ_K < w_K G_K − A_i(K) ≤ w_K − A_i(K)`; otherwise
   `ℓ_K = ℓ_{<K} < w_K e − A_i(K) ≤ w_K − A_i(K)` (LEAN `record_succ_lt_of_rejected_opening`).
   *[This pass first bounded the winner's increment by `w_K` and wrote a factor 2; the
   closing pass (§14) removed it.]*
8. **Corrected prefix theorem.**  Rule `A(k,i) = ΔM_k + 1/k` on `i ≤ ⌊√(S_k/M_k)⌋`,
   credited at the opening: `A_i(K) − m_K ≥ −M_{k_i−1} + ln(K/k_i) → ∞`, and
   `𝒜_K ≤ 2√(S_K M_K) + √S_K(1 + ln K) = o(S_K)` (LEAN `sum_support_jump_le` for the
   jump sum).  FIX `test_pressure.A`/`B`, `test_timing.Bounds`.
9. **Non-dominance remains iff.**  Only-if is unchanged (`𝒜_K ≥ A_1(K) ≥ m_K − C`); if
   is the corrected rule.  Layer I (criterion
   impossibility under dominance) is timing-independent.  III′ adds: under settlement
   timing the "if" direction has no prefix-online witness.
10. **Source-fidelity consequences.**  Three registers: the fixed-horizon *criterion*
    reduction is PAPER verbatim; the paper's *construction* has settlement timing with a
    schedule-blind allowance; the *weighted construction* is DERIVED — the paper's
    auction with opening subsidy, a small modification forced by online variable
    liabilities.  For `m ≡ 1` the opening-timed auction is literally the paper's auction
    after reindexing the allowance and adding an initial endowment; it is not "the paper's
    construction verbatim", and the phrase is withdrawn wherever it stood for the Python
    auction.  The attention bound now counts the current round's opening subsidy: no
    experimental capital credited before a test escapes the accounting (LEAN
    `chargedRecord_ge_neg_allowance`).

**The nine answers.**

1. *The paper's auction or a modified one?*  Modified: the paper's auction with the
   round's subsidy credited at the opening of the round it funds, and with the subsidy
   allowed to read the block length just revealed.  Bid-for-bid it is the paper's auction
   under a reindexed allowance with an initial endowment.
2. *When does a hypothesis receive `A(k,i)`?*  At the opening of round `k`, after `m_k` is
   revealed and before bids, if `i ≤ s(k)`.
3. *Does the current `ΔM_k` finance block `k`?*  Yes; that is what opening timing is for.
4. *What wealth forms the bid?*  The opening capital `B_k(i) = W_k(i) + A(k,i)`.
5. *Exact cumulative-capital condition for coverage.*  `A_i(K) − w_K → ∞` for every
   `i`, `A_i` through `K` inclusive.
6. *Does the prefix rule work for every non-dominant schedule?*  Yes, under opening
   timing; no prefix-online rule works under settlement timing.
7. *Is one-step lookahead needed?*  Under settlement timing, yes — the subsidy credited
   after round `k` must read `m_{k+1}`; that is opening timing with a shifted index.
   Under opening timing, no.
8. *Is non-dominance the sharp criterion-level boundary?*  Yes: layer I is timing-
   independent, and layer III's iff holds with the corrected coefficient.
9. *PAPER / DERIVED / LEAN / FIX after this repair.*  PAPER: Definitions 1–7, Lemma 6,
   Theorems 1–4, Appendices C–D, and the fixed-horizon reduction as their instance.
   DERIVED: the weighted criterion, the opening-timed auction and its coverage under
   (i″)+(ii), the existence theorem I/II/III/III′, the sparse-test agent's BRIA-ness,
   Theorems 1–3 of `GROWING_HORIZON.md`, the three-bridge theorem.  LEAN: block
   accounting, the timing-independent wealth identities, both timings' feasibility
   consequences, the rejection and attention bounds, the record lower bound, gate
   transparency, the regret decomposition, the dominance inequality, the jump-sum
   bound.  FIX: 67 exact fixtures across `test_fixed_horizon`, `test_lease`,
   `test_weighted`, `test_frontier`, `test_pressure`, `test_final`, `test_timing`.
   EXT: any claim that a gate or a return corresponds to actual corrigible execution.
   OPEN: weighted Theorem 4, infinite-horizon discounted claims, certifying `SHIFT`
   from realized data, the construction's tolerance of slowly diverging records.

## 14. Closing pass (fifth dispatch)

1. **Sharp opening-timing bound.**  The fourth pass's factor 2 was loose: at a rejection
   `K`, if `i` is the wealth-constrained winner the inclusive record gains exactly
   `w_K (G_K − e_{i,K})` and the claim cancels against `B_K(i) < w_K e_{i,K}`, giving
   `ℓ_K < w_K G_K − A_i(K) ≤ w_K − A_i(K)`; if not, `ℓ_K = ℓ_{<K} < w_K e − A_i(K) ≤ w_K −
   A_i(K)`.  Uniformly `ℓ_K < w_K − A_i(K)` (LEAN `record_succ_lt_of_rejected_opening`,
   reproved by the cancellation; FIX `test_timing.test_sharp_record_bound_at_every_rejection`).
   Capital adequacy is `A_i(K) − w_K → ∞`, the prefix rule is `A(k,i) = ΔM_k + 1/k`, the
   subsidy bound is `2√(S_K M_K) + √S_K (1 + ln K)`.  The no-win accumulation lemma is
   generalised to consume only nonnegativity at `K₀` (`wealth_ge_of_no_win`) and
   instantiated for opening capital (`B_ge_of_no_win_opening`), so the opening-timing
   coverage spine — nonnegativity, no-win accumulation, rejection bound, inclusive
   rejection bound, overestimation, attention — is Lean-backed end to end.
2. **Canonical type compressed** to `h(χ_k) = (c_{h,k}, e_{h,k})` with the system's block
   contract `χ_k = (H_k, m_k, Exec^G, R_k)`; a test is the derived event that the
   selected continuation is executed; `τ` is an explanatory factorization only
   (`CONTINUATION_HYPOTHESES.md`).  The schedule is the system's; bidders do not choose
   `m_k`.
3. **Promoted to the wiki**: `Continuation-BRIA.md`, with the Architecture,
   Corrigibility, Normative-Inductor, Normative-Induction, Deference,
   Logical-Induction-and-Deference, Glossary and Home pages amended.
4. **Fixtures.**  `test_timing.py` retuned to the sharp bound; `test_pressure.I`/`J`
   renamed to continuation language.  68 fixtures.

The nine answers of §13 stand with "coefficient 2" read as "coefficient 1" and
`A_i(K) − 2w_K` as `A_i(K) − w_K`.
