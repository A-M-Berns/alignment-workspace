# Pressure pass (2026-09-08, second dispatch on PR #95)

Verdict after pressure: **CONTINUATION-BRIA-READY-NONDOMINANCE-IFF-REPAIRED.**  Supersedes
the first pass's verdict string.  Every document marked *[repaired by the pressure pass]*
carries its corrections in place; `test_pressure.py` (16 fixtures) is the evidence added.

## 1. Strongest true existence theorem

For a declared schedule `(m_k)`, `S_K = Σ_{k≤K} m_k`, `M_K = max_{k≤K} m_k`, the following
are equivalent: `m_K/S_K → 0`; allowances with capital adequacy `A_i(K) − m_K → ∞` (every
`i`) and negligible subsidy `𝒜_K/S_K → 0` exist; the prefix constructor
`s(k) = ⌊√(S_k/M_k)⌋`, `a_k = (M_k − M_{k−1}) + 1/k` on `i ≤ s(k)` makes the weighted
auction a weighted BRIA covering every c.e. class of e.c. continuation hypotheses.  If
`limsup m_K/S_K > 0`, some rational `q` has `{K : m_K ≥ q S_K}` infinite and the two e.c.
hypotheses `(good, γ)`, `(liar, 1 on that set)` in the constant-reward environment defeat
every estimating agent.  (`WEIGHTED_BRIA.md` §4.1; LEAN `sum_support_jump_le`,
`sum_jump_div_sqrt_le`, `jump_div_sqrt_le`, `dominant_block_lower_bound`; FIX
`test_pressure.A`, `B`, `test_weighted.Dominance`, `J`, `K`.)

## 2. Exact effectivity assumptions

Sufficiency: **none beyond mathematical non-dominance.**  The constructor reads only the
observed prefix `(S_k, M_k)`; the bound `𝒜_K ≤ 2√(S_K M_K) + √S_K (1 + ln K)` is proved
from `Σ_k (M_k − M_{k−1})/√M_k ≤ 2√M_K`; no modulus, majorant, or code for the schedule
is used.  The first pass's `ρ̄`-majorant argument is withdrawn.  The learner is computable
uniformly in the schedule when the schedule is computable, and runs relative to an
online presentation otherwise.  Necessity: existential in the rational threshold `q`
(the limsup is not computable from a code); given `q`, uniform; the adversarial
hypotheses are e.c. whenever the schedule is; criterion-level, for any class containing
those two hypotheses.  Layers I (criterion impossibility), II (auction sufficiency under
(i′)+(ii)) and III (allowance existence iff non-dominance, with the uniform witness) are
stated separately and the "iff" is their conjunction with the quantifiers above.

## 3. Strongest continuation-BRIA theorem

**Theorem 1 (continuation-promise competence).**  For a covered hypothesis `h` with
condition (R), `LEARN_T(h) = Σ_k m_k (e_{h,k} − G^obs_k(α)) ≤ o(T)`.  **Theorem 2
(actual-history).**  Add `SLACK_T(h) ≤ o(T)`: `Σ_k m_k (Ĝ_k(q; H^α) − G^obs_k(α)) ≤ o(T)`.
**Theorem 3 (own-trajectory).**  Add `SHIFT_T ≤ o(T)`.  (`GROWING_HORIZON.md` §1–2.)  The
first pass's conclusion "cannot underperform a hypothesis whose promises are sound" is
Theorem 1 and is a statement about *promises*; every reading of it as a statement about a
controller's value is withdrawn (FIX `D_PromiseVersusValue`: value 1, promise 0, no
competence against 1).

## 4. Exact promise condition consumed

(R): for some `C`, the weighted record `ℓ^h_K = Σ_{tests ≤ K} m_k (G^obs_k − e_{h,k})` is
`≥ −C` at infinitely many rejection rounds — the negation of coverage's divergence
clause.  Sufficient: record bounded below; finite total tested overpromise
`Σ_{tests} m_k (e − G^obs)_+ < ∞`; wrong on finitely many tests (FIX `F`); sound on every
test.  **Not sufficient:** sublinear but divergent tested overpromise (FIX `G`): the
criterion lets a BRIA reject such a hypothesis forever while testing it on a density-zero
set.  A generic continuation hypothesis is `(controller, treatment, claim)` and the claim
is not by definition a lower bound (`CONTINUATION_HYPOTHESES.md` §1).

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

`LEARN ≤ o(T)` (Theorem 1, needs (R)); `SLACK ≤ o(T)` (promise recognizability;
one-sided, overpromising on untested blocks only helps); `SHIFT ≤ o(T)` (recoverability;
one-sided, along the learner's actual block starts, per policy).  Uniform block recovery
`m (Ĝ_m(π; H^π) − Ĝ_m(π; H)) ≤ φ(m)`, `φ(m)/m → 0`, is one checkable sufficient schema;
its corrigibility instance is the **catch-up cost** of an authorized amendment (per-block
shift exactly `d`, FIX `M_RecoverableAmendment`).  The regret class is
`Π_rec,prom = {legitimate π : covered h_π with (R), SLACK ≤ o(T), SHIFT ≤ o(T)}`.

## 7. What the constitution supplies

`Exec^G` (safe primitive execution: only admitted proposals run, refusals become `⊥`) and
the comparator class of gate-transparent continuations; through reversibility of the
slow lane, the catch-up cost that bounds `SHIFT` for policies differing by an authorized
amendment.

## 8. What it does not supply

Task-value or future-principal-value claims about any controller (`SLACK` is a
performance-recognizability interface, not a legitimacy certificate); recoverability
for irreversible amendments (those policies fall outside `Π_rec,prom`); any certificate
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
- Lease necessity restated at the level of promise–treatment alignment, with the
  whole-block lease as the canonical realization and an alternative treatment validly
  tested by interruption (FIX `I`, `J`); treatments are advisor-side only, so no
  "absent intervention" counterfactual enters a score.
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
