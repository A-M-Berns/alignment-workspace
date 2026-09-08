# Source audit: `Oesterheld, Demski and Conitzer`, "A Theory of Bounded Inductive Rationality"

TARK 2023, EPTCS 379, pp. 421–440, arXiv:2307.05068.  Read from the arXiv PDF.  Labels:
**PAPER** established there; everything else in this round is DERIVED, LEAN, FIX, EXT or
OPEN and says so.

## 1. Definitions used, with their section

| object | paper | what it says |
|---|---|---|
| setting | §2 | `DP_t ∈ Fin(T)` finite; agent `c̄`, `c_t ∈ DP_t`; rewards `r_t ∈ [0,1]`; "counterfactual rewards are not defined"; `DP_t` "may in turn be calculated depending on the agent's choices"; the target is *myopically optimal* behaviour, "regardless of what consequences that has for future decision problems" |
| estimating agent | §4.1 | `ᾱ = (α^c_t ∈ DP_t, α^e_t ∈ [0,1])`; a hypothesis has the same type; `h^e` promise, `h^c` recommendation |
| class `H` | §4.1 | any set; usually functions computable in `O(g(t))`, "efficiently computable (e.c.)" |
| cumulative overestimation | Def. 1 | `L_T = Σ_{t≤T} (α^e_t − r_t)` |
| no overestimation | Def. 2 | `L_T / T ≤ 0` as `T → ∞`, i.e. `∀ε ∃t ∀T>t: L_T/T ≤ ε` (a `limsup ≤ 0`) |
| outpromise / reject | Def. 3 | `h^e_t > α^e_t` (strict) |
| test set | Def. 4 | `M ⊆ ℕ` with `α^c_t = h^c_t` for `t ∈ M` |
| record | Def. 5 | `l_T(ᾱ, r̄, M, h̄) = Σ_{t ∈ M, t ≤ T} (r_t − h^e_t)` |
| coverage | Def. 6 | `B` = rejection times; `ᾱ` covers `h̄` with `M` iff `B` finite or `(l_T)_{T ∈ B} → −∞` |
| BRIA | Def. 7 | no overestimation and coverage of every `h_i ∈ H` with test set `M_i`; test sets are part of `ᾱ` |
| Lemma 6 | A.1 | tests at rounds where `h^e_t = 0` can be dropped from `M` |

## 2. Theorems used

**Theorem 1** (§5, proof A.2) — for c.e. `H` of `O(g(t))`-computable hypotheses, a BRIA
covering `H` is computable in `O(g(t) q(t))`.  The construction:

- allowance `A(n, i) ≥ 0` with `Σ_n A(n, i) = ∞` for each `i` and
  `(1/N) Σ_{n≤N} Σ_i A(n, i) → 0` (finite per round);
- wealth `w_0(i) = 0`; winner `i*_t ∈ argmax_i min(h^e_{i,t}, w_t(i))`, arbitrary ties;
  `α_t = (h^c_{i*,t}, e*_t)` with `e*_t` the maximal wealth-bounded bid;
- update: non-winners `w_{t+1}(i) = w_t(i) + A(t, i)`; the winner additionally
  `+ r_t − e*_t` — it pays the *bid*, not the promise.  **Timing:** the bid at `t` is
  bounded by `w_t(i)`, which contains `A(1..t−1, i)`; `A(t, i)` is credited *after* round
  `t` (settlement timing).  `A` is a fixed function of `(n, i)`; nothing in the
  construction lets it read the round's decision problem;
- no overestimation: `Σ_{i ∈ B⁺_T} w_T(i) = Σ_i Σ_{n≤T} A(n,i) + Σ_{t≤T} (r_t − α^e_t)`
  with all wealths `≥ 0`, so `L_T/T ≤ (1/T) Σ_{n≤T} Σ_i A(n,i) → 0`;
- coverage of `h_i` outpromising infinitely often, with `M_i` = its winning rounds:
  (A) `M_i` infinite, because a hypothesis that stops winning accumulates allowance until
  `w_t(i) ≥ 1` and then bids its promise, contradicting that it strictly outpromises the
  maximal bid; (B) `M_i` is a test set by construction; (C) at a rejection `T ∈ B_i`,
  `w_T(i) < h^e_{i,T} ≤ 1`, and `w_T(i) = Σ_{n≤T} A(n,i) + Σ_{t ∈ M_i, t<T} (r_t − h^e_{i,t})`
  (paid ≤ promised), so `Σ_{t∈M_i,t<T} (h^e − r) > Σ_{n≤T} A(n,i) → ∞`;
- computability: `A(t, ·)` with finite e.c. support keeps the active set finite;
  example `A(n,i) = n^{-1} i^{-2}` for `i < n`.

**Footnote 2** (§5): the first-price format "is mainly chosen for its simplicity"; other
formats "get somewhat different BRIA-like properties"; "with combinatorial auctions, one
could achieve cross-decision optimization."  One sentence, no definition, no theorem.
This round does not build on it.

**Theorem 2** (§5, A.3) — a BRIA for the `O(g)`-computable hypotheses is not
`O(g)`-computable, by the hypothesis that promises 1 and recommends an option other than
`α^c_t` whenever `|DP_t| ≥ 2` and `α^e_t < 1`.

**Theorem 3** (§6, A.4) — `ā` with `a_t ∈ DP_t` efficiently identifiable, `L̄` e.c., and
`α^c_t = a_t ⇒ r_t ≥ L_t`; then `Σ_{t≤T} r_t / T ≥ Σ_{t≤T} L_t / T` in the limit.  Proof:
the hypothesis `(a_t, L_t)` has record `≥ 0` on every test set, so it is rejected finitely
often, so `α^e_t ≥ L_t` for all but finitely many `t`; no overestimation finishes.  The
quantitative content is `liminf_T (1/T) Σ (r_t − L_t) ≥ 0`.

**Theorem 4** (§6, A.5) — with `r_t` on the rounds `α^c_t = a_t` boundedly vMWC-random
with e.c. means `μ̄`, `Σ r_t/T ≥ Σ μ_t/T`.  Proof: the hypothesis `(a_t, max(μ_t − ε, 0))`
has record `→ +∞` on any infinite e.c. test set.  Promises need not be pointwise sound;
they need only be unrefuted on the learner's own tests.

**Theorem 5** (§7) — folk theorem; the paper stresses the criterion is myopic and the
result "is unrelated to the folk theorems for repeated games."

**Appendix C** — Hannan consistency is unachievable in the setting (SAO), achievable with
independent randomization, and undesirable as a criterion: on a Newcomb-like problem regret
minimization "would therefore require choosing the policy that minimizes the actual reward
obtained".

**Appendix D** — why estimates are necessary: a meta law-of-effect over policies without
promises is defeated by *biased testing* — the max policy tested on rounds where every
option is `≤ 1/2`, the worse policy on rounds with options `> 1/2`, so raw averages rank
them backwards; "for each deterministic procedure of deciding which hypothesis to test,
there is a decision process in which this testing procedure introduces a relevant bias";
the alternatives are estimates (the paper's) or independent randomization.

## 3. What the paper does not claim

- Nothing about non-myopic planning, continuation policies, blocks, leases, or policy
  regret.  §2 and §7 say the opposite: the target is the present decision problem.
- Nothing about weighted or variable-length rounds; every round has weight one.
- No combinatorial-auction construction; footnote 2 is a remark.
- No claim that a BRIA's *behaviour* is determined by the criterion beyond the limit
  frequencies its theorems state; Theorem 1's auction is one BRIA.
- Definition 5's record sums tests `t ≤ T` (inclusive); the proof of Theorem 1 part (C)
  sums `t < T`.  For unit weights the two differ by at most 1 and the proof is
  unaffected; for block weights they differ by `w_T`, but the weighted rejection bound
  `ℓ_T < w_T − A_i(T)` holds for the inclusive record too, because the promise cancels
  when the rejected hypothesis is the wealth-constrained winner (`WEIGHTED_BRIA.md` §3).
- The paper's "myopic" is about the *criterion*, not a property of the auction: the auction
  tests every outpromising hypothesis, including ones whose recommendation changes future
  `DP_t`.  What the criterion does not require is any credit for a later reward.

## 4. Source object → round object

| paper | this round |
|---|---|
| round `t`, `DP_t`, `c_t`, `r_t` | macro-round `k`, menu `DP'_k` of `m_k`-step controllers, chosen controller, block average `G_k` |
| hypothesis `(h^c_t, h^e_t)` | continuation hypothesis `(c_{h,k}, e_{h,k})` at the block contract `χ_k`: a causal advisor continuation for the block and an accountable contextual *claim* about its realized gated block score — a claim that may be wrong, as in the paper |
| testing `h` at `t` = choosing `h^c_t` | testing `h` at `k` = the derived event that `h` is selected and `c_{h,k}` is executed through the gate for the block (intuitively, an execution lease) |
| `L_T/T ≤ 0` | fixed horizon: unchanged; variable horizon: `Σ m_k (α^e_k − G_k) / Σ m_k ≤ 0` |
| record `Σ_M (r_t − h^e_t)` | fixed: unchanged; variable: `Σ_{M} m_k (G_k − h^e_k)` |
| wealth in reward units, bid `min(h^e, w_t)` from the carried wealth, allowance credited after the round | wealth in total-reward units, per-step bid `min(e, B_k / m_k)` from the **opening capital** `B_k = W_k + A(k,i)` — the round's subsidy is credited at the opening, after `m_k` is revealed and before bids; winner pays `m_k · bid`, receives `m_k · G_k`.  The same auction as the paper's under the reindexed allowance `A'(k) = A(k+1)` with initial endowment `A(1,i)`; the modification is that the subsidy funding block `k` may read `m_k` |
| `Σ_n A(n,i) = ∞` | `A_i(k) − m_k → ∞` (capital adequacy, opening timing, `A_i` through `k` inclusive); witness the prefix rule `s(k) = ⌊√(S_k/M_k)⌋`, `A(k,i) = ΔM_k + 1/k`.  Under the paper's own timing no prefix-online rule serves every non-dominant schedule (`WEIGHTED_BRIA.md` §4.1 III′) |
| `(1/N) Σ_{n≤N} Σ_i A(n,i) → 0` | `Σ_{k≤K} Σ_i A(k,i) / Σ_{k≤K} m_k → 0` (weaker per macro-round) |
| Theorem 3 | Fixed-Horizon and continuation-promise competence (`FIXED_HORIZON.md` §3, `GROWING_HORIZON.md` §1), under condition (BR) — the record bounded below, which rules out Definition 6's divergence clause — the hypothesis the paper's own proof uses in the form `record ≥ 0` |
| Appendix D | `CONTINUATION_HYPOTHESES.md` §3, fixtures G/H |

The mapping is a typing of the same criterion; the paper's theorems are cited through it
and not re-proved, except where the round's weights change the algebra or the timing,
and then the weighted algebra is proved (Lean `ContinuationBRIA.lean`, with the source
timing as `Feasible` and the weighted timing as `FeasibleOpening`).  Three registers, kept
apart: the fixed-horizon **criterion** reduction is the paper verbatim (Definitions 1–7,
Theorems 1–4); the paper's **construction** has settlement timing with a schedule-blind
allowance; the **weighted construction** has opening timing with a prefix-reading
subsidy, a modification the round makes and names.
