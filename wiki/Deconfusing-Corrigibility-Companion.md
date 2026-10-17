# Deconfusing Corrigibility — formal companion

The formal content of the post "Deconfusing Corrigibility" — the sections *Definitions*
through *Learning with logical induction* — is one Lean file in this repository:
[`DeconfusingCorrigibility.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean), namespace
`Workspace.Deference.Contrib.DeconfusingCorrigibility`. Every table below lists a post item,
its statement in the post's notation, the Lean declaration that states and proves it, and a
link to that declaration's source line. Every declaration is kernel-checked, sorry-free, and
audits to `[propext, Classical.choice, Quot.sound]`; each theorem is registered in
[`projects/deference/CLAIMS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/projects/deference/CLAIMS.md) with class `lean-proved` under the identifier
given in its row. Each theorem's hypothesis package is inhabited by a concrete instance in
the file's `Witness` namespace (last table). Unqualified Lean names below are relative to
the file's namespace.

## Notation: post and Lean

The Lean statements are the post's up to the following choices, all of which are visible
in the linked source.

| post | Lean | remark |
|---|---|---|
| `λ` | `lam` | `λ` is a reserved word in Lean. The field is `Params.lam`; `δ`, `τ`, `κ`, `θ`, `ε`, `R`, `T`, `t` keep their names. |
| `h a ω` | `D.hist a ω` | the continuation history of action `a` in state `ω`, a field of `Decision` |
| `E_μ[f]` | `expectR μ f` | the workspace's finite credence, `LICorrigibility.expectR μ f = Σ_ω μ ω · f ω` over a `Fintype` state space, with `0 ≤ μ` and `Σ_ω μ ω = 1` as the fields `Decision.μ_nonneg`, `Decision.μ_sum` |
| `P_μ[N(h a ·) ≥ 1]` | `expectR μ (fun ω => ind (1 ≤ N (hist a ω)))` | `ind p` is the indicator `1{p}` of a decidable proposition, as a real |
| `1{N(h a ·) = 0}` | `ind (N (hist a ω) = 0)` | same |
| `(1/K) Σ_{k<K} x_k` | `(∑ k ∈ range K, x k) / (K : ℝ)` | Lean's `x / 0 = 0`, so each average is `0` at `K = 0`; every statement about averages is eventual, so `K = 0` carries no content |
| `(1/K) Σ_{k<K} (U_k a'_k − S_k)` | `Sequential.excess a' K` | the post does not name this quantity; the name is the file's |
| `E ⊆ ℕ`, `k ∈ E` | `E : ℕ → Bool`, `E k = true` | the exploration set as a Boolean predicate on decisions; `k ∉ E` is `E k = false` |
| `ε_K = |E ∩ {0,…,K−1}| / K` | `Exploration.ε K` | `((range K).filter (fun k => E k = true)).card / K` |
| `limsup_K x_K ≤ c` | `LimsupLE x c` | the eventual form, used throughout: `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, x K ≤ c + γ`. Mathlib's `Filter.limsup` is not used. |
| Unbiasedness From Feedback | `Sequential.UnbiasedFromFeedback` | `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, excess a K ≤ γ`, exactly the post's clause (with `c = 0`, `≤ γ` rather than `≤ 0 + γ`) |
| `ε_K → 0` | `LimsupLE ε 0` | since `ε_K ≥ 0`, this is convergence to `0` |
| the setting's data | structures `Params`, `Scoring H`, `Decision H Ω A`, `Sequential A`, `Exploration A` | each hypothesis package is a structure; `D.N`, `Q.U`, `X.θ` and so on are field accesses; later structures extend earlier ones |
| "`a'` available at `k`" | `avail k a'` | a field `avail : ℕ → A → Prop` of `Sequential`; `a_k*` available is the field `astar_avail` |

Two statements differ from the post in strength, both in the direction of fewer or weaker
hypotheses being stated where the post has more, except one added hypothesis:

- **Theorem 2(c), first clause.** `Decision.theorem2c` is stated for any alternative `a*`;
  the post's hypothesis that `a*` is authority-respecting is not needed for the clause
  `v a > (1 − U a*)/λ → U a* > U a` and is not assumed. It is assumed for the second clause,
  `Decision.theorem2c_tau`.
- **Corollary (b).** `Exploration.corollary_b` uses the hypothesis `U_k a' ≤ 1` for every
  `a'` available at `k` (the field `Exploration.U_le_one`), which the dispatch did not
  list. Without it the statement is false: at an exploration step nothing else bounds
  `U_k a'_k` above. The post's estimates are an inductor's expectations of a score at most
  `1`, which is where the bound comes from; here it is a hypothesis.

## Definitions

| post | statement | Lean | source |
|---|---|---|---|
| parameters | `δ > 0`; a weight `λ > 1 + δ` | `Params` (fields `δ`, `lam`, `δ_pos`, `lam_gt`) | [`Params`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L78) |
| histories, legitimacy | a type `H`; `Legit : H → Prop`, an abstract input; nothing assumed about its content beyond the bounds on `V` | `Scoring H`, field `Legit` | [`Scoring`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L115) |
| violation count | `N : H → ℕ` | `Scoring.N` | [`N`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L119) |
| evaluation | `V : H → ℝ`; `Legit h → 0 ≤ V h ≤ 1`; `¬Legit h → −δ ≤ V h < 0` | `Scoring.V`, `Scoring.V_legit`, `Scoring.V_illegit` | [`V_legit`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L122), [`V_illegit`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L123) |
| score | `S h = V h − λ N h` | `Scoring.S` | [`S`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L130) |
| `τ` | `τ = (1 + δ)/λ` | `Params.τ` | [`τ`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L91) |

## Theorem 1 (three ranges)

For every `h : H`. Registered as `deconfusing.theorem1`, statement of record
`Scoring.theorem1`.

| post | statement | Lean | source |
|---|---|---|---|
| first range | `N h ≥ 1 → S h ≤ 1 − λ` | `Scoring.theorem1_violated` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L160) |
| the gap | `1 − λ < −δ` | `Scoring.theorem1_gap` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L167) |
| second range | `N h = 0 ∧ ¬Legit h → −δ ≤ S h ∧ S h < 0` | `Scoring.theorem1_illegitimate` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L170) |
| third range | `N h = 0 ∧ Legit h → 0 ≤ S h ∧ S h ≤ 1` | `Scoring.theorem1_legitimate` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L176) |
| Theorem 1 | the conjunction of the four, for every `h` | `Scoring.theorem1` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L184) |

## Single-decision setting

| post | statement | Lean | source |
|---|---|---|---|
| states, credence | a finite `Ω`; `μ : Ω → ℝ` with `μ ≥ 0`, `Σ_ω μ ω = 1` | `Decision H Ω A`, fields `μ`, `μ_nonneg`, `μ_sum` | [`Decision`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L242) |
| continuation histories | `h a ω` | `Decision.hist` | [`hist`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L248) |
| `U a` | `U a = E_μ[S(h a ·)]` | `Decision.U` | [`U`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L255) |
| `v a` | `v a = P_μ[N(h a ·) ≥ 1]` | `Decision.v` | [`v`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L258) |
| authority-respecting alternative | `∀ ω, N(h a* ω) = 0` | `Decision.Respects a*` | [`Respects`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L261) |
| asking cost | `κ = E_μ[(S(h a ·) − S(h a* ·)) · 1{N(h a ·) = 0}]` | `Decision.κ a a*` | [`κ`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L264) |

## Theorem 2

Hypotheses: `D : Decision H Ω A`; `a a* : A`; `a*` authority-respecting (`hstar : D.Respects a*`)
where the row says so.

| post | statement | Lean | source | registered as |
|---|---|---|---|---|
| 2(a) | `v a = 1 → U a* − U a ≥ λ − (1 + δ)`, with `hstar` | `Decision.theorem2a` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L296) | `deconfusing.theorem2a` |
| 2(a), margin | `λ − (1 + δ) > 0` | `Decision.theorem2a_pos` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L304) | (with 2(a)) |
| 2(b) | `U a* − U a ≥ (λ − (1 + δ)) · v a − κ`, with `hstar` | `Decision.theorem2b` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L307) | `deconfusing.theorem2b` |
| 2(b), hence | `v a > κ/(λ − (1 + δ)) → U a* > U a`, with `hstar` | `Decision.theorem2b_strict` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L327) | `deconfusing.theorem2b-strict` |
| 2(c) | `v a > (1 − U a*)/λ → U a* > U a`, for any `a*` (see *Notation*) | `Decision.theorem2c` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L337) | `deconfusing.theorem2c` |
| 2(c), threshold | `(1 − U a*)/λ ≤ τ`, with `hstar` | `Decision.theorem2c_tau` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L345) | `deconfusing.theorem2c-tau` |

The pointwise facts behind Theorem 2 are `Decision.S_le_one_sub`
(`S(h a ω) ≤ 1 − λ · 1{N(h a ω) ≥ 1}`), `Decision.U_le` (`U a ≤ 1 − λ v a`) and
`Decision.neg_δ_le_U` (`−δ ≤ U a*` for an authority-respecting `a*`), with the linearity
lemmas `expectR_mono`, `expectR_sub`, `expectR_const_mul`, `expectR_const` for the finite
credence.

## Sequential setting

| post | statement | Lean | source |
|---|---|---|---|
| decisions, realized data | `k : ℕ`; `V_k ≤ 1`; `N_k : ℕ` | `Sequential A`, fields `V`, `N`, `V_le_one` | [`Sequential`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L404) |
| realized score | `S_k = V_k − λ N_k` | `Sequential.S` | [`S`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L426) |
| estimates, choice, availability | `U_k : A → ℝ`; `a_k`; "`a'` available at `k`" | fields `U`, `a`, `avail` | [`U`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L413) |
| authority-respecting alternative | `a_k*` available at each `k`, with `−δ ≤ U_k a_k* ≤ 1` (a hypothesis) | fields `astar`, `astar_avail`, `astar_range` | [`astar_range`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L419) |
| tolerance | `t_k = (1 − U_k a_k*)/λ` | `Sequential.t` | [`t`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L429) |
| realized rate | `R_K = (1/K) Σ_{k<K} N_k` | `Sequential.R` | [`R`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L432) |
| average tolerance | `T_K = (1/K) Σ_{k<K} t_k` | `Sequential.T` | [`T`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L435) |
| maximization | `∀ k, ∀ a'` available at `k`, `U_k a' ≤ U_k a_k` | `Sequential.Maximizes` | [`Maximizes`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L444) |
| Unbiasedness From Feedback | `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, (1/K) Σ_{k<K} (U_k a_k − S_k) ≤ γ` | `Sequential.UnbiasedFromFeedback` | [`UnbiasedFromFeedback`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L451) |
| `limsup ≤` | the eventual form | `LimsupLE` | [`LimsupLE`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L358) |

Unbiasedness From Feedback is a hypothesis of Theorem 3 and the Corollary, named and
assumed; it is not derived in this file. The post derives it from Theorem 4.8.16 of the
Logical Induction paper. In this workspace that theorem is pinned as `thm:wubexp` /
`LogicalInduction.lic_not_frequently_positive_feedback_return` in the def-lattice ledger,
[`def-lattice-report.md`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/projects/deference/faf-cleanroom-2026-10-02/packages/def-lattice/def-lattice-report.md), row 4.8.16; the derivation for the score
sequence is `PRIORITIES.md` item 111. The workspace's weighted, absolute-value form of the
same fact, `BRIAFollowup.UnbiasedFromFeedback`, at the uniform weighting and for every
`γ > 0`, implies the post's form:
[`Sequential.unbiased_of_weighted`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L457).

## Theorem 3

Hypotheses: `Q : Sequential A`; `hmax : Q.Maximizes`; `huff : Q.UnbiasedFromFeedback`.

| post | statement | Lean | source | registered as |
|---|---|---|---|---|
| 3(a) Authority | `limsup_K (R_K − T_K) ≤ 0` | `Sequential.theorem3a` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L550) | `deconfusing.theorem3a` |
| 3(a), in particular | `limsup_K R_K ≤ τ` | `Sequential.theorem3a_rate` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L555) | `deconfusing.theorem3a-rate` |
| 3(b) Best Interests | for any `a'_k` with `a'_k` available at `k`: `limsup_K (1/K) Σ_{k<K} (U_k a'_k − S_k) ≤ 0` | `Sequential.theorem3b` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L564) | `deconfusing.theorem3b` |

The pointwise step is `Sequential.N_sub_t_le`: `N_k − t_k ≤ (U_k a_k* − S_k)/λ`, from
`V_k ≤ 1`; maximization turns `U_k a_k*` into `U_k a_k` (`Sequential.rate_le_excess`), and
`T_K ≤ τ` (`Sequential.T_le_τ`) comes from `U_k a_k* ≥ −δ`.

## Corollary (Exploration)

Hypotheses: `X : Exploration A` — a `Sequential A` together with `0 ≤ θ < 1`, the
exploration set `E`, maximization off `E` (`maximizes_off`), on `E` the bound
`U_k a_k ≥ −δ − λ θ` (`explore_bound`), and `U_k a' ≤ 1` on available options (`U_le_one`,
see *Notation*) — and `huff : X.UnbiasedFromFeedback`. The post derives the exploration-step
bound from an estimated violation count at most `θ` and linearity of the inductor's
expectation; here it is the hypothesis directly.

| post | statement | Lean | source | registered as |
|---|---|---|---|---|
| hypotheses | as above | `Exploration` | [`Exploration`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L577) | — |
| `ε_K` | `|E ∩ {0,…,K−1}| / K` | `Exploration.ε` | [`ε`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L593) | — |
| (a) | `limsup_K (R_K − T_K − ε_K (τ + θ)) ≤ 0` | `Exploration.corollary_a` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L669) | `deconfusing.corollary-a` |
| (b) | for any available `a'_k`: `limsup_K ((1/K) Σ_{k<K} (U_k a'_k − S_k) − ε_K λ (τ + θ)) ≤ 0` | `Exploration.corollary_b` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L676) | `deconfusing.corollary-b` |
| specialization | if `ε_K → 0`: `limsup_K (R_K − T_K) ≤ 0`, `limsup_K R_K ≤ τ`, and `limsup_K (1/K) Σ_{k<K} (U_k a'_k − S_k) ≤ 0` for every available `a'` | `Exploration.corollary_limit` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L685) | `deconfusing.corollary-limit` |

The pointwise steps are `Exploration.N_sub_t_le_expl` and `Exploration.excess_pt`; on an
exploration step the gap `U_k a_k* − U_k a_k ≤ 1 + δ + λ θ = λ (τ + θ)` is what the
exploration term pays for.

## Witnesses

Each theorem's full hypothesis package is inhabited by a concrete instance, and the
theorem's conclusion is stated on that instance.

| theorem | instance | package inhabited by | conclusion on the instance | source |
|---|---|---|---|---|
| Theorem 1 | `Witness.scoring`: histories `Bool × ℕ` (a legitimacy flag and a count), `δ = 1`, `λ = 3`, `V = 1/2` on legitimate and `−1/2` on illegitimate histories | one history in each range | `Witness.theorem1_instance` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L728) |
| Theorem 2 | `Witness.decision`: a fair coin on `Bool`; actions `respecting` (never violates), `risky` (violates on `true`), `violating` (always) | `Witness.theorem2a_package`, `theorem2b_package`, `theorem2c_package` (`v risky = 1/2`, `v violating = 1`, `U respecting = 1/2`, `κ risky respecting = 0`) | `Witness.theorem2_instance`, `Witness.theorem2b_instance` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L794) |
| Theorem 3 | `Witness.sequential`: every action available, estimates `1/2` everywhere equal to the realized scores, no violations, `a_k* = false` on every menu | `Witness.sequential_maximizes`, `Witness.sequential_unbiased` | `Witness.theorem3_instance` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L835) |
| Corollary | `Witness.exploration`: the same sequence with `E = {0}`, `θ = 1/10` | `Witness.exploration_explores` (`0 ∈ E`), `Witness.exploration_unbiased`, `Witness.exploration_ε_limsup` (`ε_K ≤ 1/K → 0`) | `Witness.corollary_instance` | [source](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean#L890) |

## Verifying

From `lean/`: `lake build` elaborates the file; `python3 ../tests/audit_axioms.py`
re-elaborates every file and checks each `#print axioms` line at the end of the file
against `[propext, Classical.choice, Quot.sound]`. The registrations are checked by
`python3 -m checkers.run` from the repository root.

## Relation to the earlier statements in this repository

[`PostStatement.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/PostStatement.lean) (round 2026-10-01) states an earlier post's
theorem over the kernel's objects. Its `LexParams` carries `ϖ`, `D`, `w`: `ϖ` is the
per-violation weight, the post's `λ`; the ordinary term lies in `[0, D]`, where the post's
`V` lies in `[−δ, 1]` with the illegitimate floor `−δ`, so `D ↔ 1` and `w ↔ −δ` (the
window `D − ϖ < w ≤ 0` corresponds to `1 − λ < −δ`, Theorem 1's gap); the kernel's
evaluation separates a bid, a count known in advance and a priced risk, which the post's
single `U` does not. Under this dictionary `Headline.subjective_exchange_rate`'s threshold
`(D − c)/ϖ`, with `c` the value of queue-and-wait, has the form of Theorem 2(c)'s
`(1 − U a*)/λ`, and `box2_dominance`'s margin `ϖ − (D − w)` has the form of Theorem 2(a)'s
`λ − (1 + δ)`. These are correspondences of form; no equivalence is proved, and neither
statement is derived from the other here.

[`KernelExtension.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/lean/Workspace/Deference/Contrib/KernelExtension.lean) proves `realized_rate` and
`exploration_rate`: a finite-`K` bound on the `w`-weighted average of the *expected*
violation count `π_k`, with explicit overestimation and noise terms `B(K)`, `M(K)`, whose
exploration term is `ε̄ · ((D − lo)/ϖ + θ_hi)`. Theorem 3(a) and Corollary (a) here are
limsup statements on the *realized* counts `N_k` with uniform weights and no noise term.
Under `D ↔ 1`, `lo ↔ −δ`, `ϖ ↔ λ`, `θ_hi ↔ θ` the exploration coefficient
`(D − lo)/ϖ + θ_hi` is `τ + θ`, Corollary (a)'s. The objects differ — expected against
realized counts, weighted finite-`K` against uniform limsup — so neither theorem here is a
specialization or a generalization of a registered statement of that file, and Theorem 3 is
not the `realized_rate` result. The one proved link is `Sequential.unbiased_of_weighted`:
the weighted unbiasedness predicate that `exploration_rate` consumes, at uniform weighting,
implies the hypothesis the theorems here consume.

Round: [`prompts/2026-10-17-post-companion-formalization/`](https://github.com/A-M-Berns/alignment-workspace/tree/eb3556e4038d3c15568fcd206c4e80ad74a47ba9/prompts/2026-10-17-post-companion-formalization). Names are
provisional.
