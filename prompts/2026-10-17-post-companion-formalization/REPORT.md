# Report — 2026-10-17-post-companion-formalization

| | |
|---|---|
| Prompt author | the maintainer (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Lean | `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (one file; witnesses in its `Witness` namespace) |
| Wiki | `wiki/Deconfusing-Corrigibility-Companion.md` |
| Registrations | `deconfusing.*` in `projects/deference/CLAIMS.md`, against item 107 |
| Filed | `PRIORITIES.md` item 111 |
| Date | 2026-10-17 |

**Verdict.** THE-POSTS-FORMAL-CONTENT-AS-ONE-LEAN-FILE-WITH-A-COMPANION-PAGE — Theorem 1, Theorem 2(a)(b)(c), Theorem 3(a)(b) and the Corollary (Exploration) with its ε_K → 0 specialization stated in the post's notation and proved, every hypothesis package inhabited; Unbiasedness From Feedback a named hypothesis, not derived; limsup in the eventual form; Corollary (b) needs the estimate bound U_k a' ≤ 1, added as a hypothesis and declared

**Depends on** `2026-09-15-li-corrigibility`: its finite credence `LICorrigibility.expectR` is reused as a definition; no result of that round is taken as a hypothesis.

The post's formal content — Definitions, Theorem 1, the single-decision setting, Theorem 2,
the sequential setting, Theorem 3, the Corollary (Exploration) with its `ε_K → 0`
specialization — is stated in the post's notation and proved, with every hypothesis
package inhabited. Unbiasedness From Feedback is a named hypothesis. The wiki page maps
each post item to its declaration and source line and states every notational difference.

## Mapping

All names are in `Workspace.Deference.Contrib.DeconfusingCorrigibility`.

| post | Lean |
|---|---|
| `δ > 0`, `λ > 1 + δ`, `τ = (1 + δ)/λ` | `Params` (`δ`, `lam`, `δ_pos`, `lam_gt`), `Params.τ` |
| `H`, `Legit`, `N`, `V` with the two bounds, `S h = V h − λ N h` | `Scoring H` (`Legit`, `N`, `V`, `V_legit`, `V_illegit`), `Scoring.S` |
| Theorem 1, three ranges and the gap | `Scoring.theorem1_violated`, `theorem1_gap`, `theorem1_illegitimate`, `theorem1_legitimate`; bundled as `Scoring.theorem1` |
| `Ω`, `μ`, `h a ω`, `U`, `v`, authority-respecting, `κ` | `Decision H Ω A` (`μ`, `μ_nonneg`, `μ_sum`, `hist`), `Decision.U`, `Decision.v`, `Decision.Respects`, `Decision.κ` |
| Theorem 2(a) | `Decision.theorem2a`; margin `Decision.theorem2a_pos` |
| Theorem 2(b) | `Decision.theorem2b`; consequence `Decision.theorem2b_strict` |
| Theorem 2(c) | `Decision.theorem2c`; threshold `Decision.theorem2c_tau` |
| `V_k ≤ 1`, `N_k`, `S_k`, `U_k`, `a_k`, `a_k*` with `−δ ≤ U_k a_k* ≤ 1`, `t_k`, `R_K`, `T_K`, maximization | `Sequential A` (`V`, `N`, `V_le_one`, `avail`, `U`, `a`, `astar`, `astar_avail`, `astar_range`), `Sequential.S`, `t`, `R`, `T`, `excess`, `Maximizes` |
| Unbiasedness From Feedback | `Sequential.UnbiasedFromFeedback` (hypothesis) |
| Theorem 3(a), and `limsup R_K ≤ τ` | `Sequential.theorem3a`, `Sequential.theorem3a_rate` |
| Theorem 3(b) | `Sequential.theorem3b` |
| `θ`, `E`, `ε_K`, the exploration hypotheses | `Exploration A` (`θ`, `θ_nonneg`, `θ_lt_one`, `E`, `maximizes_off`, `explore_bound`, `U_le_one`), `Exploration.ε` |
| Corollary (a), (b), specialization | `Exploration.corollary_a`, `corollary_b`, `corollary_limit` |

The credence is the workspace's `LICorrigibility.expectR` (finite state space, `μ ≥ 0`
summing to one), per the dispatch; no new credence structure was introduced. Linearity of
that expectation is proved in the file (`expectR_mono`, `expectR_sub`, `expectR_const_mul`,
`expectR_const`).

**The limsup form.** Every limsup is the eventual form, throughout:
`LimsupLE x c := ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, x K ≤ c + γ`. `Filter.limsup` is not used.
`ε_K → 0` is `LimsupLE X.ε 0`. Unbiasedness From Feedback is stated exactly as the dispatch
gives it (`… ≤ γ`); `Sequential.limsup_of_unbiased` is the one-line bridge to `LimsupLE`.

**Witnesses.** `Witness.scoring` (histories `Bool × ℕ`, `δ = 1`, `λ = 3`) inhabits Theorem
1 in each range (`theorem1_instance`). `Witness.decision` (a fair coin on `Bool`; actions
`respecting`, `risky`, `violating`) inhabits every package of Theorem 2:
`theorem2a_package` (`v violating = 1`), `theorem2b_package` (`v risky = 1/2 > 0 = κ/(λ −
(1 + δ))`), `theorem2c_package` (`1/2 > 1/6`); conclusions on the instance
`theorem2_instance`, `theorem2b_instance`. `Witness.sequential` (estimates equal to realized
scores, `a_k*` on every menu) inhabits Theorem 3 (`theorem3_instance`). `Witness.exploration`
(the same sequence with `E = {0}`, `θ = 1/10`) inhabits the Corollary with exploration
occurring and `ε_K ≤ 1/K → 0` (`corollary_instance`).

**The connection to Logical Induction.** Documentation only, as dispatched: the file header,
the docstring of `Sequential.UnbiasedFromFeedback` and the wiki page point at `thm:wubexp` /
`LogicalInduction.lic_not_frequently_positive_feedback_return`, row 4.8.16 of
`projects/deference/faf-cleanroom-2026-10-02/packages/def-lattice/def-lattice-report.md`. One
proved link, not requested by the dispatch: `Sequential.unbiased_of_weighted` — the
workspace's weighted absolute-value predicate `BRIAFollowup.UnbiasedFromFeedback` at the
uniform weighting, for every `γ > 0` from some `N₀`, implies the post's form. It cites
nothing from `LogicalInduction`.

## Verification

VERIFICATION_PLACEHOLDER

## Deviations and corrections to the prompt

1. **The post text was not attached.** The dispatch says the post text is attached; nothing
   arrived with it, and the post is not in the repository. The formalization follows the
   dispatch's own section "The post's formal objects, to be matched exactly", which states
   every definition, theorem part and corollary part. Where the post's exact wording
   matters (the hypothesis of Corollary (b), the range of the estimates), this report says
   what was assumed.
2. **Corollary (b) carries one hypothesis the dispatch did not list**: `U_k a' ≤ 1` for
   every `a'` available at `k` (`Exploration.U_le_one`). The dispatched statement is false
   without it — on an exploration step `k ∈ E` nothing relates `U_k a'_k` to `U_k a_k`, so
   a single exploration step with `U_k a'_k` large violates the bound. The post's estimates
   are an inductor's expectations of a score at most `1`, which supplies the bound there;
   here it is a field of `Exploration`, stated on the wiki page.
3. **Theorem 2(c), first clause, is stated without the authority-respecting hypothesis.**
   `v a > (1 − U a*)/λ → U a* > U a` holds for any `a*` (from `U a ≤ 1 − λ v a`), so
   `Decision.theorem2c` does not assume `Respects a*`; `Decision.theorem2c_tau` does. The
   post's statement is the instance with the hypothesis present.
4. **`λ` is `lam`.** `λ` is a reserved word in Lean. Every other parameter keeps its name.
5. **The exploration set is a Boolean predicate.** `E : ℕ → Bool` with `k ∈ E` as
   `E k = true`, rather than `Set ℕ` with a decidability instance; `ε_K` is the filtered
   cardinality over `K`.
6. **Averages are `(Σ …) / (K : ℝ)`**, not `(1/K) * Σ …`; equal for `K ≥ 1`, and `0` at
   `K = 0`, which no eventual statement sees.
7. **The registrations answer item 107**, the filed item for the theorems behind the
   maintainer's posts (its *consumed by* names "any round extending the headline"). No
   item names "Deconfusing Corrigibility", and the dispatch granted one filing — the
   follow-up, item 111 — so none was filed for the registration itself. The maintainer may
   re-point `answers_item` (listed below).
8. **One lemma beyond the dispatch**, `Sequential.unbiased_of_weighted`, imports
   `BRIAFollowup` for its hypothesis's predicate. It adds a hypothesis-to-hypothesis
   implication and no claim about Logical Induction.
9. **The def-lattice pointer.** The dispatch says the pin lives "in the def-lattice
   ledger"; the row is in that package's report, `def-lattice-report.md`, row 4.8.16, and
   is cited by that path.
10. **The session could not fetch the Mathlib cache** (the hosts `release.lean-lang.org`,
    `mathlib4.lakecache.org` and `lakecache.blob.core.windows.net` are denied by the
    environment's network policy), so the toolchain was installed from the GitHub release
    and Mathlib was built from source in the session. The verification section records
    what ran. CI runs the same gates from the cache.
11. **One number outside the write scope changed.** `wiki/Deference.md` binds the deference
    registry's entry count to the state emission; registering twelve entries moved it, and
    `checkers/wiki_state_bindings.py` fails until the bound value matches. The value was
    updated and nothing else on that page was touched (`AGENTS.md` §14: a contained fix
    belongs to the round that hits it).

## What this does not establish

- **Unbiasedness From Feedback is assumed, not derived.** `Sequential.UnbiasedFromFeedback`
  is a hypothesis of Theorem 3 and the Corollary. Nothing here instantiates Theorem 4.8.16
  of the Logical Induction paper, and nothing cites
  `LogicalInduction.lic_not_frequently_positive_feedback_return`; the derivation is item
  111. `unbiased_of_weighted` relates two hypotheses; it establishes neither.
- **The Corollary's exploration hypothesis stands in for linearity.** `U_k a_k ≥ −δ − λ θ`
  on `k ∈ E` is taken directly (`Exploration.explore_bound`); the post's derivation from an
  estimated violation count at most `θ` and linearity of the inductor's expectation is not
  formalized. Likewise `U_k a' ≤ 1` (`U_le_one`) is a hypothesis, not a consequence of the
  estimates being expectations.
- **Nothing is assumed about `Legit` beyond the bounds.** `Legit : H → Prop` is an abstract
  field; the theorems use only `V_legit` and `V_illegit`. No connection to
  `ThinLegitimacy`, `Legitimacy.lean` or the authority module is stated or claimed.
- **`U_k a_k* ∈ [−δ, 1]` is a hypothesis** (`Sequential.astar_range`), as is `V_k ≤ 1`,
  `a_k*` available at every `k`, and maximization. None is derived from a model of the
  agent.
- **The post's Theorem 3 is not the repository's `realized_rate`**, and no equivalence or
  specialization relation to `KernelExtension.realized_rate`, `exploration_rate` or
  `PostStatement.post_theorem` is claimed; the wiki page's final section states the
  correspondences of form and the differences of object (expected against realized counts,
  weighted finite-`K` against uniform limsup).
- **Equivalence of `LimsupLE` with `Filter.limsup`** is not proved; the eventual form is
  the statement of record.
- **The witnesses are trivial where the dispatch allowed it**: the sequential witnesses have
  estimates equal to realized scores, so Unbiasedness From Feedback holds with every excess
  zero. They show the packages are consistent, not that they are satisfiable by a learner.

## New names introduced (provisional)

File `DeconfusingCorrigibility.lean`; namespace
`Workspace.Deference.Contrib.DeconfusingCorrigibility`. Structures `Params`, `Scoring`,
`Decision`, `Sequential`, `Exploration` and their fields as listed in the mapping;
`Params.τ`, `Params.lam_pos`, `lam_ne`, `gap_pos`, `τ_pos`, `lam_mul_τ`;
`div_le_div_same_denom`; `Scoring.S`, `V_le_one`, `neg_δ_le_V`, `S_le_one`,
`S_eq_of_N_zero`, `neg_δ_le_S_of_N_zero`, `theorem1_violated`, `theorem1_gap`,
`theorem1_illegitimate`, `theorem1_legitimate`, `theorem1`; `ind`, `ind_pos`, `ind_neg`;
`expectR_mono`, `expectR_sub`, `expectR_const_mul`, `expectR_const`; `Decision.U`, `v`,
`Respects`, `κ`, `S_le_one_sub`, `U_le`, `neg_δ_le_U`, `theorem2a`, `theorem2a_pos`,
`theorem2b`, `theorem2b_strict`, `theorem2c`, `theorem2c_tau`; `LimsupLE` and
`LimsupLE.of_le`, `add`, `add_const`, `mul_const`; `Sequential.S`, `t`, `R`, `T`, `excess`,
`Maximizes`, `UnbiasedFromFeedback`, `unbiased_of_weighted`, `limsup_of_unbiased`,
`limsup_excess_div`, `N_sub_t_le`, `t_le_τ`, `T_le_τ`, `rate_le_excess`,
`excess_le_excess`, `theorem3a`, `theorem3a_rate`, `theorem3b`; `Exploration.ε`,
`N_sub_t_le_expl`, `excess_pt`, `rate_le_expl`, `excess_le_expl`, `corollary_a`,
`corollary_b`, `corollary_limit`; `Witness.scoring`, `theorem1_instance`, `Act`, `hist`,
`decision`, `respects`, `v_violating`, `v_risky`, `U_respecting`, `κ_risky`,
`theorem2a_package`, `theorem2b_package`, `theorem2c_package`, `theorem2_instance`,
`theorem2b_instance`, `sequential`, `sequential_maximizes`, `sequential_excess`,
`sequential_unbiased`, `theorem3_instance`, `exploration`, `exploration_E`,
`exploration_explores`, `exploration_unbiased`, `exploration_ε_le`,
`exploration_ε_limsup`, `corollary_instance`. Claim identifiers `deconfusing.theorem1`,
`theorem2a`, `theorem2b`, `theorem2b-strict`, `theorem2c`, `theorem2c-tau`, `theorem3a`,
`theorem3a-rate`, `theorem3b`, `corollary-a`, `corollary-b`, `corollary-limit`. Wiki page
`Deconfusing-Corrigibility-Companion`.

## Filed

`PRIORITIES.md` item 111: Unbiasedness From Feedback for the score sequence from
`LogicalInduction` — Theorem 4.8.16 at the uniform weighting, with the
feedback-enters-the-deductive-process and latency assumptions as explicit hypotheses.

## Outstanding maintainer actions

1. Decide whether the `deconfusing.*` registrations stay against item 107 or move to an
   item of their own; if the latter, file it and change `answers_item` on the twelve
   entries in `projects/deference/CLAIMS.md`.
2. Link the companion page from where the post's readers will arrive: the post itself, and
   — outside this round's write scope — `wiki/_Sidebar.md` under *Deference*, and
   `wiki/Corrigibility.md` if wanted.

## Model attribution

Prompt author: the maintainer. Executor: Claude Fable 5.1 (Anthropic). Date: 2026-10-17.
