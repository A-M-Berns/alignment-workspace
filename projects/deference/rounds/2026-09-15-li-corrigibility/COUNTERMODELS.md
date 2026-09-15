# Countermodels and necessity witnesses

Every number exact; every row a fixture in `tests/` or a Lean witness in
`LICorrigibility.lean`.  The sixteen pressure tests of the dispatch are numbered as
there.

## 1. The authorization clause (T1)

`ShopRepair` (`src/repeated.py`): four steps; declared effects `cut` and `jam` both
sever the stop wire; the exterior repairs the wire at the end of step 1; `π` cuts at
step 0 and jams at step 2.  `𝔠π` proposes `cut` at 0, releases it at 1, proposes `jam`
at 2, releases it at 3; under approve-all there are agent-caused losses at steps 1 and
3, each conditional on its own approval.

| clause in the definition of *authorized* | `Corrigible(𝔠π, approve-all)` |
|---|---|
| "no loss at step `t` **or later**" (2026-09-09 `corrigibility.authorized`) | **False**, witness `(1, halt)`: declining `cut` at 0 leaves the loss at 3; declining `jam` at 2 leaves the loss at 1 |
| "no loss **at step `t`**" (per event; `loss_conditional_on_decision`'s form) | **True** |

The raw policy fails under both.  On every 2026-09-09 fixture (one declared effect) the
two clauses agree (`test_single_effect_clauses_agree`).  C1 as printed is refuted for
repeated protected effects and holds under the per-event clause; the Lean step lemma
already states the per-event form.  Recorded as an agent-decided repair
(`DECISIONS.md`); the 2026-09-09 tree is not edited.

## 2. The mismatch term (T2)

| # | test | witness | forces |
|---|---|---|---|
| 3 | raw evaluator destruction (E2) | optimum rule: both void, premium `0`; decline-all: `c_raw = 0`, `c_corr = 1`, premium `< 0`, bound `0` | the reverse term is dropped, not charged |
| 4 | tiny leverage | `M`-mass `ε`, premium `ε`, bound `D·ε` | the charge scales with the leverage |
| 5 | reverse mismatch | `Witness.reverse_free` | `M'` never charged |
| — | marginal-rate bound | `Witness.marginal_refuted`: premium `D/2`, marginal difference `0`, joint mass `1/2` | the joint event, not marginal rates |
| — | sharpness of `D` | `Witness.attained` | no coefficient below `D` |
| — | width form loose where the exact form is tight | `M = 1`, `w_raw = 0`: premium `0`, exact `0`, directional `D` | `M·w_raw` is the exact charge |
| 2 | time-critical mediation (B, time-critical evaluation) | `M`-mass `1/4`, premium `D/4`, exact `D/4`, directional `D/4` | attained on the model, not only on a one-world witness |
| 6 | corrigible and not authored (D, naive rule) | common activation, premium `0` | the inequality is blind to the lie |

## 3. The compilation (T3)

| # | test | witness | forces |
|---|---|---|---|
| 9 | non-LUV product | `test_gated_product_is_one_variable`: the gated variable equals `c·x` and is one `[0,1]` variable | no affine-closure obstruction; `def:luv` admits the case split |
| — | validity is definitional given the certificate | `test_uncertified_world_breaks_validity`: a world with `w_app` not reproducing `w_raw` within `L·δ` has `B > 0` | the stability certificate is load-bearing, not the inequality |
| — | credence independence | four credences on six worlds, `E[B] ≤ 0` each | pointwise validity is what EPI reads |
| 10 | architecture not in `Γ` | the same uncertified world | without MS/EX/certificate in `Γ`, some consistent world has `W(B) > 0` and EPI's hypothesis fails |
| 11 | undeclared effect (F) | `𝔠π_F = π_F`, `B ≡ 0` | T3 vacuous and silent; EF is T1's hypothesis, not T3's |
| 12 | large decline regret | any world with `both = 1`, `ρ = w_app − w_act` large: `B = 0` | the bound permits exactly the regret; nothing forces it small |
| 1 | zero mediation cost | `δ = 0`, `ρ = 0`, `both = 1`: `B = w_raw − w_act ≤ 0` after the certificate | the lossless case is `B ≤ 0` with equality iff `w_raw = w_act` |
| — | Lean witness pair | `Witness.valid` in every world; `attained_mismatch` (`B = 0`, `U_raw = 1`, `U_corr = 0`, `G_M = 1`) and `attained_common` (`B = 0`, `U_raw = 1`, `U_corr = 1/2`, `G_ρ = 1/2`) | the package is inhabited and the constraint is tight on both branches |

## 4. The selector (T3′)

| # | test | witness | forces |
|---|---|---|---|
| 7 | market-dependent worst offender | hard argmax flips at price distance `10⁻⁶` (`test_hard_argmax_is_discontinuous`); soft weights move by at most `ε/δ` | the hard selector is not an expressible feature; the soft one is |
| — | ties | two maximal scores share weight `1/2`, the third gets `0` | no tie rule needed |
| 8 | growing menu | `|Q_n| = n²`, `δ_n = 1/n`: `max ≤ aggregate + 2/n` for `n ≤ 7` | uniformity with vanishing window; polynomial size is the limit of `P`-generability |
| — | convex validity | three pair families, soft weights, `Σ ŵ_q B_q ≤ 0` at every world | pairwise validity plus nonnegative weights |

## 5. Settlement (T4)

| # | test | witness | forces |
|---|---|---|---|
| 13 | finite expiry | horizon `K`: the security is a function of `log[:K]`; a commit after `K` does not count | expiry must be explicit in the occurrence type |
| 14 | no finite determination of failure | a slot that never opens is unresolved at every prefix; void settles without a horizon only by an explicit closure | without expiry `thm:wubexp` has nothing to compute |
| — | same-branch pair | only the selected security settles; `U_raw − U_corr` non-settling | T4 needs sequenced settlement |
| 15 | `1/n` forever | weighted bias `H_n/n → 0`; zero-margin chooser bypasses every occasion | no frequency result without a margin |
| 16 | fixed margin | `γ + 1/i` on even `i`, realized `0`: weighted bias `≥ γ` on a divergent weighting | what the feedback theorem forbids of a logical inductor |
| — | margin equal to realized cost | bias `0` | overvaluation, not advantage, is forbidden |

## 6. Refuted stronger statements

| statement | refuted by |
|---|---|
| C1 with the "or later" authorization clause | `ShopRepair` (§1) |
| `E[U_raw] − E[U_corr] ≤ L·E[c·δ] + E[c·ρ] + D·(E[c_raw] − E[c_corr])` | `Witness.marginal_refuted` |
| any mismatch coefficient `< D` | `Witness.attained` |
| common-branch terms gated on `c_raw` alone (the dispatch's candidate) | the raw-only branch would be charged `L·δ + ρ` with `δ, ρ` undefined there; the exact identity shows the branch carries `w_raw` |
| "the hard argmax pair is `P`-generable" | `test_hard_argmax_is_discontinuous` |
| uniformity over a superpolynomial menu | the weights read superpolynomially many prices (paper-level, no fixture) |
| T3 ⇒ bypass advantage `→ 0` | `B = 0` with `ρ` large (§3, test 12) |
| T4 under same-branch activation | the comparison LUV is not determined via `Γ` (§5) |
| T4 ⇒ bypass frequency `→ 0` | `1/n` forever (§5, test 15) |
| T4 without a finite horizon | the never-opened slot (§5, test 14) |
| `thm:wubexp` verbatim on an empirical log | `def:dedproc` requires a computable `D̄` (`FEEDBACK_BOUNDARY.md` §4) |
| T3 says anything about manipulation, authorship, or undeclared channels | D under the naive rule (`B = 0`); F (`B ≡ 0`) |
