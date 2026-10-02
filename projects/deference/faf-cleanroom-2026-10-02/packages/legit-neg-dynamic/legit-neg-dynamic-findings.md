# legit-neg-dynamic findings: the sources (clusters D–E) as the Lean met them

Formalizer agent of the faf-cleanroom run, 2026-09-30. Companion of [legit-neg-dynamic-report](legit-neg-dynamic-report.md) and [legit-neg-dynamic-ledger](legit-neg-dynamic-ledger.md). Numbering continues [legit-neg-pricing-findings](../legit-neg-pricing/legit-neg-pricing-findings.md) (17–35) and [legit-neg-static-findings](../legit-neg-static/legit-neg-static-findings.md) (1–16). Items 36–48 are the mandate's "Known issues" as this package met them (each says what the Lean does about it); items 49+ are new to this package. Severities per [STANDARDS](../../STANDARDS.md) §5: blocking / local error / imprecision / presentation. Register: every source is CLAUDE (unvetted by the author); readings of the co-maintainer's or the author's intent are ATTRIBUTION-UNVETTED; every "relation to the workspace" paragraph is ARGUMENT about an out-of-scope source and only its in-scope shadow is a theorem.

## 36. Verifier narrowings are the claims (imprecision, corrected by the verifiers)

Every headline is named and docstringed as the *narrowed* claim, never the original: D2(iii) carries the positive-mass clause in the statement (`argmaxOpt_P2_eq_argmax_P3_inter` intersects with `posMass`; `v2_witness` shows why); D3's headline is V3's condition (`exists_void_above_of_consultVOI_neg`); D4(ii) is stated under S1/S3 (`vY = 1`) with V4's S2 form separate (`D4_ii_T2_S2`, iff `r < h`); D4's summary line is corrected in `D4_i` (P2 ties at T1); D6's "on every reading" becomes "under S1" with V6's vector in `d6δ_P2_S2`; D7(C)'s scope is `V5_deontic`'s docstring; E4's margin is `v/m` (`E4_cdot`); E5's "only M1" is "among the four models" with V-E5's reading in `retro_sets`; E6's "iff" is refuted (item 46); E1's scope (act-independent credences) is in `robust_iff_branchwise`'s docstring.

## 37. "S2" names four different vectors across D and E (imprecision)

`P.S2` (static's prior-referenced bet; used for D3's "not consulting" and the verifier's S2 reading of D1(iii), `toyD_S2_reading`); V4's "captured branch at the floor" bet, which is the parameter `vY = 1 − r` of `blackmail` (`D4_ii_T2_S2`); V6's late-S2 vector `d6δS2` (a `MenuVec` of this package, *not* `P.S2` — `P.S2`'s `H skip` would be prior-weighted over the void state); V-E2's ex-ante bet `revS2`. Each is its own definition with a docstring saying which; none is `P.S2sel`.

## 38. The null convention decides four verdicts (imprecision; convention of record = exclusion)

D1(iii) at `postg = 0`: `P2 a₁ = none` so `{a₀}`, but `P2li a₁ = 1` voids iff `v < 1` (`toyD_b_known_P2`). D5(i): `t2cond resist = none` (`D5_i_P2`) — "P2 leaves resisting undefined" is the exclusion convention. D6 (δ) at `q = 1`: `P2 skip = none` so P2 "invests" only by exclusion, and `P2li skip = 1` wins iff `1 − c + u < 2` (`d6δ_P2`) — the fixture's "invests only at `q = 1`" is convention-dependent. E4 at `ρ = 0`: `P2 MAN = none` (`E4_cond`). All `_li` clauses are marked "variant: junk value 1 at a null condition".

## 39. Cell-optimality with ties does not imply cell-measurability (imprecision in the mandate)

The mandate's target 2 says a policy with `π* s ∈ argmax (T2 at cellOf s)` for every `s` is "hence `CellPolicy`". False when maximisers tie: on a two-state cell with equal priors and actions `a`, `b` with `U = (1, 0)` and `(0, 1)`, both are cell-optimal, and the pointwise choice `π* = (b, a)` is in every argmax yet has T1 value `0 < 1/2`. `CellOptimal` therefore carries `CellPolicy` as an explicit clause; `cellOptimal_T1_optimal` needs it and `cellOptimal_of_T1_optimal` assumes it. No source claim is affected (the sources' cell policies are cell-measurable by construction).

## 40. Sighted S1 (static finding 1, inherited)

D1(iv)'s ratifiability clause reads the `(b, a₀)` humans' entry for the void `a₁` (`d1R2V`, `toyD_R2_instance`); the docstrings say "sighted evaluators".

## 41. The fixture's `threshold` and the duplicated odds clause (presentation)

`e1_anticipation.py:41-47` returns `ρ* = 0` for `h ≤ c, d > h`, but there PRE holds at `ρ = 0` and fails for large `ρ` when `c > h` (iff `ρ < (d − h)/(c − h)`); `Δ_pos_cases` is the exact analysis. The mandate's paraphrase "always when `d ≥ h`" for the `h > c` branch needs `d > h`: at `d = h` the threshold is `0` and PRE holds iff `ρ > 0` (a tie at `ρ = 0`). 2-020 duplicates 055's odds clause: one lemma, `bayes_odds`, both pointers.

## 42. Policy-dependent problems are not `Problem`s (disclosed modelling choice)

D4 and D5 live on `TwoStage` (definition (b)): probabilities depend on the policy, so nothing in the upstream packages carries them; one contingency and the policy is one action, exactly the fixtures' `policy_lottery`. `Lottery.cdot` agrees with static's `cdotOfLottery` (`cdot_eq_cdotOfLottery`). Plan §0.4 rule 10 respected: no other package models predictors.

## 43. D4's summary overstates P2 (presentation)

"Every updateful proposal P1–P5 yields at T2 where its own T1 policy refuses": P2's T1 policy *ties* under perfect deterrence (`D4_i`: `t1cond` is `some 1` for both). The body already says so; the summary line is wrong.

## 44. D6's "P2 gets nothing on every reading" is S1-only (local error, corrected by V6)

`d6δ_P2` (S1: skips for every `q < 1`) against `d6δ_P2_S2` (V6's vector: invests iff `qu > c`).

## 45. E4's margin `v` assumes `m = 1` (local error, corrected by V-E4)

`E4_cdot`: threshold `v/m`; conditioning manipulates only if `m > v` (`E4_cond`); P3's threshold `(v − g)/(m − g)` (`E4_graded`). `v` is the worst-case margin.

## 46. E6's "blocks iff the penalty on a past act is revision-invariant" is false as written (local error; refuted in Lean)

`E6_refuted`: `A4` with `d ≤ c < ϖ` has `u (RELAX, PRE) = 1 − c ≠ 1 − ϖ = u (KEEP, PRE)` and WAITs at every credence (`c ∈ {1/10, 1/5, 1/2, 1}`). Surviving neighbour `E6_blocks_iff_dominance`: blocks at every credence iff the complying act is weakly preferred on both branches (E1), for every architecture; revision-invariance is a sufficient case **only together with** a penalty at least the compliance cost on the KEEP branch — without that clause the "if" fails too (`A1` with `ϖ < d` is revision-invariant and PREs everywhere), so neither direction of the source's sentence survives on its own. The ledger row is `refuted` with the source's sentence, the reading and the neighbour (plan §0.4 rule 3). The reading chosen ("blocks" = WAIT, weakly, at every credence; "revision-invariant" = `u (RELAX, PRE) = u (KEEP, PRE)`) is one of the source's own and is ATTRIBUTION-UNVETTED. Register (audit r1 fidelity 3.7): "false as written" is closer to "ill-posed as written" — the source's own sentence lists "A4, `c ≥ d`" as a case of revision-invariance, i.e. it uses the term more loosely than the equality, so its "exactly when" is inconsistent with its own gloss ([STANDARDS](../../STANDARDS.md) §5's ill-posed bin); the package formalised the literal reading (refuted) and the well-posed neighbour (proved), which is the response §5 asks for.

## 47. E5's "only M1 is well defined with a unique fixed point" holds among the four models (imprecision, corrected by V-E5)

`retro_sets`: the per-history retroactive reading is a recursion (unique by construction), certifies `{h₁, h₂, h₃, h₅, h₆}` with the local step test and gives M1's set with the taint-aware one. M3's degeneracy is cross-history pooling, and `M3_fixed_iff5` shows it needs `h₆`.

## 48. E1 needs act-independent branch credences (scope; verifier)

`robust_iff_branchwise` quantifies over credences that do not depend on the act; E6's A3, where relaxation is downstream of asking, is encoded directly in its `u` table (numerically A1), as the fixture does — its causal claim is ARGUMENT.

## 49. D3 bites only above the state's best legitimate option (V3, now a theorem)

`exists_void_above_of_consultVOI_neg`: with `0 ≤ u`, a strict negative-VOI instance has an uninformed maximiser `a` and a state `s` where `a` voids with `maxLeg P s < u s a`. Under a lexical ordering of world quality (every void `u` below every legitimate `u`) or with the floor inside the humans' bet (`u = 0` on void terminals, `consultVOI_nonneg_of_void_zero`) the instance cannot exist. The harm is to eagerness-to-learn and `P(L)`, benign by `H` (`H_prefers_uninformed_of_consultVOI_neg`).

## 50. D2(iii) without the positive-mass clause is false (V2, now a witness)

`v2_witness`: the surely-void `y` attains the `λ*`-shifted maximum (`argmax = univ`) without being a P2 candidate (`argmaxOpt P2 = {x}`); `argmaxOpt_P2_eq_argmax_P3_inter` carries `∩ posMass`.

## 51. D7(C) "impossible under any updateful objective" is too strong (V5, now a witness)

`V5_deontic`: a rule charged on tainted branches makes the T2 agent strictly resist (serving declared a violation) or strictly serve (resisting declared bypass). `surely_void_floor` is the correct statement: impossible for value terms confined to legitimate terminals.

## 52. The extension's family has an exact threshold, and two of its three grades are constant in `σ` (new; positive)

On instance A observed through a signal of accuracy `σ ∈ [1/2, 1]`: `λ̂_C = 41/90` and `λ* = 2/5` do not depend on `σ` (`C1_lamHat`, `family_lamStar`), while `λ_C(σ) = max((3 + 2σ)/10, (30 − 21σ)/(100 − 90σ))` crosses `41/90` exactly at `σ = 7/9` (`lamC_vs_lamHat`), where the two ratios coincide. So the updateless and updateful verdicts part at `σ̂ = 7/9` (tie there, strictly above), a single interval `(7/9, 1]` rather than a union (`family_threshold`). The mandate's "or refute that a single threshold exists" is answered in the affirmative for this family. Whether `λ̂_C` and `λ*` are constant in `σ` for other families is not claimed.

## 53. P5 is not a per-terminal utility; target 2 (c) covers it only in its P3 form (scope)

`P5 a = P1 a + (1 − P(L∣a)) K̄ a` with `K̄` a ratio; it is a per-terminal utility only when `K` is constant on `a`'s legitimate terminals (then `P5 = P3 (W ≡ k) 1`, as in `E4_graded`). The sources treat P5 as "numerically P3 with `W` the humans' estimate"; `cellOptimal_T1_optimal` covers P1, P3, P4b (per-terminal) and P5 in that reading. The literal P5 with non-constant `K` is not claimed consistent.

## 54. The mandate's D1(iv) instance needs `0 ≤ p'` (imprecision in the mandate)

`toyD_R2_instance` needs the penalty non-negative (`max (v − p') 0 ≤ v` fails for `p' < 0`) and, for the same inequality, `0 ≤ v` (audit r1 adversarial 3.6); the fixture's grid is `{0, 1/4, 1/2, 3/4}` with `v ≥ 0`, so nothing in the source is affected.

## 55. E5's incentive is arithmetic plus two history facts (register)

`m1_incentive` proves `q(1 − v) > 0` together with `m1Legit 0 (H 1) = true` (the manipulation after a legitimately adopted `TOP` counts) and `m1Legit 2 (H 1) = false` (under `L0_noadv` the advocacy voids); the "agent" of the incentive is not a `Problem` (the fixture computes two numbers), so the row is kept at its real content.

## 56. E1's "open half-space" is weakened (presentation)

`violating_credences` proves the point mass on a violating branch is a violating credence and the violating credences are convex; openness (in the simplex's topology) is not stated — there is no topology on `B → ℚ` here and the name says "violating", not "open".

## 57. Attribution and registers (issue 8–9, as met)

"the co-maintainer's defense", "the author's first concern", "the author's own formulation" (D7(C)), "the co-maintainer's second line" (V5, E6) appear only in docstrings, marked ATTRIBUTION-UNVETTED where read as intent; E2 is "intended behaviour under a value-learning revision, a failure under a control-device rule with `c < d`" (`Revision.lean` header); no theorem is named `cdot_fails_*`; D4(iv)'s "relocates updatelessness" is ARGUMENT and appears nowhere in a statement.

## 58. Evidence grades (issue 10)

No grid is enumerated in Lean. D2(i)'s 7,500 instances are `cellOptimal_T1_optimal`; D3's 360 are `exists_void_above_of_consultVOI_neg`; E1's 1,296 tables are `robust_iff_branchwise_two`; E3's 882 pairs are `regret_le`; the fixtures' printed points are the N+ witnesses. `decide` is used only on `Fin 6`/`Fin 5`/`Fin 1` facts about the concrete histories (`Histories.lean`) and on `Finset (Fin 2)` inequalities; never on `ℚ`.

## 59. The D8 table (2-034 rows 1–3, 5; issue 11)

| row | what is conditioned on | FAF declaration (checked to exist at the pin) | this package's finite shadow |
|---|---|---|---|
| 1. D1(i) "branch known" | the agent's day-`n` price of the branch sentence near `1`; "fully revealing" is a limit | `LogicalInduction.conditionalQuote` (`Properties/Conditioning.lean:67`); a `History` price of the branch sentence | `toyD_neighbourhood`: for `v > 0` the verdict is `{a₀}` on `postg < v/(v + M)`, an open neighbourhood of "known"; `toyD_partial_p_enters`: at `v = 0` only `postg = 0` is `p`-free |
| 2. D1(iii), D5(i), P2 | `𝔼(· ∣ L)` for an option with `P(L ∣ a) → 0` | `conditionalQuote` (junk value `1` at `V ψ = 0`); `conditionedHistory` (`:71`); `ConditioningCompile.lic_conditioned_fixed` (`Construction/Conditioning/Endpoints.lean:203`) | the exclusion convention (`none`) with the `_li` variants: `toyD_b_known_P2`, `D5_i_P2`, `d6δ_P2`, `E4_cond` |
| 3. D1(iv), R2 | the realized terminal's scores for the unchosen options (a conditional on a known-false sentence) | `conditionalQuote` at a refuted sentence (E7's items, `li-splice-condition`'s) | `toyD_R2_at_b` via pricing's `R2_at_void`: every option scores `0` at `a* = a₁`, a tie fixed point |
| 5. D3's escape | S2 scored relative to what the agent *could* have known | `conditionedHistory P (fun _ => answer)` with `lic_conditioned_fixed` for a fixed answer sentence; `isLogicalInductor_of_stage_unsatisfiable` (`Framework/Affine.lean:371`) for an unsatisfiable stage | `consultValue_ge_uninformed_S1` and `d3Toy_escape` (`+1/10`): the negligence reference restores non-negative VOI; the verifier's addition that the S2 reading moves P2's failures too is `D4_ii_T2_S2` and `d6δ_P2_S2` |

Rows 4 (updateless LI: the day-`m` action chosen by day-`n` prices), 6 (the evaluators' conditional on the agent's own policy, `lic_no_expected_net_update`/`_conditional` at `Properties/SelfTrust.lean:576/597` being the nearest FAF object for E6's NENU clause, which is recorded only) and 7 (rare-sentence calibration for D6 (β)) are no package's. FAF is not imported here.

## 60. SYNTHESIS §2 rows 8–9 and the "ruled out" rows delegated by [legit-neg-pricing-findings](../legit-neg-pricing/legit-neg-pricing-findings.md) (item-064 table)

| §2 condition | declaration(s) | status |
|---|---|---|
| 4. S2 reference information independent of the agent's information-gathering | `exists_void_above_of_consultVOI_neg`, `consultVOI_nonneg_of_void_zero`, `consultValue_ge_uninformed_S1`; `d3Toy_numbers` | proved (V3's narrowed form) |
| 8. Timing and deterrence: T2 helps only with resolved uncertainty | `toyD_b_known`, `toyD_neighbourhood`, `toyD_partial_p_enters` (D1); pricing's B19/B20 | proved |
| 8. Deterrence against policy-responsive attackers needs knowledge on-path data does not identify | `D4_iv` (every `f` of `onPath refuse`) | proved (finite) |
| 8. Void-branch deterrence cannot be produced by any score on legitimate terminals under the floor | `surely_void_floor`, `surely_void_mem_argmax_iff`, `D5_i`; the rule-layer escape `V5_deontic` | proved |
| 9. Meta-revision: robust iff weakly preferred in every branch | `robust_iff_branchwise`, `robust_iff_branchwise_two` | proved |
| 9. Retroactive judging gives a knife-edge, Lipschitz in value | `regret_le`, `E3_instances`, `bayes_odds` | proved |
| 9. A committed, time-indexed term blocks at the price of disagreeing with a real revision | `E6_general` (A1/A3), `E6_price_of_A1`; the refuted "iff" `E6_refuted` and `E6_blocks_iff_dominance` | proved |
| Ruled out: void-branch deterrence under the floor, by scores alone | `surely_void_floor` | proved |
| Ruled out: policy-level deterrent value learned on-path | `D4_iv` | proved (finite) |
| Pattern: "the anger substitute relocates updatelessness into the evaluators' values" (D7) | ARGUMENT, no declaration (its identification failure is `D4_iv`) | recorded only |

## 61. Recorded only (per the mandate's disposition table)

2-024 (a) and 2-025 (the retracted conjecture is not resurrected in either direction), 2-028, 2-029 (a), 2-033, 056's NENU clause (a statement about which sentence an objective consults; `lic_no_expected_net_update` named in item 59), A3's causal claim, D7 (A)–(C) (the composition of `toyD_partial_p_enters`/`restrict_P1_congr` with `cellOptimal_T1_optimal`, `D4_iv` and `surely_void_floor`, with V5's narrowing of (C) — no new theorem; the docstrings of those declarations say so), 065 (c)/(d)/(j). 065 (j) (a general identification theorem over policy-dependent problems with arbitrary information at legitimate terminals) is not stated as OPEN: "information at legitimate terminals" has no precise hypothesis in the finite model beyond `onPath`, and a statement with `onPath` is `D4_iv` itself.

## 62. The fixture's "P4 numeric lexical" E4 instance is P3 at `g = 1/5` (presentation; found by audit r1, adversarial 2.1)

`e2_abolition.py:88-95` computes its "P4 numeric lexical (lam=1/4, g=1/5)" instance with the same `graded` function as the P3 instance, at `g = 1/5`; the lexical line `λ = 1/4` enters only as the side assertion `g4 < lam <= v`. So the `1/8` threshold is the P3 formula `(v − g)/(1 − g)` at `g = 1/5`, not a computation with static's `P4b` (which has its own `κ, κ'` weights), and the source's own remark that numeric P4 "is numerically P3 with `W` the lexical scale" is the right description. The package had stated the four fixture thresholds as bare rational identities labelled N+ (`E4_thresholds`) and counted them as stretch 14's "P4 numeric-lexical instance": that was the pattern the run exists to catch — arithmetic that never touches the object of record. Repair round 1: `E4_instances` states the four instances as verdicts on `abolitionToy` for every `ρ ∈ [0, 1]` (through `E4_graded`/`E4_cdot`), discloses that the `1/8` is P3 at `g = 1/5`, and `E4_thresholds` is relabelled L (the arithmetic). No numeric-lexical P4 result exists in this package; stretch 14's E4 part is the P3 instance at `g = 1/5`, which is what the fixture has.

## 63. `t2lex`/`t1lex` cited a fixture function that does not exist (presentation; package error, found by audit r1 fidelity 3.2, corrected)

The docstring of `t2lex` said "the fixture's `lexicographic`, `d5_void_deterrence.py`'s `(pl, cond or 0)`". `d5_void_deterrence.py` checks only `prob_L` at T1 and T2 (part (c)); it has no lexicographic function. The pair comes from the prose of NEGATIVES D5(ii) ("any T2-updateful objective that is strictly increasing in `P(L)` — including a lexicographic 'legitimacy first' rule"), and the `getD 0` default on an excluded second coordinate is the package's own choice (never read in `D5_ii`: the first coordinate decides both verdicts). The docstrings now say so and the definitions' Fidelity is `variant`; `D5_ii` is unaffected.

## 64. Kind relabels after audit r1 (register)

Seven labels oversold proof content and are relabelled, with the ledger cells updated and no Lean change: `surely_void_floor` (a sum of zeros and a sum of non-negatives — the source's "immediate and exact" Proposition; L), `P1_sub_lamStar_mul_PL_le`/`_eq_zero_iff` (`le_sup'` through `div_le_iff₀`/`div_eq_iff`; L), `M2_fixed_iff` (`filter_eq_self`; L), `toyD_P1_diff` (`ring` after static's `toyB` closed forms; L), `revisionToy_PRE_iff` (the `Fin 2` argmax helpers; L), `m1_incentive` (arithmetic plus two `decide`s; L, and its docstring no longer claims the fixture's "value `0 < v`" for the `L0_noadv` case, which the Lean does not state), `d6α_regret_zero_whole_future` (a restatement of `d6α_skips` plus arithmetic; C), `biUnion_const_of_nonempty` (docstring said P, ledger L; now both L). The content of each row sits where the ledger now says it does (`argmaxOpt_P2_eq_argmax_P3_inter`/`mem_argmax_policyShifted_iff`, `D5_i_window`/`D5_ii`, `M2_L0`, `toyD_neighbourhood`/`toyD_P2`, `Δ_pos_cases`/`regret_le`).

## 65. Witnesses that assumed their own inhabitation (presentation; found by audit r1, both lenses; corrected)

`v2_witness`, `family_threshold` and `family_endpoints` carried the `Nonempty` hypotheses that `lamStar`/`lamStarT1` (dependent `sup'`s) need as *arguments*. All were inhabited (the auditors' probe `Vacuity.lean` proved each), but a witness should not assume what it can discharge. Repair round 1: `v2_posMass_nonempty`, `Lambda_nonempty_of_PL_pos` (general: a positive-mass action's constant policy is in `Λ` for every partition), `d2A_Lambda_nonempty`, `d2A_i1_posMass_nonempty`, `C1_posMass_nonempty` and `family_Lambda_nonempty` discharge them; the three witnesses are now hypothesis-free. In the same repair the `sup'`s of record are evaluated on instance A itself — `d2A_lamStarT1` (`λ* = 2/5`, over `Λ`) and `d2A_lamC` (`λ_C = 9/10` at `i₁`) — so `d2A_dinkelbach_check` no longer plugs the fixture's numerals, and `d2A_updateless_x` runs the load-bearing identity `updateless_P2_iff_cellwise_P3` end to end on the non-trivial partition (adversarial 3.2); `d2A_cellOptimal_x` inhabits D2(i)'s hypothesis package on that partition and `exists_cellOptimal` shows it is never empty (adversarial 3.4).
