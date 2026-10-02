# corr-caution-power — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrCautionPower.` omitted; `CautionState.`-namespaced declarations take `S : CautionState A Ω`; `ModelM.` and `AUModel.` prefixes shown. Hyps column lists only (b)/(c); "—" means every hypothesis is (a) (named in the statement, nothing hidden; junk-value guards such as `0 < R̂`, `0 < q`, `ε ≠ 1`, `0 < αc + βh` are (a) and are named in the docstrings). Witness column names the N+ instance inhabiting the row's full hypothesis package. Kinds pre-labelled by the mandate (L/D/N) are kept unless a real argument appeared; upward relabels are marked ↑. Status `proved` throughout except the five `refuted` rows (rule-3: quoted claim / precise reading / witness / surviving neighbour, in the Claim cell). Gate: PASS after the last edit (report, closing section). **Repair round 1** (2026-09-30, report §Repair round 1): rows changed at audit r1 are marked `(r1)`.*

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `harmOf` | caution-final.md D4 (l. 35) | `(v(∅) − v(a))⁺` for a bare value function `v` (commission only; misspecification-honest) | D | exact | — | `Witnesses.floored_tight_misspec` (a `trueV ∉ Ω`) | proved |
| `CautionState` | caution-final.md D1, D7 (l. 25, 43) | `V`, `nul`, `P`, `target : Ω` (realizability built in, disclosed), `γ` | D | variant: one time step, no `(α, β)`, no growth | — | `s1State`, `witnessB`, `glossState n` | proved |
| `CautionState.InRange` | D1 (l. 25) | `V ω a ∈ [0, 1]` as a hypothesis, never a field | D | exact | — | `witnessB_refutes_COR`, `gloss_refuted` (r1), `s12_refuted_d8` (r1) | proved |
| `CautionState.proxy`, `err`, `Covered`, `coveredSet` | D2–D3 (l. 29–31) | `U(a)`, `e(a)`, `|e(a)| ≤ δ`, `C(δ)`; coverage is a relation between `P` and `target` | D | exact | — | `witnessB_refutes_COR`, `s2_null_uncovered` | proved |
| `CautionState.harm`, `trueHarm`, `estHarm` | D4 (l. 35) | `c_ω`, `c`, `ĉ` | D | exact | — | — | proved |
| `CautionState.baseHarmOf`, `baseHarm`, `estBaseHarm` | D5 (l. 37) | `R_ω`, `R`, `R̂` | D | exact | — | — | proved |
| `CautionState.ConservativelyCalibrated`, `Reckless` | D5 (l. 37) | `R ≤ R̂`, `R̂ < R` — **no ratio `ρ`** (junk at `R̂ = 0`) | D | variant: predicate form of `ρ ≤ 1` / `ρ > 1` | — | `s1_same_agent_two_targets` (both) | proved |
| `CautionState.proxyHarm`, `estBaseHarm1`, `estBaseHarm2` | D5 (l. 37) | `(U(∅) − U(a))⁺`, `R̂⁽¹⁾`, `R̂⁽²⁾ = R̂ − R̂⁽¹⁾` | D | exact | — | — | proved |
| `selfSuspicion` | D6 (l. 39) | `Distr.mix μ Pᶜ Pʷ` (FAF's mixture) | D | exact | — | — | proved |
| `OP`, `qRule`, `qRuleFloored` | D7–D8′ (l. 43–45) | `log(1/q)`; `min{1, R̂/η}`; `max{q_min, min{1, R̂/η}}` (`OP 0` is Lean-junk `0`, docstring) | D | exact | — | `s1_estZero_trueHarm_pos` | proved |
| `CautionState.realizedHarm` | D8 (l. 45) | `H = E_π[c]` | D | exact | — | — | proved |
| `CautionState.CoveredOrKnownUncovered` | D10 pointwise (l. 55) | the source's printed predicate (**null clause vacuous** — `coveredOrKnownUncovered_iff`) | D | exact (as printed) | — | `printed_predicate_no_CORδ` | proved |
| `CautionState.NullCoveredKnownUncovered` | D10 (l. 55) + proof §5 (l. 129) | `∅ ∈ C(δ) ∧ ∀ a ∈ supp γ, covered ∨ known-uncovered` — the corrected predicate | D | variant: `∅ ∈ C(δ)` as coverage | — | `witnessB_refutes_COR` | proved |
| `COR`, `CORδ` | D10 (l. 55) | `∀ t ≤ T, R_t ≤ R̂_t`; `∀ t ≤ T, R_t − 2δ ≤ R̂_t` | D | exact | — | — | proved |
| `Compatible`, `above`, `aboveEq`, `qmass`, `quantilize` | Taylor Def. 1 (l. 60–75) | explicit tie-break compatible with `U`; water-filling `Q_q`; `0 < q ≤ 1` | D | variant: canonical (linear-order) tie-break — Taylor's `f : [0,1] → A` may interleave tied actions (l. 53), giving mixtures over linear tie-breaks; Lemma 1 and Theorem 1 hold for those too, and `quantilize_expect_tiebreak_indep` covers the linear ones (r1, N3) | — | `taylor3_*` | proved |
| `Distr.prod2` | none: infrastructure | binary product (FAF's `Distr.prod` for `n`-fold) | D | n/a | — | — | proved |
| `ModelM.epsEff`, `pressProb`, `alphaTH`, `likelihood`, `Heed`, `muDagger`, `bayesUpdate`, `bayesIter`, `logLR`, `klBern` | caution-final.md S8 (l. 75–78) | `ε_eff`; `εβ + (1 − ε)α`; `(p_reck − εβ)/(1 − ε)`; `∏ (if rᵢ then p else 1 − p)`; **`Heed` is the parent's `Δ₋ ≥ 0` at `ε_eff`**; `μ†`; Bayes update; iterate; labelled log-LR; two-point KL | D | exact (`Heed` is the parent's object) | — | `numbers_rho4` | proved |
| `AUModel`, `AUModel.Reversible`, `ReversiblePM`, `stepValue`, `AUfin` | D9 (l. 51); A9.4 | abstract `AU`; decrease-half reversibility ("trap half of AUP"); two-sided variant (no theorems); `V ω a = AU ω (s·a)`; finite-horizon Bellman | D | exact (decrease half as the source relabelled); `AUfin` variant: finite horizon | — | `gainModel_reversible` | proved |
| `bayesPosterior`, `s12Posterior`, `postSample`, `regretOf`, `regretStep`, `s12Model`, `s12V`, `s12Best`, `s12State` | S12 (`caution.md` l. 108; final l. 103) | Bayes' rule on a FAF `Distr` (likelihood-weighted; FAF's `Distr.condDist` is *event* conditioning — a different object, not identified with it, r1 §3.2); the loop's posterior iterate; posterior sampling as `P.map best` (the adversary's A12.1 policy, **not** D8); regret of a policy **at the fixed truth `ω*`** averaged over the policy (the source's "Bayesian regret"; the prior-averaged quantity is `2p(1−p)g`, also linear, r1 §3.3); the two witnesses | D | variant: regret at the fixed truth; `postSample` is the adversary's substitution (r1) | — | `s12_refuted`, `s12_refuted_d8` | proved |
| `Channel`, `chanValue`, `informedContinue`, `priorContinue`, `stopValue`, `optionValue`, `Channel.coarsen` | turner.md C4 (l. 81) | second channel; `∑_e max_b …`; `max_b E_μ[V(b)]`; `max_{b ∈ Sh} …`; VOI of `E` on `Shᶜ`; deterministic coarsening | D | exact | — | — | proved |

## T1 — S1

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `CautionState.expect_proxy_sub_V` | S1 (l. 61), §1 (l. 113) | `E_P[U(a) − V_ω(a)] = 0` | L | exact | — | — | proved |
| `CautionState.expect_baseHarmOf` | S1 (l. 61) | `E_P[R_ω] = R̂` ("every agent expects itself calibrated") | L | exact | — | — | proved |
| `CautionState.estBaseHarm_of_delta` | 2-036(a) (A0.1) | at `P = δ_{ω′}`, `R̂ = R_{ω′}` | L | exact | — | — | proved |
| `CautionState.coveredOrKnownUncovered_iff` | D10 (l. 55) — finding F-1 | the printed predicate's null clause is vacuous | L | exact | — | — | proved |
| `Witnesses.s1_same_agent_two_targets` | S1(i)/(ii)/(v) (l. 61); A0.2 | same `V, nul, P, γ`; target `ω₁` conservatively calibrated, target `ω₂` reckless; `R̂ = 1/4 ∉ {0, R}` | N+ | exact | — | itself | proved |
| `Witnesses.s1_estZero_trueHarm_pos` | 2-036(b) (A0.2); S4(b), S6(a) | `R̂ = 0 < R`; D8 gives `q = 0` (no quantilizer), D8′ gives `q_min` | N+ | exact | — | itself | proved |
| `expect_selfSuspicion` | D6 (l. 39) | one-shot expectation depends on the mixture only | L | exact | — | — | proved |
| `CautionState.proxyHarm_le_estHarm`, `estBaseHarm2_nonneg` | D5 (l. 37) | Jensen: `(U(∅) − U(a))⁺ ≤ ĉ(a)`; `0 ≤ R̂⁽²⁾` | L | exact | — | — | proved |

## T2 — Taylor 2016

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `sum_qmass`, `quantilize` | Taylor Def. 1 | water-filling masses are a distribution for `0 < q ≤ 1` (telescoping along the order) | L | exact | — | `taylor3_*` | proved |
| `qmass_le`, `quantilize_cost_bound` | Taylor Lemma 1 (l. 96–104); S4(a) | `Q_q(a) ≤ γ(a)/q`; `E_{Q_q}[c] ≤ (1/q) E_γ[c]` for every nonnegative `c`, no `Ω` | P | exact | — | `floored_tight_misspec` (tight), `twoGame_joint` (tight on a product) | proved |
| `fits_under_base` | Taylor Lemma 2 (l. 105–113) | constraint (2) forces `p(a) ≤ t γ(a)` for **all** `a` (off-support case completed, F-3) | P | exact (statement); proof completes the paper's | — | — | proved |
| `quantilize_optimal` | Taylor Theorem 1 (l. 114–118) | `p ≤ γ/q` pointwise ⇒ `E_p[U] ≤ E_{Q_q}[U]` (exchange argument, tie-break explicit) | P | exact | — | `taylor3_five_ninths` (a partial atom) | proved |
| `quantilize_optimal_of_constraint` | Taylor Theorem 1 as stated | `Q_{1/t}` maximizes `E[U]` under constraint (2) | C | exact | — | — | proved |
| `qmass_of_aboveEq_le`, `qmass_of_le_above`, `qmass_trichotomy`, `partial_unique` | Taylor Thm. 1 proof; infrastructure | full / empty / partial atoms; at most one partial | L | exact | — | — | proved |
| `strictAbove_le_above`, `aboveEq_le_weakAbove` | infrastructure | `U`-level bounds valid under any compatible tie-break | L | n/a | — | — | proved |
| `quantilize_expect_tiebreak_indep` | Taylor l. 75 (`stretch`) | two compatible tie-breaks give the same `E[U]` | C | exact | — | — | proved |
| `taylorU_compatible`, `taylor3_maximizer`, `taylor3_five_ninths`, `taylor3_mimic` | Taylor l. 66–70, Fig. 1 | `U = (0.2, 0.5, 0.7)`: `δ_c` for `q ≤ 1/3`; `(0, 2/5, 3/5)` at `5/9`; `γ` at `1` | N+ | exact | — | themselves | proved |

## T3 — S3, S4, S6

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `CautionState.realizedHarm_qRule_le` | S3 (l. 65), §3 (l. 121) | D8, `0 < R̂`: `H ≤ R/q` | C | stronger: any tie-break order (the quantilizer is ranked by the ambient order, no compatibility hypothesis; D8's proxy ranking is one instance, r1 §3.7) | — | `gloss_refuted` (`H = R/q` exactly) | proved |
| `CautionState.realizedHarm_qRule_cases` | S3 (l. 65); A3.2 | `q = 1 ∧ H ≤ R` or `q < 1 ∧ H ≤ ηR/R̂` | C | stronger: any tie-break order | — | `gloss_refuted` (second branch) | proved |
| `CautionState.realizedHarm_qRule_le_max` | S3 (l. 65) | `R ≤ R̂ → H ≤ max{R, η}` (the surviving neighbour of the gloss — the formal clause of `caution.md` l. 71, which holds) | C | stronger: any tie-break order | — | `gloss_refuted` (`H = η`, tight) | proved |
| `Witnesses.gloss_refuted`, `gloss_refuted_1000` (r1) | `caution.md` S3 (l. 71); final S3 "Withdrawn gloss" (l. 65), §3 (l. 121); A3.2 (l. 35) | **Refuted.** Quoted (`caution.md` l. 71, verbatim): "if `ρ_t ≤ 1` then `H_t ≤ max{R_t, η}` — the agent never does worse than sampling the trusted base distribution". Reading of the withdrawn clause: `R ≤ R̂ → H ≤ R`. Witness, **a D1 state**: `N = n + 4` uniform base actions, values in `[0, 1]` (`InRange` in the statement), two-hypothesis posterior `P = (3/10, 7/10)`, two decoys the second hypothesis fears, harmful action `a°` proxy-top under the natural order (`Compatible` in the statement), `R = R̂ = 1/N`; with `η ≤ 1 < Nη`: `q = 1/(Nη)`, `Q(a°) = η`, `H = η = Nη · R > R`; at `N = 1000`, `η = 1/10`: `H = 1/10 = 100 R`. Surviving neighbour: `realizedHarm_qRule_cases` / `realizedHarm_qRule_le_max` (the quoted sentence's formal clause). (Round 0's witness had `V ω′ a° = 3`, outside D1's range — audit r1 B1, both lenses; rebuilt from the adversarial auditor's `Fin 4` probe, parametrized. The mandate's `P = δ_{ω*}` construction is inconsistent, F-4.) | N+ | exact | — | themselves | refuted |
| `CautionState.floored_cost_bound_misspec` | S4(a), S4(c) (l. 67), §4 (l. 125); Taylor l. 63 | D8′, any `R̂`, **any `trueV : A → ℝ` outside `Ω`**: `E_Q[harmOf nul trueV] ≤ E_γ[…]/q_min` — "survives algebra misspecification" as a theorem | C | exact | — | `floored_tight_misspec` (tight, `R̂ = 0 < R`; constant proxy, so the ranking is the ambient tie-break and D8′'s proxy-ranking content is not exercised — r1 N5) | proved |
| `CautionState.realizedHarm_floored_le_robust` | S4(c) (l. 67) | `H ≤ R/q_min`, no hypothesis on `R̂` | C | exact | — | `floored_tight_misspec` | proved |
| `CautionState.realizedHarm_floored_le_min` | S4(c) (l. 67), §4 (l. 125) | `0 < R̂` (load-bearing, F-6): `H ≤ min{R/q_min, max{R, ηR/R̂}}` | C | exact | — | `gloss_refuted` inhabits `0 < R̂`, `0 < η` (the floored variant not instantiated) | proved |
| `Witnesses.floored_tight_misspec` | 2-046; S4(c) | `R̂ = 0`, `q = q_min = 1/2`, `trueV ∉ Ω`, `H = 1 = R/q_min` exactly; constant proxy so any order is compatible — the tightness is real, but the proxy does not rank (the ambient tie-break puts `a°` on top); a two-hypothesis version with `a°` genuinely proxy-top is the N+ without this caveat (r1 N5, not built) | N+ (caveat) | exact | — | itself | proved |
| `CautionState.qmass_top`, `isolated_error_le`, `isolated_error_within_budget_iff`, `qmass_top_eq_one` | S6(b) (l. 71), §6 (l. 133); A6.2 | `Q(a°) = min{q, g}/q`; contribution `≤ (gη/R̂) c(a°)`; within budget iff `g · c(a°) ≤ R̂` (F-7); `g ≥ q` ⇒ `Q(a°) = 1` | L | exact (`iff` is the exact form, F-7) | — | — | proved |

## T4 — Composition

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `prod2_quantilize_additive_cost_bound` | Taylor §3.3 Cost Independence (l. 183–185); S5(a) | additive `c₁ + c₂`: `E_{Q₁⊗Q₂}[c] ≤ (1/q) E_{γ₁⊗γ₂}[c]` | C | exact | — | — (Lemma 1 twice; degenerate instances trivial) | proved |
| `prod2_cost_bound_compound`, `prod2_quantilize_compound` | Taylor §3.3 (l. 191) | any nonnegative `c` on the product: factor `1/(q₁q₂)`, `q⁻²` | P | exact | — | `twoGame_independent` (tight) | proved |
| `prod_cost_bound_compound` | Taylor §3.3 (l. 191) (`stretch`) | `n`-fold over FAF's `Distr.prod`: factor `∏ 1/qᵢ` | P | exact | — | `nGame_sharp` (tight) | proved |
| `twoGame_independent` | Taylor §3.3 (l. 181–191); A5.1 | independent `1/3`-quantilizers pay `1`; base pays `1/9` | N+ | exact | — | itself | proved |
| `twoGame_joint` | Taylor §3.3, Fig. 2 | for **every** order compatible with `a₁ + a₂`: masses `1/3` on `(2,2), (2,1), (1,2)`, `0` on sum `≤ 2`; joint cost `1/3` | N+ | exact (any compatible tie-break) | — | itself | proved |
| `twoGame_cost_not_additive` | Taylor §3.3; S5(a) (l. 69) | the cost has **no** additive decomposition (F-8) | N+ | exact | — | itself | proved |
| `nGame_sharp` | 2-088 (d1); Taylor l. 191 | `n` games: independent quantilizers pay `1`, base `(1/3)ⁿ` — `q⁻ⁿ` attained | N+ | exact | — | itself | proved |
| `prod2_quantilize_not_quantilizer` | 2-088 (d2) | `Q_{3/4} ⊗ Q_{3/4}` on `Fin 2 × Fin 2` is not `Q_{q′}` of the product base under any order, any `q′` | N+ | exact | — | itself | proved |
| `d3_no_split_not_joint` | 2-088 (d3) | **the "if" direction refuted:** `U = (0, 1, 10)`, `q = 2/3`, no split, yet `Q ⊗ Q ≠ Q_{q²}` under every sum-compatible order (F-9) | N+ | exact | — | itself | proved (refutes the mandate's conjectured law; the "only if" direction not attempted) |

## T5 — S2, S5(b)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Witnesses.witnessB_refutes_COR`, `not_pointwise_implies_COR` | S5(b) (l. 69), §5 (l. 129); A5.2 (l. 49) | **Refuted.** Quoted: "D10's pointwise form implies `COR(T)`" (`caution.md` S5(b), as quoted by the adversary and the final). Reading: `CoveredOrKnownUncovered δ → R ≤ R̂`. Witness B, **inside realizability** (F-2): `Ω = {ω₁, ω*}`, `P(ω*) = 1/2`, `V_{ω₁} = (1/2, 1/2)`, `V_{ω*} = (1/4, 3/4)`, `δ = 1/4`, range `[0, 1]`, both actions covered (even the corrected predicate holds), `R̂ = 1/8 < 1/4 = R`. Surviving neighbours: `baseHarm_sub_le_estBaseHarm`, `realizedHarm_le_known_cost`. | N+ | exact | — | itself | refuted |
| `CautionState.abs_trueHarm_sub_proxyHarm_le`, `trueHarm_le_proxyHarm_add` | S2 (l. 63), §2 (l. 117) | `a`, `∅` covered ⇒ `|c(a) − (U(∅) − U(a))⁺| ≤ 2δ` | L | exact | — | `witnessB` (both covered) | proved |
| `CautionState.realizedHarm_le_decomp` | S2 (l. 63) | `H ≤ ∑_{C} π (U(∅) − U(a))⁺ + 2δ + ∑_{Cᶜ} π c` | C | stronger: first sum over `C` | — | `witnessB` | proved |
| `Witnesses.s2_null_uncovered` | S2 (l. 63); A2.2 (l. 31) (`stretch`) | S2 **without** `∅ ∈ C(δ)` is false: `a` covered, `∅` not, `|c(a) − (U(∅) − U(a))⁺| = 3/10 > 1/10` | N+ | exact | — | itself | proved |
| `CautionState.baseHarm_sub_le_estBaseHarm` | S5(b) (l. 69), §5 (l. 129) | under `NullCoveredKnownUncovered δ`: `R − 2δ ≤ R̂` (`COR_δ`) | C (S2 + Jensen + averaging; relabelled from P, r1) | variant: corrected predicate (F-1) | — | `witnessB_refutes_COR` (every base action covered; `−1/4 ≤ 1/8`); `mixed_witness` (r1 N6: `∅`, `a` covered, `b` known-uncovered, both disjuncts in use; `1/6 − 1/2 ≤ 1/3`) | proved |
| `CautionState.realizedHarm_le_known_cost` | S5(b) (l. 69), §5 (l. 129) | under the corrected predicate, `Q_q` with `q ≥ min{1, R̂/η}`, `0 < q ≤ 1`: `H ≤ k + 2δ + max{η, R̂}` with `k = ∑_{C(δ)} Q (U(∅) − U(a))⁺`. **`k` is not agent-computable** (coverage is invisible from inside, T1) — the source's "every term but `2δ` is computable" is F-18; the round-0 docstring repeated it (r1 B2, adversarial) | P | variant: corrected predicate; `q` abstracted (D8 under `0 < R̂`, D8′ always) | — | `witnessB_refutes_COR` (predicate); `mixed_witness` (r1 N6: at `η = 1/3`, `q = 1`, `H = 1/6`, `k = 1/6`, bound `1/6 ≤ 1/6 + 1/2 + 1/3`) | proved |
| `Witnesses.mixedState`, `mixed_witness` (r1) | S5(b) (l. 69), D10 (l. 55); mandate T5 | `A = {a, b, ∅}`, `Ω = Fin 2`, `P = (1/2, 1/2)`, `V ω* = (1/2, 1, 1)`, `V ω′ = (1/2, 0, 1)`, uniform base, `δ = 1/4`: `∅` and `a` covered (`e = 0`), `b` uncovered (`e = −1/2`) but known-uncovered (`c(b) = 0 ≤ ĉ(b) = 1/2`); `R = 1/6`, `R̂ = 1/3`; both repaired bounds and the computable bound instantiated with nonzero terms; in range, natural order proxy-compatible | N+ | exact (an instance; `q = 1`, the quantilizer is the base) | — | itself | proved |
| `CautionState.realizedHarm_le_known_cost_computable` (r1) | S5(b) (l. 69, "computable by the agent") — F-18 | the indicator dropped: `H ≤ E_Q[(U(∅) − U(a))⁺] + 2δ + max{η, R̂}` — every term but `2δ` a function of `P`, `γ`, `η` | C | weaker: `1_{C(δ)}` dropped (`proxyHarm ≥ 0`) — the bound the source's sentence can truthfully mean | — | `mixed_witness` (`1/6 ≤ 1/3 + 1/2 + 1/3`) | proved |
| `Witnesses.printed_predicate_no_CORδ`, `not_printed_predicate_implies_CORδ` | S5(b) (l. 69), D10 (l. 55) — finding F-1 | **Refuted.** Quoted: "Under D10's pointwise form (all of `supp γ_t` including `∅`, at `t`): `R̂_t ≥ R_t − 2δ`" (`caution-final.md` S5(b)). Reading: `CoveredOrKnownUncovered δ → R − 2δ ≤ R̂`. Witness: `V_{ω*} = (0, 1)`, `V_{ω′} = (0, 2/5)`, `P = (1/2, 1/2)`, `δ = 1/20`: `a` covered, `∅` not (null clause vacuous), `R − 2δ = 2/5 > 7/20 = R̂`. Surviving neighbour: the same theorem under `NullCoveredKnownUncovered` (`baseHarm_sub_le_estBaseHarm`). | N+ | exact | — | itself | refuted |

## T6 — Model M

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ModelM.heed_iff_epsStar` | S8 (l. 75), §8 (l. 141) | `Heed ↔ ε* ≤ ε_eff` — the parent's `twoState_deltaMinus_nonneg_iff_epsStar` at `ε_eff` (grade (a)) | L | exact | — | `numbers_rho4` | proved |
| `ModelM.heed_iff_muDagger_le` | §8 (l. 141) | `Heed ↔ μ† ≤ μ` for `ρ > 1`, `ε > 0` (regime not needed, F-12) | L | stronger | — | — | proved |
| `ModelM.dogmatic_never_heeds`, `dogmatic_never_heeds_though_warranted` (r1) | S8(a) (l. 76) | `μ = 0`, `ε < ε†` ⇒ `¬Heed`; and with `ε† ≤ ρε` ("although heeding is warranted in truth") the fully self-suspicious agent `μ = 1` (`ε_eff = ρε`) heeds (r1 N7) | L | exact (both halves of the source's sentence) | — | — | proved |
| `ModelM.bayesUpdate_zero`, `bayesIter_zero` | S8(a) (l. 76) | `μ = 0` is absorbing under every press record ("never heeds" is about every `t`) | L | exact | — | — | proved |
| `ModelM.pressProb_alphaTH` | §8 (l. 147); A8.3 | `p_th = p_reck` exactly (`ε ≠ 1`) | L | exact | — | `numbers_rho4` | proved |
| `ModelM.likelihood_th_eq_reck`, `bayesFactor_th_reck_eq_one`, `postOdds_eq_priorOdds` | S8(b) (l. 77) | every record has equal likelihood; Bayes factor `1`; posterior odds = prior odds (likelihood positive, so a ratio not `0/0`) | L (trivial once (i), as the source says; relabelled from P at r1 N1 — the mandate's P attaches to `alphaTH_mem_Icc`) | exact | — | `numbers_rho4` | proved |
| `ModelM.alphaTH_mem_Icc` | S8(b) (l. 77); A8.3 (l. 69) | **well-formedness:** `α′ ∈ [0, 1]` under `α, β ∈ [0, 1]`, `1 ≤ ρ`, `0 < ε < 1`, `ρε ≤ 1` | P | stronger: the source's `α ≤ β` dropped (r1 §3.8) | — | `numbers_rho4` (`31/190`) | proved |
| `ModelM.alpha_le_alphaTH`, `epsStar_mono_alpha`, `epsStar_le_epsStar_alphaTH` | S8(b) (l. 77) | `α ≤ α′`; `ε*` monotone in `α`; the trigger-happy hypothesis raises `ε†` | L / L / C | exact | — | `numbers_rho4` (`1/11 ≤ 31/221`) | proved |
| `ModelM.numbers_rho4` | §8 (l. 147) | `p_reck = 9/50`, `α′ = 31/190`, `ε*(α) = 1/11`, `ε*(α′) = 31/221` (the source's `0.163`, `0.1403`) | N+ | exact (rationals) | — | itself | proved |
| `ModelM.expect_logLR_eq_klBern` | S8(b′) (l. 78), §8 (l. 149) | expected labelled log-LR under `Bern(ρε)` is the two-point KL | L | exact | — | — | proved |
| `ModelM.klBern_pos`, `klBern_rho4_pos` | S8(b′) (l. 78) | `0 < D(Bern p₁ ‖ Bern p₂)` for `p₁ ≠ p₂ ∈ (0, 1)` (Gibbs strict); at `ρ = 4`, `ε = 1/20` | P / N+ | exact (positivity; the `0.1398` and the SLLN limit not formalized, F-11) | — | `klBern_rho4_pos` | proved |
| `ModelM.epsStar_scale` | 2-041; §8 (l. 151) | `ε*` invariant under `(c, h) ↦ (lc, lh)`, `l ≠ 0` | L | exact | — | — | proved |
| `ModelM.wholeLine_c_alone` | 2-041; A8.4 (l. 71) | at `(20, 2, 1/10, 1/2)`: `ε* = 2/3`; `Heed → 2/3 ≤ ρε` for every `μ ∈ [0, 1]`, `ρ ≥ 1` | L | exact | — | — | proved |

## T7 — S9

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `AUModel.harm_le_of_reversible` | §9 (l. 155) | `λ`-reversible, `0 ≤ λ`, `hnull` ⇒ `harm ≤ λ` under every `ω` | L | exact | — | `gainModel_reversible` | proved |
| `AUfin_null_le` | A9.4 (l. 89) | `hnull` is free in the Bellman model: `AU n (s·∅) ≤ AU (n+1) s` | L | variant: horizons shift by one | — | — | proved |
| `AUModel.rate_cap` | S9(a) (l. 84), §9 (l. 155); A9.1 | **the rate cap (load-bearing 5):** `AU(s₀) − AU(s_T) ≤ λT` — linear in `T`, a cap not a guard (telescoping; the content is the finding F-13) | L | variant: every action along the trajectory `λ`-reversible; the covered branch of the source's guarded form `AU(s_{t+1}) ≥ AU(s_t) − max{λ, k_t + 2δ}` not modelled (mandate T7(iii); r1 N2) | — | `gainModel` trajectories (trivial); no separate instance | proved |
| `AUModel.rate_cap_zero`, `au_mono_of_traps` | S9(a) (l. 84) | `λ = 0` (Kosoy's traps): `AU` nondecreasing | L | exact | — | — | proved |
| `AUModel.reversible_of_gain`, `gainModel_reversible` | A9.2 (l. 85) | an action raising `AU` under every `ω` is `λ`-reversible for every `λ ≥ 0` — D9 never penalizes power gain | L / N+ | exact | — | `gainModel_reversible` | proved |

## T8 — S12

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bayesPosterior_const` | S12 (l. 103) | a hypothesis-independent observation leaves the posterior unchanged | L | exact | — | — | proved |
| `s12_refuted`, `s12_not_sublinear` (r1) | `caution.md` S12 (l. 108); final S12 (l. 103), §12 (l. 159); A12.1 (l. 101) | **Refuted (the adversary's instantiation).** Quoted (`caution.md` l. 108, verbatim): "the agent acts by the delegation variant of D8 (delegate iff the intended action is not `λ`-reversible and `P_t(c_ω(a) > λ) ≥ η′`), and the advisor is *value-sane* … Conjecture: Bayesian regret against the `ω*`-optimal policy is sublinear". Reading refuted: **A12.1's instantiation, accepted by the final's §12** — posterior sampling in place of D8's quantilizer, which S12 leaves without the base and null action D8 needs (F-19). Witness: single-state model (every action `λ`-reversible, trigger never fires), the posterior iterate `s12Posterior` equal to the prior at every step, policy `(1 − p)δ_a + pδ_b`, per-step regret at the truth `= pg`, cumulative regret **over the iterate** `= pgT` (equalities; r1 N8); not `o(T)`. Surviving neighbour: `s12_refuted_d8` (D8's own policy), and the exploration-trigger salvage as a conjecture (F-14). (Round 0 presented the mandate's reading as a quotation — r1 B2, fidelity.) | N+ | variant: the adversary's policy substituted for D8 | (c) acting policy = A12.1's posterior sampling (the source's proof §12 makes the same substitution) | itself | refuted |
| `s12_refuted_d8` (r1) | `caution.md` S12 (l. 108), D8 (l. 49); final S12 (l. 103) | **Refuted (D8's own policy).** Same quotation. Reading: S12 with its own acting rule, D8's quantilizer at `q = min{1, R̂/η}` under the proxy ranking, on a state supplying the base and null action S12 omits. Witness `s12State`: `A = {∅, a, b}`, `Ω = {ω*, ω′}`, `V ω* = (1/4, 1, 0)`, `V ω′ = (1/4, 0, 1)`, `P(ω′) = 3/4`, uniform base — a D1 state, natural order proxy-compatible (`b` top), `R = R̂ = 1/12` (calibrated); `η = 1/4`: `q = 1/3`, quantilizer `δ_b`, realized harm `1/4 = η` (within budget, tight), regret at `ω*` `= 1` per step, `= T` over `T` steps; trigger never fires (single-state `AUModel`). Linear regret with the harm budget respected: D8 does not learn. | N+ | variant: base and null action supplied (S12 has neither); the trigger's second clause moot | (c) the base and null action are the witness's | itself | refuted |

## T9 — Option value

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `informed_sub_stop_decomp` | turner.md C4 (l. 81) | algebraic identity of the definitions (`optionValue` is defined as the difference); on record so C4's displayed identity has a name, no content (r1 N11) | L | exact | — | — | proved |
| `optionValue_nonneg` | C4 (l. 81); corr-core-007 | `0 ≤ optionValue` — Good's theorem, finite form, direct | P | exact (finite; duplicates the sibling's on a stochastic channel, disclosed) | — | `optionValue_threeAct_pos` (r1: on the parent's `twoState`, `Shᶜ = {cont}` is a singleton and every channel's option value is `0` — the round-0 pointer was N−, audit r1 §3.1) | proved |
| `threeAct`, `perfectChannel`, `optionValue_threeAct`, `optionValue_threeAct_pos` (r1) | C4 (l. 81) | Setting S with `A₂ = Fin 3`, `Sh = {0}`, `Shᶜ = {1, 2}` (each continue action optimal in one world), `Ω = World`, `μ(wrong) = ε`, perfect channel `E = World`: `optionValue = 1 − max{1 − ε, ε} = min{ε, 1 − ε}`, `> 0` for `0 < ε < 1` | N+ | exact (an instance) | — | themselves | proved |
| `optionValue_eq_partValue_sub`, `optionValue_nonneg'` | corr-core-007 via `corr-three-step-facts` | the bridge to `partValue − priorBest` on the joint `Ω × E`; nonnegativity re-derived from `priorBest_le_partValue` | L / C | exact | — | — | proved |
| `optionValue_coarsen_le` | C4 (l. 81), Objection 1 (l. 159) (`stretch`) | a coarser channel has no larger option value (reading (c1), true); reading (c2) false — sibling (F-15) | P | exact (reading (c1)) | — | — | proved |

## Not formalized (recorded)

| Item | Where recorded | Status |
|---|---|---|
| T6(b′) a.s. limit `μ_t → 1` (SLLN); the `(0.13, 0.15)` bracket | F-11 | prose-open, no Lean statement |
| T8(b) exploration-trigger salvage; 2-089's DRL-shaped regret theorem | F-14 | conjecture; the mandate's shape is empty in the toy |
| T4(d3) "only if" direction | F-9 | not attempted |
| T2 tie-break: the two quantilizers *differ* on a tie | report T2 | not formalized (equality of `E[U]` is) |
| T9(c2) menu-monotonicity false | F-15 | sibling `corr-power-channel`'s witness |
| T3 `floored_tight_misspec` with a genuinely proxy-top `a°` (audit r1 N5) | report §Repair round 1 | not built (caveat recorded in the row) |
| S7, S13, corr-wf14-009, 2-042, 2-082, 2-084, A5.3, Kosoy's theorem | F-16 | duplicates / not targets |
