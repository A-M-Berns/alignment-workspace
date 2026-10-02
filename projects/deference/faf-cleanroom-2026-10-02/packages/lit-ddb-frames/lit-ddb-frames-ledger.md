# lit-ddb-frames — ledger

Package `lit-ddb-frames` (faf-cleanroom run, 2026-09-29). One row per headline ([STANDARDS](../../STANDARDS.md) §6); supporting lemmas have no row. All declarations live in `Cleanroom.Found.LitDdbFrames` (examples in `.Examples`, Blackwell in `.Blackwell`); files under `Cleanroom/Found/LitDdbFrames/`. Kinds: P proved · C composition · L plumbing · D definition of record · N+/N− witness. Every theorem's only hypothesis beyond its antecedent is `hπ : π ∈ stdSimplex ℝ W` (a); no (b) or (c) hypotheses anywhere in the package. Status `proved` means built and gate PASS (see the report's "State of the package").

## Definitions of record (Targets 1–6; kind D, fidelity exact unless noted)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Frame`, `E`, `mass`, `ind`, `supp`, `Frame.cell`, `Frame.cands`, `Frame.candsMinus`, `Frame.selfMass` (`Defs.lean`) | DDB §1, glossary | frame ⟨W, 𝒫⟩ as row-stochastic `W → W → ℝ`; expectation, mass, indicator, support `W_ρ`, cell `[P = ρ]`, candidates `C_ρ` as a set of distributions, `C_ρ⁻`, `ρ(P = ρ)` | D | exact | — | — | proved (gate PASS) |
| `Frame.ModestAt`, `Frame.Immodest` | DDB §1 ll. 61, 82 | modest at w: `P_w(P = P_w) < 1`; immodest frame | D | exact | — | fig3 modest, `flat` immodest | proved |
| `Frame.informed` | DDB §1 l. 95 | `P̂_ρ = ρ(· ∣ P = ρ)` as a ratio vector; junk `0` at a null self-cell, positivity carried by every consumer | D | exact under `0 < selfMass` (docstring) | — | `fig3_informed` = vertices | proved |
| `Reflects` | DDB §1 l. 75 | `π(· ∣ P = ρ) = ρ` for candidates, product form | D | exact | — | fails on fig3 | proved |
| `NewReflects` (NR-str), `NewReflectsVac` (NR-vac), `NewReflects.vac` | DDB §1 ll. 86, 97, fn 12 | informed expert exists at every candidate and `π(· ∣ P = ρ) = ρ(· ∣ P = ρ)`; vacuous reading; str → vac | D, D, L | exact / variant | — | fig2 satisfies NR-str | proved |
| `Frame.probEvent`, `SimpleTrust` | DDB §2 l. 145 | `[P(q) ≥ t]`; `t·π(P(q) ≥ t) ≤ π(q ∧ P(q) ≥ t)` guarded, all real `t` | D | exact | — | via `TotalTrust.simpleTrust` on fig3 | proved |
| `Frame.condProbEvent`, `Trust` | DDB §2 l. 154 | `[P(q ∣ p) ≥ t]` product-guarded; Trust in product form | D | exact | — | via `TotalTrust.trust` on fig3 | proved |
| `TotalTrust` | DDB §2 l. 175 | `∀ X s, 0 ≤ ∑ w, π w (X w − s) 𝟙[s ≤ E_{P_w} X]` — the record form | D | exact (equivalence with DDB's ratio form is `totalTrust_iff_cond`) | — | fig3 (holds), fig2/fact21 (fails) | proved |
| `Frame.Validates` | DDB §4 l. 337 | every `P_i` defers Φ-wise | D | exact | — | — | proved |
| `DecisionProblem`, `Frame.IsStrategy`, `Frame.Recommended`, `stratValue` | DDB §1 ll. 113–117 | finite menus; strategies with the cell constraint; recommended = cellwise maximiser; `E_π(S)` | D | exact | — | `flat_value_not_valueNoCell` shows the cell constraint is load-bearing | proved |
| `Value`, `WeakValue` | DDB §1 l. 121, App. B l. 472 | ∀ nonempty menu ∀/∃ recommended S, `E_π(S) ≥ E_π(O)` | D | exact | — | fig3 (holds), fig2/fact21 (fails) | proved |
| `Frame.twoOption` | DDB §2 l. 190 | witness strategy for `{X, const s}` | D | exact | — | — | proved |
| `Frame.ModestlyInformed`, `Frame.ModestlyInformedAt` | DDB §4 l. 325, fn 54 | `0 < ρ(P = ρ) ∧ ρ ∈ convexHull({P̂_ρ} ∪ C_ρ⁻)`; no built-in self-weight positivity | D | exact | — | fig3 both candidates; fig2 `P_a` fails; `F₂` `P_2` fails | proved |
| `ClassConvex` | DDB Def. 7.2.6 | each candidate in hull of its informed self and the other candidates of π | D | exact (no guard, as DDB) | — | — | proved |
| `HullAndModestlyInformed` | DDB Thm 4.1 / 7.6 (iv) | `π ∈ convexHull C_π ∧ ∀ ρ ∈ C_π, ModestlyInformed ρ` | D | exact | — | `fig3_hull` (N+) | proved |
| `Blackwell.Experiment`, `Stochastic`, `IsGarbling`, `BlackwellLE`, `BlackwellLT`, `ofMap`, `Refines`, `bayesValue`, `MoreValuable`, `fibreMass`, `calibratedGarbling` (`Blackwell.lean`) | infrastructure (Blackwell 1953; consumers in module docstring) | finite kernels, garbling, the Blackwell order (first argument less informative), deterministic experiments and refinement, Bayes value over `Fin (n+1)` menus, more-valuable, conditional-mean report | D | exact (`calibratedGarbling` junk at null fibres, see docstring; `calibratedGarbling_mul_fibreMass` is the guarded form) | — | — | proved |
| `Refines.blackwellLE` | infrastructure | refinement is a garbling | L | n/a | — | — | proved |
| `MeasurableWrt`, `answer`, `ReflectsWrt`, `TotalTrustWrt`, `ValuesWrt`, `questionOf` (`Local.lean`) | DDB §5 l. 396, fns 62–64 | question-relative deference, definitions only | D | exact | — | — | proved |
| `totalTrust_iff_totalTrustWrt_id`, `TotalTrust.wrt`, `Value.wrt`, `measurableWrt_questionOf_ind` | infrastructure (Target 6) | TT = TT wrt `id`; TT → TT wrt every Q; Value → Value wrt every Q; 2-cell question | L | n/a | — | — | proved |
| `Frame.estEvent`, `Frame.estEventLE`, `Frame.condEstEvent` (`TotalTrust.lean`) | DDB §2 ll. 171, 180, 182 | `[E(X) ≥ s]`, `[E(X) ≤ s]`, `[E(X ∣ q) ≥ t]` product-guarded | D | exact | — | — | proved |
| `maximizers`, `Frame.informedChoice`, `Frame.informedStrategy`, `ValueTwoOption` (`Strategies.lean`); `Frame.DecompOver` (`Hull.lean`); `Frame.boost` (`Value.lean`) | DDB Lemma 7.3 l. 544; Lemma 7.5 l. 590; infrastructure | argmax with informed tie-breaking; Value on two-option menus; abstract decomposition; `S_i^t` | D | exact / n/a | — | — | proved |

## Target 2: Total Trust is DDB's, exactly

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `totalTrust_iff_dual` | §2 l. 180 | TT ⟺ dual form with `[E(X) ≤ s]` and `≤ 0` | L | exact | — | — | proved |
| `totalTrust_iff_cond` | §2 l. 175, Lemma 7.1 l. 484 | TT ⟺ `∀ X s, 0 < π(E(X) ≥ s) → s ≤ E_π(X ∣ E(X) ≥ s)` (ratio form, DDB's convention) | L | exact | hπ nonneg (a) | — | proved |
| `TotalTrust.strict` | mandate 2(c) | TT → strict-threshold product form | L | variant (strict threshold) | (a) | — | proved |
| `TotalTrust.simpleTrust` | §2 l. 171 | TT → Simple Trust | L | exact | — | fig3 | proved |
| `TotalTrust.trust` | §2 l. 182 | TT → Trust (via conditional TT) | C | exact | (a) | fig3 | proved |

## Target 3: strategies and the two-option witness

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Value.weakValue` | App. B l. 571 | Value → Weak Value (informed strategy exists) | L | exact | — | fig3 | proved |
| `stratValue_twoOption` | §2 l. 190, Lemma 7.1 | `E_π(S_wit) − s = ∑ w, π w (X w − s) 𝟙[s ≤ E_w X]` — the product form, literally | L | exact | (a) | — | proved |
| `totalTrust_iff_twoOption` | §2 l. 190 | TT ⟺ `∀ X s, s ≤ E_π(S_wit X s)` | L | exact | (a) | — | proved |
| `valueTwoOption_iff_totalTrust` (`Value.lean`) | §2 l. 190 | Value on two-option menus over all recommended strategies ⟺ TT (⇐ via the full cycle) | C | exact | (a) | fig3 | proved |

## Targets 7–10: the structure lemmas (`Hull.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `exists_not_mem_convexHull_erase` | Lemma 7.2.2 l. 504 | a nonempty finite set has a member outside the hull of the rest (extreme point) | P | stronger (arbitrary finite set) | — | any nonempty finset | proved |
| `no_selfless_maximal_set` | Lemmas 7.2.2–7.2.5, 7.3 (shared pattern) | the maximal-set lemma: a nonempty set of maximisers each decomposing over no-higher points, maximisers in the set and ≠ itself, is impossible | P | n/a (abstracted infrastructure) | — | used 5× | proved |
| `Frame.mass_supp_eq_one_of_hull` | Lemma 7.2.4 l. 510 | hull ∧ DecompOver → every candidate has full mass on `W_π` | P | stronger (abstract decomposition serves MI and class-convexity) | (a) | fig3 | proved |
| `Frame.P_self_pos_of_hull` | Lemma 7.2.5 l. 518 | hull ∧ DecompOver → `0 < P_i i` for `i ∈ W_π` (derived, not assumed) | P | stronger | (a) | fig3 | proved |
| `classConvex_iff_modestlyInformed` | Lemma 7.2.7 l. 524 | given `π ∈ convexHull C_π`: class-convex ⟺ all candidates modestly informed | P | exact | (a) | fig3 | proved |

## Target 11: consequences of Total Trust (instances of item 053; `lit-ddb-facts` generalises)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `TotalTrust.selfMass_pos` | fn 37, Lemma 7.2.5 | TT → every candidate has `0 < ρ(P = ρ)` | P | exact | (a) | fig3 | proved |
| `TotalTrust.cond` | §2 l. 182, fn 36 | TT → conditional TT in product form (direct route, no biconvexity) | P | exact | (a) | fig3 | proved |
| `TotalTrust.cond_ratio` | fn 36 | ratio form off null events | L | exact | (a) | — | proved |
| `TotalTrust.newReflects` | §2 l. 227, fn 37 | TT → New Reflection (strong reading) | P | exact | (a) | fig3 | proved |
| `TotalTrust.newReflectsVac_iff` | mandate Target 22 | under TT, NR-vac ⟺ NR-str | L | n/a | (a) | — | proved |

## Targets 12–17: the cycle and Theorem 7.6

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `WeakValue.totalTrust` | Lemma 7.1 l. 480 | Weak Value → Total Trust | P | exact | (a) hπ | fig3 (N+) | proved |
| `StrongDual.apply_eq_E` | §2 l. 213 (Target 24) | a continuous functional on `W → ℝ` is an expectation `E_ρ(X)` | L | n/a | — | — | proved |
| `TotalTrust.mem_convexHull_cands` | Lemma 7.2 l. 534 | TT → `π ∈ convexHull C_π` (Hahn–Banach) | P | exact | (a) | fig3; fails on fact21 | proved |
| `TotalTrust.classConvex` | Lemma 7.2 l. 536 | TT → class-convex (Hahn–Banach + NR at the candidate) | P | exact | (a) | fig3; fails on fig2 | proved |
| `TotalTrust.hullAndModestlyInformed` | Lemma 7.2 l. 498 | TT → hull ∧ modestly informed | C | exact | (a) | fig3 | proved |
| `HullAndModestlyInformed.weakValue` | Lemma 7.3 l. 540 | hull ∧ MI → Weak Value (informed strategy; maximal-set lemma) | P | exact | (a) | `fig3_hull` (N+, full package) | proved |
| `Frame.mass_cell_le_selfMass_of_hull` (`SelfWeight.lean`) | Lemma 7.4 proof l. 577 | self-cell dominance `σ(P = ρ) ≤ ρ(P = ρ)` from the hull condition | P | variant (cell-level, from hull not Trust) | (a) | fig3 | proved |
| `Frame.not_mem_convexHull_candsMinus_of_hull` | Lemma 7.4 l. 575 | hull ∧ MI → `ρ ∉ convexHull C_ρ⁻` | P | exact | (a) | fig3 | proved |
| `Frame.selfWeight_pos_of_hull` | Lemma 7.4 l. 575 | every decomposition has `λ_ρρ > 0` (DDB's phrasing) | C | exact | (a) | fig3 | proved |
| `Frame.mass_cell_lt_selfMass_of_hull` | Lemma 7.5 (**) ll. 601–610 | strict dominance for distinct candidates | P | exact | (a) | fig3 (two distinct candidates) | proved |
| `WeakValue.value` | Lemma 7.5 l. 583 | Weak Value → Value (boosted options, `t_ρ = δ/ρ(P = ρ)`) | P | exact | (a) | fig3 | proved |
| `tfae_value` | Thm 7.6 = 2.2 = 4.1 | `TFAE [Value, WeakValue, TotalTrust, HullAndModestlyInformed]` | C | exact | (a) hπ only | fig3 (all hold, N+); fig2, fact21, F₂ (all fail, N+) | proved |
| `value_iff_totalTrust`, `totalTrust_iff_hullAndModestlyInformed`, `value_iff_weakValue` | Thm 2.2, Thm 4.1, Lemma 7.5 | the three named iffs | C | exact | (a) | as above | proved |
| `Value.newReflects` | §1 l. 133, fn 19 | Value → New Reflection | C | exact | (a) | fig3 | proved |

## Targets 18–20, 23: witnesses (`Examples.lean`, `ExamplesFact21.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `fig2_newReflects`, `fig2_not_value`, `fig2_mem_hull`, `fig2_not_modestlyInformed`, `fig2_summary` | Figure 2, fn 13, fn 32 | anti-expert frame: NR-str holds, `π ∈ hull`, `P_a` not modestly informed, Value fails | N+ | exact | — | itself | proved |
| `fig3_not_reflects`, `fig3_modest`, `fig3_hull`, `fig3_totalTrust_value` | Figure 3, fn 18 | modest frame, Reflection fails, hull condition with explicit weights `7/8, 1/8; 7/9, 2/9; 3/7, 4/7`, hence TT and Value | N+ | exact | — | itself (full package of 7.6 (iv), non-degenerate) | proved |
| `fact21_not_totalTrust`, `fact21_not_value`, `fact21_not_mem_hull` | Fact 2.1 | TT fails at `(O_1, 0)`, Value fails on `{0, O_1}`, `π ∉ convexHull C_π` by the separating `O_1` | N+ | exact | — | itself | proved |
| `fig5F2_not_totalTrust`, `fig5F2_not_modestlyInformed` | Figure 5 `F₂`, fn 52 | fn 52's cut verified on the frame it refers to; `P_2` not modestly informed | N+ | exact | — | itself | proved |
| `flat_value_not_valueNoCell` | mandate Target 23 | Value holds but the unconstrained variant fails on the flat immodest frame | N− | variant (refutes the encoding without the cell constraint) | — | itself | proved |

## Not done

| Item | Status |
|---|---|
| Target 20 stretch: `Trust π21 fact21` (DDB's Mathematica claim) | not attempted (no Lean statement); would need the attained-threshold reduction for Trust and a 64-pair bounded check |
| Target 22: Value over `Finset` menus ⟺ over `Fin n`-indexed menus; Trust with real ⟺ attained thresholds | not attempted; NR-str ⟺ NR-vac under TT done |
| Open statements | none (`lit-ddb-frames-open.txt` not needed) |
