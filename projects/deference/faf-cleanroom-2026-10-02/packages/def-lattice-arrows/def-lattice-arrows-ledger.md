# def-lattice-arrows — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Deference.DefLatticeArrows.` omitted (`Finite.`, `Wedge.`, `Counterfactual.`, `Amp.`, `Witness.` are sub-namespaces). "Hyps (b)/(c)" lists only non-(a) hypotheses; "—" means every hypothesis is (a) or there is none. Per the mandate's design decision 1, every arrow has a per-instance row (`C`, the theorem: instance facts as hypotheses, packages as data) and a predicate-level row (`L`, existence clauses named). Witness column: the instance in `Witness.lean` inhabiting the row's hypothesis package, or `partial: …` for the predicate-level rows whose clauses no package here discharges. Since repair round 1: for the self-expert over `paperDP T` the deference hypothesis `TowerValued` is a theorem (`Witness.towerValued_self`, no hypothesis; audit r1 adversarial N1) and the clauses `QuotesAvailable`/`ProductQuotesAvailable`/`CondQuotesReflected` are discharged for computable experts by `OneWay.lean`, so every arrow *out of* the tower has only its fold / self-endorsement clause left for the self-expert; the arrows *into* the tower and the partition still need the gap/probe/band packages (`li-quote-lane`). Status `proved` unless said; no `open`, no `refuted`, no `flagged`. Report: [def-lattice-arrows-report](def-lattice-arrows-report.md); findings: [def-lattice-arrows-findings](def-lattice-arrows-findings.md).*

## T0 — infrastructure (`Packages.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `listComb`, `listCombSyntax`, `listComb_boundedSequence` | FAF `LUVCombination`, `LUVCombinationSyntax`; def-lattice F18 | constant-coefficient combinations over a list of e.c. LUV sequences with a machine-metered (day-dependent) constant, with their syntax/`BoundedSequence` certificates | D | n/a | — | every arrow's combination | proved |
| `expect_listComb_ge_of_eventually` / `_le_` / `_eq_` | mandate T0; `total-trust-implies-value` Lemma 1 (ε-outside); FAF `thm:expprovind` | an *eventual* world bound (from some day on, for every `ε`) gives the asymptotic bound; finite patch of the constant (`patchConst`) below the day | C | stronger: FAF's all-days `hval` relaxed | — (`hworld` FAF endpoint premise) | used by T2–T6, T11 | proved |
| `expect_listComb_eq_of_slack` | mandate T0; FAF `dd:mesh` | a world bound within a vanishing slack on every day gives `≈ₙ` | C | stronger: within slack | — | used by T5, T4c | proved |
| `ExpertFoldAt`, `ExpertFoldCond`, `ExpertPin`, `GapQuote`, `constLUV` | mandate design decision 2 | the expert-side packages, asymptotic, reflection form, no `affine`, no existence | D | variant: asymptotic (the corpus's "provably" is refuted at finite days, def-lattice F3) | — | — | proved |
| `constLUV_codes`, `constLUV_valuesAt` | mandate design decision 2 | the constant LUV is e.c. (ruler dispatch on `i·q < p·k`) and valued at its constant in every world | L | exact | — | — | proved |
| `expertPin_constLUV` | def-lattice F3 (nearest well-posed (iii)); mandate T11 | an inductor expert pins every constant LUV at its value at the deferred day | C | exact (asymptotic pin) | — | any inductor expert | proved |
| `TowerValued`, `towerValued_of_tower` | `deference-notions` §Mart; def-lattice audit r2 fidelity 2 | Tower on world-valued sources; `Tower` implies it | D/L | variant: valued sources only (F7) | — | self over `paperDP T`: `Witness.towerValued_self` (N+, no hypothesis; F13) | proved |
| `expect_reflects_congr` | audit r1 adversarial N1 (probe); T0 | two e.c. quotes reflecting the same expert estimates have asymptotically equal novice expectations (T0, slack `0`) — what moves a Tower instance between quotes of the same source | C | exact | — | `Witness.towerValued_self` | proved |

## T6 — bounds transfer (`Transfer.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ramp_eventually_one` | `total-trust-implies-value` Lemma 1 (b) | under `E*(X) ≳ₙ v` and `δ < ε` the ramp at `v − ε` is eventually exactly `1` | L | exact | — | — | proved |
| `expect_weight_asympEq_one`, `expect_product_asympEq_source` | Lemma 1 first/third steps | once the ramp saturates, `E^H(W) ≈ₙ 1` and `E^H(XW) ≈ₙ E^H(X)` (T0) | C | exact (within slack) | — | `Witness.rampWitness` | proved |
| **`transfer_instance`** | Lemma 1; PDF slide 19 (F3) | one ramp package at `v − ε`, `δ < ε`, its TT instance and `E*(X) ≳ₙ v` give `E^H(X) ≳ₙ v − ε` (saturation only, no slope) | C | exact (`δ < ε` in place of `δ < ε/2`) | — | `Witness.transfer_witness` (all (a), **N−**: the package is inhabited by FAF's closed conclusions over the real inductor, but the source is valued `1` in every world, so the TT instance, `hA` and the conclusion are each independently trivial; FAF has no non-provable eventual lower bound to do better with — audit r1 fidelity B2) | proved |
| **`expert_bound_transfer`** | PDF slide 19; root-deference-016 | packages at every `0 < ε ≤ η` give `E^H(X) ≳ₙ v` (diagonal) | C | exact | — | `Witness.expert_bound_transfer_witness` (N−, as above: the conclusion is also `lic_provind_true` on `ψ ∘ f` directly), `_succ` (no hypothesis, N−) | proved |
| `RampQuotesAvailable` | `value-implies-tower` §Channel | above-ramp quotes exist for `X` at every `(s, δ)` | D | exact (existence clause) | (c) | self on literal-indicator sources for thresholds in `[0,1]`: FAF `st` (`Witness.rampWitness`, which needs `0 ≤ s ≤ 1`; `expert_bound_transfer_of_totalTrust` calls the clause at `v − ε`, negative for `v = 0`, so the clause is not asserted for the self-expert in Lean) | proved |
| `expert_bound_transfer_of_totalTrust` | slide 19 | from `TotalTrust` and ramp quotes | L | exact | (c) `RampQuotesAvailable` | partial: needs li-quote-lane (AI) | proved |

## T4 — Tower ⟹ soft Total Trust, band pinch (`TowerToTrust.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `sub_mul_wt_nonneg` / `_nonpos` | `tower-implies-total-trust` fact (c) | ramp arithmetic: `(x − s)·wt x ≥ 0` for a weight positive only above `s` (dually `≤ 0`) | L | exact | — | — | proved |
| **`thresholdAbove_instance_of_tower`** / **`thresholdBelow_instance_of_tower`** | `tower-implies-total-trust` §Proof; v6 §1.6 (root-deference-005); vq-wiki-004 | one Tower instance at `XW`, the fold, and a weight positive only above (below) `s` give `E^H(XW) − s E^H(W) ≳ₙ 0` (`≲ₙ 0`) | C | exact | (b) self / (c) general: `ExpertFoldAt` | `Witness.softAbove_witness_of_fold` (N−: fold not discharged) | proved |
| `softAbove_instance`, `softBelow_instance` | as above | the ramp instances (both halves, the below half derived directly, no `−V`) | C | exact | as above | as above | proved |
| `bandWt_pos_iff`, `bandWt_nonneg` | `tower-implies-total-trust` §The limit-equality; mandate T4 | support of the band weight: `s − ε < q < s + ε` (no `ε > δ` needed) | L | exact | — | — | proved |
| `bandAbove_instance`, `bandBelow_instance` | vq-wiki-005 | the band pinch, both faces, per instance | C | exact | as above | partial: band package (def-lattice N2) | proved |
| `ProductQuotesAvailable`, `ExpertFoldsAt` | `tower-implies-total-trust` §Hypotheses | existence of product quotes at `wt`; the folds at `wt` | D | exact / variant: asymptotic | (c) / (b)-(c) | quotes: `OneWay.productQuotesAvailable_of_marketComputation` (computable experts over `paperDP T`); folds: not discharged (F8) | proved |
| `softTotalTrustAbove_of_towerValued`, `softTotalTrustBelow_of_towerValued`, `totalTrust_of_towerValued`, `bandReflection_of_towerValued` (+ the `_of_tower` corollaries) | `tower-implies-total-trust`; vq-wiki-004/005 | predicate level: from `TowerValued` (resp. `Tower`), product quotes and folds | L | exact | (c) product quotes; (b)/(c) folds | self over `paperDP T`: `TowerValued` (a) `Witness.towerValued_self`, quotes (a) `OneWay`; folds (b) remain (`Witness.softTotalTrustAbove_self_of_folds`, `softTotalTrustBelow_self_of_folds`); AI: li-quote-lane | proved |

## T3 — the ε-fold (`Fold.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| **`condTower_instance`** | v6 §1.5 (root-deference-004); lean-deference-009; vq-wiki-003 | a `CondQuote`, a quote of `Z`, the Tower instance at `Z` and the fold `E*(Z) ≈ₙ E*(X)·w(f n)` give `E^H(Z) ≈ₙ E^H(Z')` | C | exact (weight at `w (f n)`, F2) | (b) self / (c) general: `ExpertFoldCond` | self over `paperDP T`: the Tower instance (a) via `Witness.towerValued_self`, the quotes (a) `OneWay`; the fold (b) remains (`Witness.condTower_self_of_folds`); FAF's closed `ccee` gives the *conclusion* on its own packages directly, not the instance's hypotheses | proved |
| `CondQuotesReflected`, `ExpertFoldsCond` | `value-implies-tower` §Channel; v6 §1.5 | existence of the left-product quotes; the folds | D | exact / asymptotic | (c) / (b)-(c) | quotes: `OneWay.condQuotesReflected_of_marketComputation`; folds: not discharged (F8) | proved |
| **`condTower_of_towerValued`** (+ `condTower_of_tower`) | v6 §1.5; vq-wiki-003 | predicate level: `CondTower` from `TowerValued` (`Tower`), quotes and folds | L | exact | (c) quotes; (b)/(c) folds | self over `paperDP T`: `TowerValued` (a), quotes (a); folds (b) remain (`Witness.condTower_self_of_folds`); AI: li-quote-lane | proved |
| **`towerValued_of_condTower`** | v6 §1.5 (`w ≡ 1`); mandate T3 converse | `CondTower` at the constant weight `1` gives the tower on every valued source | L | weaker: valued sources only (F7) | — | — | proved |
| `tower_condTower_square` | v6 §1.5 ("one principle") | `TowerValued → CondTower` and back | L | weaker: over `TowerValued` | as above | — | proved |

## T5 — Total Trust ⟹ Tower by gap-bets (`GapBets.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `expect_gap_pair_asympEq_one`, `expect_gap_unfold` | `total-trust-implies-mart` §Proof Steps 2–3; `value-implies-tower` Steps 4–5 | `E^H(G) + E^H(G') ≈ₙ 1`; `2E^H(G) − E^H(Z) + E^H(Y) − 1 ≈ₙ 0` (T0, slack) | C | exact (rescaled, within slack) | — | partial: gap packages (li-quote-lane) | proved |
| `tower_of_gap_halves` | as above | `E^H(G) ≳ₙ ½` and `E^H(G') ≳ₙ ½` give the Tower instance | C | exact | — | — | proved |
| **`tower_instance_of_totalTrust_gapBets`** | `total-trust-implies-mart` ⚠ (statement of record); lean-deference-071; vq-wiki-010 | gap quotes, the pins at `½`, and transfer packages at `½ − ε` (`ε ≤ ½`) give `E^H(Z) ≈ₙ E^H(Y)` — T6 twice at `½`, no `δ`-diagonalization, no provable introspection | C | variant: rescaled gaps in `[0,1]`, threshold `½` for `0`; pins asymptotic | (b) self / (c) general: `ExpertPin` on the gaps | partial: gap packages | proved |
| `GapPackagesAvailable`, `ExpertPinsGaps` | `total-trust-implies-mart` (H1); lean-deference-072 | the gap-closed class as an existence clause; the expert pins every gap quote of sign `±1` at `½` (the two signs the arrows use, no others — audit r1 N6) | D | exact / asymptotic | (c) / (b)-(c) | — (even the trivial sign `a = 0` would cost the deferred-day pull-back, F8) | proved |
| **`towerValued_of_softTotalTrust_gapBets`** (the mandate's `tower_of_softTotalTrust_gapBets`, renamed for where it lands) | `total-trust-implies-mart` §Statement | predicate level: `TotalTrust` ⟹ `TowerValued` | L | weaker: valued sources; rescaled | (c) gap packages; (b)/(c) pins | partial: gap packages (li-quote-lane; the self-expert's gap LUVs are not shown to exist) | proved |

## T11 — Value ⟹ Tower via probe menus (`Probe.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `probeConst`, `ProbeData` | `value-implies-tower` §The probe menu | the constant probe `constLUV ((1 − ε)/2)`; the follower data on `twoOptionMenu G K` | D | variant: rescaled | — | — | proved |
| `probe_eventually_top`, `expect_follower_asympEq_gap`, `expect_probeConst_asympEq` | §Proof Steps 2–3 | the gap is eventually strictly top-quoted (margin `ε/8`); the follower's expectation tracks the gap's (T0, eventual, exact); the probe's tends to its value | L/C | exact | pins | — | proved |
| **`probe_instance`** | §Proof Steps 1–3; PDF slide 11; lean-deference-070; vq-wiki-019 | per `ε`: the menu-local Value instance on `{G, K_ε}` gives `E^H(G) ≳ₙ (1 − ε)/2` | C | variant: rescaled; menu-local Value (F17) | (b)/(c) `pinG`; `pinK` (a) for inductor experts | partial: probe packages | proved |
| **`tower_of_value_probes`** | §Proof Steps 1–5 | both ways at every `0 < ε ≤ 1`, diagonalized (`η = ½`), unfolded: `E^H(Z) ≈ₙ E^H(Y)` | C | variant: rescaled; per-menu instances | (b)/(c) the gap pins; `pinK` | partial: probe packages | proved |
| `ProbeMenusAvailable` | §What the theorem costs (channel) | the probe followers and gap quotes exist | D | exact (existence clause) | (c) | — | proved |
| **`towerValued_of_value_of_probes`**, `towerValued_of_value_of_probes_inductor` (the mandate's `tower_of_value_of_probes`, renamed for where they land) | §Statement | predicate level: unconditional `Value` ⟹ `TowerValued`; constant pins discharged for inductor experts | L | weaker: valued sources; rescaled; from a predicate the corpus refutes unconditionally | (c) probe menus; (b)/(c) gap pins | partial: needs li-quote-lane | proved |
| `selfEndorse_probe` | mandate T2/T11; `value-implies-tower` §The scope condition is vacuous here | T2's `hSE` on a probe menu from the pins on `G`, `K` **and the follower** (F5) | L | weaker: needs the follower pin (disclosed) | (b)/(c) three pins | — | proved |

## T2 — Tower ⟹ Value under self-endorsement (`ArgmaxValue.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| **`value_instance_of_tower_of_selfEndorse`** | v6 §1.1 (root-deference-002); lean-deference-003 flag | two Tower instances at any e.c. `S` and option `O^i` (the follower in the predicate-level form; `Follows` and `Menu.Valued` are not consumed at the instance), the quotes, and `hSE : E*(S) ≈ₙ M_n` give `E^H(S) ≳ₙ E^H(O^i)` | C | variant: F1 asymptotic; not the refuted unconditional arrow | (c) `hSE` (H3-laden) | partial: `Probe.selfEndorse_probe` derives `hSE` on probe menus from three pins ((b) self / (c) general); no inhabitant | proved |
| `SelfEndorses`, `QuotesAvailable`, `follows_valued` | v6 F1; `total-trust-implies-value` Lemma 2; channel | self-endorsement on every valued menu; every e.c. sequence has a quote; a follower of a valued menu is valued | D/L | asymptotic / exact | (c) / (c) | `OneWay.quotesAvailable_of_marketComputation` | proved |
| **`value_of_towerValued_of_selfEndorse`** (+ `value_of_tower_of_selfEndorse`) | v6 §1.1; root-deference-002 | predicate level: `Value` from `TowerValued` (`Tower`), quotes and self-endorsement | L | variant: under `SelfEndorses` | (c) quotes, `SelfEndorses` | self over `paperDP T`: `TowerValued` (a), quotes (a); `SelfEndorses` (c) remains (`Witness.value_self_of_selfEndorses`), and it is `def-argmax-value`'s | proved |

## T7 — hedged Value ⟺ TT; the free converses (`Hedged.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `hedgedValue_iff_softTotalTrustAbove_instance` | lean-deference-010; def-lattice T6c, F6 | Value against the constant on the hedged menu **is** the product form (no `hLoe`) | L | exact (both arrows) | — | def-lattice `witness_twoOption_value` | proved |
| `value_twoOption_hardAbove_iff`, `value_twoOption_hardBelow_iff` | `two-option-value-iff-total-trust` §Statement ("iff"); def-lattice audit r2 N2 | the per-menu Value instance on `{X, C}` ⟺ the hard face at the expert's quote `q_n = E*(C_n)` | C | variant: threshold at the expert's quote (def-lattice F3) | — | no N+ inhabitant (def-lattice audit r2 N3: its T6d data inhabited only degenerately) | proved |

## T4c — the partition argument and the square (`Partition.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| **`ctsInd_sub_ctsInd_eq_band`**, `ctsInd_down_sub_eq_band` | `reflection-in-li` §It joins the circle; F1 | the corrected band identity: for `t + δ ≤ t'`, `ctsInd δ q t − ctsInd δ q t' = ctsInd δ q t · ctsInd δ (t' + δ) q` (and the downward mirror) | L | exact (the corrected identity) | — | — | proved |
| `bandWt_grid`, `sum_bandWt_grid` (+ `_down`) | as above | band `k` of a grid is the bracket; the brackets telescope to the ramp on `[0,1]` | L | exact | — | — | proved |
| `expect_weight_eq_sum_bands_of_partition`, `expect_product_eq_sum_bands_of_partition` | as above ("summing the bands with the novice's `loe`") | `E^H(W) ≈ₙ ∑ E^H(W_k)`, `E^H(XW) ≈ₙ ∑ E^H(XW_k)` for bands partitioning the weight (T0, slack) | C | exact (within slacks) | — | — | proved |
| **`softAbove_instance_of_bandFaces`**, **`softBelow_instance_of_bandFaces`** (repair r1: were `…_of_bandReflection`, from the whole predicate — a squeeze over def-lattice's unbounded-width `BandReflection`, audit r1 fidelity B1) | vq-wiki-006 | on a grid with spacing `≥ δ`, the `K` band faces (lower faces of the grid's bands, at half-width `ek ≥ δ`), taken as hypotheses, sum to the soft TT face at `(v, δ)` | C | exact (faces as hypotheses) | — (the `K` faces `hfaces` are the instance facts; packages data) | partial: band packages (def-lattice N2) | proved |
| `BandReflectionWithin`, `bandReflectionWithin_of_bandReflection` | audit r1 fidelity B1; `reflection-in-li` (narrow bands) | def-lattice's `BandReflection` restricted to bands of half-width `≤ c·δ`; the unbounded predicate implies it for every `c` | D/L | variant: half-width bounded by `c·δ` | — | — | proved |
| `BandQuotesAvailable`, `canonical_grid_up/down`, `ek_canonical`, `ekD_canonical` | mandate T4 | band quotes at every band; the canonical grids reach `1` / `0`, with bands of half-width exactly `δ` | D/L | exact | (c) | — | proved |
| `softTotalTrustAbove_of_bandReflectionWithin`, `softTotalTrustBelow_of_bandReflectionWithin`, **`totalTrust_of_bandReflectionWithin`** | vq-wiki-006 | predicate level: `BandReflectionWithin c` (`c ≥ 1`) ⟹ `TotalTrust` by the partition on the canonical grids — the content of the wiki's argument | L | exact (narrow bands) | (c) band quotes | partial: needs li-quote-lane | proved |
| **`bandReflectionWithin_iff_totalTrust_onQuotes`** | `reflection-in-li` (the four-face square) | `BandReflectionWithin c ↔ TotalTrust` under the disclosed clauses (`→` partition; `←` T5 then T4b then restriction) | L | exact modulo the clauses; narrow bands | (c) band quotes, gap packages, band product quotes; (b)/(c) gap pins, band folds | partial: needs li-quote-lane | proved |

## F12 — the wide band (`WideBand.lean`; repair round 1)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bandWt_wide_eq_ramp`, `bandWt_wide_eq_rampBelow`, `WeightQuote.toWideBand`, `WeightQuote.toWideBandBelow` | audit r1 fidelity B1 (probe) | a band of half-width `ε ≥ (1 + δ − v)/2` centred at `v ± ε` is the up-/down-ramp at `v` on `[0,1]`; a ramp `WeightQuote` is a `WeightQuote` at that band with the same `W`, `XW` | L/D | exact | — | — | proved |
| `softTotalTrustAbove_of_bandReflection`, `softTotalTrustBelow_of_bandReflection`, **`totalTrust_of_bandReflection`** | `reflection-in-li` §It joins the circle; audit r1 fidelity B1 | **`BandReflection ⟹ TotalTrust` with no clause at all**: over def-lattice's unbounded-width predicate every soft TT face is one wide-band face (F12); the partition is redundant there | L | exact (trivially: the conclusion is a special case of the hypothesis) | — | — | proved |
| **`bandReflection_iff_totalTrust_onQuotes`** | `reflection-in-li` (the four-face square); mandate T4 | `BandReflection ↔ TotalTrust`: `→` free; `←` T5 then T4b under the disclosed clauses | L | exact modulo `←`'s clauses | (c) gap packages, band product quotes; (b)/(c) gap pins, band folds — all for `←` | partial: needs li-quote-lane | proved |
| **`bandWt_ne_rampAbove_of_narrow`** | audit r1 fidelity B1 ("no wide-band route") | for `2ε < 1 − v` (any `δ`), `bandWt δ s ε` and `rampAbove δ v` differ somewhere on `[0,1]`: under `ε ≤ c·δ` no band is the ramp at any `v < 1 − 2cδ`, so `BandReflectionWithin` does not contain those faces and the partition is what proves them | P | exact | — | — | proved |

## T1 — the finite backbone (`Finite.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `decomposition` | lean-deference-001; check.py A | `gap_i = D_CM + D_UM,i + soft_i`, no normalization of `α` | L | exact | — | `fig2_decomposition_Oa` | proved |
| `value_of_defects`, `soft_nonneg`, `value_of_CM` | lean-deference-002 | finite tower ⟹ Value | L | exact | — | `fig3_gaps` | proved |
| `softmax_lower_bound` | lean-deference-004; check.py B | `∑ softmax_δ(m)_j m_j ≥ m_i − #J·δ` (`#J` the number of options) | P | weaker: crude constant `#J·δ`, not `δ log #J` (disclosed) | — | — | proved |
| `value_of_argmax`, `payoff_gap_le_l1`, `value_argmax_via_softmax` | lean-deference-006 | argmax backbone; the `L¹` bound; the `AsympLE` squeeze | L/P/L | exact | — | — | proved |
| `fig2_selection_argmax`, `fig2_gaps`, `fig2_stationary`, `fig2_decomposition_Oa` | check.py C; root-deference-2-015 | Fig 2: gaps `(−1, −1)`, `πP = π`, decomposition `(−8/5, 0, 3/5)` | N+ | exact | — | over `LitDdbFrames.fig2` | proved |
| `fig3_selection_argmax`, `fig3_gaps`, `fig3_not_stationary` | check.py C | Fig 3: gaps `(1, 1)`, `πP = (11/20, 9/20) ≠ π` | N+ | exact | — | over `LitDdbFrames.fig3` | proved |

## T9 — the wedge (`Wedge.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `hardCut_of_nonneg`, `softCut_summand_zero` | lean-deference-2-015 msgs 16/24 | one-sidedness: hard cut = `E_π(X)` where `e ≥ 0`; the soft summand vanishes at `e = 0` | L | exact | — | — | proved |
| **`boundary_soft`**, **`boundary_hard_fails`**, `boundary_hedged_endorsed`, `boundary_hard_value_fails` | lean-deference-2-015; F2 | (a) on the bet `X = (−1, 1)`: the boundary novice passes every soft threshold-0 cut at every width, fails the hard cut, and (the soft cut restated through the two-option identity) passes the hedged two-option Value instance while failing the hard one | N+ | variant: finite two-world frame with real weights, one bet (the chat's claim is about LI novices at asymptotic grade; the mandate's prescribed form) | — | itself | proved |
| **`wedge_soft`**, **`wedge_hard_fails`**, **`wedge_soft_half_fails`**, `separation` | mandate T9 (b) | (b) on the same bet, the wedge novice separates at width `δ` but not at `δ/2`; the separation is per bet and per width | N+ | variant: finite frame, one bet | — | itself | proved |

## T10 — the self-counterfactual witness (`Counterfactual.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Route`, `ActIndependent`, `reading_sound_of_actIndependent` | v2 §8 (root-deference-2-012) | the two routes; act-independence; under it the taken-route value is the commit payoff | D/L | exact (earlier-predictor model) | — | — | proved |
| **`witness`** (`witnessMenu_not_actIndependent`, `witness_value_inequality`, `witness_reading_fails`) | v2 §8 *Witness* (ATTRIBUTION: v2's own paragraph, paraphrased) | the menu violates act-independence, satisfies Value's inequality on the road taken, and the committed payoff beats the followed strategy | N+ | exact | — | itself | proved |

## T8 — the amplifier (`Amplifier.lean`; measure model throughout)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `integral_quadratic` | infrastructure | `∫ (k e² + m e + p)` | L | n/a | — | — | proved |
| **`soft_upper_cut_nonneg`**, **`soft_lower_cut_nonneg`** (+ the closed forms `integral_soft_upper_of_le/gt`) | `amplifier-counterexample` ("Soft cuts come free"); vq-wiki-011; lean-deference-019 | the amplifier passes every soft parallel cut at every width | P | variant: measure model | — | — | proved |
| `integral_gap`, **`gap_kill`**, `gap_kill_concrete` | `amplifier-counterexample` §Why it dies under gap-bets | `∫_a^b (amp c e − e) = c(b − a)(a + b − 1) ≠ 0` for `c > 0`, `a ≠ b`, `a + b ≠ 1`; at `(a, b, c) = (0, ½, 1)` it is `−1/4` (repair r1: the ledger and report printed `−1/8`; the Lean proves `−1/4 = 1·½·(−½)`) | P/N+ | variant: measure model | — | `gap_kill_concrete` | proved |
| `amp_unweighted_centered_zero`, `amp_weighted_centered_moment`, **`amp_weighted_centered_neg`** | `centered-bet-squeeze` §4; root-deference-008 | the amplifier survives the unweighted centered bet (`0`) and dies under the weight `1 − e` (`−c/6 < 0`) | P/N+ | variant: measure model | — | — | proved |
| `exact_pinch`, `amp_marginal` | lean-deference-034; `amplifier-counterexample` | the single-state pinch; `∫_0^1 amp c = ½` | L | exact / measure model | — | — | proved |

## T13 — the one-way pair (`OneWay.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| **`quotesAvailable_of_marketComputation`** | mandate T13; FAF `RationalQuoteCode.ofComputable`, `MarketComputation` | over `paperDP T`, every expert whose history is a computable market has an e.c. quote of every e.c. sequence (F6) | C | exact | — (`MarketComputation E.A` is data) | `quotesAvailable_self` (the paper market) | proved (the mandate expected `open`) |
| `productQuotesAvailable_of_marketComputation`, `condQuotesReflected_of_marketComputation`, `quotesAvailable_self` | mandate T13 | the T4/T3 existence clauses and the self-expert's quotes, discharged | L | exact | — | — | proved |

## Witnesses (`Witness.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `tautFamily`, `tautFamily_codes`, `tautFamily_holds`, `deferredTaut_codes` | mandate Witnesses | the day-varying provable family `∼(⌜a_m⌝ ⋏ ∼⌜a_m⌝)` and its deferred read `ψ ∘ f` (e.c. for a ruler deferral) | D/L | n/a | — | — | proved |
| `stWitness`, `rampWitness`, `tt_witness` | FAF `selfTrustQuoteOfRepresentation`, `lic_self_trust`; def-lattice `Witness` generalised | FAF's closed `st` package for any e.c. family; its `WeightQuote` projection (slack `≡ 0`); the TT instance | N+ | exact | — | itself | proved |
| `hA_witness` | FAF `lic_provind_true` | the expert's lower bound on the deferred tautology family, at the deferred day | C | exact | — | — | proved |
| **`transfer_witness`**, **`expert_bound_transfer_witness`**, `expert_bound_transfer_witness_succ` | mandate Witnesses (the prescribed provable-family witness of T6; the mandate's "N+" conflicts with STANDARDS §3, which wins — audit r1 fidelity B2) | T6's instance and headline over the paper's inductor with every hypothesis (a): `E^H_n(1(ψ(f n))) ≳ₙ 1` | **N−** | exact | — | itself; N− because the source is valued `1` in every consistent world, so the TT instance, `hA` and the conclusion are each independently trivial (the conclusion is `lic_provind_true` on `ψ ∘ f` directly) — the package is inhabited by FAF's closed conclusions over the real inductor with a day-varying, machine-metered source, and FAF has no non-provable eventual lower bound `E*(X_n) ≳ₙ v` to do better with (F11 (5)) | proved |
| `ceeQuote_reflects`, **`softAbove_witness_of_fold`** | mandate Witnesses (the FAF-closed T4 attempt) | the closed `cee` quote of `XW` reflects; T4's above half on FAF's closed packages with `ExpertFoldAt` the one hypothesis | L / N− | exact | (b) `hfold` | itself (N−: package-level, fold not discharged) | proved |
| `closedQuote_reflects`, **`towerValued_self`** (repair r1; audit r1 adversarial N1) | FAF `lic_expected_future_expectations_closed`; F13 | FAF's closed `cee` quote of any e.c. `X` reflects the self-expert's estimate; **`TowerValued` holds for the self-expert over `paperDP T` at every deferral, with no hypothesis** (closed `cee` at FAF's own quote, moved to any reflecting `Y` by `expect_reflects_congr`) | L / N+ | exact (`TowerValued`, not `Tower`) | — | itself: the real construction, no fold, no pull-back | proved |
| `softTotalTrustAbove_self_of_folds`, `softTotalTrustBelow_self_of_folds`, `condTower_self_of_folds`, `value_self_of_selfEndorses` | audit r1 adversarial N1 | T4 (both halves), T3 and T2 for the self-expert over `paperDP T` with only the fold / self-endorsement clause left as a hypothesis | L | exact | (b) `ExpertFoldsAt` / `ExpertFoldsCond`; (c) `SelfEndorses` | partial: the folds (F8) / `SelfEndorses` (`def-argmax-value`) | proved |
