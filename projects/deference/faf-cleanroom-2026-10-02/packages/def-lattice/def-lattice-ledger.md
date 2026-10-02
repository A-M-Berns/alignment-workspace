# def-lattice — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Found.DefLattice.` omitted (`TwoOptionFinite.` and `Witness.` are sub-namespaces). A definitions foundation: kinds are `D`/`L` with five `C` rows (T6d) and the `N` rows; nothing is `P` (`plan` §0.4). "Hyps (b)/(c)" lists only non-(a) hypotheses; "—" means every hypothesis is (a) or there is none. Witness column: the N+ instance in `Witness.lean` that inhabits the row's hypothesis package, where one applies. Status `proved` throughout; no `open`, no `refuted`, no `flagged` (the one substantive correction, finding F3, is recorded as a `variant` fidelity on the T6d rows, not as a refutation of a source). **Repair round 1 (2026-09-30):** the T6d headlines are restated with the menu-local Value instance as hypothesis (audit B1; global-`Value` forms kept as `_of_value` corollaries); the `BoundedSequence` side conditions `hbdd`/`hbddC` are discharged from code certificates, so every T6d hypothesis is now (a); `ArgmaxClosed` takes a `M.Valued DP` guard (N1); `lemma71_twoOption` is renamed `twoOption_value_imp_above_frame` (item 6/N9); `no_generable_hard_indicator` is restricted to `[0,1]`-valued histories (stronger; item 7/N4). Status on rows whose hypothesis package has no N+ inhabitant here reads `proved (witness partial: …)` in STANDARDS §6's vocabulary (item 2).*

## T1 — the expert, reflection, the quote packages (`Expert.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Expert` | `deference-notions` §Setting; `expert-conditions`; v6 §0.4 | the expert is a history `A` + deferral `f` + `[0,1]` range; estimate of `X n` is `(X n).expect A (f n)` | D | variant: deferred-day estimate only (F1) | — | `Expert.self` over `liaHistory (paperDP T)` (`Witness.lean`) | proved |
| `Expert.estimate` | `setting-and-notation` §Corner quotes | `E*(X_n)` as a real | D | exact | — | — | proved |
| `Expert.self` | v6 §0.4 instance 1 | the future self `E^H_{f(n)}` (`A = P`) | D | exact | — | `instPaperLIA` | proved |
| `Reflects` | `deference-notions` §Mart; FAF `ExpectedFutureExpectationQuote.reflected` | `Y` is `⌜E*(X)⌝`: every consistent world values `Y n` at `E*(X n)` | D | exact | — | — | proved |
| `Reflects.of_expectedFutureExpectationQuote` | FAF `thm:cee` package; mandate T1 | FAF's `cee` package reflects for the self-expert | L | exact | — | (FAF's closed `cee` packages, not built here) | proved |
| `Valued` | `setting-and-notation` §LUV; FAF `source_valued` | every consistent world values `X n` | D | exact | — | `literalIndicator_valuesAt` | proved |
| `rampAbove`, `rampBelow`, `hardAbove`, `hardBelow`, `bandWt`, `hardBand` | `deference-notions` §Total Trust; v6 §1.6; DDB l. 175/180; `reflection-in-li` | the six weight functions of record | D | exact (`ctsInd δ y t` is v6's `Ind_δ(y > t)`) | — | — | proved |
| `WeightQuote` | `deference-notions` §Total Trust; FAF `ConditionalExpectationQuote`/`SelfTrustQuote`; mandate dd. 3–4 | weight LUV reflects `wt(E*(X))` exactly; product LUV within vanishing slack; both e.c.; source valued | D | variant: product within FAF's slack (disclosed) | — | `weightQuoteWitness` (slack `≡ 0`) | proved |
| `CondQuote` | `deference-notions` §The conditional tower; FAF `ConditionalExpectationQuote` | the `ccee` quote pair minus `affine` | D | variant: weight at `w (f n)`, slack (F2, F14a) | — | (FAF's closed `ccee` packages) | proved |
| `CondQuote.of_conditionalExpectationQuote` | FAF `thm:ccee` package; mandate T2 | FAF's `ccee` package is a `CondQuote` for the self-expert | L | exact | — | — | proved |
| `literalIndicator` (+ `_isIndicator`, `_valuesAt`, `_expect`, `_machineThresholdCodeSeq`) | FAF `LUV.indicatorOf`; mandate T1 | indicator with threshold sentence `φ` itself; expectation is exactly the price; e.c. from sentence codes | D/L | exact | — | `witnessSource` | proved |
| `WeightQuote.of_selfTrustQuote` | FAF `SelfTrustQuote`; mandate T1 | FAF's `st` package at constant `δ`, `s` is a ramp `WeightQuote` with `slack ≡ 0` for the literal-indicator source | L | exact (for `literalIndicator`; F4 for `indicatorOf`) | — | `weightQuoteWitness` | proved |

## T2 — Tower and the conditional tower (`Notions.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Tower` | `deference-notions` §Mart; v6 §1 table | for every e.d. `X`, `Y` reflecting `E*(X)`: `E^H_n(X_n) ≈ₙ E^H_n(Y_n)` | D | exact (F1) | — | (hypothesis-notion; self-instance is `def-self-trust`'s) | proved |
| `CondTower` | `deference-notions` §The conditional tower; v6 §1.5 | for every e.d. `X`, P-generable `[0,1]` weight `w`, and `CondQuote` pair: `E^H_n(Z_n) ≈ₙ E^H_n(Z'_n)` | D | variant: `w (f n)`, slack (F2, F14a) | — | (as above) | proved |

## T3 — Total Trust in product form (`Notions.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThresholdIneqAbove` / `ThresholdIneqBelow` | `deference-notions` §Total Trust; mandate dd. 5 | `E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` (resp. `≲ₙ`) for every e.d. source and weight quote at `wt` | D | exact (unnormalized) | — | `softTotalTrustAbove_package_inhabited` (the *above*-ramp package only; no `WeightQuote` at `rampBelow`, `hardBelow`, `bandWt` or `hardBand` is shown inhabited here — N2) | proved |
| `soft_above_iff_unnormalized` / `soft_below_iff_unnormalized` / `thresholdIneq{Above,Below}_iff_unnormalized` | mandate T3 | product form ⟺ `E^H_n(XW_n) ≳ₙ s·E^H_n(W_n)` | L | exact | — | — | proved |
| `SoftTotalTrustAbove` / `SoftTotalTrustBelow` | `deference-notions` §Total Trust (display); v6 §1.6; `centered-bet-squeeze` §0 | the threshold inequalities at the ramp weights (content-free at `δ = 0`; fixed-width headlines take `0 < δ`) | D | exact | — | `weightQuoteWitness` (Above only — N2) | proved |
| `TotalTrust` (= `SoftTotalTrust`) | `deference-notions` §Total Trust | both soft cuts at every rational `s`, every `δ > 0` | D | exact (soft grade) | — | (hypothesis-notion) | proved |
| `HardTotalTrustAbove` / `HardTotalTrustBelow` / `HardTotalTrust` | DDB l. 175, 180 | DDB's hard cut in product form — comparison object, never a hypothesis | D | exact | — | — | proved |

## T4 — Value (`Menu.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Menu`, `Menu.Valued`, `Menu.quote`, `Menu.maxQuote` | `deference-notions` §Shared apparatus; v6 §1 | e.d. menus of `k+1` options; the quotes `m^j_n` and `M_n` | D | exact | — | `twoOptionMenu` | proved |
| `Menu.argmax` (+ `argmax_attains`, `argmax_le`, `argmax_eq_zero_iff`, `argmax_two`) | `deference-notions` §Shared apparatus ("least index"); `ledger-decided-tie-breaks` | the least index attaining the max; on two options, `0` iff `m^1 ≤ m^0` | D/L | exact | — | — | proved |
| `Follows` | `deference-notions` §Shared apparatus (`Ŝ_n := O^{j*(n)}_n`) | `S n` takes the selected option's world value in every consistent world | D | exact (reflection form) | — | (needs a quote-referencing LUV; `partial: needs li-quote-lane's ledger` for an N+ instance) | proved |
| `Value` | `deference-notions` §Value and its ⚠ scope note; v6 §1 table | for every `k`, e.d. world-valued menu, e.d. follower `S`, and `i`: `E^H_n(S_n) ≳ₙ E^H_n(O^i_n)` | D | exact (unconditional; scoped form is `def-argmax-value`'s) | — | (hypothesis-notion) | proved |
| `BlendQuote`, `BlendValue` | `soft-self-endorsement`; `deference-notions` §Terminological default | δ-hedged Value: `S` reflects `∑ blend(m_n)_j · x_j` within slack | D | variant: slack (dd. 3) | — | — | proved |
| `softmaxBlend` (+ `_denom_pos`, `_sum`), `rampPhi`, `rampBlend` (+ `one_le_rampPhi_sum`, `rampBlend_sum`) | v1 §3 (root-deference-064); `soft-self-endorsement` | the two blends; no junk division (denominators `> 0`, `≥ 1`) | D/L | exact | — | — | proved |

## T5 — Reflection (`Notions.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `BandReflection` (+ `bandReflection_iff_pinch`) | `reflection-in-li` §The value form; `deference-notions` §Reflection ⚠ re-scope | for all `s`, `ε > 0`, `δ > 0`: `(s − ε)·E^H_n(b_n) ≲ₙ E^H_n(X_n b_n) ≲ₙ (s + ε)·E^H_n(b_n)` at the band weight | D/L | exact (unnormalized) | — | (hypothesis-notion; F15: this run's identification, ATTRIBUTION-UNVETTED) | proved |
| `HardValueReflection` (+ `hardValueReflection_iff_asympEq`) | `reflection-in-li` §Exactness; LI 4.12.4 discussion | `E^H_n(X_n·1[E*(X_n) = s]) ≈ₙ s·E^H_n(1[E*(X_n) = s])` — the refuted exact object | D/L | exact (stated to be refuted elsewhere) | — | — | proved (as a definition; refutation is `def-squeeze-diamond`'s) |

## T6 — the two-option identity (`TwoOptionFinite.lean`, `TwoOptionLUV.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `TwoOptionFinite.twoOptionStrategy` | `two-option-value-iff-total-trust` §Statement | `Ŝ w = if s ≤ e w then X w else s` | D | exact | — | — | proved |
| `TwoOptionFinite.twoOption_identity_above` / `_below` | `two-option-value-iff-total-trust` §Statement (boxed); v6 §1.2; lean-deference-007 | `∑ π Ŝ − s ∑ π = ∑ π (X − s) 1[s ≤ e]`; `∑ π Ŝ − ∑ π X = ∑ π (s − X) 1[e < s]`, exactly | L | exact | — | (no hypotheses) | proved |
| `TwoOptionFinite.twoOption_value_iff_above` / `_below` / `twoOption_value_all_iff` | same | Value against the constant ⟺ above cut; against `X` ⟺ below cut; quantified over all `(X, s)` | L | exact | — | (no hypotheses) | proved |
| `TwoOptionFinite.frameEstimate`, `twoOption_value_imp_above_frame` (was `lemma71_twoOption`), `frame_twoOption_value_iff` | DDB Lemma 7.1 (transcription ll. 480–496); v6 §1.2 | on a finite frame, two-option Value against `s` ⟹ `0 ≤ ∑ π (X − s) 1[E(X) ≥ s]` (LitDdbFrames's `TotalTrust` body) — the one-strategy instance Lemma 7.1 uses, not the lemma (Weak Value over all recommended strategies with the spectral-gap `s`) | L | weaker: one strategy, one direction (F8) | — | (no hypotheses) | proved |
| `twoOptionComb` (+ `_expect`, `_value`) | `two-option-value-iff-total-trust` §Soft/LI form; mandate T6c | the hedged strategy `s + XW − s·W` as a `LUVCombination`; its expectation is `E(XW) + s − s·E(W)` by definition | D/L | exact | — | `witness_twoOption_value` | proved |
| `twoOptionComb_value_iff_productForm` | same; mandate T6c | `E^H_n(twoOptionComb) ≳ₙ s` ⟺ product form of `ThresholdIneqAbove` (F6: `hLoe` dissolved) | L | exact | — | `witness_twoOption_value` | proved |
| `twoOptionComb_value_of_softTotalTrustAbove` | same | soft TT above at `(s, δ)` ⟹ Value against the constant on every hedged menu | L | exact | — | `weightQuoteWitness` | proved |
| `twoOptionMenu`, `HardTwoOptionData`, `hardSelectionComb`, `singleComb`, `worldValue` | mandate T6d | the menu `{X, C}`; the hypothesis package (reflection clauses + code certificates for `X, C, S, W, XW` — `codes_W`/`codes_XW` added in repair round 1); the identity combination valued `0`; the canonical world valuation | D | exact | — | — | proved |
| `hardSelectionSyntax`, `hardSelectionComb_boundedSequence`, `singleCombSyntax`, `singleComb_boundedSequence` (+ `hardSelectionCoeff`, `hardSelectionLuv`, the two code lemmas, the two `l1Norm` lemmas) | audit r1 fidelity item 1 / N5; FAF `LUVCombinationSyntax`, `BoundedSequence` | compact syntax and `BoundedSequence` for the two T6d combinations, from the code certificates alone (`l1Norm = 2|s| + 2`, resp. `1`) — the side conditions `hbdd`/`hbddC` discharged; FAF API request: a constant-coefficient `LUVCombinationSyntax` constructor over `MachineThresholdCodeSeq` sources | D/L | n/a | — | — | proved |
| `HardTwoOptionData.followed_valuesAt`, `.worldValued`, `.value_eq_zero` | `two-option-value-iff-total-trust` §Proof | `S n` is valued `if q_n ≤ E*(X_n) then x else s`; the identity combination is world-valued and valued `0` (derived, no (b)/(c)) | L | exact | — | — | proved |
| `HardTwoOptionData.expect_followed_asympEq` / `.expect_const_asympEq` | mandate T6d; FAF `thm:expprovind` | `E^H(S) ≈ₙ E^H(XW) + s − s·E^H(W)`; `E^H(C) ≈ₙ s` | C | exact | — (all (a) since repair round 1) | none for `S` (needs `li-quote-lane`'s ledger) | proved (witness partial: needs li-quote-lane's ledger) |
| `value_twoOption_hardAbove` | `two-option-value-iff-total-trust` §Statement; mandate T6d | the **per-menu** Value instance `E^H(S) ≳ₙ E^H(C)` on `{X, C}` ⟹ `E^H(X·1[q_n ≤ E*(X)]) − s·E^H(1[q_n ≤ E*(X)]) ≳ₙ 0` at the expert's quote `q_n = E*(C_n)` | C | variant: threshold at `q_n`, not `s` (F3); hypothesis menu-local (stronger than the mandate's `Value → …`, audit B1) | — (`hworld` (a), caller obligation) | none (no `Follows`-satisfying `S` built here; not faked with a constant expert) | proved (witness partial: needs li-quote-lane's ledger) |
| `value_twoOption_hardAbove_of_value` / `value_twoOption_hardBelow_of_value` | mandate T6d (the literal `Value → …` shape) | the global predicate `Value P DP E` instantiated once at `{X, C}` gives the two faces — vacuous wherever unconditional Value fails (inductor-experts, per the corpus) | L | exact (instances of the local forms) | — | as above | proved (witness partial: as above) |
| `value_twoOption_hardBelow` | same | the per-menu Value instance against `X` ⟹ the below cut with complementary weight `1 − W` | C | variant (F3); menu-local | — | as above | proved (witness partial: as above) |
| `value_twoOption_hardAbove_of_weightQuote` | mandate T6d (the literal claim) | under the surrogate `E*(C_n) = s`, a hard `WeightQuote` with `slack ≡ 0` and the per-menu Value instance give `ThresholdIneqAbove`'s conclusion at `s` | C | exact under `hsur` | **(c)** `hsur` (surrogate coherence; F3) | as above | proved (witness partial: as above) |

## T7 — the common closure class (`BetClass.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `BetClass`, `BetClass.univ`, `BetClass.inter` | lean-deference-072; v6 §1.2 | a set of e.d. LUV sequences; the universal class; intersections | D | variant: LUVs, not combinations (report §T7) | — | `univ` | proved |
| `rampWeights`, `bandWeights`, `WeightClosed`, `RampClosed`, `GapClosed`, `ConstClosed`, `ArgmaxClosed`, `IsDeferenceClass` | lean-deference-072 (msg 68); `value-implies-tower`; `tower-implies-total-trust` | the four closures in reflection form, universally: every quote/product/follower of members with codes is a member (`ArgmaxClosed` over *world-valued* menus only — the `M.Valued DP` guard added in repair round 1 matches `Value`/`ValueOn`; without it one unvalued member forced every e.d. sequence into the class, N1) | D | exact (universal form; report §T7) | — | `univ_isDeferenceClass` | proved |
| `IsDeferenceClass.inter` | mandate T7 | intersections of deference classes are deference classes | L | exact | — | — | proved |
| `generated` (+ `subset_generated`, `generated_subset`, `generated_isDeferenceClass`) | mandate T7 | the least deference class containing an e.d. base | D/L | exact | — | — | proved |
| `TowerOn`, `ThresholdIneqAboveOn`, `ThresholdIneqBelowOn`, `ValueOn` (+ `_univ_iff`, `.mono`) | `deference-notions` §Value ("domain-relative"); v6 §5.11 | the notions restricted to a class; on `univ` they are the unrestricted ones; antitone in the class | D/L | exact | — | — | proved |

## T8 / N rows

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `no_generable_hard_indicator` | vq-wiki-028; `setting-and-notation` §Market-generable weights | no `EF` denotes `1[1/2 ≤ P n φ]` on all `[0,1]`-valued histories (`EF.continuous_denote`; strengthened from all real-valued histories in repair round 1) — the same-day trade-weight reading; whether the deferred-day step *sequence* fails `PGenerableRat P` is not settled (N4) | N- | exact | — | — (certifies the encoding; exercises no inductor) | proved |
| `Witness.selfTrustQuoteWitness` | FAF `selfTrustQuoteOfRepresentation`; mandate T6 | FAF's complete `st` package over `liaHistory (paperDP T)`, atom source, constant `δ > 0`, `s ∈ [0,1]` (the atom source `⌜aₙ⌝` exercises the *shape* of an e.c. source, not arithmetic content — not to be cited as evidence that Total Trust is non-trivial on interesting bets; item 11) | N+ | n/a | — | self | proved |
| `Witness.weightQuoteWitness` (+ `_slack`) | mandate T6 | the ramp `WeightQuote` for the self-expert with `slack ≡ 0`, projected from FAF's package | N+ | n/a | — | self | proved |
| `Witness.witnessSource_nonconstant`, `Witness.witnessSource_injective` | mandate T6 ("the witness varies with `n`") | the source is not a constant sequence; pairwise distinct across days (`Formula.atom` injective; the second added in repair round 1, N10) | N+ | n/a | — | self | proved |
| `Witness.softTotalTrustAbove_package_inhabited` | mandate T3 | `ThresholdIneqAbove`'s hypothesis package at the ramp weight is inhabited over a real inductor | N+ | n/a | — | self | proved |
| `Witness.witness_selfTrust_productForm` | FAF `lic_self_trust`; `deference-notions` §Total Trust (self-instance = `st`) | `E^H(XW) − s·E^H(W) ≳ₙ 0` over the paper's inductor | N+ | exact | — | self | proved |
| `Witness.witness_twoOption_value` | `two-option-value-iff-total-trust` §Soft/LI form; mandate T6 | the closed `st` conclusion is Value against the constant on the hedged two-option menu | N+ | exact | — | self | proved |
