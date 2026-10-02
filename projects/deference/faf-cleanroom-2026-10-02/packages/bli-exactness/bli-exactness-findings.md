# `bli-exactness` — findings about the sources

Findings in the register of [STANDARDS](../../STANDARDS.md) §5: errors, ill-posed claims, gaps and imprecisions in the sources this package formalizes, each with a severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. Lean names are in `Cleanroom.Bli.BliExactness` unless qualified. Written by the formalizer (Claude Fable 5.1, [scrubbed], 2026-10-02); the reading of what a person *meant* is marked ATTRIBUTION-UNVETTED where it is one.

## F1 — Soto's PC-LIC (PDF 05 Def 5) has no inhabitant · **blocking the note's conclusion**

Pointer: `research/references/bli/soto-2023/Soto 2023 - 05 Definitions.pdf` Defs 2, 4, 5; `bli-soto-a-inventory` 038/040/041; `bli-soto-a-2-inventory` 001.

Def 2 as printed: `A(T_{≤n}, P_{≤n}, n) := ∑_{i≤n} ( P_i(T_i[c]) + ∑_φ T_{i−1}[φ]·P_i(φ) )`. The round-`i` cash `P_i(T_i[c]) = −∑_φ T_i[φ]·P_i(φ)` is credited on day `i`, the round-`i` *position* is valued only inside the day-`(i+1)` summand, and the current position is never marked to market. Consequence, proved in Lean: the trader selling `n+1` tautology shares on day `n` has `A = n + 1` against **every** PC-market (`WorldMarket.A_topShorter`; only `price P ⊤ = 1` is used), so it PC-exploits every market (`WorldMarket.topShorter_pcExploits`) and Def 5 is empty for every trader class containing it (`WorldMarket.pclic_empty`). Conjectures 1–2 and Theorem 1 of PDF 05, stated over the literal `A`, are therefore vacuous or false as printed; they were **not** formalized over the literal definition (the program's named failure mode for row X5).

Repair (bli-soto-a-2-001, adopted here as the definition of record `WorldMarket.A'`): `A′(n) := A(n) + ∑_φ T_n[φ]·P_n(φ)` — mark the round-`n` position to the current prices. Then the `⊤`-shorter has `A′ ≡ 0` (`A'_topShorter`), `A′` telescopes to `∑_{j<n} ⟨T_j, P_{j+1}∘π − P_j⟩` (`A'_telescopes`), and "no profit whatever `P_{n+1}` is" is exactly Soto's `B(W) ≤ 0` at every vertex (`noProfit_iff_benefit_nonpos`, PDF 05 Thm 2's `B(W)`). Soto's prose under Def 2 ("every round the trader sells all their shares, receiving their new prices as payment for them … each trader is trying to predict the next market state") describes a trader that is always flat, which is `A′`'s accounting; that the slip is in the formula rather than the intent is ATTRIBUTION-UNVETTED.

Nearest well-posed versions of the vacuous items: Conjecture 1 (PC-LIC ⟺ LIC under the world projection) becomes bli-soto-a-2-002's two open questions over `A′`; both remain open here (§ Open below and `bli-exactness-open`).

## F2 — `bli-found`'s `D_NNU` guard is vacuous on day 1 · **imprecision**

Pointer: `Cleanroom/Bli/BliFound/Constraints.lean` `D_NNU`; mandate Known issue 4.

`D_NNU quoteAt cells ε Q` requires the identity only when every quote `quoteAt (n+1) φ I` is small on day `n` (`SmallOn n`, token size `≤ sizeBound n = 2^{2^n}`). `sizeBound 1 = 4`, while every interval quote is a conjunction of an atom and a negated atom, of token size `≥ 11` (`not_smallOn_one_quoteAt`). So the day-1 clause of `D_NNU` holds for **every** history whenever the day-2 cell family is nonempty (`d_nnu_day1_vacuous`). The day at which the guard first bites depends on the digit length of the quotation atoms' codes (`Nat.pair 2 ⟨⌜pos⌝, ⌜neg⌝, ⟨code, ⟨⟨m, ⌜φ⌝⟩, ⌜r⌝⟩⟩⟩⟩`, astronomically large), and was not computed (`stretch` X3′, not done). Consequence for this package: X3's witness violates the **unguarded** `ExactNNUAt` (the body of `D_NNU` at `ε = 0` without the guard); `ExactNNU` implies `D_NNU` at `ε = 0` (`ExactNNU.d_nnu`), not conversely. Recommendation for `bli-found`: either state D-NNU unguarded over the quote cells (the guard only protects the small-sentence budget, which the cells — being about `𝑸`'s own prices — do not need) or document that the guarded form says nothing on early days.

## F3 — The LIA's zeros make the exact identities hold trivially off its support · **imprecision** (desiderata P11)

Pointer: `bli-program-desiderata` P11 ("or take the LIA itself"); FAF `RationalBeliefState.quote_eq_zero_of_not_mem`; `bli-exact-base` `LiaSupport`; mandate Known issue 5.

`liaHistory DP n ψ = 0` for every `ψ` outside the finite day-`n` support `liaStates DP n`. At such coordinates the product identities `P_n(φ ⋏ χ) = mid·P_n(χ)` and `∑ mid·P_n(χ_I) = P_n(φ)` read `0 = 0` and are satisfied for free, so the LIA itself cannot witness a *violation* there; a violation needs a sentence the market actually prices. X3's finite-support perturbation (`x3History`) is therefore essential, and P11's alternative "take the LIA itself" is not a route to the witness. (Whether the LIA violates the exact identities *on* its support at some finite day is not settled here; the perturbation sidesteps the question.)

## F4 — bli-paper-2-008's displayed product form has a day index wrong · **presentation**

Pointer: `research/references/bli/understanding-trust/udt-tiling-working-notes-2025-06-30.md` line 5, b.273: `P_n(x ∧ P_{n+1}(x = c)) = c · P_{n+1}(x = c)`.

The right-hand side must be a **day-`n`** price of the quoted future-price sentence: `c · P_n(⌜P_{n+1}(x) = c⌝)`. As printed the right side is a day-`(n+1)` price, which the day-`n` market cannot know. The definition of record `ExactReflection` (`Defs.lean`) uses the corrected form, at interval resolution: `P_n(φ ⋏ ⌜lo < 𝑸_m(φ) ≤ hi⌝) = mid(lo, hi)·P_n(⌜lo < 𝑸_m(φ) ≤ hi⌝)`.

## F5 — The midpoint representative makes exact reflection "self-trust up to the cell width" · **imprecision** (bli-soto-b-025's flag, disclosed)

Pointer: Soto PDF 20 p. 1–2 (the `(m+0.5)/2^{k+1}` bundle); `bli-soto-b-inventory` 025.

Every exact predicate of this package (`ExactReflection`, `ExactSelfTrustX`, `ExactNNUAt`) uses the cell midpoint `mid I` as the representative of "`𝑸_m(φ) = p`" on the cell `I`. So the identities are exact *about the midpoint*, i.e. self-trust up to half the cell width, exactly as bli-soto-b-025 flags for Soto's `n = 1` bundle market. This is the right object for a finite-resolution market and is disclosed in every docstring; the point-value form `P_n(φ | P_m(φ) = p) = p` is the `lo = hi` degenerate case, which `quoteAt`'s `(lo, hi]` convention makes the empty cell — so the desiderata's single-price D-ST-x has no faithful `quoteAt` rendering and the package's object is the interval/midpoint variant, nothing stronger.

**Consequence (audit r1, both lenses; more than "imprecision" for the liar theorems).** Under theory-respect, a sentence the completed theory *decides* has conditional probability `0` or `1` on every cell (`decided_conditional`), so *midpoint*-exactness fails for it at every cell with interior midpoint — for `⊤` exactly as for the liar (`decided_fails_midpoint`, `top_fails_midpoint`). A midpoint-form liar theorem therefore carries no self-reference. Repair round 1 restated X1 (a)/(b) in the **interval form** "the conditional lies outside the cell", which `⊤` does *not* satisfy at a cell reaching `1` (`top_exact_interval`) and the liar fails at every one-sided cell; the former "FAF strengthening" `exact_reflection_fails_liar_cell` is demoted to `liar_midpoint_fails_any_cell` (Kind L, the F5 artifact at a decided sentence).

**Consequence 2 (audit r2, both lenses; severity for the exact *predicate*: local error — see F15).** The same artifact caught X3 and the definition of record. Repair round 1's X3 table was interval-exact at its headline cell (conditional `½ ∈ (0, ½]`), so its "violations" were of the midpoint only; repair round 2 retabled it to a point mass violating both forms and made the **interval forms** `ExactReflectionInterval`/`ExactNNUAtInterval` the refuted objects of record (midpoint ⟹ interval on non-degenerate cells, `ExactReflection.interval`/`ExactNNUAt.interval`). And the midpoint predicate over *every* sentence is not merely imprecise: it has no inhabitant coherent at `⊤` with positive mass on any cell of midpoint `≠ 1` (`coherentTop_forces_zero`), i.e. on any family inside `[0, 1]` it is satisfied only by `⊤`-incoherent valuations — F15. The interval form asks only that `⊤`'s cells with `hi < 1` carry no mass (`coherentTop_interval_below_cell`).

## F6 — Under the `(lo, hi]` convention the liar's threshold lies in no one-sided cell · **imprecision** (Known issue 6)

Pointer: slide 40 (`L := ℙ_m(L) < ½`); `bli-found` `quoteAt` ("`lo < 𝑸_m(φ) ≤ hi`"); `Liar.lean`.

The slide's two-case argument needs the partition event to lie entirely on one side of the threshold `p`: cells `(lo, hi]` with `hi < p` entail `L`, cells with `p ≤ lo` entail `∼L`. The point `p` itself is in neither kind (a cell `(lo, hi]` with `lo < p ≤ hi` straddles in the truth-value sense, since `L ↔ q < p` is false at `q = p`). So if the market's day-`m` quote of the liar is **exactly** `p`, no completed-theory world holds any one-sided cell and the one-sided theorem `exact_reflection_fails_liar` has no world-mixture witness at that `(m, p)`; `liar_oneSided_witness_of_ne` carries the hypothesis `q ≠ p`, which is intrinsic to one-sidedness (not to the failure). (Whether a completed-theory world can hold the boundary literal "`q > q`" is not even decided by FAF's `RationalQuoteCode` interface, which fixes the two strict sides only — `ValuesAt`'s boundary is free.)

**Register, corrected in repair round 1** (audit r1 adversarial N1, fidelity B1). The earlier text here said the straddling caveat "disappears over the real diagonal". What is true: under respect for the **completed** theory (which knows the day-`m` price on day `n`), the liar is decided, so the *midpoint* identity fails at every cell with interior midpoint (`liar_midpoint_fails_any_cell`) — but that is F5's artifact and holds for `⊤` too, so it is not a liar result; and the *interval* claim does **not** extend to straddling cells (at `(lo, 1]` with `lo < q < p` the liar's conditional `1` lies inside the cell). Under stage-provable respect the caveat stands as the slide states it. A related convention artifact: inside `[0, 1]` the `(lo, hi]` cells contain no `0`, so a *false* decided sentence fails interval-exact reflection at every cell of the family — the liar's interval failure at one-sided cells is not of this kind (`top_exact_interval` is the encoding check).

## F7 — Soto's exact-introspection obstruction is the sharp fixed point, not `bli-exact-base`'s convex one · **presentation** (Known issue 9)

Pointer: Soto PDF 07 p. 4–5 "Introspection"; `bli-soto-a-inventory` 058 (ii); `Cleanroom/Bli/BliExactBase/Obstruction.lean` (its docstring already says so).

PDF 07's "this will constitute a discontinuity of the `fix(V)` function, and so we won't be able to find a fix-point" is, at the level of a single price, `no_sharp_fixed_point`: `x = 𝟙(x < p)` has no real solution (`Abstract.lean`). Over FAF the market-level content is `lia_never_exact_on_liar`: on every day the LIA's price of its own liar differs from the liar's truth value in every completed-theory world. `bli-exact-base`'s `Obstruction.obstruction` is a *different* constraint (per-day constrained market-maker search for exact cell-NNU) and is cited, not duplicated. Soto's syntactic point (058 (iii): the self-referential sentence lacks its own numeral) is moot over FAF, whose `BooleanQuoteCode.sentence` *is* an atom whose truth the theory reflects.

## F8 — bli-soto-a-036 (i): the three readings of "`P_n` has learned `Q_n = Q̂`" · **imprecision**

Pointer: Soto PDF 04 p. 5 and footnote 3; `bli-soto-a-inventory` 036 (i).

"Updating on having observed the prices" can mean (α) probability-1 conditioning at day `n` on the quoted same-day price (the reading on which `φ := “Q_n(φ) = 0.5”` with `Q_n(φ) = 0.7` forces `P_n(φ) = 0`); (β) conditioning at a later day `m > n` on the day-`n` price; (γ) the deductive process eventually containing the quoted fact. Reading (α) is the same-day exact introspection that the liar refutes for the quoting market itself (`lia_never_exact_on_liar`) and that FAF's LIA satisfies only in the `ε_n` band (`lic_introspection_closed`) — so (α) is consistent with constraint 1 (`P_n = Q_n` on small sentences) only if `Q_n` itself is exactly introspective, which no market is about its own liar. Readings (β)/(γ) are the ones BLI uses (future states, `bli-trajectory`'s `Reflection`; `quoteAt`'s atoms entering `paperDP T`). The Appendix B "final detail" needs (β) or (γ), not (α). Footnote 3's "`φ := “P_n(φ) = 0”` has no fixed point" is `no_zero_indicator_fixed_point`.

## F9 — bli-soto-a-033: finite-time coherence is syntactic · **presentation** (recorded only)

Pointer: Soto PDF 04 pp. 3–4; `bli-soto-a-inventory` 033.

The remark that identifying at every finite round all sentences provably equivalent to a syntactic constraint would decide arbitrary sentences is an undecidability remark (the set of provably-equivalent pairs of an r.e. consistent theory extending `𝗥₀` is not decidable); no theorem was attempted. Its operative consequence for this package is that theory-respect is stated on the *two sentences actually used* (`RespectsEntailment`) rather than on an algebra (`CoherentOn`, Known issue 3): the former is what a finite-time market can be asked for, and the latter is satisfied by no finite perturbation of the LIA (`bli-exact-base` `Tables.not_coherentOn_of_finiteSupportPerturbation`).

## F10 — bli-soto-a-010, bli-soto-a-030 · recorded only

010 (epistemic self-trust "from the beginning", the desideratum) is the definition of record `ExactSelfTrustX`; its exact finite-time form is what X3 shows no inductor is guaranteed and X6 (v) shows implies the smoothed theorem. 030 (July's Desideratum 9) was retracted by the author in the August version; nothing to formalize.

## F11 — X7's sentence (bli-paper-2-013 (b), bli-paper-2-012) · the finding this package adds

Pointer: `udt-tiling-working-notes-2025-06-30.md` b.415–422, b.390–402; `Accuracy.lean`.

Over the finite trajectory prior, with constraint 2 identifying `P(φ | 𝑸_{m+1} = Q)` with `Q φ` and constraint 4 (`Balanced`) supplying `∑_Q F Q·Q φ = t φ`: the expected Brier error of the *future* price is the current error minus the kernel's variance of its own next price (`accuracy_gap`, `accuracy_gap_eq_var`), hence never larger (`futureErr_le_currentErr`), equal iff the next price is almost surely the current one (`accuracy_gap_eq_zero_iff`); the tent kernel has a strictly positive gap at every interior coordinate (`tent_gap_pos`), B0's point mass has gap `0` (`b0_gap_zero`).

**Register (corrected in repair round 1, audit r1 fidelity N3).** The identity is the law of total variance for a balanced kernel: a textbook Bayesian *also* expects her posterior to score better than her prior under her prior, and b.417's "the prior minimizes the expected error" is about forecasts available *now*. So the headline is: **"trust your prior" holds exactly for the degenerate solution and fails exactly when the kernel is uncertain about its own next price — in b.419's sense that the agent can already describe the better forecast (its own next price) and prefer it**, by the kernel's variance of that price. That this is "bli-paper-2-013 (b) made precise" is a claim about the note's intent: ATTRIBUTION-UNVETTED (the inventory marks 2-013 (b) as its writer's own formulation, "not in the source"); bli-paper-2-012's "variability" quantified as `priceVar` is this package's reading. The LI form over `liaHistory` (b.415's agent being an inductor) was not attempted (`stretch`; report).

## F12 — bli-soto-b-052: LI-paper → FAF notation map (one table)

| LI paper / journal | FAF | this package |
|---|---|---|
| `ℙ_n(φ)` (market price) | `P n φ` for `P : History`; the constructed market `liaHistory (paperDP T) n φ` | same |
| `𝔼_n(X)` for a LUV `X` | `(X : LUV).expect P n` | `nnu_asymptotic`, `self_trust_smoothed_const` |
| `𝟙(φ)` | `v.payout φ` in a world; as a LUV factor `indicatorProductLUV` | — |
| `Ind_δ(x > y)` | `ctsInd δ x y` (`Properties/SelfTrust.lean`) | `exactSelfTrustX_imp_smoothed` |
| `f(n) > n` deferral | `DeferralFunction` (`.f`, `.lt`), `succDeferral` | `nnu_asymptotic_atoms_succ` |
| e.c. sentence sequence | `MachineSentenceCodes φ` | `machineSentenceCodes_atom` |
| e.c. rational sequence / `ℙ`-generable | `MachineRatCodes` / `PGenerableRat P p` | `MachineRatCodes.const`, `PGenerableRat.ofMachineRatCodes` |
| `⌜ℙ_{f(n)}(φ_n)⌝` as a LUV | `(paperFutureQuoteCode T f φ hφ).luv n` | `nnu_asymptotic` |
| "`ℙ_m(φ) ∈ (lo, hi]`" as a sentence | `bli-found` `quoteAt T m φ lo hi` | `liarCell`, `x3CellLo`/`x3CellHi` |
| the liar `L := ℙ_m(L) < p` | `(paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m` | `liar T p m` |
| `≈ₙ`, `≳ₙ` | FAF's asymptotic relations (`Framework/Foundations`) | X6 rows |

## F13 — bli-slides-044 (cross-reference only)

Existence of an *exactly* propositionally coherent logical inductor is the OPEN pair `exactlyEnforceable_allDays`/`worldMarket_exists` owned by `bli-exact-base`; this package neither claims nor needs it (its witnesses are one-world point masses and a finite perturbation of the LIA).

## F14 — The mandate's prescribed shape for `ExactReflection` (every rational cell) is over-strong · **local error** (in the mandate, not in a source; found by audit r1, both lenses)

Pointer: `bli-exactness-mandate` § Definitions ("`∀ φ lo hi`"); `Defs.lean` `ExactReflectionAllCells`, `exactReflectionAllCells_zero_on_negative_mid`.

Quantifying the midpoint identity over *every* rational cell `(lo, hi)` — cells outside `[0, 1]`, overlapping cells of different widths — makes the predicate collapse for reasons unrelated to the liar: a nonnegative history satisfying it has mass `0` on every cell with negative midpoint (proved), and `(−3, 1]` at `quoteAt T` is a sentence every completed-theory world holds; the fidelity auditor's probe further shows additivity over `(−1, 0]`, `(0, 1]`, `(−1, 1]` forces mass `0` on `(0, 1]`. No source states this shape: slide 40 quantifies over point values, Soto's bundle market (PDF 20) over one dyadic partition, bli-soto-b-027 over the partition cells. The definition of record is now family-relative (`ExactReflection quoteAt cells P`, as `ExactNNUAt` already was); the all-cells shape is retained only with its collapse lemma. STANDARDS §3 ("an over-strong definition that nothing satisfies") wins over the mandate; the mandate text is left as written and the conflict recorded here and in the report.

## F15 — Soto's `n = 1` bundle market is incoherent at `⊤` at the exact level; midpoint self-trust over every sentence is incompatible with coherence at `⊤` · **local error** (PDF 20 p. 2's coherence-by-marginalization sentence, at the exact level) · found by audit r2 adversarial B2, proved in repair round 2

Pointer: Soto PDF 20 p. 1–2 (`bli-soto-b-inventory` 025, 027); `Defs.lean` `coherentTop_forces_zero`, `sotoBundle_top_lt_one`, `sotoBundle_obj_single`, `sotoBundle_top_incoherent`; `Perturb.lean` `quoteAt_sotoBundle_top_lt_one`.

PDF 20 p. 1 defines the `n = 1` bundle market by two clauses — `Q_k(φ) := ∑_m (m+0.5)/2^{k+1} · Q_k(Q_{k+1}(φ) ∈ cell_m)` ("Reflection principle by definition") and `Q_k(φ ∧ Q_{k+1}(φ) ∈ cell_m) := (m+0.5)/2^{k+1} · Q_k(Q_{k+1}(φ) ∈ cell_m)` ("Epistemic self-trust by definition") — and p. 2 says that since every possible `Q_{k+1}` on the betting table is coherent, "through marginalization, those Coherence properties will also be translated into our derived object-level beliefs". **At the exact level this is false, and provably so.** Take `φ := ⊤`. Every coherent `Q_{k+1}` has `Q_{k+1}(⊤) = 1`, so only the top cell `(1 − 2^{−(k+1)}, 1]` can carry mass, and the Reflection clause gives `Q_k(⊤) = mid(top cell) = 1 − 2^{−(k+2)} < 1` (`sotoBundle_obj_single`; in general `sotoBundle_top_lt_one`: for any probability on cells of midpoint `< 1`, `P_n(⊤) < 1`). Likewise `Q_k(⊤ ∧ cell) = mid · Q_k(cell) ≠ Q_k(cell)` (`sotoBundle_top_incoherent`). Coherence is inherited only up to the cell half-width `2^{−(k+2)}` — which is what the inventory's 025 flag ("self-trust up to `2^{−(k+2)}`") says, now sharpened to a provable local error for the sentence on p. 2. More generally, **no** history that is coherent at `⊤` on a cell of midpoint `≠ 1` with positive mass on it satisfies the midpoint self-trust identity over every sentence (`coherentTop_forces_zero`: the identity at `φ := ⊤` reads `P(χ) = mid · P(χ)`), so bli-soto-b-027's target as transcribed — exact self-trust in the form `P_n(φ ∧ cell_I) = mid(I) · P_n(cell_I)` for all `φ` — cannot be met by any market that is coherent at `⊤` and believes `𝑸_m(⊤) ∈ (0, 1]`. That the midpoint is the author's intended representative (rather than the inventory writer's transcription) is ATTRIBUTION-UNVETTED; the interval form (the conditional lies in the cell) has no such obstruction (`top_exact_interval`, `coherentTop_interval_below_cell`) and is this package's object of record since repair round 2. Soto's own general-`n` remark on p. 2 ("the meta-beliefs of future different stages also need to marginalize between themselves") is the same issue one level up; not formalized.

## F16 — BLI's own grid prices sit on cell *endpoints* under the `(lo, hi]` convention, so the midpoint representative misstates every grid price · **imprecision** (cross-package; for the reconciler) · audit r2 adversarial N4

Pointer: `bli-finite` `gridVals d = {k/d : k ≤ d}` (`Index.lean:147`); `bli-found` `D_NNU` (midpoint `(I.1 + I.2)/2`, cell family parametric); `bli-assemble` `dyadicMesh`.

A market whose day-`m` prices lie on the grid `{k/d}` is represented faithfully by the representative `rep I = I.2` (cell endpoints) or by cells centred on grid values, never by `mid`: with the family `((k−1)/d, k/d]` the midpoint misstates every grid price by `1/(2d)`, and `D_NNU` at `ε = 0` is then unsatisfiable by a grid market at `⊤` (F15's argument). This package's X7 is unaffected (its state atoms carry exact tables), and `bli-found`'s `D_NNU` leaves the family parametric, so nothing is wrong in Lean; but any package instantiating `D_NNU`'s cells at the BLI grid with `ε = 0` should use a representative parameter rather than `mid`. Recorded for the reconciler; not changed here.

## Open (recorded here, listed in `bli-exactness-open`)

Corrected in repair round 1 (audit r1 B3/B4: this section named two Lean declarations that did not exist). **This package has no Lean `sorry` and no Lean OPEN statement.**

* **A coherent inhabitant of the interval-form self-trust predicate over every sentence** (added in repair round 2): is there a finite mixture of completed-theory worlds of `paperDP T` satisfying `ExactSelfTrustXInterval (quoteAt T) cells P` with a cell of positive mass? The midpoint analogue is refuted (`coherentTop_forces_zero`). Expected answer at `quoteAt T` with a family covering `(0, 1]`: **no** (a world mixture would have to put `P_n(φ)` in the cell of `𝑸_m(φ)` for every `φ`, since all completed-theory worlds agree on every quote sentence, and the paper market's day-`m` prices are not coherent); the refutation needs a day-`m` incoherence of the LIA that FAF does not provide. Restricted to the day-`m` support (bli-soto-b-027's wording) the question is open in both directions. Prose only; the report § Open has the statement.

* **X1 (d3)** — a `ℙ`-state atom restores the liar for the BLI market itself: **proved conditional**, no sorry — `bli_liar_restoration` and `bli_never_exact_on_own_liar` (`Open.lean`) carry the explicit hypothesis `hQ : ComputableMarket (bliHistory Q 𝓜 sk c)`. It is the *same-day* (X2-shaped) liar about `ℙ`'s own price; the cell-reflection form of X1 (b) about `ℙ_m` is not stated. `hQ` is implied by bli-assemble's L2 row at `dyadicMesh`/`tentSkeleton`/`writeOutCoding` once its two OPEN obligations land; for other parameters no package states it. Ledger status `partial: conditional on bli-assemble OPEN`.
* **X5 (v)** — does FAF's inductor project to a repaired PC-LI, and conversely (bli-soto-a-2-002 (a)–(b))? **Prose only; not stated in Lean.** Two definitions it needs are missing and non-trivial: the normalized world projection of a non-coherent history (`u ↦ P n (worldConj u)` does not sum to `1` for the LIA at finite `n`) and the bundle translation of a FAF `Trader` (`EF.denote` is real-valued, `WorldMarket.Strategy` rational — and, F-N2, a fixed vector where Soto's strategies are price-dependent). The precise statement is in the report § Open.
* **X7-LI** — the LI form of the accuracy gap over `liaHistory`; not attempted (report § X7 has the route).
