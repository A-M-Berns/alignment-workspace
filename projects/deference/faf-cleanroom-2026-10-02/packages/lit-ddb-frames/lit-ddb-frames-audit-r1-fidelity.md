# lit-ddb-frames — audit round 1, lens: fidelity

Auditor: a fresh-context agent (faf-cleanroom run, 2026-09-29) that did not write the package. Read: [STANDARDS](../../STANDARDS.md), `AUDIT` §0.2 and §3, the mandate, [lit-ddb-frames-report](lit-ddb-frames-report.md), [lit-ddb-frames-ledger](lit-ddb-frames-ledger.md), [lit-ddb-frames-findings](lit-ddb-frames-findings.md), every file of `Cleanroom/Found/LitDdbFrames/` (all statements and docstrings; the proof bodies of Lemmas 7.1, 7.2, 7.3, 7.5, 7.2.2–7.2.7, the maximal-set lemma and every witness), and the source: `Deference Done Better` §1, §2, §4, §5, the glossary, Appendix B §7.1–7.2, fns 12, 13, 16–19, 26, 32, 36, 37, 52, 54, 62–66, plus `DORDDBv1.pdf` via `pdftotext` for the findings-file spot checks. Contamination: none — I did not touch `research/faf-lab/`, transcripts, or unfiltered git history (one `git log` restricted to this package's paths, to verify the lifecycle claim).

## 1. Verdict

**pass.**

Gate: `scripts/wp-audit Cleanroom.Found.LitDdbFrames` run by me after the package's last commit — **PASS**, 395 declarations, axioms `propext`, `Classical.choice`, `Quot.sound` only, no open statements. Every ledger row's declaration exists with the stated kind, fidelity and hypotheses. No squeeze, no undisclosed (c), no oversold name among the headlines; the only hypothesis of Theorem 7.6 (`tfae_value`) is `hπ : π ∈ stdSimplex ℝ W`, and the cycle's four proofs are genuine (read in full, §4 below). Every core target (1–21) is done; the unattempted items are all `stretch`. The findings file's claims about the sources are real and fairly described (spot-checked against the PDF, §4). **The definitions module (`Defs` + `Blackwell` + `Local`) passes this fidelity audit**, subject to the non-blocking wording points below, so under the mandate's lifecycle rule it can be frozen for dependents.

## 2. Blocking issues

None.

## 3. Non-blocking issues

Eight, none affecting the truth or strength of any headline.

**NB1. `Frame.ModestlyInformed` states a conjunct DDB presupposes.** DDB (glossary, fn 54): "P_i is in the convex hull of {P̂_i} ∪ C_i⁻", with P̂_i := P_i(· | P = P_i) undefined when P_i(P = P_i) = 0. The Lean adds `0 < F.selfMass ρ` as an explicit conjunct, so at a null self-cell the predicate is *false* rather than undefined. This is the right resolution (Total Trust forces the positivity, `TotalTrust.selfMass_pos`, so 7.6 (iv) is unaffected), and the docstring mentions the conjunct — but its `Fidelity:` line says plain `exact`. Say `exact (the informed expert's existence, which DDB presupposes, is an explicit conjunct)` so dependents importing the definition know the convention. Presentation.

**NB2. `ClassConvex` is unguarded and the report's pointer for that is dangling.** At a candidate with a null self-cell, `F.informed ρ` is the junk zero vector, and `ρ ∈ convexHull (insert 0 ↑(C_π \ {ρ}))` reduces (sum = 1 forces zero weight on `0`) to `ρ ∈ convexHull (C_π \ {ρ})`. I checked that this affects no headline: `classConvex_iff_modestlyInformed` (⇒) derives positivity from the hull membership through `Frame.DecompOver`, whose maximal-set argument treats the zero "informed self" as a point with `E = 0 ≤ t` and `≠ t`, exactly as it treats a genuine informed self off the cell; and `TotalTrust.classConvex` has positivity from Target 11(a) before it touches `informed`. But the report (Target 4) says "findings note the junk-value analysis" and [lit-ddb-frames-findings](lit-ddb-frames-findings.md) contains no such note. Either add it to the `ClassConvex` docstring (currently: "under `π ∈ convexHull C_π` it implies `0 < ρ(P = ρ)`", which is the conclusion without the analysis) or to the findings, and fix the pointer. Presentation.

**NB3. A real gap in DDB's proof of Lemma 7.2.7 is in the report but not in the findings file.** DDB's proof of 7.2.7 (⇒) (App. B l. 526) assumes class-convexity and, for reductio, that some `P_i ∈ C_π` is *not* modestly informed — then cites Lemma 7.2.4, whose stated hypothesis is that *every* candidate is modestly informed. The citation is outside 7.2.4's hypotheses; the proof of 7.2.4 does go through under class-convexity (which is what `Frame.DecompOver` and `Frame.mass_supp_eq_one_of_hull` establish), so the conclusion stands. The report says this under Target 8 ("DDB's proof of 7.2.7 cites 7.2.4 under a hypothesis 7.2.4 was not stated for; the abstract form closes that gap"), and [STANDARDS](../../STANDARDS.md) §5 makes such findings first-class output — it belongs in [lit-ddb-frames-findings](lit-ddb-frames-findings.md) as an item (severity: imprecision in a proof; statement unaffected; repaired here by `Frame.DecompOver`). Findings completeness.

**NB4. Docstring wording nits.** (i) `Value.newReflects` (`Value.lean`) is headed "**Fn 16 / fn 17 direction.**" — fn 16 is Reflection → Value and fn 17 is the immodest-frame equivalence; the theorem is fn 19's direction (Value → New Reflection), which its `Source:` line correctly cites. (ii) `Frame.Validates` says "every candidate `P_i` defers" — there is no `π` in scope; DDB's glossary and the Lean quantify over every `i ∈ W`. Write "every row `P_i`". Presentation.

**NB5. Lifecycle bookkeeping: some definitions of record live outside the frozen module.** The report names the definitions module as exactly `Defs` + `Blackwell` + `Local`, and says the other files "may keep evolving". But the ledger's D rows also include `Frame.estEvent`, `Frame.estEventLE`, `Frame.condEstEvent` (in `TotalTrust.lean` — `condEstEvent` is the event of `TotalTrust.cond`, the conditional Total Trust that `lit-ddb-facts` is told to generalise) and `ValueTwoOption` (in `Strategies.lean`, the two-option notion `def-lattice` may cite). Either move these to `Defs.lean` before freezing, or state in the report that they are frozen with the module. Presentation / lifecycle.

**NB6. Names of the form `*_of_hull` take more than the hull.** `Frame.mass_supp_eq_one_of_hull`, `Frame.P_self_pos_of_hull`, `Frame.selfMass_pos_of_hull`, `Frame.mem_cands_self_of_hull`, `Frame.cands_subset_of_hull` all take `hhull : π ∈ convexHull C_π` *and* `hdec : F.DecompOver π`; "of_hull" reads as the bare hull membership. The docstrings are clear and the theorems are genuinely stronger than DDB's (stated under the abstract decomposition), so this is naming only; `_of_hull_decomp` or similar would be honest. Low priority.

**NB7. The null-event reading of `[P(q | p) ≥ t]` should cite its basis.** `Frame.condProbEvent q p t` excludes worlds with `P_w(p) = 0` ("DDB's convention", per the docstring). DDB never state a convention for this event; the support for the exclusion reading is fn 36's proof ("this mixture gives positive weight only to the ρ_i for which ρ_i(· | q) is well-defined"). Under Total Trust the reading is immaterial (such worlds inside `p` are π-null, `TotalTrust.null_of_mass_eq_zero`), so `TotalTrust.trust` is safe either way; but `Trust` is a standalone definition of record that `lit-ddb-facts` will use where Total Trust is *not* assumed, and the Fact 2.1 stretch (Trust holds) depends on it. Cite fn 36 in the docstring and name the alternative reading (include such worlds in the event) so the choice is visible. Imprecision, disclosed.

**NB8. Optional: a positive witness independent of the theorem it guards.** `fig3_totalTrust_value` and the `Value` half of `flat_value_not_valueNoCell` obtain Total Trust / Value *through* Theorem 7.6 from `fig3_hull`; no frame in the package has Total Trust or Value proved directly from the definition. Logically this is sufficient (consistency plus `fig3_hull` yields `TotalTrust half fig3`), and the negative witnesses (`fig2_not_value`, `fact21_not_totalTrust`, `fig5F2_not_totalTrust`) are direct. A direct proof of `TotalTrust half fig3` — a two-case argument on `Fin 2`: `min(E_a X, E_b X) ≤ (X a + X b)/2`, and on the one-sided events `s ≤ E_a X < E_b X` forces `X a ≥ s` — would make the N+ grade of the positive witness rest on the definition alone. Optional.

## 4. What I checked and how

Method: for every definition of record, unfold it and compare with DDB's prose/glossary (line-cited); for every headline, state what the Lean says after unfolding and compare with the source and the mandate target; read proof bodies where the claim is that a proof is genuine (not a squeeze). "Plain reading" below is the unfolded Lean.

### Definitions of record (`Defs.lean`, `Blackwell.lean`, `Local.lean`) — all exact

- `Frame` — `P : W → W → ℝ` with every row in `stdSimplex ℝ W`: DDB's row-stochastic matrix (§1 l. 61, glossary). Exact.
- `E`, `mass`, `ind`, `supp` — `∑ w, ρ w * X w`; `∑ w ∈ q, ρ w`; indicator; `{w : 0 < ρ w}` (Def. 7.2.3). Exact.
- `Frame.cell ρ` = `{w : P w = ρ}` = `[P = ρ]`. Exact.
- `Frame.cands ρ` = `(supp ρ).image P`; for `ρ ≥ 0` equals DDB's `{δ : ρ(P = δ) > 0}` (`Basic.lean`, `mem_cands_iff_mass_cell_pos` proves it). A set of distributions, so Remark 7.2.1 needs no representatives. Exact. `candsMinus ρ` = `C_ρ \ {ρ}` per fn 54. Exact.
- `selfMass ρ` = `ρ(P = ρ)`; `ModestAt w` ⟺ `P_w(P = P_w) < 1`; `Immodest` ⟺ all `= 1`. Exact (§1 ll. 61, 80–82).
- `Frame.informed ρ` — ratio `𝟙[P_w = ρ] ρ w / ρ(P = ρ)`, junk `0` at a null self-cell, disclosed; consumers `ModestlyInformed`/`NewReflects` carry positivity; `ClassConvex` does not (NB2, harmless).
- `Reflects` — `∀ ρ ∈ C_π, ∀ w, π w 𝟙[P_w = ρ] = π(P = ρ) ρ w`. Off the cell this forces `ρ w = 0`, which is exactly why Reflection forces candidate immodesty in DDB (§1 l. 80). Exact.
- `NewReflects` (str) — `∀ ρ ∈ C_π, 0 < ρ(P = ρ) ∧ ∀ w, π w 𝟙 ρ(P = ρ) = π(P = ρ) ρ w 𝟙`: the product form of `π(· | P = ρ) = ρ(· | P = ρ)` with the informed expert's existence (fn 12's informed version needs it). `NewReflectsVac` drops the existence and guards the clause. Both readings defined, `str → vac` proved; findings F8 says why. Exact / variant as labelled.
- `SimpleTrust` — `∀ q t, 0 < π(P(q) ≥ t) → t π(P(q) ≥ t) ≤ π(q ∧ P(q) ≥ t)`: DDB §2 l. 145 in product form, all real `t`. Exact. `Trust` — same shape on `p ∧ [P(q | p) ≥ t]` with `condProbEvent` product-guarded (NB7). Exact under the stated reading.
- `TotalTrust` — `∀ X s, 0 ≤ ∑ w, π w (X w − s) 𝟙[s ≤ E_{P_w} X]`, the mandate's record form verbatim; `X` over all variables, `s` over all reals. Exact; `totalTrust_iff_cond` proves it is DDB's `E_π(X | E(X) ≥ s) ≥ s` under the `π(E(X) ≥ s) > 0` convention of Lemma 7.1.
- `Frame.Validates F Φ` — `∀ i, Φ (P i) F`: glossary "for every i ∈ W" (NB4 ii). Exact.
- `DecisionProblem` = `Finset (W → ℝ)`; `IsStrategy` = membership + `P w = P v → S w = S v` (the cell constraint, glossary "strategy"); `Recommended` = strategy + `∀ w, ∀ o ∈ 𝒪, E_w o ≤ E_w (S w)`; `stratValue` = `∑ w, π w S w w`. All exact against §1 ll. 113–121 and the glossary.
- `Value` — `∀ 𝒪 nonempty, ∀ S recommended, ∀ o ∈ 𝒪, E_π o ≤ E_π S`; `WeakValue` — `∃ S` in place of `∀ S` (App. B l. 472). Exact. The empty menu is excluded from both, as the mandate requires.
- `Frame.twoOption X s` — `if s ≤ E_w X then X else const s`. Exact (Lemma 7.1's unique strategy).
- `ModestlyInformed ρ` — `0 < ρ(P = ρ) ∧ ρ ∈ convexHull ({P̂_ρ} ∪ C_ρ⁻)`; no built-in self-weight positivity (Lemma 7.4's conclusion, `not_mem_convexHull_candsMinus_of_hull`). Exact modulo NB1.
- `ClassConvex` — Def. 7.2.6 over `C_π \ {ρ}`, unguarded (NB2). `HullAndModestlyInformed` — `π ∈ convexHull C_π ∧ ∀ ρ ∈ C_π, ModestlyInformed ρ`: Theorem 4.1's right-hand side. Exact.
- Blackwell (`Experiment`, `Stochastic`, `IsGarbling k₁ k₂ g` = `k₂ w t = ∑ s, k₁ w s g s t`, `BlackwellLE k₂ k₁` = `∃ g stochastic, IsGarbling k₁ k₂ g` with the *less* informative first as the docstring says, `BlackwellLT`, `ofMap`, `Refines f₁ f₂` = `∃ h, f₂ = h ∘ f₁`, `bayesValue` = `sup'` over all rules `S → Fin (n+1)` of `∑ w, μ w ∑ s, k w s u (δ s) w`, `MoreValuable`, `fibreMass`, `calibratedGarbling` with disclosed junk) — standard definitions; no FAF object exists to substitute (I confirm the mandate's report: FAF has none). `Refines.blackwellLE` proves the coarser map is Blackwell-below the finer, the right direction.
- Local (`MeasurableWrt`, `answer`, `ReflectsWrt`, `TotalTrustWrt`, `ValuesWrt`, `questionOf`) — checked one by one against fns 62, 63, 64: partial answers are unions of cells; Total Trust restricted to `Q`-measurable `X`; Value restricted to menus of `Q`-measurable options with strategies still cellwise in `P`. Exact. Nothing from fn 65/66 is stated, as mandated.

### Target 2 — Total Trust is DDB's (`TotalTrust.lean`)

- `totalTrust_iff_dual` — plain reading: TT ⟺ `∀ X s, ∑ π w (X w − s) 𝟙[E_w X ≤ s] ≤ 0`; proof substitutes `−X, −s`. L, exact.
- `totalTrust_iff_cond` — TT ⟺ `∀ X s, 0 < π(E(X) ≥ s) → s ≤ (∑_{event} π w X w) / π(event)`, with `prod_sum_eq_zero_of_mass_eq_zero` for the null case. This *is* the null-event convention as a theorem (findings F7). L, exact.
- `TotalTrust.strict` — the `s < E_w X` form via the least attained value above `s`. L, variant as labelled.
- `TotalTrust.simpleTrust` (no `hπ` needed — ledger's "—" is right), `TotalTrust.trust` (via `cond` at `X := 𝟙_q`). Exact instances.

### Target 3 — strategies and the two-option witness (`Strategies.lean`)

- `Value.weakValue` — a recommended strategy exists for every nonempty menu (`informedStrategy`, cellwise by construction). L, exact.
- `stratValue_twoOption` — `E_π(S_wit) − s = ∑ π w (X w − s) 𝟙[s ≤ E_w X]`, literally the record form (checked term by term: on the event the summand is `π w X w − π w s`, off it `π w s − π w s = 0`). L, exact; this is the expression `def-lattice` needs.
- `totalTrust_iff_twoOption`, `ValueTwoOption.totalTrust`, and `valueTwoOption_iff_totalTrust` (⇐ through the full cycle) — honestly named and kinded; not called "Value ⟺ Total Trust".

### Targets 7–10 — structure lemmas (`Hull.lean`)

- `exists_not_mem_convexHull_erase` — any nonempty finite `M` has `σ ∈ M` with `σ ∉ convexHull (M \ {σ})`; proof is the extreme-point argument the mandate specifies. Stronger than DDB's 7.2.2 (no decomposition hypotheses); P.
- `no_selfless_maximal_set` — I checked it is a genuine lemma, not a contradiction among its hypotheses: an extreme point of `conv M` decomposes only over level-`t` points (`weights_on_max`), which must lie in `M \ {σ}`, contradicting extremality. Used five times as the report says.
- `Frame.DecompOver` — I confirmed it is implied by both `HullAndModestlyInformed` (with `D = C_ρ⁻`) and `ClassConvex` (with `D = C_π \ {ρ}`), and requires no self-mass positivity, so theorems stated under it are strictly stronger than DDB's 7.2.4/7.2.5.
- `Frame.mass_supp_eq_one_of_hull` (7.2.4) — plain reading: hull membership + `DecompOver` ⟹ every candidate has mass 1 on `W_π`. Proof follows DDB's `W_π⁰`/maximal-set argument step by step (read in full). P, stronger.
- `Frame.P_self_pos_of_hull` (7.2.5) — `0 < π i → 0 < P_i i`; positivity derived, not assumed (read in full). P, stronger.
- `classConvex_iff_modestlyInformed` (7.2.7) — under `π ∈ convexHull C_π`; (⇒) derives positivity and shows positively weighted other candidates of `π` are candidates of `ρ` via `P_v v > 0`; (⇐) is `convexHull_mono` with `C_ρ⁻ ⊆ C_π \ {ρ}` from 7.2.4. Exact; this is where NB3 lives.

### Target 11 — consequences of Total Trust (`TotalTrust.lean`)

- `TotalTrust.selfMass_pos` — TT ⟹ `0 < ρ(P = ρ)` for every candidate, by the dual at `(𝟙[P = ρ], 0)`. P, exact; this is what makes `P̂_ρ` the genuine informed expert wherever the cycle uses it.
- `TotalTrust.cond` — `t π(q ∧ [E(X|q) ≥ t]) ≤ ∑_{q ∧ [E(X|q) ≥ t]} π w X w`, the product form of fn 36's conditional Total Trust, proved from TT at `(Y, 0)` with `Y := (X − t) 𝟙_q` plus `null_of_mass_eq_zero`. I checked the mandate's flagged derivation: the event `q ∧ [E(Y) ≥ 0]` differs from `q ∧ condEstEvent` only at worlds of `q` with `P_w(q) = 0`, which are π-null, so the two sums agree — it checks. P, exact. `cond_ratio` is the ratio form off null events.
- `TotalTrust.newReflects` — TT ⟹ NR-str, via `cell_identity` (record form at `𝟙[P = ρ]·(ρ(P = ρ)𝟙_w − ρ w)` and its negative). P, exact. `newReflectsVac_iff` under TT. L.

### Targets 12–17 — the cycle (`Cycle.lean`, `SelfWeight.lean`, `Value.lean`)

- `WeakValue.totalTrust` (7.1) — plain reading: Weak Value ⟹ TT. Proof body read in full: from a failure at `(X, t)` it derives `0 < π(E(X) ≥ t)`, the conditional expectation `a < t`, the separating threshold `s` (`exists_sep_threshold`), then that *every* recommended strategy on `{X, const s}` is forced (`X` on the event, `const s` off it) and is worth `a π(A) + s(1 − π(A)) < s = E_π(const s)`. This is DDB's proof; nothing is assumed. P, exact.
- `TotalTrust.mem_convexHull_cands` (7.2, first half) — Hahn–Banach `geometric_hahn_banach_point_closed` on the closed hull of a finite set, functional extracted as a variable by `StrongDual.apply_eq_E` (checked: `f ρ = E ρ (w ↦ f 𝟙_w)` by `pi_eq_sum_univ`), then the event is all of `W_π` and the product sum is `E_π X − u < 0`. P, exact.
- `TotalTrust.classConvex` (7.2, second half) — separates `ρ` from `convexHull ({P̂_ρ} ∪ (C_π \ {ρ}))`; `[E(X) ≥ u] ∩ W_π = [P = ρ] ∩ W_π` (both inclusions checked); `cell_identity` turns the cell sum into `π(P = ρ) (E_{P̂_ρ} X − u) ρ(P = ρ) < 0`. P, exact. `TotalTrust.hullAndModestlyInformed` composes with 7.2.7. C.
- `HullAndModestlyInformed.weakValue` (7.3) — witness `informedStrategy`; the divergence-maximising pair over `𝒪 × W_π`; F2 and F3 proved as in DDB (`E_informed_diag` is "P̂_j knows the cell"); the contradiction is `no_selfless_maximal_set` on the maximal-divergence candidates with the class-convex decomposition; then averaging over `π = ∑ λ_ρ ρ` (`exists_weights_of_hull`, `E_sum_left`). Read in full; genuine, and a real simplification of DDB's `A_i^*` step (findings F6). P, exact.
- `Frame.mass_cell_le_selfMass_of_hull`, `Frame.not_mem_convexHull_candsMinus_of_hull` (7.4), `Frame.selfWeight_pos_of_hull` (7.4 in DDB's phrasing; I checked "`ρ ∉ convexHull C_ρ⁻`" and "every decomposition has `λ_ρρ > 0`" are equivalent given `informed_weight_pos`, which also handles `P̂_ρ ∈ C_ρ⁻`), `Frame.mass_cell_lt_selfMass_of_hull` ((**) of 7.5) — all from the hull condition alone via the maximal-set lemma; no Trust, no per-candidate cycle (findings F5). P/C as labelled, exact/variant as labelled.
- `WeakValue.value` (7.5) — read in full. Given `S` recommended and `o` with gap `β`: `δ := β m / 2` (`m` the least self-cell mass, positive by 7.2.5); new menu `(𝒪 \ S[W_π]) ∪ boost[W_π]`; each candidate's boost is its unique `E`-maximiser (against unboosted options by `+δ`, against other boosts by (**)); so every recommended strategy is the boosted `S`, worth at most `E_π S + β/2`; `o` or its boost is on the menu and beats it by `β`. No IVT, no `S_i ≠ S_j` case split; `boost_cell` keeps the cell constraint. Genuine and cleaner than DDB's. P, exact.
- `tfae_value` — `TFAE [Value, WeakValue, TotalTrust, HullAndModestlyInformed]` under `hπ` only, assembled from the five arrows above. C at grade (a); the three named iffs are `.out` projections. This is Theorem 7.6 = 2.2 = 4.1 exactly, on finite frames, with both Value quantifiers over all nonempty finite menus and all recommended strategies.
- `Value.newReflects` — fn 19's direction through the cycle. C (NB4 i).

### Targets 18–20, 23 — witnesses

- Figure 2 (`fig2_newReflects`, `fig2_not_value`, `fig2_mem_hull`, `fig2_not_modestlyInformed`, `fig2_summary`): rows `(1/5, 4/5)`, `(4/5, 1/5)`, `π = (½, ½)` match §1 l. 105. NR-str proved directly at both candidates; Value refuted on the bet `{(1,−1), (−1,1)}` with the swapped strategy (recommended, cell constraint checked, `E_π = −1 < 0`); hull membership `π = ½P_a + ½P_b`; modest informedness refuted by `convexHull_min` into the half-space `x 0 ≥ 4/5`. **N+** confirmed: NR ⊉ Value, hull without modest informedness, exactly fn 32's point.
- Figure 3 (`fig3_not_reflects`, `fig3_modest`, `fig3_hull`, `fig3_totalTrust_value`): rows `(9/10, 1/10)`, `(1/5, 4/5)` match §1 l. 131; explicit weights `7/8, 1/8; 7/9, 2/9; 3/7, 4/7` verified by `norm_num`. `fig3_hull` inhabits the *full* hypothesis package of 7.6 (iv): two distinct candidates, both modest (self-masses `0.9`, `0.8` < 1), `π` strictly inside their segment. **N+** confirmed (NB8 for the optional direct check).
- Fact 2.1 (`fact21_not_totalTrust`, `fact21_not_value`, `fact21_not_mem_hull`): `π`, matrix, `O_1` match §2 ll. 163–165 and the PDF (ll. 583–588); `E_i(O_1) = 6.9, 0.3, 0.6`, `E_π(O_1) = −0.26` recomputed by hand. TT refuted at `(O_1, 0)` with event `= univ`; Value refuted with the constant strategy; hull membership refuted by the separating half-space `{E(O_1) ≥ 0}`. **N+** confirmed — the hull half fails, geometrically distinct from Figure 2.
- Figure 5 `F₂` (`fig5F2_not_totalTrust`, `fig5F2_not_modestlyInformed`): rows `(2/4, 1/4, 1/4)`, `(6/16, 8/16, 2/16)`, `(1/4, 1/4, 2/4)` and `π = (⅓,⅓,⅓)` match the transcription's Figure 5 (l. 316) and the PDF (ll. 1333–1336, 1389); `X = (5, −1, −10)` is fn 52's; `E_{P_i}(X) = −1/4, 1/8, −4` recomputed. **N+** confirmed.
- `flat_value_not_valueNoCell`: `Value` via 7.6 on the immodest flat frame; the unconstrained variant refuted by the world-wise-optimal swapped strategy. **N−** as labelled, by design. The encoding artifact is real and worth its record (findings F4).

### Findings file, checked against the sources

- F1 (transcription vs PDF): I re-ran `pdftotext -layout DORDDBv1.pdf` and checked Fact 2.1's `π`, matrix and `O_1` (PDF ll. 583–588), fn 52 (l. 1316), Lemma 7.2.2's proof end (ll. 1908–1915), Theorem 4.1 (ll. 1404–1405), and Figure 5's matrices and `π` (ll. 1333–1336, 1389): all as F1 reports.
- F2 (7.2.2's proof): the transcription's l. 506 does end in an editorial placeholder; the PDF's proof is the compressed singleton argument F2 quotes, and it is sound. Fairly described as presentation.
- F3 (fn 52 refers to `F₂`): confirmed — fn 52 is attached at transcription l. 321 to the sentence about separating `P_2` in `F₂`, and on `F₂` the cut `{E(X) ≥ 0}` isolates `w_2` as fn 52 says; on Fact 2.1's frame `X` separates nothing, as the inventory computed. Correctly attributed as an inventory error (item 056), not DDB's.
- F4–F8: presentation/imprecision items; each matches what the Lean does. One omission: NB3.

### Report and ledger

- Report's "395 declarations, standard axioms, gate PASS": reproduced by my run. "Definitions module committed first as `319e61fb` (Defs, Blackwell, Local)": confirmed by a path-filtered `git log` on the package's files. "No (b), no (c)": confirmed — every headline's hypotheses are `hπ` and its antecedent; no DDB lemma is assumed; no FAF object exists to be substituted.
- Ledger: every row's declaration exists; kinds match what the proofs do (P where the argument is real, C where it chains proved lemmas, L for plumbing, D for definitions, N+/N− as I graded above); "Hyps" columns match the signatures, including the two rows correctly marked "—" (`TotalTrust.simpleTrust`, `Value.weakValue` need no `hπ`); Status `proved` everywhere is borne out by the gate.
