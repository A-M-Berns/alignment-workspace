# lit-ddb-frames — findings about the sources

Package `lit-ddb-frames` (faf-cleanroom run, 2026-09-29). Findings per [STANDARDS](../../STANDARDS.md) §5, each with a severity (blocking / local error / imprecision / presentation) and a pointer. Sources: `Deference Done Better` (the transcription, `research/references/deference-done-better/Deference Done Better.md`, cited by line) and `DORDDBv1.pdf` beside it (cited by `pdftotext -layout` line, file `ddb.txt` in this agent's scratchpad, not committed). Inventory items are `fixpoint-lit-inventory` numbers.

## F1. Record item: transcription check against `DORDDBv1.pdf` (Target 21, item 2-017)

Item 2-017 had verified §7.3 only. Checked 2026-09-29 with `pdftotext -layout DORDDBv1.pdf` and grep; every number and definition the package relies on was compared. **Verdict: all match**, with one substantive gap in the transcription (F2). Consumers (`lit-ddb-facts`, `corr-legit-general`) may cite this item instead of re-checking.

| Passage | Transcription | PDF | Verdict |
|---|---|---|---|
| Figure 1 (matrix) | l. 66: `(0.7 0.3 / 0.4 0.6)` | ll. 185–188 | matches |
| Figure 2 (matrix, π) | l. 105: `π = (0.5 0.5)`, `(0.2 0.8 / 0.8 0.2)` | ll. 318–324 | matches |
| Figure 3 (matrix, π) | l. 131: `(0.9 0.1 / 0.2 0.8)` | l. 410 (`P_a(a) = 0.9`, `P_b(b) = 0.8`), l. 427 | matches |
| Fact 2.1 (π, matrix, `O_1`) | ll. 163–165 | ll. 583–588: `π = (0.17 0.56 0.27)`, rows `(0.45 0.10 0.45)`, `(0.15 0.70 0.15)`, `(0.30 0.10 0.60)`, `O_1 = (29, −3, −13)`, `E_π(O_1) = −0.26` | matches; arithmetic re-verified: `E_π(O_1) = 4.93 − 1.68 − 3.51 = −0.26`, `E_1(O_1) = 6.9`, `E_2(O_1) = 0.3`, `E_3(O_1) = 0.6` (Lean: `ExamplesFact21.lean`) |
| Theorem 4.1 | l. 327 | l. 1404 | matches |
| Definition 7.2.3 (`W_π`) | l. 508 | l. 1918 | matches |
| Definition 7.2.6 (class-convex) | l. 522 | ll. 1962–1966 | matches |
| Lemma 7.2.2 proof end | l. 506: "… `≠ P_1`… [the original derives a contradiction with `P_1` being a probability function]" | ll. 1913–1915: "`P_1 = ∑_{P_j ∈ C_1⁻} λ_1j P_j = 0`, contradicting the fact that `P_1` is a probability function" | transcription incomplete; see F2 |
| Lemma 7.5's `S_i^t` | l. 590 | ll. 2153–2157: `S_i^t(w) := S_i(w) + t if P_w = P_i, S_i(w) otherwise` | matches |
| Glossary: modestly informed | l. 436 | ll. 1803–1806 | matches |
| Glossary: strategy | l. 454 | ll. 1826–1829 | matches |
| Glossary: Total Trust | l. 456 | ll. 1833–1834 | matches |
| Glossary: Value | l. 462 | ll. 1838–1841 | matches |
| fn 52 | l. 1209: `X = (5, −1, −10)`, purple region `{ρ : E_ρ(X) ≥ 0}` | l. 1316 | matches; see F3 for what it refers to |
| fn 66 (frame, π) | l. 1239 | ll. 1771–1775: rows `(1 0 0 0)`, `(0 0.6 0.4 0)`, `(0 0.6 0.4 0)`, `(0 0 0 1)`, `π = (¼,¼,¼,¼)` | matches |

Not checked: §3 (accuracy), §7.3 beyond item 2-017's earlier verification, footnotes not listed above.

## F2. Lemma 7.2.2's proof (item 049) — presentation, not error

**Severity: presentation.** The transcription's proof of Lemma 7.2.2 (l. 506) ends in an editorial placeholder. The PDF's proof (ll. 1908–1915) is complete but compressed: "each `P_i` is in the convex hull of the other `P_j`, meaning that `CH(A)` has at most one extreme point and therefore is a singleton" (this step is the Krein–Milman/Minkowski fact that a nonempty compact convex set with at most one extreme point is that point), then "since `P_1 ∉ C_1⁻`, `P_1 = ∑_{P_j ∈ C_1⁻} λ_1j P_j = 0`, contradicting that `P_1` is a probability function" (if `A` is a singleton, `C_1⁻ ∩ A = ∅`, so the decomposition is the empty sum). The argument is sound. The proof of record here is the direct extreme-point argument the mandate specifies: `exists_not_mem_convexHull_erase` (`Hull.lean`) shows any nonempty finite set has a member outside the hull of the rest (`IsCompact.extremePoints_nonempty` + `extremePoints_convexHull_subset`), which is DDB's statement in contrapositive without the singleton detour.

## F3. Fn 52's separating variable refers to Figure 5's `F₂`, not to Fact 2.1 (item 056) — inventory error, not DDB's

**Severity: local error in the inventory (item 056); no error in DDB.** The mandate (Target 20) reports the inventory's arithmetic that for `X = (5, −1, −10)` on Fact 2.1's frame, `E_1(X) = −2.35`, `E_2(X) = −1.45`, `E_3(X) = −4.6`, `E_π(X) = −2.41`, so that `X` "separates nothing". The arithmetic is right but the frame is wrong: fn 52 is attached (transcription l. 321, PDF l. 1316 under §4) to the discussion of **Figure 5's `F₂`** — rows `(2/4, 1/4, 1/4)`, `(6/16, 8/16, 2/16)`, `(1/4, 1/4, 2/4)`, `π = (⅓, ⅓, ⅓)` — where the claim is that the cut `{ρ : E_ρ(X) ≥ 0}` separates `P_2` from `w_2` and the other `P_i`. On `F₂`: `E_{P_1}(X) = −1/4`, `E_{P_2}(X) = 1/8`, `E_{P_3}(X) = −4`, `X(w_2) = −1` (so the vertex `w_2` is on the far side); hence `[E(X) ≥ 0] = {w_2}` and `E_π(X | E(X) ≥ 0) = X(w_2) = −1 < 0`, exactly as fn 52 says. Verified in Lean (`ExamplesFact21.lean`, `fig5F2_not_totalTrust`), which also gives the run a second geometrically distinct Total-Trust failure: `P_2` not modestly informed with `π`'s hull membership irrelevant. Item 056 should be corrected to cite fn 52 for `F₂`; Fact 2.1's own separating variable is `O_1` (§2 l. 206: "the purple line … represents the set of probability functions `ρ` such that `E_ρ(O_1) = 0`").

## F4. The cell constraint on strategies is load-bearing (Target 23) — imprecision risk for formalisers, not an error in DDB

**Severity: imprecision (encoding).** DDB define a strategy with `S_w = S_v` whenever `P_w = P_v` (§1 l. 117, glossary l. 454). A formalisation that drops this clause and lets a "strategy" choose any world-wise optimal option makes Theorem 2.2 false: on the immodest frame with both rows `(½, ½)` and `π = (½, ½)` (which reflects the frame, so values it), the choices `S_a = (−1, 1)`, `S_b = (1, −1)` on the menu `{(1, −1), (−1, 1)}` are world-wise optimal (every option has expectation `0` at every world) yet `E_π(S) = −1 < 0 = E_π(O)`. Lean: `Examples.lean`, `flat_value_not_valueNoCell` (`Value` holds via Theorem 7.6; the unconstrained variant `ValueNoCell` fails). Recorded so that no auditor or dependent "refutes" 2.2 this way.

## F5. Lemma 7.4's proof route (item 048) — presentation

**Severity: presentation.** DDB prove Lemma 7.4 (every self-weight `λ_ii > 0`) by first applying the whole §7.1 cycle to each candidate as a deferrer and then a conditional-Trust argument with a case split on whether the maximising candidate is realised only at the excluded world (l. 577–579). The package proves it directly from the hull condition (`SelfWeight.lean`): self-cell dominance (`σ(P = ρ) ≤ ρ(P = ρ)` for all candidates) and Lemma 7.4 are both instances of the maximal-set lemma that already drives 7.2.4, 7.2.5 and 7.3, and the strict inequality (**) of Lemma 7.5 follows in three lines. No Trust, no per-candidate cycle. This is a simplification, not a correction; DDB's route is valid.

## F6. The `A_i^*` step of Lemma 7.3 (item 047) — presentation

**Severity: presentation.** The paper's proof of Lemma 7.3 (ll. 552–563) separates the maximal-divergence candidates from `A := CH({P_k : k ∉ M} ∪ {P̂_j : j ∈ M})`, then strengthens to `A_i^*` and takes an extreme point within `CH({P_j : j ∈ M})`. The package's proof shows the same contradiction is the maximal-set lemma applied to `M` directly with the class-convex decomposition (each maximiser decomposes over its informed self, where the divergence is `≤ 0` by F3, and other candidates with divergence `≤ α`); the sets `A`, `A_i`, `A_i^*` are not needed. Facts F1–F3 of the paper are used as stated.

## F7. The null-event convention (item 034, Weatherson) is a theorem here — presentation

**Severity: presentation.** DDB's Total Trust reads `E_π(X | E(X) ≥ t) ≥ t`, undefined on `π`-null events; Lemma 7.1's parenthetical "this implies `π(E(X) ≥ t) > 0`" is the convention that the requirement applies only where the conditional expectation exists. The definition of record is the denominator-free product form, and `totalTrust_iff_cond` (`TotalTrust.lean`) proves it equivalent to DDB's statement under exactly that convention. The "counterexamples" to 2.2 that item 034 attributes to the alternative convention cannot arise against the record form.

## F8. Reading of New Reflection (fn 12, fn 19) — imprecision

**Severity: imprecision.** DDB's glossary states New Reflection as "for every function `ρ`, `π(· | P = ρ) = ρ(· | P = ρ)`", which presupposes `ρ(P = ρ) > 0` whenever `π(P = ρ) > 0`. The package defines both readings (`NewReflects`: the informed expert exists at every candidate, which fn 12's informed version and fn 19's bet require; `NewReflectsVac`: the clause is vacuous at a null self-cell), proves NR-str → NR-vac, and proves that under Total Trust they coincide (`TotalTrust.newReflectsVac_iff`), because Total Trust forces `ρ(P = ρ) > 0` at every candidate (`TotalTrust.selfMass_pos`). `lit-ddb-facts` chooses between them for items 039/042 where Total Trust is not assumed.
