# lit-ddb-frames — audit round 1, lens: adversarial

Auditor: a fresh-context agent (faf-cleanroom run, 2026-09-29) that did not write the package. Read: [STANDARDS](../../STANDARDS.md), `AUDIT` §0.2 and §3, the mandate, [lit-ddb-frames-report](lit-ddb-frames-report.md), [lit-ddb-frames-ledger](lit-ddb-frames-ledger.md), [lit-ddb-frames-findings](lit-ddb-frames-findings.md), every file of `Cleanroom/Found/LitDdbFrames/` (all statements and docstrings; proof bodies of every headline rowed P/C, and of the witnesses), and the cited passages of `Deference Done Better` (§1–§2 definitions, §4 Theorem 4.1, the glossary, Appendix B §7.1–7.2 in full, fns 12, 19, 36, 37, 52, 62–66) plus `DORDDBv1.pdf` via `pdftotext` for Figure 5, fn 52 and Fact 2.1. Probes: `packages/lit-ddb-frames/audit-r1-probes/Vacuity.lean` (four probes, elaborated with `scripts/lean-check`, one cosmetic lint warning, no errors). Contamination: none — I did not open `research/faf-lab/`, any transcript, or unrestricted git history (`git log` was run only with paths under this package).

## 1. Verdict

**pass.**

Gate: `scripts/wp-audit Cleanroom.Found.LitDdbFrames` run by me on the committed tree → `PASS` (395 declarations; axioms `propext`, `Classical.choice`, `Quot.sound` only). No `sorry`, no open list (none needed: nothing rests on an unproved step). No blocking issue found under the adversarial lens: no headline is a squeeze, vacuous, trivially true or weaker than its name, ledger row or docstring; no undisclosed (c); every N+ claim is N+ on my own grading; every ledger row matches the Lean; no junk value reaches a headline; every `core` target (1–21) is done; every claim in the findings file that I checked is true.

## 2. Blocking issues

None.

## 3. Non-blocking issues

Numbered for the repair pass; none changes a statement of record.

1. **`Value.newReflects` docstring header mislabels its source** (`Value.lean`). The bold header says "Fn 16 / fn 17 direction", but fn 16 is "Reflection ⇒ Value" and fn 17 is the immodest-frame iff; the theorem (Value ⇒ New Reflection) is fn 19, which the `Source:` line correctly cites. Fix the header. Presentation.
2. **Kind of `WeakValue.value` (Lemma 7.5) is P in the ledger; C fits better.** Its proof opens with `(h.totalTrust hπ).hullAndModestlyInformed hπ` and then uses 7.2.5 (`selfMass_pos_of_hull`) and (**) (`mass_cell_lt_selfMass_of_hull`) before the boost construction — a real multi-step chaining of cited facts plus new content, which is [STANDARDS](../../STANDARDS.md) §6's C. Not a trust issue (both kinds are honest); label it C, as `Frame.selfWeight_pos_of_hull` already is.
3. **`Frame.ModestlyInformed` fidelity "exact" should say what was made explicit.** DDB's glossary sentence has no positivity clause; the guard `0 < ρ(P = ρ)` is the presupposition that `P̂_ρ` exists. Probe 1 (`hullAndMIUnguarded_iff`) proves that under the hull half of 7.6 (iv) the guard is *redundant* — the unguarded reading with Lean's junk `P̂ = 0` at a null self-cell is equivalent to the record — so Theorem 4.1/7.6's fourth condition is DDB's predicate exactly. But as a standalone definition (consumed by `lit-ddb-facts` outside the hull condition), `ModestlyInformed` is strictly stronger than the literal glossary text on a candidate with a null self-cell. Suggested wording: `Fidelity: exact (the presupposition that P̂_ρ exists is made an explicit conjunct; redundant under π ∈ convexHull C_π, audit r1 probe 1)`. Presentation.
4. **`Frame.condProbEvent` / `Trust` docstrings call the exclusion of `P_w(p) = 0` worlds "DDB's convention".** DDB do not state a convention for `[P(q | p) ≥ t]` at worlds where `P_w(q | p)` is undefined; exclusion is the standard reading (the only one under which the event is a proposition) and I found nothing in §2, fn 36 or fn 37 that contradicts it, but the attribution should be softened to "the convention under which the event is defined" (ATTRIBUTION-UNVETTED otherwise). `TotalTrust.cond`, `TotalTrust.trust` and `Frame.condEstEvent` inherit the same wording. Imprecision in docstrings; no headline of 7.6 depends on it.
5. **Findings F1's record table omits Figure 5's `F₂`**, although F3 and two N+ witnesses (`fig5F2_not_totalTrust`, `fig5F2_not_modestlyInformed`) rest on its matrix. I checked it: PDF ll. 1333–1336 give `F₂ = (2/4 1/4 1/4; 6/16 8/16 2/16; 1/4 1/4 2/4)`, matching transcription l. 316 and `fig5F2` (`![1/2, 1/4, 1/4]`, `![3/8, 1/2, 1/8]`, `![1/4, 1/4, 1/2]`); fn 52's text is at PDF l. 1316 (`X = (5 −1 −10)`, purple region `{ρ : E_ρ(X) ≥ 0}`, `E_π(X | E(X) ≥ 0) < 0`), matching l. 1209. Add the row (and `F₁`, if `lit-ddb-facts` will use it) so consumers inheriting F1 are covered. Presentation.
6. **`SimpleTrust` and `Trust` have no direct witness of failure in the package** — both definitions of record are exercised only positively, via `TotalTrust.simpleTrust`/`.trust` on Figure 3. Probe 3 gives them one: `fig2_not_simpleTrust` and `fig2_not_trust` (`q = {a}`, `t = 4/5`, event `{b}`, mass `½`, `π(a ∧ [P(a) ≥ 4/5]) = 0`). Worth moving into `Examples.lean`. Improvement.
7. **NR-vac vs NR-str (findings F8) is separated only in prose.** Probe 2's `swap2` (rows `(0, 1)`, `(1, 0)`, `π = (½, ½)`) satisfies `NewReflectsVac` and refutes `NewReflects`. Worth moving into `Examples.lean` and citing from F8, since `lit-ddb-facts` must pick between the readings. Improvement.
8. **`Hyps:` lines are missing on the `TotalTrust.lean` headlines** (`TotalTrust.selfMass_pos`, `TotalTrust.cond`, `TotalTrust.newReflects`, `TotalTrust.trust`, `totalTrust_iff_cond`), which are rowed as headlines; [STANDARDS](../../STANDARDS.md) §4 asks for the line on headlines. Their only hypothesis is `hπ : ∀ w, 0 ≤ π w` (a). Presentation.
9. **No named explicit-weights lemma for `ModestlyInformed`/`ClassConvex`.** The mandate (Target 4) asks for the `λ`-form as a lemma; the package unfolds `Finset.mem_convexHull'` inline at each use. Dependents (`lit-ddb-facts` item 053's ladder) will want `Frame.ModestlyInformed ↔ ∃ c, …`. Improvement, not a fidelity issue.
10. **Probe file lint**: `fig2_condProbEvent` uses `<;> norm_num` where only one goal needs it (`linter.unnecessarySeqFocus`); cosmetic, left as is.

Things I looked for and did not find (so the reader knows they were checked): a `Nat` subtraction, `sSup`/`iSup`, `ℝ≥0`/`ENNReal` truncation, `decide`/`native_decide` in the library, a `Classical.choose` whose default affects a statement (the one use, `Frame.informedChoice`, is a witness constructor whose specification `informedChoice_spec` is what every consumer uses), a structure field smuggling a conclusion (`Frame` has only `P_mem`; `Experiment` only `k_mem`), an `atTop`/`cofinite` filter (none: everything is finite sums), a look-alike FAF object (there are no FAF objects in this package, and the report says so correctly).

## 4. What I checked and how, per headline

Format: declaration — what the Lean statement says in plain words after unfolding — how I checked it — grade. "hπ" is `π ∈ stdSimplex ℝ W`.

### Definitions of record (Targets 1–6; `Defs.lean`, `Blackwell.lean`, `Local.lean`)

- `Frame` — `P : W → W → ℝ` with every row in `stdSimplex ℝ W`; no other field. Read; matches glossary "Probability frame". No `Nonempty W` needed: `hπ` is unsatisfiable on empty `W`, so no headline is vacuously applicable there. D, exact.
- `E`, `mass`, `ind`, `supp`, `Frame.cell`, `Frame.cands`, `Frame.candsMinus`, `Frame.selfMass` — finite sums; `cands ρ = (supp ρ).image P` is a set of distributions (Remark 7.2.1 handled without representatives); `candsMinus ρ = (cands ρ).erase ρ`. Read against glossary `C_π`, `C_i`, `C_i⁻`, `W_π`. D, exact.
- `Frame.ModestAt`, `Frame.Immodest` — `P_w(P = P_w) < 1` / `= 1 ∀ w`. Read against §1 ll. 80–89. D, exact.
- `Frame.informed` — `w ↦ if P_w = ρ then ρ w / ρ(P = ρ) else 0`; junk `0`-vector at a null self-cell, disclosed. I traced every consumer: `ModestlyInformed` and `NewReflects` carry `0 < selfMass`; `ClassConvex` is unguarded but the junk cannot admit anything spurious (a convex combination equal to a simplex point puts weight `0` on the zero vector, since coordinates sum to `1`), and `classConvex_iff_modestlyInformed` derives positivity by 7.2.5; `informedChoice` is unguarded but is used only where any maximiser suffices (`Value.weakValue`) or under the hull condition (Lemma 7.3); `Frame.boost` divides by `selfMass` only inside Lemma 7.5's proof after `selfMass_pos_of_hull`. No headline sees the junk. D, exact under the guard.
- `Reflects` — `∀ ρ ∈ C_π, ∀ w, π w · 𝟙[P_w = ρ] = π(P = ρ) · ρ w`; candidacy is the positivity guard. Read against §1 l. 75. D, exact.
- `NewReflects` (NR-str) — `∀ ρ ∈ C_π, 0 < ρ(P = ρ) ∧ ∀ w, π w · 𝟙[P_w = ρ] · ρ(P = ρ) = π(P = ρ) · ρ w · 𝟙[P_w = ρ]`; `NewReflectsVac` — same with `0 < ρ(P = ρ) →`. Read against §1 l. 86, fn 12 (which presupposes `ρ(P = P_w) = 1` for the informed version) and fn 19. Probe 2 shows the two readings are distinct predicates. D, exact / variant, as rowed.
- `Frame.probEvent`, `SimpleTrust` — `[P(q) ≥ t]`; `0 < π(E) → t · π(E) ≤ π(q ∩ E)` for all `q`, all real `t`. Read against §2 l. 145, glossary. Probe 3: fails on Figure 2 (not vacuous). D, exact.
- `Frame.condProbEvent`, `Trust` — `{w : 0 < P_w(p) ∧ t · P_w(p) ≤ P_w(q ∩ p)}`; `0 < π(p ∩ E) → t · π(p ∩ E) ≤ π(q ∩ p ∩ E)`. Read against §2 l. 154. Convention on `P_w(p) = 0` worlds: see issue 4. Probe 3: fails on Figure 2. D, exact under the stated convention.
- `TotalTrust` — `∀ X s, 0 ≤ ∑ w, π w (X w − s) 𝟙[s ≤ E_{P_w}(X)]`, all `X : W → ℝ`, all `s : ℝ`. Exactly the mandate's record form; `totalTrust_iff_cond` (read, L) shows it is DDB's ratio form off null events and `0 ≤ 0` on them. Fails on Fact 2.1, `F₂`, and (probe 4) at a vertex deferrer on Figure 3; holds on Figure 3. D, exact.
- `Frame.Validates` — `∀ i, Φ (P_i) F`. Glossary l. 460. D, exact.
- `DecisionProblem`, `Frame.IsStrategy`, `Frame.Recommended`, `stratValue` — `Finset (W → ℝ)`; `∀ w, S w ∈ 𝒪` and the cell constraint `P_w = P_v → S w = S v`; recommended = strategy ∧ `∀ w, ∀ o ∈ 𝒪, E_{P_w}(o) ≤ E_{P_w}(S w)` at *every* world (glossary "for each w ∈ W"); `∑ w, π w · S w w`. Read against §1 ll. 113–117 and the glossary. `flat_value_not_valueNoCell` shows the cell constraint is load-bearing. D, exact.
- `Value`, `WeakValue` — `∀ 𝒪 nonempty, ∀/∃ recommended S, ∀ o ∈ 𝒪, E_π(o) ≤ E_π(S)`. Read against §1 l. 121 and App. B l. 472. Not trivially true (Figure 2, Fact 2.1 refute both), not trivially false (Figure 3); recommended strategies always exist (`informedStrategy_recommended`), so `WeakValue` is not vacuous. D, exact.
- `Frame.twoOption` — `w ↦ if s ≤ E_{P_w}(X) then X else const s`. D, exact.
- `Frame.ModestlyInformed`, `Frame.ModestlyInformedAt` — `0 < ρ(P = ρ) ∧ ρ ∈ convexHull({P̂_ρ} ∪ C_ρ⁻)`; no self-weight positivity built in (checked: the hull is over the *set* including `P̂_ρ`, weight on it unconstrained). Probe 1: the guard is redundant under the hull condition. D, exact with issue 3's caveat.
- `ClassConvex` — `∀ ρ ∈ C_π, ρ ∈ convexHull({P̂_ρ} ∪ (C_π \ {ρ}))`, unguarded as Def. 7.2.6. D, exact.
- `HullAndModestlyInformed` — `π ∈ convexHull C_π ∧ ∀ ρ ∈ C_π, ModestlyInformed ρ`. Theorem 4.1's right-hand side verbatim. D, exact.
- Blackwell (`Experiment`, `Stochastic`, `IsGarbling`, `BlackwellLE`, `BlackwellLT`, `ofMap`, `Refines`, `bayesValue`, `MoreValuable`, `fibreMass`, `calibratedGarbling`) — read each; `BlackwellLE k₂ k₁ := ∃ g stochastic, k₂ = k₁ ∘ g` with the first argument the less informative (docstring says so); `bayesValue` is `sup'` over all rules `S → Fin (n+1)` with a nonemptiness proof (no junk); `calibratedGarbling` junk at null fibres disclosed with the guarded form. Mathlib's square `rowStochastic` not used. D, exact as infrastructure. `Refines.blackwellLE` — `f₂ = h ∘ f₁ → BlackwellLE (ofMap f₂) (ofMap f₁)`: the coarser map is below; L, correct.
- Local (`MeasurableWrt`, `answer`, `ReflectsWrt`, `TotalTrustWrt`, `ValuesWrt`, `questionOf`) — read against fns 62–64: `ReflectsWrt` is fn 62's `π(q | P = ρ) = ρ(q)` for `q` a union of cells, in product form; `TotalTrustWrt` is fn 63; `ValuesWrt` is fn 64 (options `Q`-measurable, strategies still cellwise in `P`). The four L lemmas are one-liners and correct. D/L, exact.
- `Frame.estEvent`, `Frame.estEventLE`, `Frame.condEstEvent` — `[E(X) ≥ s]`, `[E(X) ≤ s]`, `{w : 0 < P_w(q) ∧ t · P_w(q) ≤ ∑_{v ∈ q} P_w v X v}`. D, exact (issue 4 for the last).
- `maximizers`, `informedChoice`, `informedStrategy`, `ValueTwoOption`, `DecompOver`, `boost` — read; `DecompOver` is weaker than both MI and class-convexity (any finite set of rows `≠ ρ` at worlds seen by `π` or `ρ`), so the lemmas proved from it are genuinely stronger, as rowed; `ValueTwoOption` is honestly named as a restriction. D.

### Target 2 (`TotalTrust.lean`)

- `totalTrust_iff_dual` — record form ⟺ `∀ X s, ∑ π (X − s) 𝟙[E(X) ≤ s] ≤ 0`; statement read; L.
- `totalTrust_iff_cond` — record form ⟺ `∀ X s, 0 < π[E(X) ≥ s] → s ≤ (∑_{event} π X) / π[event]`; the ratio is under a positivity hypothesis; the null-event branch is `prod_sum_eq_zero_of_mass_eq_zero`. Read the proof. L, exact; this is what makes Target 2(b) a theorem.
- `TotalTrust.strict` — strict-threshold product form from the record form via the next attained value. Read the proof (finite `exists_min_image`). L, variant as rowed.
- `TotalTrust.simpleTrust`, `TotalTrust.trust` — TT → Simple Trust (via `probEvent = estEvent (ind q)`), TT → Trust (via `cond` at `X = 𝟙_q`). Read both. L / C, exact under issue 4's convention.

### Target 3 (`Strategies.lean`, `Value.lean`)

- `Value.weakValue` — the informed strategy exists and is recommended. L.
- `stratValue_twoOption` — `E_π(S_wit) − s = ∑ w, π w (X w − s) 𝟙[s ≤ E_w X]` literally, needing only `∑ π = 1`. Read the proof (`sum_congr`, `ring`). L, exact; this is the `def-lattice` bridge expression.
- `totalTrust_iff_twoOption` — TT ⟺ `∀ X s, s ≤ E_π(S_wit X s)`. L.
- `valueTwoOption_iff_totalTrust` — ⇒ via `twoOption_recommended` (one recommended strategy suffices), ⇐ via the full cycle. Not named "Value ⟺ TT". C, exact.

### Targets 7–10 (`Hull.lean`)

- `exists_not_mem_convexHull_erase` — any nonempty finite `M ⊆ W → ℝ` has `σ ∈ M` with `σ ∉ convexHull (M \ {σ})`; proof is the Krein–Milman extreme-point argument the mandate prescribes. P, stronger than 7.2.2 as rowed (I confirmed 7.2.2 is its contrapositive applied to DDB's decompositions).
- `no_selfless_maximal_set` — the abstracted engine: a nonempty finite set of `E · X`-maximisers each decomposing over points no higher, whose maximisers lie in the set and differ from it, is impossible. Read fully; the two components `weights_on_max` and `mem_convexHull_of_weights_subset` are correct. P. Used five times; I re-checked each instantiation's side conditions (the informed self has mass `0` on a foreign cell via `mass_informed_cell_of_ne`; a candidate coinciding with `P̂_τ` is handled since `insert` does not duplicate).
- `Frame.mass_supp_eq_one_of_hull` — `hπ`, `π ∈ convexHull C_π`, `DecompOver π` ⊢ `∀ ρ ∈ C_π, ρ(W_π) = 1`. Read the proof: DDB's `W_π⁰` argument step by step. P, stronger (abstract decomposition), as rowed. Not vacuous: Figure 3 satisfies all hypotheses.
- `Frame.P_self_pos_of_hull` — same hypotheses, `0 < π i → 0 < P_i i`. Positivity derived, never assumed. P, stronger.
- `classConvex_iff_modestlyInformed` — under `hπ`, `π ∈ convexHull C_π`: `ClassConvex ↔ ∀ ρ ∈ C_π, ModestlyInformed ρ`. Read both directions; (⇒) derives the guard by 7.2.5. P, exact.

### Target 11 (`TotalTrust.lean`)

- `TotalTrust.selfMass_pos` — `∀ w, 0 ≤ π w`, TT ⊢ `∀ ρ ∈ C_π, 0 < ρ(P = ρ)`; the dual at `(𝟙[P = ρ], 0)`. Read. P, exact (fn 37's consequence).
- `TotalTrust.cond` — TT ⊢ `t · π(q ∩ [E(X | q) ≥ t]) ≤ ∑_{q ∩ …} π X`, unconditional (product form; `0 ≤ 0` on null events). Read the proof (`Y := (X − t) 𝟙_q`, `null_of_mass_eq_zero`). P, exact under issue 4's convention; the mandate's own derivation checks.
- `TotalTrust.cond_ratio` — the ratio form under positivity. L.
- `TotalTrust.newReflects` — TT ⊢ NR-str; via `cell_identity` (the record form at a two-point variable and its negative). Read. P, exact.
- `TotalTrust.newReflectsVac_iff` — under TT, NR-vac ⟺ NR-str. L.

### Targets 12–17 (`Cycle.lean`, `SelfWeight.lean`, `Value.lean`)

- `WeakValue.totalTrust` (7.1) — `hπ`, WeakValue ⊢ TT. Read the proof fully: contrapositive, `0 < π(A)` from the failure, `s` from `exists_sep_threshold`, the forced strategy on `{X, const s}`, `E_π(S) = s + (a − s) π(A) < s`. No hypothesis beyond `hπ`. P, exact.
- `StrongDual.apply_eq_E` — `f ρ = E_ρ(w ↦ f(𝟙_w))`. L.
- `TotalTrust.mem_convexHull_cands` (7.2 first half) — `hπ`, TT ⊢ `π ∈ convexHull C_π`; Hahn–Banach on the closed hull, the functional extracted as `X`, the event is all of `W_π`. Read fully. P, exact. Fact 2.1 refutes the conclusion directly (so the hypothesis is not vacuous-by-triviality).
- `TotalTrust.classConvex` (7.2 second half) — `hπ`, TT ⊢ ClassConvex; separation of `ρ` from `{P̂_ρ} ∪ (C_π \ {ρ})`, event ∩ `W_π` = `ρ`'s cell, New Reflection turns the cell sum into `π(P = ρ) (Ê_ρ(X) − u) ρ(P = ρ) < 0`. Read fully. P, exact.
- `TotalTrust.hullAndModestlyInformed` (7.2) — composition of the two halves with 7.2.7. C, exact.
- `HullAndModestlyInformed.weakValue` (7.3) — `hπ`, hull condition ⊢ WeakValue, witnessed by `informedStrategy`; F2/F3 as DDB; maximal-set lemma on the maximal-divergence candidates with the class-convex decomposition; averaging over `π = ∑ λ_ρ ρ`. Read fully; the replacement of DDB's `A_i^*` step is sound (F6). P, exact. Figure 3 inhabits the full hypothesis package: N+.
- `Frame.mass_cell_le_selfMass_of_hull` — `hπ`, hull condition, `ρ, σ ∈ C_π` ⊢ `σ(P = ρ) ≤ ρ(P = ρ)`. Read fully. P, variant as rowed (from the hull, not Trust).
- `Frame.not_mem_convexHull_candsMinus_of_hull` (7.4) — `ρ ∉ convexHull C_ρ⁻`. Read fully. P, exact. `Frame.selfWeight_pos_of_hull` — every decomposition has `λ_ρρ > 0` (and `P̂_ρ ∉ C_ρ⁻`). C, exact — this is DDB's literal 7.4.
- `Frame.mass_cell_lt_selfMass_of_hull` ((**)) — `σ ≠ ρ → σ(P = ρ) < ρ(P = ρ)`. Read. P, exact.
- `WeakValue.value` (7.5) — `hπ`, WeakValue ⊢ Value. Read fully: the new menu `(𝒪 \ S[W_π]) ∪ boost[W_π]`, uniqueness of each candidate's boost via (**), `E_π(S') ≤ E_π(S) + β/2`, `o` or its boost beats it. Correct; kind label see issue 2. Exact.
- `tfae_value` (7.6 = 2.2 = 4.1) — `hπ` ⊢ `TFAE [Value, WeakValue, TotalTrust, HullAndModestlyInformed]`; the five `tfae_have` arrows are the theorems above. Only hypothesis `hπ`. C at grade (a), exact against DDB's Theorem 7.6 (read at App. B l. 625) and Theorems 2.2/4.1. Witnesses: Figure 3 inhabits all four (N+, genuine: modest, two distinct candidates, `π` interior); Figure 2, Fact 2.1, `F₂` refute all four by direct proofs of one failing condition each (N+).
- `value_iff_totalTrust`, `totalTrust_iff_hullAndModestlyInformed`, `value_iff_weakValue` — `.out` of the TFAE. C, exact.
- `Value.newReflects` — Value ⊢ NR-str through 2.2 and Target 11(c). C, exact (issue 1 for the header).

### Witnesses (`Examples.lean`, `ExamplesFact21.lean`)

- `fig2_newReflects`, `fig2_not_value`, `fig2_mem_hull`, `fig2_not_modestlyInformed`, `fig2_summary` — rows `(1/5, 4/5)`, `(4/5, 1/5)`, `π = (½, ½)` (PDF-checked in F1). Each is a direct proof, not via the theorem: NR-str by computation; Value fails on `{O_a, O_b}` with the recommended `S_a = O_b, S_b = O_a`, `E_π(S) = −1 < 0`; hull by explicit `½P_a + ½P_b`; MI fails by the half-space `{x₀ ≥ 4/5}`. I re-did the arithmetic. N+ confirmed.
- `fig3_not_reflects`, `fig3_modest`, `fig3_hull`, `fig3_totalTrust_value` — rows `(9/10, 1/10)`, `(1/5, 4/5)`; explicit weights `7/8, 1/8; 7/9, 2/9; 3/7, 4/7` (re-checked: `7/8·(1,0) + 1/8·(0.2,0.8) = (0.9, 0.1)`, `7/9·(0,1) + 2/9·(0.9,0.1) = (0.2, 0.8)`, `3/7·(0.9,0.1) + 4/7·(0.2,0.8) = (0.5, 0.5)`); `fig3_hull` proves *both* conjuncts of `ModestlyInformed` at both candidates. TT and Value then by 7.6. N+ confirmed — this is the full hypothesis package of 7.6 (iv), non-degenerate.
- `fact21_not_totalTrust`, `fact21_not_value`, `fact21_not_mem_hull` — `π = (0.17, 0.56, 0.27)`, DDB's matrix, `O_1 = (29, −3, −13)` (PDF l. 584–588 matches); `E_i(O_1) = 6.9, 0.3, 0.6`, `E_π(O_1) = −0.26` (re-done). All three are direct proofs. N+ confirmed (hull half fails, MI not needed).
- `fig5F2_not_totalTrust`, `fig5F2_not_modestlyInformed` — `F₂` matrix PDF-checked by me (issue 5); `E(X) = (−1/4, 1/8, −4)` re-done; the cut `{E(X) ≤ 0}` separates `P_2` from `{P̂_2, P_1, P_3}`. Direct proofs. N+ confirmed.
- `flat_value_not_valueNoCell` — Value holds via 7.6 on the immodest flat frame, the unconstrained variant fails. N−, disclosed and by design.

### Findings file

F1: spot-checked Figures 2, 3, Fact 2.1, fn 52 and (issue 5) Figure 5 against the PDF — all match. F2: read the PDF's Lemma 7.2.2 proof (ll. 1908–1915); the finding's reconstruction is right and the argument is sound. F3: verified — fn 52 is attached at transcription l. 321 (PDF l. 1288) to the `F₂` discussion, the inventory's arithmetic (`−2.35, −1.45, −4.6`) is `X` against Fact 2.1's rows, and on `F₂` the cut does what fn 52 says; the inventory (item 056) is the party in error, as the finding states. F4: theorem proved. F5, F6: I read DDB's proofs of 7.4 and 7.3; the package's routes are simplifications, not corrections — fairly described. F7: `totalTrust_iff_cond` is the theorem claimed. F8: real distinction (probe 2 separates the readings).

### Probe outputs

`scripts/lean-check packages/lit-ddb-frames/audit-r1-probes/Vacuity.lean`: no errors; one warning (`linter.unnecessarySeqFocus` at line 97). Probes: 1 `hullAndMIUnguarded_iff` (guard redundant under the hull), 2 `swap2_newReflectsVac_not_newReflects` (NR-vac ≠ NR-str), 3 `fig2_not_simpleTrust`, `fig2_not_trust` (Simple Trust and Trust bite), 4 `fig3_not_totalTrust_vert0` (a vertex deferrer is refuted, not trivially admitted).
