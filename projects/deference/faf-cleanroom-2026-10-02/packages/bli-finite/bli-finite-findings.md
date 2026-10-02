# `bli-finite` — findings about the sources

Findings per [STANDARDS](../../STANDARDS.md) §5: errors, ill-posed claims and gaps in the sources this package formalizes, each with a severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. Items 1–8 are the mandate's "known issues" (checked here); F-9 onward are new. Attribution claims about what an author meant are labelled ATTRIBUTION-UNVETTED per `research/CLAUDE.md`.

## F-1 — Appendix B's coherence axioms omit non-negativity / the `[0,1]` range

- **Severity**: imprecision.
- **Pointer**: `main.tex:412–421` (bli-paper-030, its flag); bli-slides-003; bli-soto-a-001.
- **What is wrong**: the paper's two axioms (tautologies price 1; disjoint disjunctions add) admit signed valuations. `twoAxiom_signed_counterexample` (`CoherenceExamples.lean`, kind N−) exhibits `V := 2·[trueWorld ⊨ ·] − [falseWorld ⊨ ·]` with `V p = 2`, `V (∼p) = −1`, satisfying `TwoAxiomNoNonneg V {p} ∅` (both axioms, on the whole generated algebra) and failing `TwoAxiomCoherent`.
- **Corrected version**: the definition of record `TwoAxiomCoherent` adds `∀ φ ∈ GenBy A, 0 ≤ V φ`; with it, `V ≤ 1` follows (`TwoAxiomCoherent.le_one`), and the finite de Finetti theorem `twoAxiom_iff_worldMarginal` (`DeFinetti.lean`) proves the paper's "amount to the Kolmogorov axioms with only finite additivity": two-axioms-plus-non-negativity on `GenBy A` relative to `D` ⟺ marginal of a rational probability on FAF's `FiniteWorld B` supported on `D`-consistent worlds (`hB` covering `A ∪ D`).

## F-2 — "`D_n` … maintaining propositional consistency" is unargued and false for coordinatewise rounding

- **Severity**: local error (for the coordinatewise reading).
- **Pointer**: `main.tex:427` (bli-paper-033); bli-slides-008.
- **What is wrong**: `roundTo_not_coherent` (`CoherenceExamples.lean`, kind N−/refuted): the coherent table `(3/10, 3/10, 6/10)` on `{p ⋏ ∼q, ∼p ⋏ q, (p ⋏ ∼q) ⋎ (∼p ⋏ q)}` (world weights `3/10, 3/10, 4/10` on `p∧¬q, ¬p∧q, p∧q`) rounds coordinatewise at `d = 2` (ties down) to `(1/2, 1/2, 1/2)`, which is not `CoherentOn` (any world distribution prices the disjunction of two exclusive conjunctions at the sum of their prices). The paper does not say which rounding it means; ATTRIBUTION-UNVETTED that coordinatewise was intended. The surviving version is world rounding: `worldRound` (`WorldRound.lean`) rounds the world weights by remainder distribution and takes the marginal; `worldRound_coherent`, `worldRound_mem_coherentGrid`, and `worldRound_err : |worldRound t φ − t φ| < 2^B / d` (not `1/(2d)`, which is `roundTo`'s bound `roundTo_err`).

## F-3 — Roman's grid has no 0

- **Severity**: local error in the desiderata (pointer only; the impossibility is `bli-superbelief` E5's).
- **Pointer**: Roman's deck p. 2 (`D = {1/d, …, 1}`, bli-slides-017), p. 17 ("`[0;1]` boundaries" listed as a missing detail).
- **Here**: the definition of record `gridVals d = {0, 1/d, …, 1}` includes 0 and 1 (`zero_mem_gridVals`, `one_mem_gridVals`), so that exact agreement at price 0 is representable and `roundVal_zero`/`roundVal_one` hold. The contradiction between full support with `0 ∉ D` and exact constraint 1 at price 0 is E5's target, not this package's.

## F-4 — Full support on all of `D^S` is refuted; `NonDegenerate` is the surviving face form

- **Severity**: local error in the desiderata (the finding itself is E5's; the mechanism is proved here).
- **Pointer**: Roman's deck p. 5 (bli-slides-018), refuted by bli-slides-021.
- **Here**: `faceGen_subset_faceProd` (`Superbelief.lean`, kind P) is the mechanism: a balance solution puts no mass on a grid table disagreeing with `t` at a coordinate `t` prices 0 or 1 (`IsProbOn.coord_eq_one_of_meanOn_eq_one`, `coord_eq_zero_of_meanOn_eq_zero`). `NonDegenerate` (positive mass on the product face) is the surviving form and is satisfiable — the tent kernel inhabits it (`tentLaw_nonDegenerate`), so the impossibility is about the sources' formulation, not the encoding.

## F-5 — bli-paper-036's "martingale consequence" is the inventory's derivation, and `𝐏_n` as a measure is never stated

- **Severity**: imprecision.
- **Pointer**: `main.tex:433` (bli-paper-036 and its inventory note).
- **Here**: `trajLaw_martingale` (`Kernel.lean`, kind C) proves constraint 4 at every horizon and day *over the skeleton*, where `𝐏_n` restricted to the state algebra is a probability by construction (`trajLaw_isProbOn`). The paper never says whether `𝐏_n` is a measure on the state algebra; the docstring says exactly that and keeps the ATTRIBUTION-UNVETTED label. This is not "Appendix B's martingale property".

## F-6 — Dot grid for beliefs about beliefs vs bin grid for real variables (recorded only)

- **Severity**: presentation / scope.
- **Pointer**: Extra Notes p. 6 (bli-slides-013).
- **Note**: the remark is about what can be *stipulated*: beliefs about beliefs can be forced onto a dot grid because the written-out state is rounded (`actualState`), whereas a general bounded real variable needs bins. The LIC part ("rounding does not threaten the LIC") is `bli-transfer`'s. No target here; `actualState` is the dot-grid stipulation made explicit.

## F-7 — Roman's "norm" is a linear functional

- **Severity**: presentation.
- **Pointer**: Roman's deck pp. 6–10 (bli-slides-019).
- **Here**: `massOn` is the functional `∑ F`; `massOn_add`/`massOn_smul` (its docstring notes it is linear, not a norm, on signed vectors).

## F-8 — Attribution

- **Severity**: presentation (register).
- The tent kernel (`tent1`, `tentKernel`, `tentSkeleton`), `faceGen`, the world-rounding lemma (`exists_gridRound`, `remainderRound`, `worldRound`) and the `SmallIndex` parametrization are this run's (program §7 item 14). No theorem here is named after Eisenstat, Roman or Soto; `Source:` lines cite item IDs. "Eisenstat's BLI", "Roman's construction", "Soto's chain rule" are ATTRIBUTION-UNVETTED bridge claims and appear only as such.

## F-9 — The mandate's `restrict_mem_grid` is false (new; a mandate/program-level slip, not a source error)

- **Severity**: local error in the mandate (design decision 3 / T1 lemma list); no source claims it.
- **Pointer**: `bli-finite-mandate` T1 ("`restrict_mem_grid` (uses `d_dvd`)"); `bli-program` §2.2 ("nested grids").
- **What is wrong**: "the restriction of a day-`(m+1)` grid table is a day-`m` grid table" fails when `d m < d (m+1)`: with `d m = 2`, `d (m+1) = 4`, the fine value `1/4` is not coarse. The nesting `d m ∣ d (m+1)` gives the *opposite* inclusion, `gridVals (d m) ⊆ gridVals (d (m+1))` (`gridVals_mono`). The true consequence, which is what a point-mass kernel at the current table needs, is `mem_grid_of_restrict_mem_grid`: a day-`(m+1)` table whose restriction is a coarse grid table and whose new coordinates are fine grid values is a fine grid table. The special case that holds as stated is `restrict_mem_grid_of_eq` (`d (m+1) = d m`). Dependents (`bli-trajectory` E4 point-mass kernel) should use the former.

## F-10 — `gridVals_mono` needs `0 < d'`, not `0 < d` (new; mandate-level)

- **Severity**: imprecision in the mandate.
- **Pointer**: `bli-finite-mandate` T1.
- **Note**: `d ∣ 0` holds and `gridVals 0 = {0}`, so `d ∣ d' → gridVals d ⊆ gridVals d'` is false at `d' = 0`; the lemma of record takes `0 < d'` (which implies `0 < d`). `Mesh.d_pos` supplies it.

## F-11 — `Superbelief 𝒮 d m` cannot carry `d` (new; program/mandate spelling)

- **Severity**: presentation (interface).
- **Pointer**: `bli-program` §2.4, mandate design decision 4.
- **Note**: the type `Table 𝒮 m → ℚ` does not depend on `d`; a phantom parameter is not inferable from a function type, so `Superbelief 𝒮 m` is the definition of record and `d` is an explicit argument of `IsProb`/`mean`/`Balanced`/`Kernel`. See the report's interface note 2.

## F-12 — "Largest remainder" is not what the bounds need (new; mandate naming)

- **Severity**: presentation.
- **Pointer**: `bli-finite-mandate` T4 (`largestRemainder`).
- **Note**: the error bounds `|w' i − w i| < 1/d` and `∑|w' − w| ≤ card/d` hold for *any* distribution of the missing units to coordinates with positive remainder, which the proof chooses classically; the definition is therefore named `remainderRound` (and `worldRound` on top of it) so the name does not oversell a "largest remainder" selection that is not established. A canonical computable selection is T10(b), not attempted.

## F-13 — The mandate's T9 "`norm_num` on the 9-term sum" (new; on the witness)

- **Severity**: presentation.
- **Pointer**: `bli-finite-mandate` T9; `plan` §0.4 rule 8.
- **Note**: the mass check on the witness is done as `9 · (1/9) = 1` after showing every grid table has mass exactly `1/9` (`tentLaw_t₀`, `sum_tentLaw_t₀`), which is the honest numeric form of the 9-term sum without listing tables; balance and non-degeneracy on the witness are the general theorems instantiated (`balanced_t₀`, `nonDegenerate_t₀`), and the horizon-2 martingale identity is `trajLaw_martingale` instantiated (`trajLaw_martingale_witness`), as the mandate asks ("by the theorem, not by enumeration").
