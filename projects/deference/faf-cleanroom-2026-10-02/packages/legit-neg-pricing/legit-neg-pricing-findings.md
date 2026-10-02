# legit-neg-pricing findings: errors, ill-posed claims and gaps in the sources

Formalizer agent of the faf-cleanroom run, 2026-09-30. Companion: [legit-neg-pricing-report](legit-neg-pricing-report.md), [legit-neg-pricing-ledger](legit-neg-pricing-ledger.md). Sources: `research/corrigibility/legitimacy-negatives-2026-09-25/` (clusters B and C, `SYNTHESIS.md`), read through `corr-legit-neg-inventory` and `corr-legit-neg-2-inventory`; VERIFY files authoritative. Severity scale ([STANDARDS](../../STANDARDS.md) §5): blocking the note's conclusion / local error / imprecision / presentation. Register: the sources are CLAUDE (unvetted by the author); every attribution to a person is ATTRIBUTION-UNVETTED.

Numbering continues [legit-neg-static-findings](../legit-neg-static/legit-neg-static-findings.md) (1–16). Items 17–27 are the mandate's "Known issues" as this package met them (each says what the Lean does about it); items 28+ are new to this package. The item-064 table is at the end.

## 17. S1 is sighted off-diagonal (imprecision; carried from static finding 1)

Every R2-S1 statement here (`B14_toy`, `B16_R2`, `B17_R2ref`, `V14_*`, `ratifiable_S2` is S2, not S1) holds *because* `S1` prices the void terminal of an unchosen option. Docstrings say "sighted evaluators"; the blind variants are `Problem.blindImpute` (B17 (ii), `B17_R2ref`) and this package's `blindRelS3` (B12). Nothing here re-derives the R2-S1 lemma; it is cited from `legit-neg-static`.

## 18. `S3` is not `[0, 1]`-valued; C11(b)'s S3 is a different normalisation (presentation; carried from static finding 2)

No headline here adds a range hypothesis to `S3`: `P2_S3_eq_one_of_hindsight_best`, `B12_sighted`, `S3_eq_reanchor`, `thin_P2_S3` are all over the ℚ-valued `S3`. C11(b)'s min–max normalisation is `S3norm` (target 27, `S2Collapse.lean`), a separate definition of record.

## 19. B2's fixture folds the penalty into `u` (imprecision, B VERIFY on B2)

`toyC v p x` has `u(g, a₁) = 1 − p`, so `H` is penalised too. This package states the chat's `(1 − v)/2` on `toyC` (`toyC_P2_news`, `C1_toy`) and the δ-form `π_g δ + π_b (1 − v)` on the hybrid of record `toyB v w (1 − δ) 1 π_b` with `hybridV` (penalty in `V` only, `H` clean; `hybrid_P2_news`, `B16_*`, `C9_state_g`). Every theorem's docstring names its toy.

## 20. B6's conservativity needs a fully legitimate alternative; B8 attained only at the tie; B9/B10/B19 register-narrowed (imprecision; V6, V9, V10, V19)

`H_conservative_of_allLeg` carries `∀ s, leg s b = true` as a hypothesis, and `V6_witness` proves it cannot be dropped (all void values `≥ 0`, cdot picks the more-voiding option, `H` the other). `B8_attained` states the tie at `ε = 0` as the attainment (and that `η = 1` makes `P2 = none`, rather than excluding it). `B9_over_protection`'s docstring carries the register (a distortion relative to `H`; the author's own steering worry from `H`'s side, ATTRIBUTION-UNVETTED); `V10_witness` gives the floor case of the double counting; `V19_S3_overprotects` the S3 rescue's over-protection at the floor.

## 21. B14: "R2 is not a decision rule" is too strong; B15's R2 clause was a tautology (imprecision; V14, V15)

`MixedRatifiable` is the well-typed fixed-point predicate; `V14_scenario_N`/`_C` exhibit interior mixed fixed points; `selectDiag` with `V14_selectDiag_N`/`_C` shows the own-diagonal selection reproduces R1-P1 (instances only, as the mandate directs). `B15_toy` makes no R2 claim.

## 22. C2a's "G3 is the LI default" is contested; C2b's "P4b `q`-free" is false; C3 needs `P(L | a*) > 0`; C7's fixture depends on an imaged report; C10's numbers are normalisation-dependent; C9's matrix row omits P3/P5; "P4b the only row with no unconditional fails" narrowed (imprecision; C VERIFY)

`C2a_capture`'s docstring says "G3 as the source". `argmaxOpt_R2scoresP2_eq` carries `P(L | a*) ≠ 0` and `R2_at_void` gives the V1 boundary. C2b (`Voi.lean`, target 22) states V2's `q`-dependence of `P4b`; C7's positivity instance (`CrossBranch.lean`, target 21) is the verifier's; C10's flip credences (`Lexical.lean`, target 24) are docstringed "illustrative"; C9's V5 correction is recorded in `C9_state_b`'s docstring (P3/P5's T1 protection relies on `p ≥ x − v`, `c − v`, from `C1_toy`); no name or docstring claims P4b is unconditionally safe.

## 23. C1's fixture never asserts cdot's tie at `v = p = 0` (presentation; inventory 033)

Asserted here: `toyC_P1_keeps_iff` (`= univ ↔ v + p = 0`) and `C1_toy` (tie iff `v = 0 ∧ p = 0` for `v, p ≥ 0`).

## 24. `P5`'s weights are action-conditional (ill-posed in `RUN.md`; static finding 9)

Every P5 statement here is over `legit-neg-static`'s action-conditional `P5` through `P5_of_ne`; the `P(L | a) = 1` branch (which reads no `K`) is used explicitly in `P5_void_sub_keep` and the toy P5 lemmas (`toyC_P5`, `C2a_capture`, `C8_witness`).

## 25. Every "relation to the workspace" paragraph is out of scope (scope)

B14, B15, C2a, 2-030, 2-031: the in-scope lemmas are `mem_ratifiable_congr`, `allvoid_ratifiable`, `MixedRatifiable`, `mismatchMass`, `P4b_const_void`, and static's `ratifiable_eq_argmax_of_SelectionBlind` (cited). `research/alignment-workspace/` was not opened.

## 26. Attribution (register)

B11's identification with "the author's LI challenge" and every reading of the co-maintainer's intent are ATTRIBUTION-UNVETTED (`P1_S2sel_eq_P1_S1`'s docstring; the report's register line).

## 27. Evidence grades (presentation; 2-007)

No grid is enumerated in Lean. Universal statements are proved by algebra over the `Problem` of record (B1, B2, B3, B5, B6, B8b, B10, B11 (i)/(ii), B13, C3, C5, 2-031, C1's identity); fixture points are witnesses, one per headline (`norm_num`); `decide` is used only on `Fin 4` partition axioms (`S2cell_witness4`) and `Fin 4` subset facts (`b4arm`).

## 28. B1's cdot clause "P1 keeps for `ε < 1`" is not exact as stated (imprecision; new)

NEGATIVES B1 / the fixture's check `if eps < 1: argmax(p1) == {"keep"}` is true for the fixture's `η = 10⁻⁶`, but the general condition is `ε (1/2 + η) < 1/2`, i.e. `ε < 1/(1 + 2η)`: with a large bonus `η` on the thinned option, cdot takes it at some `ε < 1`. `B1_witness` states the exact condition. Severity: imprecision (the fixture's assertion is correct on its own grid).

## 29. B3's "equality iff every kept state attains the max" needs a positive-prior qualification (imprecision; new)

A kept state of prior mass `0` can carry any `x` without moving the conditional mean; `Hcond_kept_eq_xmax_iff` and `Bstar_subset_of_optimal` are stated on states of positive prior. Likewise B3's `P1 (void B) = P1 keep` iff `x = 0` on `B` (`P1_void_le_keep`). Severity: imprecision.

## 30. The S2cell identity holds without `L_a`-purity (strengthening, not an error; new)

`P1_S2cell_eq`: for any partition of the states, `P1 (S2cell) a = ∑ t, π t · u t a · P(L_a | cell t)` — the cell-conditional legitimacy probability replaces the indicator. V11's collapse is the pure case (`condLeg_eq_ind_of_pure`), and the extension's covariance form is the general case (`PartialCollapse.lean`). Recorded because the source states only the pure case.

## 31. B8b's hypothesis package is one-sided (presentation; new)

The bound `H b − H a ≤ D · P(¬L | b) − 𝔼[(1 − ℓ_a) u_a]` needs only `0 ≤ u` on `a`'s void terminals and `u ≤ D` on `b`'s (`B8b_bound`); the source's "`u ∈ [0, D]`" is more than needed. Not an error.

## 32. The C1 general identity's "P5 with `P(¬L | a₁) 𝔼(K | L, a₁)` in place of the `B` sum" is a difference of two terms, not a substitution (presentation; new)

`P5_void_sub_keep`: `(P1 a₁ + (1 − P(L | a₁)) K̄ a₁) − P1 a₀` equals the off-`B` score difference plus `π(B) K̄ a₁ − ∑_{s ∈ B} π V_{s,a₀}(a₀)` — the `B` sum's `V_{s,a₀}(a₀)` part survives; only the `W` part is replaced by `π(B) K̄`. NEGATIVES C1's sentence is right in spirit and imprecise in wording.

## 33. C7's original fixture is not formalised: its flip is an artefact of an imaged report at a zero-mass cell (presentation; V3, recorded)

`c07_cross_branch_reflection.py` has `P(L | state) = 1, 1/2, 0` on three equiprobable states, so at `g` the conditional `𝔼[U | a, ¬L, g]` does not exist and the assessor must image it; V3 shows that imaging `risky` at `0` there makes P5 pick `safe`. `CrossBranch.lean` therefore carries V3's positivity instance (`V3_witness`) as the witness for `P5_located_eq_forall_iff`, and states the general bridge with the report vector `k` free (`locatedK k`) — an imaged value is a choice of `k` at that cell, not a fact about the problem. `trueK` at a zero-mass cell is `Hcond`'s junk `0`; `Hpart_located` shows such a cell contributes `0 · junk = 0` to `H`, so no headline depends on it. Severity: presentation (the verifier already narrowed the fixture; recorded so that nobody re-imports the original numbers as a witness).

## 34. The mandate's extension conjecture is derived, with a junk-free form (strengthening; new)

`P1_S2cell_sub_P1_S1` (`PartialCollapse.lean`): for any partition of the states into cells of positive mass, `P1 (S2cell) a − P1 (S1 u) a = ∑_C (π(C ∧ L_a) ∑_{C ∧ ¬L_a} π u − π(C ∧ ¬L_a) ∑_{C ∧ L_a} π u)/π(C)`; under positivity of both parts of a cell the term is the conjectured `π(C ∧ L_a) π(C ∧ ¬L_a)/π(C) · (𝔼[u_a | C ∧ ¬L_a] − 𝔼[u_a | C ∧ L_a])` (`cellCov_eq_cov`), and it vanishes iff the cell is `L_a`-pure or has equal conditional means (`cellCov_eq_zero_iff`). The conjecture's product form is only stated where both conditional means exist; the difference itself needs no such positivity. Not an error in the source (the source states only the pure case); recorded as the extension's result.

## 35. C2b's threshold `r(1 − max(q, 1 − q))` is the `q ≥ 1/2` case of an identity that holds for every `q` in the fixture's model (presentation; new)

`C2b_P3` (`Voi.lean`): `P3 a₁ − P3 a₀ = (g − r(1 − q))/2` for every `q ∈ [0, 1]` on `voiProblem q r g`, because the model (the fixture's `voi_problem`) fixes the agent's void-branch act to hypothesis `A`; `max(q, 1 − q)` describes an agent that acts on its better hypothesis, which the fixture does not model. NEGATIVES C2b's "for `q ≥ 1/2`" is correct and its `max` is decorative in the fixture. Severity: presentation.

## The item-064 table: the synthesis's necessary-condition list, one row per condition

`SYNTHESIS.md` §2 items 1–9 and "Where the defense is ruled out", each mapped to the declaration that witnesses it (`legit-neg-static` = LNS, `legit-neg-pricing` = LNP), or to `legit-neg-dynamic` (LND, for the D/E rows), or "ARGUMENT, no declaration". Register: the "necessary" reading is the run's; every reading of the co-maintainer's intent is ATTRIBUTION-UNVETTED.

| §2 condition | Source items | Declaration(s) | Status |
|---|---|---|---|
| 1. Inferability | A2 (007), A2c (008) | LNS `Problem.P1_lworld_eq_of_LIndist`, `argmax_P1_lworld_eq_of_LIndist`, `A2_witness`; the escape's incentive `A2c_barrier_safe` | proved (LNS) |
| 2. Ex-ante, not posterior, conditioning | A3 (009), A3b (010), B11 (023), A6/V5 (014, 2-011) | LNS `condExp_gap_eq_neg_cov_div`, `Phi_exact_iff`, `exists_Phi_exact_iff`, `Problem.readLocal_exact_iff`; LNP `P1_S2sel_eq_P1_S1`, `P1_S2cell_eq_P1_S1_of_pure`, `P1_S2cell_eq`; LNS `P1_weighted_eq_mass_mul_EU`, `A6_V5_yardstick_prior` | proved (LNS + LNP) |
| 3. Positivity, violated by voiding actions by construction | C8 (041), C7 (040) | LNP `C8_structural`, `C8_witness`; C7's iff `CrossBranch.lean` (target 21) | proved (LNP; C7 see target 21) |
| 4. S2 reference information independent of the agent's information-gathering | D3 (048) | LND | not this package |
| 5. Under cdot, S2 double-counts | B10 (022) | LNP `P1_S2_eq`, `B10_witness`, `V10_witness`; the repair's scale `impWeighted_unbounded` | proved (LNP) |
| 6. For conditioning the defense is S2-accurate evaluation, and then P2 is unconstrained EU | B10 (022), C11 (044) | LNP `P2_S2_eq`, `P2_betScore_EN`; C11(a) `S2Collapse.lean` (target 27) | proved (LNP); the P5 identification is ARGUMENT (`S2Collapse.lean` docstring) |
| 7. Readout: under R2/R3 the floor, tier and gap cancel; the surviving branch's humans must mark down their own realized option | C3 (036), B16 (028), B17 (029) | LNP `argmaxOpt_R2scoresP2_eq`, `argmax_R2scoresP4b_eq_P3`, `argmaxLex_R2scoresP4a_eq`, `ratifiable_eq_ratifiableP2_union`; `B16_R2` (`a₁ ∈ ratifiable ↔ p ≤ δ`); `ratifiable_S2`; R3: LNS `ratifiable_eq_argmax_of_SelectionBlind` | proved (LNP + LNS) |
| 8. Timing and deterrence | D1 (045), B19 (030), D4 (049, 050), D5 (051) | LNP `B19`, `B19_below_floor`, `V19_S3_overprotects`, `B20`, `C9_state_b`, `C9_state_g`; D1/D4/D5 → LND | B19/B20/C9 proved (LNP); the rest LND |
| 9. Meta-revision | E1 (053), E3 (055), E6 (056); C10 (043) | LND for E1/E3/E6; C10's flip credence `Lexical.lean` (target 24) | LND; C10 see target 24 |
| Ruled out: `¬L` harms not determined by `L`-observables, agent's state unconsulted | A2 (007) | LNS `P1_lworld_eq_of_LIndist`, `A2_witness` | proved (LNS) |
| Ruled out: atoms with `¬L` mass and no `L` mass | A3b (010), C8 (041) | LNS `exists_Phi_exact_iff` (absolute continuity), `A3b_unsupported`; LNP `C8_structural` | proved (LNS + LNP) |
| Ruled out: protection of the sealed occurrence's own `C_n` | A4a (011) | LNS `Problem.PL_eq_mass_of_SealedBy`, `PL_const_of_SealedBy` | proved (LNS) |
| Ruled out: void-branch deterrence under the floor, by scores alone | D5 (051) | LND | not this package |
| Ruled out: policy-level deterrent value learned on-path | D4 (iv) (050) | LND | not this package |
| Partial escape: the lexical authority term for declared violations | A4 (012), 2-024 | LNS `Problem.ruleScore_ungated_excludes` | proved (LNS); "learned rules inherit A3's bias" is ARGUMENT, no declaration |
| Pattern: "wherever the defense succeeds it has imported a narrow updatelessness" | A6 (014), D7 | ARGUMENT, no declaration (A6's positive boundary is LNS `A6_positive_boundary`) | recorded only |
