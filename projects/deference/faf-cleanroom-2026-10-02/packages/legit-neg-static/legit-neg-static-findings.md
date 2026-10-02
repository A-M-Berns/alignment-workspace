# legit-neg-static findings: errors, ill-posed claims and gaps in the sources

Formalizer agent of the faf-cleanroom run, 2026-09-29. Companion: [legit-neg-static-report](legit-neg-static-report.md), [legit-neg-static-ledger](legit-neg-static-ledger.md). Sources: `research/corrigibility/legitimacy-negatives-2026-09-25/` (cluster A, `RUN.md`, the B/C fixtures the definitions of record are pinned from), read through `corr-legit-neg-inventory` and `corr-legit-neg-2-inventory`. Severity scale ([STANDARDS](../../STANDARDS.md) §5): blocking the note's conclusion / local error / imprecision / presentation. Register: the sources are CLAUDE (unvetted by the author); every attribution to a person is ATTRIBUTION-UNVETTED.

Numbering continues the mandate's "Known issues" list (1–12); items 13+ are new to this package.

## 1. S1 prices void terminals off-diagonal (imprecision; affects the R2-S1 rows downstream)

`clusters/B/fixtures/model.py:80-94`: `S1` scores an unchosen option `c` at a legitimate terminal `(s, a)` by `u(s, c)` even when `(s, c)` is void, against the run's own "void terminals carry no scores" (the source run's `prompts/00-common.md:18`, repeated in D's NEGATIVES §0; NEGATIVES A §0 says instead that neither proposal consults `Q` on void terminals — pointer corrected in repair round 1). This convention is what makes the R2-S1 lemma true: `Problem.R2scores_S1_eq_H_of_allLeg` and `mem_ratifiable_S1_iff_of_allLeg` (`Readouts.lean`) hold *because* `S1` reads `u` on the void terminal of the unchosen option; their docstrings say "sighted evaluators". The honest variant `blindImpute` breaks the lemma: `R2_S1_lemma_fails_blindImpute` (`ToyWitnesses.lean`) shows the `H`-optimal fully legitimate `a₀` is not ratifiable with `y = 1`. Downstream, every grid verdict in the R2-S1 column should be read "with sighted evaluators".

## 2. S3 is not a `[0, 1]` score (presentation / junk value)

`model.py:122-131`: `S3 = 1 − (max_{c'} u − u_c)/D` is negative when the within-state range of `u` exceeds `D`; `S3_toy_neg` proves the value `−1/4` on B12's instance (`v = 1/4`, `w = −1`, `D = 1`). The Lean type is `ℚ`; a `Set.Icc 0 1` codomain would be false. C11(b) uses a different S3 (min–max normalisation, not formalized here; `legit-neg-pricing`'s cell).

## 3. Ordinal S3 breaks A1's bound even at `π(¬L) = 0` (local error, corrected by V1)

NEGATIVES A1 says S3 is covered "by the same computation". True for `¬L`-blindness and for shift-type S3 (`argmax_P1_shiftS3_eq_of_SealedBy`: a per-state shift cancels), false for the rank-score reading: `A1_ordinal_breaks_bound` proves `W`-regret `197/500` with `π(¬L) = 0` on VERIFY's V1 instance. It is an `L`-world distortion and the exception to A6's positive boundary.

## 4. A3b's "81 = 7 + 53 + 21" double-counts (presentation)

V4's count is 60 configurations (7 independent, 53 dependent, of which 21 unsupported). Not reproduced in Lean: A3b is proved as three iffs general in the number of atoms, with three `J = 2` witnesses (`A3b_independent`, `A3b_dependent`, `A3b_unsupported`). The sentence in A3 saying the identity was checked "on 81 instances" refers to the same 60.

## 5. A2's "whatever the agent knows" needs the agent's state outside, or untrusted in, `O` (imprecision, V6)

The necessity theorem `P1_lworld_eq_of_LIndist` is a congruence in `(π|_L, O|_L, Φ)`. If `Obs` carries the agent's day-`n` credence and the evaluators take it at face value, the harm is inferable and they pick `safe`: `A2_V6_credence_in_O` (credence `1` → `safe`; `1/100` → `risky`). `O` is a parameter of the formalization so that this narrowing is visible rather than hidden. The `Q|_L` clause of `LIndist` is not used by the congruence (it is what makes S1 an `L`-world evaluation through an `O` that reveals `Q`); recorded in the docstring.

## 6. A2c's P2 inversion holds only under the 1-at-null convention (local error in framing, V3)

Under the exclusion convention of record, the coverage barrier makes P2 pick `safe` exactly like P1 (`A2c_barrier_safe`, with `P2 silent = none`); the inversion needs the junk value `1` (`A2c_barrier_inverted_li`, a `_li` variant). `main.tex:1610` calls that convention "nonstandard" and permits ignoring it. The source's headline "the coverage barrier … is inverted by P2" should read "inverted by P2 under the LI convention only".

## 7. A5's "exactly when not conditioned on `L`" is overstated both ways (corrected)

Independence (`Cov(h, 1_L) = 0`) lets every reading escape, D2′ included; prior-ratio reweighting of `L`-conditioned counterfactuals escapes too (A3b (1) with `c = b/a`). The statement that holds is A3b's: a local-linear reading escapes for every harm profile iff `a_j c_j = b_j`, i.e. iff its `¬L` term is integrated against the prior's `¬L`-conditional law — abstractly `Phi_exact_iff`, and over the `Problem` of record `readLocal_exact_iff` (`SealedDefense.lean`; the bridge is `P1_readLocal` + `W_eq_Lpart_add_Eg`), with D2′ as the constant-weight instance whose criterion is `L ⊥ k` (`readD2'_weights_exact_iff`: iff `aW = aS`) and D3 escaping *directly*, outside the local-linear family, by `argmax_readD3_eq_argmax_W`. The original is not proved.

## 8. A6's "the agent's own ex-ante view" is an artifact of defining `W` with `π` (imprecision, V5)

The issuance-weight identity (`P1_weighted_eq_mass_mul_EU`, `SealedDefense.lean`) says the choice tracks `EU` under the prior `(1 − w, w)` that the evaluators use; it matches the yardstick iff the yardstick's prior is that one. V5's instance (`A6_V5_yardstick_prior`) has `W_π` and `W_μ` disagreeing and each weight tracking its own yardstick. The robust content: the `¬L` term must be weighted under *whichever ex-ante prior defines the standard*, never under the evaluators' posterior given `L`.

## 9. `RUN.md` §2.4 item 3's `D(a)` is ill-posed under action-dependent legitimacy (ill-posed)

It weights the two branches by the *unconditional* `P^A_n(L)`, which is not defined before the action when `L` depends on the action. Cluster C's action-conditional `P5` (`Proposals.lean`) is the only well-typed reading found; its `P(L | a) = 1` case reads no `K` (a definition note, not an error).

## 10. `W`/`H` are unconstrained expected utility (register)

`Problem.W`'s docstring carries the verifiers' caveat: "distorts relative to `W`" is not "fails by the author's concerns". No theorem in this package is named `cdot_fails_…`; names carry the property (`blind`, `regret_le`, `argmax_eq`).

## 11. Every workspace citation is out of scope (scope)

`LEGITIMATE_DEFERENCE.md`, `wiki/Corrigibility.md`, `GateIsLegitimacy.lean`, `selectionBlind_of_blind`, `regretU_eq_mass_mul_regretAuth` were not opened. Where the slice re-derives their content over the toy (A0's identity, item 2-030's selection-blindness lemma, the ungated rule term), the Lean here is the slice's reading formalized over the `Problem` of record, not a statement about the workspace.

## 12. Every cluster-A fixture check is a grid or an instance, none a seeded sample (presentation)

See the report's evidence table.

## 13. The gated-vs-ungated rule term: gating is inert for the `P1` form under sealing; the mandate's inversion is real for the plain-EU form (imprecision in the mandate's expected witness; scoped by audit r1)

The mandate expected an N− witness "showing the gated variant fails (A1's family with the harm declared and `q` near 1)". **For the `P1` form** that witness does not exist as an inversion: under `SealedBy ℓ`, `P1` is itself `[leg]`-gated, so the gated rule-scored `P1` is `P1 V a − ϖ n a · π(L)`, and with `0 ≤ V ≤ D`, `ϖ > D` it still excludes every declared violator for `π(L) > 0` (`ruleScore_gated_excludes_of_mass_pos`, `SealedDefense.lean`). On A1's family with the harm declared, `risky` is rejected under both gatings for every `q < 1`. The gated `P1` form fails only when the violator's legitimate mass is zero *and* the compliant option scores zero on its legitimate terminals, and then only by a tie (`ruleScore_gated_tie_witness`), because with `V ≥ 0` no option can be strictly below the violator's `0`; a strict inversion would need a negative legitimate score, outside the theorem's own range. **For the plain-EU form** (`ruleScore_EU_excludes`, a score that accrues value on void worlds) the mandate's trap is exactly right: on the void-heavy `toyB 0 1 0 1 (9/10)` (`π(b) = 9/10`; the violator `a₁` legitimate on `g` only, so `P(L | a₁) = 1/10`; `0 ≤ u ≤ 1`; `ϖ = 2 > D = 1`) the ungated EU score excludes `a₁` (`1 − 2 < 0`) while the `[leg]`-gated `W Q a − ϖ n a · P(L | a)` picks it strictly (`1 − 2/10 = 4/5 > 0`): `ruleScore_EU_gated_inverts` (`voidHeavy`, `gatedEUrule`). So the honest statement is: gating is inert exactly for scores that are themselves `[leg]`-gated (the `P1` form, where the ungated term's only advantage is at `π(L) = 0` / fully voiding violations, and there by a tie); for any score that accrues value on void worlds, gating fails on void-heavy priors under action-dependent legitimacy. Severity: imprecision (in the mandate/plan's expected witness for the `P1` form; NEGATIVES claims only the ungated escape, and the plain-EU trap is as the mandate has it). The first version of this finding overgeneralised the `P1` fact to rule terms in general; corrected in repair round 1 (audit r1 adversarial N1).

## 14. A2's converse needs no positivity of `π(¬L)` (strengthening, not an error)

NEGATIVES states the converse identity `J₁ = π(L) W` with `m_b = E[Q | ¬L]`; at `π(¬L) = 0` the source's `m_b` is a division by zero. `P1_inferable_eq_mass_mul_W` holds with no hypothesis: the `¬L` sum vanishes state by state (`prior_eq_zero_of_mass_eq_zero`) and `0 · junk = 0`. The argmax statement needs `0 < π(L)` only.

## 15. The quantitative refinement of A2 (item 2-010) has its expected posterior misreported (presentation)

Item 2-010 gives `E_o[post(θ₂ | o)] ≈ 0.085` at `acc = 9/10`, `r = 1/100`. From the fixture's own formula, `post(θ₂ | o) = 1/12`, `post(θ₂ | o') = 1/892`, so the expectation is `(9/10)(1/12) + (1/10)(1/892) = 67/892 ≈ 0.0751`. The item's comparison "`≈ 0.085 < 0.2`" also misstates the threshold: by its own criterion (`safe` iff `q · E_o[post] · harm > (1−q)δ`) the bound on `E_o[post]` is `(1−q)δ/(q · harm) = 1/10`, not `0.2`; the verdict is unchanged (`0.0751 < 0.1`). The conclusion (`0.0376 < 0.05`, `risky`) is unchanged. Stretch S2 (the general iff) was not formalized; the design is in the report's §"Stretch and what was not done".

## 16. The mandate's "P4a is P3 with `λ = 1` under sealing" needs the tie-break read correctly (imprecision)

Under `SealedBy ℓ`, `PL` is constant so `P4a`'s first coordinate never separates options and the lexicographic argmax is the argmax of the second coordinate, `P3 W 1 V` — true as an argmax statement (`argmaxLex_P4a_eq_argmax_P3_of_SealedBy`, `BlindnessChar.lean`), not as an identity of scores.
