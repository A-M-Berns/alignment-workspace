# legit-finite-defect — findings about the sources

Findings per [STANDARDS](../../STANDARDS.md) §5, from the formalizer of package `legit-finite-defect` (faf-cleanroom run, 2026-09-29/30). Severities: **blocking** (the note's conclusion does not survive) / **local error** / **imprecision** / **presentation**. Pointers are to the sources named in `legit-finite-defect-mandate`; Lean names are in `Cleanroom/Trust/LegitFiniteDefect/`.

## F1. "The wirehead is exactly an operation that drives the defect strictly negative" is false as a consequence of "reported utility rises" — local error in the prose, theorem correct

- **Where**: `models/legitimacy-corrigibility-model.md` §0 and §2.2 (headline sentence); the red team's Finding 1 (`redteam/legitimacy-corrigibility-redteam.md` (a)).
- **What**: the proved statement (`wirehead_declined`) needs *pointwise* overstatement `θ_x ≤ E_drug_x`; "average reported utility rises" is strictly weaker and does not give the sign. Compiled witness: `Wirehead.numb_average_rises` (average report rises by `3/40`) with `Wirehead.numb_defect_pos` (defect `+1/40 > 0` on the model's own gate `𝟙[R > 1/2]`, which `Wirehead.numb_gate_eq_ind` identifies with `ind {0}`).
- **Corrected version**: the characterisation `defect_nonpos_on_iff` — nonpositive defect on every nonnegative weight supported in `S` **iff** overstatement at every positive-mass world of `S`. The dangerous drugs are the *overstating* ones; a numbing drug that under-reports the real good is invisible or positive-defect, not declined.
- **Severity**: local error (prose); the theorem is correct and the corrected statement is now proved as an iff.

## F2. "Declines" is a tie — presentation

- **Where**: model §2.2 clause 1, §2.4 table row "decision by current-endorsement: decline"; the red team's Finding 2.
- **What**: `V_now(drug) = E_π θ = V_now(abstain)`: under current endorsement the agent is *indifferent*; "declines" means "never strictly prefers the drug", which is `defect ≤ 0`. The strictly negative number (`−13/20` in §2.4) is the report-valuation gap, not a strict abstention incentive. Recorded as a remark; nothing in the package is named `declines`.
- **Severity**: presentation.

## F3. The report's D5 row and the "corrigibility theorem" wording oversell — presentation

- **Where**: trust-lab-020's flag ("the report's D5 row still says 'drives the defect ≤ 0 … ⇒ abstention'"); trust-lab-021's flag ("report over-reads it as a corrigibility theorem").
- **What**: `complyAdv_nonneg_of_endorsed` / `complyAdv_nonpos_of_adversarial` are sign lemmas over the model's *pointwise encodings* ("endorsement-faithful" := `0 ≤ s x (2 d x − 1)`); the content is the encoding plus linearity (kind L). What is real is the witness: one frame, three signals, advantages `+1/2, 0, −1/2`, with the blank signal failing both encodings (`Corrigibility.three_signals`, `Corrigibility.hypotheses_discriminate`). "Corrigibility" is interpretation.
- **Severity**: presentation.

## F4. Round 3's "kernel-checked" claims were self-reported; every number re-derived here agrees — imprecision (status), no numerical error found

- **Where**: `trust-lab-inventory` header point 1; items 050–054.
- **What**: round 3 never had a verification phase. This package is the first check of items 050–054 and of the §B.4 table. Every re-derived value agrees with the self-report: trace `[(1/2,1/2),(5/8,5/8),(3/4,3/4),(3/4,3/4)]`, defects `0` and `1/2` (`Trace.d_pair`); `9/256`, `7/16`, `3/4`, `9/1024`, `3/20`, `−9/16` (`StopGradient.*`); `J_all(honest) = −3/16`, `J_all(wirehead 3/4) = −7/64`, `J_L(wirehead s) = −1/4`, the Brier flip at `2/5` (`Residue.base_wirehead`, `Residue.base_flip`); the log signs at `1/5, 2/5, 3/5` (`LogCompare.base_log_residue`).
- **Severity**: imprecision (in the sources' status labels only).

## F5. Item 054's closed form was paper-sketched and grid-asserted; it is now kernel-derived for general parameters — imprecision

- **Where**: `stop-gradient-steering` §B.4 ("closed form `J_L(steer σ) = −(1−σ)(3+5σ)/16` asserted on the whole grid (paper derivation: steered posteriors `q_y = σ + (1 − σ)P_y` with `P₁ = 3/4, P₀ = 1/4`; boundary from `(1 − σ)(3 + 5σ) = 3 ⟺ σ(2 − 5σ) = 0`)").
- **What**: the source had the one-line paper derivation and checked the form on an exact-rational grid; what was missing was a proof, not the idea (an earlier title of this finding, "observed, not derived", was unfair — audit round 1, fidelity N2). `Residue.residue_closed_form` derives `J_L(steer σ) − J_L(honest) = σ (A + σ B)` for all parameters with positive `Y₁`-groups, and `Residue.base_closed_form` recovers the baseline polynomial from it as a corollary; the zeros in `σ` are exactly `0` and `2/5` (`Residue.base_flip`). The grid assertion becomes a theorem over all `σ`.
- **Severity**: imprecision (plan §0.4 rule 4).

## F6. Item 2-035's "grid limitation declared loudly" is unnecessary — imprecision

- **Where**: `run3/questions/scout-fresh-eyes.md` Q3 (ii) ("on the declared finite grid … the grid limitation declared loudly").
- **What**: with `lit-ddb-frames`'s cycle (`totalTrust_iff_hullAndModestlyInformed`) Total Trust under the clean prior is proved with the exact `∀ X s` quantifier (`Mechanism.totalTrust_clean`), and failure under every mixture with `0 < λ` is one explicit `(X, s)` (`Mechanism.not_totalTrust_mix`). No grid.
- **Severity**: imprecision.

## F7. Item 2-043 (ii) is circular as written — imprecision

- **Where**: `run3/questions/scout-acceleration.md` Q6 (ii) ("if `inf_{a∈[0,1]} |s(a) − a| ≥ J` then every quote has defect ≥ `J`").
- **What**: that is the definition of an infimum, not a theorem. The well-posed content is the *computed* infimum: `Settlement.isGLB_settleGap_antiIndAt` proves `min c (1 − c)` is the greatest lower bound of the anti-indicator's gap over `[0, 1]` for every level `c`, with the `c = 1/2` case re-proving lean-deference's `no_exact_quote` + `residual_half`. The fixed-point half (i) is the genuinely new positive statement (`Settlement.exists_fixedPoint`). The reading "feedback is legitimate iff the settlement responds continuously" is ATTRIBUTION-UNVETTED interpretation and is kept in prose.
- **Severity**: imprecision.

## F8. The log-score flip boundary differs from Brier's — a finding about rule-dependence, not a bug

- **Where**: item 2-047 (a); `stop-gradient-steering` §B.4 ("Scoring-rule dependence").
- **What**: at the baseline the Brier residue is exactly `0` at `σ = 2/5` (`Residue.base_flip`), while the log residue is already strictly positive at `2/5` (`LogCompare.base_log_residue`, decided by the exact rational comparison `(3/4)^30 (1/4)^10 < (17/20)^17 (3/20)^3 (11/20)^11 (9/20)^9`) and still strictly negative at `7/20` (`LogCompare.base_log_flip_bracket`, repair round 1: `(67/80)^67 (13/80)^13 (41/80)^41 (39/80)^39 < (3/4)^120 (1/4)^40`), so the log flip is bracketed to `(7/20, 2/5)` exactly as the source's sweep says. Signs agree at `1/5` (negative) and `3/5` (positive). The *location* of the flip is a property of the scoring rule; only the existence of the residue region is rule-robust. Statements about "the" flip should name the rule.
- **Severity**: imprecision (in any prose that quotes `2/5` without naming Brier).

## F9. Item 2-030's "Value strictly drops" needs a declared tie rule; the instance holds under "act iff `R ≥ c`" — imprecision

- **Where**: `run3/questions/scout-legitimacy.md` Q2 (3) ("argmax-following Value strictly drops").
- **What**: the coexistence instance is proved for the declared two-option rule "act iff `R ≥ c`" (the dependency's `Frame.twoOption` when the report is a frame expert's — `thresholdValue_frameReport`), with `c = 2/5` separating the reports: `1/5` vs `1/10` (`Detection.Coexist.value_drop`). The general "a garbling never gains" is `tt-finite-frames`'s and is not proved here; the instance is N+ because the fine report is itself a proper garbling (`Detection.Coexist.Rfine_ne_θ`) and the threshold separates the two reports.
- **Severity**: imprecision (a tie rule must be declared for "Value drops" to be a statement).

## F10. Item 050's impossibility is two-point; the identified-set theorem shows it is generic for interior traces — extension, no error

- **Where**: `trace-nonrecoverability` §8 caveat 2 ("the quantifier over systems is existential (one indistinguishable pair)"); §5 strengthening (a).
- **What**: `Trace.IdentifiedSet.exists_faithful`, `exists_steered` and `d_le_D` prove that for *every* valid system with interior terminal opinion the trace is consistent with defect `0` and with the maximal defect `D > 0` (`max Y₃ (1 − Y₃)` when `a₃ = Y₃`, `Y₃` when `a₃ > Y₃`, `1 − Y₃` when `a₃ < Y₃`), and no trace-consistent valid system exceeds `D`. So no valid trace with an interior terminal opinion identifies legitimacy — the existential over systems becomes a universal over traces. Caveat 2 can be retired for this class. Repair round 1 adds the intermediate values: `Trace.IdentifiedSet.exists_defect_eq` (every `δ ∈ [0, D]` is attained) and `defect_consistent_iff` (the trace-consistent defects are *exactly* `[0, D]`), so the identified set is the full interval, not just its endpoints.
- **Severity**: none (extension recorded so the note can be updated).

## F14. The `e₂ = 1/8` Brier boundary is exactly `σ = 18/73` — extension, no error

- **Where**: `stop-gradient-steering` §B.4 ("The secondary sweep (`e₂ = 1/8`) moves the baseline boundary down to `(1/5, 1/4)`").
- **What**: `Residue.e2_row` instantiates `residue_closed_form` at `p = 1/2, e₁ = 1/4, e₂ = 1/8`: posteriors `P(G = 1 | Y₁ = 1) = 11/16`, `P(G = 1 | Y₁ = 0) = 5/16`, `A = −9/128`, `B = 73/256`, so the residue `σ(A + σB)` vanishes at `σ = −A/B = 18/73 ≈ 0.2466`, inside the source's bracket, and nowhere else in `(0, 1]`. The source's sweep step `1/20` could only bracket it; the derived closed form locates it. (In general the boundary is `σ* = −A/B` whenever `A < 0`, which is what `regime_iff` says in the other direction.)
- **Severity**: none (a sharpening the note can quote).

## F15. The mandate's monotone-settlement stretch formula `min (s(c⁻) − c) (c − s(c⁺))` is false; the gap at the crossing is a third term — local error (in the mandate, not a source note)

- **Where**: `legit-finite-defect-mandate` Target 11, "Stretch: for a nonincreasing `s` on `[0,1]` without a fixed point, the gap infimum equals the distance from the diagonal at the crossing (`min (s(c⁻) − c) (c − s(c⁺))`)". Provenance: the mandate-writer's — inventory item 2-043 and `scout-acceleration.md` Q6 (ii) state only the computed-infimum target and leave the jump hypothesis "to the executor to fix".
- **What**: an antitone settlement without a fixed point crosses the diagonal once, at `c = sSup {a ∈ [0,1] | a < s a}`, and the gap `|s a − a|` is decreasing on `[0, c)` and increasing on `(c, 1]`, so its infimum on each side is the one-sided limit term — but the value of `s` *at* `c` is unconstrained between the two limits and its gap `|s c − c|` is a third candidate for the infimum, which the two-term formula omits. Compiled: `Settlement.Crossing.jump_counterexample` — `s = 1` on `[0, 1/2)`, `s (1/2) = 5/8`, `s = 0` on `(1/2, 1]` is antitone, self-mapping and fixed-point-free; its crossing is `1/2` with one-sided values `1` and `0`, so the two-term formula evaluates to `min (1 − 1/2) (1/2 − 0) = 1/2`, but the greatest lower bound of the gap over `[0, 1]` is `1/8` (attained at `1/2`). The corrected theorem, `Settlement.Crossing.isGLB_settleGap_crossing`, has three terms, `min |s c − c| (min (s(c⁻) − c) (c − s(c⁺)))`, for crossings `c ∈ (0, 1)`; `antiIndAt_via_crossing` checks it reproduces the anti-indicator's `min c (1 − c)` (`isGLB_settleGap_antiIndAt`). For the anti-indicator the middle term equals the left one (`s c = 1`), which is presumably why the omission went unnoticed.
- **Severity**: local error in the mandate's stretch statement (no source note makes the two-term claim); the corrected statement is proved.

## F11. `Frame.report` cannot be spelled as a dot-notation field of the dependency's `Frame` — presentation

- **Where**: mandate Target 1 (`Frame.report (F : Frame W) (θ)`).
- **What**: a declaration named `Frame.report` inside this package's namespace would not resolve under `F.report` (dot-notation looks in `Cleanroom.Found.LitDdbFrames.Frame`), and adding to the dependency's namespace is defining in another package. The bridge is `frameReport F θ`, with the `θ`-instance lemma `TotalTrust.report_ineq` (literally `h θ s`) and `thresholdValue_frameReport` connecting the threshold rule to `stratValue π (F.twoOption θ c) − c`.
- **Severity**: presentation (naming only).

## F12. `MeasurableWrt` in the dependency requires a finite question type; the package's `DeterminedBy` does not — no error, recorded for `legit-li-register`

- **Where**: `lit-ddb-frames` `Local.lean` (`MeasurableWrt` with `[Fintype C] [DecidableEq C]`, verified by the mandate).
- **What**: a real-valued report cannot be a `MeasurableWrt` question, so the package defines `DeterminedBy Q w` without finiteness and proves `determinedBy_iff_measurableWrt` for finite `C`. The characterisation `endorses_questionGates_iff` therefore holds for any question type with decidable equality, which is what makes the report case (`C = ℝ`) an instance rather than a separate proof.
- **Severity**: none (API note).

## F13. The model's own §2.4 micro-example does not satisfy the hypothesis of the §2.2 theorem it illustrates; the red team's "non-vacuous (micro-example satisfies it)" is false — local error (model §2.4 as an illustration of §2.2; red team (b))

- **Where**: `models/legitimacy-corrigibility-model.md` §2.4 ("Worked micro-example (PROVED by hand and by script)": `π = (1/4, 3/4)`, `θ = (1, 0)`, `E_drug = (9/10, 9/10)`, `w = (1, 1)`, defect `−13/20`) against §2.2 ("Suppose at every world the drugged self's reported estimate pointwise overstates the target: `θ_x ≤ E_drug(θ)_x`"); `redteam/legitimacy-corrigibility-redteam.md` (b) ("`wirehead_declined`: … Non-vacuous (micro-example satisfies it)"). Found by the round-1 adversarial auditor (probe P1); compiled here as `Wirehead.WireheadModel.*`.
- **What**: at the good world `h`, `θ_h = 1 > 9/10 = E_drug,h`, so the pointwise-overstatement hypothesis fails (`WireheadModel.drug_not_overstating`). The number `−13/20` on `w = (1, 1)` is correct (`drug_defect_on_ones`), but on the point mass at `h` the same drug has defect `+1/40 > 0` (`drug_point_mass_pos`), so by `defect_nonpos_on_iff` the model's drug is *not* nonpositive on the full class of nonnegative gates (`drug_not_nonpos_on_class`). Two consequences: (i) the model's flagship example illustrates that the §2.2 hypothesis is *sufficient but not necessary* for one fixed gate — it is not an instance of the theorem; (ii) it is the very kind of drug (under-reporting the real good, over-reporting in the bad world) that the iff says is not declined on the class. The red team checked non-vacuity by the wrong example. A witness that *does* satisfy `θ ≤ R` pointwise with a non-constant report is the example repaired, `E_drug = (1, 9/10)` (`WireheadModel.RdrugFix`): honest in the good world, "happy" in the bad one; `drugFix_overstates`, `drugFix_defect_nonpos_on_class` (defect `≤ 0` on every nonnegative gate, `−27/40` on `w = (1, 1)`), `drugFix_strict`. This is now the ledger's witness for the instances `defect_nonpos_of_overstates` / `defect_neg_of_strict_overstate`, whose earlier witness pointers ("as above") named the numb and localised examples, which fail the global hypothesis — a package-side imprecision found while writing this finding, fixed in repair round 1.
- **Severity**: local error (in the model's §2.4 status "PROVED … " read as an illustration of §2.2, and in the red team's (b)); the §2.2 theorem itself is correct and untouched. Nothing downstream in the model relies on the example being an instance of the theorem — the table's `−13/20` is a fixed-gate computation and stays true.
