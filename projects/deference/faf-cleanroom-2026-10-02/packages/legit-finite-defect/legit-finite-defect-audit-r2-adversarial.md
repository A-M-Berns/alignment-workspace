# legit-finite-defect — audit round 2, lens: adversarial

Auditor: a fresh-context agent of the faf-cleanroom run (2026-09-30) that did not write the package and did not write round 1's audits or the repair. Binding: `00-common`, [STANDARDS](../../STANDARDS.md), `run/prompts/audit.md`; patterns from `AUDIT` §0.2 and §3. Read: `legit-finite-defect-mandate`, [legit-finite-defect-report](legit-finite-defect-report.md) (state, per-target sections, "Repair round 1"), [legit-finite-defect-ledger](legit-finite-defect-ledger.md), [legit-finite-defect-findings](legit-finite-defect-findings.md) (F1–F15), both round-1 audits (`legit-finite-defect-audit-r1-adversarial`, `legit-finite-defect-audit-r1-fidelity`) and the round-1 probes' declaration lists; **every Lean file** under `Cleanroom/Trust/LegitFiniteDefect/` in full (4,636 lines: all statements, docstrings and definitions; proof bodies of every P/C headline, every witness and every repair-round addition), and the root module; the dependency's `TotalTrust`, `HullAndModestlyInformed`, `Frame.cands`/`cell`/`selfMass`/`informed`, `E`, `mass`, `ind`, `MeasurableWrt`, `stratValue_twoOption` (statements read from `Cleanroom/Found/LitDdbFrames/`). Sources re-read for the repair-round rows: `legitimacy-corrigibility-model.md` §2.2–2.4; `legitimacy-corrigibility-redteam.md` (b) l. 49; `stop-gradient-steering.md` §B.4 (the grid, the closed-form parenthesis, the `e₂ = 1/8` sentence, the scoring-rule paragraph); `trace-nonrecoverability.md` §5 and §8; inventory items 2-043 and 2-047; `scout-acceleration.md` Q6. Round 1's audits were treated as claims and re-checked, not inherited. Contamination: none — nothing under `research/faf-lab/`, no transcript, no git history (no `git log`/`git show` run).

Probes: `packages/legit-finite-defect/audit-r2-probes/Vacuity.lean` — five probes (P1–P5), elaborated with `scripts/lean-check`, exit 0, no warnings, `#print axioms` on the three substantive ones: `propext`, `Classical.choice`, `Quot.sound` only. Not imported by the library. None is a counterexample to a package theorem; P2 recovers the mandate's refuted formula under an extra hypothesis, P3 and P5 show two hypotheses are load-bearing, P4 shows a positive headline is not automatic, P1 certifies the new theorem's terms are genuine distances.

Every witness number added in repair round 1 was re-derived by hand before its proof was read: `−13/20`, `+1/40`, `−27/40` (`WireheadModel`); `+1/8` at world `2` and `3/10` (`Coexist`); `11/16`, `5/16`, `−55/256`, `−9/128`, `73/256`, `18/73` (`e2_row`); the `σ = 7/20` steered means `67/80`, `41/80` and the sign of `67 ln(67/80) + 13 ln(13/80) + 41 ln(41/80) + 39 ln(39/80) ≈ −90.93` against `120 ln(3/4) + 40 ln(1/4) ≈ −89.97` (`base_log_flip_bracket`); the three constructions of `exists_defect_eq` (each realises `Y₃` on day 3 and has `|Y₃ − h₃| = δ`); the `jump` map's crossing `1/2`, one-sided values `1`, `0`, gap `1/8` at the crossing, GLB `1/8`; the affine flip's unique fixed point `1/2`. All agree.

## 1. Verdict

**pass.**

Gate: I ran `scripts/wp-audit Cleanroom.Trust.LegitFiniteDefect` on the tree as committed → `PASS` (952 declarations; axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`; no open list and none needed). Round 1's one blocking issue (`const_half_fixedPoint` graded N+) is fixed as the auditor asked: `affine_flip_fixedPoint` is a genuine N+ witness (non-constant, continuous, self-mapping, unique fixed point, and `affine_flip_exists_fixedPoint` runs the theorem on it), and the constant instance is regraded N− in docstring and ledger. Every round-1 non-blocking note I re-checked is either fixed as the repair notes say or honestly recorded as a note. The ledger has 89 rows (86 `proved`, 3 `refuted`, 0 open, 0 flagged — recounted by script), every one of its 158 backticked declaration names resolves in the Lean (checked by script), and every P/C/N+-kinded declaration in the Lean has a ledger row except one supporting N+ fact (non-blocking 1). No headline is a squeeze, vacuous, trivially true, or weaker than its name, docstring or ledger row; the only `(c)` is the disclosed `traderProfit` shadow; no junk value (division by zero, `sSup`/`sInf` of an empty set, `Classical.choice` default) reaches a headline; the package imports no FAF and says so; every core target is done, the stretch items are done or declared not attempted; every claim in the findings file that I checked against its source is true as stated (F13 and F15, the two new local-error findings, both verified against the model, the red team and the mandate/inventory).

## 2. Blocking issues

None.

## 3. Non-blocking issues

Numbered for a repair pass, if one is run; none changes a statement of record.

1. **`Wirehead.numb_not_overstating_on_support` (docstring Kind N+) has no ledger mention.** The grouped row for witness (a) names `numb_average_rises` / `numb_gate_eq_ind` / `numb_defect_pos`; this fourth fact (the iff's right-hand side fails on `S = {0}`) is what ties the witness to `defect_nonpos_on_iff` and should be named in the same row. Presentation. (Script check: it is the only P/C/N+-kinded declaration in the package absent from the ledger.)

2. **F15 is a missing-hypothesis error, and the package can say so in one line.** The mandate's two-term formula `min (s(c⁻) − c) (c − s(c⁺))` is false as stated (`jump_counterexample`, verified), but it is *recovered* under the extra hypothesis `s c = s(c⁻)` — probe P2 `two_term_of_left_value` proves `IsGLB (settleGap s '' Icc 0 1) (min (leftVal s − crossing s) (crossing s − rightVal s))` from the package's three-term theorem plus `s (crossing s) = leftVal s`, and `antiIndAt_left_value` shows the anti-indicator satisfies that hypothesis (which is why the omission went unnoticed, as F15 guesses). The symmetric right-continuous case is the same argument (not compiled). Fix: one sentence in F15 and in `isGLB_settleGap_crossing`'s docstring ("the two-term formula holds when `s c ∈ {s(c⁻), s(c⁺)}`"), and optionally ship P2 as a named corollary — it is the mandate's statement under the hypothesis its author presumably had in mind. Presentation/extension.

3. **The crossing theorem's one-sided terms are genuine distances; say so.** Probe P1 proves `crossing s ≤ leftVal s` and `rightVal s ≤ crossing s` under the theorem's hypotheses (antitone, self-mapping, fixed-point-free, `0 < c < 1`), so both one-sided terms are `≥ 0` and the three-way `min` cannot be won by a negative junk term. The docstring's "three distances from the diagonal" reading is correct; the nonnegativity is not stated anywhere. A two-line lemma in `Crossing` would close it. Presentation.

4. **`IdentifiedSet.exists_steered`'s interiority hypothesis is sharp, and the findings could record the converse.** Probe P3 `boundary_identifies`: a valid system with terminal opinion `Y₃ = 0` and positive terminal quote has `D = 0`, so *every* trace-consistent valid system has defect `0` — the trace identifies legitimacy. So "no valid trace with an interior terminal opinion identifies legitimacy" (F10, docstrings) is exactly right and the boundary is where identification returns (except at `a₃ = Y₃ ∈ {0, 1}`, where `D = 1`). Worth one sentence in F10 as the sharpness remark. Presentation.

5. **`Mechanism.totalTrust_clean`: the hull weights are load-bearing, not just the support.** Its docstring says "nothing subtler than the hull condition with explicit weights is at work", which is true; probe P4 makes the point sharper: the clean-supported distribution `πbad = (1/2, 0, 0, 1/2, 0, 0, 0, 0)` (all mass on `(lo, 0)` and `(hi, 1)`) is in the simplex, has `mech = 0` on its support, and *fails* Total Trust at `X = 𝟙{world 1}`, `s = 1/4` (product sum `−1/8`): the `lo` row says `θ = 1` with probability `1/4`, but under `πbad` a `lo` report means `θ = 0` surely. So the positive half is not "any clean prior is trusted"; it is "the prior that is the rows' mixture is trusted". One clause in the docstring. Presentation.

6. **`Residue.regime_iff`'s `0 < B` is load-bearing** (probe P5: at `A = B = 0` the biconditional is false). The docstring lists it under `Hyps: (a)`; fine. Recorded so the next reader does not try to drop it.

7. **Ledger cell wording for `Coexist.value_drop`.** The docstring's Fidelity is `variant: fine-vs-coarse garblings`; the grouped ledger row's Fidelity cell reads `exact (instance; value_drop is the fine-vs-coarse variant, …)`. Both disclose the same thing, but the cell leads with "exact" for a row whose named declaration is a variant. Lead with `variant` (or split the row). Presentation.

8. **Round-1 probe files now shadow library names.** `audit-r1-probes/Vacuity.lean` and `Fidelity.lean` define `manip_worlds_outside_rows`, `value_drop_other_thresholds`, `fine_worldGate_sees`, `ungarbled_value`, `settleGap_antiIndAt_attained` in their own namespaces; the repair moved same-named theorems into the library. Harmless (probes are not imported and were evidence for round 1), noted so nobody "deduplicates" the evidence.

Things I looked for and did not find: a `Nat` subtraction (none; `ℕ` is only day indices and exponents); an `sSup`/`sInf` whose emptiness could reach a headline (`Crossing.crossing` is over a set containing `0` under `hnf`; `leftVal`/`rightVal` are over nonempty images under `0 < c < 1`, which the theorem assumes and the docstrings say; the `c ∈ {0, 1}` boundary cases are excluded and correctly described as degenerate in the docstring — I checked that an antitone fixed-point-free self-map with crossing `0` is `0` on `(0, 1]`); `ℝ≥0`/`ENNReal` truncation (none); `decide`/`native_decide` in the library (none; the gate confirms); a `Classical.choose` whose default affects a statement (the one use, `DeterminedBy.exists_comp`, is inside a proof); a structure field smuggling a conclusion (`DerivedSign.Model` has positivity and the unused sum fields — which do exclude an empty signal type; `Sys`, `Params`, `Frame` carry no inequality about a headline); an `atTop`/`cofinite` filter (none); a look-alike FAF object (none; no FAF import); a hypothesis equivalent to a conclusion (none among P/C; the L rows are pointwise-sign ⇒ sum-sign and say so); a division whose zero case reaches a headline (`condMean`/`Jbrier` under `0 < Pmarg`, `Z ≠ 0`; `exists_defect_eq`'s `δ / (a₃ − Y₃ + δ)` under a positive denominator; `Calibrated` is product-form; `calibratedGarbling`'s null fibres are handled explicitly); a `sorry` in a helper (gate: none); a witness that fails its theorem's full hypothesis package (each N+ row's witness re-checked against the exact hypotheses of the theorem it guards — see §4).

## 4. What I checked and how, per headline

Format: declaration — what the Lean says after unfolding — what I did (degenerate models tried, witness graded). Ledger Kind/Fidelity/Hyps/Status compared with the docstring and the statement for every row.

### Defs (Target 1)

- `defect`, `defect_decomp`, `defect_swap`, `defect_ind_singleton` — `E π (θ·w) − E π (R·w)` over the dependency's `E` (read: `∑ w, ρ w * X w`); identities. L. ✓
- `Endorses`, `worldGates`, `DeterminedBy`, `ReportMeasurable`, `reportGates`, `questionGates`, `reportGates_eq_questionGates` (`rfl`), `determinedBy_iff_measurableWrt` (`Iff.rfl` against the dependency's `MeasurableWrt`, same formula, read) — as mandated. D/L. ✓
- `Calibrated` — product form on positive-mass values; no division. D. ✓ `Calibrated.ratio` L. ✓
- `frameReport`, `TotalTrust.report_ineq` — the latter is literally `h θ s` against the dependency's `TotalTrust` (`∀ X s, 0 ≤ ∑ w, π w * (X w − s) * 𝟙[s ≤ E (F.P w) X]`, read). L. ✓
- `thresholdValue`, `thresholdValue_frameReport` — the bridge is `stratValue_twoOption` (statement read: `stratValue π (F.twoOption X s) − s = ∑ w, π w * (X w − s) * 𝟙[s ≤ E (F.P w) X]` under `π ∈ stdSimplex`), then `rfl`. L. ✓
- `complyAdv`, `complyAdv_decomp`, `traderProfit`, `traderProfit_eq_defect` — identities; `(c)` disclosed three times. ✓

### Wirehead (Target 2, load-bearing 1)

- `defect_nonpos_on_iff (hπ) θ R S` — `(∀ w ≥ 0 supported in S, defect ≤ 0) ↔ ∀ x ∈ S, 0 < π x → θ x ≤ R x`. Read both directions (point masses; three-case sum). Degenerate corners: `S = ∅` (both sides true), `π ≡ 0` (both sides true), `R = θ` (both true) — consistent, not vacuous. P, exact. ✓
- `defect_nonpos_of_overstates`, `defect_neg_of_strict_overstate` — L instances at `S = univ`. Witness pointer now `WireheadModel.drugFix_*`, which inhabits the *global* hypothesis (repair r1 fixed the earlier mispointer). ✓
- `Wirehead.numb_*` — `3/40`, gate `= ind {0}` (function equality), `1/40`, RHS fails on `{0}`. Re-derived. N+; `refuted` status fair (ATTRIBUTION-UNVETTED reading of model §0/§2.2, the red team's own Finding 1). ✓ (Non-blocking 1 on the fourth fact's ledger mention.)
- `WireheadModel.drug_not_overstating` / `drug_defect_on_ones` / `drug_point_mass_pos` / `drug_not_nonpos_on_class` — read model §2.4 (`π = (1/4, 3/4)`, `θ = (1, 0)`, `E_drug = (9/10, 9/10)`, `−13/20`) and §2.2's hypothesis (`θ_x ≤ E_drug(θ)_x`): at `h`, `1 > 9/10`, so the example fails the theorem's hypothesis; `1/4·(1 − 9/10) + 3/4·(0 − 9/10) = −13/20` ✓; point mass `1/40` ✓; the class statement follows from the iff. Red team l. 49 "Non-vacuous (micro-example satisfies it)" is false as F13 says. N+, `refuted` fair. ✓
- `WireheadModel.drugFix_overstates` / `drugFix_defect_nonpos_on_class` / `drugFix_strict` — `RdrugFix = (1, 9/10)` overstates `θ = (1, 0)` pointwise (strict at world 1, `π·w = 3/4 > 0`); defect on `(1, 1)` is `1/4·0 + 3/4·(−9/10) = −27/40` ✓. Non-constant report, non-uniform prior. N+. ✓
- `WireheadLocal.flat_*` — `S = {1}` hypothesis holds, global fails at `0`, `defect (ind {1}) = −1/4` ✓. N+ (round 1's note 7 accepted: the iff's mechanism is exercised regardless of the report's constancy). ✓

### Corrigibility (Target 3)

- `complyAdv_nonneg_of_endorsed`, `_nonpos_of_adversarial`, `complyAdv_pos_of_endorsed` — pointwise sign ⇒ sum sign; `0 ≤ s` dropped as unused, Fidelity `stronger` in docstring and ledger, the negative-weight reading (`s = (−1, 0, 0, 0)`) recorded. L. ✓
- `Corrigibility.three_signals`, `hypotheses_discriminate`, `legit_strict` — `+1/2, 0, −1/2` re-derived; blank fails both encodings at worlds `1` and `3`; all three signals nonnegative (so the model's `ℝ₊` is honoured by the witness). N+. ✓

### Detection and Target 12 (load-bearing 2)

- `defect_comp_eq_sum_fibres` — read the proof: `Finset.sum_fiberwise_of_maps_to`, then constancy on fibres. Not a relabelling. P. ✓ `defect_comp_report` — the `Q = R` case via `sum_fibre_mul_report`. P. ✓
- `endorses_questionGates_iff (hπ)` — `⟹` by cell indicators, `⟸` by `exists_comp` + regrouping + null cells (`hπ` used only there, and needed). Degenerate `Q` constant: both sides reduce to "if `π(univ) > 0` then `E π θ = E π R`" — consistent. P. ✓
- `endorses_reportGates_iff_calibrated` — unfolds to `Calibrated` exactly. P. ✓ `endorses_worldGates_iff` — the iff twice via `defect_swap`. P. ✓
- `calibrated_calibratedGarbling (hπ)` — read the dependency's `calibratedGarbling` (ratio, junk `0` on a null fibre) and the proof's null-fibre branch (every `π x = 0`, both sides `0`). Junk never enters. P. ✓ `calibratedGarbling_endorsed_on_reportGates` C. ✓ `Endorses.of_refines` — `Refines Q' Q := ∃ h, Q = h ∘ Q'`; finer gates ⊇ coarser. L. ✓
- `Coexist.*` — `Rfine = (1, 0, 1/2, 1/2)`, `Rcoarse ≡ 1/2` from the dependency's ratio; `worldGate_sees = −1/8`; `fine_worldGate_sees = 1/4·(1 − 1/2) = +1/8` ✓; `ungarbled_value`: fires at worlds `0, 2`: `1/4·(3/5 + 3/5) = 3/10` ✓; `value_drop`: `1/5` vs `1/10`, threshold separates (`Rfine 1 = 0 < 2/5 ≤ 1/2 = Rcoarse 1`) ✓; `value_drop_other_thresholds` `1/8`/`0`, `1/16`/`0` ✓; `Rfine_ne_θ` at world `2` ✓. The coarse half of (a) is degenerate (constant report) and the fine half is not — disclosed in `fine_worldGate_sees`'s docstring. N+. ✓ (Non-blocking 7 on the ledger cell's lead word.)

### DerivedSign (Target 5, load-bearing 3)

- `Model`, `target`, `m`, `p`, `k`, `odds`, `q`, `prior`, `pos`, `prior_nonneg` — `q l s = k (a/b)^l / (1 + k (a/b)^l)` with `Real.rpow`; the sum fields are declared unused (and do exclude an empty signal type). D/L. ✓
- `p_lt_q_iff (1 < λ)`, `p₀_lt_q_iff (0 < λ)` — trichotomy on the ratio with the named `rpow` lemmas. P. ✓ `defect_fibre`, `defect_threshold_gate` L. ✓
- `defect_neg_of_exaggeration (1 < λ) (p₀ ≤ t) (0 < fired mass)` — no `θ ≤ R`/`p ≤ q` hypothesis (grep-checked); overshoot derived. Degenerate `S` singleton: `a = b = 1`, `q = p = p₀`, the gate never fires at `t ≥ p₀`, so the mass hypothesis fails — the theorem is not vacuous there, the model simply cannot inhabit it. P, exact. ✓
- `bayes_calibrated` — `q 1 = p`; report gates of `p ∘ snd` are `snd`-determined (direction checked). C. ✓ `defect_pos_of_numbing` P. ✓
- `Witness.*` — `m ≡ 1/2`, `p = (3/4, 1/4)`, `q₂ = (9/10, 1/10)`, fired mass `1/2`, defect `−3/40`; `λ = 1/2` sign only. N+. ✓

### Mechanism (Target 6, load-bearing 4)

- `mech`, `rep`, `θ8`, `ρhi`, `ρlo`, `F`, `F_P`, `E_rows`, `πclean`, `πmanip`, `πmix`, `priors_mem`, `reportMarginal` — decoded `w = 4·mech + 2·rep + θ` against the mandate's table; rows and priors as specified. D/L. ✓
- `reportMarginal_eq`, `observable_blind` — `(1/2, 1/2)` computed under every `λ` (also non-priors, harmless). N+/L. ✓
- `hull_clean`, `totalTrust_clean` — `cands πclean = {ρlo, ρhi}`, `πclean = ½ρlo + ½ρhi` (coordinatewise), self-mass `1`, informed self = itself; then the cycle under `πclean ∈ stdSimplex`. Probe P4: the weights are load-bearing (a clean-supported non-mixture prior fails). C, exact quantifier. ✓
- `mix_product_sum`, `not_totalTrust_mix (0 < λ)` — `−λ/4` re-derived over worlds `2, 3, 6, 7`. Docstring now says the failure is at the hull condition (`manip_worlds_outside_rows`). P. ✓ `mechanism_nonidentifiable` C, `not_totalTrust_manip` N+. ✓

### Trace (Target 7)

- `Sys`, `run`, `trace`, `Afree`, `d`, `Valid`, `S1`, `S2`, `valid_and_differ`, `trace_eq`, `d_pair`, `gate_blind`, `no_recovery`, `transparency_gate_exists`, `influence_deletion_breaks_trace`, `hidden_defect_needs_full_influence` (now L), `S2_tracking` — as in round 1; re-read, numbers agree. ✓
- `IdentifiedSet.modify3`, `run_modify3`, `terminal_of_trace_eq`, `trace_modify3_iff`, `d_modify3`, `valid_modify3`, `D` — `D` by the sign of `a₃ − Y₃`, no division. D/L. ✓
- `d_le_D` — three cases read: `a₃ = Y₃` (`|Y − h'| ≤ max Y (1 − Y)` for `h' ∈ [0, 1]`); `a₃ > Y₃` (`(1 − β')(h' − Y) = β'(Y − a) ≤ 0`, `β' = 1` contradicts `a ≠ Y`, so `h' ≤ Y`); dual. P. ✓
- `exists_faithful` (`modify3 S Y₃ 0`) P. ✓ `exists_steered` — four constructions; each `run 3 = Y₃`, `d = D`, `D > 0` under interiority. P. ✓ Probe P3: interiority is sharp (non-blocking 4).
- `exists_defect_eq` — the three constructions re-derived: `a₃ = Y₃`: `h₃ = Y ∓ δ`, `β = 1`, `d = δ`; `a₃ > Y₃`: `h₃ = Y − δ`, `β = δ/(a − Y + δ)`, `run = Y(a − Y + δ)/(a − Y + δ) = Y`, `d = δ`; `a₃ < Y₃`: dual. Denominators positive. P. ✓ `defect_consistent_iff` — `⟹` by `d_le_D` + `|·| ≥ 0`, `⟸` by `exists_defect_eq`. C, exact. ✓

### StopGradient (Target 8)

- `verdict`, `pay`, constants, `Yraw`, `weights_prob`, `raw_rewards_manipulation` (`9/256`, `7/16`, `3/4`, global optimum), `filt`, `Yfilt`, `stop_gradient_identity` (L), `filtered_channel_independent` (L, with the raw-side contrast `0 ≠ −9/16`), `filtered_optimum_unique` (P, small), `Ymis`, `aMis`, `misspecified_filter` (`2/5`, `9/1024`, `3/20`), `Ydel`, `deletion_test` (`−9/16`) — re-read; kinds honest; "quote gap" wording in the ledger. ✓

### Residue (Target 9, load-bearing 5)

- `Params`, `bit`, `Pθ`, `Py₁`, `Pg`, `Law`, `honest`, `steer`, `wirehead`, `wireheadClean` — laws matched clause by clause to §B.1 (`steer`: `G` anchored to `1` w.p. `σ`, all legitimate; `wirehead`: `Y₁ ≡ 1`, corrupt branch w.p. `s` with `Y₂ = 1`). D. ✓
- `restrict`, `Pmarg`, `Njoint`, `Z`, `condMean`, `groupScore`, `Jbrier`, `groupScore_condMean`, `propriety` — plug-in score with propriety proved (gap `(Pq − N)²/P`), so not defined as the optimum. Junk `condMean = 0` on a null group gives `groupScore = 0`; every headline carries positivity. ✓
- `residue_closed_form (0 < Py true) (0 < Py false)` — per-group identity `group_residue` re-derived (`−P[q'(1−q') − q(1−q)]` with `q' = σ + (1 − σ)q`). P, exact, general parameters. ✓
- `regime_iff (0 < B)` — both directions read; probe P5: `0 < B` load-bearing. P (small). ✓ `regime_instances` (`A lean34 = 1/20`, baseline fails at `1/5`) N+. ✓
- `base_values`, `base_closed_form`, `base_flip` — `−(1 − σ)(3 + 5σ)/16` derived; zeros exactly `{0, 2/5}`. N+/P. ✓
- `baseE2`, `e2_row` — re-derived by hand: `P(Y₁ = 1) = 1/2`; `P(G = 1 | Y₁ = 1) = 2·(21/64 + 1/64) = 11/16`; `P(G = 1 | Y₁ = 0) = 2·(7/64 + 3/64) = 5/16`; `A = (30 − 66)/512 = −9/128`; `B = 146/512 = 73/256`; `J_L(honest) = −55/256`; zero at `−A/B = 18/73 ≈ 0.2466 ∈ (1/5, 1/4)`, the source's bracket (§B.4 read). Fidelity `stronger` fair. N+. ✓
- `wirehead_values`, `wirehead_JL (s < 1)`, `tv_identity`, `honest_sub_wirehead`, `gap_formula`, `wirehead_gap_zero_iff`, `wireheadClean_restrict`, `wireheadClean_JL` (L, by construction), `base_wirehead` (`−7/64`, `−1/4`), `steer_noop` (T) — as in round 1; re-read. ✓

### LogCompare (Target 10)

- `log_prod_pow`, `prod_pow_pos`, `sum_log_le_iff`, `sum_log_lt_iff` — the device over two index sets. P (small, as the report says). ✓
- `negEnt`, `gibbs`, `Jlog`, `log_propriety`, `steer_condMean`, `Jlog_eval`, `base_log_values` — plug-in log score with Gibbs propriety on interior groups. ✓
- `base_log_residue` — the weight vectors are correct clearings (`20·J_L(honest) = 15 log 3/4 + 5 log 1/4`, etc.); signs `−, +, +` at `1/5, 2/5, 3/5`. N+. ✓
- `base_log_value_720`, `base_log_flip_bracket` — steered means `7/20 + 13/20·3/4 = 67/80`, `7/20 + 13/20·1/4 = 41/80` ✓; `160·J` clearings correct; the decisive inequality `(67/80)^67 (13/80)^13 (41/80)^41 (39/80)^39 < (3/4)^120 (1/4)^40` checked numerically (logs `−90.93 < −89.97`), so the log residue is negative at `7/20` and the bracket `(7/20, 2/5)` matches inventory 2-047 (a) and §B.4 (both read). N+. ✓
- `base_log_wirehead` — `(1/2)^4 < (3/4)^3 (1/4)`. N+. ✓

### Settlement (Target 11)

- `settleGap`, `settleGap_eq_zero_iff`, `exists_fixedPoint` (IVT on `s a − a`; P), `not_continuousOn_of_no_fixedPoint` (L), `antiIndAt`, `antiIndAt_mapsTo`, `settleGap_antiIndAt_ge` (unused hypothesis dropped), `isGLB_settleGap_antiIndAt (c ∈ [0, 1])` (P; boundary cases `c = 0, 1` re-checked: GLB `0` both), `settleGap_antiIndAt_attained` (L; `1 − c` at `a = c`), `antiInd_half_gap`, `antiInd_half_attained` (N+). ✓
- `affine_flip_fixedPoint`, `affine_flip_exists_fixedPoint` — `s a = 1 − a`: continuous, self-mapping, `s 0 ≠ s 1`, gap `0` at `1/2`, unique (`1 − a = a ⟹ a = 1/2`); the theorem run on it returns `1/2`. Inhabits `exists_fixedPoint`'s full package and exercises the IVT (`s a − a = 1 − 2a` changes sign). **N+ on my grading.** ✓ `const_half_fixedPoint` N− with `constant_fixedPoint` as the reason — correct regrade. ✓
- `Crossing.below`, `crossing`, `leftVal`, `rightVal`, `zero_mem_below`, `below_bddAbove`, `crossing_mem`, `lt_of_lt_crossing`, `lt_of_crossing_lt` — read; `crossing = sSup below` is over a set containing `0` under `hnf`; the one-sided values are over nonempty images under `0 < c < 1`. D/L. ✓
- `Crossing.isGLB_settleGap_crossing (antitone) (mapsTo) (no fixed point) (0 < c) (c < 1)` — plain words: the GLB of `|s a − a|` over `[0, 1]` is the least of the gap at the crossing, `s(c⁻) − c`, and `c − s(c⁺)`. Read the whole proof: lower bound by trichotomy on `a` vs `c` (left: `s a − a ≥ leftVal − c`; right: `a − s a ≥ c − rightVal`; at `c`: the first term); greatest by two `by_contra` constructions of quotes near `c` (a quote `≥ a₀` and close enough to `c` from below makes the gap `< b`; dual on the right — each inequality chain re-derived by hand). I also checked the mathematics independently: for antitone `s`, `s a ≥ s(c⁻) ≥ c` left of `c` and `s a ≤ s(c⁺) ≤ c` right of it (probe P1 compiles the two bounds), the one-sided terms are approached in the limit, and `s c ∈ [s(c⁺), s(c⁻)]` is free, so a third term is necessary. P; Fidelity `variant` (three terms; open interval) honest. ✓
- `Crossing.below_antiIndAt`, `crossing_antiIndAt`, `image_Ico_antiIndAt`, `image_Ioc_antiIndAt`, `antiIndAt_antitoneOn_noFixed`, `antiIndAt_via_crossing (0 < c < 1)` — crossing `c`, one-sided values `1`, `0`, gap at `c` is `1 − c`, `min (1 − c) (min (1 − c) c) = min c (1 − c)`: consistent with `isGLB_settleGap_antiIndAt`. N+. ✓
- `Crossing.jump`, `jump_counterexample` — `jump = 1` on `[0, 1/2)`, `5/8` at `1/2`, `0` on `(1/2, 1]`: antitone ✓, self-mapping ✓, fixed-point-free (`1 ≠ a < 1/2`; `0 ≠ a > 1/2`; `5/8 ≠ 1/2`) ✓, `below = [0, 1/2]` ✓ (`1/2 < 5/8`), crossing `1/2` ✓, one-sided values `1`, `0` ✓, gap at `1/2` is `1/8` ✓, GLB `1/8` (gaps are `> 1/2` off the crossing) ✓, two-term value `1/2 > 1/8` ✓. N+; `refuted` status refers to the mandate's stretch formula, and F15 correctly attributes it to the mandate-writer (inventory 2-043 and scout Q6 (ii), both read, contain no crossing formula). ✓ (Non-blocking 2.)

### Ledger, report, findings

- Ledger: 89 rows (86 proved, 3 refuted; kinds 24 P + 3 small/mixed P, 5 C, 14 L + 6 mixed, 11 D, 23 N+, 1 N−, 1 T — recounted by script, matches the totals line); every name resolves; every Kind/Fidelity/Hyps/Status compared with the docstring and the statement — no mismatch beyond non-blocking 1 and 7. The only `(c)` is `traderProfit`. Round 1's blocking grade is fixed.
- Report: gate claim reproduced (952); "Repair round 1" section accurately describes each fix (I checked every item against the Lean); Target 10 and 11 sections updated for the new declarations; "not attempted" items honestly listed (other log-grid rows; settlement crossings `c ∈ {0, 1}`).
- Findings: F13 verified against model §2.2/§2.4 and red team l. 49 (true, fairly described, severity right — the §2.2 theorem is untouched); F14 numbers re-derived (true); F15 verified (the two-term formula is false as stated; provenance correct; severity "local error in the mandate" fair — non-blocking 2 adds the hypothesis under which it holds); F8 and F10 updates consistent with the Lean; F5's retitle fair to the source (the §B.4 parenthesis quoted in full). F1–F4, F6, F7, F9, F11, F12 as verified in round 1; spot-checked F7 (scout Q6 (ii) is the definition of an infimum) and F12 (`MeasurableWrt` needs `[Fintype C]`, read).
