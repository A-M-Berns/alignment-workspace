# dp-calib-limits — findings about the sources

Findings per [STANDARDS](../../STANDARDS.md) §5: errors, ill-posed claims and gaps in the sources, each with a severity (**blocking** the note's conclusion / **local error** / **imprecision** / **presentation**) and a pointer. Written by the formalizer (Fable 5.1, [scrubbed], 2026-09-30) from what the Lean established; "proved" means a kernel-checked declaration in `Cleanroom/Decision/DpCalibLimits/`. Attribution claims are marked ATTRIBUTION-UNVETTED where the reading is mine.

## F1 — The count of Popper axioms that fail without the convention is axiom-set-relative; no source sentence asserts "four axioms" (imprecision, survey-level)

**Pointer:** `run/survey/dp-sl-inventory.md` item 029 (headline "without that convention four Popper axioms fail"; its claim body "checked exhaustively on one tree: 4 violations without the convention"); P07 I2′ ("without which the axioms fail on any tree with an unreachable act (e.g. Told-You-So's `m=10 ∧ n=5`)").
**What the Lean says:** with `dp-calibration`'s junk `0` on tremble-unreachable conditions, `limitCond C B` satisfies on *every* tree the bounds (P0) (`limitCond_bounds`), unconditional additivity (`limitCond_add`, hence (P2) on normal conditions), the multiplication axiom (P3) (`limitCond_mul`: at an unreachable `C'` every factor is `0`, at a reachable `C'` with unreachable `B' ∩ C'` both sides are `0`) and non-triviality (P4) (`limitCond_nontrivial`). Under `IsPopper` as typed it fails exactly (P1), `limitCond O O = 1`, at unreachable `O` (`limitCond_self_iff`; witness `tys_limitCond_unreachable_ne_one` on Told-You-So at `n = 5 ∧ m = 10`). But the count is not invariant under the presentation of the same axiom system: under Hájek 2003 p. 316's clause (ii), "if `B` is normal then `p(· | B)` is a probability measure" **[reconstructed: Hájek 2003 is not in the repo; only the multiplication axiom was confirmed from it by the SL run, mandate §5 item 6 — so this chunking is (b), as the axiom set `IsPopper` is; the mathematics below does not depend on the wording]**, normalization `p(⊤ | B) = 1` sits inside (P2); an unreachable `O` is *normal* for `IsPopper`'s `Abnormal` (`limitCond ∅ O = 0 ≠ 1`) and `limitCond ⊤ O = 0` (`div_zero`), so Hájek's (ii) fails at `O` as well as (P1) — two axioms (`limitCond_unreachable_normal_univ_eq_zero`, `tys_limitCond_univ_unreachable`). The systems agree (`p(⊤|B) = 1` is derivable from (P1)+(P3) in the typed set); the count of failing axioms does not.
**Reading (repair round 1, fidelity B1 / adversarial N3):** P07 I2′'s sentence is **confirmed** (the axioms do fail on any tree with an unreachable act). The sentence "four Popper axioms fail" is the survey headline's compression of the inventory's "4 violations", which reads at least as naturally as four violating *instances* on one tree; P07 itself gives no count. So there is no source sentence to refute, and the package's "exactly one" is a fact about `IsPopper` as typed, not a correction of the research. Sharper (repair round 2, adversarial N4): P07-2′(a) (`P07.md` line 34) lists Popper's axioms as "normalization, first-argument additivity, multiplication" — three — and reports "on the cut tree 0 violations with the convention, 4 without it (A§B)"; so the inventory's "4" is a count of violating *instances* on one tree, and the survey headline's "four Popper axioms fail" cannot be a count against P07's own list, which has three. The mandate's request to "prove (P3) fails at a named triple" cannot be met: (P3) holds (F18). ATTRIBUTION-UNVETTED as to which axiom set, if any, the inventory counted.

## F2 — `TS ⊆ MSR` is asserted and false; SE-18′(b)'s Open is settled affirmatively (blocking for the chain as stated)

**Pointer:** `sl-defensible-claims.md` S10 and `C2.md` C2-9′/20′ ("`FF ⊆ TS ⊆ MSR = DE ⊆ MSR¹⁷` [derived]"); `seeds.md` SE-18′(b) ("approved at the Definition-10 (ray) state under the added hypothesis that `ν_{C₀}(a ∧ O_d) > 0` … whether a fixed-point family realizes the reversal is Open"); P04 Open 11.
**What the Lean says:** `ts_not_msr` (`TsMsr.lean`): on a five-point tree (`tsTree`) the procedure `C₀ = tsProc 0` is test-sequence tremble-EDT-consistent (`tsC0_ts`, along `ε_n = 1/(n+2)`, `C_n = tsProc ε_n` with the D2 condition verified at every point for every `n`, `tsProc_d2At`) and not mixed-strategy ratifiable at the queried point `d` (`tsC0_not_msrAt`: uniform-ray values `(5, 15)`, `supp C₀(d) = {a}`). The mechanism is SE-18′(b)'s: the moving coordinate `C_n(e)(u) = 2ε_n` is approved because `e`'s two acts tie exactly for every `ε` (the alternative branch carries a copy of the `d`-payoffs at a different point `g`), while the right entry `C_n(f)(w) = 0` stays at the tremble floor `ε/2`; so `s ≫ t` along the sequence but `s = t` on the uniform ray. The guarded inclusion holds (`msrAt_of_ts_of_realized`: TS at a point where every act event is `C`-realized gives MSR there).
**Consequence:** the sources' chain must read `FF ⊆ TS`, `TS ∩ {realized acts} ⊆ MSR`, `MSR ⊆ MSR¹⁷` (under recording, at strict states); the unguarded second link is refuted, and the Open of SE-18′(b) is closed in the form it asks: the family `tremble (tsProc ε) ε` is an ε-floored fixed-point family (`tsTr_epsFP`: `EpsFP … ε` for `ε ∈ (0, ½]`) converging to `C₀` (`tsTr_tendsTo`), so a fixed-point family does realize the reversal (repair round 1, adversarial N1). S10's "[derived]" for the second inclusion should be withdrawn. The guarded inclusion is inhabited non-degenerately on the miniature (`miniature_msr_realized_instance`: the non-constant test sequence of `procQ ⅔`, both act events realized).

## F3 — P07-1′ refinement (ii)'s "ray-dependence … needs two points" is false beyond two actions (local error, ATTRIBUTION-UNVETTED); P07 I2′'s single-point sentence is confirmed

**Pointer:** `P07.md` line 32, P07-1′ refinement (ii): "the ray-dependence of SE-18′(b) … needs two *points* trembling at different rates and an observation the untrembled procedure never realizes; Definition 10 trembles a procedure with one `ε` and the post's nets have one decision node, so within the post's class there is no ray to choose [derived]". **Two readings** (repair round 2, fidelity N4): on the *necessity* reading, "needs two points" is a necessary condition for ray dependence in general, and `threeAct_ray_dependent` refutes it — the severity `local error` holds under this reading; on the *descriptive* reading, line 32 describes the mechanism of SE-18′(b)'s own instance (which is produced by two points at different rates), nothing is refuted, and only the inference drawn from it ("the post's nets have one decision node, so … no ray to choose") is challenged — and that inference survives within the #4 class (below). The ATTRIBUTION-UNVETTED flag is the choice between the readings. (The survey headline dp-sl-029, "ray-dependence needs two points and a `C`-unrealized observation (absent from single-point classes)", is this run's own compression, not a source sentence; P07 I2′, line 92, says the opposite of the compression — "at a single point with realized `O_d` there is nothing to choose" — and is confirmed by `limitCondRay_eq_of_pos`. Retargeted in repair round 1, fidelity N1 / adversarial B2.)
**What the Lean says:** `threeAct_ray_dependent`: on the one-node tree with acts `a, b, c`, `C = δ_a` and the `C`-null observation `{b, c}`, the limiting conditional of `{b}` given `{b, c}` is `1` along the ray `(w_b, w_c) = (ε, ε²)` and `0` along `(ε², ε)`, both rays starting at `δ_a`. So "needs two points" is false: per-act rates at one point suffice, and no nesting is needed (the mandate's two-nested-node construction is not needed either). **What survives of line 32:** its class-relative half. P07's "#4 class" (P07-4′; S21: every act tremble-reachable, the observation a parent of the act) forbids act-decided observations, and `{b, c}` is decided by the act, so within the post's class there is still no ray to choose — the Lean does not touch that reading. The two-action case (the off-support act's order is the only free choice and cancels) is the other surviving neighbour, now **proved** (`twoAct_single_point_ray_independent`, via `limitCondRay_eq_levelMass`: along any full-support ray of a pure label the limit is the ray-free level-mass ratio; stated OPEN in the first round, proved in repair round 1). So the exact boundary is `|A_d| = 2` versus `|A_d| ≥ 3` at a single point: at two actions no ray choice exists; at three, per-act rates decide the argmax.

## F4 — The SL grid's masked column is a `(c)` substitution strictly stronger than Definition 9 (imprecision, inherited)

**Pointer:** C1 Open 8 (dp-sl-2-062).
**What the Lean says:** `maskedUniformAt_imp_maskedOCAt` (the uniform-column verdict implies Definition 9's existential) and `zo1_not_maskedUniform` (ZO-1's state is masked-calibrated, even under the letter, with unique self-model `¼`, hence not uniform-column calibrated). Every masked-grade verdict inherited from the grid therefore carries the flag "computed at `C[d ↦ ½]`, not at Definition 9's existential".

## F5 — The Popper axiom form is (b), reconstructed (presentation / provenance)

**Pointer:** P07 reading ledger (Popper 1959 / van Fraassen 1976 unread; multiplication axiom confirmed from Hájek 2003 p. 316).
**Disposition:** `IsPopper` is typed as the reconstruction and every row that uses it is graded (b) for the axiom set; `popperLimit_isPopper` proves all five axioms as typed. Converting the definition to (a) needs the primary texts.

## F6 — The Strong Thesis is a type fact, not a theorem (presentation)

**Pointer:** L3-2′; S15.
**Disposition:** `State` has a total `P : FinDistr K Ω`, so every act event gets a number; "the agent has no credence in its own acts" has no slot. `WeakThesisAt` is the nearest expressible relative and is typed; the Strong Thesis is recorded here and in `WeakThesisAt`'s docstring, with no theorem (a theorem "every state assigns some number to every act event" would be a `T` row).

## F7 — Plan mislabel: dp-sl-2-062 is the grid substitution, not "Appendix B's small claims" (presentation)

**Pointer:** `run/plan/plan.md` line 476's WP entry.
**Disposition:** treated as the mandate directs (T6(c)); Appendix B's small claims proper (dp-core-2-061) were not picked up.

## F8 — dp-sl-2-019 (curve selection) is out of reach (gap, recorded)

**Pointer:** P07 I1′ cost clause ("the converse of (ii) … [derived] only via the semialgebraic curve-selection lemma [reconstructed], unchecked (Open 1)").
**Disposition:** Mathlib has no semialgebraic curve-selection lemma; not attempted. The forward directions are proved: every εFP limit is a test-sequence limit (`ts_of_epsFP_limit`), and on the miniature the nonstandard label's sequence is a test sequence (`miniature_testSeq`).

## F9 — The mandate's hypothesis for (P4) is derivable (presentation)

**Pointer:** mandate T1(a) ("carry `∃ ℓ, Positive B ℓ` as hypothesis (a)").
**Disposition:** every tree has a chance-positive leaf (`exists_chanceWeight_pos`); `popperLimit_isPopper` has no hypothesis.

## F10 — The bridge lemma needs no Archimedean hypothesis (presentation)

**Pointer:** mandate §3.4 ("over `LinearOrderedField K` with `[Archimedean K]`").
**Disposition:** `nonnegNear0_iff_eventually` is proved over any linearly ordered field: `ε₀ = min 1 (c/(M+1))` with `M` the sum of the absolute coefficients of the cofactor. (Archimedean-ness is needed only for `ε_n = 1/(n+2) → 0`, i.e. for the test-sequence statements over `ℚ`.)

## F11 — The routing root does not separate MSR from `T_EDT` (recorded per mandate T4(d))

**Pointer:** mandate T4(d) ("find whether `MSRAt` holds while `TEdtAt` fails, and record").
**Disposition:** `routingRoot_msrAt_iff`: MSR at the routing root holds iff `C(d) = δ_a` (a supported `b` violates Definition 18′'s unconditional realizability clause since `b ∧ O = ∅`), which is also `T_EDT`'s verdict at the strict state (`A_d^+ = {a}`). A separation would need a supported act with `ν_C(a ∧ O_d) = 0` but `nuPoly (a ∧ O_d) ≠ 0` at a point with `ν_C(O_d) > 0` — an unrecorded configuration not in the catalogue; not pursued.

## F12 — `TB(θ)`'s forced branch is rendered with a dummy point (presentation / fidelity)

**Pointer:** P11 line 57 (`TB(θ, 0, ·)`); mandate T12(b) ("the forced branch carries no `d`-node").
**Disposition:** `dp-core-tree`'s trees need a uniform shape under a chance node for the leaf-sum lemmas, so the forced branch is a decision node at a *different* point `forced` both of whose edges lead to the forced leaf. It carries no `d`-node, so every statement about `occ(d)`, coverage and recording at `d` is as P11 states; the extra queried point is never read by the T12 statements (all are "at `d`"). Disclosed as `Fidelity: variant`.

## F13 — The chicken witness is Told-You-So at `d₁₀`, not `coinQuery`/`tieTree` (presentation)

**Pointer:** mandate T9 ("`coinQuery` or `tieTree` with payoffs perturbed to a strict maximum").
**Disposition:** (c)'s hypotheses (`T_EDT` approval + self-transparency) force `C(d) = δ_{a*}` and `A^+ = {a*}`, so the argmax singleton is automatic at any recorded deterministic point; no perturbation is needed. Told-You-So at `d₁₀` under `(ten, ten)` has every hypothesis already proved in `dp-calibration` (`tys_recordsFor_ten`, `tys_take10_strictOC`) and a strict maximum `10 > 5` besides; `coinQuery` (all payoffs `0`) would witness (b) but not a strict maximum.

## F14 — Definition-15 inconsistency needs a mixed label (imprecision)

**Pointer:** dp-sl-030 / S11 ("stipulated accuracies are inconsistent").
**What the Lean says:** `sigmaPi_not_consistent` needs `q ∈ (0,1)`: at a pure label one of `ν(one)`, `ν(two)` is `0`, the corresponding stipulation is `0 = π·0`, and the other conditional alone does not force `π = ½`. The source's "at every mixed label" is the right scope; a pure-label version would need a different argument (and is false for suitable `p`: at `q = 1`, `P(fill | one) = p`, so `π = p` is consistent). The encoding is not an artifact: `Σ_{½}` *is* strictly consistent (`sigmaPi_half_consistent`: fill coin `p = ½`, every label `q`; the strict state of `procQ q` on `opaqueNewcomb ½` meets both stipulations), so the impossibility lives exactly at `π > ½` (repair round 1, fidelity N2).

## F15 — The Popper class question stays a question; the affirmative sentence is dead (recorded)

**Pointer:** P07 Open 3; `sl-synthesis.md` Dead list ("every Popper function is a limit along some ray"); mandate T15/T16.
**What the Lean says:** `chanceTwin_refutes` — the Popper function `condOfMeasure twinMeasure` (value ⅓ at `{(H,a)} | {(H,a),(T,a)}`) is no ray limit *on the chance-twin tree* (the claim is tree-relative, as P07 Open 3 is: on the tree "chance `(⅓, ⅔)` then the two `a`-leaves" over the same worlds the same function is `popperLimit C` for every `C`, unreachable worlds being abnormal under the convention — repair round 1, adversarial N2); `popperLimit_twin_leaves` — every ray limit satisfies chance-conditional invariance (leaves with the same draws are conditioned by their chance weights), inhabited on `chanceTwin`'s two `a`-leaves (`chanceTwin_twin_leaves_instance`, returning the `½`). Sufficiency (which Popper functions *are* ray limits) was not attempted and no open declaration is stated, because the "level structure by number of off-support draws" hypothesis could not be made precise enough to be confident of a true statement; recorded as a question, not a claim.

## F16 — Fairness vocabulary not typed (recorded)

**Pointer:** mandate T14; `sl-synthesis.md` line 23, §5.3 seam 1; dp-sl-007.
**Disposition:** not attempted. The definitions the mandate asks for: `DDOperational` (ID-26: no two distinct points `d ≠ d'` with `obs d = obs d'`, `acts d ≃ acts d'`, `s d ≠ s d'` separated in `ν` by some procedure) and `DDPayoff` (C1's grid: the payoff is a function of the act coordinate and a designated lesion coordinate only), with a compulsion tree separating them; and exploration-blindness as ray-independence of every off-fiber leaf law. `IsCalibrated κ` already serves as "honest at grade κ".

## F17 — The mandate's "for every ray … = ½" on `chanceTwin` needs `w_a ≠ 0` (imprecision, mandate-level)

**Pointer:** mandate T15 ("for every ray `R` (of any procedure), `limitCondRay R B {(H,a)} {(H,a),(T,a)} = ½`").
**What the Lean says:** on a trap ray with `w_a = 0` both event polynomials vanish and `limitCondRay` is the junk `0` (the Popper reading is the convention's `1`). `chanceTwin_popperLimitRay` states the correct dichotomy `½ ∨ 1`; the refutation (`chanceTwin_refutes`) is unaffected since neither value is ⅓.

## F18 — The mandate's "(P3) fails at a named triple" cannot be met: the multiplication axiom holds for the junk-`0` function (mandate-level imprecision)

**Pointer:** mandate T1(b) ("prove (P3) fails at a named triple"); P07 I2′.
**What the Lean says:** `limitCond_mul`: for every tree and procedure, `limitCond (A ∩ B') C' = limitCond A (B' ∩ C') · limitCond B' C'` — at an unreachable `C'` every factor is the junk `0`; at a reachable `C'` with unreachable `B' ∩ C'`, `A ∩ B' ∩ C' ⊆ B' ∩ C'` makes the left side `0` and the middle factor `0`; with both reachable the orders `k ≤ k'` split into `k < k'` (both sides `0`, `coeff_eq_zero_of_lt_natTrailingDegree`) and `k = k'` (the middle coefficient cancels). So no triple fails (P3). The mandate's expectation was wrong in the same way the "four axioms" count was (F1): normalization, not multiplication, is what the junk `0` breaks. Promoted from the report to a finding in repair round 1 (fidelity N7).

## F19 — T7(e)'s witness pairing: the product state with marginals (½, ⅓) is off the manifold *and off its convex hull*, so it cannot witness "credal candidate ⊋ manifold" (mandate-level imprecision; CA-10′ confirmed)

**Pointer:** `dp-calib-limits-mandate` T7(e) ("the product state with marginals `(1/2, 1/3)` is on no point of it (N+: \"Q2's credal candidate = convex hull strictly exceeds the manifold\")"); CA-10′ (`calibration.md` line 68: "`M_d = {(c², c(1−c), c(1−c), (1−c)²)}` … live and sample independent with *equal* marginals … the product state with marginals (½, ⅓) is off the curve"); Q2 (`decision-problems-v2` line 297: "The credal candidate of Appendix B is its convex hull; masked calibration is membership; strict calibration is its ratifiable point").
**What the Lean says** (`Curve.lean`, repair round 2): on the miniature the run law of every procedure is the product of the label with itself, `ν_C(X) = ∑_{(s,l)∈X} C(d)(s)C(d)(l)` (`miniature_nu_eq`), so the calibration manifold is exactly the open curve `{X ↦ ∑_{(s,l)∈X} m(s)m(l) : m full-support}` for every procedure (`miniature_manifold_iff`) and every manifold point has equal sample and live marginals (`manifold_equal_marginals`). CA-10′'s sentence is **confirmed**: the product state with marginals `(½, ⅓)` is on no point of the manifold (`prodState_half_third_not_mem_manifold`). But the marginals are linear, so every point of the convex hull has equal marginals too, and the same product state is outside the hull (`prodState_half_third_not_in_hull`, for the two-point hull `InHull2`). The hull does strictly exceed the manifold — the witness is the midpoint of the curve points at `m = ¼` and `m = ¾`, `(5/16, 3/16, 3/16, 5/16)`, a convex combination of two manifold points that is on no point of the curve (`miniature_hull_exceeds_manifold`: a curve point with `f{(a,a)} = 5/16` would need `m(a)² = 5/16`, while `f(sample = a) = ½` forces `m(a) = ½`).
**Reading:** no source sentence is wrong. CA-10′ says "off the curve", which is true; Q2 says the credal candidate is the convex hull, which is a definition. The mandate's parenthetical attaches the off-curve witness to the hull claim, which it cannot witness; the claim itself is true with `hullMid`. Severity: mandate-level imprecision. (Also recorded: CA-10′'s "rank 1" is not formalized — the Lean gives the parametrization, not the rank.)

