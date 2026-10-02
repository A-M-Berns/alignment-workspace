# uea-sink-swim findings

*Findings about the sources ([STANDARDS](../../STANDARDS.md) §5), written 2026-09-30 by the formalizer of `uea-sink-swim`. Severity: **blocking** (the note's conclusion fails) / **local** (a false or ill-posed local claim) / **imprecision** / **presentation**. Each entry points at the source and, where there is one, at the Lean declaration in `Cleanroom.Uea.UeaSinkSwim.*` that settles it. Claims about what a person meant are ATTRIBUTION-UNVETTED.*

## F-1 (blocking for the printed theorem; the author retracted it) — the 2025 Theorem 1 is false as printed

[lesswrong-post--live-2026-08-22](../../sources/unbounded-embedded/01-primary/lesswrong-post--live-2026-08-22.md) line 236 states: for every `ε` there is `δ` such that `ξ ≥ (1-δ)ψ^{π_S}` makes `π_S` `ε`-optimal. In the finite-shadow reading (`Printed2025.Reading`, ATTRIBUTION-UNVETTED: deterministic percepts, the premise by construction, "π_S" = any plain fixed point) it is refuted by sink-or-swim at `b = 1, c = 1/2, s = 1`, where the trap is a pure plain fixed point with root loss `1/2` for **every** `δ ∈ (0,1)` (`Printed2025.refuting_family`, `Printed2025.printed_theorem1_refuted`). The trap condition `b(1-s) ≤ c` carries no `δ` (`TheoremA.trap_isPlainFP_iff`); that `δ`-freeness *is* the refutation (the plan's "surviving neighbour is the δ-free form" is read this way). The theorem was retracted by its author: the July-2025 copy `01-primary/lesswrong-post--logsidian-annotated-copy-2025-07.md` line 591 carries the author's `[EDIT: This theorem is currently broken. The problem is that, in Lemma 1, the action-values for off-policy actions can be underestimates, which means the expansion in terms of maxima is wrong. …]`, and the live post keeps the theorem under the heading "Appendix: Original Broken Argument" (line 233); the inline marker at line 254 ("[This is the gap, the expansion is wrong because action-values / value functions off-policy are wrong]") locates the gap in Lemma 1's off-policy value expansion and is, per `uea-inventory` 021, the corpus author's annotation rather than the post author's. (Erratum, repair round 1: this finding and the mandate's target 2 cited an `[EDIT: … broken …]` "at line 198" of the live post; the live post has no `[EDIT` and no "broken" at or near line 198 — line 198 opens the revised result. `uea-inventory` 021 had the pointers right.) The refutation does not depend on reading "π_S" as *every* fixed point: under the charitable existential reading (some plain fixed point is `ε`-optimal at the root) it is refuted too, by the trap chain, on which every plain fixed point loses more than `ε` (`Printed2025.ReadingExists`, `Printed2025.readingExists_false`, `Printed2025.both_readings_false`; at `γ = 1`). Surviving neighbours: Theorem B (`uea-cole-shadow`), D1 with horizon-dependent `δ` (`BestOnPath.theoremD1`, `Quantifiers.horizon_dependent_delta`), and Theorem A's good-point condition `δ s ≤ 1 - c/b`. Lemma 2 of the post is not formalized.

## F-2 (local, corrected in the note itself) — "when both pure fixed points exist" needs *strictly*

[00-founding-sketches](../../sources/unbounded-embedded/unbounded-embedded-lab/notes/00-founding-sketches.md) §1 says a mixed fixed point exists when both pure fixed points exist; [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §2 corrects this to *strictly*. `TheoremA.jstar_mem_Ioo_iff` proves `0 < j* < 1 ↔ b(1-s) < c ∧ c < b(1-δs)`: at a boundary `j*` is `0` or `1` and the "mixed" point is a pure one.

## F-3 (presentation) — D0–D2 are a docstring plus unasserted code

`theorem1_search.py` has no `main`, no assertions, no sections (v)–(vi) and no sympy solver (`uea-2-inventory` 2-016); the survey's first run "refuted" D0 on `δ = 5/4` instances (a sampling artifact: `δ ∉ (0,1)`). Nothing in this package rests on the scripts having run. D0, D1 and D2 are now theorems (`ResidualArgmax.piR_isPlainFP`, `BestOnPath.theoremD1`, `TrapChain.isPlainFP_iff`); the proof sketches were the mandate writer's, verified here. Two points the sketch left implicit, settled in the Lean: D1 needs its own base case at the last level (`S = Q^*` there, `BestOnPath.S_eq_Qstar_of_children_terminal`), and a node with `w ≥ 1-δ` can be `ξ`-null off the path (`w = 1` by convention), where the loss is `0` because `π^B = π^R` is optimal on null subtrees.

## F-4 (local) — D2's "unique pure fixed point" is unique among all policies; the boundary `δ' = δ`

The source verified uniqueness among pure policies for `K ≤ 6`; `TrapChain.isPlainFP_iff` proves it among all policies, pure or mixed, for every `K, δ, δ'` with `0 < δ' < δ`, with strict preference at every node. At the boundary `δ' = δ` uniqueness fails (not formalized — `TrapChain.TP` has `δ' < δ`; the strict inequality is where `TrapChain.Qxi_goH_1_lt` uses it): the policy *go at every `h_k` for `k < K`, swim at `h_K`* becomes a plain fixed point, because under it `ξ_S(h_k) = 1` along the chain, so `w_{h_k go} = 1-δ` and `Q_ξ(h_k, go) = (1-δ)·1 + δ·0 = 1-δ`, which ties `c_{K-1} = 1-δ` at `h_{K-1}` and strictly exceeds `c_k = (1-δ)^{K-k}` for `k < K-1`. The literal all-`go` policy (sink at `h_K`, `Chain.allGo`) is *not* a fixed point even there (`Q_ξ(h_{K-1}, go) = 0 < c_{K-1}`), and the mechanism is `1-δ ≥ c_k`, not the one-step bound becoming an equality (that would need `V^π(h_{k+1}) = c_{k+1}`, which is false along the go path). Reworded in repair round 1 (audit r1 adversarial N5).

## F-5 (imprecision) — the post's "`n` bits ⇒ `2⁻ⁿ`" does not give the w.h.p. clause

[lesswrong-post--live-2026-08-22](../../sources/unbounded-embedded/01-primary/lesswrong-post--live-2026-08-22.md) line 222 argues that `n` bits of evidence against `π_S` has probability `≤ 2⁻ⁿ`. [audit-revised-theorem-1](../../sources/unbounded-embedded/audit-revised-theorem-1.md) §3.3 (the Ville correction) replaces this by the maximal inequality for the non-negative martingale `(1-w_t) ξ(h_{<t})`. The one-step identity behind it is `Martingale.one_step`; the maximal inequality and the composite clause are `stretch` S3, not done. The mixed sink-or-swim point shows the martingale is not constant (`Martingale.witness`: `w_island = 3/4`, `w_water = 1/3`).

## F-6 (local) — opaque Newcomb is ill-posed at the model level: the `ξ`-null-action convention decides

`uea-2-inventory` 2-003: with the class `{T₁}` alone, `two` is `ξ_{-S}`-null and its percept kernel is the fallback `∑ wᵢ νeᵢ/δ = T₁`'s kernel, so `ξ(M|two) = q` and two-box is the unique fixed point for every `q ∈ [0,1]` (`Opaque.onlyT1_fixedPoints`; the difference is `1/1001`). With a two-boxing hypothesis present (`f = (1/2,1/2,0)`) one-box is the unique fixed point iff `q > 1001/2000` (`Opaque.half_fixedPoints`). The note's "opaque Newcomb one-boxes" is therefore convention-dependent when the class lacks a two-boxing hypothesis: the fixed-point set is a function of the null-action convention (the continuous extension of `uea-cole-shadow` target 1), not only of the instance. Disclosed as (c) in the docstrings and ledger.

## F-7 (local) — 2-004's "argmax is UDT for `q > 1/2`" is the wrong comparison

The binding comparison for the argmax of `V_upd` is `UDT` vs `2box`: `UDT - 2box = (1999 q - 1000)/1001` (`Updateless.trueValue_diffs`), threshold `1000/1999 ≈ 0.50025`; the survey's `q > 1/2` is `UDT` vs `worst` (`UDT - worst = 1000(2q-1)/1001`). For `q ∈ (1/2, 1000/1999]` the argmax is `2box`. `Updateless.argmax_Vupd_UDT_iff` proves the corrected threshold. The script carries the same error, not only the survey (repair round 1, audit r1 adversarial N9): `newcomb_interleaving.py` `section3_report` (lines 334–335) asserts `pol_star == POLICIES["UDT"] and Ustar == q * MEG + (1 - q) * KILO` under `if q > F(1, 2)`; that assertion fails on `q ∈ (1/2, 1000/1999]` and was latent because the script's section-3 runs use `q = 9/10` and `q = 1`.

## F-8 (local) — 2-006's "unique fixed point is UDT" holds in one regime only

Without self mass the policy-level floor's unique fixed point is `UDT` iff `trueValue(2box) < (1-δ) V_upd^*` — for `q > 1000/1999`, iff `1001 - 1000 q < (1-δ)(999 q + 1)` — and `2box` otherwise (`PolicyFloor.isPolFloorFP_iff`, `PolicyFloor.twoClass_cond_iff`). With self mass, `2box` is a fixed point iff `g(f) ≥ 0`, i.e. iff `f ≤ f*` when the `UDT` inequality holds (`PolicyFloor.twoBox_selfFP_iff_le_fstar`), so for small `f` **both** `UDT` and `2box` are fixed points (the self-trap). Without self mass the policy-level floor on transparent Newcomb is **not self-referential**: `polFloor π` does not depend on `π` at all (`w_root = 1-δ` for every policy and the rule outputs the fixed function `2box`), so `isPolFloorFP_iff` is the fixed point of a constant map (`PolicyFloor.polFloor_const`; the iff is regraded Kind L, the content being `piA_polEq` and `twoClass_cond_iff`); self-reference enters only through `VupdSelf π 2`, i.e. in the self-trap. The mandate's "`g 1 < 0 < g 0` for `q > 1000/1999` and small `δ`" is sharper than needed: `g(0) > 0` for every `q, δ ∈ (0,1)` (`PolicyFloor.g_zero_pos`) and `g(1) < 0` is exactly the `UDT` inequality (`PolicyFloor.g_one_neg_iff`).

## F-9 (local) — the current-node floor with the `V_upd` yardstick is inert

`uea-2-inventory` 2-005 tested specific values; `Updateless.isUpdFlooredFP_iff` proves it for every `U ≤ 1` and all `q, δ, f`: the floor never fires at `H_M` (`M(H_M) = 1 ≥ w U`), fires at `H_0` iff `KILO < (1-δ) U` and prescribes `two` either way. A per-node floor compares a per-node quantity against a global yardstick and is defeated by the last-level identity `Q_ξ = Q^*`; the answer to the sketch's round-2 target 2 is "it does nothing".

## F-10 (local) — mupi's Prop 4.29 transcribed with tree-fixed rewards is false

"Any deterministic policy is a fixed point of *some* dogmatic prior" fails when rewards are tree-fixed and there is no punishing percept: on the two-node tree with `jump ↦ 1`, `stay ↦ 1/2` and a unique percept, `stay` is a plain fixed point of **no** model, whatever the residual class — every index type `ι`, every `νa`, `νe`, `w`, `δ` (`NoPunish.stay_not_isPlainFP_any_residual`, quantified over all of them; `NoPunish.stay_not_isPlainFP` is the one-model instance), because with one percept `Q_ξ(root, a)` is the tree reward for every policy and every residual (`NoPunish.Qxi_eq_reward_of_unique`): `jump` pays its reward whatever the residual expects. (Repair round 1: the first round shipped only the one-model instance and labelled it the refutation; the existential over priors needs the quantified form, audit r1 fidelity B1.) The finite form that holds needs the reward to come through the percept — here the punishing percept `e₀` after any deviation (`Dogmatic.pol_isPlainFP`), disclosed (c). The `ξ`-loss of the dogmatic fixed point is `0` (`Dogmatic.Vstar_eq_Vpi`: the equilibrium is subjective); the trap is against the true kernel (`Dogmatic.witness`: loss `1/2` on a one-step tree). Theorem A's trap is a *different* mechanism (residual mass on the deviation with a bad continuation) from the dogmatic one (no residual mass on the deviation, punishing percept); sink-or-swim is the former.

## F-11 (imprecision) — uea-016's "`c_root = 1` is impossible" is retracted

The audit's claim is retracted by `uea-cole-shadow`'s Instance B; this package only adds `FiveTen.instB_floored_not_plain` (the strictly-firing floored point `(1,0)` is not plain — "the floor is a chicken rule"). Cole's view of the floor is ATTRIBUTION-UNVETTED and not asserted in any Lean statement.

## F-12 (presentation) — Idea 4 reading (a) is a squeeze; S9 (uea-2-027 (a)) recorded as a squeeze

[findings--unbounded-embedded-agency-ideate](../../sources/unbounded-embedded/04-deference-trust-lab/findings--unbounded-embedded-agency-ideate.md) Idea 4 reading (a) assumes what it concludes; no Lean. uea-2-027 (a) likewise: a hypothesis equivalent to the conclusion; recorded, no Lean (the mandate's disposition).

## F-13 (presentation) — the `2025-07-26` and `2025-10-20` chats add no formal content

Per `uea-2-inventory` 2-023/2-024 (recorded only; not opened here, per the mandate): copies of the post and the Discord thread plus note-taking outlines, and one unvetted methodological claim. No target.

## F-14 (presentation) — Cole's "`k → ∞`" gloss on mupi is wrong (uea-039)

mupi's Theorem 5.33 is per fixed `k`; its `k_t → ∞` proposition gives convergence. A note for correspondence; not a Lean target (rO-level). The finite content of uea-037 (the honest self-posterior frozen below the premise) is target 3: `Twin.twin_kills_good` and `Twin.premise_iff`.

## F-15 (presentation) — uea-036 and uea-047 have no finite statement here

uea-036 (oracle-call independence: an Omega modelled by independent oracle calls is uncorrelated with the agent's choice) is rO-level; its finite content is S2 (the agent-simulating Omega), not attempted. uea-047 (ROSI → ROLI translation) has no statement to formalize.

## F-16 (recorded) — the literature (b)-citation table (uea-045, 2-017–2-022), with verified numbering

**No finite theorem in this package uses any of these as a hypothesis**; every headline is grade (a) or a disclosed (c). The table records the citations the slice relies on, as the survey verified them:

| Item | Citation (verified numbering per the survey) | Status here |
|---|---|---|
| 2-017 | Wyeth–Hutter–Leike–Taylor, *Limit-Computable Grains of Truth* (arXiv:2508.16245v1): the definitions and theorems the audit and re-audit cite | recorded; not used |
| 2-018 | Catt et al. 2023, *Self-Predictive Universal AI*: Lemma 3 (= Leike 4.17), Lemma 9 (linearity of `Q`), Def 10 (Self-AIXI), Lemma 15, Thm 16 (assumes "sensible off-policy"), Thm 18 (main). uea-045's "Thm 4.31" is mupi's number for Catt's condition, not Catt's | recorded; citation corrected; not used |
| 2-019 | Kim–Lee 2026, *A Model-Free Universal AI* (AIQI): the `ε`-greedy Self-AIXI result is a §5 remark, not a theorem (uea-045 cites it as a theorem) | recorded; citation corrected; not used |
| 2-020 | Fallenstein–Soares–Taylor, *Reflective variants of Solomonoff induction and AIXI*: Thm 2.1 (a reflective oracle exists; proof deferred) and Thm 3.1 (rOSI dominance `ξ ≥ c_M · M`) | recorded; the finite shadow of the dominance remark is `Mixtures.mutual_dominance` (target 16), which does not cite it |
| 2-021 | Everitt–Leike–Hutter 2015: Def 3 (SAEDT), Def 4 (SPEDT), Def 6 (SCDT), Prop 7 (policy-causal = action-causal), one-step coincidence | recorded; not used |
| 2-022 | Leike 2016 thesis Lemma 4.17 (value difference `≤` TV distance); Wyeth–Hutter 2025 Thms 6–8 and Conjecture 9 | recorded; the finite Lemma 4.17 is `stretch` S6, not attempted |
| uea-045 | the literature table of the slice, with the two corrections above | recorded |

## F-17 (recorded) — the ten `recorded only` items, one line each (why no target)

- **uea-2-018, 2-019, 2-020**: literature; (b) citations only, none used (F-16).
- **uea-2-023, 2-024**: chats with no formal content (F-13).
- **uea-036**: rO-level (oracle-call independence); finite content is S2, not attempted (F-15).
- **uea-037**: mupi's Theorem 5.33; finite content is target 3, done (`Twin.twin_kills_good`).
- **uea-039**: Cole's `k → ∞` gloss; a note for correspondence (F-14).
- **uea-045**: the literature table; two citation corrections (F-16).
- **uea-047**: the ROSI → ROLI translation; no statement exists (F-15).

## F-18 (presentation) — a dead root action in the transparent-Newcomb encoding

The finite model has one action type per model, so the transparent root carries a second action (`1`, a dead node with reward `0`). It is never in an argmax (`Transparent.Qxi_root_1 = 0 < Q_ξ(look)`, `Transparent.Qxi_root_0_pos`, which needs `q ∈ (0,1)` so that `ξ(M) > 0`); disclosed in the docstring of `Transparent.model`. At `q ∈ {0, 1}` with a class that makes `ξ(M) = 0` the dead action could tie with `look` — the encoding is only claimed for `q ∈ (0,1)`.

## F-19 (presentation) — the mandate's "D1 non-vacuity on `sos`" was not formalized

The mandate asks that `π^B` be shown to equal the good point on `sos` in the coexistence regime. `π^B` is built from `Classical.choice` maximisers, so evaluating it on `sos` is a separate computation, still not done (not a doubt about D1). The chain half is now a theorem (repair round 1): `BestOnPath.piB_on_chain` — on the trap chain `π^B` is trusted at the root, loses exactly `1-(1-δ')^K` there, and D1's bound there is `1-(1-δ)^K` with `δ' < δ`, so the bound is attained up to `δ' → δ` (D1's N+ witness); `BestOnPath.gap_piB_root_le` is D1 at the root of every model with no hypothesis (`w_root = 1-δ` always); `TrapChain.piR_stay`, `TrapChain.piB_stay`: both canonical fixed points are `stay` on the chain.

## F-20 (local) — the floored fixed-point set of sink-or-swim is strictly larger than the plain one on the boundary `c = (1-δ) b`

The floored map's equality clause (`resid = 0 ⇒ supp ⊆ 𝒜_h ∪ {π⋆(h)}`, the note's `λ_h` mixing) makes every swimming policy with `QJ(j) ≤ c` a floored fixed point when `c = (1-δ) b` (`TheoremA.isFlooredFP_of_boundary`). Precisely (repair round 1, audit r1 fidelity N5): `QJ` is increasing in `j` with `QJ(0) = b(1-s)`, so that set is the interval `[0, j*]`, nonempty iff `b(1-s) ≤ (1-δ)b` iff `s ≥ δ`, and a *proper* superset of the plain set iff `j* > 0` iff `s > δ`; at `s < δ` the family is empty, at `s = δ` it is `{0}`. On the boundary the plain fixed points are `j = 0` (iff `s ≥ δ`), `j = 1` (always: `(1-δ)b ≤ b(1-δs)` for `s ≤ 1`) and `j = j*` when `0 < j* < 1`, i.e. `δ < s < 1` — so for `δ < s < 1` the plain set is `{0, j*, 1}` and the floored set adds the whole segment `(0, j*)`. Off the boundary the floored fixed points of `sos` are exactly: the trap iff `b(1-s) ≤ c ∧ (1-δ) b ≤ c`, the good point iff `c ≤ b(1-δs)`, the mixed point `j*` iff `(1-δ) b ≤ c` (`TheoremA.trap_isFlooredFP_iff`, `good_isFlooredFP_iff`, `mixedStar_isFlooredFP_iff`); every floored fixed point has `resid(island) ≥ 0` (`resid_island_nonneg_of_isFlooredFP`) — the floor never fires at a fixed point of this family. [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §2's A6 (as paraphrased by the mandate: "the trap is a floored FP iff `δ ≥ 1 - c/b`") is correct for the plain trap; the boundary family is the addition.
