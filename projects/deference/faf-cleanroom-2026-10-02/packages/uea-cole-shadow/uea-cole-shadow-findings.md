# uea-cole-shadow findings: errors, imprecisions and gaps in the sources

*Formalizer agent of the faf-cleanroom run (Fable 5.1, [scrubbed]), 2026-09-30. Per [STANDARDS](../../STANDARDS.md) §5. Severities: blocking (the note's conclusion falls) / local error / imprecision / presentation. Lean names are in `Cleanroom.Uea.UeaColeShadow`.*

## F1. F1 fails at percepts of probability zero (imprecision, [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §1, [audit-revised-theorem-1](../../sources/unbounded-embedded/audit-revised-theorem-1.md) §1)

The note states F1 as "`w_{hae} = w_{ha}` — percepts never move the self-posterior", for every percept `e`. Under the note's own convention `w_h := 1` at `ξ`-null `h`, this is false when `ξ(ha) > 0` and `ξ(e|ha) = 0`: then `ξ(hae) = ξ(e|ha) ξ(ha) = 0`, so `w_{hae} = 1`, while `w_{ha}` can be anything in `(0,1)`. The correct statement is `wS_ext_of_xie_ne_zero` (F1 for `ξ(e|ha) ≠ 0`) plus `wS_ext_of_xiA_eq_zero` (both sides `1` when `ξ(ha) = 0`). Nothing downstream needs F1 at a zero-probability percept — every use is inside a sum weighted by `ξ(e|ha)` (Theorem C's node identity, the odds along `π⋆`, `child_odds`) — so Theorems B and C are unaffected; the Python never sees the case because its percept kernels are fully supported or deterministic. Fix: add "for every `e` with `ξ(e|ha) > 0`".

## F2. The mandate's F1 gloss inherits the same gap (presentation, `uea-cole-shadow-mandate` target 2)

"F1: `w_{hae} = w_{ha}` for every percept `e` (both `= 1` when null)" — the parenthesis covers `ξ(ha) = 0` but not `ξ(e|ha) = 0` with `ξ(ha) > 0`. Formalized as in F1.

## F3. The `T = 2` pure-existence argument needs a fallback at residual-null root actions (imprecision, [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §4.5)

The note argues: under the pure root policy `x`, `Q_ξ(ε,y) = Q^{π̄}_ξ(ε,y)` for `y ≠ x`, so the root action maximising `Q^{π̄}_ξ(ε,·)` is a plain fixed point. At a root action `y` with `ξ_{-S}(εy) = 0` (no hypothesis plays it), `π̄(·|εy)` is undefined (the Lean junk value is `0`) and the continuous extension gives `Q_ξ(ε,y) = Q^π_ξ(ε,y) = Q^*_ξ(ε,y)` instead, which can exceed `Q^{π̄}_ξ(ε,x)`. The argument survives with the corrected score `g(y) := Q^{π̄}_ξ(ε,y)` if `ξ_{-S}(εy) > 0`, else `Q^*_ξ(ε,y)`: under pure `x`, `Q_ξ(ε,y) = g(y)` for `y ≠ x` and `Q_ξ(ε,x) ≥ g(x)` (Lemma A′ or the extension), so the maximiser of `g` is a plain fixed point; the floored variant goes through likewise. Severity: imprecision (the theorem is true; the proof's identity is false at residual-null actions). Status here: formalized with the corrected score — `PureT2.score`, `PureT2.Qxi_pure2_root_ne`, `PureT2.score_le_Qxi_pure2_root`, `PureT2.pure_T2`.

## F4. The post's u.s.c. claim has the direction backwards (blocking for the post's proof; the conclusion is open in rOSI) — [lesswrong-post--live-2026-08-22](../../sources/unbounded-embedded/01-primary/lesswrong-post--live-2026-08-22.md) line 216, `uea-inventory` 007

"`f` remains upper semicontinuous because we only reset the subtree when a strict inequality is satisfied": strictness makes the reset region *open*, and a correspondence that switches between two single-valued branches needs the switching set closed on both sides, impossible unless the branches agree on the boundary (they do not: Instance A at `t⋆` has `𝒜_root = {a₁} ≠ {a₂} = {π⋆}`, `InstA.tstar`). Instance B is the finite witness: `InstB.not_hasClosedGraphOn_strict` proves the strict-reset map has no closed graph over the product of simplices, `InstB.not_isStrictResetFP` that it has no fixed point at all, and `key_lemma_refuted` that no plain fixed point satisfies the trust bound everywhere. The post's *conclusion* is not refuted: Theorem B holds at every trust-bound node (`theoremB`), the floored agent has near-optimal fixed points everywhere (`theoremC`), and the finite loss on B is `1.5 δ`. Whether the modified `f` produces a reflective oracle in rOSI is untouched here (the rOSI statement is not formalized).

## F5. The founding sketch's horizon-free `C · O_h` bound is false, and its measure-change step was wrong as an argument (local error, [00-founding-sketches](../../sources/unbounded-embedded/unbounded-embedded-lab/notes/00-founding-sketches.md) §2; [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §4.2–4.3)

`Chain.no_horizon_free_bound`: for every `C` there are a model, a floored fixed point and a node with `0 < w_h` and `ε(h) > C · O_h` (the dyadic chain `δ = 2^{-m}`, `K = m`). The chain's loss `(O₀/2) ∑_{k<K} 1/(1+O₀ 2^k)` is proved as an exact identity for every `K` and `δ` (`Chain.gap_root`), not only for the seven pairs the note checks. The correct rate is `Θ(δ log(1/δ))`; the horizon form `O_h (1+T)` is `theoremC`.

## F6. uea-004's `(1+|A|)δ` constant is loose (presentation, [audit-revised-theorem-1](../../sources/unbounded-embedded/audit-revised-theorem-1.md) §3)

Superseded by Theorem B's `O_h` with no `|A|` factor (`theoremB`, `theoremB_corollary`); recorded in the ledger, not re-proved.

## F7. The mandate's Lemma A positivity hypothesis is stronger than needed (presentation, `uea-cole-shadow-mandate` target 3)

Lemma A in the note's form holds at every decision node with `ξ(h) ≠ 0`, not only where `ξ(ha) > 0` (`xia_mul_Qxi`): at `ξ_{-S}(ha) = 0` the junk values of `π̄(a|h)` and `Q̄(h,a)` are multiplied by vanishing factors. The unnormalised form `xiA_mul_Qxi` needs no hypothesis at all. Lemma A′'s identity `Q̄ = Q^{π̄}` does need `ξ_{-S}(ha) > 0` (`Qmix_eq_Qbar`), as the mandate says.

## F8. `π⋆` as "the first action attaining the max" needs an order the model does not carry (presentation, [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §1)

Formalized as one fixed `Classical.choice` of an optimal action (`piStar`), which is what §7 item 6 asks for ("any fixed selection works"); at every node of every instance in this package the optimum is unique, so the selection is determined (`piStar_eq_of_unique`).

## F9. The reaudit's Instance B numbers are exact at `δ = 0.2`; the family's `≈ 1.25 δ` is not formalized (presentation)

`InstB.Vpi_root_of_isPlainFP`: loss `3/10 = (3/2) δ`; `InstB.resid_root_neg_of_isFlooredFP`: loss `3/20 = (3/4) δ`. The `δ`-family `c₁ = 1 - δ/2`, `c₀ = (1-δ)(1-δ/4)` is `stretch` and was not attempted.

## F10. uea-2-016: nothing here rests on the round-2 scripts (presentation)

`theorem1_search.py` has no `main` and the round-2 write-ups do not exist; D0–D2 are `uea-sink-swim`'s. No claim in this package cites them.

## F11. The mandate's Gap 1 sequence `(1, 1-1/n)` needs the water coordinate fixed (presentation, `uea-cole-shadow-mandate` target 6a)

The reaudit's state is `(j, k)` with `s = π(swim|water) = 1` assumed ("the water node is a last step, so swim always"). In the product of simplices the water coordinate is free; the Lean sequence is `(1, 1 - 1/(n+2), swim)` and the value computation `Q_ξ(root, go) ≤ 4/5` with equality iff `(j, k, s) = (1, 1, 1)` (`InstB.Qxi_root_1_eq_iff`) carries `s` explicitly.

## F12. `fix-kakutani` naming (presentation)

Existence cites `kakutani_pi_stdSimplex` (a `variant` of Wyeth–Hutter–Leike–Taylor's Thm 33: finite-dimensional, closed graph), never "Thm 33".

## F13. Theorem B is strict: the mandate's target-10 attainment question is answered "never" (presentation, `uea-cole-shadow-mandate` target 10; [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §3)

The note states Theorem B as `gap ≤ O_h` and its tightness remark says the trap gives `gap/O_h = 1 - δ` "for every `δ`" — so the supremum `1` is approached; whether it is attained was left as target 10. `theoremB_strict` (`Strict.lean`, repair round 1) proves `gap < O_h` at every plain fixed point and trust-bound decision node with `0 < w_h < 1`, and `gap_eq_odds_not_attained` records the answer: the supremum is not a maximum. Each step of Theorem B's two-step bound is attained separately, and never both: the first at the tight trap (`gap = (1-w_h)V^*` with `p̄ = 0`, `SinkOrSwim.tight_trap_pbar`), the second exactly when `p̄_h = 1` (`theoremB_second_eq_iff`; e.g. at the informative mixed witness, where the second step is an equality and the first is strict, `SinkOrSwim.mixed_witness_second_step_tight`); `theoremB_strict` says they are never tight simultaneously (both tight would force `Q̄ = 1` on the support and an optimal self below, contradicting the tight first step). The supremum `1` of `gap/O_h` is approached by the trap with `p̄ = 0` (`SinkOrSwim.sup_approached_with_pbar_zero`), not through `p̄ → 1`. (Repair round 1 had written "tight in its first step and never in its second" here; that was false, and corrected in repair round 2 after the round-2 fidelity audit's B1.) The note could state Theorem B with `<` for `w_h < 1`. Severity: presentation — nothing in the note is wrong; the open question is closed.

## F14. The note's own §5 conjecture "some plain fixed point satisfies `(TB)` at every ξ-positive node" is false (local error in the note's status table, [sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §5; [oracle-side-gaps-reaudit](../../sources/unbounded-embedded/unbounded-embedded-lab/redteam/oracle-side-gaps-reaudit.md) Q5)

[sequential-self-game](../../sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md) §5 (line 146: "every one of the 2,000 instances had a pure fixed point of the plain agent satisfying `(TB)` at every ξ-positive node — the finite shadow of Cole's 'there is a reflective oracle' — true on all instances tried, unproved in general") and its status table (line 162: "some plain fixed point satisfies `(TB)` everywhere (Cole's existence lemma, finite shadow) | CONJECTURE, 2,000/2,000 instances") state as a conjecture exactly what `key_lemma_refuted_xi_pos` refutes: Instance B (`δ = 1/5`, [oracle-side-gaps-reaudit](../../sources/unbounded-embedded/unbounded-embedded-lab/redteam/oracle-side-gaps-reaudit.md) Instance B, same date 2026-08-25) has a unique plain fixed point, `(0,0,swim)`, and it fails `TB` at the root, where `ξ(root) = 1` (`InstB.isPlainFP_iff`, `InstB.not_TB_root_of_isPlainFP`, `InstB.xi_root`). The reaudit already says at Q5 that the lemma "is false in the finite shadow for `δ = 0.2`"; the note's status table is stale relative to it. F4 records the refutation against the post and the reaudit; this finding records it against the note's own conjecture. Severity: local error (a status-table entry that should read REFUTED); the note's Theorems B and C are unaffected. Fix: change the §5 sentence and the table row to "REFUTED (Instance B of the reaudit; `key_lemma_refuted_xi_pos`)". (Round-2 fidelity audit §3.2; added in repair round 2.)
