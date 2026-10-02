# dp-devices-catalog — findings about the sources

Severity scale ([STANDARDS](../../STANDARDS.md) §5): blocking / local error / imprecision / presentation. Each entry names its pointer and the Lean declaration that establishes it.

## F1 — v2 §7.1 remarks (2)/(4) presuppose a draw-conditioned evaluator; the typed Remark-3.12 device inverts (local error in the remarks' wording, v2 line 229; DY-5)

v2 line 229, remark (2): "A procedure evaluating actions by tremble-limit conditional value takes ten at both points and thereby makes `O_5` *inconsistent* (Definition 16)"; remark (4): "Problem-side limit calibration does *not* exonerate `C_0`; only procedure-side trembling rescues". Read with Remark 3.12's device typed as dp-calibration's D2 (`EventTrembleEdtConsistent` / `D2At`, Definition 8 clause 1 for `C^ε` then Definition 18, with the escape clause), the verdict is the **opposite**: `ν_{C*^ε}(· ∣ O₅) = δ_{(5,5)}` exactly at every `ε` (`tys_tremble_nu_five`: the `ten ∧ O₅` event has no leaf-world), so `A⁺_{d₅}(ε) = {five} ⊉ supp C*(d₅) = {ten}` and D2 rejects `C*` at every `ε` (`procTake10_not_d2At`) while approving `C₀` (`procFiveTen_d2At`); `tys_d2_inverts`. The remarks are right for an evaluator conditioning on the *draw* — Theorem 1's forcing under `C^ε` (D3), where `C*` is approved at every `ε` (`procTake10_occTrembleEdtConsistent`: `5` vs `10 − 5ε/2` at `d₅`) — and the static picture separates `C₀` from `C*` without dynamics (`procFiveTen_not_coherentPureAt_five`, `procFiveTen_sia_five`, `procFiveTen_ssa_five`). Remark (2)'s own phrase is "tremble-limit conditional value", D4's; D4 also approves exactly `C₀` for every procedure (`tys_adviceEdt_iff`), so the remark fails under *both* event-conditioned readings — D2 at each `ε` and D4's limit — and the finding does not depend on typing Remark 3.12's device as D2. Fix: in remarks (2) and (4), say "occurrence-trembled" (draw-conditioned) rather than "tremble-limit conditional value", or state that the event-conditioned devices invert.

## F2 — Proposition 8's masked clause is false for `C*` (inherited from dp-calibration findings F2; not re-litigated)

Inherited: `tys_take10_not_maskedOCV` (dp-calibration). This package adds Proposition 8's *value* clause (T5(a)).

## F3 — Remark 3.14 is not v2 text (presentation)

It is sl-amendments SL-17 (ADOPT), `sl-amendments.md:126–128`; formalized here as this package's proposal (`Source: sl-amendments SL-17 (proposed Remark 3.14)`). P13-10′'s reading of the label `π := P_{s₅}(m=10)` as the agent's prior is ATTRIBUTION-UNVETTED. SL-17's definitional sentence is also internally inconsistent with its applications: F12.

## F4 — Proposition 9's "no optimal V1 policy one-boxes at the empty box" fails at `p = 1` (imprecision, v2 line 244)

v2 allows `p ∈ (½, 1]`. At `p = 1` with `L > S`, `V1(1,1) = L = V1(1,2)`, so the one-boxer `(1,1)` is a pure optimum of V1 and one-boxes at the (never-realized) empty box. For `p < 1` the claim holds. Lean: `tnV1_empty_box_one_boxers` (both halves). Fix: state the clause for `p < 1`, or read "one-boxes at the empty box" as "at a realized empty box".

## F5 — Proposition 9's "optimum" is over pure policies and does not extend to mixed ones in V1 (imprecision, v2 line 244; the mandate's T2 trap)

In V1 at `p = 1`, `L = 3/2`, `S = 1` (so `L > S > 0`, `(2p−1)L > pS`), the mixed policy `(x, y) = (9/10, 0)` has `V = 77/50 > 3/2`, the maximum of the four pure values: mixing at the hypothetical `d_F` sends the run to the empty branch with probability `1 − x`, where `both` collects `S`, while the full branch still pays `L + (1−x)S`. Lean: `tnV1_mixed_beats_pure`. In V2 the pure optimum `(1,1)` is optimal among all procedures under `(2p−1)L > S` (`tnV2_large_isOptimal`), so the asymmetry is real. Fix: say "among pure policies" in V1, or add the mixed optimum.

## F6 — Mandate slip: the V2 `(1,2)` value at `(¾, 4, 1)` is `7/4`, not `5/2` (mandate T2)

`(1−p)L + pS = 1 + 3/4 = 7/4`. Lean: `tn_instance_values`. The mandate said "recompute, do not copy"; recorded so the ledger's numbers are traceable.

## F7 — Mandate slip: `mug1_value ≠ mug2_value` is not "for every interior `q`" (mandate T7(f))

`V_{B₁}(C) − V_{B₂}(C) = y(2q − 1)/2`, so the two values coincide at `q = ½` (for every `x, y`). Lean: `mug_fp6`. The source (FP-6) claims only that the strict states are identical while the PDC slots differ; shipped as "differ iff `q ≠ ½`".

## F8 — dp-cf-2-013's "third carrier" presumes the 12-atom product algebra; on the four-world carrier its uncalibratability clause is trivial (encoding-dependent, dp-cf-2-013 / FP-4)

FP-4's act-supposition `½δ_{(T,pay,0)} + ½δ_{(H,pay,1)}` needs the atom `(H, pay, 1)`, which `dp-core-tree`'s `MugW` does not contain (the `H`-leaf world `hOne = (H, ⊥, 1)` records the transfer, not the simulated act). The nearest object is the pushforward `thirdCarrier = ½δ_{tPay} + ½δ_{hOne}` (value `½(y−x)`, `thirdCarrier_value`), and the clause "`ν_{C'}(H ∧ pay) = 0` for every `C'`" holds because the event is *empty* (`mug1_nu_H_pay_zero`), not as a calibration fact. The known-issue 7 check came out as the mandate anticipated: the encoding does not carry the simulated act, and the claim was not forced. The encoding-dependence cuts the other way too (machine-checked, `thirdCarrier_perRunSSC`): on this carrier `occ = Leaves`, so per-run clause 1 reads `P_s = ν`, and `ν_{δ_pay} = ½δ_{tPay} + ½δ_{hOne}` is exactly `thirdCarrier` — it is the `P` of the per-run-SSC-calibrated state at `C = δ_pay` (dp-calibration's calibrated state at `⊤`, `mug1_perRun_not_strict`), so FP-4's nearest rendering here is a *calibrated* state at the SSC grade for the payer, not an uncalibratable one.

## F9 — dp-sl-065's penalty threshold "`c ≳ .68`" is underspecified in `k`, and confirmed at `k = 10` (imprecision, plan §0.4 rule 4)

dp-sl-065 gives ".98 at `q = 2/3`, `k = 10`" in the same sentence, so `k = 10` is fixed by context; at that `k` and the miniature's tie `q = 2/3` the detector fires with probability `58024/59049` and the exact threshold is `c ≥ 19683/29012 ≈ 0.6784` (`probe_threshold`) — the decimal is right. At other `k` the number differs (at `k = 1` the detector never fires), so the threshold should carry its `k` explicitly. Fix: name `k` next to the threshold.

## F10 — Known issue 4 confirmed and closed: CA-14′'s "D2 False everywhere" on the AMD is a universal, encoding by encoding (dp-cf-047)

Last-draw: `amd_last_not_eventTremble` for every `q ∈ [0,1]` (the source checked `{0, ⅓, ⅔, 1}`); first-draw: exactly `{δ_b}` (`amd_first_eventTremble_iff`); unrecorded: every `q`, vacuously (`amd_unrec_eventTremble`). The same universality for D3 (`amd_not_occTremble`; the source's cell was one `ε`).

## F11 — The vacuity criterion makes ZO-19's nineteen `vac` cells a corollary, not a list (extension)

`d2VacuousAt_eps_free`: D2's escape clause fires for all small `ε` at `d` iff no chance-positive leaf-world lies in any `a ∧ O_d` — a property of `(B, obs, actEv)` alone; `eventTremble_of_unrealised`: then every procedure is D2-consistent. So "the AMD is event-tremble-EDT-consistent at every `q`" (the phase-1 `T`) is true and empty, exactly as ZO-19 (i) says; the grid's `vac` is the right reading and its per-row check can be replaced by the tree-level condition.

## F12 — SL-17's definitional sentence for "trap" and "dilemma" contradicts its own three applications (local error in SL-17's wording, `sl-amendments.md:126`; found by audit round 1)

SL-17(b), verbatim: "Say a procedure class fails a stipulation set *regardless of label* if every member makes the good outcome inconsistent at every κ-calibrated label, and call the failure a *dilemma* rather than a *trap* if some procedure outside the class attains more (Definition 21)." Read literally: fails regardless of label **and** some outside procedure attains more ⇒ *dilemma*. The same paragraph then applies the words three times: (i) strict Told-You-So, where the family fails only at the self-fulfilling label, is "a dilemma of selection (Remark 5.2)"; (ii) masked/limit Told-You-So, where "the family fails at every calibrated label while `C*` attains `10` (Proposition 8)", is "a trap with a way out"; (iii) "a two-round tree punishing every crossing is a trap and no dilemma." Application (ii) is exactly the definitional sentence's *dilemma* case and is called a trap; (i) is a case the sentence does not cover (the family does not fail regardless of label); only (iii) is consistent with the sentence. P13-10′'s two tests, which SL-17 cites, agree with the applications, not the sentence.

The two well-posed readings. **(A) The applications' reading**, which this package formalizes (`FailsRegardlessOfLabel`, `Trap`, `Dilemma` in `Remark314.lean`): *trap* = fails regardless of label with a way out (an outside procedure, itself κ-calibrated, attaining the outcome); *dilemma* = not failing regardless of label (some member attains the outcome at some calibrated label); a tree with no way out is neither. Under (A) the verdicts are `tys_strict_dilemma`, `tys_masked_trap`, `tys_limit_trap`. **(B) The sentence's literal reading**: *dilemma* = fails regardless of label with an outside winner; *trap* = fails regardless of label with no outside winner (reading "rather than" as the complementary case). Under (B) masked/limit Told-You-So would be a *dilemma* and a no-way-out tree the only *trap*, the opposite labels; the strict case has no name. Fix for SL-17: swap the two words in the definitional sentence — "call the failure a *trap* … if some procedure outside the class attains more" — and add the clause the first application needs: "and a *dilemma* if the failure is label-dependent (the class attains the outcome at some calibrated label)". Audit round 1 of this package (both lenses) found the discrepancy; the package's docstrings now quote the sentence in full and say which reading they render.
