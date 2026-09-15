# Report

Verdict:
**LI-LEARNS-THE-CORRIGIBILITY-INEQUALITY-UNIFORMLY-OVER-EFFICIENT-MENUS-WITH-A-DIRECTIONAL-MISMATCH-TERM**
(`README.md`).  Outcome **A** of the dispatch: a theorem that a logical inductor learns
the structural no-bypass inequality from the architecture specification itself, with a
finite-menu corollary; plus one refutation inside the existing structural theorem.

## The stack

| | statement | status |
|---|---|---|
| T1 | corrigibilization preserves principal options: structural corrigibility (per-event authorization), idempotence, forcing preservation (exact at `δ = 0`, `δ`-neighbourhood otherwise), `W_opt(𝔠π) ≥ W_h(π) − L·E[δ]`, `W_h(π) ≤ W_h(𝔠π; ρ) + L·E[δ] + E[ρ]` | existing LEAN (`corr_idem`, `corr_fix_iff`, `ensures_mono`, `sup'_le_sup'_add`, `option_dominance_of_approx_reproduction`, `loss_conditional_on_decision`) + FIX; **the "or later" authorization clause is refuted** (`ShopRepair`) and the per-event clause restores C1 |
| T2 | `U_raw − U_corr = both·(w_raw − w_act) + M·w_raw − M'·w_act`; `E[U_raw] − E[U_corr] ≤ L·E[both·δ] + E[both·ρ] + D·E[M]`, `M = c_raw ∧ ¬c_corr`; `D` sharp; marginal-rate form false; sealing is `M ≡ 0` | LEAN (`mismatch_identity`, `mismatch_bound_exact`, `mismatch_bound`, `security_bypass_le_mismatch`, `Witness.attained`, `Witness.marginal_refuted`, `Witness.reverse_free`); FIX (B time-critical attains it) |
| T3 | gated products are single `[0,1]`-LUVs; `B_n = U_raw − U_corr − λG_δ − G_ρ − G_M ∈ BLCS`; valid in every `W ∈ PC(Γ)` under the architecture specification; `thm:expprovind` gives `E_n(U_raw,n) − E_n(U_corr,n) ≲_n L·E_n(Δ_n) + E_n(R_n) + D·E_n(M_n)` with no calibration term | PAPER (`thm:expprovind`); LEAN (`MediatedPair.B`, `ValidAt.value_le_of_valuesAt`, `ValidAt.ofGated`, `GatedAt.valuesAt`, `li_constraint_le`, `li_bypass_le` through the pinned `thm:expcoh` with its operational premises as named hypotheses; `Witness.valid` inhabits the package in every world) |
| T3′ | `max_{q ∈ Q_n}[…] ≲_n 0` for `|Q_n| ≤ poly(n)` by the near-argmax weighting; bounded menus need no selector | LEAN (`softWeight_aggregate_ge`, `nearMax_weighted_ge`, `uniform_of_soft`, `max_asympLE`); PAPER for `P`-generability of the weights; FIX (hard argmax discontinuous, ties, `n²` menus) |
| T4 | `thm:wubexp` on the sequenced-settlement pair with a finite horizon: no persistent efficiently detectable positive-margin overvaluation; a switching margin gives finitely many bypasses when realized costs vanish | PAPER (with the support-condition erratum); FIX (expiry, categories, margins); not Lean |

Lean: `lean/Workspace/Deference/Contrib/LICorrigibility.lean`, 25 audited
declarations, `[propext, Classical.choice, Quot.sound]` throughout.  Fixtures: 45,
`python3 tests/run.py`.

## The fourteen questions

1. **Representable as a bounded LUV-combination sequence?**  Yes.  Constant
   coefficients `1, −1, −λ, −1, −1`; `ℓ¹` norm `3 + λ`; the LUVs are formula templates
   instantiated with the codes of `π_n`, `𝔠π_n`, the occurrence and the horizon.
2. **Activation-gated products?**  Cleanly: a gated product is one LUV whose defining
   formula contains the case split (`def:luv` admits any formula); at the pinned
   threshold interface it is `GatedAt`, with `gate φ X` the concrete family.  No closure
   theorem is needed; the only obstruction is formalization labour.
3. **What lives in `Γ`?**  The interaction model as definitions and theorems: the
   transition and effect semantics (EX), the gate and latch programs (MS, DP), the
   activation and expiry semantics, the evaluator's `L`-stability certificate, the
   definition of `ρ`.  EF is *not* needed for the inequality; it is T1's hypothesis.  In
   a finite model all of it is decidable; as a claim about the real system it is the
   architecture's external contract, and the theorem applies inside the worlds satisfying
   it (`LUV_COMPILATION.md` §3).
4. **Does EPI apply directly?**  Yes, the `≤` case with `b = 0`; its hypothesis is
   validity in `PC(Γ)`, not provability in `D̄_n`.
5. **Can the selected pair depend on current prices?**  Only continuously.  A hard
   argmax is not an expressible feature; the near-argmax weighting is, and the
   conclusion survives with a `2δ_n → 0` window.
6. **A true finite-menu uniform theorem?**  Yes, T3′, for every efficiently
   enumerable menu of polynomial size; trivially for bounded size.
7. **Which mismatch term?**  `M = c_raw ∧ ¬c_corr`, the joint directional event in one
   world, with the common-branch terms gated on `both` — not on `c_raw` alone as the
   dispatch's candidate had it, and not the marginal difference.
8. **Is `D` sharp?**  Yes (`Witness.attained`); the exact charge on the mismatch branch
   is `M·w_raw`.
9. **What remains of calibration?**  Nothing in T3: the inequality is between the
   inductor's own expectations.  Calibration re-enters only to relate `E_n(G_δ,n)` to
   the physical discrepancy — by `thm:expprovind` if it is `Γ`-determined with an e.c.
   value, by T4 if it settles, by nothing if it is same-branch.
10. **What makes the right-hand side small?**  Small `E_n(Δ_n)`: faithful mediation
    (joinability bounds `δ`, T_JOIN).  Small `E_n(R_n)`: the principal's decision quality
    at the cell.  Small `E_n(M_n)`: the sealed-comparison architecture (item 89) —
    sequenced settlement gives `M ≡ 0`.  None is supplied by Logical Induction.
11. **What settles?**  The structural inequality is deductive; the program's output on
    a fixed trace is adjudicated; the trace is empirical; an amendment's goodness
    without a program is non-settling.  Under same-branch activation only the selected
    option's security settles and the comparison never does.  Finite expiry must be in
    the occurrence type.
12. **Chooser-side assumption?**  A switching margin `γ > 0`, with realized costs on
    the bypass occasions averaging below `γ`.
13. **Does any assumption restate the conclusion?**  No.  The `(1,1)`-branch inequality
    is definitional given the stability certificate and `ρ`'s definition; what is
    assumed is what `δ` and `ρ` *are*, and nothing assumes their expectations small.  The
    assumption that would restate the conclusion — small right-hand side — is not made.
14. **Strongest alignment claim without manipulation/authorship?**  `LI_CORRIGIBILITY.md`
    §6: no primitive bonus for control is needed; under a faithful mediated counterpart
    and a specified architecture the inductor learns, uniformly over efficient menus and
    by its own expectations, that bypass has no advantage beyond the mediation
    discrepancy, the principal's decline regret and the candidate's causal leverage over
    the comparison's evaluation.  `Corrigible ∧ ¬Authored` remains inhabited; the pair
    satisfies the inequality with `B = 0`.

## Deviations and prompt corrections

- The candidate inequality `U_raw − U_corr ≤ L·Δ + R + D·M` is confirmed with `Δ, R`
  gated on `c_raw ∧ c_corr` (the dispatch's "activation-gated" read as gated on the
  common event), not on `c_raw`; the exact identity shows why.
- The dispatch's `q*_n := argmax` selector is inadmissible as stated; the round proves
  the softened form and records the hard form as refuted.
- The dispatch's T1 asks for "every principal-forcible set … remains principal-forcible";
  that is exact only at `δ = 0`, and the round states the `δ`-neighbourhood form
  otherwise.
- The 2026-09-09 authorization clause was found to fail for repeated effects; the round
  does not edit that tree and records the repair as a decision entry.
- Effect completeness is not a hypothesis of T3, contrary to the dispatch's expected
  list of architecture axioms; it is T1's.
- `thm:wubexp` is used with the support condition the printed statement omits (the
  pinned formalization's erratum).
- Empirical settlement is outside the paper's computable deductive process; T4 is
  stated for the closed finite model or an oracle-relativized inductor, and the
  relativized theorem is not proved here.

## What is not established

- `P`-generability of the compiled sequence at the pinned interface
  (`LUVCombination.PolySequence` with `RpnSpliceStream` serialization); taken as named
  hypotheses in `li_bypass_le`.
- The object-level derivation of `GatedAt` from a first-order gated formula (the
  frontend's arithmetic-closure boundary).
- T4 in Lean (the pinned feedback lane has one constant inhabitant).
- Any rate, any smallness of the right-hand side, anything about manipulation,
  authorship, undeclared channels, superpolynomial menus, or a latent utility.
- The oracle-relativized inductor for empirical logs.
- The trajectory-level C1 in Lean (the step lemma is; the predicate is FIX).

## Proposed priority changes

- **Item 84**: dated note — the security-score register now has an EPI theorem with no
  calibration term; the latent-value bridge is unchanged.
- **Item 89**: dated note — sealed comparison is now the case `E_n(M_n) = 0` of a learned
  inequality, and item 89's deliverable becomes "make `E_n(M_n)` small", with sequenced
  settlement giving `M ≡ 0`.
- **New item 90**: relativized logical induction for empirical settlement of activated
  securities, and the `P`-generability certificate of the compiled sequence.

## Outstanding maintainer actions

1. Decide whether the per-event authorization clause replaces the "or later" clause in
   the 2026-09-09 register and on `wiki/Corrigibility.md` §1 (the round adopts it,
   agent-decided, reversible; `DECISIONS.md`).
2. Decide whether T2–T3′ enter `wiki/Corrigibility.md` §4 and `wiki/Theorem-Spine.md`
   §10 as research state after this pass is adjudicated; the round does not edit the
   wiki.
3. Decide whether `li_bypass_le` and `softWeight_aggregate_ge` are registered against
   item 90 (the round files the item; registration is the merge).
4. Merge is the maintainer's; the round does not merge.

## New names introduced (provisional)

*directional activation mismatch* `M`, *common branch* `both`, *reverse mismatch* `M'`,
*compiled constraint* `B`, *gated LUV* (`GatedAt`, `gate`), *near-argmax weighting*
(`softWeight`, `ramp`), *sequenced-settlement pair*, *switching margin*, *per-event
authorization*; Lean `LICorrigibility`, `MediatedPair`, `ValidAt`, `canonicalValue`,
`li_constraint_le`, `li_bypass_le`, `uniform_of_soft`, `max_asympLE`, `indR`,
`expectR`; fixture `ShopRepair`, `TimeCritical`.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-15-li-corrigibility/PROMPT.md`.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-15.
