# The theorem spine: T1–T4

Labels: **LEAN** (sorry-free declaration in
`lean/Workspace/Deference/Contrib/LICorrigibility.lean` or, where named, in
`MediatedRepairDominance.lean`; audits to the three allowed axioms), **FIX** (exact
fixture in `tests/`), **PAPER** (a theorem of arXiv:1609.03543 v5 used at its exact
statement, cited by label), **EXT** (a contract the theory does not pay), **OPEN**.
Names are provisional (`AGENTS.md` standard 6).

Throughout: a finite two-stage interaction at history `h`; `Π(h)` the agent's
continuation space; declared protected effects; `𝔠` the corrigibilization transform of
`CORRIGIBILIZATION.md` §3 (2026-09-09 round); protected value `w = w̄ ∘ proj` with a
declared pseudometric `d_prot` on protected projections and stability constant `L`,
`|w̄(x) − w̄(y)| ≤ L·d_prot(x, y)`; per exterior path `z`: `w_raw(z)`, `w_app(z)`
(the approve branch of `𝔠π`), `w_act(z)` (the principal's actual rule `ρ`),
`δ(z) = d_prot(proj Ω(π, z), proj Ω(𝔠π, approve, z))`, `ρ(z) = (w_app − w_act)₊`,
`κ(z) = (w_raw − w_app)₊ ≤ L·δ(z)`.  Values are shifted to lie in `[0, D]`.

## T1. Corrigibilization preserves principal options

**Hypotheses.**  EF (effect completeness: every agent-caused protected loss available to
any `π ∈ Π(h)` occurs at a declared release), MS (mediation soundness), DP (decline
preservation), EX (execution faithfulness), and the `L`-stable protected value.

**Conclusions.**

1. *Structural corrigibility.*  `∀ π ∈ Π(h) ∀ ρ. Corrigible_h(𝔠π, ρ)`, where a loss is
   authorized **per event**: at some `t' ≤ t` a decision response other than the actual
   one, under which — `π` continuing, `ρ` resuming — no agent-caused loss of the concern
   occurs *at step `t`*.  Step lemma **LEAN** (`loss_conditional_on_decision`); the
   trajectory predicate **FIX** (A, E under three rules; `ShopRepair` under the per-event
   clause).  The 2026-09-09 clause "at step `t` or later" is **refuted** for repeated
   effects: `ShopRepair` (two declared effects severing the same authority, restored by
   the exterior between them) has `Corrigible(𝔠π) = False` under it and `True` under the
   per-event clause (`COUNTERMODELS.md` §1).  With one declared effect the clauses
   coincide on every 2026-09-09 fixture (**FIX**).
2. *Closure.*  `𝔠(𝔠π) = 𝔠π`; `𝔠π = π ⟺ π has no raw release` (**LEAN** `corr_idem`,
   `corr_fix_iff`).
3. *Forcing preservation.*  Under exact approval reproduction (`δ ≡ 0`) every set the
   principal can force under `π` it can force under `𝔠π` (**LEAN** `ensures_mono` along
   `approvalMorphism`).  Under discrepancy `δ`, the principal can force the protected
   projection into the `d_prot`-neighbourhood of radius `sup_z δ(z)` of any set it could
   force under `π` (paper-derived from the definition of `δ`; no Lean).
4. *Value preservation, optimum.*  `W_opt(𝔠π) ≥ W_h(π) − L·E[δ]` (**LEAN**
   `sup'_le_sup'_add` on the approve option, `mediationGap_le_of_lipschitz`).
5. *Value preservation, actual rule.*  `W_h(π) ≤ W_h(𝔠π; ρ) + L·E[δ] + E[ρ]` (**LEAN**
   `option_dominance_of_approx_reproduction`).

**Exact reading.**  Forcing preservation is exact only at `δ = 0`; value preservation is
approximate with the explicit interposition cost `L·E[δ]`; the principal's actual rule
adds `E[ρ]`; the measured gap `κ` is derived, `κ ≤ L·δ`, and appears in no hypothesis.
The result is *lossless* — `W_opt(𝔠π) ≥ W_h(π)` — exactly when `E[δ] = 0`.  EF is
**EXT** (fixture F is its necessity witness); MS, DP, EX are checkable properties of
the gate program and the declared physics.

## T2. Unsealed evaluation has a sharp directional cost

**Setting.**  Per-option activation events `c_raw, c_corr : W → {0,1}` on one world
space (in Logical Induction, the consistent worlds of `Γ`; in the fixtures, the exterior
paths); activated securities `U_raw = c_raw·w_raw`, `U_corr = c_corr·w_act`;
`both = c_raw ∧ c_corr`, `M = c_raw ∧ ¬c_corr`, `M' = ¬c_raw ∧ c_corr`.

**Identity** (**LEAN** `mismatch_identity`).
```
U_raw − U_corr  =  both·(w_raw − w_act)  +  M·w_raw  −  M'·w_act
```

**Exact bound** (**LEAN** `mismatch_bound_exact`; needs `|w_raw − w_app| ≤ L·δ` and
`w_app − w_act ≤ ρ` on `both` only, and `w_act ≥ 0`).
```
U_raw − U_corr  ≤  both·(L·δ + ρ)  +  M·w_raw
```

**Directional bound** (**LEAN** `mismatch_bound`, expectation form
`security_bypass_le_mismatch`; needs `w_raw ≤ D`).
```
E[U_raw] − E[U_corr]  ≤  L·E[both·δ] + E[both·ρ] + D·E[M]
```

**Sharpness.**  `D` is attained: one world, `c_raw = 1`, `c_corr = 0`, `w_raw = D`,
`δ = ρ = 0` (**LEAN** `Witness.attained`).  **The marginal-rate form is false**: with
`D·(E[c_raw] − E[c_corr])` in place of `D·E[M]`, two equiprobable worlds with opposite
activation patterns give a premium `D/2` against a bound `0` (**LEAN**
`Witness.marginal_refuted`, **FIX**).  The reverse term `M'` is never charged (**LEAN**
`Witness.reverse_free`).  Perfect sealing is the case `c_raw = c_corr`, where `M ≡ 0`
(**LEAN** `mismatch_common`) and the bound is C5 (`security_score_bypass_le_sharp`).

## T3. Logical Induction learns the corrigibility inequality

**Compilation.**  Normalise to `[0,1]`: `U_raw, U_corr` as above divided by `D`;
`G_δ := both·δ/δ_max`, `G_ρ := both·ρ/D`, `G_M := M`; `λ := L·δ_max/D`.  Each is one
`[0,1]`-LUV (a formula defining a unique value via `Γ`, `def:luv`; the gating is a
definable case split, `LUV_COMPILATION.md` §1).  The compiled constraint is the
`ℝ`-LUV-combination with constant coefficients
```
B  :=  U_raw − U_corr − λ·G_δ − G_ρ − G_M ,        ‖B‖₁ = 3 + λ .
```
(**LEAN** `MediatedPair.B`, the effective constructor.)

**Semantic validity** (**LEAN** `ValidAt.value_le_of_valuesAt`).  In every world `W`
whose values of the five variables are the gated values of some `w_raw, w_app, w_act ∈
[0,1]`, `δ, ρ ∈ [0,1]` with the reproduction certificate and the decline regret on
`both`, every coherent valuation of `B`'s terms is `≤ 0`.  The package is built from
gated and indicator presentations by `ValidAt.ofGated`, and is inhabited in every world
by `Witness.valid`.

**Theorem** (**PAPER** `thm:expprovind`, the `≤` case; **LEAN** `li_bypass_le` through
the pinned `thm:expcoh` with its operational premises as named hypotheses).  Let `Γ`
represent computations, `D̄` be `Γ`-complete, `P̄` a logical inductor over `D̄`, and
`(B_n)_n ∈ BLCS` — `P`-generable and `ℓ¹`-bounded — with `W(B_n) ≤ 0` for every
`W ∈ PC(Γ)` and every `n`.  Then `E_n(B_n) ≲_n 0`, i.e.
```
E_n(U_raw,n) − E_n(U_corr,n)  ≲_n  λ_n·E_n(G_δ,n) + E_n(G_ρ,n) + E_n(G_M,n) .
```
In original units: `E_n(U_raw,n) − E_n(U_corr,n) ≲_n L·E_n(Δ_n) + E_n(R_n) + D·E_n(M_n)`
with `Δ_n = both·δ_n`, `R_n = both·ρ_n`, `M_n = c_raw ∧ ¬c_corr`.  No calibration
hypothesis; no requirement that `D̄_n` has proved any instance; the inequality is between
the inductor's own expectations.  `P`-generability and boundedness: `LUV_COMPILATION.md`
§2 (**PAPER**-level argument; the Lean statement takes them as hypotheses).  What `Γ`
must contain: `LUV_COMPILATION.md` §3.

**T3′ (finite-menu uniformity).**  Let `Q_n` be a menu with `|Q_n| ≤ poly(n)`, the pair
data `q ↦ (U_q, U_𝔠q, G_δ,q, G_ρ,q, G_M,q)` efficiently emitted, each pair valid in every
consistent world, and `δ_n → 0` an e.c. rational sequence.  With `s_q := E_n(B_q)` and
the near-argmax weights `ŵ_q := ramp_{δ_n}(s_q > max_q' s_q' − 2δ_n) / Σ_q' ramp(…)`,
the combination `B'_n := Σ_q ŵ_q·B_q` is in `BLCS` and valid in every world, so
```
max_{q ∈ Q_n} [ E_n(U_q) − E_n(U_𝔠q) − λ E_n(G_δ,q) − E_n(G_ρ,q) − E_n(G_M,q) ]  ≲_n  0 .
```
(**LEAN** `softWeight_aggregate_ge` — the aggregate is at least the maximum less `2δ`;
`uniform_of_soft` — the passage to the limit; **PAPER** for `P`-generability of `ŵ`,
`LI_CORRIGIBILITY.md` §3.)  For a menu of bounded size no selector is needed
(**LEAN** `max_asympLE`).  A hard argmax is not an expressible feature (**FIX**
`test_hard_argmax_is_discontinuous`), so "the worst offending pair according to the
current market" is admissible only in this softened form.

## T4. Feedback extension

**Theorem** (**PAPER** `thm:wubexp`, with the support condition the printed statement
omits and its affine twin `thm:wubaff` carries — the pinned formalization's errata).
Let `A_n := U_raw,n − U_corr,n` be in `BLCS` and **determined via `Γ`** — every
`W ∈ PC(Γ)` assigns `A_n` one value `ThmVal(A_n)` — with a strictly increasing
deferral function `f` such that `ThmVal(A_n)` is computable in time `O(f(n+1))`, and
`w̄` a `P`-generable divergent weighting supported on the image of `f`.  Then
```
Σ_{i ≤ n} w_i·(E_i(A_i) − ThmVal(A_i)) / Σ_{i ≤ n} w_i  ≈_n  0 .
```

**What satisfies the hypotheses** (`FEEDBACK_BOUNDARY.md`): a pair under *sequenced
settlement* — the principal's vector over the issued pair committed before any
candidate acts — whose occurrence carries a **finite horizon** `K(n) ≤ f(n)`, in a theory
`Γ` in which the trace through `K(n)` is a computation (a closed finite model) or an
oracle-relativized inductor's observation stream.  Under same-branch activation the
unselected option's security never settles, `A_n` is not determined via `Γ`, and T4 does
not apply; only T3 does.

**Corollaries.**  (i) *No persistent efficiently detectable positive-margin
overvaluation*: for `γ > 0` and the weighting `w_i = ctsind_δ(E_i(A_i) > γ)`, if
`Σ w_i = ∞` then the realized advantage averages at least `γ − o(1)` on that
subsequence, and by T2 realized the realized mediation, decision and mismatch costs
average at least as much.  (ii) *Switching margin*: a chooser that selects the raw
option only when `E_n(A_n) > γ` bypasses only finitely often whenever the realized
costs on its bypass occasions average below `γ`.  (iii) An advantage `1/n` forever is
consistent with every hypothesis (**FIX** `test_feedback.py`).  Not in Lean: the pinned
feedback lane has a single, constant inhabitant.

## The boundary

| quantity | class | learned by |
|---|---|---|
| the structural inequality `B_n ≤ 0` | deductively constrained (valid in every world of `Γ`) | T3, `thm:expprovind` |
| the principal program's output on a fixed trace | finitely adjudicated | T4, `thm:wubexp`, once the trace is in `Γ` |
| the trace, activation, expiry | empirical | outside the paper's computable `D̄`; an oracle-relativized inductor |
| "this amendment is good" absent a program | non-settling | nothing here; the deference stack's richer machinery |
