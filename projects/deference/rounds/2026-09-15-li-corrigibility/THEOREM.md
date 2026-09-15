# The theorem spine: T1–T4

Labels: **LEAN** (sorry-free declaration in `lean/Workspace/Deference/Contrib/`;
`LICorrigibility.lean`, `LICorrigibilityCertificate.lean`, `Corrigibilization.lean`, or,
where named, `MediatedRepairDominance.lean`; each audits to the three allowed axioms),
**FIX** (exact fixture in `tests/`), **PAPER** (a theorem of arXiv:1609.03543 v5 used at
its exact statement, cited by label), **EXT** (a contract the theory does not pay),
**OPEN**.  Names are provisional (`AGENTS.md` standard 6).

Throughout: a finite two-stage interaction at history `h`; `Π(h)` the agent's
continuation space; declared protected effects; `𝔠` the corrigibilization transform;
protected value `w = w̄ ∘ proj` with a declared pseudometric `d_prot` on protected
projections and stability constant `L`, `|w̄(x) − w̄(y)| ≤ L·d_prot(x, y)`; per exterior
path `z`: `w_raw(z)`, `w_app(z)` (the approve branch of `𝔠π`), `w_act(z)` (the
principal's actual rule `ρ`), `δ(z) = d_prot(proj Ω(π, z), proj Ω(𝔠π, approve, z))`,
`ρ(z) = (w_app − w_act)₊`, `κ(z) = (w_raw − w_app)₊ ≤ L·δ(z)`.  Values are shifted to lie
in `[0, D]`.  The soft-selector width of T3′ is `τ_n`; `δ` is only ever the mediation
discrepancy.

## T1. Corrigibilization preserves principal options

**The interaction** (**LEAN** `Corrigibilization.Interaction`).  Physical states, declared
effects with their semantics `exec` (execution faithfulness: `exec` is the physics), task
moves, exterior moves, concerns with immediate response semantics `φ`, corrections.  The
mediated state carries `pending`, `latch`, `refused`.  Mediation soundness and decline
preservation hold by construction of the response stage: a gated release fires only on a
latch, the latch is set only by an approval of a pending proposal, and a decision changes
nothing but the bookkeeping.  **Response authority** `K r s` — some response realizes
`φ r` now — depends on the physical state only (`K_iff_exists_response`).  An
**agent-caused loss** at step `t` is `K` failing after the agent's move and holding after
the idle move; the principal's own stop and the exterior's stage are not losses
(`no_loss_of_idle`).

**Event-linked authorization** (**LEAN** `Authorized`).  A loss at step `t` is authorized
when the agent's move at `t` is the gated release of an effect `e` whose latch was set by
the principal's approval of `e`'s proposal at an earlier step `t'`, and the decline
alternative at `t'` — the policy continuing, the rule resuming — has no agent-caused
loss of the concern at step `t`.  Each loss event is tied to the decision that enabled
its effect; an unrelated earlier decision that happens to avoid the loss does not count;
repeated effects are handled independently; an approved irreversible successor is
authorized (its release is a gated release after an approval).  The 2026-09-09 clause
"no loss at step `t` **or later**" is **refuted** for repeated effects (`ShopRepair`,
`COUNTERMODELS.md` §1); the per-event clause of the first pass and the event-linked clause
agree on every single-effect fixture and on `ShopRepair`, and the event-linked one is the
canonical form (`DECISIONS.md`, 2026-09-15).

**Hypotheses.**  Effect completeness (**LEAN** `EffectComplete`: a task move never removes
response authority, so every agent-caused loss is at a declared release; **EXT** for a
real interface, fixture F its necessity witness); the `L`-stable protected value for the
value clauses.

**Conclusions.**

1. *Structural corrigibility* (**LEAN** `corrigible_corrPolicy`).  Under effect
   completeness, for every policy `π`, every principal rule `ρ` that does not correct at
   the authorizing step, every initial state with a clear latch and every exterior path,
   every agent-caused loss along `𝔠π` is event-authorized: `∀ π ρ, Corrigible (𝔠π) ρ`.
   Inhabited: `Witness.corrigible_instance` on a two-state physics (a wire, a cut, a stop
   through the wire), with `Witness.raw_cut_loses` the raw loss it authorizes.  The
   2026-09-09 step lemma `loss_conditional_on_decision` is the one step of this proof.
2. *Closure* (**LEAN** `corrPolicy_idem`, `corrPolicy_no_raw`; on move sequences
   `corr_idem`, `corr_fix_iff`).  `𝔠(𝔠π) = 𝔠π`; `𝔠π` emits no raw release.
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
approximate with the explicit interposition cost `L·E[δ]`; the actual rule adds `E[ρ]`;
`κ` is derived, `κ ≤ L·δ`, and appears in no hypothesis.  The result is *lossless* —
`W_opt(𝔠π) ≥ W_h(π)` — exactly when `E[δ] = 0`.

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

**Sharpness.**  `D` is attained (**LEAN** `Witness.attained`).  **The marginal-rate form
is false**: with `D·(E[c_raw] − E[c_corr])` in place of `D·E[M]`, two equiprobable worlds
with opposite activation patterns give a premium `D/2` against a bound `0` (**LEAN**
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
B  :=  U_raw − U_corr − λ·G_δ − G_ρ − G_M ,        ‖B‖₁ = 4 + |λ| .
```
(**LEAN** `MediatedPair.B`; the compiler from activation sentences and base evaluation
variables is `MediatedPair.compile`.)

**Semantic validity** (**LEAN** `ValidAt.value_le_of_valuesAt`).  In every world `W`
whose values of the five variables are the gated values of some `w_raw, w_app, w_act ∈
[0,1]`, `δ, ρ ∈ [0,1]` with the reproduction certificate and the decline regret on
`both`, every coherent valuation of `B`'s terms is `≤ 0`.  The package is built from
gated and indicator presentations by `ValidAt.ofGated` / `MediatedPair.compile_validAt`,
and is inhabited in every world by `Witness.valid`.

**The generability certificate** (**LEAN** `MediatedPair.syntaxOf`).  The pinned
library derives its whole operational package — `PolySequence`, the mesh-softmax
operational witness, the threshold codes — from one syntactic certificate,
`LUVCombinationSyntax`.  The round constructs it for `(B_n)` from: an e.c. code of
`−λ_n`, and threshold emission of the five component families; and those follow from the
emission of the two activation sentence families and the four base evaluation families
(`gate_thresholdCodeSeq`, `indicator_thresholdCodeSeq`, `rpnSentenceCodes_imp` for the
negation in `M`).  `MediatedPair.boundedSequence` is the `def:blcp` object with the bound
`4 + Λ`.

**Theorem** (**PAPER** `thm:expprovind`, the `≤` case; **LEAN** `li_bypass_le_compiled`
through the pinned `expcoh_ofSyntax`).  Let `Γ` represent computations, `D̄` be
`Γ`-complete with a consistent world at every stage, `P̄` a logical inductor over `D̄`;
let `(φraw_n)`, `(φcorr_n)` be efficiently emitted activation sentence families and
`(X_raw,n)`, `(X_act,n)`, `(X_δ,n)`, `(X_ρ,n)` efficiently emitted `[0,1]`-LUV families;
let `λ_n` be an e.c. rational sequence with `|λ_n| ≤ Λ`; and let the compiled pair be
valid in every `W ∈ PC(Γ)` at every `n`.  Then
```
E_n(U_raw,n) − E_n(U_corr,n)  ≲_n  λ_n·E_n(G_δ,n) + E_n(G_ρ,n) + E_n(G_M,n) ,
```
in original units `E_n(U_raw,n) − E_n(U_corr,n) ≲_n L·E_n(Δ_n) + E_n(R_n) + D·E_n(M_n)`
with `Δ_n = both·δ_n`, `R_n = both·ρ_n`, `M_n = c_raw ∧ ¬c_corr`.  No calibration
hypothesis; no requirement that `D̄_n` has proved any instance; the inequality is between
the inductor's own expectations.  The theorem's hypotheses are the realization's inputs
and nothing else; `Witness.li_instance` discharges every one of them but the stage
consistency of `D̄` on a constant two-atom family.  What `Γ` must contain:
`LUV_COMPILATION.md` §3.

**T3′ (uniformity over polynomial-size efficiently generated menus).**  Let `Q_n` be a
menu of size `|Q_n| ≤ poly(n)` whose pair data `q ↦ (U_q, U_𝔠q, G_δ,q, G_ρ,q, G_M,q)` is
efficiently emitted, each pair valid in every consistent world, and `τ_n → 0` an e.c.
rational sequence.  With `s_q := E_n(B_q)` and the near-argmax weights
`ŵ_q := ramp_{τ_n}(s_q > max_q' s_q' − 2τ_n) / Σ_q' ramp(…)`, the combination
`B'_n := Σ_q ŵ_q·B_q` is in `BLCS` and valid in every world, so
```
max_{q ∈ Q_n} [ E_n(U_q) − E_n(U_𝔠q) − λ E_n(G_δ,q) − E_n(G_ρ,q) − E_n(G_M,q) ]  ≲_n  0 .
```
(**LEAN** `softWeight_aggregate_ge` — the aggregate is at least the maximum less `2τ`;
`uniform_of_soft` — the passage to the limit; **PAPER** for `P`-generability of `ŵ`,
`LI_CORRIGIBILITY.md` §3.)  For a menu of bounded size no selector is needed (**LEAN**
`max_asympLE`).  A hard argmax is not an expressible feature (**FIX**
`test_hard_argmax_is_discontinuous`), so "the worst offending pair according to the
current market" is admissible only in this softened form.  **Residual**: the pinned-
interface certificate for `(B'_n)` — the serialization of the growing `max`/reciprocal
chains of `ŵ` — is not constructed; the pinned splice suite exposes variable-width folds
for token concatenation only (`LUV_COMPILATION.md` §4).  The menu is polynomial-size and
efficiently generated; nothing is claimed about all efficiently enumerable continuations.

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
feedback lane has a single, constant inhabitant.  T4 is a boundary statement, not the
centrepiece.

## The boundary

| quantity | class | learned by |
|---|---|---|
| the structural inequality `B_n ≤ 0` | deductively constrained (valid in every world of `Γ`) | T3, `thm:expprovind` |
| the principal program's output on a fixed trace | finitely adjudicated | T4, `thm:wubexp`, once the trace is in `Γ` |
| the trace, activation, expiry | empirical | outside the paper's computable `D̄`; an oracle-relativized inductor (item 91) |
| "this amendment is good" absent a program | non-settling | nothing here; the deference stack's richer machinery |
