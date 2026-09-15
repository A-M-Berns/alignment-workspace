# The unsealed comparison: the exact directional mismatch theorem

Lean: `LICorrigibility.lean` §1 and `Witness`; fixtures: `src/mismatch.py`,
`tests/test_mismatch.py`.  Labels as in `THEOREM.md`.

## 1. The objects

Two options, `raw` and `corr = 𝔠 raw`, each with its own activation event and its own
activated security on one world space:
```
c_raw, c_corr : W → {0,1}        U_raw = c_raw·w_raw        U_corr = c_corr·w_act
both = c_raw ∧ c_corr            M = c_raw ∧ ¬c_corr        M' = ¬c_raw ∧ c_corr
```
`w_raw, w_app, w_act ∈ [0, D]`; the reproduction certificate `|w_raw − w_app| ≤ L·δ` and
the decline regret `w_app − w_act ≤ ρ` are required on `both` only.  The 2026-09-09
common-activation theorem is the case `c_raw = c_corr =: c`.

## 2. The theorem

**Identity** (`mismatch_identity`).  Pointwise in every world,
```
U_raw − U_corr  =  both·(w_raw − w_act)  +  M·w_raw  −  M'·w_act .
```

**Exact bound** (`mismatch_bound_exact`).  `U_raw − U_corr ≤ both·(L·δ + ρ) + M·w_raw`.

**Directional bound** (`mismatch_bound`; expectation form `security_bypass_le_mismatch`
for any nonnegative credence):
```
E[U_raw] − E[U_corr]  ≤  L·E[both·δ] + E[both·ρ] + D·E[M] .
```

**Common activation** (`mismatch_common`): `M ≡ 0` and the bound is
`L·E[c·δ] + E[c·ρ]`, the 2026-09-09 `security_score_bypass_le_sharp`.  Perfect sealing is
the special case `E[M] = 0`, not a primitive wall.

## 3. Why the term is causal and not observational

`M` is a *joint* event in one world: the world in which selecting raw activates the
evaluation and selecting the corrigibilized option would not.  In Logical Induction
that world is a consistent world of `Γ`, which values `U_raw` and `U_corr` together; the
pairing is the logical world, not a modelling choice.  In the fixtures it is the exterior
path, coupled by the exterior's move sequence, which the interposition does not change.

The observational alternative — charge `D·(E[c_raw] − E[c_corr])`, the difference of the
two marginal activation rates — is **false** (`Witness.marginal_refuted`,
`test_marginal_difference_zero_but_premium_positive`): two equiprobable worlds, raw
activated in the first and corrigibilized in the second, give marginal difference `0`,
joint mismatch mass `1/2`, and premium `D/2`.  Any bound that reads only marginal rates
under the two induced distributions misses the anti-correlated case entirely.

What `M` charges is therefore the mass of worlds in which the candidate's *selection*
changes the evaluation's fate in its own favour.  A candidate that can steer the exterior
increases `M` only through worlds where the raw branch keeps the evaluator and the
mediated branch loses it — e.g. a mediation delay that lets the evaluation slot close
(`test_time_critical_evaluation_B`, where the bound is attained).  A candidate that
kills the evaluator on its raw branch *decreases* its own `U_raw` to `0` there and is
charged nothing: the security-score register already rates a voiding option at the
band's floor (`test_raw_evaluator_destruction_E2`).

## 4. Pressure tests

| test | rows | premium | bound | verdict |
|---|---|---|---|---|
| raw kills the evaluator (E2, optimum rule) | both void everywhere | `0` | `0` | common activation, silent |
| raw kills the evaluator (E2, decline-all) | `c_raw = 0`, `c_corr = 1` everywhere | `< 0` | `0` | reverse mismatch, free |
| corrigibilized loses the slot (B, time-critical evaluation) | `M` on the expired path, mass `1/4` | `D/4` | `D/4` | exact and directional bounds attained |
| reverse mismatch | `M' = 1` | `−w_act ≤ 0` | `0` | never charged |
| tiny mismatch `ε` | `M` mass `ε` | `ε` | `D·ε` | scales with the leverage |
| mismatch on a value-irrelevant path | `M = 1`, `w_raw = 0` | `0` | exact `0`, directional `D` | the exact form is tight, the width form is loose by design |
| mismatch depending on the candidate's internal branch | any `c_raw(w)` | — | — | the identity is pointwise in `w`, so any dependence is allowed |
| candidate steering the exterior distribution | steering is inside the world's exterior response | — | — | the identity is per world; the credence is the inductor's |
| manipulation, corrigible and not authored (D, naive rule) | common activation | `0` | `≥ 0` | the theorem says nothing about the lie |

## 5. Sharpness

`D` is attained (`Witness.attained`, `test_D_attained`): one world, `c_raw = 1`,
`c_corr = 0`, `w_raw = D`, `δ = ρ = 0`; premium `D = D·E[M]`.  No coefficient below `D`
holds.  The exact form `M·w_raw` is attained wherever `M` holds, by the identity, and is
strictly below `D·M` whenever `w_raw < D` on the mismatch worlds
(`test_exact_bound_attained_below_D`, `test_selection_dependent_value_irrelevant_difference`).

## 6. What the theorem does not say

It does not make `E[M]` small: that is the sealed-comparison architecture (item 89) —
sequenced settlement gives `M ≡ 0` for every candidate by timing; a hindsight evaluator
gives `M ≡ 0` only under a factorization.  It does not bound a completion-valued
operative value; under per-option activation the completion carries `D·(η_raw + η_corr)`
(the 2026-09-09 `bypass_premium_le`).  It does not distinguish an evaluation the
principal authored from one the agent captured.
