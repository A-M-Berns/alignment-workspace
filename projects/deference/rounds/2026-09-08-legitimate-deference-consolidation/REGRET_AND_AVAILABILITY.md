# Regret and availability

**Status:** `ci-only`.  Lean: `lean/Workspace/Deference/Contrib/PartialActivatedValue.lean`
(the #93 module, corrected and extended here).  Fixtures: `tests/test_countermodels.py`
(`TestA`, `TestB`, `TestC`, `TestAuthoritative`).

## 1. Setting

Finite worlds `W` with credence `π ≥ 0`; a common activation `c : W → Bool`; a partial
evaluation `Ṽ : (w) → c w = true → Q → ℚ` on a finite nonempty menu; completions `V̄`
agreeing with `Ṽ` on certified worlds with values in `[L, L + D]`; a followed strategy
`α : W → Q → ℚ`, a world-dependent probability vector.  Regret is against the best
**fixed** candidate: `max` outside `𝔼`.  Regret is **not** assumed nonnegative — a
world-dependent strategy may beat every fixed comparator.

## 2. The correction

The reason-mediated-authorship round claimed `R_V̄ ∈ [R_U, R_U + D·η]` for every
completion.  **False.**  `SharpLower.attained` (**LEAN**; fixture **B**): two worlds of
mass `½`; on the certified world candidate `0` is worth `1` and `1` worth `0`; the
completion reverses them on the void world; the strategy follows `0` on the certified
world and `1` on the void one.  `R_U = 0`, `R_V̄ = −½ = R_U − D·η`.  The void branch lets
the strategy beat both fixed candidates.

The old fixture happened to use a world-independent strategy, for which the one-sided
statement is true; the general statement is:

**Completion theorem** (`regretV_sub_regretU_abs_le`, **LEAN**).  Under `π ≥ 0`, `α` a
probability vector on every world, values in `[L, L + D]`, finite nonempty `Q`:

```
|R_V̄(α) − R_U(α)| ≤ D · voidMass ,        voidMass := 𝔼[1 − c] .
```

Proof shape: every candidate's excess `𝔼[V̄_a] − 𝔼[U_a]` and the strategy's excess both
lie in `[L·v, (L+D)·v]` (`excess_bounds`, `followed_excess_bounds`); a `sup'` shifted by
increments in that interval moves by an amount in it (`sup'_add_bounds`); the difference
of two numbers in `[L·v, (L+D)·v]` is in `[−D·v, D·v]`.

**Sharpness.**  Upper: PR #92's `Sharp.transfer_sharp` (`R_V̄ = R_U + D·η`, world-independent
strategy).  Lower: `SharpLower.attained`.  Both constants are exactly `D`.

**Corollary** (`availability_transfer_completion`, the one-sided upper bound, kept):
`R_U ≤ ε`, void mass `≤ η` ⇒ `R_V̄ ≤ ε + D·η`.  It has no fewer hypotheses than the
two-sided theorem (the strategy must be a probability vector for the lower excess
bound, which the upper bound also uses through the strategy's excess).

**The lesson.**  Completions are not authoritative.  Changing the arbitrary void-world
completion moves fixed-menu regret by at most `D·η` in either direction; the
authoritative quantity is `R_auth`.

## 3. The primary theorem

**Identity** (`regretU_eq_mass_mul_regretAuth`, **LEAN**): with `p = 𝔼[c] > 0`,
`R_U(α) = p · R_auth(α)`, and `R_auth` is defined from `Ṽ` alone (`condExpectPartial`).

**Authoritative regret** (`regretAuth_le_div`, **LEAN**).  With `Σπ = 1`, `R_U ≤ ε`,
`0 ≤ ε`, void mass `≤ η < 1`:

```
1 − η ≤ p        and        R_auth(α) ≤ ε / (1 − η) .
```

The hypothesis `0 ≤ ε` matters: with `ε < 0` the direction `ε/p ≤ ε/(1−η)` reverses.
Since `R_U ≤ max(R_U, 0)` always, the bound with `ε := max(R_U, 0)` is unconditional
(fixture sweep, `TestAuthoritative`).

**Asymptotic form** (`regretAuth_asymptotic`, **LEAN**): over real sequences, if
`R_U,n = p_n · R_auth,n`, `1 − η_n ≤ p_n`, `η_n → 0`, and `R_U ≲ₙ 0`, then
`R_auth ≲ₙ 0`.  The positivity needed is eventual: `η_n < ½` eventually gives
`p_n ≥ ½`.

## 4. What the three quantities mean

| quantity | reads | meaning |
|---|---|---|
| `R_auth` | `Ṽ` on certified worlds | worse than the best fixed candidate *by the actual authoritative future principal, where that principal's evaluation has authority* — **the deference target** |
| `R_U` | `Ṽ` (completion-invariant) | the same, scaled by the probability that authority obtains; what Value bounds |
| `R_V̄` | a completion | the same plus an arbitrary story on void worlds; a robustness lemma, not a target |

"Objectively good" is none of these and is not claimed.

## 5. What is not established

- Any rate for `η_n`; that `η_n → 0` for any realized ecosystem (OPEN; item 87).
- The tower on activated LUVs (PAPER, conditional).
- A per-candidate-activation analogue of the identity (there is none; common activation
  is what makes `R_U = p·R_auth` an identity).
