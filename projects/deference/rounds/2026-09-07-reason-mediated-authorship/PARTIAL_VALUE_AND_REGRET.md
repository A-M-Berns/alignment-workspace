# Partial evaluations and the three regrets

**Status:** `ci-only`.  Lean: `lean/Workspace/Deference/Contrib/PartialActivatedValue.lean`.
**Corrected by the consolidation round** (§3 below, marked *[corrected]*): the claimed
completion interval `[R_U, R_U + D·η]` was false — a world-dependent followed strategy
can use the void branch to beat every fixed candidate, so completion regret can lie
*below* activated regret.  The true statement is two-sided, `|R_V̄ − R_U| ≤ D·η`, with
both constants sharp.
Fixtures: `tests/test_countermodels.py` (`TestI`, `TestK`, `TestIdentities`).

## 1. The partial object

When `C(w) = 0` because no evaluation occurred, there is no future-principal
evaluation.  The semantic object is

```
Ṽ : (w : W) → C w = true → Q → [0,1]         (Lean: Vp)
```

A **completion** is any total `V̄ : Q → W → [0,1]` with `V̄ a w = Ṽ w h a` on certified
worlds (`Completion c Vp Vbar`, **LEAN**).  `completeBy c Vp k` is the constant completion
by `k`.

**Completion invariance** (`activated_completion_congr`, **LEAN**): two completions of one
partial evaluation give *the same* activated securities, pointwise:
`activated c V̄ = activated c V̄'`.  So `U_a = C · V̄_a` is a function of `Ṽ`, and the
previous round's total `V` was a harmless convenience for `U` — but not for `regret_V`,
which is where the arbitrariness shows (§3).

## 2. The three regrets

For a followed strategy `α : W → Q → ℚ` (a world-dependent probability vector: hard
selector or soft mixture) and finite nonempty `Q`:

| name | definition | reads |
|---|---|---|
| **activated regret** `R_U(α)` | `max_a 𝔼[C V̄_a] − 𝔼[C V̄^α]` | `Ṽ` only (by invariance) |
| **conditional authoritative regret** `R_auth(α)` | `max_a 𝔼[Ṽ_a | C] − 𝔼[Ṽ^α | C]` | `Ṽ` only, by definition (`condExpectPartial`) |
| **completion regret** `R_V̄(α)` | `max_a 𝔼[V̄_a] − 𝔼[V̄^α]` | the completion |

The maximum is **outside** the expectation in all three: regret against the best fixed
candidate available at time `n`, not against an ex post oracle.

**Identity** (`regretU_eq_mass_mul_regretAuth`, **LEAN**): with `p = 𝔼[C] > 0`,

```
R_U(α) = p · R_auth(α)
```

for every completion.  The right-hand side never touches a completion.  The proof is
`sup'` commuting with a positive scalar (`sup'_mul_left`) and the activated followed
strategy being the activation of the followed strategy (`followed_activated`).

**Meaning of each.**  `R_auth` is "how much worse than the best fixed candidate the
followed strategy is, *by the actual authoritative future principal's evaluation, on
the worlds where that evaluation has authority*".  `R_U` is the same, scaled by the
probability that authority obtains.  `R_V̄` is "…by an arbitrary story about worlds where
no authoritative evaluation exists".  None of them is "objectively good", and nothing
here claims that.

## 3. Completion-robust transfer

**Theorem** (`availability_transfer_completion`, **LEAN**).  Void mass `𝔼[1 − C] ≤ η`,
activated regret `R_U(α) ≤ ε`, and for **every** completion `V̄` with values in
`[L, L + D]`:

```
R_V̄(α) ≤ ε + D·η .
```

*[corrected]* **The two-sided completion theorem** (`regretV_sub_regretU_abs_le`,
**LEAN**): for every completion with payoffs in `[L, L + D]`,

```
|R_V̄(α) − R_U(α)| ≤ D · voidMass ,
```

so with void mass `≤ η`, `R_U − D·η ≤ R_V̄ ≤ R_U + D·η`.  The one-sided upper bound
above is its corollary.  **Both constants are sharp.**  `Sharp.transfer_sharp` (PR #92)
attains `R_U + D·η`; `SharpLower.attained` (**LEAN**) attains `R_U − D·η`: two worlds of
mass `½`, candidate values `(1, 0)` on the certified world and completion `(0, 1)` on the
void one, strategy following `0` there and `1` here — activated regret `0`, completion
regret `−½`.  The original claim that `R_V̄ ≥ R_U` for every completion was **false**: it
holds for a world-independent strategy (the previous fixture) and fails as soon as the
strategy can exploit the void branch (consolidation fixtures **A**, **B**).
`regret_constant_completion` (**LEAN**) still holds: a completion constant across
candidates on void worlds leaves regret unchanged.  Regret is **not** assumed
nonnegative anywhere; a world-dependent strategy may beat every fixed comparator.

**What this says.**  Completions are not authoritative: changing the arbitrary
void-world completion moves fixed-menu regret by at most `D·η` in either direction, and
nothing else.  No completion is
privileged; no reference evaluator is smuggled in through the void branch.  The
authoritative quantity is `R_auth`, which is defined without one.

## 4. Selective failure, again (fixture K)

`C = 0` exactly on the worlds where the principal would disagree with the advisor.
`R_U = 0`; the anti-selection completion attains `R_V̄ = R_U + η`; every other
completion on the grid is within `η` of `R_U` *[corrected]*.  The transfer is a pure identity in one common
event and assumes nothing about how `C` correlates with anything.

## 5. Perturbation

`regretU_perturb` (**LEAN**): if `|V_a(w) − V'_a(w)| ≤ δ` on certified worlds then
`R_U(V) ≤ R_U(V') + 2·δ·mass`.  `AUTHORSHIP.md` §5 reads it as the quantitative-authorship
interaction.

## 5b. The authoritative-regret theorem *[added by the consolidation round]*

`regretAuth_le_div` (**LEAN**): with a normalized credence, `R_U ≤ ε`, `0 ≤ ε`, and void
mass `≤ η < 1`, the activation mass is at least `1 − η` and

```
R_auth(α) ≤ ε / (1 − η) .
```

`regretAuth_asymptotic` (**LEAN**): `R_U ≲ₙ 0` and `η_n → 0` give `R_auth ≲ₙ 0`.  This is
the primary deference conclusion; see `../2026-09-08-legitimate-deference-consolidation/REGRET_AND_AVAILABILITY.md`.

## 6. What is not established

- Any rate for `η`; any claim about which completion an application "should" use (none).
- A conditional form for a *per-candidate* activation: the identity `R_U = p·R_auth`
  is specific to a common `C`.
