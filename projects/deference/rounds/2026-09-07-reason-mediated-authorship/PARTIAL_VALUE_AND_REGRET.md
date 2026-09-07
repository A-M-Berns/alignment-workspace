# Partial evaluations and the three regrets

**Status:** `ci-only`.  Lean: `lean/Workspace/Deference/Contrib/PartialActivatedValue.lean`.
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

**The interval is exact.**  `regret_constant_completion` (**LEAN**): a completion constant
across candidates on void worlds has `R_V̄ = R_U`.  The previous round's
`Sharp.transfer_sharp` is a completion attaining `R_V̄ = R_U + D·η` with `D = 1`.  So over
all completions

```
R_V̄(α) ∈ [R_U(α), R_U(α) + D·η]
```

and both ends are attained (fixture **I**, **FIX**, sweeps the grid).  The sharpness
example of the previous round is unchanged: its void-world payoffs were a completion
choice, and the bound is tight as a statement over completions.  The constant is `D`,
not `2D`.

**What this says.**  Failed-evaluation worlds contribute a bounded uncertainty mass
`D·η` to any total regret one might write down, and nothing else.  No completion is
privileged; no reference evaluator is smuggled in through the void branch.  The
authoritative quantity is `R_auth`, which is defined without one.

## 4. Selective failure, again (fixture K)

`C = 0` exactly on the worlds where the principal would disagree with the advisor.
`R_U = 0`; the anti-selection completion attains `R_V̄ = R_U + η`; every other
completion on the grid is at most that.  The transfer is a pure identity in one common
event and assumes nothing about how `C` correlates with anything.

## 5. Perturbation

`regretU_perturb` (**LEAN**): if `|V_a(w) − V'_a(w)| ≤ δ` on certified worlds then
`R_U(V) ≤ R_U(V') + 2·δ·mass`.  `AUTHORSHIP.md` §5 reads it as the quantitative-authorship
interaction.

## 6. What is not established

- Any rate for `η`; any claim about which completion an application "should" use (none).
- A conditional form for a *per-candidate* activation: the identity `R_U = p·R_auth`
  is specific to a common `C`.
