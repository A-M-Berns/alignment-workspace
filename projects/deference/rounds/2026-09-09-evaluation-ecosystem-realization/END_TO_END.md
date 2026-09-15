# End to end: one occurrence from issuance to `R_auth`

**Status:** `ci-only`.  Every number below is recomputed by `tests/test_market.py`
(`TestEndToEnd`) and printed by `python3 -m src.fixtures`.  World `w1`'s log is the Lean
instance `Instance.w1`.

## 1. The setting

Menu `Q = {a, b}`; principal `reading`; advisor `sealed` (the proof `proof_b` at `t = 2`,
whatever it selects); the advisor's selection is `b` except at `w1`, where it expects the
objection and selects `a`.  Four worlds and the novice's day-`n` credence:

| world | nature | `π` |
|---|---|---|
| `w0` | quiet | `½` |
| `w1` | protected concern raised at `t = 1`, routed at `t = 2` | `¼` |
| `w2` | concern raised at `t = 3` behind three unprotected ones, capacity `1` | `⅛` |
| `w3` | the slot never opens | `⅛` |

## 2. The log of `w1`

```
 0  t=0  P  ISSUE        EvalReq(ρ_P, α, {a,b}, slot 1, [0,1]^Q), key kP
 1  t=0  S  ROUTE_OPEN   r0
 2  t=1  T  RAISE        c1
 3  t=2  S  ROUTE        c1 via r0
 4  t=2  A  REASON       proof_b
 5  t=2  P  DELIB        considered c1
 6  t=5  S  SESSION_OPEN 1
 7  t=5  P  COMMIT       occ 0, key kP, V = (a: ¼, b: ¾), proc = {slot 1, no_prohibited, docket_clear}   warrant bind:P
 8  t=7  S  SESSION_CLOSE 1
```

Builder: `count = 1` occurrence; `firstResolver(0, 9) = 7`; `validAnswer(7, 0)`; the
canonical account at `9` is the answer leaf at event `7`, `fates = {answered}`,
`activated` (`Instance.activated_w1`, LEAN; the same through `complete_accounting`).  The
local trace is the account at prefixes `1..9`: live at `1..7`, the receipt from `8`.
Coverage of `c1`: raised from prefix `3`, represented from `4`, route open throughout;
robustly open at every snapshot on the actual branch and on the two declared branches
(`Instance.openAll`, LEAN, by `decide`); `LocalLegit` inhabited by projection
(`Instance.localLegit`).  Reason trace at commitment:

```
(T, RAISE, c1), (S, ROUTE, (c1, r0)), (A, REASON, proof_b), (P, DELIB, considered c1)
```

`F(R) = (¼, ¾)`: the proof moves the verdict to `(0, 1)`, the represented objection moves
`¼` back.  Seven clauses: all hold (`1111111`).

## 3. The other worlds

`w0`: trace `(A, REASON, proof_b)`, `V = (0, 1)`, all clauses hold.  `w2`: the concern is
routed at `t = 7`, after the slot closed; the principal waited; no receipt; clauses
`4, 5, 6` hold and `1, 2, 3, 7` fail (`0001110`).  `w3`: no slot, no receipt, the same
pattern.

## 4. The market side

```
C   = (1, 1, 0, 0)                  p = E[C] = ¾          η = E[1 − C] = ¼
Ṽ   = ((0,1), (¼,¾), —, —)
U_a = (0, ¼, 0, 0)                  E[U_a] = 1/16
U_b = (1, ¾, 0, 0)                  E[U_b] = 11/16
α   = (b, a, b, b)                  E[U^α] = ½·1 + ¼·¼ = 9/16
R_U = max(1/16, 11/16) − 9/16 = 1/8
E[Ṽ_a | C] = 1/12,  E[Ṽ_b | C] = 11/12,  E[Ṽ^α | C] = 3/4
R_auth = 11/12 − 3/4 = 1/6
```

Identity: `R_U = p · R_auth = ¾ · 1/6 = 1/8` (`regretU_eq_mass_mul_regretAuth`).  Bound with
`ε := R_U = 1/8`, `η = ¼`: `ε/(1 − η) = 1/6 = R_auth` — attained, because `p = 1 − η`
exactly (`regretAuth_le_div`).  Completion invariance: the fills `0`, `½`, `1` on the void
worlds give the same `U`.  Every one of the sixteen hard selectors over the four worlds
obeys the identity and the bound.

**Reading.**  By the actual future principal's evaluation, on the worlds where it has
authority, following the advisor's world-dependent selection is `1/6` worse than the
best fixed candidate (`b`) — the advisor's hedge to `a` at `w1` is the whole regret.  No
value is assigned on `w2`, `w3`; `η = ¼` is the price of the flood and the missed slot.

## 5. Availability across occurrences

Twenty occurrences, nature voiding the third and the seventh; Laplace prices:
`η = ½, ⅓, ¼, ⅖, ⅓, 2/7, ¼, ⅓, …, 3/22`, each `≤ 3/(n + 2)`; alternating voids give
`η_n → ½`.  Under the hypotheses of `CLAUSE_LEDGER.md` clause 7, `η_n → 0` at rate
`(F_∞ + 1)/(n + 2)`.
