# Exact conditions on a price history — statements of record and assumption ledgers

Every named object is a declaration in the namespace
`Workspace.Normativity.Contrib.ExactConditions`, in `ExactConditions.lean`,
`ExactConditionsReserve.lean` or `ExactConditionsFloor.lean` under
`lean/Workspace/Normativity/Contrib/`. Rerun: `~/.claude/scripts/safe-lake.sh build Workspace`
from `lean/`, then `python3 tests/audit_axioms.py`. Each module ends with its `#print axioms`
list; every result audits to `[propext, Classical.choice, Quot.sound]`.

Days are indexed from `0`. `L` is an `AssessmentProcess.Assessment`; a world is a `PCWorld`
and `W` also denotes its payout vector.

## 0. The objects (`ExactConditions`)

**Bet.** `Bet` is a list of `(coefficient, sentence)` terms with rational coefficients and a
rational constant; `g.eval x = Σ a·x(φ) + b`. `Bet.floor φ c` is `x(φ) − c`.

**Condition.** `Condition` gives each day `n` a number `count n` and bets `bet n j`, `j < count n`.
`C.Holds n x`: every day-`n` bet is nonnegative at `x`. `C.Region n x`: `x` is in the cube and
`C.Holds n x`. For weights `w : ℕ → ℕ → ℝ`, `C.stake w n x = Σ_j w n j · (bet n j).eval x` and
**the account** `C.account w N x = Σ_{n ≤ N} C.stake w n x`.

**The interface** (A0). `DualCertifiedMarket` carries: `L`; a history `P` with exact rational
quotes and values in `[0,1]`; a condition `C`; multipliers `mu ≥ 0`; `mem : ∀ n, C.Holds n (P n)`;
tolerances `eps n > 0` whose partial sums are at most `epsTotal`; and the **day inequality**

    ∀ n w, (∀ φ, 0 ≤ w φ ≤ 1) →
      ((tradingFirmTrader L quote).strat n).value P w + C.stake mu n w ≤ eps n.

`U = 2 + epsTotal`. The realized firm is `AssessmentFirm.tradingFirmTrader L quote`, the firm
whose floor and dominance theorems are stated for an arbitrary history.

## 1. Ceiling and preservation (A1, A2)

**Theorem** (`DualCertifiedMarket.account_le`). For every `N` and every world live at `N`,
`M.C.account M.mu N W ≤ M.U`.

**Theorem** (`DualCertifiedMarket.no_efficient_trader_exploits`, registered
`exact.account-preserves-criterion`). If `M.AccountBounded B` — `−B ≤ M.C.account M.mu N W` for
every `N` and every world live at `N` — then no efficiently computable trader exploits `M.P`
relative to `M.L`.

Beside it: `isLogicalInductor` (the same with `ComputableMarket M.P` as a further hypothesis,
concluding `M.L.IsLogicalInductor M.P`); `account_unbounded_of_exploit` (if an efficiently
computable trader exploits, then for every `B` some world live at some `N` has account below
`−B`); `budgeted_netWorth_le` (for the firm's component of enumeration index `j` and budget
`r + 1`, weight times its net worth at a live world is at most `U − account`).

*Ledger.* The proofs read the day inequality at world payouts only, and use neither `mem` nor
`mu_nonneg`. No bound is stated for an unbudgeted trader. *Inhabited:* `plainMarket_entailed`
(`B = 0`, empty condition), `constantFresh_unexploited` (a nontrivial condition, not entailed).
`ComputableMarket M.P` is inhabited nowhere in this round.

## 2. Entailed conditions (A3)

`C.Entailed L`: every world live on day `n` satisfies the day-`n` rows.

**Theorem** (`DualCertifiedMarket.account_nonneg_of_entailed`). If `M.C.Entailed M.L`, the
account is nonnegative at every world live at `N`; hence `AccountBounded 0`
(`accountBounded_of_entailed`).

A world live at `N` need not be live at `n ≤ N`; `Condition.holds_of_live_later` gets the
day-`n` rows at it from the assessment's support-local nesting, a day's rows reading finitely
many sentences.

**Theorem** (`DualCertifiedMarket.deductive_exact`, registered
`exact.entailed-conditions-free`). Let `DP` be a deductive process with
`M.L.Live n v ↔ v.ConsistentWith (DP.D n)`, and `coords n` a fragment per day such that on cube
points `M.C.Holds n x ↔ DeductiveRegion.deductiveRegion (DP.D n) (coords n) x`. Then no
efficiently computable trader exploits `M.P` relative to `DP`, and
`deductiveRegion (DP.D n) (coords n) (M.P n)` for every `n`.

*Ledger.* That the rows present the deductive region is a hypothesis; no row presentation of
a hull is computed. *Inhabited:* `deductive_witness` — stage `{p}` on every day, fragment
`[p]`, the floor at level one, the market `pinSchedule.market`; the region is the point `p = 1`
(`deductiveRegion_assert`) and the theorem's conclusion is `P n p = 1` for every `n`.

## 3. Obstruction (A5)

`C.seller w` is the trader whose day-`n` strategy holds `−(w n j)·a` shares of `φ` for each
term `(a, φ)` of each day-`n` bet, `w` rational; its coefficients are constants.

**Theorem** (`Condition.seller_netWorth_ge`). For any history `P` with `C.Holds n (P n)` for
all `n` and any `w ≥ 0`: `−C.account w N W ≤ (C.seller w).netWorth P W N` at every world and
every `N`. (`sellStrategy_value`: the day value is `stake(P n) − stake(W)` exactly.)

**Theorem** (`Condition.seller_exploits`, registered `exact.seller-obstruction`). If moreover
`C.account w N W ≤ Ub` at every world live at `N`, and for every `B` some world live at some
`N` has `C.account w N W < −B`, then `L.Exploits (C.seller w) P`.

*Ledger.* `P` is any history: no certificate, no rationality, no range. Efficiency of the
seller is a hypothesis of `not_isLogicalInductor_of_seller` and is not discharged for any
seller. *Inhabited:* `seller_exploits_witness`.

## 4. Two conditions no compliant history survives (A6)

`tighteningLevel n = 1 − 2^-(n+1)`.

**Theorem** (`tighteningFloor_seller_exploits`, registered `exact.tightening-floor-exploited`).
`tighteningFloor φ` demands `tighteningLevel n ≤ P n φ`. If on every day some live world
refutes `φ`, then against every history satisfying the condition the seller of one share a day
exploits. Values (`tighteningFloor_seller_value`): at least `−1` at every world and every `N`;
at least `N` through day `N` where `φ` is false. Every demanded bet is nonnegative where `φ` is
true (`tighteningFloor_entailed_where_true`). *Inhabited:* `tighteningFloor_witness`.

**Theorem** (`freshFloor_seller_exploits`, registered `exact.fresh-floor-exploited`).
`freshFloor` demands `tighteningLevel n ≤ P n (atom n)`. If on every day `n` some live world
refutes `atom n`, then against every history satisfying the condition the seller of `n` shares
of `atom n` on day `n` exploits. Values (`freshFloor_seller_value`): at least `−1` at every
world and every `N`; at least `N − 1` through day `N` where `atom N` is false. *Inhabited:*
`freshFloor_witness`, over `revealProcess` (`D n = {atom k : k < n}`), where every demand is
true at every world live the next day.

*Ledger.* The criterion forms `tighteningFloor_not_isLogicalInductor` and
`freshFloor_not_isLogicalInductor` take `EfficientlyComputable` of the seller as a hypothesis.

## 5. The prefix reserve bound (A4, `ExactConditionsReserve`)

**Lemma** (`reserve_sum_bound`). `Ω` finite; `r, q : ℕ → Ω → ℝ`; `r n ≥ 0` and
`r (n+1) ≤ r n` for `n ≤ N`; `Σ_ω r 0 ω = 1`; `Σ_ω r n ω · q n ω ≥ 0` for `n ≤ N`;
`Q_n = Σ_{i ≤ n} q i`; `Q_n(ω') ≤ U` whenever `r (n+1) ω' < r n ω'`, `n < N`, and `Q_N(ω') ≤ U`
whenever `ω' ≠ ω` and `r N ω' > 0`. If `r N ω > 0` then `Q_N(ω) ≥ −U(1 − r N ω)/r N ω`.

`PrefixReserve L C N`: a finite profile type with a world per profile and masses `r` as above,
with `r n ω > 0 → L.Live n (world ω)` and every day-`n` bet of nonnegative `r n`-average, for
`n ≤ N`.

**Theorem** (`DualCertifiedMarket.reserve_bound`, registered `exact.prefix-reserve-bound`).
For `R : PrefixReserve M.L M.C N` and `ω` with `R.r N ω > 0`:
`M.C.account M.mu N (R.world ω) ≥ −M.U (1 − R.r N ω)/R.r N ω`.

Beside it: `accountBounded_of_reserve` (if every world live at `N` is a profile of some prefix
reserve through `N` with mass at least `ρ > 0` on it, then `AccountBounded (U(1 − ρ)/ρ)`);
`account_ge_neg_odds` (if `v'` is live at `N` and `ρ·g(v') + g(w) ≥ 0` for every bet of every
day through `N`, then `account N w ≥ −ρU`).

*Inhabited:* `oneFloor_reserve_bound`. One floor at `c ∈ (0,1)` on day `0` on the atom `p`,
which `refuteProcess` refutes from day `1`. Profiles: `p` true, `p` false. `r 0 = (c, 1 − c)`,
`r 1 = (0, 1 − c)`. The day-`0` row averages to `c(1 − c) − (1 − c)c = 0`. Conclusion: the
account through day `1` at the world refuting `p` is at least `−3c/(1 − c)`, in the market
`(oneFloor c).market`, whose ceiling is `3`.

## 6. The conditional bridge (A7, `ExactConditionsReserve`)

`prior n = Σ_{i<n} mu i (x i − c)`; `margin n = U + 1 − prior n`; `ratio n = mu n / margin n`.
`Bridge.Frequency c U γ x mu`: if `ratio` is not summable, there is `N₀` with
`(c + γ) Σ_{i<N} ratio i ≤ Σ_{i<N} ratio i · x i` for all `N ≥ N₀`.

**Theorem** (`Bridge.bridge`, registered `exact.conditional-bridge`). Let `0 < c < 1`, `γ > 0`,
`0 ≤ x n ≤ 1`, `mu n ≥ 0`, `prior n + mu n (1 − c) ≤ U` for all `n`, and
`Frequency c U γ x mu`. Then `ratio` is summable; `margin` is bounded above; `mu` is summable;
and for every finite `S` and every `y ≥ 0`, `Σ_{i∈S} mu i (y i − c) ≥ −c Σ' mu`.

**Instance** (`DualCertifiedMarket.accountBounded_of_frequency`). `M.C = floors φ (fun _ => c)`,
`0 < c < 1`; a truth sequence `b`; every world live at `N` gives `φ i` the value `b i` for
`i < N`; on every day `n` some live world affirms `φ n`; `Frequency c M.U γ (realized b)
(fun n => M.mu n 0)`. Then `M.AccountBounded (c · Σ' n, M.mu n 0)`, and no efficiently
computable trader exploits (`no_exploit_of_frequency`).

*Ledger.* `Frequency` is a hypothesis on the realized normalized stakes. It is not derived
from pseudorandomness, calibration or any property of the truth sequence against efficiently
expressible weightings. *Inhabited:* `constantFresh_unexploited` — fresh atoms at a constant
level `c`, over `revealProcess`, where `b ≡ true` and `Frequency` holds with `γ = 1 − c` for
any stakes. There the floors are not entailed (a world refuting the day's atom is live), the
prices satisfy them exactly, and the account is bounded below.

## 7. The floor market (Tier B for one floor per day; A8; `ExactConditionsFloor`)

`liftDay n lo e` replaces each price feature `φ^{*n}` in `e` by `lo φ + (1 − lo φ)·φ^{*n}`;
`liftDay_denoteWith`: its denotation at `V` is `e`'s at the history whose day-`n` prices are
`lo + (1 − lo)·V n`; `liftDay_rank`: the rank is unchanged.

**Theorem** (`floor_day_le`). `T` a day-`n` strategy, `lo` with values in `[0,1]`, `V'` a
cube valuation such that the lifted strategy's value at `V'` is at most `ε` at every Boolean
table on its support. Then at the lifted prices, for every cube `w`,
`T.value w + Σ_{φ ∈ support} max 0 (−position φ) · (w φ − lo φ) ≤ ε`.

`FloorSchedule`: a sentence `φ n` and a level `c n ∈ [0,1]` per day. `FloorSchedule.market L`:
day by day, the pinned `MarketMaker` at tolerance `marketMakerError n` prices the lift of the
firm's action, and the posted quote is `lo + (1 − lo)·quote` (`floorState`).

**Theorem** (`FloorSchedule.exists_market`, registered `exact.floor-market`). For every
assessment `L` and floor schedule `F` there is a `DualCertifiedMarket` with assessment `L`,
condition `floors F.φ F.c` and `U = 3`.

Its multiplier on day `n` is `max 0` of minus the firm's aggregate position on `F.φ n` at the
posted prices (`FloorSchedule.mu`); exact membership is `floor_holds`; the day inequality is
`FloorSchedule.day_le`.

**The unconstrained market** (`plainMarket L`). `AssessmentFirm.history L` with the empty
condition and zero multipliers is a `DualCertifiedMarket`; the day inequality at cube
valuations is `value_le_of_bitTables` applied to the market maker's acceptance.

*Ledger.* One floor per day. `ComputableMarket` is not proved for `FloorSchedule.market`.

## What is typed and what is not shown

Typed and kernel-checked: every statement above.

Not shown:

- **Existence for a general polytope.** No projected fixed point on a polytope, no rational
  point of a polytope near a real one, and no multipliers from a duality theorem are proved.
  Item 136.
- **Computability** of any constructed market. Every `IsLogicalInductor` conclusion in the
  round is conditional on `ComputableMarket`.
- **Efficiency of any seller.** The three `not_isLogicalInductor` statements are conditional
  on it. Item 137.
- **The frequency hypothesis** from any property of the truth sequence. Item 138.
- **The converse of preservation**: that an account unbounded below yields an exploiting
  efficiently computable trader. Item 139.
- **That the reserve bound is tight**, and that a reserve supported only on worlds live at
  the last day fails in the witness example; the second is a remark in the source, not a
  theorem.
- **A reduction to the force layer.** `account_ge_neg_odds` has the shape of
  `OddsBankroll.Account.netWorth_ge_neg_odds`; neither is derived from the other.
- **Necessity of hypotheses.** No necessity witness is given for a hypothesis of any theorem
  here, beyond the two counterexamples of §4 as failures of boundedness.
