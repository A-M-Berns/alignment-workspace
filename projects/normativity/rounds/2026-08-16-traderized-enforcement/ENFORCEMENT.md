# Enforcement

Three strengths, kept apart: asymptotic pressure toward `K_n`; approximate
finite-time enforcement with a stated modulus; exact finite-time enforcement,
`P_n ∈ K_n` at every date. The round proves the third under an exact contract and
the second under the algorithm's actual contract, and displays the smallest
counterexample separating them. Asymptotic pressure is not studied: nothing here
needs it, and a per-date statement that holds at every date already implies any
asymptotic reading of it.

## 1. The contract, resolved

**Lemma 1 (extremal pinning).** For a realised coefficient vector `ζ` at
displayed prices `P`,

    max over W ∈ {0,1}^Φ of ⟪ζ, W - P⟫  =  ∑_φ [ ζ_φ⁺ (1 - P_φ) + ζ_φ⁻ P_φ ] .

*Proof.* The maximising world takes `W_φ = 1` exactly where `ζ_φ > 0` and
`W_φ = 0` where `ζ_φ < 0`; the cash terms cancel because a day-`n` strategy's
value at the prevailing prices is zero. ∎

Every summand is nonnegative, so a bound `≤ ε` on the whole is a bound on each
coordinate: a sentence the aggregate net-buys with coefficient `c` has price at
least `1 - ε/c`. That, and not a projection, is the force the fixed-point
construction supplies. It is why a single separating hyperplane overshoots
(`PROSECUTION.md` W3).

Checked: `test_enforcement.ExtremalPinning`, and `max_gain`/`min_value` are
checked against brute enumeration over the cube in `test_deduction` and the
sanity sweep.

## 2. The enforcement inequality

Fix a row presentation `{(c_j, r_j)}`, intensities `β_j > 0`, violations
`g_j(P)`, and the violation-proportional position `ζ_E(P) = ∑_j β_j g_j(P) c_j`.

**Theorem 2 (enforcement inequality).** For every `x` satisfying every row,

    ⟪ ζ_E(P), x - P ⟫  ≥  ∑_j β_j g_j(P)² .

*Proof.* `⟪ζ_E(P), x - P⟫ = ∑_j β_j g_j(P) (⟪c_j, x⟫ - ⟪c_j, P⟫)`. For each `j`,
`g_j ≥ 0` and `⟪c_j, x⟫ ≥ r_j`, so
`g_j (⟪c_j, x⟫ - ⟪c_j, P⟫) ≥ g_j (r_j - ⟪c_j, P⟫) = g_j²`, the last step because
`max(0,a)·a = max(0,a)²`. ∎

Kernel-checked as
`Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_le_pair`,
with an inhabitation witness (`enforcement_inequality_is_nonvacuous`) exhibiting
a violated price at which the inequality is an equality.

**Theorem 3 (exact finite-time enforcement).** If `K_n ≠ ∅`, the contract holds
at slack zero against the enforcement trader alone, and every `β_j > 0`, then
`P_n ∈ K_n`.

*Proof.* Take `x ∈ K_n`. `x` is in the cube, so the contract gives
`⟪ζ_E(P), x - P⟫ ≤ 0`. Theorem 2 gives `∑_j β_j g_j² ≤ 0`; every term is
nonnegative and `β_j > 0`, so every `g_j = 0`. ∎

Kernel-checked as `le_pair_of_contract_zero`. Two things it does *not* say. It
does not say the intensity has to be large: it holds for every positive `β`,
including arbitrarily small ones, and the contract-feasible set is *identical*
across `β ∈ {1/100, 1, 37}` in `test_enforcement.ExactEnforcement`. And it does
not hold vacuously: the same tests confirm the contract-feasible set is nonempty
and, on a four-sentence Boolean fragment, that the region is not a point.

## 3. Enforcement under the algorithm's actual contract

**Theorem 4 (modulus).** With market-maker slack `ε_n`, ordinary aggregate
position `τ` with `‖τ‖₁ ≤ M_n`, and any `x ∈ K_n`,

    ∑_j β_j g_j(P_n)²  ≤  ε_n + M_n .

*Proof.* The contract applies to `ζ = ζ_E + τ` and to the cube point `x`, giving
`⟪ζ_E, x - P⟫ + ⟪τ, x - P⟫ ≤ ε_n`. Since `x, P ∈ [0,1]^Φ`,
`⟪τ, x - P⟫ ≥ -‖τ‖₁ ≥ -M_n`. Apply Theorem 2. ∎

Kernel-checked as `weighted_square_le_slack_add_volume`. Consequences, per row:

    g_j(P_n)  ≤  sqrt( (ε_n + M_n) / β_j ) .

`M_n` is available: `SOURCE_AUDIT.md` §2 derives `M_n ≤ C^{tf}_n`, the source's own computable
volume bound (the paper's `C_n`), which the `TradingFirm` construction already
produces from the belief history. So the intensities can be chosen **adaptively at date `n`** — set
`β_j = (ε_n + C^{tf}_n)/δ_n²` for any schedule `δ_n` and every row violation is at
most `δ_n`. What cannot be done is choosing `β` from the observed violation: the
enforcement trader is a strategy, a function of prices, and its intensities are
fixed before the market maker picks a price.

For a presentation whose rows each touch one coordinate, `max_j g_j` *is* the
supremum-norm distance to the region, so the modulus converts with no constant.
For a general presentation the conversion carries the row system's Hoffman
constant; the round does not compute one in general and the deduction fixtures
use box rows where none is needed.

**Theorem 5 (exactness fails under slack).** Exact enforcement is false for
`ε_n > 0`.

*Witness.* One sentence, `K = [1/2, 3/4]`, `β = 1`, no ordinary traders,
`ε = 1/8`. At `P = 1/3` the violation is `1/6`, the position is `1/6` shares
long, and `maxgain = (1/6)(2/3) = 1/9 ≤ 1/8`. The contract is met and
`P ∉ K`. `test_enforcement.PositiveSlackBreaksExactness` enumerates the escape
set at denominator twelve as exactly `{1/3, 5/12, 5/6}`. ∎

**Theorem 6 (opposing volume defeats exactness even at slack zero).** With
`ε = 0` and an ordinary aggregate of `ℓ¹` mass `M > 0`, prices outside `K` can
meet the contract.

*Witness.* One sentence, `K = {P ≥ 1/2}` demanded against `K' = {P ≤ 1/2}` — the
worked adversarial fixture of `FUNDING_AND_SAFETY.md` §2 — with `M = 1/2` and
`β = 10`. The unique contract-feasible price is `11/20`, violating by exactly
`1/20 = M/β`. ∎

Theorems 4 and 6 agree: the bound gives `g ≤ sqrt(M/β)` and the truth is
`g = M/β`, which is smaller for `β > M`. The bound is not tight; it is
sufficient, computable, and enough for the safety argument.

Theorems 5 and 6 are about **this compiler**. Whether some other legal trader
does better is §5, and the answer is not the same for every region.

## 4. Finite-time prices differ

Theorem 3 forces `P_n ∈ K_n` for every choice of positive intensity, and an
unmodified market has no such constraint: at a stage where nothing is settled the
unmodified market's price on a sentence is unconstrained by the criterion, while
the enforced market's is confined to `K_n`. In the fixture of
`test_deduction.TraderizedDeduction`, enforcement onto the coherence polytope
after `φ` is settled leaves exactly one feasible price vector, `(1, 0)`, where the
unmodified market at that date is free to price `φ` anywhere. So relation R1 of
`SOURCE_AUDIT.md` §4 is false, and no argument in this round depends on it being
true.

## 5. The exactness fork

Take the disturbance class seriously: every ordinary realised position of `ℓ¹`
mass at most `M`. A price is displayable when some disturbance in that class
brings the aggregate inside the contract, so the mechanism enforces exactly when
**no** price outside `K` is displayable. `exactness.min_max_gain` computes the
disturbance's best play — greedily, and checked against brute force.

One fact organises the answer. At an interior price the contract at slack zero
forces the aggregate to vanish, so a price is displayable exactly when
`‖ζ_E(P)‖₁ ≤ M`. Exact enforcement therefore demands `‖ζ_E‖₁ > M` on the whole
interior complement of `K` — a **floor**, which the violation-proportional
position cannot have because it vanishes as the violation does.

**Theorem 7 (exactness, for a region with an interior).** If `K` has a strictly
interior point `z`, the interior-anchored position

    ζ_E(P) = λ · ramp(γ(P)) · (z − P) ,

with `γ` the Minkowski gauge of `K` about `z` written from the rows, is a legal
expressible strategy and enforces `P ∈ K` exactly against every disturbance of
mass at most `M`, for `λ` large enough.

*Evidence.* `test_exactness.GaugeTraderIsExact`, in one and two dimensions: the
whole contract-feasible set lies inside `K` where the violation-proportional
trader's does not. `test-supported`, not proved in general.

**Theorem 8 (exactness costs the safety property).** The interior-anchored
position does not vanish on `K`, so it holds a position where there is no
violation, and Theorem 2 does not apply to it.

*Witness.* Two mutually exclusive sentences; `K` the convex hull of the three
plausible worlds, which is world-inclusive and full-dimensional. The
violation-proportional position is worth at least `0` in every plausible world at
every grid price. The interior-anchored position is worth `−1/2` at six of them —
including at `P = (0, 1/2)`, which is **inside** `K` with every row violation
zero. ∎

**Theorem 9 (exactness needs an interior, for a region strictly inside the open
interval).** Let one sentence be priced, `K ⊆ (0,1)` nonempty and closed, and
`ζ_E` any continuous strategy. If no price outside `K` is displayable against
disturbances of mass `M > 0`, then `K` has nonempty interior.

*Proof.* `P = 0` is outside `K`, and there the contract charges nothing for a
short position, so excluding it requires `ζ_E(0) > M`. Symmetrically
`ζ_E(1) < −M`. By the intermediate value theorem `ζ_E(P₀) = 0` for some
`P₀ ∈ (0,1)`, and by continuity `|ζ_E| < M` on a neighbourhood of `P₀`. Every
price there is displayable, so all of it lies in `K`. ∎

**The hypothesis `K ⊆ (0,1)` is load-bearing, and an earlier draft of this
section dropped it.** A region touching a cube face is not covered, and is not
covered because the theorem is false there: `K = {0}` is enforced exactly by the
*constant* strategy `ζ_E ≡ −λ` for any `λ > M`. At `P = 0` a short position costs
the disturbance nothing to leave, so the contract charges zero; at every `P > 0`
the aggregate stays short by at least `λ − M` and the cube maximum gain is
`(λ−M)P > 0`. The feasible set is exactly `{0}`
(`test_regressions.EmptyInteriorDoesNotImplyImpossibility`).

**Settlement is therefore the easy case, not the hard one.** Pinning a sentence
to probability one is `K = {P : P_φ = 1}`, a cube face, and a constant long
position enforces it exactly — verified in one and two dimensions. Any statement
that settlement equalities are generically unenforceable is withdrawn.

What is genuinely hard is a region that lies in **no proper cube face** and has
empty relative interior. The coherence polytope of a fragment carrying a
propositional relation is one: `p(φ) + p(¬φ) = 1` cuts a segment through the open
cube, an enforcement position must be long above it and short below it, and
continuity puts a cancellable band across it at every finite intensity — half-width
`M/(2β)`, exhibited exactly because a grid coarser than that reports none
(`test_regressions.CoherenceSegmentIsStillHard`).

**Conjecture (face-solidity).** Exact enforcement against a positive disturbance
budget is available exactly when `K` has nonempty interior *relative to the
smallest cube face containing it*. It is a theorem in one dimension for convex
`K = [a,b]`, where the three cases are: `a < b`, possible; `a = b ∈ {0,1}`,
possible; `a = b ∈ (0,1)`, impossible. In higher dimensions it is a conjecture
delimited by the witnesses above — settlement faces on the possible side, the
coherence segment on the impossible side — and nothing here proves it.

What survives on the impossible side is tolerance at any level: for
`ζ_E(P) = s(c − P)` the displayable interval around `c` has width exactly `2M/s`,
positive for every finite `s` and shrinking without limit. So the fork resolves as
**A for face-solid regions, at a cost; B for regions that are not; C as the
asymptotics in that second case.** Whether that matters is `D`, and
`FORCE_INTERFACE.md` §1 answers it: the constitutional interface consumes a
declared tolerance schedule, not exactness.

## What this section does not establish

That any market maker realises the contract. `MarketMaker` is read as delivering
it in `SOURCE_AUDIT.md` §2 and it enters every theorem here as a hypothesis. That
`M_n = C^{tf}_n` is the tightest available bound — it is the one the source
construction already computes, and nothing here shows it cannot be improved. That
the enforced prices are *good*: enforcement onto a region says nothing about
whether the region is the right one, which is the whole of §VII of the report.
