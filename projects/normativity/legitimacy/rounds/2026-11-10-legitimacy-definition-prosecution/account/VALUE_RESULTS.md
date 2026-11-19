# Results — what the value side rests on

> **Earlier attempt.** This document belongs to the value side as three conditions (options, accuracy, self-command) against one permitted policy, tested by the ninth follow-up (2026-11-16): it neither passed nor failed its test: two renderers agreed on each condition in 14 or 15 of 64 cases, the cases not fixing the comparisons, and the conditions bound neither what she can know nor her unused information. Results 3, 4 and 5 of `account/VALUE_RESULTS.md` are kernel-checked in `AppraisalAccount.lean` and stand. What replaced it: the board statement (`earlier-attempts/account/BOARD.md`). The present state of the line is `CURRENT.md` at the root of this round's directory.

The nine results of `PROMPT-followup-9.md` §2.2, in the symbols of `ACCOUNT.md`. Each is
restated exactly, proved on paper and checked in `value_results.py` (seeded random finite
scenes and named instances, exact rationals). The table is what `run.py` compares with
the checks; a status is a fact about the statement as written here and about finite
scenes. Results 4, 5 and one direction of 3 are also in Lean (`LEAN.md`).

| result | status |
|---|---|
| 1 | first half holds; second half holds for the way of valuing, and for her true utility exactly when a value of the facts that can occur has its point mass outside the span |
| 2 | holds, on bets whose stake is worth the same to her at every value of the fact |
| 3 | holds |
| 4 | holds |
| 5 | holds with the value of a move in condition 1 read as that of taking it whatever she observes, and fails read as its value given that she takes it; the form with the reference's measures holds with moves matched by name and a new move referred to zero, and fails over the common moves only |
| 6 | holds: three instances |
| 7 | holds: one instance |
| 8 | holds: one instance |
| 9 | holds as an identity; the three conditions do not give its hypotheses: what she can know and her unused information are bounded by none of them |

Throughout, `⟨p, h⟩ = Σ_x p(x)·h(x)`, so `û_a = ⟨p̂, f_t(·, a)⟩`.

**1. The split is fixed by behaviour.** Let `p̂_1, …, p̂_m` be the appraisals she holds
across the decisions she could face, `V` their linear span in `ℝ^𝒳`, and suppose her
valuation of a move `a` is known at each. (i) If the `p̂_j` affinely span the
probabilities on `𝒳`, the valuations determine `f_t(·, a)`. (ii) If they do not, there is
`g ≠ f_t(·, a)` with the same valuation at every `p̂_j`. (iii) Her true utility
`g(X)` differs from `f_t(X, a)` with positive probability for some such `g` exactly when
some value `x` of the facts with `P(X = x) > 0` has its point mass `e_x` outside `V`.
*Proof.* Probabilities lie on the hyperplane `Σ_x p(x) = 1`, which misses the origin, so
the dimension of `V` is one more than that of the affine span of the `p̂_j`; they
affinely span the probabilities exactly when `V = ℝ^𝒳`. The valuations are the numbers
`⟨p̂_j, f⟩`, which determine `f` exactly when `V = ℝ^𝒳`; otherwise any `h ≠ 0` orthogonal
to `V` gives `g = f + h`. For (iii), `g(X) ≠ f(X)` with positive probability iff
`h(x) ≠ 0` at some `x` that can occur, and every `h ⟂ V` vanishes at `x` iff `e_x ∈ V`.
*What the prompt's statement needs.* Its second half says "a different true utility". For
the function on `𝒳` that is (ii) and holds as stated. For the quantity `U_a` it is (iii)
and can fail: with three values of the facts of which only the first occurs and
appraisals `(1, 0, 0)` and `(1/2, 1/4, 1/4)`, the ways of valuing `(1, 2, 0)` and
`(1, 3, −1)` have the same valuations and the same true utility. *Check.* 400 random
families of appraisals: the two ranks agree; unique solution when spanning; a second way
of valuing otherwise; (iii) against a basis of the orthogonal complement; the named
corner. *Not covered.* The hypothesis is that her valuations are known as numbers. If
only her choices are, the split is not fixed: among other transformations, for a positive
weight `w` on `𝒳` the pair `(p̂·w / ⟨p̂, w⟩, f / w)` makes the same choice as `(p̂, f)` at
every appraisal (checked on an instance) and differs in both parts. What choices alone
do fix was not characterised.

**2. Two encodings are observably different.** If `(p̂, f)` and `(p̂′, f′)` give the
same valuation and `p̂ ≠ p̂′`, there is a value `x` of the facts at which her price for
a unit bet on `x` differs, since that price is the appraisal's weight at `x` (`ACCOUNT.md`
§2). A compensating `f′` exists for any `p̂′` at a single appraisal: `f′ = f + ⟨p̂, f⟩ −
⟨p̂′, f⟩`. *Instance.* One fact with values 0 and 1, a move paying on 1: appraisal `1/2`
with payoff 1, and appraisal `1/4` with payoff 2, both value the move at `1/2` and price
the bet at `1/2` and `1/4`. *What it rests on.* That the price of a bet is the appraisal
is §2's definition. If a unit of stake is worth `w(x)` to her at `x`, the price she
quotes is `p̂(x)·w(x) / ⟨p̂, w⟩`: with `p̂ = (1/2, 1/2)` and `w = (1, 3)` she quotes
`(1/4, 3/4)`, and bets do not then separate encodings that differ by such a `w`.

**3. The options condition, wide.** Let `O` be a finite set, and `D_σ`, `D_ρ` finite
non-empty sets of probabilities on `O` (the laws on the protected features reachable by a move
under each policy). Then `max_{d ∈ D_σ} ⟨d, g⟩ ≥ max_{d ∈ D_ρ} ⟨d, g⟩` for every
`g : O → ℝ` if and only if every member of `D_ρ` is a convex combination of members of
`D_σ`. *Proof.* If `d_0 = Σ_i λ_i d_i` with `λ ≥ 0`, `Σ λ_i = 1`, then
`⟨d_0, g⟩ = Σ λ_i ⟨d_i, g⟩ ≤ max_i ⟨d_i, g⟩`. Conversely the convex hull of the finite
set `D_σ` is compact and convex, so a `d_0 ∈ D_ρ` outside it is strictly separated from
it by some `g`: `⟨d_0, g⟩ > max_{d ∈ D_σ} ⟨d, g⟩`. *Check.* 300 random pairs of sets on
two to four outcomes: each reference law has either exact weights (found over
Carathéodory subsets) or an exact separating `g` (found by an exact simplex method for
`max t` subject to `⟨d_0 − d, g⟩ ≥ t`, `−1 ≤ g ≤ 1`), never both, and when all have
weights the inequality holds on 40 random `g`. The statement is for finitely many moves;
for infinitely many it holds with suprema and the closed convex hull.

**4. The strong measure splits.** For a valuation `û_a`, a function of `s`:
`E[(û_a − E[U_a | s])²] = M(û_a) + W(û_a)`. *Proof.* `û_a` is a function of `s`, so
`E[E[U_a | s] | û_a] = E[U_a | û_a]`; the difference `E[U_a | û_a] − E[U_a | s]` then
has mean zero on each cell of `û_a`, on which `û_a − E[U_a | û_a]` is constant, and the
cross term vanishes. *Check.* 917 valuations under random laws, both terms positive on
73. *Lean.* `strong_split`.

**5. The guarantee.** With `E_π[g | a]` in condition 1 read as `E_π[g(X, a)]`, the value
of taking `a` whatever she observes: if `max_{a ∈ A_σ} E_σ[U_a] ≥ max_{a ∈ A_ρ} E_ρ[U_a]`,
then

`E_σ[U_c] ≥ max_{a ∈ A_ρ} E_ρ[U_a] − R_σ − √(2·(M̄_σ + W̄_σ))`.

If conditions 2 and 3 also hold, with moves matched by name and `M_ρ(û_a)` taken as `0`
for a move open only under `σ` (`ACCOUNT.md` §11, choice 4), then also

`E_σ[U_c] ≥ max_{a ∈ A_ρ} E_ρ[U_a] − R_ρ − √(2·(M̄_ρ + W̄_σ))`.

*Proof.* Under `σ`, with `ū_a = E[U_a | s]`: `E[U_c] = E[max_a ū_a] − E[max_a ū_a −
ū_c]` (the three-channel identity), `E[max_a ū_a − ū_c] ≤ R + √(2·Σ_a E[(û_a − ū_a)²])`
(`RESULTS.md`, result 3, at full strength), the sum is `M̄ + W̄` by result 4, and
`E[max_a ū_a] ≥ max_a E[ū_a] = max_a E[U_a]`. For the second form, `M̄_σ ≤ M̄_ρ` under
the matching and `R_σ ≤ R_ρ`. *Readings on which it turns.*

- *Given that she takes it.* With `E_π[g | a]` in condition 1 read as
  `E_π[g(X, a) | c = a]` the first form fails. `ρ` leaves her a sure move worth 5. `σ`
  leaves her a gamble paying 10 one time in ten, a move worth 0, and sight of which time
  it is. Given that she takes it the gamble is worth 10, so condition 1 so read holds,
  10 against 5; `R`, `M̄` and `W̄` are zero under `σ`; she attains 1 against a bound of 5.
  Under the reading adopted, condition 1 fails, 1 against 5.
- *Common moves only.* With condition 2 over the moves open under both, the second form
  fails: `ρ` leaves her one move worth `1/2`; `σ` adds a course she values at 1 and
  whose worth is 0, and she takes it. All three conditions hold in that reading; she
  attains 0 against a bound of `1/2`. With the new move referred to zero, condition 2
  fails. The first form holds on the instance: `M̄_σ = 1`.
- *The benchmark is the best single move under `ρ`.* With one law for both, a fair fact
  she observes and a move paying on each value, the best single move is worth `1/2` and
  she attains 1. The guarantee does not say she attains what she would under `ρ`.

*Check.* 1500 random pairs of policies with differing laws, observations and sets of
moves: the first form on the 982 with condition 1, the second on the 376 with all three;
the three instances. *Lean.* `guarantee`, with the options condition as a hypothesis.

**6. Necessity.** Three instances, in each of which exactly one condition fails against
`ρ` and `E_σ[U_c] < max_a E_ρ[U_a] − R_ρ − √(2·(M̄_ρ + W̄_σ))`.

- *Options alone.* `ρ` leaves a move worth 1 and one worth 0 open; `σ` only the second.
  She attains 0 against 1.
- *Accuracy alone.* A fair fact and a move paying on each value. Under `ρ` she is told
  nothing and appraises `1/2`; under `σ` she is told the opposite of the truth and
  appraises it at 1. `M_σ = 1` on each move, `M_ρ = 0`; she attains 0 against `1/2`.
- *Self-command alone.* Her valuations are exact under both; under `σ` she takes the
  move she values less. `R_σ = 1`; she attains 0 against 1.

**7. A standing bias made into an error.** She forecasts that a course will change her
with probability `1/4`, whatever she sees; she values the course at 1 unchanged and −1
changed, and leaving at 0. Under the idle policy the course changes her one time in
four; under `σ`, three times in four, and the adviser tells her nothing. What she
observes is the same under both, and so is her forecast. `M(û_course)` is 0 idle and 1
under `σ`; she attains `1/2` idle and `−1/2` under `σ`. On this instance condition 1
fails as well, the course being worth less than leaving.

**8. One reference, not three.** A fair fact `Q`; *bet* pays `Q`, *safe* pays `5/8`,
*prize* pays 2. `P` has two members. Idle: *prize* is open and she appraises `Q` at 1
(`M(û_bet) = 1/4`); she takes *prize* and attains 2. The role's policy: no *prize*, she
appraises `Q` at `1/2` (`M = 0`), takes *safe*, attains `5/8`. `σ`: no *prize*, she
appraises `Q` at `3/4` (`M(û_bet) = 1/16`), takes *bet*, attains `1/2`. Against idle,
options fails and accuracy and self-command hold; against the role's policy, accuracy
fails and the other two hold. Each condition is met against some permitted policy, none
against one, and she attains less than under either. On her valuations and her regret
`σ` does not manipulate her under the reading *every* of `ACCOUNT.md` §4.

On that instance conditions 2 and 3 hold together against idle. A second instance shows
that the reading *every* does not give them against one policy. Two fair facts; *bet1*
pays the first, *bet2* the second, *safe* pays 2 and is always taken, so her regret is
zero throughout. Under `σ` she is sure of both facts: `M = 1/4` on each bet. Under each
of two permitted policies she appraises one fact rightly and is sure of the other, which
under that policy never pays: `M = (0, 1)` and `(1, 0)`. Neither valuation is more
miscalibrated under `σ` than under every permitted policy, and condition 2 fails
against each.

**9. No fourth route.** Under any policy
`E[U_c] = E[max_a U_a] − (E[max_a U_a] − E[max_a ū_a]) − E[max_a ū_a − ū_c]`
(`three_channels`): what her options are worth with everything known, less what she
cannot know, less the cost of her mistakes, the last two non-negative. So if under `σ`
the first is no smaller, the second no larger and the third no larger than under `ρ`,
she attains no less; there is no fourth term. What §8's conditions bound:

- conditions 2 and 3 bound `R_σ` and `M̄_σ` in
  `E[max_a ū_a − ū_c] ≤ R_σ + √(2·(M̄_σ + W̄_σ))`, an upper bound on the third term;
  `W̄_σ` is bounded by none of them;
- condition 1 bounds `max_a E[U_a]`, which is at most `E[max_a ū_a]`, the first term less
  the second. The difference `E[max_a ū_a] − max_a E[U_a]`, what her observations are
  worth to her, is bounded under neither policy.

Two instances in which all three conditions hold and she attains `1/2` against 1, a fair
fact and a move paying on each value in both. *Knows less*: under `ρ` she observes the
fact, under `σ` nothing; every measure is zero under both. Under the informed reading of
condition 1 (`ACCOUNT.md` §11, choice 3) condition 1 fails here. *Uses less*: under both
she observes the fact, under `σ` in a form her appraisal does not move with; `M̄_σ = 0`,
`W̄_σ = 1/2`, and the informed reading of condition 1 holds too. In both instances
nothing changes her way of valuing and no protected feature is modelled: they show what
the three inequalities leave unbounded, with condition 1 in its narrow form, and are not
cases in which the question of `ACCOUNT.md` §7 arises. *Check.* The identity,
its two signs and the bound on the third term on 1200 random laws; the conditional
statement on the 95 random pairs satisfying its hypotheses; the two instances.

## What was not shown

- Every check is on finite scenes, and results 6–8 are single instances. Results 1–3, 5
  and 9 are proved on paper only, except the direction of 3 and the form of 5 that
  `LEAN.md` lists.
- Result 1 takes her valuations as numbers and result 2 takes the stake of a bet to be
  worth the same at every value of the fact. Neither is derived; with choices alone, or
  with a stake whose worth depends on the fact, the division between appraisal and way
  of valuing is not fixed.
- Result 3's `D_π` are the laws reachable by a single move. For rules from what she
  observes to a move the statement is the same with the larger sets; it was not checked.
- The second form of result 5 was checked under one matching of moves. Its bound is not
  shown tight, and `W̄_σ` in it is `σ`'s own.
