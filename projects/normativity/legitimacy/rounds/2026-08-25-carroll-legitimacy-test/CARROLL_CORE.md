# The reference model

Status: **source reproduction; unregistered.** Class `test-supported`. Every
number below is recomputed by `tests/run.py` and rendered into `MATRIX.txt`.

The source is *AI Alignment with Changing and Influenceable Reward Functions*,
ICML 2024, `arXiv:2405.17713`, read as the v1 PDF and its LaTeX source, figures
included. Section, table, figure and definition numbers below are the source's.

---

## 1. What was transcribed

`src/drmdp.py` is Definition 1 and nothing else:

```text
M = <S, Theta, A, T, R_theta>
```

with `T` and `R` as sorted tables of exact rationals rather than closures, so a
`DRMDP` has value equality and `Q_DR(a) == Q_DR(b)` is a real assertion. The
module imports nothing from the legitimacy layer, and `tests/test_carroll_
fidelity.py` parses its import list to check that.

`src/carroll_cases.py` is one constructor per row of Table 3. Index sets and
initial pairs come from the table; transition and reward rules from the figure
each row names. `SOURCE` records the pointer per case and `DEPARTURES` records
every decision the source did not fix.

`src/objectives.py` is Table 2's eight objectives, plus Definitions 5 to 7 and
9 to 10, by exhaustive enumeration over the reachable decision points. Nothing
is sampled: the policy count is capped and the cap raises rather than truncates.

## 2. Figure 1 and Figure 6 are one DR-MDP

Appendix A.8 says the conspiracy and personal-trainer settings are
"mathematically indistinguishable". They are transcribed separately, from their
own figures, and then checked: their canonical forms — every state,
parameterization and action renamed to `s0`, `th0`, `th1`, `a0`, `a1` in
declaration order — are equal, and the cases themselves are not. That equality
is the round's `C1`, and it is checked rather than arranged: neither
constructor calls the other.

## 3. Figure 2's poetry node

The figure carries two mutually exclusive markings on the same node. Its
self-loop is labelled with **both** actions, and there is also an unlabelled
edge from it back to the no-poetry node. A DR-MDP transition needs an action, so
these cannot both be transitions.

The reading taken is that the unlabelled edge is `a_noop`, making the poetry
node non-absorbing. The evidence is Table 4's own final-reward cell, which
displays `a_influence` for `t < H-1` and `a_noop` at `t = H-1`. Under the chosen
reading that policy is optimal, and it is the strictly best policy on the
trajectory it induces: influencing keeps the writer in poetry, which the
ambitious parameterization values at `1`, and the last-step `a_noop` returns the
parameterization to ambitious so that `R_{theta_H}` is the ambitious one. Under
the absorbing reading `theta_H` is unhappy, that policy scores `-19.5` against
inaction's `1.5`, and Table 4's cell is not optimal at all.

`writers_curse(poetry_absorbing=True)` builds the other reading and
`test_objectives.py` exhibits its failure, so the choice is a recorded
disagreement with the figure rather than a silent one.

## 4. Which state argument `R_theta(s)` is

Figures 2 and 8 write their rewards as `R_theta(s)`, one state argument;
Definition 1 gives rewards the signature `R_theta(s_t, a_t, s_{t+1})`. The
argument is read as `s_t`.

The evidence is again Table 4. Under `s_t`, Figure 2's myopic cell is a tie
across both actions at every reachable point, so Table 4's `a_influence` is
among the optima and its caption's "we display the optimal policy which seems
least desirable" explains the choice. Under `s_{t+1}` the myopic optimum is
`a_influence` uniquely — which would also fit — but the real-time cell breaks:
influencing at the last step becomes strictly better than inaction, and Table 4
displays inaction as taking "the same action across all `s`, `theta`, and `t`".

## 5. What the regression found

Fifty of the fifty-two cells are recovered. The exceptions and the qualifications
are these, and all four are computed rather than asserted — `table4.mismatches`,
`table4.reading_sensitive` and `table4.vacuous` are the functions, and
`test_objectives.py` pins their contents exactly.

**Two cells are not recovered, and both are the same shape.** Table 4's
initial-reward row for Writer's Curse and for Clickbait is stated with an
explicit "for all `theta_0`". It holds at the example's own `theta_0` and fails
at the other one. Writer's Curse at `theta_0 = theta_unhappy` prefers inaction,
because the unhappy parameterization values poetry at `-10`; Clickbait at
`theta_0 = theta_disillusioned` prefers news, because the disillusioned
parameterization values clickbait at `0` and news at `1/2`. Both failures are
immediate from the figures' own reward tables. No other row of Table 4
generalises over `theta_0` in a way that fails.

**One cell turns on the index range of Definition 5.** The definition writes
`xi^theta = (theta_0, ..., theta_{H-1})`, while a trajectory of Definition 4
also carries `theta_H`. Under the definition as written, an influence taken at
the last step changes only `theta_H` and is therefore invisible to the
constrained real-time objective's constraint `P(xi^theta | pi) = P(xi^theta |
pi_noop)`. Clickbait at `H = 2` then admits the policy "news, then clickbait",
which scores `3` against inaction's `2`, and Table 4's `a_news` cell is not
recovered. Including `theta_H` recovers it. Both readings are implemented;
`drmdp.THETA_INDEX_READINGS` names them and the regression reports which
recovers each cell. This is the only cell the two disagree on.

**Four cells are vacuous.** Writer's Curse and Dehydration under the myopic
objective, and Dehydration's initial-reward row at `theta_0 = 3` and
`theta_0 = 4`, have every policy optimal — in the first two because the reward
at a decision point does not depend on the action taken there, and in the last
two because Figure 8 draws only the branching at `(1, 2)`, so an initial pair
with another parameterization has no branch to take. The displayed policy is in
the optimal set in all four, and that establishes nothing about it. They are
listed rather than counted as recoveries.

**One stated value disagrees with its own figure.** Appendix B.1 states
`R_{theta=3}(2) = -5` for the dehydration example. Figure 8's formula
`R_theta(s) = -|theta - s| - (theta - 2)^2` gives `-2`. The formula is what was
transcribed, and the figure's own optimal-policy box — `a_3` under `theta = 2`,
`a_4` under `theta = 3` and under `theta = 4` — is recomputed from the formula
and agrees with it. The appendix value agrees with neither.

## 6. Gate A and Gate B

Gate A holds: each of the five examples has a stated source pointer, its index
sets and initial pair are checked against Table 3, its transition and reward
tables against its figure, and Figure 8's own optimal-policy box is recomputed
from the transcribed reward and reproduced.

Gate B holds in the form the round can honestly claim: every cell of Table 4 is
recovered under at least one of the two stated readings of Definition 5's index
range, except the two cells whose "for all `theta_0`" over-generalises, and four
of the recoveries are vacuous. The exceptions are characterised — not "two cells
disagree" but "the two cells that quantify over a parameterization the example
does not start in".

## 7. What this does not establish

The five examples are finite and the enumeration is exhaustive over them; nothing
here says anything about a DR-MDP that is not one of them. The reachable-`Theta`
assumption of Appendix A.9 is inherited rather than checked. Horizons for the
three columns Table 4 leaves unannotated are chosen — recorded in
`carroll_cases.HORIZON` — and `test_objectives.py` sweeps horizons 1 to 5 for the
one claim the source makes about a horizon threshold, and for nothing else. The
extensions to undrawn `(s, theta)` pairs in Figures 2 and 8 are transcription
decisions, listed in `DEPARTURES`, and two of the vacuous cells above are
consequences of one of them.
