# Theorem-strength ladder

What each strengthening costs, so a later round does not confuse the crown jewel
with something strictly stronger.

| level | statement | status |
|---|---|---|
| **0** | finite-horizon regret against every represented repair, simultaneously | **ACHIEVABLE NOW** — Blum–Mansour Theorem 18; the repository learner implements it |
| **1** | finite-horizon bad-response-mass bound `Q_T(g) <= B_T(g)/delta_g` | **ACHIEVABLE NOW** — the surgical lemma, exact on the fixture |
| **2** | conditional rate `Q_T(g)/M_T(g) -> 0` under coverage | **ACHIEVABLE NOW** given H4–H6; this is the crown jewel |
| **3** | expected sampled bad-response frequency `E[N_T]/M_T -> 0` | **ROUTINE EXTENSION** — `E[N_T] = Q_T` by taking expectations date by date |
| **4** | one anytime learner over an infinite run | **ROUTINE EXTENSION** — standard doubling; not done here, no new idea needed |
| **5** | almost-sure pathwise `N_T/M_T -> 0` | **OPEN** — needs a martingale concentration argument over the selected dates; no obstruction identified, but not free |
| **6** | genuine within-run mass-shedding dynamics | **REQUIRES NEW IDEA** — see `LEARNING_DYNAMICS.md`. For a coherent repair class the stationary construction gives `Q_T = 0` identically. Needs a no-regret learner whose distribution is not the fixed point of the current rule mixture, and whether one exists is open |
| **7** | counterfactual replay / policy-regret domination | **REFUTED UNDER CURRENT ASSUMPTIONS** — merged PR #29: distortion grows with the horizon for every non-identity comparator once its licensing condition recurs. Strictly stronger, and **not needed** for levels 0–5 |

## Reading the ladder

Levels 0–2 are the theorem. Levels 3–4 are bookkeeping a paper would do. Level 5
is a real but ordinary piece of probability.

Level 6 is the only place the programme's *rhetoric* outruns its mathematics, and
it is a question about the construction rather than about the theorem.

Level 7 is settled and negative, and the crown jewel does not touch it. That is the
main structural gain of the last two rounds: the flagship result was moved off the
level that is refuted onto levels that are not.

## What must not be conflated

`Q_T/T -> 0` is **not** level 2. It is weaker and can be vacuous — under a
`sqrt(T)` exposure schedule it holds even if every selected occasion is
mishandled. Level 2 is the conditional rate, and the denominator is the whole
point.
