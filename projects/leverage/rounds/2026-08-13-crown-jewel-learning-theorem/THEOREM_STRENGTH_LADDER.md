# Theorem-strength ladder

What each strengthening costs, so a later round does not confuse the crown jewel
with something strictly stronger.

| level | statement | status |
|---|---|---|
| **0** | finite-horizon regret against every represented repair, simultaneously | **ACHIEVABLE NOW** — Blum–Mansour Theorem 18; the repository learner implements it |
| **1** | finite-horizon bad-response-mass bound `Q_T(g) <= B_T(g)/delta_g` | **ACHIEVABLE NOW** — the surgical lemma, exact on the fixture |
| **2** | conditional rate `Q_T(g)/M_T(g) -> 0` under coverage | **ACHIEVABLE NOW** given H4–H6; this is the crown jewel, and it is **pathwise** — it holds on each realized history |
| **3** | expected sampled register | **ROUTINE EXTENSION**, once stated correctly: `E[N_T] = E[Q_T]`, since `Q_T` is random. `E[N_T]/M_T` is **not** well formed — `M_T` is random too |
| **4** | one anytime learner over an infinite run | **ROUTINE EXTENSION** — standard doubling; not done here, no new idea needed |
| **5** | almost-sure pathwise `N_T/M_T -> 0` | **OPEN** — needs a martingale concentration argument over the selected dates; no obstruction identified, but not free |
| **6** | genuine within-run mass-shedding dynamics | **WITNESSED** — on a regenerating fixture with a coherent irreducible repair graph, mass on the inferior response falls from `1/2` to below `10^-4` while a matched uninformative control stays exactly at `1/2`. A witness at four horizons, **not** a convergence theorem: `p_t(b) -> 0` is unproved |
| **7** | counterfactual replay / policy-regret domination | **REFUTED UNDER CURRENT ASSUMPTIONS** — merged PR #29: distortion grows with the horizon for every non-identity comparator once its licensing condition recurs. Strictly stronger, and **not needed** for levels 0–5 |

## Reading the ladder

Levels 0–2 are the theorem. Levels 3–4 are bookkeeping a paper would do. Level 5
is a real but ordinary piece of probability.

Level 6 was where the programme's rhetoric outran its mathematics. The first pass
located the obstruction in the construction; the refinement relocated it to the
fixture; the final pass removed the fixture defect and the dynamics appeared. What
remains at level 6 is a proof, not a phenomenon.

Level 7 is settled and negative, and the crown jewel does not touch it. That is the
main structural gain of the last two rounds: the flagship result was moved off the
level that is refuted onto levels that are not.

## What must not be conflated

`Q_T/T -> 0` is **not** level 2. It is weaker and can be vacuous — under a
`sqrt(T)` exposure schedule it holds even if every selected occasion is
mishandled. Level 2 is the conditional rate, and the denominator is the whole
point.


## Formalization status

Levels 1 and 2 are now **kernel-checked**. `SurgicalRepairBound.lean` proves
`margin_mul_mass_le_regret`, `mass_le_regret_div_margin` and
`rate_le_bound_div_margin_mul_exposure`, with the regret upper bound entering as
an explicit hypothesis — Blum–Mansour is cited, not reproved. It ships an
inhabitation witness and a necessity witness showing the margin's positivity is
load-bearing. All declarations audit to `[propext, Classical.choice, Quot.sound]`.
