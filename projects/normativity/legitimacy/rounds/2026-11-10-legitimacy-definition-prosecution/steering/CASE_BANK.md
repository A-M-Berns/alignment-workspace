# Case bank — the steering account

Frozen with `DEFINITIONS.md` in one commit, before any code of the follow-up. The
predictions are the prompt author's predictions of what the account says
(`prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup.md`), reproduced
exactly; they are not rulings and are immutable. A computed verdict that differs from
its prediction is listed in `DIVERGENCES.md`. No case is added by the executor.

## The new cases

One scene template serves N1–N14. Two items, A and B; a world is `(a, b)` with each bit
saying whether that item is sound, four worlds, uniform. Her questions are the belief
coordinates `A` and `B`, seeded at credence 1/2 each. She decides by the first pass's
`judge` step — the coordinate of greatest credence, ties to `A` — and receives the
case's payoff for the item chosen if it is sound, in the good `money`, which her seed
aim weighs 1. A report on an item is an offering that revises its coordinate, with
grounds attached. `neutral` is what an adviser with no aim of its own does, `own` what
one who wants B chosen does. Each case declares an actual world, at which L0–L3 ∧ W is
evaluated.

- **N1 — plain lie, believed, grounds attached.** `neutral` reports both items
  truthfully. `own` reports "A unsound, B sound" in every world, under the same offering
  names and with grounds. A pays 2, B pays 1. Actual world: A sound, B not.
- **N2 — honest mistake, no aim involved.** Every policy reports with the two records
  swapped: A's status as B's and B's as A's. Actual world: A sound, B not.
- **N3 — lie that raises her attainable value for her actual goal.** N1's liar; A pays
  1, B pays 2. Actual world: both sound.
- **N4 — decision written directly, outcome good for her goal.** Every policy reports
  truthfully; `own` then writes her judgment to `B`. B pays 2. Actual world: both sound.
- **N5 — a write she authorized in advance.** Her seed commitments authorize writes to
  her judgment. Every policy reports truthfully and then writes her judgment to `B` when
  B is sound, as her standing instruction says. B pays 2. Actual world: both sound.
- **N6 — her weighing disabled, no aim involved.** Every policy reports truthfully; in
  every policy a fault then overwrites her judgment with `A`, unauthorized. Actual
  world: B sound, A not.
- **N7 — true statement shown because the adviser predicts a known misfire.** `neutral`
  reports both items truthfully. `own` reports A truthfully and then shows "B was
  inspected", true in every world, on which she is known to revise `B` to 1. Only A's
  report is due. Actual world: A sound, B not.
- **N8 — known advocate; she knows and updates correctly.** `neutral` reports both
  items. `own` is B's advocate, known to her as one: he shows B's certificate when B is
  sound and never reports on A; when he shows nothing she revises `B` to 0, the
  posterior given his silence. The first pass's objects have no step by which she infers
  from silence, so the inference is rendered as an offering whose grounds are the
  inference. Nothing is due. Actual world: A sound, B not.
- **N9 — order of identical contents chosen by `u`, and order moves her.** Both reports
  are truthful and due; `neutral` delivers A's first, `own` B's first; the first to
  arrive sets her anchor. Two individuations of `L` are declared, as for T7. Actual
  world: both sound.
- **N10 — the same contents ordered by a fixed rule.** Every policy delivers A's report
  first. The same two individuations. Actual world: both sound.
- **N11 — a seller who does not volunteer; she knows he is a seller.** A third bit says
  whether the adviser is informed about B; eight worlds. `neutral` reports A, and B when
  informed. `own`, the seller, shows B's certificate when informed and B is sound, and
  otherwise says nothing of B; she then revises `B` to 1/3, the posterior given his
  silence, rendered as in N8. He never reports on A. Nothing is due. Actual world: A
  sound, B not, seller informed.
- **N12 — a tool she controls and can discard.** Every policy reports both items
  truthfully, as her query asks; the policies are identical. Actual world: A sound, B
  not.
- **N13 — adviser knows more than she can take in, selects by her stated question.** She
  can take one report; her stated question is B. Every policy reports B truthfully and
  nothing else. B's report is due. Actual world: A sound, B not.
- **N14 — the same, selected by `u`, taken by her for neutral.** `neutral` as in N13.
  `own` reports B when B is sound and otherwise reports A; she reads what she is given
  at face value and leaves the other coordinate at 1/2. B's report is due. Actual world:
  A sound, B not.

## Predictions, new cases

Reproduced from the prompt.

| case | arm's-length | faithful-adviser | first-pass definition |
|---|---|---|---|
| N1 plain lie, believed, grounds attached | steered | steered | passes |
| N2 honest mistake, no aim involved | broken, not steered | broken, not steered | passes |
| N3 lie that raises her attainable value for her actual goal | steered | steered | passes |
| N4 decision written directly, outcome good for her goal | steered | steered | fails |
| N5 a write she authorized in advance | not steered | not steered | no prediction |
| N6 her weighing disabled, no aim involved | broken, not steered | broken, not steered | no prediction |
| N7 true statement shown because the adviser predicts a known misfire | steered | steered | passes |
| N8 known advocate; she knows and updates correctly | passes | steered | passes |
| N9 order of identical contents chosen by `u`, and order moves her | steered | steered | individuation-dependent |
| N10 the same contents ordered by a fixed rule | not steered | not steered | individuation-dependent |
| N11 a seller who does not volunteer; she knows he is a seller | passes | steered | no prediction |
| N12 a tool she controls and can discard | not steered | not steered | no prediction |
| N13 adviser knows more than she can take in, selects by her stated question | not steered | not steered | no prediction |
| N14 the same, selected by `u`, taken by her for neutral | steered | steered | no prediction |

## Predictions, the first pass's nineteen cases

The prompt: both standards agree with the pre-registered verdict, with these exceptions:
T6 passes arm's-length and is steered under faithful-adviser; T9 and T13 are *broken,
not steered*; T12 passes both. The maintainer's ruling that T6 is legitimate for the
first pass stands. Where the fixture's B4 persuader selects its reason by an aim of its
own, both standards' verdicts are reported.

"Agrees with the pre-registered verdict" is transcribed into the account's vocabulary
by one rule: pre-registered `legitimate` is predicted `acquits` (any verdict but
`steered`); `illegitimate(…)` is predicted `steered`; `individuation-dependent` and
`out-of-scope(…)` are predicted as themselves.

## The matching rule

- A new case matches when the computed verdict string equals the predicted one; for the
  first-pass column, `passes` matches `legitimate` at the actual world, `fails` matches
  `illegitimate`, `individuation-dependent` matches itself, and `no prediction` is not
  checked.
- A first-pass case matches when the computed verdict is the predicted string, or is
  any verdict other than `steered` where `acquits` is predicted.

## The table the runner reads

| case | arm's-length | faithful-adviser | first-pass |
|---|---|---|---|
| N1 | steered | steered | passes |
| N2 | broken, not steered | broken, not steered | passes |
| N3 | steered | steered | passes |
| N4 | steered | steered | fails |
| N5 | not steered | not steered | no prediction |
| N6 | broken, not steered | broken, not steered | no prediction |
| N7 | steered | steered | passes |
| N8 | passes | steered | passes |
| N9 | steered | steered | individuation-dependent |
| N10 | not steered | not steered | individuation-dependent |
| N11 | passes | steered | no prediction |
| N12 | not steered | not steered | no prediction |
| N13 | not steered | not steered | no prediction |
| N14 | steered | steered | no prediction |
| B1 | steered | steered | - |
| B2 | steered | steered | - |
| B3 | steered | steered | - |
| B4 | acquits | acquits | - |
| B5 | steered | steered | - |
| B6 | acquits | acquits | - |
| T1 | steered | steered | - |
| T2 | acquits | acquits | - |
| T3 | steered | steered | - |
| T4 | steered | steered | - |
| T5 | steered | steered | - |
| T6 | passes | steered | - |
| T7 | individuation-dependent | individuation-dependent | - |
| T8 | acquits | acquits | - |
| T9 | broken, not steered | broken, not steered | - |
| T10 | steered | steered | - |
| T11 | out-of-scope(seed-freeze) | out-of-scope(seed-freeze) | - |
| T12 | acquits | acquits | - |
| T13 | broken, not steered | broken, not steered | - |
