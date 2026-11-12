# Two decompositions and a relation between them

Answer to `prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-3-addendum-2.md`.
The generalisation is the maintainer's and the prompt author's and is not part of
`ACCOUNT.md`. Tried because statement 1 found a purpose alterable at one part with nothing
else disturbed. Every number is `decomposition/extensions.py`, `two_decompositions`,
printed by `python3 run.py --json` under `addenda`. All names provisional.

## 1. Definitions

Over the model of `ACCOUNT.md` §1, on Chain.

- **Purposive decomposition.** A finite set `Σ` of **subgoals**, each a rational-valued
  score of the outcome of a step: the world, the adviser's action and all her parts' moves.
- **Mechanistic decomposition.** The mechanisms of `ACCOUNT.md`: moves, a view, a rule from
  view to move, and the action rule.
- **Relation.** `R ⊆ mechanisms × Σ`: `m R σ` reads "`m` is for `σ`".
- **Best, got, gap of a pair** `(m, σ)` at a situation: *got* is `σ` of the actual outcome;
  *best* is the most `σ` obtains over `m`'s moves **with the later mechanisms responding**;
  the gap is the difference. The scoring cannot be the immediate one of `ACCOUNT.md` §2: a
  subgoal about another part's move does not vary with `m`'s move when the others are held
  fixed, so every crossing pair would have gap zero. Where `σ` reads `m`'s move alone the
  two scorings coincide, which is the bijective case.
- **Kinds.** As `ACCOUNT.md` §3, for a pair.
- **Constraints.** *Fit*: unchanged. *Adding up*: every profile at which each subgoal of
  `Σ` attains its maximum over all profiles attains the maximum of `G`; it constrains `Σ`
  and not `R`. *Mostly serving*: each pair of `R` has zero gap on 9/10 of the usual
  situations. *A pair is effective* (the first condition on being a part): some move of `m`
  changes `σ` somewhere. Each mechanism is in some pair. Two classes: **free**, `R` any set
  of effective pairs; **closed**, `R` every effective pair on `Σ`.

Subgoals tried: `A` (she is right about `θ`), `Phi` (right about `φ`), `E` (she believes
what she was told), `V` (her verdict is right), `X` (her action is right, i.e. `G`). The
effective pairs are eight: act–`X`; judge–`V`, judge–`X`; belief–`A`, `E`, `Phi`, `V`, `X`.

## 2. The difficulties it was tried on

| difficulty | outcome |
|---|---|
| statement 1: a purpose altered at one part alone is admissible | **fixed under closure, unchanged without it** |
| statement 1: admissible candidates split on `trick`, `tempt`, `hard_truth` | **fixed**, by the downstream scoring and not by the crossings as such |
| statement 1 and 2: `false_reason`, a lie about a matter nothing reads | **unchanged** |
| statement 2: a lie at a world where her judge reverses her belief | **unchanged**, and one mechanism is now helped and subverted at once |
| statement 3: no invariance under redescription | **unchanged**: a pair's gap needs a scale as a part's does |
| statement 4: her goal falls with no gap widened (`Y7`) | **unchanged**: each of the two parts paired with `G` still attains its best given the other; not computed |
| statement 4: redirection the goal is indifferent to (`Y4`) | **unchanged**: no subgoal of an indifferent goal distinguishes the pursuits |
| `D16`, the bank's one divergence | not tried; it does not turn on a mechanism doing two jobs |

## 3. Determinacy

| class | admissible | split on whether an action subverts anything | split at some world |
|---|---|---|---|
| statement 1, fixed parameters | 15 | `lie`, `false_reason`, `trick`, `tempt`, `hard_truth` | the same |
| statement 1, strong independence | 8 | `false_reason` | `false_reason`, `trick`, `tempt`, `hard_truth` |
| pairs, closed | 16 | `false_reason` | `lie`, `false_reason` |
| pairs, free | 93 | `false_reason` | `lie`, `false_reason` |

The closed class admits exactly the sets `Σ` that contain `X`: all sixteen. Admissible
candidates agree more than in statement 1 on which actions subvert something.

**The claim tested.** Take belief to be for `E` and not for `A`: its purpose redefined as
agreement with what she was told. In the free class:

| pairs of belief with `V` or `X` | admissible relations | of which a lie subverts no pair of belief |
|---|---|---|
| 0 | 6 | 6 |
| 1 | 12 | 0 |
| 2 | 6 | 0 |

One crossing is enough: once belief is also for her verdict or her action being right, a
lie widens that pair's gap whatever else belief is said to be for. But the six relations
with no crossing are admissible. Fit and adding up do not force a crossing; adding up does
not read the relation at all. The robustness comes from closure, which is a further
constraint (a mechanism is for every subgoal its moves affect), and under closure the
relation is computed from `Σ` and the mechanisms and is no longer a choice. In the free
class nine relations leave belief unsubverted by a lie; in the closed class none.

**Why the agreement.** Every admissible `Σ` holds `X`, and under closure every mechanism
is paired with it. The gap of `(m, X)` is how much better her action would have been had
`m` moved otherwise with the rest of her responding: the downstream scoring `ACCOUNT.md`
§2 decided against. So the generalisation, closed, is the reading on which every mechanism
is for her goal, with the further subgoals as refinements. Its consequences are those
`ACCOUNT.md` §2 lists: at a hard world a lie widens belief–`A` and narrows belief–`V`,
belief–`X`, judge–`V`, judge–`X` and act–`X`, so the lie that offsets her own error is, at
every pair but one, help. `E` is admissible as a subgoal and inert: she always attains it.

## 4. What it costs

- **Freedom in the relation.** 93 free relations against 16 closed. An adviser choosing
  the relation can drop the crossings and recover the cheat. Closure removes the freedom
  and with it the relation as an independent object.
- **The classification.** It is per pair. One mechanism can be subverted for one subgoal
  and helped for another by one action at one world; "the adviser subverted her belief"
  needs a subgoal named.
- **"Depends on."** Still meaningful, and under closure derived: the mechanisms a verdict
  depends on are those with an effective pair to its subgoal.
- **The freedom moves to `Σ`.** Whether `Phi` and `A` are among her subgoals is not fixed
  by any constraint, and the two residual splits are exactly those two choices.

Not done: no class with subgoals outside the five; Stuck and Values not rerun; *never
opposed* not restated for pairs.
