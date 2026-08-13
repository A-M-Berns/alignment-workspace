# The crown-jewel normative-learning theorem

What the strongest achievable normative-learning theorem is, what it assumes, and
why it deserves — or does not deserve — the word "learning".

**Verdict: `CROWN-JEWEL-PATH-POSITIVE / DYNAMICS-STRENGTHENING-OPEN`.**

The theorem is viable and its assumptions are intelligible. The construction
satisfies it by immediate compliance rather than by a learning curve, and that is
characterised exactly rather than left as an observation.

```sh
python3 tests/run.py     # 31 tests
```

| file | what it is |
|---|---|
| `CROWN_JEWEL_THEOREM.md` | definitions, hypotheses, construction, guarantee, corollary, non-claims |
| `ASSUMPTION_AUDIT.md` | hypothesis / construction / derived split; low regret is a conclusion |
| `COVERAGE_INTERFACE.md` | four candidate coverage shapes; the weakest sufficient one; the corrigibility composition |
| `REPAIR_LANGUAGE.md` | the typed shape, the five constraints, and the new recurrence condition |
| `LEARNING_DYNAMICS.md` | when the construction can put mass on a bad response at all |
| `THEOREM_STRENGTH_LADDER.md` | levels 0–7 with what each costs |
| `PROSECUTION.md` | P1–P10 and the three weaknesses |
| `PATH_INVENTORY.md` | what remains; three blocking items |
| `FOR_HUMANS.md` | the human register |

The headline change from the merged rounds is the **denominator**: the theorem is
about `Q_T(g)/M_T(g)`, the bad-response rate *among occasions where the reason was
due*, not `Q_T(g)/T`. That makes the coverage condition `B_T = o(M_T)` — far
weaker than positive density — and makes the statement non-vacuous under sparse
exposure.

Status: `test-supported`, nothing registered, no Lean.
