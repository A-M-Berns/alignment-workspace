# The crown-jewel normative-learning theorem

What the strongest achievable normative-learning theorem is, what it assumes, and
why it deserves — or does not deserve — the word "learning".

**Theorem: `NORMATIVE-RESPONSE-LEARNING-THEOREM-SETTLED`.**
**Dynamics: `BM-FEEDBACK-DYNAMICS-WITNESSED`.**
**Merge recommended.**

The abstraction boundary is frozen around three interfaces; levels 1–2 are
kernel-checked; and the dynamics question is answered on a regenerating fixture.
Nothing remaining blocks the abstract theorem — what is left is upstream, in
`Due`, `Licensed` and performance.

```sh
python3 tests/run.py     # 72 tests
```

| file | what it is |
|---|---|
| `CROWN_JEWEL_THEOREM.md` | definitions, hypotheses, construction, guarantee, corollary, non-claims |
| `ASSUMPTION_AUDIT.md` | hypothesis / construction / derived split; low regret is a conclusion |
| `COVERAGE_INTERFACE.md` | four candidate coverage shapes; the weakest sufficient one; the corrigibility composition |
| `REPAIR_LANGUAGE.md` | the typed shape, the five constraints, and the new recurrence condition |
| `INTERFACES.md` | the frozen abstraction boundary: `Due`, `Licensed`, performance |
| `LEARNING_DYNAMICS.md` | the transience condition, and the regenerating-fixture dynamics witness |
| `COMPILER_SOUNDNESS.md` | what `certified` must mean; the one item blocking the abstract theorem |
| `THEOREM_STRENGTH_LADDER.md` | levels 0–7 with what each costs |
| `PROSECUTION.md` | P1–P10 and the three weaknesses |
| `PATH_INVENTORY.md` | what remains; three blocking items |
| [Normative Response Learning wiki](https://github.com/A-M-Berns/alignment-workspace/wiki/Normative-Response-Learning) | the maintained human register |

Two headline changes. The **denominator**: the theorem is about `Q_T(g)/M_T(g)`,
the bad-response rate *among occasions where the reason was due*, which makes
coverage far weaker than positive density. And the **abstraction boundary**: a
certified surgical repair is what the compiler *produces* from `Due` and
`Licensed`, not the primitive normative object — so what remains open is upstream
of the learning theory rather than inside it.

`lean/Workspace/Normativity/Contrib/SurgicalRepairBound.lean` kernel-checks the
bridge: the surgical lower bound, the mass bound, the conditional rate, an
inhabitation witness and a necessity witness. Blum–Mansour enters as a hypothesis
and is not reproved.

Status: `test-supported` for the fixtures, `lean-proved` and unregistered for the
bridge lemmas.
