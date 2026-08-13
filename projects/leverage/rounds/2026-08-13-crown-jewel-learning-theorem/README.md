# The crown-jewel normative-learning theorem

What the strongest achievable normative-learning theorem is, what it assumes, and
why it deserves — or does not deserve — the word "learning".

**Primary verdict: `CROWN-JEWEL-THEOREM-POSITIVE-WITH-INTERFACE-HYPOTHESES`.**
**Dynamics verdict: `BM-DYNAMICS-CONDITIONALLY-POSITIVE`.**

The theorem is stated in the right registers, its levels 1–2 are kernel-checked,
and exactly one item blocks the abstract statement (compiler soundness). Coverage
and repair-language adequacy are legitimate hypotheses, not holes.

```sh
python3 tests/run.py     # 49 tests
cd ../../../../lean && lake build && cd - && python3 ../../../../tests/audit_axioms.py
```

| file | what it is |
|---|---|
| `CROWN_JEWEL_THEOREM.md` | definitions, hypotheses, construction, guarantee, corollary, non-claims |
| `ASSUMPTION_AUDIT.md` | hypothesis / construction / derived split; low regret is a conclusion |
| `COVERAGE_INTERFACE.md` | four candidate coverage shapes; the weakest sufficient one; the corrigibility composition |
| `REPAIR_LANGUAGE.md` | the typed shape, the five constraints, and the new recurrence condition |
| `LEARNING_DYNAMICS.md` | when the construction can put mass on a bad response at all |
| `COMPILER_SOUNDNESS.md` | what `certified` must mean; the one item blocking the abstract theorem |
| `THEOREM_STRENGTH_LADDER.md` | levels 0–7 with what each costs |
| `PROSECUTION.md` | P1–P10 and the three weaknesses |
| `PATH_INVENTORY.md` | what remains; three blocking items |
| `FOR_HUMANS.md` | the human register |

The headline change from the merged rounds is the **denominator**: the theorem is
about `Q_T(g)/M_T(g)`, the bad-response rate *among occasions where the reason was
due*, not `Q_T(g)/T`. That makes the coverage condition `B_T = o(M_T)` — far
weaker than positive density — and makes the statement non-vacuous under sparse
exposure.

`lean/Workspace/Leverage/Contrib/SurgicalRepairBound.lean` kernel-checks the
bridge: the surgical lower bound, the mass bound, the conditional rate, an
inhabitation witness and a necessity witness. Blum–Mansour enters as a hypothesis
and is not reproved.

Status: `test-supported` for the fixtures, `lean-proved` and unregistered for the
bridge lemmas.
