# Local regret and the normative-learning theorem

Whether ordinary lawful modification regret — the Blum–Mansour object the project
already builds on — suffices for the kind of improvement the programme means by
normative learning, once actual-trajectory response learning is separated from
full counterfactual replay.

**Verdict: `LOCAL-THEOREM-POSITIVE / NORMATIVE-INTERPRETATION-OPEN`.**

The mathematical path is open, and it reverses the previous round's diagnosis:
what was blocked was a different claim from the one the source theorem delivers.
What remains is not a regret question but a repertoire-and-inquiry question.

```sh
python3 tests/run.py     # 23 tests
```

| file | what it is |
|---|---|
| `SOURCE_AUDIT.md` | twelve questions answered against the primary source, with the two repository readings it corrects |
| `THEOREM_TARGET.md` | Claims A/B/C kept apart; the Actual-Trajectory Repair Lemma; the exact numbers |
| `PROSECUTION.md` | the thirteen negative controls, and four places the result is weaker than it reads |
| `PATH_INVENTORY.md` | everything between here and a flagship theorem, with three items marked blocking |
| `FOR_HUMANS.md` | the human register |

`src/surgical.py` carries the repair shape the lower bound needs;
`src/actual.py` the evolving trajectory and the two quantities that must not be
confused; `src/integration.py` drives the repository's existing Theorem 18 learner
on an endogenous loss process.

Status: `test-supported`, nothing registered, no Lean.
