# Relational scorekeeping bridge

Whether a small relational theory of answerability can be the common object
consumed by the normative-learning arc and the legitimate-corrigibility arc.

**Verdict: `Shared-representation-positive / corrigibility-interface-positive /
learning-replay-blocked`.** A refinement pass downgraded the first pass's
`Shared-substrate-positive`; `TWO_ARC_INTERFACE.md`'s closing section says where.

```sh
python3 tests/run.py     # 147 tests
```

| file | what it is |
|---|---|
| `MODEL.md` | the state, the move grammar, and the declared simplifications |
| `LOSS_DEPENDENCY_AUDIT.md` | every input of every loss term, who can move it, and the class of edits the loss resists |
| `ACTION_SEMANTICS.md` | what each label decodes to, and the two that misdescribed their moves |
| `BRANDOM_MAP.md` | source, formal analogue and research inference, kept apart |
| `THEOREM_MAP.md` | every statement at the strength its witnesses support |
| `PROSECUTION.md` | where the architecture is weaker than the verdicts read |
| `TWO_ARC_INTERFACE.md` | the main artifact: what is shared, and the disposition of the existing objects |
| [Legitimacy wiki](https://github.com/A-M-Berns/alignment-workspace/wiki/Legitimacy) | the human register |

`src/scorekeeping.py` carries the one equation the round turns on. Everything on
the answerability arc follows from it together with the write discipline in
`src/moves.py`.

This round is additive and independent. It branches from `main` and takes nothing
from any open pull request; where it uses another round's findings, it replays
them as attacks against its own construction rather than importing them.

Status: `test-supported`, nothing registered, no Lean.
