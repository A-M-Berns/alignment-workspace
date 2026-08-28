# Provenance

## Sources read, not inherited

The round was dispatched with a claim about two papers attached. Both were
fetched and read; the claim is substantially right and wrong in three places,
and `LEGITIMATE_IMPROVEMENT.md` §F records which.

```text
Subhash Khot and Ashok Kumar Ponnuswami, "Minimizing Wide Range Regret with
Time Selection Functions", COLT 2008.
    https://www.learningtheory.org/colt2008/papers/83-Khot.pdf
    Read in full. Used: the model of §2, Theorem 2, Theorem 3 with equations
    (1), (3), (4) and (5), and Theorem 5's first-order bound.

Haipeng Luo and Robert E. Schapire, "Achieving All with No Parameters:
AdaNormalHedge", COLT 2015.  arXiv:1502.05934
    Read §§1-5. Used: the potential and weight of §3, Algorithm 1, Theorem 1,
    and the confidence-rated extension of §4 with Theorem 3.

Avrim Blum and Yishay Mansour, "From external to internal regret", JMLR 8
(2007), 1307-1324.
    Not fetched. Cited only as the source of the model Khot-Ponnuswami improve
    on, and every quantitative comparison to it is quoted from their §1 rather
    than checked against Blum-Mansour directly. Declared here rather than
    implied.
```

## Frozen inputs, read and not modified

```text
rounds/2026-08-25-legitimate-evolution/src/replay.py   imported unchanged
rounds/2026-08-25-legitimate-evolution/src/answer.py   imported unchanged
```

`tests/test_composition.py::TestFrozenLEIsUntouched` asserts by AST parse that
this round reads only the frozen public interface and adds nothing to it.

## New names introduced

All provisional under `AGENTS.md` §6.

Learning: *occasion*, *menu*, *selector*, *comparator*, *repair regret*,
*comparative advantage*, *effective mass*, *opportunity mass*, *predictability*.

Surface: *comparison surface*, *licensed*, *in menu*, *designated*, *evaluator*,
*falling edge*, *surgical repair*, *repair registry*, *repair identity by
content*.

Composition: *improvement challenge*, *evidence episode*, *demonstrated*,
*LIVE*, *CONTESTED*, *SETTLED*, *ESCAPED*, *No Free Evasion*, *coherence of the
surface with the legitimate state*.

## What was computed rather than asserted

Every number in `LEGITIMATE_IMPROVEMENT.md`'s countermodel table is produced by
`src/cases.py` and re-derived by `tests/test_composition.py`. The composition of
Khot-Ponnuswami with AdaNormalHedge is **re-derived, not imported**: the
published theorems assume losses in `[0,1]` and the reduction emits `[-1,+1]`.
The analysis needs `|r_t| <= 1`, which holds because the reduction forces the
inner player's loss to zero. `thm_a_repair_regret` is the numerical check of
that step and is run on twelve adversarial streams.
