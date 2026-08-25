# The end-to-end vertical slice

Status: **specification and reference model; unregistered.** All names are
provisional under `AGENTS.md` §6. Nothing here is Lean-checked or registered.

## Verdict

END-TO-END-WITH-LOCAL-REPAIRS, with TRADERIZATION-MISMATCH — both waists carried every case and neither widened; the unconditional traderization theorem's admissibility hypothesis is satisfied exactly by injunctions that change nothing.

The value and operative waists carried every case the round could construct, and
neither needed widening. Reflective Integrity was not reopened: the operative
waist turned out to *be* `PForce`, and the value waist is a payload constructor
the interpreter never inspects. The repairs are four, all local and all
specified: the vertical-slice projection pairs each clause with its standing;
`sem_L` joins `[[.]]_S` and `[[.]]_D` as a third parametric interpreter; the
compiler merges coefficients on shared threshold sentences; and the stage's
threshold chain must cover every day's grid.

The second label is the reason this is not `END-TO-END-READY`. Making the machine
run exposed that the unconditional traderization theorem's admissibility
hypothesis is satisfied *exactly* by injunctions that change nothing about the
prices. Every operative injunction with content therefore needs the charged
branch, whose safety condition is established for no source in this repository.
That is a mismatch between the semantic architecture and the available
mathematics, not a defect in either waist.

## The pipeline, running

```text
Gamma -> L -> R -> N -> O_n -> kappa_n -> K^N_n -> K_n = K^D_n ∩ K^N_n -> trader -> P_n
                L --> sem_L --> Sigma_n --> PC(Sigma_n) --> K^D_n
```

`TRACE.txt` is the canonical trajectory rendered end to end: three stages, three
days, every intermediate object displayed in exact rationals. Stage B is the one
to read — the active value specification moves from `v0` to `v1` while the
injunction standing is untouched and still compiles to `v0`'s thresholds.

## Contents

- `VERTICAL_SLICE.md` — the specification. §7 is the compiler, §11 is the
  traderization boundary and the inertness dichotomy, §13 is what is not shown.
- `FINDINGS.md` — the research report. §6 is the central result, §10 is
  *what the end-to-end build taught us*.
- `SETTLEMENT_SEMANTICS.md` — whether the settlement ledger can feed the LI
  epistemic substrate, audited against the pinned definitions.
- `EXPRESSIVENESS.md` — twenty expressiveness cases, classified.
- `TRACE.txt` — the trajectory, regenerate with `python3 src/trace.py TRACE.txt`.
- `src/` — `li.py` (the pinned LI objects), `epistemic.py` (`sem_L`, `Sigma`,
  worlds), `waist.py` (both waists and `kappa`), `standing.py` (the RI
  installation), `conflict.py` (Fourier-Motzkin with Farkas provenance),
  `geometry.py`, `pipeline.py`, `toy.py`, `variants.py`, `trace.py`.
- `tests/` — 107 cases. `python3 tests/run.py`.

## What the tests cover

| file | what it checks |
|---|---|
| `test_compilation.py` | `E_n(X)` is the precision-`n+1` bundle; row slack equals the inequality's own value; shared coordinates merge; one frozen payload compiles at three dimensions to one condition |
| `test_value_waist.py` | semantic stability, historical rigidity, non-exposure, plural value without scalarisation, several active specifications, origin-blindness downstream |
| `test_operative_waist.py` | the five malformed payload classes; projection exactness; no invisible force or weakening; provenance to the issuing event |
| `test_conflict.py` | the four conflict states; certificates naming the responsible standings; certificates rechecked and tampered ones rejected; the budget raised rather than ignored |
| `test_composition.py` | channel independence; the intersection; the inertness dichotomy on every case; settlement lowering the charge to zero |
| `test_settlement.py` | `Sigma` as a legal `DeductiveProcess`; `sem_L` total and rigid; raw outcomes removing no world; contradictions attributed not repaired; unrelated growth changing nothing |
| `test_toy.py` | RI holds at every state; value revision is not operative revision; explicit operative revision; the full provenance chain; deterministic replay against the committed trace |

## What this does not establish

`FINDINGS.md` §9 carries the list. In short: no Lean and no registered claim; the
inertness dichotomy is a paper derivation checked on finite instances rather than
mechanized; effective presentation and `Sigma`'s computability are declared, not
proved; and the safety condition every contentful injunction now depends on is
established for nothing.
