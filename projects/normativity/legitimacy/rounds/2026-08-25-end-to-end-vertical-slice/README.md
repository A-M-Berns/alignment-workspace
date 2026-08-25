# The end-to-end vertical slice

Status: **specification and reference model; unregistered.** All names are
provisional under `AGENTS.md` §6. Nothing here is Lean-checked or registered.

## Verdict

END-TO-END-DEMONSTRATION-CLOSED-WITH-OPEN-SAFETY-THEOREM — the charged traderization path runs end to end on the canonical safety layer's own quantity, and no normative source is shown to satisfy the condition that path needs.

The pipeline runs from settlement and reasons through normative standing, value
exposure and operative force to a region, a live-world deficit certificate, a
charge, an account debit, and only then a price. Both waists carried every case
constructed against them and neither was widened; Reflective Integrity was not
reopened.

What is open is one condition, and it is now the right one. Every contentful
injunction falls outside the unconditional theorem — admissibility holds exactly
for injunctions that change nothing — so each must be paid for out of a finite
account, and `sum_t (eps_t + M_t) D_t / delta_t < infinity` is established for no
source here. Four synthetic trajectories are exhibited, two convergent and two
not.

**Are the waists canonical?** No. **Provisional-but-usable**, and the round does
not recommend freezing them. Nothing it could construct forced either to widen,
and the repairs are local and specified.

**Is the charged path exercised end to end?** Yes. `compile_safe_force` computes
`LiveDeficitCertificate.by_enumeration` from the region it is about to enforce,
charges, debits, and emits; a date the account cannot fund produces no force and
no price. The slice reimplements no liability quantity.

**What is the remaining theorem?** Item 61, restated to ask for the condition
above over a schedule of *presentations*, with the three facts the slice
established about it: `D_t` is not monotone across days, the charge is
presentation-dependent, and the tolerance route is bounded.

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

**Start with `ARCHITECTURE.md`.** It is the canonical account of what the round
built — the four kinds of thing, the reason multihypergraph, the settlement
projection into the LI substrate, the reflective schema loop, the three waists,
the charged boundary, and the minimal persistent state. The documents below
defer to it for what the objects *are*.

- `ARCHITECTURE.md` — the canonical architecture, with one signature block.
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
  `geometry.py`, `safety.py` (the charged branch, on the canonical objects),
  `pipeline.py`, `toy.py`, `variants.py`, `trajectories.py`, `trace.py`.
- `tests/` — 170 cases. `python3 tests/run.py`.

## What the tests cover

| file | what it checks |
|---|---|
| `test_compilation.py` | `E_n(X)` is the precision-`n+1` bundle; row slack equals the inequality's own value; shared coordinates merge; one frozen payload compiles at three dimensions to one condition |
| `test_value_waist.py` | semantic stability, historical rigidity, non-exposure, plural value without scalarisation, several active specifications, origin-blindness downstream |
| `test_operative_waist.py` | the five malformed payload classes; projection exactness; no invisible force or weakening; provenance to the issuing event |
| `test_conflict.py` | the four conflict states; certificates naming the responsible standings; certificates rechecked and tampered ones rejected; the budget raised rather than ignored |
| `test_composition.py` | channel independence; the intersection; the inertness dichotomy on every case and at its edges; presentation-dependence of the charge |
| `test_safety.py` | the billed quantity is the canonical sharp aggregate and not a clone; fixed-request monotonicity; the cross-day counterexample; four charged trajectories |
| `test_settlement.py` | `Sigma` as a legal `DeductiveProcess`; `sem_L` total and rigid; raw outcomes removing no world; contradictions attributed not repaired; unrelated growth changing nothing |
| `test_toy.py` | RI holds at every state; value revision is not operative revision; explicit operative revision; the full provenance chain; deterministic replay against the committed trace |
| `test_architecture.py` | the reason substrate is a multihypergraph whose edges carry identity; schema revision is ordinary supersession, including a schema retiring its own standing; the three graphs are disjoint; the persistent state is three components; the charged object is a presentation |

## What this does not establish

`FINDINGS.md` §9 carries the list. In short: no Lean and no registered claim; the
inertness dichotomy is a paper derivation checked on finite instances rather than
mechanized; effective presentation and `Sigma`'s computability are declared, not
proved; the cross-day counterexample is a witness rather than a
characterisation; and **no normative source is shown to satisfy the safety
condition** every contentful injunction now depends on.

One claim an earlier draft of this round made is withdrawn: that a fixed
injunction gets cheaper as the record settles. It is true at a fixed day and
false across days, and `src/trajectories.py` carries the counterexample.
