# Item 30 report — construct the lawful Φ-regret learner

**Verdict: Learning-positive, integration-blocked.**

## Result

The frozen `N=8`, `M=1`, `K=9` bridge supports a concrete implementation of
Blum and Mansour (2007), Theorem 18. The learner maintains 72 source-action /
program weights, builds the transformation-weighted stochastic matrix, selects
a stationary mixed action, receives the full eight-action charge vector, and
performs the theorem's row-conditioned update.

The actual executable uses high-precision real approximation where the source
algorithm is inherently real-valued. Its finite Decimal weights are converted
to exact rationals for the transition matrix and stationary solve. Reducible and
non-unique cases use the exact uniform-start Cesàro-limit stationary selection.
No exact-real identity is claimed.

The source theorem plus the item-29 preservation bridge justifies a horizon-
tuned ideal learner with expected mixed-action charge regret

`O(ell_max sqrt(8 T log 9))`.

The implementation uses `eta=sqrt(8 ln(9)/T)`, `beta=exp(-eta)`. The finite
source-proof bound reported for that beta is

`ell_max ((1/beta-1)T + 8 ln(9)/(beta ln(1/beta)))`.

This is expected mixed loss, not realized sampled-path loss. No concentration or
anytime result is added.

## Experiments

All nine programs are reported at every horizon `T in {12,24,48,96}`:

1. `identity`
2. `repair_declines`
3. `repair_declines_even`
4. `repair_declines_odd`
5. `toll_declines_1`
6. `toll_declines_2`
7. `toll_declines_4`
8. `default_declines`
9. `withdraw_merits`

The complete tables are in `EXPERIMENT_RESULTS.md`. On
`impediment_pressure`, uniform maximum regret is `7.5, 15, 30, 60`; the
Blum--Mansour learner's is approximately `2.879, 4.023, 5.572, 7.748`.
Its maximum regret per round falls from approximately `0.240` to `0.081`.
These are numerical experiments, not verification of big-O from four points.

The external-action Hedge baseline often achieves lower charge, but does not
control regret to history-dependent lawful modification rules. Conversely, the
`persistent_interval` witness shows that zero regret against the nine programs
can coexist with charge `T/2`; at `T=96`, action Hedge's charge is about 9.782.
This kills any reading of the result as general charge minimization or adequate
comparator coverage.

## Recurrent failure

The bridge's Lean-proved inequality says that expected mixed mass `rho T` on
labels for which one admitted fixed repair saves at least `delta`, up to bounded
distortion `B`, forces regret at least `rho delta T-B`. Combined with the cited
`o(T)` guarantee, the learner cannot retain positive asymptotic expected mass on
a represented, uniformly remediable failure. Nothing pathwise follows here.

## Answerability and service

Sampled actions decode to ordinary canonical responses. Across all `T=96`
fixtures the histories are well formed, identity-replay faithful, contain no
burden drops or retargets, and remain feasible under response service capacity.
Comparator lawfulness still uses the fixed declarative non-capturing class; the
learner's charge feedback never becomes a legality input.

Full integration fails. `ServiceCosts` prices only response dispositions. It
does not price the 72 weight updates, matrix construction, or stationary solve,
and `ActualHistory` does not record learner-policy state. Treating these as free
would not establish the bounded answerability/service conjunction. The next
task is therefore a learner-state/work interface, not another regret experiment.

## Evidence classes

- **Source-theorem fact:** the reduction and expected mixed-loss bound.
- **Lean-proved upstream:** representation/regret preservation and recurrent-
  failure lower bound.
- **Exact-test-supported:** dimensions, transition construction, exact
  stationarity for represented weights, decode/charge equality, frozen-boundary
  rejection, sampled answerability checks.
- **Finite audit:** comparator non-capture for exactly nine programs.
- **Numerical experiment:** learner trajectories, regret tables, precision
  comparison, and baseline comparisons.
- **Open:** exact-real executable identity, sampled-path guarantee, anytime
  tuning, service-priced learner state, and richer comparator coverage.

## Deviations and limitations

- No Lean file was added: the stable representation and recurrent lemmas already
  exist; encoding the Python numerical solver would not strengthen the theorem.
- The source-optimized real parameter was not silently rounded. A declared
  horizon-tuned parameter and its actual source-proof bound are reported.
- No doubling trick was implemented; this remains a horizon-tuned learner.
- No comparator was added beyond the frozen nine.
- `DECISIONS.md` and all deference research artifacts are unchanged.

## Verification

- `python3 projects/leverage/rounds/2026-08-11-phi-regret-learner/tests/run.py`:
  **20/20 passed**.
- `python3 tests/run.py`: **all green**, including all six project runners,
  gate self-tests, name lint, conservativity, sorry gate, and axiom discipline.
- `lake build`: **completed successfully (2,634 jobs)**.
- `python3 tests/audit_axioms.py`: **182 results across 13 files**, all within
  `Classical.choice`, `Quot.sound`, and `propext`.
- `git diff --check`: clean before commit.
- PR-context DCO, attribution, and path gates are checked after the signed commit
  and push.

## Human review surfaces

1. `src/phi_learner.py`: source update and stationary selection.
2. `PHI_REGRET_LEARNER.md`: theorem/implementation boundary and finite bound.
3. `EXPERIMENT_RESULTS.md`: complete numerical results.
4. `ANSWERABILITY_SERVICE_AUDIT.md`: why the top-level verdict is blocked.
5. `PRIORITIES.md` and `RESEARCH_STATE.md`: partial closure wording.

## Outstanding action

Define and verify an answerable learner-state transition with declared work for
the 72 updates and stationary computation, or explicitly adopt an oracle
boundary that removes computation from the bounded-service claim. Separately,
future research must test whether nine hand-selected repair programs are rich
enough to support a robust normative-self-correction interpretation.

## Source

Avrim Blum and Yishay Mansour, “From External to Internal Regret,” *Journal of
Machine Learning Research* 8 (2007), especially §7 and Theorem 18.
