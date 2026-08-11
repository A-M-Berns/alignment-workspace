# Φ-law learner: verification register

## Verdict

**Learning-positive, integration-blocked.** The theorem-faithful learner exists
on the frozen bridge and the recurrent-failure consequence applies to its
expected mixed actions. Its chosen repository responses pass the extant
answerability and response-service checks. The architecture does not declare a
work budget or historical record for the learning computation itself.

## Source construction

**Source-theorem fact.** Section 7 of Blum and Mansour (2007), Theorem 18, uses
one external-regret algorithm for every source action. With the always-on
selector (`M=1`) and the audited programs (`K=9`), this gives weights

`w[j, phi]`, for `j in Lambda` and `phi in Phi_law`.

At round `t`, row normalization gives

`Q[j,i] = sum_{phi: F_phi^t(j)=i} w[j,phi] / sum_psi w[j,psi]`.

The learner chooses any stationary distribution `p = pQ`. The row loss is

`ell_H,j = sum_phi q[j,phi] ell_t(F_phi^t(j))`,

and the source exponential update is

`w'[j,phi] = w[j,phi] beta^(p[j] (ell_t(F_phi^t(j)) - beta ell_H,j))`.

`src/phi_learner.py` implements exactly these objects with 8 rows and 9 weights
per row. It does not substitute multiplicative weights over the nine programs.

## Arithmetic and stationary selection

**Implementation fact.** The source update is not rationally closed: a real
`beta` is raised to a generally rational exponent. The implementation therefore
uses a declared `Decimal` precision (80 digits by default), with

`eta = sqrt(8 ln(9) / T)` and `beta = exp(-eta)`.

This is a horizon-tuned, asymptotically suitable parameter, not a claim that a
rounded value is the exact real optimizer. After every numerical update, each
finite decimal weight is interpreted exactly as a rational. The transition
matrix and stationary vector are then computed with `Fraction` arithmetic for
those represented weights.

Reducible matrices are handled deterministically. The selector decomposes the
support graph into closed communicating classes, solves the unique stationary
vector inside each class, computes exact transient absorption probabilities,
and combines them using a uniform initial distribution. This is the uniform-
start Cesàro-limit stationary distribution. Tests cover identity matrices,
multiple recurrent classes, transient absorption, degeneracy, and exact `p=pQ`.

**Numerical-control evidence.** Re-running the `T=24` impediment experiment at
50 and 90 decimal digits changes cumulative charge and maximum regret by less
than `1e-40`. This is stability evidence, not proof of equality to real
arithmetic.

## Theorem hypotheses

| Theorem 18 interface | Frozen instantiation | status |
|---|---|---|
| fixed finite actions `N` | item-29 semantic alphabet `Lambda`, `N=8` | Lean-proved bridge + exact tests |
| modification rules `F^t(history, action)` | nine fixed causal declarative lawful programs | finite audit + exact tests |
| selector family `M` | always-on selector, `M=1` | definition |
| comparator count `K` | `K=9` | exhaustive class check |
| full information | all eight occasion-local charge values are computed | exact test-supported |
| bounded loss | charge lies in `[0, ell_max]`, `ell_max=2` | exact test-supported |
| stationary mixed action | exact selector for represented positive weights | exact test-supported |
| row-conditioned external learners | 8×9 weights and source update | implementation + tests |
| causal history | actual strict pre-action public reason context | inherited finite audit |
| additive loss | frozen filings/reasons, no suspension or solvency coupling | boundary check + negative suspension test |

The frozen boundary also retains one occasion per date, service window 4,
canonical responses, no post-hoc affordability deletion, and no profit-based
comparator filtering.

## Bound actually justified

**Source-derived theorem.** Theorem 18 plus the proved item-29 bridge gives a
horizon-tuned real-arithmetic learner whose expected mixed-action charge regret
against every member of the nine-program class is

`O(ell_max sqrt(8 T log 9))`.

The source proof, at the implementation's declared `beta`, yields the displayed
finite worst-case bound

`ell_max * ((1/beta - 1) T + 8 ln(9)/(beta ln(1/beta)))`.

Every numerical run lies below that bound. The finite bound is loose at the four
small horizons. The implementation is controlled numerical evidence for the
source learner; it is not a machine proof that Decimal trajectories equal the
ideal real trajectory.

The guarantee concerns `sum_t p_t · ell_t`, the expected loss of each mixed
action. Sampled histories in this round test repository integration only. No
concentration, high-probability, or realized-path regret theorem is supplied.
The learner is horizon-tuned; no doubling or anytime theorem is claimed.

## Experiments

**Numerical experiment.** `EXPERIMENT_RESULTS.md` reports all three policies,
all nine programs, and `T in {12,24,48,96}` on three fixtures.

- `persistent_interval` gives uniform policy linear repair regret `T/4`, while
  the Φ learner selects common fixed behavior and has zero regret.
- `impediment_pressure` forces nontrivial row learning: maximum regret is
  `2.879, 4.023, 5.572, 7.748`; regret per round is
  `0.240, 0.168, 0.116, 0.081`.
- `fully_licensed` exercises interval, toll, and ripeness grounds together.
- action Hedge is a control, not a substitute theorem. It often lowers charge,
  but external action regret does not compare history-dependent repairs.

The persistent fixture is also a necessity witness: at `T=96`, Φ regret is zero
at charge 48 while action Hedge has charge about 9.782. A weak comparator class
can certify no profitable represented transformation while missing cheaper
behavior.

## Recurrent-failure consequence

**Lean-proved upstream + derived consequence.** The item-29 bridge proves that
if one fixed lawful program saves at least `delta` on source labels receiving
total expected mixed mass at least `rho T`, up to distortion `B`, then

`R_T(phi) >= rho delta T - B`.

Combining this with the source `o(T)` expected regret guarantee rules out positive
asymptotic expected mass on a represented, uniformly saving, admitted repair.
The impediment experiment exhibits the finite pattern: positive-saving mass for
`toll_declines_4` grows much more slowly than `T`, while uniform play retains
linear regret.

This does not imply eventual correctness, moral correctness, convergence to a
unique state, correction outside the nine programs, or realized-path frequency.

## What is and is not constructed

Constructed: the theorem's row-conditioned learner, deterministic stationary
selection, numerical arithmetic boundary, full comparator tables, exact
repository charge preservation checks, sampled answerability witnesses, and a
precise integration obstruction.

Not constructed: an exact-real executable proof, sampled-path theorem, anytime
learner, richer comparator language, or a service-priced and historically
recorded learner-state transition.
