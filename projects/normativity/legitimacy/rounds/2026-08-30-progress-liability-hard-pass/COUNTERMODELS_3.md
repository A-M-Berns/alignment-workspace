# Liability countermodels and boundary fixtures

All new numerical checks are exact rationals in `src/joint_margin.py` and
`tests/test_joint_margin.py`. PR50 market outcomes are cited at its open head and keep
their `model-supported` grade.

## Classification key

- **proves:** the Common-Mixture theorem applies.
- **silent:** a theorem hypothesis fails and no conclusion is drawn.
- **refutes:** the trace falsifies a candidate implication.

## CM1 — centered binary point peg

Settlements are `0,1`, `K={1/2}`, and the unique compatible mixture is
`(1/2,1/2)`. Coverage is `theta=1/2`, so current LI constants give liability at most
`3`. This proves tolerance-independent bounded liability without a homothetic core.

- common mixture: **proves**;
- “positive homothetic core is necessary”: **refuted**;
- PR50 direct result: separately model-supported.

## CM2 — near-vertex binary point peg

For `K={epsilon}`, the unique compatible mixture is `(1-epsilon,epsilon)` and
coverage is `epsilon` for `epsilon<=1/2`. The bound is

\[
3(1-\epsilon)/\epsilon.
\]

The inverse-margin scale is unavoidable under only mixture value and pointwise upper
cap: the algebraic sharpness fixture attains it.

- common mixture: **proves boundedness for each fixed epsilon**, with the correct
  divergence as `epsilon -> 0`;
- uniform-in-epsilon coverage: fails.

## CM3 — two individually affordable coordinates with self-financing subsidy

PR50 fixes phi at `[2/5,3/5]` and alternates psi between `[1/10,1/5]` and
`[4/5,9/10]`. A single ordinary component pumps psi and drains its gains against phi;
authority liability grows geometrically in the exact market model.

- separate row affordability: **refuted as a composition rule**;
- no-cross-coordinate-subsidy: fails;
- one mixture compatible through time: fails.

## CM4 — two stationary coordinates with a common mixture

Take four binary worlds uniformly, and any stationary joint region containing mean
`(1/2,1/2)`. Coverage is `1/4`; the theorem gives authority liability at most `9`.
The sharp abstract value vector `(-9,3,3,3)` has mixture value zero, showing the
constant cannot be improved without more structure.

- common mixture: **proves**, even with ordinary cross-coordinate trading;
- coordinate account separation: unnecessary.

## CM5 — separate coordinate mixtures but no joint mixture

Assessed profiles are `(0,1)` and `(1,0)`. Coordinate 1 can separately have mean
`3/4`, and coordinate 2 can separately have mean `3/4`, each with coverage `1/4`.
Every joint mean satisfies `v_1+v_2=1`, so no one mixture has both coordinates at
least `3/4`.

- coordinatewise compatibility implies joint compatibility: **refuted**;
- common-mixture theorem: silent.

## CM6 — nonempty normative region outside the settlement hull

Assessed profiles are `(0,0),(1,0)` and `K={(1/2,1/2)}`. `K` is nonempty and inside
the cube but disjoint from the settlement segment.

- syntactic nonemptiness implies affordability: **refuted**;
- value compiler obligation failing: settlement compatibility.

## CM7 — compatibility without uniform coverage

On binary settlements let `K_n={1/n}`. Every finite date has a full-support mixture,
but its minimum mass is `1/n`. No uniform `theta>0` exists.

- per-date full support implies uniform liability: **refuted**;
- fixed-episode theorem: silent across the schedule;
- near-vertex blow-up is correctly predicted.

## CM8 — several repair sources with one target

For one-hot profiles on `{x_1,x_2,y}`, use mixture mean `(1/5,1/5,3/5)`. Both
directions `y-x_i` have gain `2/5>=1/5`; coverage is `1/5`.

- finite Answer-Mode common-target realization: **proves**;
- dimension appears only through coverage.

## CM9 — cyclic repair directions

Rows `v_1-v_0>=1/4` and `v_0-v_1>=1/4` sum to `0>=1/2` and make `K` empty.

- feasibility screen: correctly rejects;
- liability theorem: not reached;
- “repair directions automatically compatible”: **refuted**.

An acyclic row is not enough either: if assessed profiles are only `(0,0),(1,1)`,
all mixtures have zero difference and cannot satisfy `v_1-v_0>=1/2`.

## CM10 — time-multiplexed scalar constraints

PR50's low/high psi eras are individually compatible with product mixtures of minimum
world mass `3/40`. Their intervals are disjoint, so no fixed expectation satisfies
both. Repeated fair switching is exactly a non-summable temporal recharge path.

- per-date mixture plus fair rotation implies bounded liability: **refuted**;
- common mixture: silent for exactly the intended reason.

## CM11 — stationary `K`, moving plausible region

Let `K={1/2}`. While both binary worlds are live, the centered mixture works. After
the plausible set collapses to the false world, every supported barycenter equals
zero and compatibility fails although `K` did not move.

- stationary region alone implies persistent affordability: **refuted**;
- the relevant motion is the pair `(K, plausible region)`, matching PR50's diagnosis.

## CM12 — summable set-gap motion

Let singleton regions have means

\[
c_n=1/2+2^{-(n+2)}.
\]

Their total movement is finite and every date has coverage at least `3/8`, but the
singletons have no common point. The Common-Mixture theorem is silent. PR50 suggests
such motion can be affordable in one dimension, but that remains model-supported,
not proved by this pass.

- summable motion implies common mixture: **refuted**;
- summable motion implies bounded liability: **open outside PR50's model fragment**.

## CM13 — eventual evaluator contradiction

An enforced descriptive row says `v(y)-v(x)>=gamma`, but the surviving future
evaluator world settles `V_y=0,V_x=1`. Once only that world remains plausible, no
compatible mixture exists and historical authority inventory may be billed.

- descriptive settlement automatically respects normative rows: **refuted**;
- fresh evaluator account erases liability: **refuted by accounting identity**;
- direct certified-loss realization: unaffected.

## CM14 — world inclusion

If every live settlement profile lies in every `K_n`, every authority day has
nonnegative value at every assessed world. `ProjectionBudget` gives exact zero
liability.

- zero-liability theorem: **proves**;
- semantic legitimacy: not inferred; it depends on security type.

## CM15 — recycling coefficient near threshold

Let coverage `theta=1/4`, pointwise authority upper bound `U=3`, and potential slack
`S=1`. The closure lemma gives

\[
L\le\frac{13/4}{1/4-\kappa}.
\]

It equals `13` at `kappa=0`, `26` at `kappa=1/8`, and has no finite conclusion at
`kappa=theta`. This fixes the normalization and threshold exactly.

- `kappa<theta`: **proves algebraic closure**;
- schedule-local derivation of such a `kappa`: open;
- PR50 pump: because liability is unbounded with fixed `U`, it necessarily violates
  every uniform `kappa<theta` certificate for the chosen potential.

## Additional failed repairs

### Separate authority accounts

Summing ledgers recovers the original aggregate loss. Ordinary trader wealth remains
global. No theorem hypothesis changes.

### Separate Budgeter components

PR50's patsy fixture shows other components can transfer a finite aggregate war chest;
its self-financing pump shows authority losses can recharge one component without
breaching its nominal floor. Separate component names are not fencing.

### Small tolerance

None of CM3, CM7, CM10, CM11 or CM13 is repaired by smaller tolerance. Their problem
is settlement/potential geometry and accumulated opposing capacity.

