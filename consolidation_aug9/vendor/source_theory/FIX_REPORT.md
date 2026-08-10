# T1 fix — NL-J2' core-certificate repair

A soundness fault in the jump-tightening module delivered in the closing phase,
repaired. Scope: `src/joint_tightening.py`, its tests, and the affected ledger
rows. Nothing else was touched.

## The fault, reproduced before repair

`retains_certificate` tested bare-point admission,
`change.after.admits(incumbent_reference)`. The certificate the frozen cap
assumes is the fixed-core condition `q + theta(P - q) subset S`. These come
apart, and the module as delivered returned:

```
theta = 1/10, q = 3/5, base x >= 1/2, change adds x >= 3/5
bare point admitted   : True
module says retains   : True
module zero_jump      : 0        <- unsound
core lower end 27/50 in region : False
forced q' >= 2/3, real charge  : 2/15
```

So `NL-J2'`'s conclusion was false as stated, `tightening_count` undercounted
`m*`, and the cap at `caps[m*]` was breachable by chaining such changes.

A second fault: `tightening_count` judged every change against the **initial**
incumbent rather than the incumbent in force at that change — wrong in both
directions once the reference has moved.

Both were reproduced against the shipped module before any edit.

## What changed

- **F1.** `retains_certificate` is replaced by `retains_core_certificate(change,
  incumbent, theta, vertices)`, which checks every vertex of the shrunk simplex
  `q + theta(v - q)`. The region is an intersection of half-spaces hence convex
  and the core is the convex hull of those vertices, so vertex checking decides
  inclusion. A module-level note records that bare-point admission is **not** the
  certificate, with the counterexample inline. `NL-X6`'s content — `S subset S'`
  preserves inclusion, so deactivations and suspensions retain — is now a test,
  not a remark.
- **F2.** `tightening_count` and `tightened_cap` take a finite recorded
  trajectory of `RecordedChange(change, incumbent_before)` pairs read from public
  history. No compiler policy is invented and no successor reference is
  synthesized; successors are input. Monotonicity in the history is retained and
  tested over prefixes.
- **F3.** The test that enshrined the wrong predicate is inverted into the
  point-survives-core-dies witness, with the verified numbers, and carries a new
  ledger row `NL-N-J2a` as a **NECESSITY WITNESS** — it shows the core condition
  is needed in the retention predicate.
- **F4.** The mild fixture is tested at both `theta = 1/10` (retaining) and
  `theta = 1/2` (invalidating), with the crossover exact at `theta = 1/6` where
  `q(1-theta) = 1/2` precisely. Retention is recorded as a `theta`-relative
  property, not a shape property: the change is constraint-adding at every
  `theta`.
- **F5.** The lemma and the `NL-J2'` row name `theta` and the core condition
  explicitly. The separation is restated as **core-invalidating vs
  constraint-adding**, replacing the closing phase's "point-excluding vs
  constraint-adding", which was the unsound framing.
- **F6.** `PatronFenceTests` and its imports moved above the `__main__` guard;
  collected count unchanged at 19.

## Prediction scores

- **P-F1 — CONFIRMED.** The showcase classification is unchanged: the
  deactivation retains under the corrected predicate (its after-region drops a
  constraint, so both core vertices survive), and the displayed tightening
  `x >= 4/5` excludes even the bare point at `q = 3/5`, so it still counts.
  `m* = 1`, `Psi_0 = 2`, and the headline constants survive **verbatim**:
  `321/10 -> 31/10`.
- **P-F2 — CONFIRMED.** The mild fixture at `theta = 1/10` is still retaining:
  core `[27/50, 32/50]` sits inside `x >= 1/2`. Same verdict, corrected reason —
  previously it passed because the bare point was admitted, which was accidental.
- **P-F3 — CONFIRMED.** At `theta = 1/2` the same fixture is core-invalidating
  (core lower end `3/10 < 1/2`), and the crossover is exact at `theta = 1/6`,
  where `(3/5)(5/6) = 1/2` and the weak inequality still admits.

The P5 scope sentence from the closing phase survives the fix unchanged: the
improvement is strict on any trace containing a core-retaining change, and
vanishes otherwise.

## Test count

224 before this fix, **227 after** (+3 in `test_joint_tightening.py`: 12 -> 15).
`test_case_stream.py` unchanged at 19. Full packaged suite green, pinned digests
verified, frozen files byte-identical, downstream rename roundtrip after
discovery.

## What this does NOT show

- **The fix tightens a predicate and a count.** It makes no behavioral,
  convergence, or learning claim, and changes what no policy does.
- **The extensionality cost is inherited, not resolved.** It is now *more*
  explicit: `m*` is counted against a recorded trajectory read from public
  history, which is exactly the dependence `C-PROV-IRR` concedes. Making it an
  input type is honesty about the cost, not payment of it.
- **`NL-J2'-B` is untouched.** It is pure `theta` arithmetic — attained factor
  `(1-theta)/theta` against the recursion's `1/theta` — and no part of the core
  repair bears on it.
- **Higher-dimensional sharpness stays open.** Everything verified here is the
  one-dimensional fixture with `P = [0,1]`; the vertex formulation is written for
  general finite `P` but only the scalar case is exercised.
- **No claim that the corrected predicate is the weakest sound one.** It is
  sufficient and its necessity is witnessed only for the core condition itself
  (`NL-N-J2a`), not for the vertex formulation against alternatives.
