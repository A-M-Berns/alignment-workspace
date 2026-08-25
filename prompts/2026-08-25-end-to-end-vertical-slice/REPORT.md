# Report — the end-to-end vertical slice

Attribution: prompt author unrecorded (authored outside this repository);
executor Claude Opus 5 (Anthropic); dispatched and executed 2026-08-25.

## Verdict

```text
END-TO-END-WITH-LOCAL-REPAIRS      (primary)
TRADERIZATION-MISMATCH             (second label)
```

The slice runs. `projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/`
carries the specification, the report, the reference model, 107 tests and a
committed trace of the canonical trajectory. Both waists carried every case
constructed against them and neither was widened.

The second label is why this is not `END-TO-END-READY`, and it is the round's
main finding: the unconditional traderization theorem's admissibility hypothesis
is satisfied *exactly* by injunctions that change nothing about the prices, so
every contentful injunction needs the charged branch, whose safety condition is
established for no source in this repository.

## The four local repairs

1. **The vertical-slice projection is the graph, not the image.** RI §35 gives
   `O_t = { compiledClause p : ... }`. Two active standings with equal payloads
   collapse in it and no member resolves to an event; enforcement provenance and
   per-term conflict attribution both need the identity. The slice consumes
   `O_n = {(i, J_i)}`. No store, constructor or conservation law changes.
2. **`sem_L` is a third parametric interpreter**, alongside `[[.]]_S` and
   `[[.]]_D`, with assumptions E1 (rigidity), E2 (finiteness) and E3
   (computability). Monotonicity of `Sigma` is then a theorem, not an assumption.
3. **The compiler merges coefficients on shared threshold sentences.** Two LUVs,
   or a `Prob` term, can name the same sentence, and `RationalConstraintSchedule`
   carries `nodup`.
4. **The stage's threshold chain must cover every day's grid.** The grid moves
   with `n` and the stage does not; an uncovered threshold is an unconstrained
   atom and admits worlds in which a LUV has no reading as a number.

## Deviations from the prompt

1. **§5 asked for a `PInjunction(J)` standing extension; the round uses
   `PForce`.** Reflective Integrity already has
   `PForce (commitRef, schemaRef, compiledClause : Clause)`, `Clause` is already
   opaque, and `O_t` is already its projection. Adding `PInjunction` would have
   duplicated an existing payload and made `O_t` read two constructors where it
   reads one. Consequence recorded rather than hidden: `PForce` carries two
   reference fields inside the payload, which §5 says justification should not
   be encoded in. They are inert — `kappa` reads `clause` and nothing else — and
   a test pins that.

2. **§2's `L ∈ Ext(L_min(V))` was not needed in the strong form.** Nothing in
   the pipeline requires an LI sentence meaning a reason. Reasons are consumed by
   `basis(a) = ReasonLeaves(D_a)`, which compares identifiers; the compiler never
   sees `V`. What `L` must code is the value layer's query vocabulary and the
   settlement layer's readings, and ordinary effective coding suffices for that.
   The round states what it used rather than formalizing more, per §2's own
   instruction not to overengineer, and files the untested question.

3. **§13's nonconvex permissibility is not a waist question.** It is refused by
   the execution layer's geometry — `K^N` is an intersection of half-spaces,
   `K^D` a convex hull, and the schedule's region a `RationalPolytope`. The
   classification table says so rather than reporting a waist failure.

4. **§14's return path is described, not built.** The five pressure conditions
   are computed by the forward run and the report states what the interface must
   consume and emit, but no inquiry machinery is written.

5. **The reference model is finite and propositional.** Sentences are
   propositional formulas and LUVs are threshold families over atoms. The
   first-order content the pinned dependency itself discloses as a modelling
   choice is not reconstructed.

## Structural friction found

`tests/name_lint.py` cannot distinguish a bibliographic citation of a third
party's published work from naming the program after a person. Addendum 2 asked
for a prior-art note citing an author who is also a maintainer of this
repository, and the gate rejects it. The note ships with that one surname in
backticks — the gate's own allowance — and the friction is filed under
`PRIORITIES.md` *Workspace friction*. The fix would change a gate's matching
logic, which is spec-layer and retroactive, so it is left to the maintainer
rather than taken by this round.

## Items filed

Five `PRIORITIES.md` items, within this round's scope, named in the ledger:
the liability gap that the inertness dichotomy creates, the Lean port of the
dichotomy, the effective-presentation obligation, the inquiry interface's
consumed type, and the name-lint friction.

## Outstanding maintainer actions

1. **Rule on the primary verdict's consequence for the programme's next step.**
   The round recommends that the next research step is *not* expanding the toy
   but establishing or refuting a summable-liability condition for some
   normative source, because the inertness dichotomy makes every contentful
   injunction depend on one. The decision turns on external knowledge the round
   lacks: whether a paper or a collaborator needs the toy expanded first.
   Recorded in `DECISIONS.md` *Awaiting the author*.

2. **Naming ruling, batched.** New provisional names introduced:
   `value waist`, `operative waist`, `cognitive waist`, `certified LUV`,
   `non-exposure`, `value specification`, `injunction`, `settlement reading`,
   `raw outcome`, `settlement semantics` / `sem_L`, `stage entry`,
   `inertness dichotomy`, `deductively inert`, `exclusion depth`
   (reused from the traderized-enforcement round), `compiled row`. None is
   identified with an existing workspace term. No Lean identifiers or wiki
   vocabulary are affected yet, so this does not enter the queue as an item.

3. **Decide whether `tests/name_lint.py` should exempt citation contexts.**
   Filed as friction; the fix is spec-layer and this round did not take it.

## What this round does not establish

The round directory's `README.md` and `FINDINGS.md` §9 carry the full list. The
three that matter most: nothing is Lean-checked or registered; the inertness
dichotomy is a three-line paper derivation checked on finite instances rather
than mechanized; and the safety condition every contentful injunction now
depends on is established for nothing.
