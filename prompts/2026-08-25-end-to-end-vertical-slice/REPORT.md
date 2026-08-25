# Report — the end-to-end vertical slice

Attribution: prompt author unrecorded (authored outside this repository);
executor Claude Opus 5 (Anthropic); dispatched and executed 2026-08-25, in two
passes against the same branch.

## Verdict

```text
END-TO-END-DEMONSTRATION-CLOSED-WITH-OPEN-SAFETY-THEOREM
```

The slice runs from settlement and reasons through normative standing, value
exposure and operative force to a region, a live-world deficit certificate, a
charge, an account debit, and only then a price.
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/`
carries the specification, the report, the reference model, 135 tests and a
committed trace.

Answers to the four closeout questions:

1. **The waists are provisional-but-usable, not canonical.** Nothing constructed
   against them forced either to widen. The round does not recommend freezing.
2. **The charged traderization path is exercised end to end.** The slice imports
   the traderized-enforcement round's `outflow`, `force_api`, `enforcement` and
   `deduction` and calls them; it computes no liability quantity of its own.
3. **The remaining theorem is item 61**, restated: does a plausible normative
   source with a settlement trajectory satisfy
   `sum_t (eps_t + M_t) D_t / delta_t < inf`, with `D_t` the sharp aggregate for
   the exact day-`t` compiled request? Three obstructions are now known and
   recorded on the item.
4. **The next pass should be item 61, not inquiry.** This is read off the run
   rather than from preference: §5 below says why the inquiry socket cannot be
   specified until the summability question has an answer, because the only
   pressure signal the forward run supports is a property of the charge history.

## The second pass

The first pass shipped a defect the follow-up dispatch identified correctly.

**The quantity was wrong.** The slice computed `sum_omega max_j d_j(omega)` over
the excluded worlds and called it the exclusion depth. The safety layer's sharp
aggregate is `max_omega sum_j d_j(omega)`; the two are different, and the first
number is not a quantity any theorem in the repository mentions. It is now
removed rather than renamed, the canonical implementations are imported and
called, and `test_safety.py` pins both that the billed figure is the
certificate's and that it differs from the withdrawn one.

**A conclusion rested on it and is withdrawn.** The first pass reported that a
fixed injunction gets cheaper as the record settles. The repaired run separates
three claims: fixed-request monotonicity holds and is the only monotonicity
available; the cross-day version is false, with a counterexample; and the charge
is not the deficit. The counterexample is that the precision-`k` reading of a
value is `ceil(x*k)/k`, which is not monotone in `k`, so one frozen injunction
against one stage gives `D_1 = 0` and `D_2 = 1/6` — and still rises when the
day-2 stage is made strictly larger.

Two further facts came out of the pressing: the charge is presentation-dependent
(a demand stated twice costs twice and enforces the same prices), and the
tolerance route to summability is bounded above by the only tolerance value that
keeps the promise meaningful.

## The four local repairs, from the first pass

1. **The vertical-slice projection is the graph, not the image.** RI §35 gives a
   set of clauses; enforcement provenance and per-term conflict attribution both
   need the standing identity. No store, constructor or conservation law changes.
2. **`sem_L` is a third parametric interpreter**, alongside `[[.]]_S` and
   `[[.]]_D`, with E1 (rigidity), E2 (finiteness) and E3 (computability).
   Monotonicity of `Sigma` is then a theorem.
3. **The compiler merges coefficients on shared threshold sentences**, which
   `RationalConstraintSchedule.nodup` requires.
4. **The stage's threshold chain must cover every day's grid**, or worlds appear
   in which a LUV has no reading as a number.

## Deviations from the prompt

1. **`PForce` rather than a new `PInjunction` standing extension.** RI already
   has `PForce (commitRef, schemaRef, compiledClause : Clause)` and `O_t` is
   already its projection; adding a constructor would have duplicated a payload.
   Consequence recorded rather than hidden: `PForce` carries two reference
   fields inside the payload, which §5 of the dispatch says justification should
   not be. They are inert — `kappa` reads `clause` and nothing else — and a test
   pins it.
2. **`L in Ext(L_min(V))` was not needed in the strong form.** Reasons are
   consumed by identifier comparison and the compiler never sees `V`. The round
   states what it used and files the untested question as item 65, per §2's own
   instruction not to overengineer.
3. **Nonconvex permissibility is not a waist question.** It is refused by the
   execution layer's geometry: `K^N` is an intersection of half-spaces, `K^D` a
   hull, and the schedule's region a `RationalPolytope`.
4. **The return path is described, not built**, per §9 of the follow-up.
5. **The reference model is finite and propositional.** The first-order content
   the pinned dependency itself discloses as a modelling choice is not
   reconstructed.
6. **`tolerance_route` and the trajectory harness run at most six days.** The
   geometry is exponential in the fragment size and the fragment grows with the
   day; six days is enough to display the tolerance ceiling being reached and
   the charge going constant. Stated because it is a coverage limit, not a
   result.

## Structural friction found

`tests/name_lint.py` cannot distinguish a bibliographic citation of a third
party's published work from naming the program after a person. Addendum 2 asked
for a prior-art note citing an author who is also a maintainer here. The note
ships with that surname in backticks — the gate's own allowance — and the
friction is filed under `PRIORITIES.md` *Workspace friction* as F6. The fix would
change a gate's matching logic, which is spec-layer and retroactive, so it is
left to the maintainer.

## Items filed

`PRIORITIES.md` items 61 through 65, and friction entry F6. Item 61 was
rewritten in the second pass to ask for the condition over a schedule of
presentations and to record the three obstructions.

## Outstanding maintainer actions

1. **Rule on the next step.** The round recommends item 61 ahead of expanding
   the toy, and answers the closeout question from the run: the inquiry socket
   cannot be specified until summability has an answer, because the only
   pressure signal the forward run supports is a property of the charge history
   rather than of any date. The round is still low-confidence on the *ordering*
   against external needs. Recorded in `DECISIONS.md` *Awaiting the author*.

2. **Naming ruling, batched.** Fifteen provisional names, listed in the pull
   request. `exclusion depth` was used in the first pass for a quantity that is
   not the corpus's and is withdrawn rather than renamed; the corpus's term keeps
   its sense. No Lean identifiers or wiki vocabulary are affected, so this does
   not enter the queue as an item.

3. **Decide whether `tests/name_lint.py` should exempt citation contexts.**

## What this round does not establish

The round directory's `README.md` and `FINDINGS.md` §9 carry the full list. The
four that matter most: nothing is Lean-checked or registered; the inertness
dichotomy is a paper derivation checked on finite instances; the cross-day
counterexample is a witness rather than a characterisation of when `D` rises;
and **no normative source is shown to satisfy the safety condition** that every
contentful injunction now depends on.
