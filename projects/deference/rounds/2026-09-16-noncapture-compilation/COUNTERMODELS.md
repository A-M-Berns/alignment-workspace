# Countermodels and fixtures

**Status:** `ci-only`.  Every row is an exact finite model in `src/attacks.py`, evaluated
by `tests/test_steering.py`; the table is generated from `Fixture.report()` (values are
`fractions.Fraction`).  The declared interface carries `for` (a true reason for the
advisor's candidate, weight `+1/4`), `against` (a true counterreason, `−1/4`),
`p_against` (a true *protected* counterreason, `−1/4`) and `noise` (true, weight `0`);
`secret` is a true reason outside the declared interface; the prior is `1/2`; verdicts are
clamped to `[0,1]`.  The comparator is `N_full` (fully informed) unless the attack is a
form attack, where it is `N_form` (same content, canonical form).  `W = 1/4` is the unit
of advantage.  "Holds" says whether the hypothesis named in the row survives the attack;
**NO** marks the rows on which the literal two-interface thesis fails.

## 1. The minimal counterexample

Fixture 2.  Omit the unprotected true counterreason and nothing else.  Every clause of the
thesis holds (`test_all_clauses_hold_yet_steering_remains`: extensional program, audit
passes, every reason inside the declared interface, nothing late) and the advantage is
`W`.  Fixture 13 is the same attack with the advisor's reason additionally certified; it
changes nothing.  The two repairs, total scope
(`test_total_scope_repairs_the_counterexample`, `test_total_scope_forces_full_content`)
and a supplied reason (`test_supplied_reason_repairs_the_counterexample`), are not
interface properties (`REASON_INTERFACE.md` §3).

## 2. The table

| # | attack | hypothesis it tests | holds | advantage | `d_canon` | `κ` | `M` | `both` | bound |
|---|---|---|---|---|---|---|---|---|---|
| 1 | omit protected counterreason | coverage barrier | yes | −1/4 | 2 | 0 | 0 | 0 | 0 |
| 2 | truthful cherry-picking | scope totality (every declared reason protected) or a supply obligation | **NO** | 1/4 | 2 | 0 | 0 | 1 | 1/2 |
| 3 | adversarial ordering | canonicalization (extensional program) | **NO** | 1/4 | 0 | 1/4 | 0 | 1 | 1/4 |
| 4 | duplication | canonicalization (extensional program) | **NO** | 1/4 | 0 | 1/4 | 0 | 1 | 1/4 |
| 5 | framing metadata | canonicalization (extensional program) | **NO** | 1/4 | 0 | 1/4 | 0 | 1 | 1/4 |
| 6 | world-changing intervention | effect-side interface (the change is an effect, not a trace edit) | yes | 0 | 1 | 0 | 0 | 1 | 1/4 |
| 7 | undeclared reason | interface completeness (the program reads only declared ids) | **NO** | 1/4 | 0 | 1/4 | 0 | 1 | 1/4 |
| 8 | granularity | representation faithfulness at the declared granularity | yes | 0 | 1 | 0 | 0 | 1 | 1/4 |
| 9 | delayed past commitment | liveness (raised before the deadline) | **NO** | 1/4 | 2 | 0 | 0 | 1 | 1/2 |
| 10 | route open, never exercised in time | coverage barrier (voids); liveness is availability, not steering | yes | −1/4 | 2 | 0 | 0 | 0 | 0 |
| 11 | canonical program | canonicalization | yes | 0 | 0 | 0 | 0 | 1 | 0 |
| 12 | unproved claim | authentication | yes | 0 | 2 | 0 | 0 | 0 | 0 |
| 12b | forged certificate | authentication soundness (a false declared reason certified true) | **NO** | 1/4 | 2 | 0 | 0 | 1 | 1/2 |
| 13 | true but selective | scope totality or a supply obligation | **NO** | 1/4 | 2 | 0 | 0 | 1 | 1/2 |
| 14 | inquiry control | issuance authenticity (outside the trace interface) | yes | 0 | 0 | 0 | 0 | 1 | 0 |
| 15 | program overweights a true reason | program quality (not a capture failure) | yes | 0 | 0 | 0 | 0 | 1 | 0 |
| 16 | dynamics | declared log transform = causal counterfactual (EXT) | **NO** | 1/4 | 2 | 0 | 0 | 1 | 1/2 |

The identity and the bound hold on every row (`test_identity_and_bound_on_every_fixture`).

## 3. Row by row: which hypothesis fails

- **1 omit protected counterreason.**  Caught: the barrier voids the steered trace
  (`both = 0`), and the void is a loss for the advisor (`−1/4`).
- **2 truthful cherry-picking.**  Survives every clause; the advantage is the omitted
  reason's weight.  The missing hypothesis is scope totality or a supply obligation.
- **3 adversarial ordering.**  Content identical; an order-sensitive program pays exactly
  its form term.  Canonicalization (extensionality) is the hypothesis, and it is absent.
- **4 duplication.**  As 3, against a count-sensitive program.
- **5 framing metadata.**  As 3, against a frame-sensitive program.
- **6 world-changing intervention.**  Relative to the changed world the trace is fully
  informed; no reason-side advantage.  The intervention is an effect, for the effect
  interface (`d_canon = 1` is the weightless `noise`).
- **7 undeclared reason.**  The program reads an id outside the declared interface;
  `canon` cannot see it, so the charge lands on the *form* term, not on content.  This is
  what interface incompleteness looks like from inside the theory: an extensionality
  failure over the declared interface.
- **8 granularity.**  Two facts under one declared id give canonically identical traces;
  no quantity of the theory separates them; advantage `0` *as the theory measures it*,
  which is the failure.
- **9 delayed past commitment.**  The late unprotected reason does not count; no void;
  content discrepancy.  Liveness of *supply*, not of routes.
- **10 route open, never exercised in time.**  The late reason is protected: the barrier
  voids.  Robust Openness (a route exists) is availability, not exercise, exactly as the
  openness page states.
- **11 canonical program.**  Order, duplication and framing are free against an
  extensional program.
- **12 unproved claim.**  Authentication voids.
- **12b forged certificate.**  Authentication soundness fails: a false declared reason
  passes; it is content discrepancy against `N_full` at `L`.  (Added beyond the dispatch's
  sixteen: the dispatch's "authenticated false reason" splits into the unproved claim,
  which voids, and the forged certificate, which charges.)
- **13 true but selective.**  Fixture 2 with a certified reason; the certificate changes
  nothing.
- **14 inquiry control.**  With the menu fixed at issuance the full trace has no
  advantage; controlling *which* inquiry is asked is an issuance-authenticity question
  outside the trace interface.
- **15 program overweights a true reason.**  The fully-informed comparator has the same
  verdict; a bad program is not a capture failure and the theorem does not bound it.
- **16 dynamics.**  The comparator is a declared transform; the residual is real
  (`1/4`) and whether the transform is the causal counterfactual is external.

## 4. Sharpness and the free branch

- `test_mismatch_sharpness`: a steered trace carrying a protected reason its comparator
  lacks passes an audit the comparator fails; advantage `1`, bound `D·1 = 1`.  The
  coefficient `D` is sharp (`LICorrigibility.Witness.attained` applies verbatim).
- `test_reverse_mismatch_is_free`: a void steered trace against a passing comparator has
  negative advantage and bound `0`.
- `Witness.form_attained` (LEAN): the form branch is attained at `κ = 1/4`.
- `Witness.lipschitz_attained` (LEAN): the content-Lipschitz bound is attained at
  `L·|c Δ c'| = 1/4`.

## 5. Refuted stronger statements

| statement | refuted by |
|---|---|
| coverage + liveness suffice against truthful selective omission | fixtures 2, 13 |
| an extensional program is not needed once the interface is complete | fixtures 3, 4, 5 |
| an undeclared reason is charged to content | fixture 7 (charged to the form term) |
| a world-changing intervention is a reason-side residual | fixture 6 |
| granularity failures are visible to the theory | fixture 8 |
| Robust Openness as a causal claim is `Γ`-valid | fixture 16; only the declared-transform form is |
| the reason-side normalization is realizable by rewriting the advisor's outputs | fixture 2: the omitted content is not in them |
| "authenticated false reason" is one attack | fixtures 12 and 12b: it voids or it charges |
| the audit mismatch can favor steering against `N_full` or `N_form` | §4: `M` needs a comparator lacking a protected reason the steered trace carries, which neither log-side comparator can |
