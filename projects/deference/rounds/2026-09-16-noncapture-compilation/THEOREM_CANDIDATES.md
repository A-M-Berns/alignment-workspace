# Theorem candidates, with their verdicts

Labels: **LEAN** (sorry-free declaration in `lean/Workspace/Deference/Contrib/TraceSteering.lean`,
or, where named, in the landed corrigibility modules), **FIX** (exact fixture in `tests/`),
**PAPER** (a theorem of the Logical Induction paper at its exact statement), **EXT**, **OPEN**,
**REFUTED**.  Names are provisional (`AGENTS.md` standard 6).

Throughout: a committed principal program `π_P : ℛ → 𝒱` re-executed at commitment, so
the committed vector is `V(T) := π_P(T)` on the trace `T` the program was given; a
declared interface `I` of reason ids with settleable truth; a protected scope `Γ ⊆ I`;
the canonical content `canon(T) ⊆ I` (reasons present at commitment, withdrawn ones
removed); the form-normalized trace `N_form(T)` (canonical content in canonical order,
no metadata, no duplicates); the fully-informed comparator `N_full(T)` (every true
declared reason, canonical form); the audit `C(T)` (authentication, authorship, the
protected coverage barrier, timing).  The advisor's activated security for its candidate
under a trace is `U(T) = C(T)·V(T)`.

## R1. The steering identity and bound — **survives** (LEAN, FIX)

For a steered trace `T` and a comparator `N` on one world,
```
U(T) − U(N)  =  both·(V(T) − V(N)) + (C(T) ∧ ¬C(N))·V(T) − (¬C(T) ∧ C(N))·V(N)
```
(`steering_identity`, which is the effect side's `mismatch_identity`), and with a
**content-Lipschitz certificate** `|V(N_form T) − V(N_form N)| ≤ L·d_canon(T, N)` and the
**form terms** `κ(T) := |V(T) − V(N_form T)|`, `κ(N)` likewise,
```
E[U(T)] − E[U(N)]  ≤  L·E[both·d_canon] + E[both·(κ(T) + κ(N))] + D·E[C(T) ∧ ¬C(N)]
```
(`steering_bound`, **LEAN**; **FIX** on all sixteen attacks and fixture 12b).  The three right-hand terms
are the **content residual**, the **form residual** and the **audit mismatch**.  `D` is
sharp (`Witness.attained` of the landed module applies verbatim); the reverse mismatch is
free; the form residual is attained by an order-sensitive program
(`Witness.form_attained`).

## R2. Extensionality kills form steering — **survives** (LEAN, FIX)

If `V` factors through `canon` then `κ ≡ 0` (`extensional_form_free`), and ordering,
duplication, salience and framing have no advantage (fixtures 3, 4, 5 against the
canonical program, fixture 11).  A program that reads the trace beyond its content is
not extensional (`not_extensional_of_form`), and against it each of those attacks is
worth exactly its form term (fixtures 3–5, `κ = 1/4`).  Canonicalization is
**independently necessary**: it is a property of the program, not of coverage or
liveness, and none of the other clauses substitutes for it.

## R3. Weighted-count programs are content-Lipschitz — **survives** (LEAN)

For the committed-program class of weighted reason counts,
`|V(c) − V(c')| ≤ L·|c Δ c'|` with `L` the largest weight (`weightedCount_lipschitz`,
attained by `Witness.lipschitz_attained`).  The reason-side twin of the evaluator's
`L`-stability on the effect side: a certifiable program property.

## R3′. The total-scope repair — **survives** (LEAN, FIX)

With every declared reason type protected, the coverage barrier (every true declared
reason present) and sound authentication (every present declared reason true) force the
canonical content to equal the true declared set, so the content residual against
`N_full` is `0` on every audited world (`content_residual_zero_of_total_scope`;
`test_total_scope_forces_full_content`).  Neither hypothesis is an interface property:
one is a scope decision, the other the engine's soundness (fixture 12b is its failure,
charged at `L`).

## R4. Robust Openness over a declared class is `Γ`-valid — **survives, as stated**

Over a finite declared class `J` of log transforms, openness under every transform is
the finite conjunction of the audit's verdicts on the transformed traces
(`openUnder_iff`, **LEAN**; **FIX** `test_declared_transform_class_is_a_finite_computation`).
With the program committed, each transformed trace's verdict is a computation, so the
predicate is decidable and, in a theory representing computations, `Γ`-valid.  What is
**not** `Γ`-valid is the claim that a declared transform is the causal counterfactual of
the intervention it names: that contract is **EXT** (the 2026-09-10 round's P2), and the
obstructions the dispatch lists fall on it exactly — reason-truth dependence (a
world-changing intervention is not a log transform), and reason-generation dynamics
(the transform must re-simulate what the principal would have deliberated).  The
intervention class need not be finite in principle, but only a finite declared class is a
finite computation.

## R5. Logical Induction learns the steering inequality — **survives** (LEAN, PAPER)

The steering package supplies the landed `ValidAt` for a compiled pair with the
approve-branch surrogate `w_app := V(N_form N) + (V(T) − V(N_form T))`, discrepancy
`d_canon/d_max`, regret `κ(T) + κ(N)` (`steering_validAt`), so the landed
`li_bypass_le_compiled` applies **verbatim** (`li_steering_le`): for efficiently emitted
audit sentence families and base families (steered verdict, comparator verdict, content
discrepancy, form regret), an e.c. bounded `λ_n`, and validity in every completed-theory
world,
```
E_n(U(T_n)) − E_n(U(N_n))  ≲_n  L·E_n(both·d_n) + E_n(both·κ_n) + D·E_n(M_n) .
```
No calibration hypothesis; the finite-menu uniformity over polynomial-size efficiently
generated menus transfers unchanged (`softWeight_aggregate_ge`, `uniform_of_soft`).
Nothing of Logical Induction is re-proved.

## R6. The residual reduces to interface completeness + liveness — **REFUTED**

The literal thesis: with a complete, authenticated, canonical reason interface and
coverage plus liveness, no steering advantage remains.  **Counterexample** (fixtures 2
and 13): a true unprotected counterreason inside the declared interface is omitted; the
advisor's own reason is authenticated and true; the program is extensional; the
protected barrier holds (the protected counterreason is present); nothing is late; and
the advantage is the omitted reason's weight, `1/4`.  Every clause holds and the
residual is the content term.  The two repairs that remove it are not interface
properties: **scope totality** (protect every declared reason type, so the omission
voids; `test_total_scope_repairs_the_counterexample`) at the price of availability,
or a **supply obligation** discharged by a party other than the advisor
(`test_supplied_reason_repairs_the_counterexample`).  The effect side has no such
term because `𝔠` is the agent's own move rewritten; the reason side's normalization
cannot be realized by rewriting the advisor's outputs, since the omitted content is not
in them.

## R7. The two-interface thesis — **survives only in a strengthened form**

The symmetry holds under: (i) interface completeness *by construction* — with a
committed program re-executed on the trace, every influence on the committed vector
factors through the trace (`reasonMediated_of_reexecution`, registered); (ii) an
**extensional** program (R2); (iii) a **total protected scope** with **liveness supplied
by the ecosystem** (the registrar or third parties raise every true declared reason
before the deadline), so that declared omissions are voids, not advantages; (iv)
**effect-side containment** of world-changing interventions (fixture 6 is an effect,
caught by the effect interface or an undeclared-channel failure); (v) the
**declared-transform contract** for dynamics (R4).  Under (i)–(v) the remaining
reason-side residual is the mass of **undeclared reason types** (fixture 7) and
**insufficient granularity** (fixture 8), which no interface-local predicate sees.  The
asymmetry that survives: on the effect side the residual is made small by the agent's
own rewritten policy; on the reason side by the ecosystem's supply and scope.

## R8. Undetected steering, exactly

Not one Boolean.  On audited worlds the advantage of steering over the comparator is at
most the sum of three named residuals (R1): the content residual (declared reasons
missing or inserted relative to the comparator), the form residual (the program's
non-extensionality), and the audit mismatch (the steered trace passes an audit the
comparator would fail).  The Boolean "steering occurred and the audit passed" is the
support of the first two; the third is the analogue of the effect side's directional
activation mismatch and is charged at `D`.

## Refuted stronger statements

| statement | refuted by |
|---|---|
| coverage + liveness suffice against truthful selective omission | fixtures 2, 13 |
| an extensional program is not needed once the interface is complete | fixtures 3, 4, 5 |
| an undeclared reason is charged to content | fixture 7: it is charged to the form term, since `canon` cannot see it |
| "authenticated false reason" is one attack | fixtures 12 and 12b: the unproved claim voids, the forged certificate charges at `L` |
| a world-changing intervention is a reason-side residual | fixture 6: relative to the changed world the trace is fully informed |
| granularity failures are visible to the theory | fixture 8: canonically identical traces |
| Robust Openness as a causal claim is `Γ`-valid | R4: only the declared-transform form is |
| the reason-side normalization is realizable by rewriting the advisor | R6: omitted content is not in the advisor's outputs |

---

# Second pass: the supply theorem

Labels as above; Lean names in `lean/Workspace/Deference/Contrib/ReasonSupply.lean`.

## R9. The content residual is the adverse sensitivity mass — **survives** (LEAN, FIX)

For an extensional program with per-reason adverse certificates `A_r`, the advisor's
gain from the absence of a set `S` is at most `Σ_{r ∈ S} A_r` (`adverse_union`); the
symmetric telescoping bound is `sensitive_symmDiff`; weighted-count programs have
`A_r = (−w_r)⁺` and `L_r = |w_r|` (`weightedCount_adverse`, `weightedCount_sensitive`).
Per-weight charging is wrong for defeat programs and every static certificate is loose
under redundancy (fixtures 7, 8 of the second pass).  `CONTENT_RESIDUAL.md`.

## R10. The service obstruction — **survives** (LEAN, FIX, PAPER)

Service received by reasons released at or after `s` is at most `Cap(s)`
(`served_cut_le`); full service forces the suffix-cut condition (`cut_of_servesAll`); the
unserved cost is at least the cut excess (`unserved_ge_excess`); for unit service the
suffix-cut condition is also sufficient (`unit_servable_iff_cut`, Hall).  The least
unserved count is the maximal cut excess and the least adverse miss is the matroid layer
formula, attained by heaviest-first (random-instance checks against exhaustive search).
`SUPPLY_THEOREM.md` §2.

## R11. Online equals offline for unit service — **survives** (FIX)

Serving the heaviest discovered unserved reason at each free slot attains the offline
optimum for a common deadline (`test_online_greedy_is_offline_optimal`); the
affordability round's online gap is about prices revealed later, absent here.

## R12. The hybrid protection bound — **survives** (LEAN)

On the audited branch only the unprotected missing adverse mass is charged; a missing
protected reason voids (`hybrid_bound`).  Total protection is right iff the whole
interface is servable; otherwise protect a servable set of largest adverse mass.

## R13. The composition — **survives** (LEAN)

`li_gated_le`: a gated family bounded by `α` in every consistent world has expectation
`≲ α` (a degenerate pair fed to the landed compiled theorem, constants removed by
`expect_constLUV`).  `li_noncapture`: with a certified content bound, an extensional
program and a sealed audit, `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α`.  `COMPOSITION.md`.

## R14. "Reason supply is the affordability round's timeliness case" — **NARROWED**

The budget half is (D4 over the release window, M1's additivity); the capacity half,
where the Hall form and the missed-mass bound live, is not in that theory and is new
here.  `AFFORDABILITY_REFINEMENT.md` §5.

## R15. Greedy by weight is optimal for general costs — **REFUTED** (FIX)

Fixture 17: greedy misses `1/2`, the optimum `3/8`; the weighted problem is knapsack-hard.

## R16. An independent supplier has exogenous costs — **made explicit** (FIX)

Fixture 12: the advisor raising a counterreason's authentication cost from `1` to `3`
breaks the cut.  This was an implicit hypothesis of the first pass and is now a named
one; without it the certified bound ranges over the advisor's cost-influence class.

## Refuted or narrowed in the second pass

| statement | status |
|---|---|
| the content term should be the count `d_canon` | replaced by the adverse mass (R9) |
| coverage/liveness suffice once a supplier exists | no: the supplier's cut condition is the criterion (R10) |
| greedy is optimal for general costs | refuted (R15) |
| static certificates are tight | refuted under redundancy (fixture 8) |
| discovery is a property of the docket | refuted: it is policy-dependent (fixture 9) |
| `N_full` is the comparator to certify against | replaced by `N_disc` for the certified theorem |
| reason supply is exactly affordability's timeliness case | narrowed (R14) |
| an independent supplier needs no cost hypothesis | refuted (R16) |

---

# Third pass: the discovery residual

Labels as above; Lean names in `lean/Workspace/Deference/Contrib/ReasonDiscovery.lean`.

## R17. The discovery residual is bounded by the conditional adverse mass — **survives** (LEAN, FIX)

`V(Disc) − V(Truth) ≤ Σ_{r ∈ Truth \ Disc} A_{r|Disc}` (`adverseAbove_union`); the
conditional certificate vanishes for a defeated counterreason once the defeater is
docketed and for a redundant reason once its partner is found.  `DISCOVERY_RESIDUAL.md`.

## R18. The frontier theorem — **survives** (LEAN, FIX)

Empty frontier ⇒ residual `≤ 0` (`residual_le_zero_of_frontier_empty`); contrapositively
an unresolved reason of positive conditional adverse mass is an explicit inquiry obligation.

## R19. The information-cell obstruction — **survives** (LEAN, FIX)

Every sound docket policy has, on some world of every repertoire cell, residual at least
the cell gap (`residual_ge_cellGap`); the exhaustive policy attains it
(`exhaustive_attains_cellGap`); the least worst-case residual with unbounded budget is the
largest cell gap, zero iff the repertoire separates what the verdict separates.

## R20. The budgeted value is a decision-tree minimax — **survives, no closed form** (FIX)

`V(K, B)` by the recursion, checked against enumerated decision trees; monotone in the
budget; between the obstruction and the best nonadaptive value.

## R21. A fractional-progress theorem for direct queries — **REFUTED** (FIX)

The needle: worst-case residual at its full value until the last query.  Geometric decay
holds only under witness completeness (`potential_decay`), a repertoire property.

## R22. Adaptivity is inessential — **REFUTED** (FIX)

Level queries on a chain: adaptive binary search closes the residual with two queries;
every fixed pair leaves a cell of gap `1/8`.

## R23. The chain composes — **survives** (LEAN)

`li_noncapture_chain`: `𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)` with the middle family
shared; `β` is `Γ`-valid relative to the declared hypothesis space.

## Refuted or narrowed in the third pass

| statement | status |
|---|---|
| additive adverse mass is the discovery residual | replaced by the omission gain, certified by the *conditional* mass (R17) |
| "discover every true reason" is the target | replaced by decision-sufficient discovery (frontier empty) |
| a progress theorem holds for any repertoire | refuted for direct queries (R21) |
| the budgeted residual has a cut-like formula | no: decision-tree value (R20) |
| `N_full` needs an oracle | no: bounded by the cell gap relative to the declared hypothesis space (R23) |
| an interface-incompleteness mass can be defined | rejected: no measurable object in the declared representation |
