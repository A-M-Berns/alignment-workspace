# Report

Two passes.  The **second pass** (refinement and pressure, 2026-09-16) is reported first;
the first pass's sixteen answers are retained below, with the verdict they reached.

## Verdict of record (second pass)

**B. CONTENT-RESIDUAL-REDUCED-TO-A-SHARP-SERVICE-OBSTRUCTION**, with the A-case as an
explicit corollary: the content residual is closed by supply affordability exactly when
the suffix-cut condition holds on the discovered docket.  The verdict sentence of record
is the first paragraph of `README.md`.

What changed from the first pass: the content term is no longer a count but the adverse
sensitivity mass of the reasons not served before commitment
(`CONTENT_RESIDUAL.md`); an exact service theorem bounds it and characterizes when it is
zero (`SUPPLY_THEOREM.md`); the bound composes with the landed Logical-Induction theorem
in Lean with no new certificate (`COMPOSITION.md`); protected scope becomes a design
parameter (`hybrid_bound`); the affordability connection is stated at theorem level and
two first-pass claims are narrowed (`AFFORDABILITY_REFINEMENT.md` §5); one hypothesis the
first pass had left implicit, exogenous service costs, is made explicit
(`COUNTERMODELS_SECOND_PASS.md` row 12).

Consumes `../2026-09-15-li-corrigibility/`, `../2026-09-10-committed-principal-program/`,
`../2026-09-09-evaluation-ecosystem-realization/`, and, for the budget half of
affordability, `../../../normativity/legitimacy/rounds/2026-08-31-normative-affordability/`
(BD1, D4, M1, read rather than paraphrased).  Nothing of the canonical wiki is edited.

## The twenty questions

1. **The exact quantity for missing deliberative content.**  `Miss_n := Σ_{r true
   declared, not served by T_n} A_r`, the adverse sensitivity mass of the unserved true
   declared reasons, where `A_r := sup_c (F(c) − F(c ∪ {r}))⁺` is how much adding `r` can
   lower the advisor's candidate's verdict (`CONTENT_RESIDUAL.md` §1).
2. **Count, weighted, sensitivity-weighted, or direct?**  Sensitivity-weighted and
   directional (`D^A`).  Relations, all Lean: omission gain `≤ D^A ≤ D^L ≤ L_max·count`
   (`adverse_union`, `sensitive_symmDiff`); for weighted-count programs `A_r = (−w_r)⁺`
   (`weightedCount_adverse`).  Per-weight is wrong for defeat programs (fixture 7); the
   direct discrepancy is sharper (fixture 8) but is the comparator problem again; count
   charges weightless reasons.  The theorem charges the smallest statically certifiable
   quantity.
3. **The independent supplier model.**  A process other than the advisor with capacity
   `cap(t)` at each slot `t < T_n`, which sees a docket of discovered true declared
   reasons with release slots and costs and chooses which to serve; certified policy:
   heaviest-available-first (`SUPPLY_THEOREM.md` §1, RS6).  Independence means two
   things: its capacity is not consumed by the advisor's submissions (row 11) and the
   cost profile is not the advisor's to raise (row 12).
4. **The resource.**  Capacity units in slots, usable by a reason only in its release
   window `[a_r, T_n)`; and, where service is itself enforcement, the affordability
   round's liability budget with date prices, additively (`AFFORDABILITY_REFINEMENT.md`
   §2).
5. **The deadline model.**  One common commitment deadline `T_n` per occurrence, with
   reason-specific release times; windows are nested suffixes, not the affordability
   round's uniform-delay intervals.
6. **The theorem that makes it small.**  RS1–RS4: the cost served from reasons released
   at or after `s` is at most `Cap(s)` (`served_cut_le`, Lean); full service forces the
   suffix-cut condition (`cut_of_servesAll`, Lean); for unit service the condition is
   also sufficient (`unit_servable_iff_cut`, Lean, Hall); the least unserved count is
   the cut excess and the least adverse miss is the matroid layer formula, attained by
   the greedy (fixtures, random-instance checks).  Hence `Miss*_n = 0` iff the suffix-cut
   condition holds on the discovered reasons of positive adverse weight.
7. **Iff / dual.**  Yes for unit service: full service iff every suffix cut is
   underwritten (Hall); least unserved count = max cut excess (Hall's deficiency); least
   adverse miss = total mass − `Σ_j (A_(j) − A_(j+1))·rank(top-j)` with the rank the
   deficiency-corrected size.  For general costs: the cut bound is exact for unserved
   cost, the weighted optimum is knapsack-hard (`RELATED_MATH.md`).
8. **Affordability, scheduling, flow, covering?**  A bipartite transportation problem
   with nested neighbourhoods, i.e. a transversal matroid, for capacity; plus the
   affordability round's additive budget (D4 over the window) if service is enforcement.
   Not the authority-underwriting geometry, which has no shared slot (its N1); not online
   knapsack, since arrivals only add options and costs are known at release.
9. **Discovery vs service.**  `Miss_n = discovery_n + Miss*_n + authentication_n` with
   scope outside (`decompose`, tests).  Discovery is the adverse mass of true reasons no
   supplier releases before `T_n` (or releases too late to serve is *service*, since
   release is on the docket); it is policy-dependent (fixture 9).  Only the service part
   is a computation on the log.
10. **Protected scope.**  A design parameter: `hybrid_bound` (Lean) charges only the
    unprotected missing adverse mass on the audited branch and voids on any missing
    protected reason.
11. **Is total protected scope desirable?**  Exactly when the suffix-cut condition holds
    for the whole interface; then voids come only from discovery and authentication.
    Otherwise it converts every service failure into a void: availability destroyed.
12. **Does a hybrid dominate?**  Yes: protect exactly a servable set of largest adverse
    mass (the greedy set), so protected reasons are never missed by service, and charge
    the rest at their adverse mass; fixture 3 is the unit.  Risk-sensitive: replace `A_r`
    by the designer's loss function of a missed `r`.
13. **Is `N_full` legitimate?**  As a yardstick, yes: it is what "fully informed on the
    declared interface" means and it compiles as a world-valued LUV with no oracle.  As a
    comparator a supplier can certify against, no: its content term includes discovery
    loss, which no log determines (fixture 16).
14. **A realizable supplier comparator.**  The **discovered comparator** `N_disc`: every
    true declared reason on the docket before `T_n`, canonical form.  The content term
    against it is service plus authentication loss, a computation on the log.  The
    supplier's own output is not a separate comparator: with the supplier in the loop the
    actual trace *is* it, and the theorem's content is `N_service` against `N_disc`.
15. **Does the service theorem compose with `li_steering_le`?**  Yes, in Lean:
    `li_noncapture` takes `hsupply : ∀ n v, ∃ d, ValuesAt (X_d n) d ∧ (both → d ≤ a/b)`,
    which is exactly the sentence family "service loss ≤ α on the audited branch", and
    concludes `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·(a/b)`.  The bridge is `li_gated_le`, a degenerate
    pair fed to the landed compiled theorem, plus `expect_constLUV`.
16. **Assumptions under which the content residual vanishes.**  Against `N_disc`: the
    suffix-cut condition on the discovered reasons of positive adverse weight at every
    occurrence, sound authentication, unit (or servable) costs exogenous to the advisor,
    supplier capacity not consumable by the advisor.  Against `N_full`: additionally no
    discovery loss, which is not certifiable.
17. **What remains after it vanishes.**  One quantity: **the discovery residual**, the
    adverse mass of true declared reasons no independent process raises before
    commitment.  It is an inquiry problem, not a service problem, and no interface-local
    quantity measures it.  Everything else remaining is a hypothesis rather than a
    residual: exogenous costs (row 12), the declared representation (scope,
    granularity), effect-side containment of world changes, the declared-transform
    contract for dynamics.
18. **A serious non-capture theorem?**  Yes, `li_noncapture`: under a committed
    extensional program re-executed on the authenticated trace, a certified service
    bound `α`, and a content-monotone audit, Logical Induction learns
    `𝔼ₙ(U_T) − 𝔼ₙ(U_disc) ≲ₙ A_tot·α`; with the cut condition, `≲ₙ 0`.  The comparator
    hides no oracle.
19. **Does it compose with the effect-side theorem?**  They are instances of one
    compiled inequality (`li_bypass_le_compiled`), with the same certificate and the same
    shape of residual; `COMPOSITION.md` §5.  The combined statement is below.
20. **The strongest honest combined statement.**  See the next section.

## The strongest honest combined corrigibility statement

Relative to: effect completeness and the interaction model carried by `Γ` (T1's
hypothesis); a declared reason representation with a committed extensional program
re-executed on the authenticated trace; an independent supplier with exogenous costs and
capacity the advisor cannot consume; the sealed-comparison architecture for the effect
side's activation mismatch (item 89) and a content-monotone audit on the reason side;
the declared-transform contract wherever a counterfactual is named.  Then for every
candidate continuation `q` and its principal evaluation,

```
𝔼ₙ(U_q) − 𝔼ₙ(U_𝔠q)      ≲ₙ  L·𝔼ₙ(Δ_n) + 𝔼ₙ(R_n) + D·𝔼ₙ(M_n)          (PR #100)
𝔼ₙ(U_T) − 𝔼ₙ(U_disc)    ≲ₙ  A_tot·α_n                                  (this round)
```

with `Δ` the mediation discrepancy, `R` the decision regret, `M` the activation
mismatch, and `α_n` the certified service loss on the discovered docket.  When the
right-hand sides vanish,

> the agent has asymptotically no operative advantage either from bypassing the
> principal's protected decision authority or from steering the declared reasons on
> which that authority is exercised, beyond the adverse mass of true reasons no
> independent process raised before commitment.

The last clause is the discovery residual and is not removable by any interface-local
hypothesis.

## What is in Lean and in fixtures (second pass)

`lean/Workspace/Deference/Contrib/ReasonSupply.lean`, 14 audited declarations, sorry-free,
`[propext, Classical.choice, Quot.sound]` only: `sensitive_symmDiff`, `adverse_union`,
`weightedCount_adverse`, `weightedCount_sensitive`, `served_cut_le`, `cut_of_servesAll`,
`unserved_ge_excess`, `unit_servable_iff_cut`, `hybrid_bound`, `constLUV_thresholdCodes`,
`expect_constLUV`, `gatedPair_validAt`, `li_gated_le`, `li_noncapture`.  Fixtures:
`src/supply.py`, `src/sensitivity.py`, `src/attacks_second_pass.py`; `python3 tests/run.py`
runs 31 tests (11 first pass, 20 second), including random-instance checks of the cut
criterion against exhaustive schedule search, of the deficiency and layer formulas against
exhaustive optimization, and of online greedy against the offline optimum.

## Deviations from the second dispatch

- The mechanized sufficiency of the cut condition is for unit costs and unit slots
  (Hall); general costs with preemption are checked exhaustively and argued by flow, not
  mechanized.
- The weighted optimum's exactness for unit costs (matroid greedy, layer formula) is
  fixture-checked and cited, not mechanized.
- `li_noncapture` is stated for a constant bound `a/b`; the `α_n → 0` corollary is by a
  routine shift of the families and is not mechanized (`COMPOSITION.md` §3).
- The sealed-audit hypothesis `hsealed` is taken as a hypothesis of the realization, not
  proved for a concrete audit; against `N_form`, `N_disc` and `N_full` it holds by content
  monotonicity of the audit (first pass §2), which is not re-derived in Lean.
- One fixture beyond the dispatch's sixteen (row 17: greedy fails for general costs).

## What this does not establish

- Any bound on the discovery residual; any characterization of reason relevance.
- That any realized supplier has exogenous costs or advisor-proof capacity.
- The general-cost weighted optimum in closed form (it is knapsack-hard).
- The effect-side sealed comparison (item 89), consumed as a hypothesis.

## Reserved to the maintainer

Whether to adopt the hybrid protection rule (protect the servable set of largest adverse
mass) as the realization's default; whether the discovery residual should be named as
the manipulation side's single open quantity in the canonical wiki.  Neither is done
here.

## Registration

Nothing.  The Lean results are set identities, Hall's theorem specialized, and an
application of the landed compiled theorem; the round is a research branch.

## Outstanding maintainer actions

1. Decide the merge of this pull request.
2. Decide the two reserved questions above; item 92 is updated accordingly.

---

## First pass (retained): NONCAPTURE-COMPILES-BUT-REASON-COMPLETENESS-FAILS

The first pass's verdict stands as the round's starting state: the trace-steering
comparison has exactly the algebra of the effect-side inequality and supplies the landed
compiled pair's validity package verbatim; scoped Robust Openness over a finite declared
class of log transforms is a finite computation; the two-interface thesis is refuted as
stated by truthful cherry-picking of an unprotected declared counterreason; the two
repairs are scope and supply.  Its sixteen answers:

1. **Trace-steering analogue of T2.**  Yes: `steering_identity` and `steering_bound`
   (Lean), with the mediation discrepancy replaced by the canonical content discrepancy,
   the decline regret by the program's non-extensionality, the activation events by the
   audit verdicts; `D` sharp, reverse mismatch free, form branch attained.
2. **Compiles into a bounded LUV inequality.**  Into the same one: `steering_validAt`
   supplies the landed `ValidAt` with `w_app := V(N_form N) + (V(T) − V(N_form T))`.
3. **EPI transfers unchanged.**  `li_steering_le` is `li_bypass_le_compiled` applied to
   steering pairs; the finite-menu uniformity is inherited.
4. **Undetected steering.**  Not one Boolean: the content, form and audit-mismatch
   residuals; the mismatch is zero against both log-side comparators.
5. **Scoped Robust Openness `Γ`-valid.**  Over a finite declared class of log transforms,
   yes (`openUnder_iff`); the causal reading of the class stays external.
6. **Intervention class.**  A finite declared class of log transforms; form by `N_form`,
   content by `N_full`, dynamics by declared transforms, world changes by the effect
   interface, grounds tampering by authentication.
7. **Analogue of effect completeness.**  Two halves: trace mediation by construction
   (re-execution) and declared-content mediation (extensionality); a rewrite of the
   advisor's outputs exists for form and not for content.
8. **Finiteness.**  Needed for the compilation and for decidability; reason relevance is
   not finitely characterizable.
9. **Canonicalization independently necessary.**  Yes (`not_extensional_of_form`).
10. **Coverage and liveness sufficient?**  No: fixture 2.
11. **Affordability.**  Through the supply obligation; refined in the second pass.
12. **Remaining modes.**  Undeclared types, granularity, dynamics beyond declared
    transforms; refined to the discovery residual in the second pass.
13. **One residual?**  On the declared interface, `L·E[both·d] + E[both·κ] + D·E[M]`;
    refined to the adverse mass in the second pass.
14. **Measurable.**  Form and transform mismatch from the log; content against `N_full`
    needs settlement of absent reasons; refined: the service loss is log-computable.
15. **Two-interface thesis.**  Refuted as stated; survives strengthened.
16. **Minimal counterexample.**  Fixture 2.

## Attribution

Claude Fable 5.1 (Anthropic), under `prompts/2026-09-16-noncapture-compilation/`
(the maintainer's two-phase dispatch of 2026-09-15, Phase II, and the refinement
dispatch of 2026-09-16, both verbatim in `PROMPT.md`).
