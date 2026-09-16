# The corrigibility nucleus: final statement

**Status:** the landing statement of PR #101 (2026-09-16), consolidating PR #100 (landed)
and the three passes of this round.  This is the reading path; the pass documents are
research provenance.  Labels: **LEAN** (a sorry-free declaration in the named module,
axioms `propext`, `Classical.choice`, `Quot.sound` only), **PAPER** (a theorem of the
Logical Induction paper at its exact statement), **FIX** (an exact fixture), **EXT**
(external contract), **OPEN**.

## 1. Setup

Two interfaces, both declared.

**Effect interface.**  A finite interaction (agent move, principal response, exterior
move); protected concerns with response semantics; **response authority** `K_r` (after
the agent's move some principal response realizes the concern now); an **agent-caused
loss** (authority lost after the actual move, kept after the idle move); the
**authorization interface** (proposal, approve/decline, gated release, latch), with
losses **authorized** when event-linked to the decision that enabled the effect.

**Reason interface.**  A declared set of reason ids `I` with settleable truth; a
**committed principal program** `π_P : ℛ → 𝒱` re-executed on the authenticated trace at
commitment, so the vector is `V(T) := π_P(T)`; the **canonical content** `canon(T) ⊆ I`;
the **audit** `C(T)` (authentication, authorship, the protected coverage barrier,
timing); the advisor's **activated security** `U(T) := C(T)·V(T)`.  Three comparators:
the form-normalized trace `N_form` (log-determined), the **discovered comparator**
`N_disc` (every true declared reason on the docket before commitment), the
**fully-informed comparator** `N_full` (every true declared reason).

**The learner.**  A logical inductor over a deductive process carrying the declared
interaction and reason models as a specification `Γ`.

**Vocabulary** (one term each): *corrigibilization* `𝔠`; *directional activation
mismatch* `M`; *trace steering*; the *steering advantage* `𝔼ₙ(U_T) − 𝔼ₙ(U_N)`; its
*content*, *form* and *audit-mismatch residuals*; *adverse sensitivity* `A_r` and
*conditional adverse sensitivity* `A_{r|D}`; the *service residual* `α` and *discovery
residual* `β`; the *information-cell gap*; the *inquiry frontier*; *independent inquiry*
and *independent supplier* as defined in §5.

## 2. Protected authority (PR #100)

**A1 (Corrigibilization soundness; LEAN `Corrigibilization.corrigible_corrPolicy`).**
Under effect completeness (EXT), with mediation soundness, decline preservation and
execution faithfulness holding by construction, every continuation's corrigibilization
is corrigible under every rule that does not correct at the authorizing step:
`∀π ρ, Corrigible_h(𝔠π, ρ)`, with event-linked authorization.  Closure: `𝔠` is idempotent
and fixed exactly on release-free behaviour (LEAN); approval reproduces the raw policy
(LEAN, `approvalMorphism`).

**A2 (Directional activation mismatch; LEAN `mismatch_identity`, `mismatch_bound`).**
`U_raw − U_corr = both·(w_raw − w_act) + M·w_raw − M'·w_act`, and
`E[U_raw] − E[U_corr] ≤ L·E[both·δ] + E[both·ρ] + D·E[M]`; `D` sharp, the reverse term
free, the marginal-rate form false (FIX).

**A3 (Logical Induction learns it; LEAN `li_bypass_le_compiled`, PAPER
`thm:expprovind`).**  The compiled constraint `B = U_raw − U_corr − λG_δ − G_ρ − G_M`
with its `P`-generability certificate (`MediatedPair.syntaxOf`) gives
`𝔼ₙ(U_raw) − 𝔼ₙ(U_corr) ≲ₙ λ𝔼ₙ(G_δ) + 𝔼ₙ(G_ρ) + 𝔼ₙ(G_M)`, no calibration hypothesis;
uniformly over polynomial-size efficiently generated menus by the near-argmax weighting
(LEAN `uniform_of_soft`; the weighting's own certificate OPEN, item 90).

**A4 (Sealing; EXT, item 89).**  `𝔼ₙ(G_M) → 0` is the zero case of A2, supplied by the
sealed-comparison architecture (sequenced settlement or evaluator factorization).

## 3. Trace steering (pass 1)

**S1 (Identity and bound; LEAN `steering_identity`, `steering_bound`).**  For a steered
trace and a comparator on one world, the identity of A2 holds verbatim with the audit
verdicts as the events, and
`U(T) − U(N) ≤ both·(L·d + κ(T) + κ(N)) + D·M`, with `d` the content discrepancy under a
content-Lipschitz certificate and `κ` the program's non-extensionality.

**S2 (Form; LEAN `extensional_form_free`, `not_extensional_of_form`).**  An extensional
program has `κ ≡ 0`; canonicalization is independently necessary.

**S3 (Transfer; LEAN `steering_validAt`, `li_steering_le`).**  The steering package
supplies the landed `ValidAt`, so A3 applies verbatim.

**S4 (Robust Openness as a computation; LEAN `openUnder_iff`).**  Over a finite
declared class of log transforms, openness is a finite conjunction of audit verdicts,
hence `Γ`-valid; the causal reading of the class is EXT.

**S5 (The two-interface thesis; FIX).**  Completeness, authentication, canonicalization,
coverage and liveness of a declared reason interface do *not* remove the content
residual: truthful omission of an unprotected declared counterreason passes every
clause (fixture 2).  Rewriting the advisor's outputs removes form steering and cannot
supply omitted content.

## 4. Service (pass 2)

**C1 (The content quantity; LEAN `adverse_union`, `sensitive_symmDiff`,
`weightedCount_adverse`).**  The advisor's gain from a missing set `S` is at most
`Σ_{r∈S} A_r`, `A_r := sup_c (F(c) − F(c ∪ {r}))⁺`; for weighted counts `A_r = (−w_r)⁺`;
per-weight charging is wrong for defeat programs and every static certificate is loose
under redundancy (FIX).  The compiled content LUV is `Σ_{missing} A_r / A_tot`.

**C2 (The suffix-cut obstruction; LEAN `served_cut_le`, `cut_of_servesAll`,
`unserved_ge_excess`, `unit_servable_iff_cut`).**  With releases `a_r`, costs `c_r` and
per-slot capacity before the deadline `T`, service from reasons released at or after `s`
is at most `Cap(s)`; full service forces `∀s: Demand(s) ≤ Cap(s)`; for unit service the
condition is also sufficient (Hall on nested neighbourhoods).  The least unserved count
is the maximal cut excess and the least adverse miss is the matroid layer formula,
attained by heaviest-available-first offline and online (FIX, random instances);
general costs are knapsack-hard (FIX).

**C3 (The service residual).**  `Miss = discovery + service + authentication` by stage,
scope outside.  The service part `α_n := Miss*_n` is a computation on the docket, hence
`Γ`-valid.

**C4 (Protected scope; LEAN `hybrid_bound`).**  On the audited branch only the
unprotected missing adverse mass is charged; a missing protected reason voids.  Total
protection is right iff the whole interface is servable; otherwise protect a servable
set of largest adverse mass.

**C5 (Affordability, read).**  The affordability round's D4 and M1 supply the *budget*
resource over the release window; the *capacity* resource and the missed-mass bound are
C2.  A supplier is affordable when both hold.

## 5. Discovery (pass 3, with the landing generalization)

**D1 (The residual; LEAN `adverseAbove_union`).**  `V(Disc) − V(Truth) ≤ Σ_{r ∈ Truth \
Disc} A_{r|Disc}`, `A_{r|D} := sup_{c ⊇ D, r ∉ c} (V(c) − V(c ∪ {r}))⁺`: a defeated
counterreason stops counting once its defeater is docketed, a redundant reason once its
partner is found.

**D2 (The frontier; LEAN `residual_le_zero_of_frontier_empty`).**  Empty frontier
(undetermined reasons of positive conditional adverse mass) ⇒ residual `≤ 0`.  An
unresolved reason of positive conditional adverse mass is an explicit inquiry
obligation.

**D3 (The information-cell obstruction, general form; LEAN `bestResp_antitone`,
`residual_ge_cellGap'`, `exhaustive_attains_cellGap'`).**  In a finite inquiry model
(declared hypothesis space `Ω`, repertoire of outcome functions), the advisor is a
strategic content-adder with best response `bestResp(D, T) := max_{S ⊆ T \ D} V(D ∪ S)`;
larger dockets never help it; so for **every extensional program**, every sound docket
policy has on some world of every repertoire cell a best-response residual at least the
general cell gap `gap*(K) := max_{ω∈K} [bestResp(certain K, Truth ω) − V(Truth ω)]`, and
the exhaustive docket attains it.  **The antitone case is the corollary** (LEAN
`cellGap'_eq_cellGap`, `residual_ge_cellGap`, `exhaustive_attains_cellGap`): when the
verdict is antitone in the adverse content the best response is `V(certain K)` and the
gap is `max_ω [V(certain K) − V(Truth ω)]`.  Hence the least worst-case discovery
residual with unbounded budget is exactly the largest cell gap, zero iff the repertoire
separates every pair of worlds whose shared content leaves the advisor a gain.

**D4 (Budget; FIX).**  The budgeted least worst-case residual is the value of the
minimax recursion, exact against enumerated decision trees, monotone in the budget,
never below the obstruction; no closed form.  The needle refutes any fractional-progress
theorem for direct queries; adaptive inquiry strictly beats nonadaptive; geometric decay
holds under witness completeness (LEAN `potential_decay`).

**D5 (The discovery residual).**  `β_n := gap*` (or the budgeted value) relative to the
declared hypothesis space and repertoire: a computation on the declaration and the
program, hence `Γ`-valid.  Adequacy of the declaration is EXT.

## 6. Composition

**E1 (`li_gated_le`; LEAN).**  A gated LUV family bounded by `α` in every consistent
world has expectation `≲ α` (a degenerate pair fed to A3; constants removed by
`expect_constLUV`).

**E2 (`li_noncapture`; LEAN).**  With a certified content bound `α`, an extensional
program and a content-monotone audit, `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α`.

**E3 (`li_noncapture_chain`; LEAN).**  With the discovered comparator as the shared
middle, `𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)`.

## 7. The combined corrigibility theorem (schema)

For every efficiently represented candidate continuation `q` and its principal
evaluation, under the hypotheses of §8:

```
Adv_bypass,n(q)  :=  𝔼ₙ(U_q) − 𝔼ₙ(U_𝔠q)     ≲ₙ  L·𝔼ₙ(Δ_n) + 𝔼ₙ(R_n) + D·𝔼ₙ(M_n)
Adv_steering,n   :=  𝔼ₙ(U_T) − 𝔼ₙ(U_full)  ≲ₙ  A_tot·(α_n + β_n)          [+ form and audit terms, zero under §8]
```

uniformly over polynomial-size efficiently generated menus on the authority side (A3),
with `α_n` characterized by C2 and `β_n` by D3/D4.  If the mediation discrepancy,
decision regret and activation mismatch vanish and `α_n, β_n → 0`, both advantages are
asymptotically nonpositive.

> Relative to declared effect and reason interfaces, a bounded logical reasoner has no
> asymptotically unexplained advantage either from bypassing protected principal
> authority or from selectively controlling the decision-relevant information on which
> that authority is exercised.  Any remaining advantage is accounted for by explicit
> physical mediation costs, principal decision error, comparison failure, finite inquiry
> limitations, finite service capacity, or representation assumptions.

It is a schema assembled from LEAN components (A1–A3, S1–S4, C1–C4, D1–D3, E1–E3) with
named EXT contracts; it is not one Lean declaration, and it does not say the agent
values control, that manipulation is eliminated, that all relevant reasons are
discovered, that ontology adequacy is learned, that the world cannot be changed, or that
Logical Induction creates corrigibility.

## 8. Hypotheses and boundaries

| class | hypothesis | where it enters |
|---|---|---|
| logical/semantic | `Γ` carries the interaction and reason models; a consistent world at every stage; efficient emission of the sentence and LUV families | A3, S3, E1 |
| logical/semantic | the committed program is extensional; its adverse sensitivity certificate | S2, C1, D1 |
| architectural | effect completeness; mediation soundness, decline preservation, execution faithfulness | A1 |
| architectural | sealed comparison (item 89) | A4 |
| architectural | trace mediation by re-execution; content-monotone audit; sound authentication | S3, E2 |
| architectural | independent supplier: advisor-proof capacity, exogenous service and authentication costs | C2, C3 |
| architectural | independent inquiry: evidence-sound outcomes, engine-owned selection, stopping and candidate generation, exogenous inquiry costs | D3, D4 |
| representation | the declared reason interface `I` and its granularity; the declared hypothesis space `Ω` and repertoire | S5, D5 |
| causal contract | declared log transforms and inquiry outcome functions are the counterfactuals they name | S4, D3 |
| physical | every authority-changing causal path passes through the effect interface | A1 (EF) |

These are boundaries, not unfinished pieces: representation adequacy, physical effect
completeness, inquiry causal faithfulness, dynamic competence (Continuation BRIA,
legitimate evolution) and the evolution of the reason representation itself
(legitimacy/normativity) are the next agenda, not corrigibility residuals.

## 9. The twenty attacks

| # | attack | disposition |
|---|---|---|
| 1 | undeclared effect | excluded by effect completeness (EXT); fixture F of PR #100 |
| 2 | undeclared reason type | excluded by the declared representation (EXT); first-pass fixture 7, discovery row 18 |
| 3 | insufficient reason granularity | excluded by the declared representation (EXT); fixture 8, row 19 |
| 4 | approved irreversible effect | covered: authorized (event-linked), A1 |
| 5 | repeated independently approved effects | covered: `ShopRepair`, event-linked authorization, A1 |
| 6 | raw policy destroys the evaluator | charged to `M` (E2 of PR #100); zero under sealing (item 89) |
| 7 | truthful cherry-picking | charged to the content residual; bounded by the service theorem (fixture 2; C2) |
| 8 | reason order only | charged to the form residual; zero for an extensional program (S2) |
| 9 | flooding inquiry candidates | covered under engine-owned candidate generation (discovery row 4) |
| 10 | raising inquiry cost | excluded by exogenous inquiry costs (row 5) |
| 11 | raising service cost | excluded by exogenous service costs (second-pass row 12) |
| 12 | finite service bottleneck | charged to `α_n`: the cut excess (C2) |
| 13 | information-cell indistinguishability | charged to `β_n`: the cell gap (D3; rows 11, 12) |
| 14 | direct-query needle | charged to `β_n` at the budgeted value (D4; row 14) |
| 15 | adaptive-query advantage | covered: the minimax value is adaptive (D4; row 15) |
| 16 | world manipulation makes a counterreason false | effect side: an effect through the effect interface or an undeclared effect (first-pass fixture 6) |
| 17 | evidence tampering | excluded by evidence soundness of the repertoire (authentication of the inquiry channel) |
| 18 | principal program reads metadata | charged to the form residual; excluded by extensionality (S2; fixtures 3–5) |
| 19 | defeat-sensitive program | covered by conditional adverse sensitivity (D1; rows 7, 8) and the general obstruction (D3) |
| 20 | actual world outside declared `Ω` | excluded by representation adequacy (EXT); D5 |

## 10. Verification status

Lean: `Corrigibilization.lean` (11 declarations), `LICorrigibility.lean` (25),
`LICorrigibilityCertificate.lean` (15), `TraceSteering.lean` (11), `ReasonSupply.lean`
(14), `ReasonDiscovery.lean` (13); all sorry-free, axioms `[propext, Classical.choice,
Quot.sound]`.  Fixtures: 45 tests (PR #100 round) and 51 tests (this round), exact
rationals, random-instance checks against exhaustive search where a characterization is
claimed.  Imported mathematics: Hall's theorem (Mathlib), Expectation Provability
Induction and the generability interface (the pinned Formalized-Agent-Foundations),
decision-tree minimax and matroid greedy (cited, fixture-checked).
