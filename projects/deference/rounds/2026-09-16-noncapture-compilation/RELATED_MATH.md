# Related mathematics: what is imported and what is new

**Status:** `ci-only`.  Citations are to the standard sources; nothing below is claimed
as new except where marked.

## The service problem is a known object

With a common deadline `T`, release times `a_r`, and a supplier with per-slot capacity,
the question "which reasons can be served before `T`" is a bipartite assignment problem
whose neighbourhoods `[a_r, T)` are **nested**.

- **Feasibility of full service** is Hall's marriage theorem (P. Hall, *On representatives
  of subsets*, J. London Math. Soc. 10 (1935) 26–30), in the form Mathlib carries
  (`Finset.all_card_le_biUnion_card_iff_exists_injective`).  Because the neighbourhoods
  are nested, Hall's condition collapses to the **suffix cuts**; with general integer
  costs and capacities and preemptive service it is the max-flow/min-cut condition on the
  nested network, the same reduction as Gale–Hoffman for interval neighbourhoods
  (D. Gale, *A theorem on flows in networks*, Pacific J. Math. 7 (1957) 1073–1082;
  A. J. Hoffman, *Some recent applications of the theory of linear inequalities to
  extremal combinatorial analysis*, Proc. Sympos. Appl. Math. 10 (1960) 113–127).  The
  affordability round's BD1 uses the interval case for a uniform delay `H`
  (`projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/BOUNDED_DELAY_TRANSPORT.md`);
  the reason-supply problem is the common-deadline case, where the interval `[a_r, a_r+H]`
  becomes the suffix `[a_r, T)`.
- **The least number missed** is the deficiency form of Hall's theorem (König–Ore):
  the size of a maximum matching is `#R − max_S (#S − #N(S))⁺`, which on nested
  neighbourhoods is `#R − max_s (Demand(s) − Cap(s))⁺`.
- **Maximum-weight service with unit costs**: the servable sets form a **transversal
  matroid** (J. Edmonds and D. R. Fulkerson, *Transversals and matroid partition*, J.
  Res. Nat. Bur. Standards 69B (1965) 147–153), so the greedy algorithm by weight is
  optimal (R. Rado, *Note on independence functions*, Proc. London Math. Soc. 7 (1957)
  300–320; J. Edmonds, *Matroids and the greedy algorithm*, Math. Programming 1 (1971)
  127–136).  For nested (more generally convex) bipartite graphs the greedy matching
  is Glover's (F. Glover, *Maximum matching in a convex bipartite graph*, Naval Res.
  Logist. Quart. 14 (1967) 313–316).  The layer formula `Σ_j (w_(j) − w_(j+1))·rank(top-j)`
  is the standard expression of the greedy value through the rank function.
- **General processing times**: minimizing the weighted number of late jobs on one
  machine with a common deadline, `1 | d_j = d | Σ w_j U_j`, contains knapsack and is
  NP-hard (R. M. Karp, *Reducibility among combinatorial problems*, in Complexity of
  Computer Computations, 1972, 85–103); it has a pseudo-polynomial dynamic programme
  (E. L. Lawler and J. M. Moore, *A functional equation and its application to resource
  allocation and sequencing problems*, Management Sci. 16 (1969) 77–84).  The unweighted
  case is polynomial (J. M. Moore, *An n job, one machine sequencing algorithm for
  minimizing the number of late jobs*, Management Sci. 15 (1968) 102–109).  With release
  dates and preemption, feasibility of meeting all deadlines is earliest-deadline-first
  (W. A. Horn, *Some simple scheduling algorithms*, Naval Res. Logist. Quart. 21 (1974)
  177–185), which with a common deadline is any work-conserving order.
- **Online with a common deadline and unit costs**: serving the heaviest available job
  is optimal by the exchange argument (a special case of the fact that the greedy on a
  matroid can be run in arrival order when the ground set is revealed in a way that
  never removes options); the affordability round's online gap (OS1) concerns
  prices revealed later, not capacity.

## What is new here

- The identification of the **missed adverse mass** as the content term of the steering
  inequality, and the choice of the adverse sensitivity certificate over count, weight
  or symmetric sensitivity (`CONTENT_RESIDUAL.md`), with the telescoping and omission
  lemmas in Lean.
- The **decomposition** of the missed mass into discovery, service and authentication
  with scope outside, and the observation that only the service part is a computation on
  the log, hence `Γ`-valid (`SUPPLY_THEOREM.md` §3).
- The **hybrid bound**: protected scope turns missing mass into void rather than charge,
  so the protected set is a design parameter and "protect a servable set of largest
  adverse mass" is the rule (`hybrid_bound`, Lean).
- The **composition** with Expectation Provability Induction through the landed
  compiled pair, so that a per-world certified bound on the content LUV yields
  `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α` with no new certificate (`li_gated_le`, `li_noncapture`,
  Lean).
- The **negative** results: greedy fails for general costs; redundancy makes every
  static certificate loose; discovery is policy-dependent; cost influence by the advisor
  breaks the cut; all as exact fixtures.

## What is deliberately not imported

The affordability round's liability geometry (signed cumulative account, star-shaped
per-date costs, the sharp persistence criterion, D4's sliding-window sum) is the
**budget** resource of a supplier whose service is enforcement.  Reason supply has a
second, structurally shared resource, **capacity in release windows**, and that is
where the Hall form lives.  The two coexist: a supplier is affordable when both the
suffix-cut condition (capacity) and D4's sum over `[a_r, T)` (budget) hold.
`AFFORDABILITY_REFINEMENT.md` records the interface.
