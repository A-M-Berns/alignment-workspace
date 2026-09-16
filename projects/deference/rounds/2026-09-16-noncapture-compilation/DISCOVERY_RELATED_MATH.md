# Related mathematics for discovery: imported versus new

**Status:** `ci-only`.

## Imported

- **Decision-tree / query complexity.**  The budgeted problem "identify enough of a
  hidden object to bring a worst-case loss below `ε`, choosing queries adaptively" is
  minimax decision-tree complexity; the value recursion `V(K, B)` is the standard one and
  the adversary argument (answer so as to keep the largest consistent set) is the
  standard lower-bound technique.  The needle instance is the elementary
  `Ω(n)` lower bound for identifying one of `n` candidates with membership queries.  See
  D. E. Knuth, *The Art of Computer Programming*, Vol. 3, §6.2 for the basic theory of
  such trees, and the information-theoretic bound `⌈log_{|O|} m⌉` on the depth needed to
  separate `m` outcome classes.
- **Generalized binary search / adaptive set cover.**  When the objective is to identify
  the world (not merely a value), greedy policies that maximize the number of hypothesis
  pairs separated are near-optimal in expectation: S. Dasgupta, *Analysis of a greedy
  active learning strategy*, NIPS 2004; D. Golovin and A. Krause, *Adaptive submodularity:
  theory and applications in active learning and stochastic optimization*, JAIR 42
  (2011) 427–486.  These are *average-case* (a prior over worlds) guarantees; the
  worst-case objective of this round has no such approximation guarantee in general, and
  the needle shows why (every policy is equally bad until the end).
- **Hall-type indistinguishability.**  The repertoire cells are the classes of an
  equivalence; that a policy's output is measurable with respect to the cells is the
  elementary fact behind `residual_ge_cellGap`, the same "you cannot act on what you
  cannot see" argument as in the theory of information structures (Blackwell's
  comparison of experiments gives the general form: a policy measurable with respect to a
  coarser partition does no better on any loss).  D. Blackwell, *Equivalent comparisons
  of experiments*, Ann. Math. Statist. 24 (1953) 265–272.
- **Argumentation / defeat.**  The conditional adverse mass is the round's own object,
  but its behaviour under defeat matches the standard picture that reinstatement and
  undercutting are non-monotone in the set of arguments: J. L. Pollock, *Defeasible
  reasoning*, Cognitive Science 11 (1987) 481–518; the workspace's own defeat-landing
  round (`projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/HORTY.md`)
  records that defeat is non-stratified and history-dependent.  Nothing in that landed
  machinery carries numeric force (`.../2026-08-23-reason-representation/MEMO.md`);
  the sensitivity certificates here are properties of the *committed program*, and the
  round does not introduce force into the reason ontology.
- **The workspace's inquiry architecture.**  `wiki/Normative-Record-and-Inquiry.md`
  already docketed inquiry as an ordinary obligation and named set cover with delay,
  submodular ranking and adaptive submodularity as scheduler models; `PRIORITIES.md`
  items 54 (an unprocessed defeater is invisible to the substrate) and 64 (what an inquiry
  step consumes and emits) are the open items this pass touches from the deference side.

## New here

- The **discovery residual** as the omission gain of the undiscovered adverse reasons,
  certified by the **conditional adverse sensitivity above the docket**
  (`adverseAbove_union`), and the **frontier theorem** turning an unresolved reason of
  positive conditional mass into an explicit obligation
  (`residual_le_zero_of_frontier_empty`).
- The **information-cell obstruction** for the discovery residual: least worst-case
  residual with unbounded budget equals the largest cell gap of the repertoire
  (`residual_ge_cellGap`, `exhaustive_attains_cellGap`), the discovery analogue of the
  service cut.
- The **negative result** that no fractional-progress theorem holds for direct-query
  repertoires (the needle), so the budgeted value is a decision-tree quantity and not a
  cut, and the explicit form of the witness-completeness hypothesis under which
  geometric decay does hold (`potential_decay`).
- The **composition** `actual → discovered → full` with the middle family shared, so
  the two second-pass bounds add in Lean (`li_noncapture_chain`), and the observation
  that the discovery bound is `Γ`-valid relative to the declared hypothesis space.
- The **independence conditions** for inquiry, stated as which objects must be the
  engine's (`INQUIRY_MODEL.md` §5), with the flooding, cost and stopping attacks as exact
  instances.
