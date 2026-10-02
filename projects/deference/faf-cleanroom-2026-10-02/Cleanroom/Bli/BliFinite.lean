import Cleanroom.Bli.BliFinite.Index
import Cleanroom.Bli.BliFinite.Round
import Cleanroom.Bli.BliFinite.Superbelief
import Cleanroom.Bli.BliFinite.Kernel
import Cleanroom.Bli.BliFinite.Actual
import Cleanroom.Bli.BliFinite.Bridge
import Cleanroom.Bli.BliFinite.Coherence
import Cleanroom.Bli.BliFinite.DeFinetti
import Cleanroom.Bli.BliFinite.CoherenceExamples
import Cleanroom.Bli.BliFinite.WorldRound
import Cleanroom.Bli.BliFinite.Tent
import Cleanroom.Bli.BliFinite.Witness
import Cleanroom.Bli.BliFinite.FaceCoherent

/-!
# `bli-finite`: FAF-free foundations of the BLI area — tables, grids, rounding, finite de
Finetti, superbeliefs, kernels, the trajectory law

Root module of the package `bli-finite` (area `bli`, namespace `Cleanroom.Bli.BliFinite`).
A dependent imports this one name and gets, with **no inductor, criterion or construction in
sight**:

* **Index** (T1) — `SmallIndex` (the index of small sentences is a *parameter*; `bli-found`'s
  `smallSet` instantiates it), `Table 𝒮 m := ↥(𝒮.S m) → ℚ`, `Table.InUnit`, `Table.restrict`,
  `Mesh` (`0 < d m`, `d m ∣ d (m+1)` as fields), `gridVals d = {0, 1/d, …, 1}` **with 0 and 1**,
  the product `grid 𝒮 d m`, and the grid lemmas.
* **Round** (T2) — `clamp01`, `roundVal`/`roundTo` (nearest grid value, ties down),
  `roundTo_mem_grid`, `roundTo_err ≤ 1/(2d)`, fixed points 0 and 1.
* **Superbelief** (T5) — `Superbelief 𝒮 m := Table 𝒮 m → ℚ` (no `d` in the type: see its
  docstring), `IsProbOn`/`IsProb` (**with the off-grid support clause**), `massOn`/`mass`,
  `meanOn`/`mean`, `Balanced` (day-`(m+1)` mean restricted to day `m`), `faceProd`, `faceGen`
  (with which "every balance solution is supported inside the face" is definitional, kind `T`),
  `NonDegenerate`, linearity, and the pinning lemmas `faceGen_subset_faceProd`.
* **Kernel** (T6) — `Kernel 𝒮 d m` (`m → m+1`; **no computability field**), `Skeleton`, the
  snoc-oriented `Traj`, `trajLaw` (defined by the recursion), `trajGrid`, `trajLaw_isProbOn`,
  `trajLaw_marginal`, the chain rule `trajLaw_chain`, and the load-bearing
  `trajLaw_martingale` (constraint 4 at every horizon and day, over the skeleton).
* **Actual** (T8) — `RatHistory`, `actualTable`, `actualState`.
* **Bridge** (T8) — `ofBeliefStates` from FAF `RationalBeliefState`s; the only file importing
  `Construction.MarketMaker`.
* **Coherence** + **DeFinetti** (T3) — `GenBy`, `DTaut`/`DContra`/`DEquiv`, `TwoAxiomCoherent`
  (the two axioms **plus non-negativity**, `D`-relativized, over `GenBy A`), its consequences,
  `IsWorldMarginal`, the load-bearing finite de Finetti theorem `twoAxiom_iff_worldMarginal`
  (over FAF's `FiniteWorld B`, atom bound `hB`), `CoherentOn` for tables and
  `coherentOn_iff_twoAxiom`.
* **CoherenceExamples** — `twoAxiom_signed_counterexample` (N−: the paper's pair admits signed
  valuations), `twoAxiom_on_given_sentences_only_not_coherent` (N+: quantifying over the given
  sentences is vacuous), `roundTo_not_coherent` (N−: coordinatewise rounding breaks coherence).
* **WorldRound** (T4) — `exists_gridRound`/`remainderRound` (rounding a probability vector to
  `(1/d)·ℕ`, error `< 1/d` per coordinate), `worldWeights`/`marginalOf`/`coherentGrid`,
  `worldRound` with `worldRound_coherent`, `worldRound_mem_coherentGrid`,
  `worldRound_err < 2^B/d` — the surviving reading of Appendix B's `D_n`.
* **Tent** (T7) — `uniform1`, `tent1` (nonnegative, sums to 1, mean `x`, support = grid iff
  `0 < x < 1`), `tentCoord`/`tentLaw`/`tentKernel`/`tentSkeleton`, `tentLaw_isProb`,
  `tentLaw_balanced`, `tentLaw_pos_iff` (support = product face), `tentLaw_nonDegenerate`,
  and `faceProd_eq_faceGen` (E1 on the product grid).
* **Witness** (T9) — the worked instance `worked_witness` (`S 0 = {p}`, `S 1 = {p, q}`, `d = 2`)
  and `trajLaw_martingale_witness`.
* **FaceCoherent** (extension) — `faceGen_coherentGrid_not_prod`: on the coherent grid the face
  is not a product.

The definitions of record do not change after the definitions release.
-/
