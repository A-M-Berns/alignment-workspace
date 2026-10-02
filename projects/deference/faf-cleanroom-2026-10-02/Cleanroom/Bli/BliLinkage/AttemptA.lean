import Cleanroom.Bli.BliLinkage.AttemptA.Defs
import Cleanroom.Bli.BliLinkage.AttemptA.Forced
import Cleanroom.Bli.BliLinkage.AttemptA.Determination
import Cleanroom.Bli.BliLinkage.AttemptA.AbstractInstance
import Cleanroom.Bli.BliLinkage.AttemptA.Trilemma
import Cleanroom.Bli.BliLinkage.AttemptA.Degenerate
import Cleanroom.Bli.BliLinkage.AttemptA.InstanceB2
import Cleanroom.Bli.BliLinkage.AttemptA.Faith
import Cleanroom.Bli.BliLinkage.AttemptA.Asymptotic

/-!
# `bli-linkage`, attempt A: exact cell-literal linkage — 4′ forced, the determination theorem
and the trilemma, no degenerate linked BLI, faith's scope forced

Root module of attempt A of the dual package `bli-linkage` (area `bli`, namespace
`Cleanroom.Bli.BliLinkage.AttemptA`), over `bli-found` (the B2 state sentence and its cell
literals, the σ-parametric constraints, `Sminus`, `smallSet`) and `bli-trajectory` (the
partition argument's payout lemmas, `cohAtom`). Linkage is propositional: the B2 state sentence
is the conjunction of its cell literals, which partition in every completed-theory world.

* **Defs** — `CellFamily DP` (field `cellLit`), `stateOf`, partition-respecting worlds,
  `CoherentOnCell`/`CoherentOnTheory`, `PCPσ`/`PCPσTheory` (`PCPσ_of_PCPσTheory`), `pinned`,
  `cellMass`, `D_NNUcell`, `Degenerate`, `E2xσIdx` (faith on the written-out coordinates),
  `Tabular`.
* **Forced** (K1) — the σ-parametric partition engine `weight_mul_stateSum`; `forced_marginal`
  / `forced_marginal_base`: constraint 4′ is forced by coherence with the quote atoms;
  `theory_coherent_point_mass`.
* **Determination** (K2) — `balance_at`, `nnu_at`, `determination` (over `E2xσIdx`),
  `determination_e2xσ`, `trilemma_contrapositive` (T0).
* **AbstractInstance** — the Boolean two-cell family over the empty process, the one-coordinate
  index, two tables, `absSystem`, the four worlds and `mix4` with the predicates computed.
* **Trilemma** (K2 witnesses) — `baseQ_viol`, T1/T2/T3 with two tables charged,
  `no_T2_over_coherent_base`, `sharp`, `free_marginal_day_zero`.
* **Degenerate** (K3) — K3a `degenerate_lit_zero`/`_one`/`degenerate_move_zero`; K3b `buyOne`,
  `buyOne_efficientlyComputable`, `buyOne_exploits` (with `hmove` explicit),
  `no_cheap_moving_family`; `no_degenerate_linked_bli`; `degenerate_summable_needed`.
* **InstanceB2** — `b2Family` over `paperDP T` (`stateOf_eq_stateSentence` by `rfl`),
  `halfFamily`/`fixedSystem01` at `𝗜𝚺₁` with endpoint representatives (`Tabular`),
  `forced_marginal_B2`, `determination_B2`, `exists_pinned_from` (the pinned set is eventually
  non-empty), the refutations `e2xσ_unsat_of_unlisted_tautology`/`fixedSystem01_e2xσ_unsat`
  and `witnessRep_faith_unsat`.
* **Faith** (K4) — `liar_holds_iff`, K4b `liar_notMem_Sminus`, K4a
  `faith_full_scope_inconsistent` (completed-theory coherence), K4c `scoped_faith_consistent`
  (N−, a point mass by necessity).

* **Asymptotic** (K5c) — `nnu_asymptotic_threshold`: FAF's `thm:ceu` with `LUV.expect` unfolded, the
  `o(1)` bracket balance in threshold form (ledgered L: a citation, nothing composed).

Not built: `Existence.lean` (K5a/b), `InstanceMoves.lean` (K3's `leakDP` instance),
the B2 cell-literal form of K5c and K6 — see the report.
-/
