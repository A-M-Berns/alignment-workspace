import Cleanroom.Li.LiCoupledPair.Defs
import Cleanroom.Li.LiCoupledPair.DefsHeavy
import Cleanroom.Li.LiCoupledPair.QuotePackage
import Cleanroom.Li.LiCoupledPair.Scheduling
import Cleanroom.Li.LiCoupledPair.Decided
import Cleanroom.Li.LiCoupledPair.Siblings
import Cleanroom.Li.LiCoupledPair.TwoWay
import Cleanroom.Li.LiCoupledPair.A.Sigma
import Cleanroom.Li.LiCoupledPair.A.SigmaWitness
import Cleanroom.Li.LiCoupledPair.A.LedgerDecided
import Cleanroom.Li.LiCoupledPair.A.Sibling
import Cleanroom.Li.LiCoupledPair.A.Joint
import Cleanroom.Li.LiCoupledPair.A.JointInductor
import Cleanroom.Li.LiCoupledPair.A.Sealed
import Cleanroom.Li.LiCoupledPair.A.SealedInductor
import Cleanroom.Li.LiCoupledPair.A.Open
import Cleanroom.Li.LiCoupledPair.B

/-!
# `li-coupled-pair`: the coupled pair — the quote package discharged, the sealed-sibling family,
and the two-way OPEN of record (reconciled root)

Root module of the dual package `Cleanroom.Li.LiCoupledPair` (mandate:
`run/wp/li-coupled-pair/li-coupled-pair-mandate.md`), reconciled from two independent angles kept
as evidence: **A** (`Cleanroom.Li.LiCoupledPair.A`, `A/`: the Σ₁ discharge from
`Construction/Quotation` and `paperDP`, the staggered joint recursion, the sealed-sibling system)
and **B** (`Cleanroom.Li.LiCoupledPair.B`, `B/`: the conditioning route through `prefixProcess` /
`conditionedHistory` and FAF's `thm:scon`). The five **main modules** state each target once in
the package namespace over the definitions of record, proved by the angle named in each
docstring, and add the reconciler's own results; deliverables in `run/wp/li-coupled-pair/`
(`li-coupled-pair-report.md` with its "Two attempts" section, `-findings.md`, `-ledger.md`,
`-open.txt`).

Definitions of record (shared, written by angle A, imported by B):
* `Defs` (light): the sealed-sibling family `siblingSchedule`/`siblingProcess`/`siblingHistory`
  with `siblingSchedule_mem_iff` (frozen, not delayed), the carriers `SealedSiblingSystem`,
  `TwoWayPair`.
* `DefsHeavy`: the package's one named hypothesis `UniformLIAEvaluator` (FAF's private
  `liaPrefixFromStagesAtFuel_prim`, graded (b)) with `uniform_of_primrec`; the Σ₁ determinacy
  carrier `SigmaPair`.

Main modules:
* `QuotePackage` (T1): **`crossQuotePackage_sigma`** of record (Σ₁, zero (c), timing none; N+
  `sigmaPair_paper`), `liaHistory_eq_machine` (T1.2), and the timed variant kept from angle B —
  **`clockedSeq_codes`** (the conditioning route's (c) discharged) with `clocked_inductor`,
  `crossQuotePackage_clocked` (N+ `paperConditionedPair`); `sigmaPair_H_eq_conditionedPair_H`.
* `Scheduling` (T2, angle B's): `fresh_needs_computable` / `conditioned_needs_machineCodes`
  (T2.1), `quoteStream_cost_le` (T2.2, `≤ t(t−1)`), `theoremDP_is_steps_form` (T2.3),
  `ledgerSeq_codes_of_dominated` (the scheduled record under `FuelDominated`, (c), no instance
  known — `B.exists_fuelDominated` OPEN), `not_perDay_dominated`, `not_fuelDominated_le`,
  `liaHistory_inductor_iff_computable`.
* `Decided` (T3): **`ledgerDecided_iff_computable`** (T3.1, angle A; `computable_of_ledgerDecided`
  over any computable process; N+ `altSel_ledgerDecided`), `psiTieBreak_finite` /
  `psiTieBreak_LI` (T3.3, angle B), and the reconciler's N+ witness `psiTieBreak_LI_paper`
  (`paperDP_tieAtom_undecided`: a fresh atom is undecided both ways by `paperDP 𝗜𝚺₁`).
* `Siblings` (T4.1): **`sibling_inductor`** of record (angle A, fresh LIA on the frozen ledger)
  with `sibling_hworld`, `siblingLuv_determinedVia`, `sibling_agree_below`; angle B's
  `sibling_inductor_B`, `sibling_frozen`, `siblingB_agree_below`, `siblingB_determinedVia`; both
  witnesses (`paperSiblingFamily`, `paperSiblingFamily_B`); the reconciler's
  **`siblingB_literal_iff_siblingA`** (the two frozen processes adjoin the same ledger literals).
* `TwoWay` (T4.2, T4.3, T5, angle A's): the identifications `jointDay_states` / `sealedDay_states`
  (unconditional), `contract_computable`, the inductors and `twoWayPair_exists_of_uniform` /
  `sealedSystem_exists_of_uniform` under `UniformLIAEvaluator` (b), the **OPEN rows of record**
  `twoWayPair_exists` (T5.2) and `sealedSystem_exists` (T4.3) pointing at `A/Open.lean`'s, and the
  unconditional N+ grounds.

Attempt modules (evidence; headlines of their own are in the ledger's second table):
`A/Sigma`, `A/SigmaWitness`, `A/LedgerDecided`, `A/Sibling`, `A/Joint`, `A/JointInductor`,
`A/Sealed`, `A/SealedInductor`, `A/Open`; `B/Clocked`, `B/Conditioned`, `B/Scheduled`, `B/Counting`,
`B/TieBreak`, `B/Sibling`, `B/ConditionedWitness` (root `B.lean`).
-/
