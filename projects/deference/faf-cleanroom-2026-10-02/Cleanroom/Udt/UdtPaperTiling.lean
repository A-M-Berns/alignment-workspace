import Cleanroom.Udt.UdtPaperTiling.Structure
import Cleanroom.Udt.UdtPaperTiling.StructureWitness
import Cleanroom.Udt.UdtPaperTiling.ElimOrder
import Cleanroom.Udt.UdtPaperTiling.Rules
import Cleanroom.Udt.UdtPaperTiling.Theorem1
import Cleanroom.Udt.UdtPaperTiling.Theorem1Witness
import Cleanroom.Udt.UdtPaperTiling.Vingean
import Cleanroom.Udt.UdtPaperTiling.VingeanWitness
import Cleanroom.Udt.UdtPaperTiling.Collapse
import Cleanroom.Udt.UdtPaperTiling.Coordination
import Cleanroom.Udt.UdtPaperTiling.CoordinationWitness
import Cleanroom.Udt.UdtPaperTiling.Theorem2Witness
import Cleanroom.Udt.UdtPaperTiling.Tables
import Cleanroom.Udt.UdtPaperTiling.IncomparableWitness
import Cleanroom.Udt.UdtPaperTiling.ThirdButton
import Cleanroom.Udt.UdtPaperTiling.ThirdButtonPrior
import Cleanroom.Udt.UdtPaperTiling.PolicyLevel
import Cleanroom.Udt.UdtPaperTiling.PolicyLevelWitness
import Cleanroom.Udt.UdtPaperTiling.MuggingEvidence
import Cleanroom.Udt.UdtPaperTiling.Slides

/-!
# `Cleanroom.Udt.UdtPaperTiling`: the Understanding Trust paper's UDT tiling theorems

Root module of the `udt-paper-tiling` work package (faf-cleanroom run, 2026-09-30). Report,
findings, ledger and open list in `run/wp/udt-paper-tiling/`. Dependents (`udt-bli-tiling`)
import this one name; `PolicyCoordination`, `thm2_udt10_tiling` and `thm2_no_strict_selfMod` are
the declarations it cites for bli-paper-006/007.

* `Structure`, `StructureWitness`, `ElimOrder` — the paper's formalism (T1): `PaperStructure`,
  `WellTyped`, `NonMod`, `elim`, `EffData` (grade (c)), the construction of record
  `CausalStructure.effCausal` with non-modification, idempotence and typing as theorems, Paul's
  race conditions, the order-independence of iterated `elim` *among rank-sorted orders*
  (`elimSeq_eq_effCausal`: in any rank-sorted enumeration one pass of `elim` equals `effCausal`;
  OPEN in round 1, proved in repair round 1; a rank-sorted enumeration always exists,
  `effCausal_reached`), and the fourth race condition `Chain.limit_not_unique` (repair round 2):
  under a valid causal structure the paper's *unordered* "limit of repeated applications of
  `elim`" is still not unique, so the causal order is a clause of the definition of `eff`, not a
  consequence of the three hypotheses.
* `Rules` — the paper layer over `udt-bli-core`'s `ProcLayer`, `chosenEU`, `IsUDT10`, `IsUDT11`,
  the null-event lemmas (T2).
* `Theorem1`, `Theorem1Witness` — Policy Fairness identified with `PolicyFair`, Theorem 1 as one
  application (weak tiling), the unfair layer and a fairness-free paper prior as failure
  witnesses (T3).
* `Vingean`, `VingeanWitness` — Limited Self-Modification, Fine-Grained Fairness, the
  computation-output model `ArgmaxVars`, Faith in (Joint) Argmax, (Naive) Action Coordination,
  Knowledge of Decision Procedure, Theorems 3 and 4, the twelve-world N+ witness and the separable
  N− check (T4, T5).
* `Collapse` — the extensional reading is empty: constant-maximizer Faith holds in every model,
  Action Coordination is an equation between constants, KDP nulls the chain's cells (T6).
* `Coordination`, `CoordinationWitness`, `Theorem2Witness`, `IncomparableWitness` — Policy
  Coordination and its variants, Theorem 2 (fixed-point form, the paper's corollary, and the
  forced tie `thm2_forced_tie`), the squeeze `PCAtEff`, mix-and-match, strict PC vacuous at an
  optimum and Theorem 2 false under it, the restricted variants' countermodel, tie-PC
  inconsistent, the two witnesses of Theorem 2's full package (repair round 1), Theorem 1's
  package on a paper layer, PC and extensional NAC incomparable (T7, T8, T9).
* `ThirdButton`, `ThirdButtonPrior`, `Tables` — the 5/10/20 game over `instanceGame`, its pure and
  mixed equilibria (EconCSLib's `IsMixedNashEq`, `q = 1/3`), Coordinated Buttons as a self-trust
  failure, the refutation of naive communicative cloning (T10).
* `PolicyLevel`, `PolicyLevelWitness` — the policy-level modification model: kernel, three
  fairness notions, Avoidability, the mixture identity, the tiling theorem, kernel idempotence,
  the bridge `policyFair_iff_meanFair`, and the five witnesses (T12).
* `MuggingEvidence` — Counterfactual Mugging with Evidence, Versions A and B, over `udt-bli-core`'s
  independent-policy construction: `NoCrossBranch` holds in A and fails in B, the optima, the
  exact threshold `10/11` (T13).
* `Slides` — the slides diffed against the paper, value relevance (T14, T15).
-/
