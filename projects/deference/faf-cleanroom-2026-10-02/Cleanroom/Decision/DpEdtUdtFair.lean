import Cleanroom.Decision.DpEdtUdtFair.FairClass
import Cleanroom.Decision.DpEdtUdtFair.Step1
import Cleanroom.Decision.DpEdtUdtFair.Limit
import Cleanroom.Decision.DpEdtUdtFair.Theorem3
import Cleanroom.Decision.DpEdtUdtFair.Assignment
import Cleanroom.Decision.DpEdtUdtFair.DfTheorem
import Cleanroom.Decision.DpEdtUdtFair.Ca3
import Cleanroom.Decision.DpEdtUdtFair.Trees
import Cleanroom.Decision.DpEdtUdtFair.FairWitnesses
import Cleanroom.Decision.DpEdtUdtFair.PermWitness
import Cleanroom.Decision.DpEdtUdtFair.Necessity
import Cleanroom.Decision.DpEdtUdtFair.Threat
import Cleanroom.Decision.DpEdtUdtFair.LimitState
import Cleanroom.Decision.DpEdtUdtFair.Graded
import Cleanroom.Decision.DpEdtUdtFair.GradedWitnesses
import Cleanroom.Decision.DpEdtUdtFair.Corner
import Cleanroom.Decision.DpEdtUdtFair.Newcomblike
import Cleanroom.Decision.DpEdtUdtFair.Devices
import Cleanroom.Decision.DpEdtUdtFair.Records
import Cleanroom.Decision.DpEdtUdtFair.Open

/-!
# `dp-edt-udt-fair`: EDT = UDT on the fair class and its boundary

Root module of the package `Cleanroom.Decision.DpEdtUdtFair`; dependents (`dp-faithful-udt`) import
this one name. Over `dp-core-tree`, `dp-calibration`, `dp-local-opt`, `dp-fairness-reloc`. See
`run/wp/dp-edt-udt-fair/`.

**Definitions of record** (frozen once released):
* `FairClass` — the fair class `𝔉` (A36's (F)(R)(P)(O)), with `Realized`, `FRec`, `FRecPR` (the
  three non-fairness clauses), `Corner` (GR-11); `refChildren`/`Q` — the fiber-constant one-step
  deviation value; `FiberValueBound`, `decDepth` (T9); `N1`, `N2`, `N3` (FR-14).
* Catalogue (`Trees`): `dupPay`, `cornerTree`, `mislabelled`, `doppel`, `tieTree3`, `revTree`,
  `stagObs`/`stagActEv`; (`PermWitness`): `permPay`.

**Theorems** (each file's docstring says which target it serves): `FairClass` (T1),
`Step1` (T2), `Limit` (T3), `Theorem3` (T4: `eventTrembleEdt_isOptimal_of_fairClass`),
`Assignment` (T5: `stronglyFair_assignment`, the leaves-up argmax `exists_pointwise_best`),
`DfTheorem` (T12(b): `fairClass_dfMasked_isOptimal`; Step 1 without the full-support device),
`Ca3` (CA-3′ by the size argument; DF self-models exist on `𝔉`, CA-2′(i); `{D2} ⊆ {DF-EDT}`),
`FairWitnesses` (T1(b), T4 witnesses, T6(a), T8's tremble clause), `PermWitness` (a fiber of isomorphic, unequal members: `permPay_theorem3_witness`), `Necessity` (T7 (ii)–(iv),
T16(a)), `Threat` (T8, T7(i)), `LimitState` (their D1 clauses: `outY_limitStateEdt`), `Graded` (T9: `graded_fr11`, the corner corollary),
`GradedWitnesses` (T9's mugging witness), `Corner` (T1(c)), `Newcomblike` (T10),
`Devices` (T12(a): `FairClass.eventTremble_iff_occTremble`), `Records` (T11(a), ZO-2's chain on
`𝔉`), `Open` (T6(b) as OPEN).
-/
