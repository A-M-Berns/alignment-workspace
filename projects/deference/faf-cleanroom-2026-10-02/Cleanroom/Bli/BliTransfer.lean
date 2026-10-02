import Cleanroom.Bli.BliTransfer.Defs
import Cleanroom.Bli.BliTransfer.Certificate
import Cleanroom.Bli.BliTransfer.Transfer
import Cleanroom.Bli.BliTransfer.Restricted
import Cleanroom.Bli.BliTransfer.Clamp
import Cleanroom.Bli.BliTransfer.WitnessLia
import Cleanroom.Bli.BliTransfer.AttemptA
import Cleanroom.Bli.BliTransfer.AttemptB

/-!
# `bli-transfer` — the expressible-overlay transfer theorem (reconciled root)

Root module of the dual work package `bli-transfer` (area `bli`, namespace
`Cleanroom.Bli.BliTransfer`), reconciled from two independent attempts kept as evidence under
`AttemptA/` (angle A: the machine-model flat pass) and `AttemptB/` (angle B: the splice-stream
route). The main modules state each target once over the definitions of record:

* `Defs` — the definitions of record (attempt A's copies, re-exported; bridges to attempt B's),
  the splice of record and its laws.
* `Certificate` — T1.3: the certificate interface (`SpliceOracle`, `SpliceCertificate`,
  `RunAgrees`) and `EfficientlyComputable.spliceOn` for **every** e.c. trader (attempt A).
* `Transfer` — T1: `overlay_isLogicalInductor_of_transfer` (two-hypothesis form),
  `overlay_isLogicalInductor` (certificate form), `overlay_isLogicalInductor'` (**headline of
  record**); T1.4: `overlay_computableMarket`.
* `Restricted` — T2: `restrictedEC_not_exploits_overlay` (disclosed `(c)`: the class), its N+
  witness and the separation.
* `Clamp` — T3 **refuted** (`clamp_not_isLogicalInductor`, attempt B), Known issue 7 refuted
  (`not_magnitude_le_two_pow_poly`), and the reconciliation of the two attempts
  (`clamp_bounded_partial_sums_false`, `clamp_conditional_antecedent_false`: attempt A's
  conditional headline had a false antecedent); `floor_not_isLogicalInductor` (T4's ceiling
  half).
* `WitnessLia` — T1.5: the N+ package at FAF's LIA over `paperDP 𝗜𝚺₁`
  (`witness_package_paperDP`); T3's N+ (`clamp_lia_not_isLogicalInductor`).

T4 (Route A) is an attempt record in the findings (both attempts; the ceiling half refuted);
T5 (iterated overlays) was attempted by neither. Deliverables: `run/wp/bli-transfer/`
(`bli-transfer-report.md` with its "Two attempts" section, `bli-transfer-findings.md`,
`bli-transfer-ledger.md`, `bli-transfer-open.txt` — empty).
-/
