import Cleanroom.Fa.FaAdaptiveJoint.Defs
import Cleanroom.Fa.FaAdaptiveJoint.Expressibility
import Cleanroom.Fa.FaAdaptiveJoint.Counting
import Cleanroom.Fa.FaAdaptiveJoint.Bridge
import Cleanroom.Fa.FaAdaptiveJoint.Theorem2
import Cleanroom.Fa.FaAdaptiveJoint.Witnesses
import Cleanroom.Fa.FaAdaptiveJoint.Staleness
import Cleanroom.Fa.FaAdaptiveJoint.ValueGap
import Cleanroom.Fa.FaAdaptiveJoint.JointClearing

/-!
# `fa-adaptive-joint` — adaptive traders, (A4) expressibility and joint clearing (root)

Root module of `Cleanroom.Fa.FaAdaptiveJoint` ([[fa-adaptive-joint-mandate]]). The package
decides v3's (A4) over FAF's feature language and recovers v3's Theorem 2 (the all-days
violation-weight limit, FA's boxed claim) from FAF's criterion on both sides, with the
`H`-side bridge for one-position weightings as the one OPEN statement.

* `Defs` — the softened one-position machine as an `EF` straight-line program (`adaptFire`:
  `letE` chain, additive softening, open test decided by `f.graph_fp` through the ruler
  `openCount`), its denotation laws (`adaptFire_denoteWith`, `adaptFireR_rec`), `OnePosition`,
  the recursion law `FireRec`.
* `Expressibility` — **T1 `adaptFire_pgenerable`** ((A4)'s expressibility half, decided: the
  machine is a `PGenerableWeighting`), the real firing sequence `fireSeq`, uniqueness of the
  recursion law, closure of (joint) legibility under the machine (`legibleOn_fireSeq_joint`).
* `Counting` — **T2 `FireRec.eventually_lt_of_summable`** (the counting argument), the
  one-position invariant, the additive update, the support clause, F2's product-softening
  counterexample.
* `Bridge` — **T4 `adaptiveBridge`** (OPEN, listed) with its proved hard instance
  `adaptiveBridge_of_schedule := hSideBridge` and `onePosition_of_windowDisjoint_support`.
* `Theorem2` — **T3 `v3Theorem2_of_bridge`** (sorry-free, the bridge as a named hypothesis) and
  the statement of record `v3Theorem2_of_jointLegible` (rests on T4; listed); Corollaries 2, 3;
  the gate-general `v3Theorem2_gate_of_bridge`.
* `Witnesses` — T5: the firing pattern of the saturated machine (`fireSeq_pattern`), T2's and T4's
  real-sequence instances, joint legibility discharged at `A = H` (`legibleOn_viol_self`).
* `Staleness` — T7: the stale gate, what alternation costs (`stale_gate_fires_off_violation`),
  the positive transfer under no one-day jumps, and the OPEN `v3Theorem2_strictAlternation`
  over `AlternatingPair` (listed).
* `ValueGap` — T8: `valueGap_not_persistent` (lean-deference-011's claim located in the
  dependency's Theorem SS under (L)).
* `JointClearing` — T9 (construction-facing; sections C–E reshaped in repair round 1): the
  atom-renamed merged process, world projection/gluing (`consistentWith_mergedStage_iff`,
  `mergedProcess_hworld_iff`), the per-day joint fixed point for an `H`-tagged and an `A`-tagged
  strategy against every pair of half-worlds (`jointClearing_perDay_fixedPoint`), the trader side
  of the projection lemma (`jointClearing_criterion_projection`), tagged LUVs and the sides
  `sideH`/`sideA`, the carrier `JointClearingPair` (families tagged into their halves by the
  type), v3 under joint clearing as a statement through the two sides
  (`v3Theorems_of_jointClearing`), and the OPEN existence `jointClearingPair_exists` (listed;
  `X` pinned; reduces to `li-coupled-pair`'s).

Deliverables: `run/wp/fa-adaptive-joint/fa-adaptive-joint-{report,findings,ledger}.md`,
`fa-adaptive-joint-open.txt`.
-/
