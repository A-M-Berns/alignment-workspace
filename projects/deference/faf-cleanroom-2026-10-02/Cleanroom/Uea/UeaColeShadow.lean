import Cleanroom.Uea.UeaColeShadow.Defs
import Cleanroom.Uea.UeaColeShadow.Facts
import Cleanroom.Uea.UeaColeShadow.TheoremB
import Cleanroom.Uea.UeaColeShadow.Instances
import Cleanroom.Uea.UeaColeShadow.Floored
import Cleanroom.Uea.UeaColeShadow.Existence
import Cleanroom.Uea.UeaColeShadow.Gap
import Cleanroom.Uea.UeaColeShadow.SinkOrSwim
import Cleanroom.Uea.UeaColeShadow.Chain
import Cleanroom.Uea.UeaColeShadow.InstanceA
import Cleanroom.Uea.UeaColeShadow.Open
import Cleanroom.Uea.UeaColeShadow.PureT2
import Cleanroom.Uea.UeaColeShadow.Encoding
import Cleanroom.Uea.UeaColeShadow.Convex
import Cleanroom.Uea.UeaColeShadow.Strict
import Cleanroom.Uea.UeaColeShadow.InstanceW

/-!
# `Cleanroom.Uea.UeaColeShadow`: Cole's theorem in the finite shadow

Root module of the `uea-cole-shadow` work package (faf-cleanroom run, 2026-09-30). Dependents
(`uea-sink-swim`, `uea-self-game`) import this one name.

* `Defs`: the finite model (`Model`), histories, the non-self mixture, the self-hypothesis, the
  mixture `ξ` built from a policy, values by backward induction, `π⋆`, the trust bound, the plain
  and floored fixed-point predicates, and `IsPure` (definitions of record).
* `Facts`: kernel normalisation, value bounds, the mixture identities, F1, F2, Lemma A, Lemma A′.
* `TheoremB`: the per-action inequality and Theorem B (with refinement and corollary).
* `Instances`: Instance B exact, the refutation of the key lemma (`key_lemma_refuted`); `InstanceA`: Instance A.
* `Floored`: Theorem C, horizon form (depth-refined).
* `Chain`: the chain of equality nodes for every `K`, `δ`; the refutation of the horizon-free `C · O_h` bound.
* `Existence`: continuity on the product of simplices; plain and floored fixed points exist by
  `kakutani_pi_stdSimplex` with the closed graph proved.
* `Gap`: the strict-reset map — soundness of the contradiction argument; on Instance B no fixed point and no
  closed graph.
* `SinkOrSwim`: the sink-or-swim family; Theorem B's tightness witnesses (each step of the two-step bound
  attained separately: the first at the tight trap, the second at the informative mixed witness).
* `Open`: the open statements (Theorem C's `ln⁺` form, pure fixed points at `T ≥ 3`); a leaf — nothing in the
  library imports it.
* `PureT2`: pure plain and floored fixed points exist at `T = 2` (with the corrected score).
* `Encoding`: Gap 2 — the continuous, order-faithful encoding `G` (model-free).
* `Convex`: the convexified reset map on Instances B (unique fixed point `(1,1)`, not plain) and A (`t⋆`);
  Instance A at `t = 0` as the strict-reset map's fixed point (witness for `IsStrictResetFP.sound`).
* `Strict`: Theorem B is strict — `gap < O_h` whenever `0 < w_h < 1` (target 10 resolved: the bound is never
  attained; the tight trap approaches it).
* `InstanceW`: the `w_h = 1` corner — a plain fixed point with a decision node the residual never reaches, where
  `gap = 0 = O_h` (Theorem B's bound attained; `w_h < 1` in `Strict` is necessary).
-/
