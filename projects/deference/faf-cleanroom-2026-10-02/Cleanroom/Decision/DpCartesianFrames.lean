import Cleanroom.Decision.DpCartesianFrames.Observe
import Cleanroom.Decision.DpCartesianFrames.Profiles
import Cleanroom.Decision.DpCartesianFrames.Local
import Cleanroom.Decision.DpCartesianFrames.Straddle
import Cleanroom.Decision.DpCartesianFrames.Reloc
import Cleanroom.Decision.DpCartesianFrames.Hon
import Cleanroom.Decision.DpCartesianFrames.MapWorld
import Cleanroom.Decision.DpCartesianFrames.Witnesses
import Cleanroom.Decision.DpCartesianFrames.RelocWitnesses
import Cleanroom.Decision.DpCartesianFrames.OneRound
import Cleanroom.Decision.DpCartesianFrames.ChuWitnesses
import Cleanroom.Decision.DpCartesianFrames.TreeM
import Cleanroom.Decision.DpCartesianFrames.Congr
import Cleanroom.Decision.DpCartesianFrames.Records
import Cleanroom.Decision.DpCartesianFrames.Xor
import Cleanroom.Decision.DpCartesianFrames.Cff8
import Cleanroom.Decision.DpCartesianFrames.Shadows
import Cleanroom.Decision.DpCartesianFrames.TypeA
import Cleanroom.Decision.DpCartesianFrames.HypsLoadBearing
import Cleanroom.Decision.DpCartesianFrames.Diag
import Cleanroom.Decision.DpCartesianFrames.DiagStruct
import Cleanroom.Decision.DpCartesianFrames.DiagWitnesses

/-!
# `dp-cartesian-frames`: decision trees as Cartesian frames

Root module of the package `Cleanroom.Decision.DpCartesianFrames`, over `dp-core-tree`,
`dp-fairness-reloc` and FAF's `CartesianFrames`. See `run/wp/dp-cartesian-frames/`.

* `Observe`: post 11's observability predicates over FAF's `Frame` (an FAF API request), the
  sum and tensor of frames; CF-8, CF-9, monotonicity under `assume` (T8(a)), biextensional
  invariance (T9(a)), the assuming definition (T10(b)), `External ≅ &` of commits (T12(a)).
* `Profiles`: the representation of record — lazy chance profiles, the run, `Fr`, `FrFine`,
  `FrNode`, `Loc`, `S_O`; T1(b) `Loc d B ◁ₓ Fr B` on the nose; T1(c) `Fr B ◁₊ Fr^nd B`.
* `Local`: the run lemmas and the Local Theorem (T3).
* `Straddle`: straddling, the no-straddle theorem, Lemma A, CFF-13(a) (T6).
* `Reloc`: the diagonal profile, the identified frame, UN-7 (T7).
* `Hon`: the honest companion, the truth test, ZO-8's image-product criterion (T9).
* `MapWorld`: the frame of a relabelled tree.
* `Witnesses`: the AMD, the inert simulation, the umbrella-mugging, the policy-menu mugging,
  the mugging and its decoupling, look-decide, the β-pair.
* `RelocWitnesses`: the relocated mugging — strongly fair, coin not column-determined lazily
  (T5(b) ⟹), column-determined and unobservable under identification (CFF-15).
* `OneRound`: the one-round Global Theorem CF-12 and its `&`-decomposition (T4(a),(b)).
* `ChuWitnesses`: UN-6 over the derived frames — no lazy Chu morphism `Fr B₁ ⟶ Fr (Rel B₁)`, the
  counit unique (T7(d)).
* `TreeM`: CFF-13's tree `M`, the N+ witness of headline 3 and of CF-12 (repair round 1); the
  β-pair is N− for both directions of dp-core-063; the backward direction refuted
  non-degenerately by tree `Mₓ` (`M` with unequal `d`-copies, repair round 2); observable at
  `Loc d` while coverage fails, non-degenerately on CF-10's three-branch mugging variant
  `uncov3` (repair round 3; the two-branch `uncovTree` regraded N−).
* `Congr`: `&` and `⊗` respect `≃ᵇ` (T10(a)).
* `Records`: ZO-15 — pruned + recording at `d` for every procedure ⟹ `S_{O_d}` column-determined
  at `Loc d`; the global-frame variant refuted; the converse refuted (T11(d)).
* `Xor`: ZO-14 — the XOR tree's coin partition is observable in `Fr` and not at `Loc d` (T11(c)).
* `Cff8`: CFF-8 — "spurious queries are frame-invisible" is false lazily (the relocated inert
  query), true under identification and for chance-free subtrees (T8(c)).
* `Shadows`: CF-23 — the β-pair has one frame and different shadows; the scrambled-consultation
  pair has equal shadows for every procedure and inequivalent frames (T5(c)).
* `TypeA`: CF-16 — Transparent Newcomb at `Loc d_E` (V1: `{S_E, S_F}` a true Observation; V2:
  `S_E` not column-determined — the wedge) and at `Loc d_F` (the full-box event not
  column-determined in both variants — "never a proper Observation"), and Told-You-So's `O_5`
  not column-determined but controllable (T11(b), T9(c)).
* `HypsLoadBearing`: the mugging shows the hypotheses of headline 3 (`StronglyFair`, no
  straddle) and of CF-12 (`hV`) are load-bearing, in the global frame `Fr` (repair round 2).
* `Diag`: the kernel of the chosen diagonal `diag` is "same leaf under every pure policy",
  for every `U` (`diag_eq_iff`); so `diag` is not injective even on a chance-only tree, and
  ZO-5(b)'s nested/non-nested distinction is invisible to `FrIdent` (repair round 3).
* `DiagStruct`: the structural diagonal `diagS`/`diagStruct` (copies read their original's
  coordinate, consulted or not — CFF-A's identification, no choice), the structural
  identified frame `FrIdentS`, **ZO-5(c)** (`diagStruct_injective_of_not_nestedFiber`: no
  nested `U`-fiber ⟹ the column map is injective) and **ZO-5(b) "if"**
  (`frLitIsoFr_of_injective`, `frLit_iso_fr_of_not_nestedFiber`: the literal identified
  frame is isomorphic in `Chu(W)` to `Fr B` under the row bijection and the column identity)
  — T7(c)'s core half (repair round 3).
* `DiagWitnesses`: UN-7 for the structural frame; the 2-fold linear mugging (ZO-5's own
  numbers) where the structural diagonal forgets the transfer coin (ZO-5(b) "only if",
  `notInjective_diagStruct_zm`); the zero-mass variant showing the mandate's positive-mass
  `¬ Nested` hypothesis is not enough (`not_nested_insufficient`, findings F20).
-/
