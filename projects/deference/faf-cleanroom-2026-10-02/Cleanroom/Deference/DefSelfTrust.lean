import Cleanroom.Deference.DefSelfTrust.Ramp
import Cleanroom.Deference.DefSelfTrust.Comb
import Cleanroom.Deference.DefSelfTrust.Transfer
import Cleanroom.Deference.DefSelfTrust.Weights
import Cleanroom.Deference.DefSelfTrust.FeatComb
import Cleanroom.Deference.DefSelfTrust.SelfInstances
import Cleanroom.Deference.DefSelfTrust.Est
import Cleanroom.Deference.DefSelfTrust.Diamond
import Cleanroom.Deference.DefSelfTrust.Legitimacy
import Cleanroom.Deference.DefSelfTrust.GateCollapse
import Cleanroom.Deference.DefSelfTrust.RobustSelfTrust
import Cleanroom.Deference.DefSelfTrust.Pseudorandom
import Cleanroom.Deference.DefSelfTrust.Witness
import Cleanroom.Deference.DefSelfTrust.SoftUpdate
import Cleanroom.Deference.DefSelfTrust.Grades

/-!
# `def-self-trust`: the self-case is free — over FAF

Root module of the package `Cleanroom.Deference.DefSelfTrust`. Every deference notion of record
in `def-lattice`, instantiated at the novice's own future self `Expert.self P DP f` over the
paper's inductor `P = liaHistory (paperDP T)`, with hypothesis provenance (a) throughout.
Mandate: `run/wp/def-self-trust/def-self-trust-mandate.md`; report, findings and ledger beside
it.

* `Ramp` (6a): ramp arithmetic — Lipschitz, monotone, sandwich, no-false-positives products.
* `Comb`, `FeatComb`: constant- and feature-coefficient LUV combinations with compact syntax;
  the zero-prefix patch and the eventual forms of `thm:expprovind`.
* `Transfer` (1c): the quote-transfer lemma (FAF's own quote ↔ every reflecting quote).
* `Weights` (decision 3): the pull-back along an injective deferral; the ramp of the deferred
  expectation as a `GeneratedRatFeature` (the `est` weight); closure lemmas.
* `SelfInstances` (1a, 1b, 9, 10): `selfTower_valued`, `selfCondTower`, `selfCeu`, `mergeHop1`;
  `not_all_valued` (the mandate's conditional `Tower` form has a refutable antecedent — the
  all-`⊤` family `allTop` is e.c. and valued by no world — so it is not stated) and
  `selfTower_allTop` (on that very family the self-expert's `Tower` instance still holds).
* `Est` (2): **`est`** — `selfTotalTrust : TotalTrust P DP (Expert.self P DP f)`, both faces.
* `Diamond` (3): `selfCase_diamond` (Tower on valued sources ∧ CondTower ∧ TotalTrust ∧
  δ-hedged two-option Value against the constant), `selfCase_twoOptionValue`.
* `Legitimacy` (4a, 4b): `legitimacyGated_tower_of_generable`, `gatedSelfTrust_productForm`,
  `modifiedTower_decomposition`, `correctionFunction_idle`.
* `GateCollapse` (5): Lemma B, Prop 3.1, the T1 identity by two routes.
* `RobustSelfTrust` (6): Lemma C, Theorem B, Corollary B.1, both faces (up- and down-ramps);
  Prop 6.3's numerical example.
* `Pseudorandom` (7, 4c(i)): uniform accuracy is false on pseudorandom targets; the `truthStar`
  instance; the deferred-day `thm:benford` on the family of record (OPEN,
  `truthStar_deferred_benford`); a pseudorandom truth sequence is not a generable weight of its
  own market.
* `SoftUpdate` (11): the soft update is directed; the converse refuted by a constant history.
* `Grades` (8): the pointwise gated law is free in the self-case specialization; the margin-free
  sum is governed by the square of the `cee` gap (its divergence is OPEN, `selfV_divergent_open`).
* `Witness`: the witness of `est` whose gate is provably live and dead infinitely often (graded
  N− for the content: the source is decided), and the parity-source inhabitant of Theorem B's
  hypothesis package (`theoremB_parity_instance`).

Repair round 1 (2026-09-30): see `run/wp/def-self-trust/def-self-trust-report.md`
§ Repair round 1.
-/
