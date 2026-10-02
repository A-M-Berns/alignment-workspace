import Cleanroom.Bli.BliCoherentMm.AttemptB.Waived
import Cleanroom.Bli.BliCoherentMm.AttemptB.FixedPoint
import Cleanroom.Bli.BliCoherentMm.AttemptB.Accept
import Cleanroom.Bli.BliCoherentMm.AttemptB.Interior
import Cleanroom.Bli.BliCoherentMm.AttemptB.Contrast
import Cleanroom.Bli.BliCoherentMm.AttemptB.Sat
import Cleanroom.Bli.BliCoherentMm.AttemptB.Recursion
import Cleanroom.Bli.BliCoherentMm.AttemptB.Witness
import Cleanroom.Bli.BliCoherentMm.AttemptB.Payoffs

/-!
# `bli-coherent-mm` · attempt B: the coherent fixed point, the coherent (interior,
truth-respecting) market maker, the propositionally coherent inductor

Angle B of the dual package (namespace `Cleanroom.Bli.BliCoherentMm.AttemptB`): FAF's clipped
price adjustment carried to the simplex and renormalised (`clipMap`), FAF's Brouwer
(`stdSimplex_hasFPP`), and the **rounded** real fixed point (floor-and-dump `gridRound` at a
mesh found by `Nat.find`) as the market maker — no enumeration of rational belief states.

* **Waived** (T0) — `not_exploits_of_dayValue_le_consistent_off_finite`, the stage-relative
  waived-days lemma, and its firm corollaries.
* **FixedPoint** (T1) — `coherent_fixed_point_abstract` (Soto's Theorem 2, proved) and the
  FAF-facing headline `coherent_fixed_point` over `D`-consistent worlds; the identity
  `sum_worldValue_eq_zero` proved, continuity from `EF.continuous_denote`.
* **Accept** (D2–D4, T2) — `IsWorldMeasure`, `piTable`, `ofWeights`, `CoherentAccepts`
  (decidable), the real/rational bridge, `gridRound`, `exists_coherentAccepts`,
  `coherentMesh`/`coherentWeights`/`coherentMarketMaker` with acceptance, coherence
  (`IsWorldMarginal` of the extended table, `CoherentOn`, two-axiom), `respects`,
  `dayValue_le_of_coherentAccepts`, the `smallSet` instance.
* **Interior** (T3) — `interiorCoherentMarketMaker` with full support on `W_D`,
  `interior_nonDogmatic`, `interior_decided_at_truth`, `interior_D_ND_day`.
* **Contrast** (T4(a)–(c)) — `marketMaker_incoherent_on_pair` (FAF's maker is forced incoherent;
  N−/finding), the coherent makers on `T_pair` (N+), the responsive strategy (N+).
* **Sat** (T5) — `pos_iff_satisfiable`.
* **Recursion** (D5, T6) — the coherent overlaid market `pcHistory`, `pcCoreWeights`,
  **`pcOverlay_no_ec_trader_exploits`**, **`pcOverlay_coherent_mentioned`**, `PCInductor`
  inhabited; `ComputableMarket` open.
* **Witness** (T4(d), T6 witness) — the hypothesis package over `paperDP 𝗜𝚺₁`.
* **Payoffs** (T8, extension; FAF-free) — Soto's intermediate payoffs as finite arithmetic:
  the running total is the uniform-completion probability, the three increment rules telescope,
  fully decided worlds and bundles pay their truth, the `½`-forcing per-step inequality.

No `sorry` in the attempt; no OPEN statement (T7 is not attempted in this attempt — see the
report).
-/
