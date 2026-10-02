import Cleanroom.Bli.BliMeasure.Worlds
import Cleanroom.Bli.BliMeasure.Grid
import Cleanroom.Bli.BliMeasure.Kernel
import Cleanroom.Bli.BliMeasure.Face
import Cleanroom.Bli.BliMeasure.Round
import Cleanroom.Bli.BliMeasure.Measure
import Cleanroom.Bli.BliMeasure.Coherence
import Cleanroom.Bli.BliMeasure.Bayes
import Cleanroom.Bli.BliMeasure.Constraints
import Cleanroom.Bli.BliMeasure.Dogmatism
import Cleanroom.Bli.BliMeasure.NullConditioning
import Cleanroom.Bli.BliMeasure.Base
import Cleanroom.Bli.BliMeasure.Witness
import Cleanroom.Bli.BliMeasure.Lic
import Cleanroom.Bli.BliMeasure.Refuted
import Cleanroom.Bli.BliMeasure.Ui
import Cleanroom.Bli.BliMeasure.Introspective
import Cleanroom.Bli.BliMeasure.Norm
import Cleanroom.Bli.BliMeasure.NormLimit

/-!
# `bli-measure`: B3, the measure-valued BLI over the coherent inductor

Root module of the package `bli-measure` (area `bli`, namespace `Cleanroom.Bli.BliMeasure`), over
`bli-coherent-mm` (the coherent recursion `pcQuote`/`pcCoreWeights`), `bli-finite` (`coherentGrid`,
`remainderRound`, `Traj`), `bli-superbelief` (`faceAverage`, `faceGen_eq_hullFace`), `bli-found`
(`StateSystem`, the constraints `E1r`–`E5`, `TB`, `PCP`, `CoherentOn`, `bliDP`) and
`bli-trajectory` (`stateData`, `BayesRatio`, `TB_on`).

**B3 of record** (finding F1, [[bli-measure-findings]]): the day-`m` state is the **rounded world
measure itself** — a `(1/d m)·ℕ` weight vector on `FiniteWorld (B m)`, coded as a table over the
index of world conjunctions `wIndex B` — not a price table on `smallSet m` with a canonical
selection (which cannot be a world measure across horizons). The kernel is `bli-superbelief`'s
face average over the stage-free coherent grid; `𝐏_n` is the disintegration "trajectory law ×
last vector" at any covering horizon (`b3Mass_succ`: horizon consistency, by balance on world
conjunctions).

* **Worlds, Grid, Kernel, Face, Round, Measure** — target 0: the definitions of record.
* **Coherence** — target 1: `b3History_coherentOn` — `𝐏_n` is coherent on every finite algebra
  relative to `DP.D n ∪ {realized state literals, days ≤ n}` (pinning along the chain keeps the
  stage-free kernel inside the base's support); `PCP` over `bliDP` proved.
* **Bayes** — target 3, the flagship: `b3_TB` — exact total Bayesian update on **every** sentence
  (the statement `bli-trajectory` refutes for B1), by the front decomposition of the chain.
* **Constraints** — target 2: `E1r`/`E1x`/`E2x`/`E3`/`E4` on the state-free scope with the atom
  bound (finding F2: a Markov superbelief does not honor `bli-found`'s `Sminus` scope — refuted
  on a past state atom, `paper_E2x_refuted`/`paper_E3_refuted`; the future-atom case argued), `E5`
  exactly, `FS`, the bundle `IsBLI_B3`; `RespectsPast` for the full `smallSet` scope (an
  assumption, refuted at the instantiation of record).
* **Refuted** — target 2, the other half (repair round 1): `bli-found`'s `E1r`, `E1x` (on the
  denominator mesh), `E2x`, `E4` and `IsBLI_AppB` are **refuted** for B3 of record on the real
  construction, at the realized day-`0` state's atom; so are `RespectsPast` and obstruction (ii)
  of target 7 (`paper_*_refuted`).
* **Dogmatism** — target 4: the face on the grid of record is a support condition; the realized
  next state is charged under the per-day mesh proviso (automatic on the denominator mesh).
* **NullConditioning** — target 4's N− (repair round 2): a concrete dogmatic base over the empty
  process whose next measure leaves the support, so `𝐏_n(σ_{n+1}) = 0` and `b3_TB` reads `0 = 0`
  there — the degeneracy the hypothesis-free flagship admits, which `Witness.lean`'s N+ excludes
  on the real construction.
* **Base** — the instantiation over `bli-coherent-mm`'s recursion (`X := smallSet`, running-maximum
  bounds, measures spread over fibers) and over `paperDP 𝗜𝚺₁`; **conditional on
  `bli-coherent-mm`: computability open**.
* **Witness** — the N+ instance of `TB` over the paper process on the denominator mesh.
* **Lic** — target 7: `IsLogicalInductor` for B3 stated OPEN with its obstructions named (B3 is
  noncomputable as defined — `ComputableMarket` undetermined from the definition, finding F5;
  exact small agreement fails on past state atoms on every mesh, `Refuted.lean`).
* **Ui** — target 8: exact UI for families whose implications lie in the stage; exact HM over the
  paper process.
* **Introspective** — target 9: the coherent-introspective inductor, stated OPEN over fresh
  quote atoms of record (`introQuote`, family `9`) and the adjoined quote process
  (`IntroQuoteProcess`: the base's own true quote literals, learned eventually), the base run
  over and inexploitable over that process (repair round 2).
* **Norm** — target 6: Conjecture 2 repaired online — the normalized world measure (a), the N−
  over FAF's LIA (the default branch is hit at every finite day), (d) OPEN.
* **NormLimit** — target 6 (c), proved (repair round 2's push): the normalizer tends to `1` for a
  logical inductor (`normSum_tendsto_one`: FAF's `thm:con` and Gaifman coherence of the limit
  over the exclusive, exhaustive family `{φ_u}`), and the online weights converge to the limiting
  belief of the world conjunctions (`normWeights_tendsto`).

Target 5 (Soto's PDF 05 objects) is `Worlds.lean` (`WMeasure`/`wMarginal`, `wMarginal_eq_sum_filter`,
`respects_iff`). Target 10 is not attempted ([[bli-measure-report]]).
-/
