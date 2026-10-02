/-
  Root module of the `dp-troll-bridge` package: Troll Bridge and the Löbian lesion over
  Foundation's GL (the logic under FAF's `ModalAgents`).

  - `Basic`: clauses, the utility encoding, the nested-`if` rule, agents as GL fixed points.
  - `Orderings`: the Troll Bridge theorem (cross-first `χ 🡘 □⊥`), the escapers, the dead
    orderings, the odd one, the dead-tail lemma, Stuart's rewrites, the 12/3/8/1 count.
  - `Lesion`: Lemma 8 / Proposition 9 as the schema `H` (one axiom-L step: the boxed schema
    is boxed staying, `boxdotH_iff_boxdot_neg`), Stuart's schema, the X-troll, the
    exploring-agent troll, the flower fixed point.
  - `Countermodels`: Proposition 10 (`provable_crosser_not_afflicted`, syntactic through
    FAF's `unprovable_box_bot`; the atom form `causal_not_afflicted` kept as a K-fact) and
    every other `GL ⊬` via Kripke countermodels and soundness.
  - `Payor`: Payor's lemma and Payor-bot cooperation.
  - `Fallible`: the fallible troll's threshold.
  - `LILesion`: the Löbian lesion at the level of a logical inductor (the (α)-bridge, the
    coherence step `li_lesion_conj`, the `ε`-conditional composite, and the two OPEN
    statements).
  - `FlowerLI`: Soto's flower obstruction conditional on the quotation portfolio
    (`flower_liminf_of_portfolio`; `theory_coherent` derived from the reflection).

  Repair round 1 (2026-09-30) is recorded in `run/wp/dp-troll-bridge/dp-troll-bridge-report.md`.
-/

import Cleanroom.Decision.DpTrollBridge.Basic
import Cleanroom.Decision.DpTrollBridge.Orderings
import Cleanroom.Decision.DpTrollBridge.Lesion
import Cleanroom.Decision.DpTrollBridge.Countermodels
import Cleanroom.Decision.DpTrollBridge.Payor
import Cleanroom.Decision.DpTrollBridge.Fallible
import Cleanroom.Decision.DpTrollBridge.LILesion
import Cleanroom.Decision.DpTrollBridge.FlowerLI
