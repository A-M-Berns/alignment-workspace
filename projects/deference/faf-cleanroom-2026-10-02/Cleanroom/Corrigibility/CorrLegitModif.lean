import Cleanroom.Corrigibility.CorrLegitModif.Y1Model
import Cleanroom.Corrigibility.CorrLegitModif.Plumbing
import Cleanroom.Corrigibility.CorrLegitModif.Y1Legit
import Cleanroom.Corrigibility.CorrLegitModif.Y1Reflect
import Cleanroom.Corrigibility.CorrLegitModif.Collapse
import Cleanroom.Corrigibility.CorrLegitModif.Separation
import Cleanroom.Corrigibility.CorrLegitModif.LayerCake
import Cleanroom.Corrigibility.CorrLegitModif.Detector
import Cleanroom.Corrigibility.CorrLegitModif.LearnAlpha
import Cleanroom.Corrigibility.CorrLegitModif.Tripwire
import Cleanroom.Corrigibility.CorrLegitModif.FileConfident
import Cleanroom.Corrigibility.CorrLegitModif.Deception
import Cleanroom.Corrigibility.CorrLegitModif.Capability
import Cleanroom.Corrigibility.CorrLegitModif.Capture
import Cleanroom.Corrigibility.CorrLegitModif.Anchors
import Cleanroom.Corrigibility.CorrLegitModif.Reach
import Cleanroom.Corrigibility.CorrLegitModif.Boundary

/-!
# corr-legit-modif — root module

Legitimacy under modification (faf-cleanroom run, 2026-10-02). Files: `Y1Model` (the Y1 model of
record and its values, T1(a)), `Plumbing` (frame lemmas), `Y1Legit` (the legitimacy label at grade
(a), T1(b)), `Y1Reflect` (Reflection from the coarse and the informed judge, T1(d)), `Collapse`
(collapse under Reflection, domination, T2(a)(c)), `Separation` (separation under Total Trust and
the sign flip, T2(b), T3(b)), `LayerCake` (the layer-cake bound, T3(a)), `Detector` (the single-score
detector, T4), `LearnAlpha` (learning `α`, T5), `Tripwire` (T6), `FileConfident` (filing the
confident case in `¬L`, T7; the learned detector, T13), `Deception` (T8), `Capability` (T9),
`Capture` (T10), `Anchors` (the three anchors, T11), `Reach` (T12), `Boundary` (the dodge boundary
and the retention form, T14). Open list (`run/wp/corr-legit-modif/corr-legit-modif-open.txt`) is
empty. Deliverables in `run/wp/corr-legit-modif/`.
-/
