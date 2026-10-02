import Cleanroom.Lit.LitDdbFacts.Cells
import Cleanroom.Lit.LitDdbFacts.Reflection
import Cleanroom.Lit.LitDdbFacts.Ladder
import Cleanroom.Lit.LitDdbFacts.Convexity
import Cleanroom.Lit.LitDdbFacts.DutchBook
import Cleanroom.Lit.LitDdbFacts.Geometry
import Cleanroom.Lit.LitDdbFacts.Hereditary
import Cleanroom.Lit.LitDdbFacts.Prior
import Cleanroom.Lit.LitDdbFacts.Collected
import Cleanroom.Lit.LitDdbFacts.Examples
import Cleanroom.Lit.LitDdbFacts.ExamplesFig5
import Cleanroom.Lit.LitDdbFacts.ExamplesPrior

/-!
# lit-ddb-facts — root module

Deference Done Better beyond the cycle: the Reflection facts of §1 (`Reflection`), the ladder
Total Trust ⟹ Trust ⟹ New Reflection and the immodest collapse (`Ladder`), the convexity
formulations (`Convexity`), fixed-option Dutch books (`DutchBook`), Facts 4.2/4.3 and
Corollaries 4.4/4.5 (`Geometry`), hereditary deference and positive access (`Hereditary`), prior
frames with the corrected Theorem 7.4 — Trust ⟹ Value on *nested* prior frames, refuted without
nestedness (`Prior`, `ExamplesPrior`), Theorem 5.1 collected (`Collected`), and the
witnesses (`Examples`, `ExamplesFig5`, `ExamplesPrior`). Everything is stated over `lit-ddb-frames`' definitions
of record (`Cleanroom.Found.LitDdbFrames`); dependents import this one name.
-/
