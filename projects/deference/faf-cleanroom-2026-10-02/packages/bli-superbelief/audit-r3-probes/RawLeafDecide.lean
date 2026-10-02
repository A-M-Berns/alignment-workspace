import Cleanroom.Bli.BliSuperbelief.Escape
import Cleanroom.Bli.BliSuperbelief.Witnesses

/-!
# Audit r3 (adversarial) probe — the raw stream of a witness weight term is misparsed

`w0E (price pW 0)` is the first weight of the witness term `tentExpr₁ witMesh 0 Q₁`'s
`p`-coordinate. Its raw serialization (about 30 tokens, one price leaf `[0, 3, 0]`) is read by
FAF's `unRpn` into something else — kernel evaluation on this small concrete stream.
Not imported by the library.
-/

open LogicalInduction Cleanroom.Bli.BliFinite Cleanroom.Bli.BliSuperbelief

namespace AuditR3

example : unRpn (w0E (EF.price pW 0)).serialize ≠ (w0E (EF.price pW 0)).serialize := by
  decide

end AuditR3
