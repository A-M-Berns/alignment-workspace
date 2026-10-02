import Cleanroom.Lit.LitWeathersonFrames.Pooling
import Cleanroom.Lit.LitWeathersonFrames.PoolingWitnesses
import Cleanroom.Lit.LitWeathersonFrames.PoolingCountable
import Cleanroom.Lit.LitWeathersonFrames.Chain
import Cleanroom.Lit.LitWeathersonFrames.CFrame
import Cleanroom.Lit.LitWeathersonFrames.Ray
import Cleanroom.Lit.LitWeathersonFrames.Coin
import Cleanroom.Lit.LitWeathersonFrames.Bentham
import Cleanroom.Lit.LitWeathersonFrames.Composite

/-!
# lit-weatherson-frames — root module

Weatherson, *Deference and Infinite Frames*: the pooling theorems and the countable frames.
Gallow's and Zhang's theorems on finite carriers with the extremal proof and the `Fin 8`
refutation of the open reading (`Pooling`, `PoolingWitnesses`); Zhang with finite range on any
carrier (`PoolingCountable`) and the chain on `ℤ × Bool` showing it does not extend to countable
ranges (`Chain`); countable frames, the definitions of record and Value ⟹ Total Trust on every
countable frame (`CFrame`); ray frames, the lumping bridge to the dependency's finite Geanakoplos
theorems and the ray lemma (`Ray`); frame Coin (`Coin`); frame Bentham and the null-event
artifact (`Bentham`); the composite and the OPEN of record (`Composite`). Mathlib-only above
`Cleanroom.Trust.TtFiniteFrames` and `Cleanroom.Found.LitDdbFrames`, and free of measure theory:
`GallowCondExp` (S1, Gallow's theorem over Mathlib's `condExp`) is deliberately left out of this
root so that dependents stay light; import it by name.
-/
