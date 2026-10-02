import Cleanroom.Bli.BliAssemble.SmallList

/-!
# Audit probe (bli-assemble, round 2, adversarial): `smallList` really executes, and how fast
`sentencesUpTo` grows

Repair round 1 landed `smallList` as a compiled `def` (the gate cannot see whether a `def` is
executable beyond the compiler accepting it). This probe runs it: `smallList 0` must be the
sentences of token size `≤ sizeBound 0 = 2`, i.e. exactly `[⊥]` (`tokenSize ⊥ = 1`; every atom has
token size `≥ 3`, every connective `≥ 3`). It also prints the lengths of `sentencesUpTo 1..3` —
`5, 92, 25457` — which square at each level (`|sentencesUpTo (K+1)| ≥ 3·|sentencesUpTo K|²`): the
structural superset is **doubly** exponential in `K`, while `|S n|` (token size `≤ K`) is singly
exponential (`≈ c^K`). So `smallList n` costs exponentially many steps *in `|S n|`*, not
polynomially many — relevant to the handoff's stage-5 remark that `sentencesUpTo` is "exponential
in `K` as a list, which is polynomial in `|S n|`" (it is not); irrelevant to target 5
(`Computable` has no cost), and `smallList 1` is already too long to run (`sentencesUpTo 4` has
about `1.9 · 10⁹` entries).

`#eval` only; nothing is proved here, and nothing is imported by the library.
-/

open Cleanroom.Bli.BliAssemble

#eval (sentencesUpTo 1).length
#eval (sentencesUpTo 2).length
#eval (sentencesUpTo 3).length

#eval (smallList 0).length
#eval (smallList 0).map Encodable.encode
#eval (smallList 0).map fun φ => Cleanroom.Bli.BliFound.tokenSize φ
-- `⊥` has FAF code `0`? Whatever it is, it must coincide with the code of `(⊥ : Sentence)`:
#eval Encodable.encode (⊥ : LogicalInduction.Sentence)
