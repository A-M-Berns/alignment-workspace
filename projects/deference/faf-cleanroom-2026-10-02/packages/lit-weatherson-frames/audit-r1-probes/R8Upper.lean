import Cleanroom.Lit.LitWeathersonFrames.PoolingWitnesses

/-!
Audit r1 (fidelity) probe for `lit-weatherson-frames`. Not imported by the library.

Two ledger claims about the witness column of `zhang_finite_upper` that the package states in
prose but does not compile:
1. `R8` fails the *upper-half* hypothesis `BetweenUpper` (the package compiles `¬ Between4`,
   which could in principle fail through the lower half alone); the failure is at the agreement
   cell `A = B = 4/5`, posterior `17/20 > 4/5`.
2. `G5` inhabits `BetweenUpper` (through `Pools` at `λ = 1/2`), so the upper-half theorem's
   hypothesis package is non-empty.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset

theorem probe_R8_not_betweenUpper : ¬ BetweenUpper R8.C R8.Y R8.A R8.B := by
  intro h
  obtain ⟨c, hc, hle, -⟩ := h (4/5) (4/5)
  norm_num [lev₂, sum_filter, Fin.sum_univ_succ, R8.A, R8.B, R8.C, R8.Y] at hc hle
  linarith

theorem probe_G5_betweenUpper : BetweenUpper G5.C G5.Y G5.A G5.B :=
  ((G5.pools (1/2)).between4 (by norm_num) (by norm_num)).upper

end Cleanroom.Lit.LitWeathersonFrames
