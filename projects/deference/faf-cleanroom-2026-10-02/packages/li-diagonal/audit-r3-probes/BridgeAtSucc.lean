import Cleanroom.Li.LiDiagonal.Forcing

/-!
# li-diagonal · audit round 3 (fidelity) · probe: Lemma B's bridge at `succDeferral`

Repair round 2 added `padG_codes_succ : MachineSentenceCodes (padG succDeferral)` and the
rows `forcingA_of_lemmaB` / `two_faces_pair_of_lemmaB`, whose Hyps cell lists `hG` as (c)
"(a) at `succDeferral`". No declaration in the package instantiates the bridge at `succ` with
`hG` discharged. This probe does, so the (a)-ness of `hG` at `succ` is machine-checked rather
than asserted: over a diagonal pair at `succDeferral`, Forcing Theorem A and the two-faces
statement follow from `cross.reflected` and the two side certificates `hR`, `hR'` alone.
Not imported by the library.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- `succDeferral` is injective (`n ↦ n + 1`). -/
theorem succDeferral_injective : Function.Injective succDeferral.f :=
  fun _ _ h => Nat.succ_injective h

/-- Forcing Theorem A at `succDeferral`, `hG` discharged by `padG_codes_succ`: only
`cross.reflected` (inside `D`) and the two side certificates remain. -/
theorem forcingA_of_lemmaB_succ (D : DiagonalPair succDeferral)
    (hR : MachineSentenceCodes (padTrueSide D.pair.a succDeferral))
    (hR' : MachineSentenceCodes (padFalseSide D.pair.a succDeferral)) :
    (fun n => D.pair.A n (D.pair.quoted 0 n)) ≈ₙ fun _ => (1 / 2 : ℝ) :=
  forcingA_of_lemmaB D succDeferral_injective hR hR' padG_codes_succ

/-- The cross-process two-faces statement at `succDeferral`, `hG` discharged. -/
theorem two_faces_pair_of_lemmaB_succ (D : DiagonalPair succDeferral)
    (hR : MachineSentenceCodes (padTrueSide D.pair.a succDeferral))
    (hR' : MachineSentenceCodes (padFalseSide D.pair.a succDeferral)) :
    (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |(D.pair.a 0 n : ℝ) - side (D.pair.a 0) n|) ∧
    ∀ u : ℕ → EF, PGenerableWeighting u → DivergentWeighting u D.pair.A →
      HasLimitPoint (weightedAverage (fun i => (u i).denote D.pair.A)
        (fun n => side (D.pair.a 0) n - 1 / 2)) 0 :=
  two_faces_pair_of_lemmaB D succDeferral_injective hR hR' padG_codes_succ

end Cleanroom.Li.LiDiagonal
