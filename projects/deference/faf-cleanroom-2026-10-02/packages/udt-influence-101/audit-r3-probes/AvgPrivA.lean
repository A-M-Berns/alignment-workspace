import Cleanroom.Udt.UdtInfluence101.Priv

/-!
# Audit r3 (adversarial) probe: `privA` *is* its own time-`0` average

Not imported by the library. One claim.

The docstring of `Priv.theorem1_fails` (Priv.lean, Fidelity line) grades the witness N+ partly on
the clause "`privA ≠ Ā_{hT,0}` on the support". That clause is false: `privA` reads only the private
root state `ξ₀`, which the time-`0` atom fixes, so its time-`0` conditional average at `hT` is
`privA` itself. This probe proves `play (avg privA hT 0) hT ω = play privA hT ω` at **every** world
(`play_avg_privA`); in particular Assumption 3 for `privA` at `hT` is the identity `x = x`, and the
mechanism of `theorem1_fails` is not "`A` differs from its average" but "`A`'s on-atom action differs
from its global profile" (which the module docstring states correctly). The N+ grade survives on the
other two clauses (`128` positive worlds; `IE_eq` depends on `A`).
-/

namespace Cleanroom.Udt.UdtInfluence101.AuditR3

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Cleanroom.Udt.UdtInfluence101.Home (hT mem_pReach_hT)
open Cleanroom.Udt.UdtInfluence101.Priv
open ProfileModel

noncomputable section

/-- The averaging event at `hT`, time `0`, for any state sequence `s`, contains the world with private
signal `s 0`, a full box and all letters `(true, true, true)`; every world is positive, so it is
positive. -/
theorem avgEvent_pos (s : Fin (hT.1.val + 1) → Bool) :
    0 < mass Priv.S.ℙ.w (Priv.S.avgEvent hT 0 s) := by
  refine mass_pos_of_mem Priv.S.ℙ.nonneg (Priv.S.mem_avgEvent.2 ⟨?_, ?_⟩)
    (baseW_pos (((), s ⟨0, Nat.succ_pos _⟩), fun _ => (true, true, true)))
  · intro i hi _
    have hi0 : i = 0 := Fin.ext (Nat.le_zero.1 hi)
    subst hi0
    rfl
  · exact (mem_pReach_hT _).2 rfl

/-- **`Ā_{hT,0} = privA` at `hT`, at every world**: the time-`0` conditional average of `privA`'s
action is `privA`'s action, because `privA` reads only the private signal the atom fixes. -/
theorem play_avg_privA (ω : PWorld Bool Bool Bool Unit 2) :
    Priv.S.play (Priv.S.avg privA hT 0) hT ω = Priv.S.play privA hT ω := by
  rw [Priv.S.play_avg]
  apply FinDist.ext
  intro a
  rw [Priv.S.avgDist_w_of_pos (avgEvent_pos _)]
  refine condExpJunk_const_on (fun ω' hω' => ?_) (avgEvent_pos _)
  have hs := (Priv.S.mem_avgEvent.1 hω').1 0 le_rfl (Nat.succ_pos _)
  have h0 : ω'.1.2 = ω.1.2 := hs
  show (privA hT (Priv.S.statesAlong ω' hT)).w a = (privA hT (Priv.S.statesAlong ω hT)).w a
  unfold privA
  rw [if_pos rfl, if_pos rfl, statesAlong_zero_eq, statesAlong_zero_eq, h0]

end

end Cleanroom.Udt.UdtInfluence101.AuditR3
