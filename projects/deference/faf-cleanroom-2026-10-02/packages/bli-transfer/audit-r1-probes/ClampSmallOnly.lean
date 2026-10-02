import Cleanroom.Bli.BliTransfer.Clamp

/-!
# `bli-transfer` · audit round 1 · adversarial lens · probe: the refutation survives the
program's own scoping of the clamp

**Not imported by the library.** The definition of record clamps *every* sentence; the program
(§3.2(d)) clamps only the day's small sentences `S_k`. Since `⊥` is small on every day
(`bli-found`'s `smallOn_falsum`), the `S_k`-scoped clamp floors `⊥` at `ε_k` too, and the same
`⊥`-seller refutes it: the refutation of T3 is not an artifact of clamping large sentences.
-/

namespace BliTransferAuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliTransfer

/-- The program's clamp, scoped to the day's small sentences; `Q` elsewhere. -/
noncomputable def clampSmall (Q : History) : History :=
  fun k ψ => if SmallOn k ψ then clamp Q k ψ else Q k ψ

/-- The `S_k`-scoped clamp is never a logical inductor either (over a process with consistent
worlds). -/
theorem clampSmall_not_isLogicalInductor (Q : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (clampSmall Q) DP := by
  apply floor_not_isLogicalInductor (clampSmall Q) DP hworld
  · intro n
    simp only [clampSmall, if_pos (smallOn_falsum n)]
    exact le_trans (by exact_mod_cast (epsK_pos n).le) (clamp_mem_Icc Q n ⊥).1
  · intro n
    simp only [clampSmall, if_pos (smallOn_falsum n)]
    exact (clamp_mem_Icc Q n ⊥).1

end BliTransferAuditR1
