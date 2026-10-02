import Cleanroom.Bli.BliSuperbelief.Paper
import Cleanroom.Bli.BliFinite.Tent

/-!
# Audit r3 (adversarial) probe — E6(d)'s superbelief package is inhabited at the LIA's table

`supportEntry_null` concludes `F (actualState …) = 0` for every `F` with `IsProb ∧ Balanced` at
the LIA's day-`n` actual table. If no such `F` existed the theorem would be vacuous in `F`. The
tent kernel is one, for **every** `DP` and `n` (the LIA's quotes lie in `[0,1]`), so the theorem
pins a real object: the tent mass of the realized day-`(n+1)` state is `0` on a support-entry
day. The second example runs the other direction of `dogmatism` on the same object: the face
condition fails there. Not imported by the library.
-/

open LogicalInduction Cleanroom.Bli.BliFinite Cleanroom.Bli.BliFound Cleanroom.Bli.BliSuperbelief

namespace AuditR3

/-- The LIA's actual table is in the unit cube on every day (FAF's `quote_mem_Icc`). -/
lemma lia_actualTable_inUnit (DP : DeductiveProcess) (n : ℕ) :
    (actualTable smallIndex (ofBeliefStates (liaStates DP)) n).InUnit :=
  actualTable_inUnit (ofBeliefStates_inUnit (liaStates DP))

/-- The tent kernel at the LIA's table gives the realized state mass `0` on a support-entry day —
`supportEntry_null` applied to a superbelief that satisfies its package (`tentLaw_isProb`,
`tentLaw_balanced`). -/
theorem tentLaw_null_on_supportEntry (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hoff : φ ∉ (liaStates DP n).support)
    (hnext : 1 / (2 * (𝓜.d (n + 1) : ℚ)) < liaQuote DP (n + 1) φ) :
    tentLaw 𝓜 n (actualTable smallIndex (ofBeliefStates (liaStates DP)) n)
      (actualState smallIndex 𝓜.d (ofBeliefStates (liaStates DP)) (n + 1)) = 0 :=
  supportEntry_null DP 𝓜 n hφ hoff hnext (tentLaw_isProb _)
    (tentLaw_balanced (lia_actualTable_inUnit DP n))

/-- Consistency with `dogmatism`'s positive direction: on such a day the face condition fails at
the LIA's table (the tent kernel is non-degenerate there, so `dogmatism`'s iff applies). -/
theorem face_condition_fails_on_supportEntry (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet n) (hoff : φ ∉ (liaStates DP n).support)
    (hnext : 1 / (2 * (𝓜.d (n + 1) : ℚ)) < liaQuote DP (n + 1) φ) :
    ¬ ∀ ψ : ↥(smallIndex.S n),
        (liaQuote DP n ψ.1 = 0 ∨ liaQuote DP n ψ.1 = 1) →
          roundVal (𝓜.d (n + 1)) (liaQuote DP (n + 1) ψ.1) = liaQuote DP n ψ.1 := by
  intro hface
  have hu := lia_actualTable_inUnit DP n
  have hpos := (dogmatism (𝒮 := smallIndex) (d := 𝓜.d) (ofBeliefStates (liaStates DP)) n
    (tentLaw_isProb _) (tentLaw_balanced hu) (tentLaw_nonDegenerate hu)).mpr hface
  rw [tentLaw_null_on_supportEntry DP 𝓜 n hφ hoff hnext] at hpos
  exact lt_irrefl _ hpos

end AuditR3
