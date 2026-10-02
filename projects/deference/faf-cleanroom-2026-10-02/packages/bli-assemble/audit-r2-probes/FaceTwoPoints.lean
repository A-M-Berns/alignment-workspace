import Cleanroom.Bli.BliAssemble.Inherit

/-!
# Audit probe (bli-assemble, round 2, adversarial): the product face has two points, both charged

[[bli-program]] §7 item 11 lists "a face with one point" and "`d = 1`" among the degenerate
witnesses and asks every `N+` row to name "a face with `≥ 2` points". Round 1 (adversarial N6)
found that `bli_hypotheses_paperDP`'s conjunct (4) exhibits one face point and nothing states the
face has two; repair round 1 recorded the fact as true but not landed (budget). This probe lands
it, for every mesh, every day and every day-`n` table, in the shape the row can conjoin:

* `freshCoord n` — the atom `a` with `a + 5 = 4 ^ sizeBound n`, of token size `sizeBound n + 2`:
  not small on day `n`, small on day `n + 1` (the new coordinate `S (n+1) \ S n`).
* `faceProd_two_points` — the `0/1` copy of `t` (as `exists_mem_faceProd`) with the fresh
  coordinate set to `0`, and the same with it set to `1`, are two distinct points of the face.
* `bliHistory_pos_on_two_face_points` — `𝐏` charges both (`bliHistory_tent_nonDegenerate`).
* the `d ≥ 2` half of the guard at the mesh of record: `dyadicMesh.d (n+1) = 2^(n+1) ≥ 2`.

Elaborated with `scripts/lean-check`; not imported by the library.
-/

namespace Cleanroom.Bli.BliAssemble.AuditR2

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliAssemble

open Classical

noncomputable section

/-- The fresh day-`(n+1)` coordinate: the atom `a` with `a + 5 = 4 ^ sizeBound n`. -/
def freshCoord (n : ℕ) : Sentence := Formula.atom (4 ^ sizeBound n - 5)

lemma two_le_sizeBound (n : ℕ) : 2 ≤ sizeBound n := by
  unfold sizeBound
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

lemma five_le_pow_sizeBound (n : ℕ) : 5 ≤ 4 ^ sizeBound n :=
  calc 5 ≤ 4 ^ 2 := by norm_num
    _ ≤ 4 ^ sizeBound n := Nat.pow_le_pow_right (by norm_num) (two_le_sizeBound n)

lemma sizeBound_succ (n : ℕ) : sizeBound (n + 1) = sizeBound n * sizeBound n := by
  unfold sizeBound
  rw [pow_succ, pow_mul, pow_two]

/-- Its token size is `sizeBound n + 2`. -/
lemma tokenSize_freshCoord (n : ℕ) : tokenSize (freshCoord n) = sizeBound n + 2 := by
  unfold freshCoord
  rw [tokenSize_atom, Nat.sub_add_cancel (five_le_pow_sizeBound n),
    length_natDigits4_eq_log (by positivity), Nat.log_pow (by norm_num)]

/-- Not small on day `n`. -/
lemma freshCoord_not_mem (n : ℕ) : freshCoord n ∉ smallSet n := by
  rw [mem_smallSet]; unfold SmallOn; rw [tokenSize_freshCoord]; omega

/-- Small on day `n + 1`. -/
lemma freshCoord_mem (n : ℕ) : freshCoord n ∈ smallSet (n + 1) := by
  rw [mem_smallSet]; unfold SmallOn; rw [tokenSize_freshCoord, sizeBound_succ]
  have := two_le_sizeBound n
  nlinarith

/-- The `0/1` copy of `t` with the fresh coordinate set to `v`. -/
def facePt (n : ℕ) (t : Table smallIndex n) (v : ℚ) : Table smallIndex (n + 1) :=
  fun ψ => if ψ.1 = freshCoord n then v else
    if h : ψ.1 ∈ smallIndex.S n then (if t ⟨ψ.1, h⟩ = 1 then 1 else 0) else 0

lemma facePt_mem (𝓜 : Mesh) (n : ℕ) (t : Table smallIndex n) {v : ℚ}
    (hv : v ∈ gridVals (𝓜.d (n + 1))) : facePt n t v ∈ faceProd smallIndex 𝓜.d n t := by
  rw [mem_faceProd_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_grid_iff]
    intro ψ
    unfold facePt
    split_ifs
    · exact hv
    · exact one_mem_gridVals (𝓜.d_pos _)
    · exact zero_mem_gridVals _
    · exact zero_mem_gridVals _
  · rintro ⟨φ, hφ⟩ h01
    rw [Table.restrict_apply]
    unfold facePt
    dsimp only
    have hne : φ ≠ freshCoord n := fun h => freshCoord_not_mem n (h ▸ hφ)
    rw [if_neg hne, dif_pos hφ]
    split_ifs with h1
    · exact h1.symm
    · rcases h01 with h0 | h1'
      · exact h0.symm
      · exact absurd h1' h1

/-- **The face has two points**, for every mesh, day and table. -/
theorem faceProd_two_points (𝓜 : Mesh) (n : ℕ) (t : Table smallIndex n) :
    ∃ A ∈ faceProd smallIndex 𝓜.d n t, ∃ B ∈ faceProd smallIndex 𝓜.d n t, A ≠ B := by
  refine ⟨facePt n t 0, facePt_mem 𝓜 n t (zero_mem_gridVals _),
    facePt n t 1, facePt_mem 𝓜 n t (one_mem_gridVals (𝓜.d_pos _)), ?_⟩
  intro h
  have := congrFun h ⟨freshCoord n, freshCoord_mem n⟩
  simp [facePt] at this

/-- **`𝐏` charges two distinct face points on every day** — the shape conjunct (4) of
`bli_hypotheses_paperDP` can take (instantiate `Q := liaBase`, `c := writeOutCoding 𝓜`,
`hQ := range_of_isLogicalInductor …`). -/
theorem bliHistory_pos_on_two_face_points (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) :
    ∃ A ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex Q n),
      ∃ B ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex Q n), A ≠ B ∧
        0 < bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)) ∧
        0 < bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) B)) := by
  obtain ⟨A, hA, B, hB, hne⟩ := faceProd_two_points 𝓜 n (actualTable smallIndex Q n)
  refine ⟨A, hA, B, hB, hne, ?_, ?_⟩
  · have := bliHistory_tent_nonDegenerate c Q hQ n A hA
    unfold bliHistory
    exact_mod_cast this
  · have := bliHistory_tent_nonDegenerate c Q hQ n B hB
    unfold bliHistory
    exact_mod_cast this

/-- The `d ≥ 2` half of §7 item 11's guard at the mesh of record. -/
example (n : ℕ) : 2 ≤ dyadicMesh.d (n + 1) := by
  show 2 ≤ 2 ^ (n + 1)
  exact Nat.le_self_pow (Nat.succ_ne_zero n) 2

end

end Cleanroom.Bli.BliAssemble.AuditR2

#print axioms Cleanroom.Bli.BliAssemble.AuditR2.faceProd_two_points
#print axioms Cleanroom.Bli.BliAssemble.AuditR2.bliHistory_pos_on_two_face_points
