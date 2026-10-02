import Cleanroom.Bli.BliMeasure.Kernel
import Cleanroom.Bli.BliSuperbelief.Face

/-!
# `bli-measure` · Face: the face-average kernel of record (target 0)

The kernel of record is `bli-superbelief`'s face average `faceAverage (cgrid (m+1)) t`, with full
support exactly on `faceGen (cgrid (m+1)) t`. `bli-superbelief` exports its properties only
through the existential `exists_fullSupport_faceGen` (whose witness *is* `faceAverage`), so the
three properties are re-proved here for the named object (`faceAverage_isProbOn`,
`faceAverage_restrict_meanOn`, `faceAverage_pos_iff`; FAF/bli-superbelief API request: export
them). The nonemptiness hypothesis is discharged on the grid of record by the extension lemma
(`extTable_mem_cgrid`, `extTable_restrict`, `mem_faceGen_of_restrict_eq`). Off `cgrid m` the law
is `0` (junk, disclosed, never charged).
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction Finset Cleanroom.Bli.BliFinite Cleanroom.Bli.BliSuperbelief

variable {𝒮 : SmallIndex} {m : ℕ}

/-! ## The face average, named -/

/-- The face average is a probability on the carrier (when the face is nonempty).
Source: [[bli-program]] §3.4; `bli-superbelief` `exists_fullSupport_faceGen` (its witness)
Kind: L
Fidelity: exact -/
lemma faceAverage_isProbOn (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m)
    (hne : (faceGen G t).Nonempty) : IsProbOn G (faceAverage G t) := by
  have hcard : (0 : ℚ) < (faceGen G t).card := by exact_mod_cast hne.card_pos
  refine ⟨?_, ?_, ?_⟩
  · intro R
    unfold faceAverage
    exact div_nonneg (Finset.sum_nonneg fun Q hQ => (faceWitness_spec hQ).1.1 R) hcard.le
  · intro R hR
    unfold faceAverage
    rw [Finset.sum_eq_zero (fun Q hQ => (faceWitness_spec hQ).1.2.1 R hR), zero_div]
  · unfold faceAverage
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl (fun Q hQ => (faceWitness_spec hQ).1.2.2), Finset.sum_const,
      nsmul_eq_mul, mul_one, div_self hcard.ne']

/-- The face average is balanced (when the face is nonempty).
Source: [[bli-program]] §3.4; `bli-superbelief` `exists_fullSupport_faceGen` (its witness)
Kind: L
Fidelity: exact -/
lemma faceAverage_restrict_meanOn (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m)
    (hne : (faceGen G t).Nonempty) : (meanOn G (faceAverage G t)).restrict = t := by
  have hcard : (0 : ℚ) < (faceGen G t).card := by exact_mod_cast hne.card_pos
  funext φ
  rw [Table.restrict_apply]
  have hφ : ∀ Q ∈ faceGen G t, meanOn G (faceWitness G t Q) ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := by
    intro Q hQ
    have := congrFun (faceWitness_spec hQ).2.1 φ
    rwa [Table.restrict_apply] at this
  unfold meanOn faceAverage
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ Q ∈ faceGen G t,
      ∑ R ∈ G, faceWitness G t Q R * R ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := fun Q hQ => hφ Q hQ
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The face average charges exactly the face (when the face is nonempty).
Source: [[bli-program]] §3.4; `bli-superbelief` `exists_fullSupport_faceGen` (its witness)
Kind: L
Fidelity: exact -/
lemma faceAverage_pos_iff (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m)
    (hne : (faceGen G t).Nonempty) (R : Table 𝒮 (m + 1)) :
    0 < faceAverage G t R ↔ R ∈ faceGen G t := by
  have hcard : (0 : ℚ) < (faceGen G t).card := by exact_mod_cast hne.card_pos
  constructor
  · intro hpos
    by_contra hR
    have hle : ∀ Q ∈ faceGen G t, faceWitness G t Q R ≤ 0 := fun Q hQ =>
      not_lt.mp fun h => hR (mem_faceGen_of_pos (faceWitness_spec hQ).1 (faceWitness_spec hQ).2.1 h)
    have : faceAverage G t R ≤ 0 := by
      unfold faceAverage
      exact div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos hle) hcard.le
    linarith
  · intro hR
    unfold faceAverage
    apply div_pos _ hcard
    calc (0 : ℚ) < faceWitness G t R R := (faceWitness_spec hR).2.2
      _ ≤ ∑ Q ∈ faceGen G t, faceWitness G t Q R :=
        Finset.single_le_sum (fun Q hQ => (faceWitness_spec hQ).1.1 R) hR

/-! ## The kernel of record -/

variable (𝔅 : AtomBounds) (𝓜 : Mesh)

/-- The face over a grid table is nonempty (the extension lemma).
Source: [[bli-measure-mandate]] target 0 (extension lemma discharging `hne`)
Kind: L
Fidelity: exact -/
lemma faceGen_cgrid_nonempty {Q : Table (wIndex 𝔅.B) m} (hQ : Q ∈ cgrid 𝔅 𝓜 m) :
    (faceGen (cgrid 𝔅 𝓜 (m + 1)) Q).Nonempty :=
  ⟨extTable 𝔅 Q, mem_faceGen_of_restrict_eq (extTable_mem_cgrid 𝔅 𝓜 hQ) (extTable_restrict 𝔅 𝓜 hQ)⟩

/-- The law of the kernel of record: the face average on the grid, `0` off it.
Source: [[bli-measure-mandate]] target 0 (`faceKernel`)
Kind: D
Fidelity: exact (off-grid junk `0`, disclosed) -/
noncomputable def faceLaw (m : ℕ) (t : Table (wIndex 𝔅.B) m) : Superbelief (wIndex 𝔅.B) (m + 1) :=
  if t ∈ cgrid 𝔅 𝓜 m then faceAverage (cgrid 𝔅 𝓜 (m + 1)) t else 0

/-- The law at a grid table is the face average.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceLaw_of_mem {t : Table (wIndex 𝔅.B) m} (ht : t ∈ cgrid 𝔅 𝓜 m) :
    faceLaw 𝔅 𝓜 m t = faceAverage (cgrid 𝔅 𝓜 (m + 1)) t := by
  unfold faceLaw; rw [if_pos ht]

/-- **The kernel of record**: the face average over the coherent grid.
Source: [[bli-measure-mandate]] target 0 (`faceKernel`); [[bli-program]] §3.4
Kind: D
Fidelity: exact -/
noncomputable def faceKernel (m : ℕ) : KernelOn (wIndex 𝔅.B) (cgrid 𝔅 𝓜) m where
  law := faceLaw 𝔅 𝓜 m
  prob t ht := by
    rw [faceLaw_of_mem 𝔅 𝓜 ht]
    exact faceAverage_isProbOn _ _ (faceGen_cgrid_nonempty 𝔅 𝓜 ht)
  balanced t ht := by
    rw [faceLaw_of_mem 𝔅 𝓜 ht]
    exact faceAverage_restrict_meanOn _ _ (faceGen_cgrid_nonempty 𝔅 𝓜 ht)
  junk t ht := by
    unfold faceLaw; rw [if_neg ht]

/-- **The skeleton of record**: the face kernel on every day.
Source: [[bli-measure-mandate]] target 0 (`CoherentSkeleton`)
Kind: D
Fidelity: exact -/
noncomputable def faceSkeleton : SkeletonOn (wIndex 𝔅.B) (cgrid 𝔅 𝓜) := ⟨faceKernel 𝔅 𝓜⟩

/-- Unfolding the skeleton's law at a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceSkeleton_law_of_mem {t : Table (wIndex 𝔅.B) m} (ht : t ∈ cgrid 𝔅 𝓜 m) :
    ((faceSkeleton 𝔅 𝓜).κ m).law t = faceAverage (cgrid 𝔅 𝓜 (m + 1)) t :=
  faceLaw_of_mem 𝔅 𝓜 ht

/-- **The kernel of record charges exactly the face**: at a grid table `t`, the next table `Q`
has positive law iff `Q ∈ faceGen (cgrid (m+1)) t`.
Source: [[bli-measure-mandate]] target 0 (`faceKernel` "with full support exactly on `faceGen`")
Kind: L
Fidelity: exact -/
theorem faceKernel_pos_iff {t : Table (wIndex 𝔅.B) m} (ht : t ∈ cgrid 𝔅 𝓜 m)
    (Q : Table (wIndex 𝔅.B) (m + 1)) :
    0 < ((faceSkeleton 𝔅 𝓜).κ m).law t Q ↔ Q ∈ faceGen (cgrid 𝔅 𝓜 (m + 1)) t := by
  rw [faceSkeleton_law_of_mem 𝔅 𝓜 ht]
  exact faceAverage_pos_iff _ _ (faceGen_cgrid_nonempty 𝔅 𝓜 ht) Q

end Cleanroom.Bli.BliMeasure
