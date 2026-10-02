import Cleanroom.Bli.BliFinite

/-!
# `bli-finite` · audit r1 (fidelity) probes

Not imported by the library. Three probes:

* **P1** — the headline statements re-`#check`ed (existence and shape; the plain readings are in
  `bli-finite-audit-r1-fidelity.md` §4).
* **P2** — the extension `faceGen_coherentGrid_not_prod` exhibits a point *outside* the
  coherent-grid face but never shows the face is *nonempty*. It is: the day-1 copy of
  `extT = (1/2, 1/2, 0)` lies on the coherent grid (one unit of world mass on `p ∧ ¬q`, one on
  `¬p ∧ q`) and the point mass at it is a balance solution, so `extT₁ ∈ faceGen (coherentGrid …) extT`.
* **P3** — `actualState` (T8) is *coordinatewise* rounding, the reading `roundTo_not_coherent`
  refutes as coherence-preserving: the rational history whose day-0 table is the coherent
  `roundTable` has an incoherent day-0 `actualState`. So the docstring's "Fidelity: exact" on
  `actualState` oversells relative to the paper's "`D_n` … maintaining propositional consistency".
-/

namespace Cleanroom.Bli.BliFinite.AuditR1Fidelity

open LogicalInduction LO.Propositional Finset BoolPCWorld Classical Cleanroom.Bli.BliFinite

/-! ## P1 — the headlines exist with the shapes the ledger claims -/

#check @twoAxiom_iff_worldMarginal
#check @coherentOn_iff_twoAxiom
#check @roundTo_not_coherent
#check @twoAxiom_on_given_sentences_only_not_coherent
#check @twoAxiom_signed_counterexample
#check @exists_gridRound
#check @worldRound_coherent
#check @worldRound_mem_coherentGrid
#check @worldRound_err
#check @faceGen_subset_faceProd
#check @nonDegenerate_iff_support_eq_faceProd
#check @trajLaw_chain
#check @trajLaw_martingale
#check @tentLaw_pos_iff
#check @tentLaw_nonDegenerate
#check @faceProd_eq_faceGen
#check @worked_witness
#check @trajLaw_martingale_witness
#check @faceGen_coherentGrid_not_prod

/-! ## P2 — the coherent-grid face over `extT` is nonempty -/

/-- The day-1 copy of `extT`: `(p ↦ 1/2, q ↦ 1/2, p ⋏ q ↦ 0)`. -/
def extT₁ : Table extIndex 1 := fun φ => if φ.1 = pA ⋏ qA then 0 else 1 / 2

lemma extT₁_restrict : extT₁.restrict = extT := by
  funext φ; rfl

/-- One unit of world mass on `p ∧ ¬q`, one on `¬p ∧ q` (total `d = 2`). -/
def extC₁ (u : FiniteWorld 2) : Fin (extMesh.d 1 + 1) :=
  if u = wPnQ then ⟨1, by norm_num [extMesh]⟩
  else if u = wnPQ then ⟨1, by norm_num [extMesh]⟩ else ⟨0, by norm_num⟩

lemma extC₁_val (u : FiniteWorld 2) :
    (extC₁ u).val = (if u = wPnQ then 1 else 0) + (if u = wnPQ then 1 else 0) := by
  unfold extC₁
  by_cases h1 : u = wPnQ
  · subst h1; simp [wPnQ_ne_wnPQ]
  · by_cases h2 : u = wnPQ
    · subst h2; simp [wPnQ_ne_wnPQ.symm]
    · simp [h1, h2]

lemma payout_wPnQ_p : wPnQ.payoutRat pA = 1 := by decide
lemma payout_wPnQ_q : wPnQ.payoutRat qA = 0 := by decide
lemma payout_wPnQ_pq : wPnQ.payoutRat (pA ⋏ qA) = 0 := by decide
lemma payout_wnPQ_p : wnPQ.payoutRat pA = 0 := by decide
lemma payout_wnPQ_q : wnPQ.payoutRat qA = 1 := by decide
lemma payout_wnPQ_pq : wnPQ.payoutRat (pA ⋏ qA) = 0 := by decide

lemma extT₁_mem_coherentGrid : extT₁ ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 := by
  unfold coherentGrid
  rw [Finset.mem_image]
  refine ⟨extC₁, ?_, ?_⟩
  · unfold worldWeights
    rw [Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_, ?_⟩
    · simp only [extC₁_val, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · intro u _ φ hφ; simp at hφ
  · funext φ
    unfold marginalOf extT₁
    have hval : ∀ u : FiniteWorld 2, (((extC₁ u).val : ℕ) : ℚ) / (extMesh.d 1 : ℚ) =
        (if u = wPnQ then (1 / 2 : ℚ) else 0) + (if u = wnPQ then (1 / 2 : ℚ) else 0) := by
      intro u
      rw [extC₁_val]
      show _ / ((2 : ℕ) : ℚ) = _
      push_cast
      split_ifs <;> norm_num
    simp only [hval, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hφ := φ.2
    simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with h | h | h <;> rw [h]
    · rw [payout_wPnQ_p, payout_wnPQ_p, if_neg (fun h => by cases h)]; norm_num
    · rw [payout_wPnQ_q, payout_wnPQ_q, if_neg (fun h => by cases h)]; norm_num
    · rw [payout_wPnQ_pq, payout_wnPQ_pq, if_pos rfl]; norm_num

/-- **The coherent-grid face over `extT` is nonempty**: the point mass at `extT₁` is a balance
solution supported on the coherent grid, so `extT₁ ∈ faceGen (coherentGrid …) extT`. Together
with `faceGen_coherentGrid_not_prod` (which puts `extQ₀ ∈ faceProd ∩ coherentGrid` outside the
face), the face is a proper, nonempty subset. -/
theorem extT₁_mem_faceGen_coherentGrid :
    extT₁ ∈ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT := by
  set G := coherentGrid extIndex extMesh.d 1 ∅ 2 with hG
  have hmem : extT₁ ∈ G := extT₁_mem_coherentGrid
  refine mem_faceGen_of_pos (G := G) (F := fun Q => if Q = extT₁ then 1 else 0) ?_ ?_ (by simp)
  · refine ⟨fun Q => ?_, fun Q hQ => ?_, ?_⟩
    · dsimp only; split_ifs <;> norm_num
    · dsimp only
      rw [if_neg]
      intro h; subst h; exact hQ hmem
    · simp only [Finset.sum_ite_eq', hmem, if_true]
  · rw [← extT₁_restrict]
    congr 1
    funext φ
    unfold meanOn
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hmem, if_true]

/-! ## P3 — `actualState` of a coherent history can be incoherent (it is `roundTo`) -/

/-- The rational history whose day-`n` prices are the coherent `roundTable`'s on the three
sentences of `roundIndex` (and `6/10` elsewhere). -/
def coherentHist : RatHistory := fun _ φ =>
  if φ = pA ⋏ ∼qA then 3 / 10 else if φ = ∼pA ⋏ qA then 3 / 10 else 6 / 10

lemma actualTable_coherentHist : actualTable roundIndex coherentHist 0 = roundTable := by
  funext φ; rfl

/-- The day-0 actual table of `coherentHist` is coherent, and its day-0 `actualState` (mesh
`d = 2`) is not: `actualState` is coordinatewise rounding, the reading `roundTo_not_coherent`
refutes. -/
theorem actualState_coherentHist_not_coherent :
    CoherentOn (actualTable roundIndex coherentHist 0) ∅ 2 ∧
    ¬ CoherentOn (actualState roundIndex (fun _ => 2) coherentHist 0) ∅ 2 := by
  rw [actualTable_coherentHist]
  exact ⟨roundTable_coherent, by
    show ¬ CoherentOn (roundTo 2 (actualTable roundIndex coherentHist 0)) ∅ 2
    rw [actualTable_coherentHist]
    exact roundTo_roundTable_not_coherent⟩

end Cleanroom.Bli.BliFinite.AuditR1Fidelity
