import Cleanroom.Corrigibility.CorrValueChange.Update

/-!
# corr-value-change — the alternative formalization of conditional reflection (T8(e), S3)

Source: [[value-change-as-epistemic-update]] §2.6 ("An alternative formalization"). Ask that the
installed state, itself conditioned on `L`, match the agent's: `Q_i(· ∣ L) = P(· ∣ E_i, L)`, with
`Q_i` free to carry its own doubt about `L`. If that doubt matches the agent's, `Q_i(L) = P(L ∣ E_i)`,
and the `¬L` parts match too, this is unconditional reflection. Here `L` is an event of the joint
and `L_i = {w ∣ (w, i) ∈ L}` its slice at outcome `i`, which is how a state on `W` can "have a
doubt about `L`".
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W I : Type} [Fintype W] [Fintype I] [DecidableEq W] [DecidableEq I]

/-- The slice `L_i = {w ∣ (w, i) ∈ L}` of an event of the joint at outcome `i`.
Source: [[value-change-as-epistemic-update]] §2.6 (alternative formalization)
Kind: D
Fidelity: exact -/
def Lslice (L : Finset (W × I)) (i : I) : Finset W := univ.filter fun w => (w, i) ∈ L

/-- `Q_i(L_i)`.
Source: [[value-change-as-epistemic-update]] §2.6
Kind: D
Fidelity: exact -/
def QL (Q : Installed W I) (L : Finset (W × I)) (i : I) : ℝ := ∑ w ∈ Lslice L i, Q.Q i w

/-- `P(E_i ∧ L) = ∑_{w ∈ L_i} P(w, i)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πL_eq_sum_slice (J : Joint W I) (L : Finset (W × I)) (i : I) :
    J.πL L i = ∑ w ∈ Lslice L i, J.P w i := by
  unfold Joint.πL Joint.PL Lslice
  rw [sum_filter]

/-- `π_i − P(E_i ∧ L) = ∑_{w ∉ L_i} P(w, i)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_sub_πL (J : Joint W I) (L : Finset (W × I)) (i : I) :
    J.π i - J.πL L i = ∑ w ∈ univ \ Lslice L i, J.P w i := by
  rw [πL_eq_sum_slice, eq_comm, eq_sub_iff_add_eq, sum_sdiff (subset_univ _)]
  rfl

/-- `1 − Q_i(L_i) = ∑_{w ∉ L_i} Q_i(w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem one_sub_QL (Q : Installed W I) (L : Finset (W × I)) (i : I) :
    1 - QL Q L i = ∑ w ∈ univ \ Lslice L i, Q.Q i w := by
  unfold QL
  rw [eq_comm, eq_sub_iff_add_eq, sum_sdiff (subset_univ _)]
  exact Q.sum_one i

/-- **T8(e), the alternative formalization is unconditional reflection**: if, for every outcome of
positive probability, (i) the installed state conditioned on `L_i` is the agent's conditional on
`E_i ∧ L` — `Q_i(w) P(E_i ∧ L) = Q_i(L_i) P(w, i)` for `w ∈ L_i`; (ii) the installed doubt matches the
agent's — `Q_i(L_i) π_i = P(E_i ∧ L)`; and (iii) the `¬L` parts match —
`Q_i(w) P(E_i ∧ ¬L) = Q_i(¬L_i) P(w, i)` for `w ∉ L_i`; then (R⁺) holds. (Each hypothesis is the
product form of the note's equation; the null cases are handled, not assumed away.)
Source: [[value-change-as-epistemic-update]] §2.6 ("so the alternative is the hedged installation in
other notation")
Kind: P
Fidelity: exact (the ⇐ half of the note's sentence; the iff is `alternative_formalization_iff`)
Hyps: (a) `h1`, `h2`, `h3` (the alternative formalization's three clauses); witness
`hedged_alternative_clauses` (CondLegit) -/
theorem alternative_formalization (J : Joint W I) (Q : Installed W I) (L : Finset (W × I))
    (h1 : ∀ i, 0 < J.π i → ∀ w ∈ Lslice L i, Q.Q i w * J.πL L i = QL Q L i * J.P w i)
    (h2 : ∀ i, 0 < J.π i → QL Q L i * J.π i = J.πL L i)
    (h3 : ∀ i, 0 < J.π i → ∀ w ∉ Lslice L i,
      Q.Q i w * (J.π i - J.πL L i) = (1 - QL Q L i) * J.P w i) :
    Reflection J Q := by
  intro i hi w
  by_cases hw : w ∈ Lslice L i
  · rcases (J.πL_nonneg L i).lt_or_eq with hL | hL
    · have := h1 i hi w hw
      have hQL : QL Q L i = J.πL L i / J.π i := by
        rw [← h2 i hi]; field_simp
      rw [hQL] at this
      field_simp at this
      nlinarith [this, hi, hL]
    · -- `P(E_i ∧ L) = 0`: both sides vanish on `L_i`
      have hQL0 : QL Q L i = 0 := by
        have := h2 i hi; rw [← hL] at this
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hi.ne'
      have hQw : Q.Q i w = 0 := by
        have := (sum_eq_zero_iff_of_nonneg fun w _ => Q.nonneg i w).1 hQL0 w hw
        exact this
      have hPw : J.P w i = 0 := by
        rw [πL_eq_sum_slice] at hL
        exact (sum_eq_zero_iff_of_nonneg fun w _ => J.nonneg w i).1 hL.symm w hw
      rw [hPw, hQw, mul_zero]
  · have hw' : w ∈ univ \ Lslice L i := mem_sdiff.2 ⟨mem_univ w, hw⟩
    rcases (sub_nonneg.2 (J.πL_le_π L i)).lt_or_eq with hnL | hnL
    · have := h3 i hi w hw
      have hQnL : 1 - QL Q L i = (J.π i - J.πL L i) / J.π i := by
        rw [← h2 i hi]; field_simp
      rw [hQnL] at this
      field_simp at this
      nlinarith [this, hi, hnL]
    · -- `P(E_i ∧ ¬L) = 0`: both sides vanish off `L_i`
      have hQnL0 : 1 - QL Q L i = 0 := by
        have h2' := h2 i hi
        have : (1 - QL Q L i) * J.π i = J.π i - J.πL L i := by rw [← h2']; ring
        rw [← hnL] at this
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hi.ne'
      have hQw : Q.Q i w = 0 := by
        rw [one_sub_QL] at hQnL0
        exact (sum_eq_zero_iff_of_nonneg fun w _ => Q.nonneg i w).1 hQnL0 w hw'
      have hPw : J.P w i = 0 := by
        rw [π_sub_πL] at hnL
        exact (sum_eq_zero_iff_of_nonneg fun w _ => J.nonneg w i).1 hnL.symm w hw'
      rw [hPw, hQw, mul_zero]

/-! ## The converse: (R⁺) gives the three clauses, so T8(e) is an iff -/

/-- Under (R⁺), clause (ii): `Q_i(L_i) π_i = P(E_i ∧ L)`.
Source: [[value-change-as-epistemic-update]] §2.6 (alternative formalization); audit r1
Kind: L
Fidelity: exact -/
theorem h2_of_reflection (J : Joint W I) (Q : Installed W I) (L : Finset (W × I))
    (h : Reflection J Q) : ∀ i, 0 < J.π i → QL Q L i * J.π i = J.πL L i := by
  intro i hi
  rw [πL_eq_sum_slice]
  unfold QL
  rw [sum_mul]
  refine sum_congr rfl fun w _ => ?_
  rw [h i hi w]; ring

/-- Under (R⁺), clause (i): the installed state conditioned on `L_i` is `P(· ∣ E_i, L)`.
Source: [[value-change-as-epistemic-update]] §2.6; audit r1
Kind: L
Fidelity: exact -/
theorem h1_of_reflection (J : Joint W I) (Q : Installed W I) (L : Finset (W × I))
    (h : Reflection J Q) :
    ∀ i, 0 < J.π i → ∀ w ∈ Lslice L i, Q.Q i w * J.πL L i = QL Q L i * J.P w i := by
  intro i hi w _
  have h2 := h2_of_reflection J Q L h i hi
  rw [← h2, h i hi w]; ring

/-- Under (R⁺), clause (iii): the `¬L` parts agree.
Source: [[value-change-as-epistemic-update]] §2.6; audit r1
Kind: L
Fidelity: exact -/
theorem h3_of_reflection (J : Joint W I) (Q : Installed W I) (L : Finset (W × I))
    (h : Reflection J Q) :
    ∀ i, 0 < J.π i → ∀ w ∉ Lslice L i,
      Q.Q i w * (J.π i - J.πL L i) = (1 - QL Q L i) * J.P w i := by
  intro i hi w _
  have h2 := h2_of_reflection J Q L h i hi
  rw [← h2, h i hi w]; ring

/-- **T8(e) as an iff: the alternative formalization *is* unconditional reflection.** For every
event `L`, the three clauses (i)–(iii) hold iff (R⁺) holds. (⇐ is `alternative_formalization`; ⇒
is `h1_of_reflection`, `h2_of_reflection`, `h3_of_reflection`.)
Source: [[value-change-as-epistemic-update]] §2.6 ("so the alternative is the hedged installation
in other notation"); audit r1 (B3)
Kind: P
Fidelity: exact (the note's sentence is the iff; the earlier theorem is its ⇐ half)
Hyps: (a) none -/
theorem alternative_formalization_iff (J : Joint W I) (Q : Installed W I)
    (L : Finset (W × I)) :
    Reflection J Q ↔
      ((∀ i, 0 < J.π i → ∀ w ∈ Lslice L i, Q.Q i w * J.πL L i = QL Q L i * J.P w i) ∧
       (∀ i, 0 < J.π i → QL Q L i * J.π i = J.πL L i) ∧
       (∀ i, 0 < J.π i → ∀ w ∉ Lslice L i,
         Q.Q i w * (J.π i - J.πL L i) = (1 - QL Q L i) * J.P w i)) :=
  ⟨fun h => ⟨h1_of_reflection J Q L h, h2_of_reflection J Q L h, h3_of_reflection J Q L h⟩,
   fun ⟨h1, h2, h3⟩ => alternative_formalization J Q L h1 h2 h3⟩

end

end Cleanroom.Corrigibility.CorrValueChange
