import Cleanroom.Lit.LitShutdownPrefs

/-!
# lit-shutdown-prefs — audit round 2, adversarial lens: probe on the open question

Not imported by the library. Elaborated with `scripts/lean-check`. Evidence for the audit's
non-blocking remark on `PostConsistency.posl_ilpacs_nontrivial_model_open` and on the report's
"what was tried" record (§ Repair round 1, item 4).

**Isolated lotteries.** Call `I` *isolated* for `lt` when nothing is preferred to it and it is
preferred to nothing. Two isolated lotteries are *behaviourally indifferent* for the trivial
reason that both have no sweetenings and no sourings (`indiff_of_isolated`). ILPACS then lets a
strict pair `A ≻ B` be mixed with any two isolated lotteries, and POSL forces the two mixtures to
have the same length set (`isolated_lengths_eq`):

  `A.lengths ∪ I₁.lengths = A.lengths ∪ I₂.lengths`.

Consequences for the record of attempts in the report:

* The "ILPACS-closure of the single preference `[10] ≻ [9]`" (report, Repair round 1, item 4) is
  not a model of POSL ∧ ILPACS whatever its asymmetry: in any relation whose winners all contain
  `[10]` and whose losers all contain `[9]`, the point masses `[0, 0]` and `[0, 0, 0]` are both
  isolated, and `not_both_isolated` shows POSL ∧ ILPACS then fails. So "a Lean proof that the
  closure of item 4 is asymmetric (a model)" cannot settle the question in the existence direction.
* Any model must be *rich*: all its isolated lotteries share the same lengths outside
  `A.lengths`; in particular a model in which every trajectory of length ≥ 2 outside `{1}` is
  isolated is impossible.
* Independently, "the least relation containing the seed and closed under the display" is not
  well defined: the display's antecedents `lacks` and behavioural `indiff` are *negative* in `lt`
  (they shrink as `lt` grows), so the ILPACS rule is not a Horn clause and has no least fixed point
  in general. This is a remark, not a Lean statement.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace AuditR2

open Lottery Strict Finset

/-- The mass of an event under a mixture. -/
theorem mass_mix (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (X Y : Lottery Traj) (q : Traj → Prop)
    [DecidablePred q] : (mix a ha X Y).mass q = a * X.mass q + (1 - a) * Y.mass q := by
  simp [mass, expect_mix]

/-- The lengths of an interior mixture are the union of the lengths. -/
theorem lengths_mix (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (h0 : 0 < a) (h1 : a < 1)
    (X Y : Lottery Traj) : (mix a ha X Y).lengths = X.lengths ∪ Y.lengths := by
  apply lengths_eq_of_mass_pos_iff
  intro l
  rw [mass_mix, Finset.mem_union, mem_lengths_iff, mem_lengths_iff,
    SIS.pos_mix_iff (X.mass_nonneg _) (Y.mass_nonneg _) ha]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr ⟨h1, h⟩

/-- `I` is isolated: nothing is preferred to it and it is preferred to nothing. -/
def Isolated (lt : Lottery Traj → Lottery Traj → Prop) (I : Lottery Traj) : Prop :=
  ∀ Z, ¬ lt Z I ∧ ¬ lt I Z

/-- Two isolated lotteries are behaviourally indifferent, vacuously: neither has a sweetening
or a souring. -/
theorem indiff_of_isolated {lt : Lottery Traj → Lottery Traj → Prop} {I₁ I₂ : Lottery Traj}
    (h₁ : Isolated lt I₁) (h₂ : Isolated lt I₂) : Strict.indiff lt I₁ I₂ :=
  ⟨⟨(h₁ I₂).2, (h₁ I₂).1⟩, fun Z hZ => absurd hZ (h₁ Z).1, fun Z hZ => absurd hZ (h₂ Z).1,
    fun Z hZ => absurd hZ (h₂ Z).2, fun Z hZ => absurd hZ (h₁ Z).2⟩

/-- **Isolated lotteries in a model of POSL ∧ ILPACS with a strict preference `A ≻ B` all have
the same lengths outside `A.lengths`.** ILPACS on `Xs = (A, I₁)`, `Ys = (B, I₂)` with weights
`(½, ½)`: `A` and `I₁` lack a preference (`I₁` is isolated), `A ≻ B`, and `I₁ ≽ I₂` by vacuous
behavioural indifference; so `½A + ½I₁ ≻ ½B + ½I₂`, and POSL makes the two same-length. -/
theorem isolated_lengths_eq {lt : Lottery Traj → Lottery Traj → Prop} (hP : POSL lt)
    (hI : ILPACS lt) {A B : Lottery Traj} (hAB : lt A B) {I₁ I₂ : Lottery Traj}
    (h₁ : Isolated lt I₁) (h₂ : Isolated lt I₂) :
    A.lengths ∪ I₁.lengths = A.lengths ∪ I₂.lengths := by
  have hSAB : A.lengths = B.lengths := hP A B hAB
  have hXY : lt (mix (1/2) (by norm_num) A I₁) (mix (1/2) (by norm_num) B I₂) := by
    refine hI 2 ![1/2, 1/2] ![1/2, 1/2] ![A, I₁] ![B, I₂] _ _ ?_ ?_
      (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
      (fun i j hij => ?_) (fun i => ?_) ⟨0, hAB⟩
    · ext t
      simp only [mix_p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      ring
    · ext t
      simp only [mix_p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      ring
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact ⟨(h₁ A).1, (h₁ A).2⟩
      · exact ⟨(h₁ A).2, (h₁ A).1⟩
      · exact absurd rfl hij
    · fin_cases i
      · exact Or.inl hAB
      · exact Or.inr (indiff_of_isolated h₁ h₂)
  have hS := hP _ _ hXY
  unfold SameLength at hS
  rw [lengths_mix _ _ (by norm_num) (by norm_num), lengths_mix _ _ (by norm_num) (by norm_num),
    ← hSAB] at hS
  exact hS

/-- **The closure route cannot produce a model.** In any relation with `[10] ≻ [9]` in which both
`[0, 0]` and `[0, 0, 0]` are isolated (as they are in every relation whose winners contain `[10]`
and whose losers contain `[9]`), POSL ∧ ILPACS fails. -/
theorem not_both_isolated {lt : Lottery Traj → Lottery Traj → Prop} (hP : POSL lt)
    (hI : ILPACS lt) (h10 : lt (dirac [10]) (dirac [9])) :
    ¬ (Isolated lt (dirac [0, 0]) ∧ Isolated lt (dirac [0, 0, 0])) := by
  rintro ⟨h₁, h₂⟩
  have heq := isolated_lengths_eq hP hI h10 h₁ h₂
  have h2 : (2 : ℕ) ∈ (dirac ([10] : Traj)).lengths ∪ (dirac ([0, 0] : Traj)).lengths := by
    rw [lengths_dirac, lengths_dirac]; simp [len]
  rw [heq, lengths_dirac, lengths_dirac] at h2
  simp [len] at h2

end AuditR2

end Cleanroom.Lit.LitShutdownPrefs
