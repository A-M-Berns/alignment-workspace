import Cleanroom.Bli.BliExtrapolation.Decay

/-!
Audit round 3, adversarial lens — does `decay_witness` really inhabit the *full* hypothesis
package of `decay_scheme_pow`?

`decay_witness` (Decay.lean) computes both sides of the `n = 1` identity independently and says in
its docstring that the halving hypotheses are "discharged by `halving_witness`". But
`halving_witness : HalvingCondition …` is an existential over the level map `k` and the index map
`i`; the witness statement itself never applies `decay_scheme_pow`. Here the theorem is applied
*directly* with `k = halvingK`, `i = id`, every unpacked hypothesis discharged from the package's
own lemmas (`halvingK_strictMono`, `halvingK_zero`, `halving_lev`, `halving_fresh`,
`fresh_undecided`), and the output is read off: at `n = 1` it is `¾`, agreeing with the independent
`halving_val_inst0`; at `n = 2` it is `5/8`, a value the package computes nowhere else.

Not imported by the library.
-/

namespace Cleanroom.Bli.BliExtrapolation.AuditR3Adv

open LogicalInduction LO.Propositional BoolPCWorld Finset
open Classical

/-- The instance atoms of `halvingS` sit at the halving levels (index map `id`). -/
lemma halving_hinst : ∀ n, halvingS.inst 0 (id n) = Formula.atom (freshEnum (halvingK n)) := by
  intro n
  simp [halvingS, halvingK, freshEnum_instAtom]

/-- The agnostic clause at every halving level, from freshness (`halving_of_fresh_instances`'s
argument, unpacked for the explicit `k = halvingK`). -/
lemma halving_hhalf :
    ∀ n (w : FiniteWorld (halvingK n)), AxConsistent halvingS {conj freshEnum w} →
      ¬ (enumWorld freshEnum w).toPCWorld.Holds (halvingS.univSentence 0) →
      ¬ AxEntails halvingS {conj freshEnum w} (Formula.atom (freshEnum (halvingK n))) ∧
        ¬ AxEntails halvingS {conj freshEnum w} (∼Formula.atom (freshEnum (halvingK n))) :=
  fun n w hc hnU => fresh_undecided halvingS freshEnum 0 (halvingK n) n
    (halving_lev.trans (halvingK_strictMono.monotone (Nat.zero_le n)))
    (halving_fresh n (halvingK n) (freshEnum_instAtom n)) w hc hnU

/-- `decay_scheme_pow` applied to the 4b witness: `P(⋀_{j<n} a_j) = ½ + (½)^n · ½`. -/
theorem decay_applied (n : ℕ) :
    extrapolateVal halvingS freshEnum halvingBase (instPrefix (fun j => halvingS.inst 0 (id j)) n) =
      1 / 2 + (1 / 2) ^ n * (1 / 2) := by
  have h := decay_scheme_pow halvingS freshEnum halvingBase 0
    (fun w => by rw [halvingBase_apply]; norm_num)
    (chainPMF_sum_one halfRule 1) halving_baseAxConsistent halvingK id halvingK_strictMono
    (by rw [halvingK_zero]; norm_num) halving_lev halving_hinst halving_hhalf n
  rw [h, halving_val_univ, halving_val_neg_univ]

/-- At `n = 1` the theorem's output is `¾`, which is `halving_val_inst0`'s independent value
(`instPrefix … 1 = ⊤ ⋏ a_0`). -/
theorem decay_n1_crosscheck :
    extrapolateVal halvingS freshEnum halvingBase (instPrefix (fun j => halvingS.inst 0 (id j)) 1)
        = 3 / 4 ∧
    extrapolateVal halvingS freshEnum halvingBase (halvingS.inst 0 0) = 3 / 4 :=
  ⟨by rw [decay_applied]; norm_num, halving_val_inst0⟩

/-- At `n = 2` the theorem gives `P(a_0 ∧ a_1) = 5/8`, a value computed nowhere else in the
package (so the theorem is exercised beyond the witness's own `n = 1`). -/
theorem decay_n2 :
    extrapolateVal halvingS freshEnum halvingBase (instPrefix (fun j => halvingS.inst 0 (id j)) 2)
      = 5 / 8 := by
  rw [decay_applied]; norm_num

end Cleanroom.Bli.BliExtrapolation.AuditR3Adv
