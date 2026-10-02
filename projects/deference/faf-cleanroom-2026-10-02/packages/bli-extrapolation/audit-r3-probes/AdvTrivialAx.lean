import Cleanroom.Bli.BliExtrapolation.Product
import Cleanroom.Bli.BliExtrapolation.Refutations
import Cleanroom.Bli.BliExtrapolation.ConstraintWitnesses

/-!
Audit round 3, adversarial lens — the hypothesis `UnivStructure.TrivialAx` of 5d's
`sotoRule_eq_productRule_iff` (Product.lean) and what the iff distinguishes.

The ledger's Witness cell for the iff names bases (`guardBase`, "every product base") but no
structure `S` with `S.TrivialAx`; if that hypothesis were uninhabitable the headline would be
vacuous. Checked here:

1. `trivS_trivialAx`: `TrivialAx` is inhabited (the template with every instance `⊤`).
2. `trivialAx_forces`, `halvingS_not_trivialAx`: every `TrivialAx` structure has *no quantifier
   content* — each instance holds in every world where its universal does — so the package's own
   `halvingS` is excluded. This is forced by the definition (`Ax S` always contains schema 1), and
   it is what PDF 01's "`Ax = ∅`" means, so the class is degenerate by necessity, not by accident;
   the witness should still be named.
3. On the base side: at `B = 1` every mass-one base is a Bernoulli product, so the iff first bites
   at `B = 2`. `refBase_sotoIsProductAe`: the uniform base `refBase` (`B = 2`, `¼` each) is a
   product and Soto's rule is product on its positive prefixes. `twoBase_not_sotoIsProductAe`:
   the two-cell base `chainPMF twoCellRule 2` (`q(T,F) = ⅓`, `q(F,T) = ⅔`, zeros elsewhere) has
   Soto's rule read `0` and `1` on the two positive-mass level-`1` prefixes, so it is not product
   there, and by the (⇐) direction of the iff, contrapositively, it is not a product base
   (`twoBase_not_isProduct`) — a non-trivial consequence, obtained through the headline.

Not imported by the library.
-/

namespace Cleanroom.Bli.BliExtrapolation.AuditR3Adv

open LogicalInduction LO.Propositional BoolPCWorld Finset
open Classical

/-- The template with every instance `⊤`: `Ax` consists of the tautologies `U_u 🡒 ⊤`. -/
def trivS : UnivStructure := mkStructure (fun _ => ⊤) (fun _ => ⊤)

/-- `TrivialAx` is inhabited. -/
theorem trivS_trivialAx : trivS.TrivialAx := by
  intro v
  rw [trivS, mk_axHolds_iff]
  exact ⟨fun _ _ => PCWorld.holds_top v, fun _ _ => PCWorld.holds_top v⟩

/-- Under `TrivialAx` every instance holds wherever its universal does, in every world: the
structure has no quantifier content. -/
theorem trivialAx_forces (S : UnivStructure) (hS : S.TrivialAx) (u i : ℕ) (v : PCWorld)
    (hU : v.Holds (S.univSentence u)) : v.Holds (S.inst u i) := by
  have hax : S.univSentence u 🡒 S.inst u i ∈ Ax S := by
    left; left; exact ⟨u, i, rfl⟩
  exact (holds_imp v _ _).mp (hS v _ hax) hU

/-- The package's own halving structure is not `TrivialAx` (the world affirming `U` and denying
`a_0` breaks `U 🡒 a_0`). -/
theorem halvingS_not_trivialAx : ¬ halvingS.TrivialAx := by
  intro h
  have hv := (mk_axHolds_iff _ _ (fun a => a ≠ instAtom 0)).mp (h _)
  have := hv.1 0 (univAtom_ne_instAtom 0 0)
  simp [PCWorld.holds_atom] at this

/-- `refBase = chainPMF halfRule 2` is the Bernoulli product with parameter `½`. -/
theorem refBase_isProduct : IsProductBase refBase :=
  ⟨fun _ => 1 / 2, fun w => by unfold refBase; exact chainPMF_productRule _ 2 w⟩

/-- The (⇐) direction of the iff on a `B = 2` product base. -/
theorem refBase_sotoIsProductAe (e : ℕ ≃ ℕ) : SotoIsProductAe trivS e refBase :=
  (sotoRule_eq_productRule_iff trivS e trivS_trivialAx (chainPMF_nonneg halfRule_inUnit 2)
    (chainPMF_sum_one halfRule 2)).mpr refBase_isProduct

/-- The two-cell base at `B = 2`: `q(T,T) = 0`, `q(T,F) = ⅓`, `q(F,T) = ⅔`, `q(F,F) = 0`. -/
def twoBase : FiniteWorld 2 → ℚ := chainPMF twoCellRule 2

/-- On `twoBase`, Soto's rule at level `1` reads `0` on `[T]` and `1` on `[F]`, both prefixes of
positive chained mass (`⅓`, `⅔`). -/
theorem twoBase_rule_values (e : ℕ ≃ ℕ) :
    sotoRule trivS e twoBase 1 (fun _ => true) = 0 ∧
    sotoRule trivS e twoBase 1 (fun _ => false) = 1 ∧
    sotoPMF trivS e twoBase 1 (fun _ => true) ≠ 0 ∧
    sotoPMF trivS e twoBase 1 (fun _ => false) ≠ 0 := by
  have hq0 : ∀ w, 0 ≤ twoBase w := chainPMF_nonneg twoCellRule_inUnit 2
  have hq1 : ∑ w, twoBase w = 1 := chainPMF_sum_one twoCellRule 2
  have hMT : baseMarginal twoBase 1 (fun _ => true) = 1 / 3 := by
    rw [twoBase, baseMarginal_chainPMF _ 2 1 (by norm_num)]
    simp [chainPMF, twoCellRule]
  have hMF : baseMarginal twoBase 1 (fun _ => false) = 2 / 3 := by
    rw [twoBase, baseMarginal_chainPMF _ 2 1 (by norm_num)]
    simp [chainPMF, twoCellRule]; norm_num
  have hTT : baseMarginal twoBase 2 (Fin.snoc (fun _ => true) true) = 0 := by
    rw [twoBase, baseMarginal_self, chainPMF_snoc]
    simp [chainPMF, twoCellRule]
  have hFT : baseMarginal twoBase 2 (Fin.snoc (fun _ => false) true) = 2 / 3 := by
    rw [twoBase, baseMarginal_self, chainPMF_snoc]
    simp [chainPMF, twoCellRule]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [sotoRule, hMT, hTT]
  · simp [sotoRule, hMF, hFT]
  · rw [sotoPMF_eq_baseMarginal trivS e hq0 hq1 1 (by norm_num), hMT]; norm_num
  · rw [sotoPMF_eq_baseMarginal trivS e hq0 hq1 1 (by norm_num), hMF]; norm_num

/-- Soto's rule on `twoBase` is not product on the positive-mass prefixes. -/
theorem twoBase_not_sotoIsProductAe (e : ℕ ≃ ℕ) : ¬ SotoIsProductAe trivS e twoBase := by
  rintro ⟨c, hc⟩
  obtain ⟨h0, h1, hT, hF⟩ := twoBase_rule_values e
  have hcT := hc 1 (fun _ => true) hT
  have hcF := hc 1 (fun _ => false) hF
  rw [h0] at hcT
  rw [h1, ← hcT] at hcF
  norm_num at hcF

/-- Through the headline's (⇐) direction: `twoBase` is not a Bernoulli product. -/
theorem twoBase_not_isProduct : ¬ IsProductBase twoBase :=
  fun h => twoBase_not_sotoIsProductAe (Equiv.refl ℕ)
    ((sotoRule_eq_productRule_iff trivS (Equiv.refl ℕ) trivS_trivialAx
      (chainPMF_nonneg twoCellRule_inUnit 2) (chainPMF_sum_one twoCellRule 2)).mpr h)

end Cleanroom.Bli.BliExtrapolation.AuditR3Adv
