import Cleanroom.Corrigibility.CorrExoTrader.GenLic

/-!
# Audit r3 (fidelity) probe — the N+ for T2.4 gives the net-worth difference its docstring claims

Not imported by the library. `joinBuyers_agree_on_traded`'s docstring says: "T2.4 gives a
net-worth difference of `∑_{i ≤ n} c`, not `0`". The theorem itself proves only the hypothesis and
the payout difference; this probe closes the loop and computes the difference, `(n + 1) · c`, so
the N+ grade (hypothesis exercised, conclusion non-zero for `c ≠ 0`) is machine-checked end to end.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional

theorem joinBuyers_netWorth_diff (a b : ℕ) (hab : a ≠ b) (c c' : ℚ) (P : History) (n : ℕ) :
    (Trader.join (constBuyer (Formula.atom a) c) (constBuyer (Formula.atom b) c')).netWorth P
        worldAll n -
      (Trader.join (constBuyer (Formula.atom a) c) (constBuyer (Formula.atom b) c')).netWorth P
        (worldExcept a) n = ((n : ℝ) + 1) * (c : ℝ) := by
  obtain ⟨hagree, hdiff⟩ := joinBuyers_agree_on_traded a b hab c c' n
  rw [netWorth_sub_netWorth_of_agree_on_traded _ P _ _ (Formula.atom a) n hagree, hdiff]
  have hba : Formula.atom b ≠ Formula.atom a := fun h => hab (Formula.atom.inj h).symm
  simp [Trader.join, Strategy.join, constBuyer, hba, Finset.sum_const, Finset.card_range]

end Cleanroom.Corrigibility.CorrExoTrader
