import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesMutualSmall

/-!
# audit r4 (fidelity) probe — the relation `mA_mH_witness` leaves unstated

`WitnessesMutualSmall.lean`'s docstring and the ledger row for `mutual_totalTrust_eq` say the
conclusion "fails with exactly one of its relations missing". The packaged witness proves
`¬ TotalTrust (mA.P 0) mH` but does not state the other relation, `TotalTrust (mH.P 0) mA`,
which "exactly one" asserts. It is true (Theorem 4.1: `(1/3, 1/3, 1/3) = 2/3·(1/2, 1/2, 0) +
1/3·δ₂`, both candidates immodest); here it is proved directly in product form so the sentence
is machine-checked. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

/-- The uniform state (`mH.P 0`) totally trusts `mA`: the threshold sum at any `(X, s)` splits
on the two expert expectations `(X 0 + X 1)/2` and `X 2`, every case linear.
Source: audit r4 fidelity N1 (the relation `mA_mH_witness` omits)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem mH_totalTrust_mA : TotalTrust (mH.P 0) mA := by
  intro X s
  obtain ⟨⟨a0, a1, a2⟩, ⟨h0, _, _⟩, _⟩ := m_P
  simp [Fin.sum_univ_three, E, a0, a1, a2, h0, vec3_two]
  split_ifs <;> linarith

/-- The T8 bite claim as a single statement: both frames clear, non-dogmatic both ways at `0`,
states differ, one relation holds and the other fails.
Source: audit r4 fidelity N1
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem mA_mH_exactly_one_missing :
    mA.Immodest ∧ mH.Immodest ∧ 0 < mass (mA.P 0) (mH.cell (mH.P 0)) ∧
      0 < mass (mH.P 0) (mA.cell (mA.P 0)) ∧ mA.P 0 ≠ mH.P 0 ∧
      TotalTrust (mH.P 0) mA ∧ ¬ TotalTrust (mA.P 0) mH :=
  ⟨mA_mH_witness.1, mA_mH_witness.2.1, mA_mH_witness.2.2.1, mA_mH_witness.2.2.2.1,
    mA_mH_witness.2.2.2.2.1, mH_totalTrust_mA, mA_mH_witness.2.2.2.2.2⟩

#print axioms mH_totalTrust_mA
#print axioms mA_mH_exactly_one_missing

end

end Cleanroom.Corrigibility.CorrLegitGeneral
