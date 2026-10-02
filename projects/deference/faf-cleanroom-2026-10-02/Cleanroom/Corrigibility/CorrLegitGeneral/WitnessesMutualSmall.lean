import Cleanroom.Corrigibility.CorrLegitGeneral.Mutual
import Cleanroom.Corrigibility.CorrLegitGeneral.Eval

/-!
# corr-legit-general — T8's witnesses on three worlds (gated)

`WitnessesMutual.lean` (four worlds, importing `Cleanroom.Lit.LitDdbFacts.Examples`) elaborates
but could not be built under the run's memory budget (report, T8). The round-3 audits asked for a
cheap pair that shows the theorems' bite inside the gate (adversarial N3, fidelity N5); this is
it, on `Fin 3` with `mk3`:

- `mA`: cells `{0, 1}`, `{2}` (rows `(1/2, 1/2, 0)`, `(1/2, 1/2, 0)`, `δ₂`) — the agent's clear
  frame;
- `mH`: the single cell `{0, 1, 2}` (row `(1/3, 1/3, 1/3)` everywhere) — a humans' clear frame
  that disagrees with `mA` at the actual world `0`;
- `mH'`: the single cell `{0, 1, 2}` with row `(1/2, 1/2, 0)` everywhere — a humans' clear
  frame that agrees with `mA` at `0` and differs from it at `2`.

Forward theorem (`mutual_totalTrust_eq`): `mA`, `mH` are immodest, non-dogmatic both ways at `0`
(`P^A_0([0]_H) = 1`, `P^H_0([0]_A) = 2/3`), `mA.P 0 ≠ mH.P 0`, and accordingly one trust relation
fails — `mA.P 0` does not totally trust `mH` at the bet `X = 𝟙_{2}`, `s = 1/3` (sum `−1/3`). So the
conclusion fails with exactly one hypothesis missing: the hypotheses bite. Converse
(`mutual_totalTrust_of_eq`): `mA`, `mH'` are distinct clear frames agreeing at `0`, and each
state totally trusts the other's frame.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSimpArgs false

/-- The agent's clear frame on three worlds: cells `{0, 1}`, `{2}`.
Source: mandate T8 (witness; no example in the source); audit r3 adversarial N3
Kind: D
Fidelity: n/a -/
def mA : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 2, 0] ![1 / 2, 1 / 2, 0] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The humans' clear frame disagreeing at `0`: the single cell `{0, 1, 2}`, uniform row.
Source: mandate T8 (witness); audit r3 adversarial N3
Kind: D
Fidelity: n/a -/
def mH : Frame (Fin 3) :=
  mk3 ![1 / 3, 1 / 3, 1 / 3] ![1 / 3, 1 / 3, 1 / 3] ![1 / 3, 1 / 3, 1 / 3]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- A humans' clear frame agreeing with `mA` at `0` but coarser: the single cell `{0, 1, 2}`
with row `(1/2, 1/2, 0)` everywhere. Distinct from `mA` at world `2`.
Source: mandate T8 (witness); audit r3 adversarial N3
Kind: D
Fidelity: n/a -/
def mH' : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 2, 0] ![1 / 2, 1 / 2, 0] ![1 / 2, 1 / 2, 0]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The rows of the three frames.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem m_P : (mA.P 0 = ![1 / 2, 1 / 2, 0] ∧ mA.P 1 = ![1 / 2, 1 / 2, 0] ∧ mA.P 2 = ![0, 0, 1]) ∧
    (mH.P 0 = ![1 / 3, 1 / 3, 1 / 3] ∧ mH.P 1 = ![1 / 3, 1 / 3, 1 / 3] ∧
      mH.P 2 = ![1 / 3, 1 / 3, 1 / 3]) ∧
    (mH'.P 0 = ![1 / 2, 1 / 2, 0] ∧ mH'.P 1 = ![1 / 2, 1 / 2, 0] ∧ mH'.P 2 = ![1 / 2, 1 / 2, 0]) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- The cells: `mA` has `{0, 1}` and `{2}`; `mH` and `mH'` have the single cell `univ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem m_cell : (mA.cell (mA.P 0) = {0, 1} ∧ mA.cell (mA.P 2) = {2}) ∧
    mH.cell (mH.P 0) = univ ∧ mH'.cell (mH'.P 0) = univ := by
  obtain ⟨⟨a0, a1, a2⟩, ⟨h0, h1, h2⟩, ⟨g0, g1, g2⟩⟩ := m_P
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ext w <;> fin_cases w <;>
    simp [Frame.cell, a0, a1, a2, h0, h1, h2, g0, g1, g2]

/-- `mA` is immodest (clear).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mA_immodest : mA.Immodest := by
  obtain ⟨⟨a0, a1, a2⟩, _, _⟩ := m_P
  obtain ⟨⟨c0, c2⟩, _, _⟩ := m_cell
  have e1 : mA.P 1 = mA.P 0 := rfl
  intro w
  fin_cases w
  · show mA.selfMass (mA.P 0) = 1
    unfold Frame.selfMass; rw [c0, a0]
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · show mA.selfMass (mA.P 1) = 1
    unfold Frame.selfMass; rw [e1, c0, a0]
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · show mA.selfMass (mA.P 2) = 1
    unfold Frame.selfMass; rw [c2, a2]
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two]

/-- `mH` is immodest (clear).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mH_immodest : mH.Immodest := by
  obtain ⟨_, ⟨h0, _, _⟩, _⟩ := m_P
  obtain ⟨_, c, _⟩ := m_cell
  have e1 : mH.P 1 = mH.P 0 := rfl
  have e2 : mH.P 2 = mH.P 0 := rfl
  intro w
  fin_cases w
  · show mH.selfMass (mH.P 0) = 1
    unfold Frame.selfMass; rw [c, h0]
    simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · show mH.selfMass (mH.P 1) = 1
    unfold Frame.selfMass; rw [e1, c, h0]
    simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · show mH.selfMass (mH.P 2) = 1
    unfold Frame.selfMass; rw [e2, c, h0]
    simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num

/-- `mH'` is immodest (clear).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mH'_immodest : mH'.Immodest := by
  obtain ⟨_, _, ⟨g0, _, _⟩⟩ := m_P
  obtain ⟨_, _, c⟩ := m_cell
  have e1 : mH'.P 1 = mH'.P 0 := rfl
  have e2 : mH'.P 2 = mH'.P 0 := rfl
  intro w
  fin_cases w
  · show mH'.selfMass (mH'.P 0) = 1
    unfold Frame.selfMass; rw [c, g0]
    simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · show mH'.selfMass (mH'.P 1) = 1
    unfold Frame.selfMass; rw [e1, c, g0]
    simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · show mH'.selfMass (mH'.P 2) = 1
    unfold Frame.selfMass; rw [e2, c, g0]
    simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num

/-- `mA.P 0` does not totally trust `mH`: at `X = 𝟙_{2}`, `s = 1/3`, every `mH`-row expects
`1/3`, so the indicator is `1` everywhere and the sum is `1/2 · (−1/3) + 1/2 · (−1/3) = −1/3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mA_not_totalTrust_mH : ¬ TotalTrust (mA.P 0) mH := by
  intro h
  obtain ⟨⟨a0, _, _⟩, ⟨h0, h1, h2⟩, _⟩ := m_P
  have := h (ind {2}) (1 / 3)
  simp +decide [Fin.sum_univ_three, E, ind, a0, h0, h1, h2, vec3_two] at this
  norm_num at this

/-- **T8 forward, the hypotheses bite**: `mA`, `mH` are clear, non-dogmatic both ways at `0`
(`P^A_0([0]_H) = 1 > 0`, `P^H_0([0]_A) = 2/3 > 0`), their states at `0` differ, and accordingly
`mA.P 0` does not totally trust `mH` — `mutual_totalTrust_eq`'s conclusion fails with exactly one
of its relations missing.
Source: [[mm]] I9.3 l. 188; mandate T8; audit r3 adversarial N3
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem mA_mH_witness :
    mA.Immodest ∧ mH.Immodest ∧ 0 < mass (mA.P 0) (mH.cell (mH.P 0)) ∧
      0 < mass (mH.P 0) (mA.cell (mA.P 0)) ∧ mA.P 0 ≠ mH.P 0 ∧ ¬ TotalTrust (mA.P 0) mH := by
  obtain ⟨⟨a0, _, _⟩, ⟨h0, _, _⟩, _⟩ := m_P
  obtain ⟨⟨cA0, _⟩, cH, _⟩ := m_cell
  refine ⟨mA_immodest, mH_immodest, ?_, ?_, fun h => ?_, mA_not_totalTrust_mH⟩
  · rw [cH, a0]; simp [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · rw [cA0, h0]; simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  · have := congrFun h 0
    rw [a0, h0] at this
    norm_num at this

/-- **T8 converse, instantiated**: `mA` and `mH'` are distinct clear frames (at world `2`)
agreeing at `0`, and each state totally trusts the other's frame (`mutual_totalTrust_of_eq`).
Source: [[mm]] I9.3 l. 188 (converse); mandate T8; audit r3 adversarial N3
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem mA_mH'_witness : mA.P 2 ≠ mH'.P 2 ∧ mA.P 0 = mH'.P 0 ∧
    TotalTrust (mA.P 0) mH' ∧ TotalTrust (mH'.P 0) mA := by
  have heq : mA.P 0 = mH'.P 0 := rfl
  obtain ⟨⟨_, _, a2⟩, _, ⟨_, _, g2⟩⟩ := m_P
  refine ⟨fun h => ?_, heq, (mutual_totalTrust_of_eq mA_immodest mH'_immodest 0 heq).1,
    (mutual_totalTrust_of_eq mA_immodest mH'_immodest 0 heq).2⟩
  have := congrFun h 0
  rw [a2, g2] at this
  norm_num at this

end

end Cleanroom.Corrigibility.CorrLegitGeneral
