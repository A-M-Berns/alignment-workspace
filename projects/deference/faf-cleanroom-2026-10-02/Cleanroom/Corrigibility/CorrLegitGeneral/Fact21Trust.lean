import Cleanroom.Corrigibility.CorrLegitGeneral.TrustAttained
import Cleanroom.Corrigibility.CorrLegitGeneral.Eval

/-!
# corr-legit-general — T11 (stretch): the Trust half of Fact 2.1, machine-checked

DDB's Fact 2.1 asserts (by a Mathematica check the paper does not print) that `π21 = (0.17, 0.56,
0.27)` *trusts* the frame `fact21` in DDB's sense — `π(q | p ∧ [P(q | p) ≥ t]) ≥ t` for all
`q, p, t` — while not valuing it. `trust_iff_attained` (`TrustAttained.lean`) reduces Trust on a
finite frame to the guarded product inequality at the attained conditional values
`P_v(q ∩ p)/P_v(p)` only. Here that finite check is carried out: the masses are expanded as sums
of `if`s over the three worlds, the membership of each world in `q` and in `p` is split
(`by_cases`, 64 cases), the attaining world `v` is split (`fin_cases`, 3), and `norm_num` closes
every leaf — no `decide` beyond `Fin 3` membership. `fact21_trust_open` (`Fact21.lean`) is
thereby proved (`fact21_trust`); the OPEN entry is retired.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Mass of `p ∧ [P(q | p) ≥ t]` as a full sum of `if`s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_condProbEvent_eq (π : W → ℝ) (F : Frame W) (q p : Finset W) (t : ℝ) :
    mass π (p ∩ F.condProbEvent q p t) =
      ∑ w, if ((0 < mass (F.P w) p ∧ t * mass (F.P w) p ≤ mass (F.P w) (q ∩ p)) ∧ w ∈ p)
        then π w else 0 := by
  show (∑ w ∈ p ∩ F.condProbEvent q p t, π w) = _
  unfold Frame.condProbEvent
  rw [inter_comm, ← filter_mem_eq_inter, filter_filter, sum_filter]

/-- Mass of `q ∧ p ∧ [P(q | p) ≥ t]` as a full sum of `if`s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_inter_condProbEvent_eq (π : W → ℝ) (F : Frame W) (q p : Finset W) (t : ℝ) :
    mass π (q ∩ (p ∩ F.condProbEvent q p t)) =
      ∑ w, if ((0 < mass (F.P w) p ∧ t * mass (F.P w) p ≤ mass (F.P w) (q ∩ p)) ∧ w ∈ q ∩ p)
        then π w else 0 := by
  show (∑ w ∈ q ∩ (p ∩ F.condProbEvent q p t), π w) = _
  unfold Frame.condProbEvent
  rw [← inter_assoc, inter_comm, ← filter_mem_eq_inter, filter_filter, sum_filter]

set_option maxHeartbeats 4000000 in
/-- **The Trust half of Fact 2.1**: `π21` trusts `fact21` in DDB's sense (every `q`, `p`, `t`).
Proof: `trust_iff_attained`, then the finite table — 64 membership patterns for `(q, p)` on three
worlds, three attaining worlds each, every leaf closed by `norm_num`. This verifies DDB's
unprinted Mathematica check; with `fact21_not_value` (cited) it completes Fact 2.1 (Trust ⇏
Value) in Lean.
Source: [[Deference Done Better]] §2 Fact 2.1 l. 165 ("π trusts the frame"); mandate T11
(stretch); Known issues 6
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fact21_trust : Trust π21 fact21 := by
  rw [trust_iff_attained (fun w => by fin_cases w <;> norm_num [π21, vec3_two])]
  intro q p v _ hpos
  obtain ⟨h0, h1, h2⟩ := fact21_P
  rw [mass_inter_condProbEvent_eq] at hpos ⊢
  rw [mass_inter_inter_condProbEvent_eq]
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;> by_cases h0p : (0 : Fin 3) ∈ p <;>
    by_cases h1p : (1 : Fin 3) ∈ p <;> by_cases h2p : (2 : Fin 3) ∈ p <;>
    simp only [mass_eq_sum_ite, Fin.sum_univ_three, mem_inter, h0q, h1q, h2q, h0p, h1p, h2p,
      if_true, if_false, and_true, and_false, add_zero] at hpos ⊢ <;>
    fin_cases v <;> first
      | (norm_num [h0, h1, h2, π21, vec3_two] at hpos ⊢)
      | (norm_num at hpos)

/-- **Fact 2.1 complete**: `π21` trusts `fact21` and does not value it.
Source: [[Deference Done Better]] §2 Fact 2.1 l. 165; mandate T11
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem fact21_trust_not_value : Trust π21 fact21 ∧ ¬ Value π21 fact21 :=
  ⟨fact21_trust, fact21_not_value⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
