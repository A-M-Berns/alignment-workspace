import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Found.LitDdbFrames.Basic

/-!
# corr-legit-general — T11 (stretch): Trust reduces to the attained conditional values

DDB's `Trust` quantifies over every real threshold `t`: `π(q | p ∧ [P(q | p) ≥ t]) ≥ t` for all
`q, p, t` (guarded by positivity). On a finite frame the conditioning event
`[P(q | p) ≥ t]` changes only when `t` crosses one of the finitely many *attained* conditional
values `P_v(q ∩ p) / P_v(p)`, and for a fixed event the inequality is tightest at the largest `t`
that produces it — which is the smallest attained value inside the event. So Trust is equivalent
to the guarded inequality at the attained thresholds only (`trust_iff_attained`): a finite check
for a finite frame. This is the reduction the mandate asked for before the `norm_num` table on
Fact 2.1's frame; the table is carried out in `Fact21Trust.lean` (`fact21_trust`, repair round 2),
which retired the OPEN `fact21_trust_open`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Membership in the conditional-probability event, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_condProbEvent (F : Frame W) (q p : Finset W) (t : ℝ) (w : W) :
    w ∈ F.condProbEvent q p t ↔
      0 < mass (F.P w) p ∧ t * mass (F.P w) p ≤ mass (F.P w) (q ∩ p) := by
  simp only [Frame.condProbEvent, mem_filter, mem_univ, true_and]

/-- **Trust is the guarded inequality at the attained conditional values**: `π` trusts `F` iff for
every `q, p` and every world `v` with `P_v(p) > 0`, the inequality holds at `t = P_v(q ∩ p) / P_v(p)`
(the only place a division appears; it is `P_v(q | p)` under the guard). (⇒) is an instance;
(⇐): for any `t` whose event `E_t = [P(q | p) ≥ t]` has positive `π`-mass on `p`, pick `v ∈ E_t`
with the smallest conditional value `t' := P_v(q | p)`; then `t ≤ t'` and `E_{t'} = E_t` (every
`w ∈ E_t` has `P_w(q | p) ≥ t'` by minimality, and conversely `t' ≥ t`), so the inequality at
`t'` gives the one at `t` since `t · π(p ∩ E) ≤ t' · π(p ∩ E)`.
Source: [[Deference Done Better]] §2 l. 154 (Trust); mandate T11 ("prove the reduction 'Trust ⟺
the guarded inequality at the attained conditional values'")
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem trust_iff_attained {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (F : Frame W) :
    Trust π F ↔ ∀ q p : Finset W, ∀ v, 0 < mass (F.P v) p →
      0 < mass π (p ∩ F.condProbEvent q p (mass (F.P v) (q ∩ p) / mass (F.P v) p)) →
      (mass (F.P v) (q ∩ p) / mass (F.P v) p) *
          mass π (p ∩ F.condProbEvent q p (mass (F.P v) (q ∩ p) / mass (F.P v) p)) ≤
        mass π (q ∩ (p ∩ F.condProbEvent q p (mass (F.P v) (q ∩ p) / mass (F.P v) p))) := by
  constructor
  · intro h q p v _ hpos
    exact h q p _ hpos
  · intro h q p t hpos
    have hne : (F.condProbEvent q p t).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, inter_empty] at hpos
      simp [mass] at hpos
    obtain ⟨v, hvE, hvmin⟩ :=
      Finset.exists_min_image (F.condProbEvent q p t)
        (fun w => mass (F.P w) (q ∩ p) / mass (F.P w) p) hne
    rw [mem_condProbEvent] at hvE
    obtain ⟨hv1, hv2⟩ := hvE
    have htt' : t ≤ mass (F.P v) (q ∩ p) / mass (F.P v) p := by
      rw [le_div_iff₀ hv1]; exact hv2
    have hEE : F.condProbEvent q p (mass (F.P v) (q ∩ p) / mass (F.P v) p) =
        F.condProbEvent q p t := by
      ext w
      rw [mem_condProbEvent, mem_condProbEvent]
      constructor
      · rintro ⟨hw1, hw2⟩
        refine ⟨hw1, ?_⟩
        calc t * mass (F.P w) p ≤ (mass (F.P v) (q ∩ p) / mass (F.P v) p) * mass (F.P w) p :=
              mul_le_mul_of_nonneg_right htt' (mass_nonneg (F.P_mem w).1 p)
          _ ≤ _ := hw2
      · rintro ⟨hw1, hw2⟩
        refine ⟨hw1, ?_⟩
        have hmin := hvmin w ((mem_condProbEvent F q p t w).2 ⟨hw1, hw2⟩)
        rwa [le_div_iff₀ hw1] at hmin
    have key := h q p v hv1 (by rw [hEE]; exact hpos)
    rw [hEE] at key
    calc t * mass π (p ∩ F.condProbEvent q p t)
        ≤ (mass (F.P v) (q ∩ p) / mass (F.P v) p) * mass π (p ∩ F.condProbEvent q p t) :=
          mul_le_mul_of_nonneg_right htt' (mass_nonneg hπ _)
      _ ≤ _ := key

end

end Cleanroom.Corrigibility.CorrLegitGeneral
