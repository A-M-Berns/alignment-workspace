import Cleanroom.Uea.UeaSinkSwim.BestOnPathPolicy
import Cleanroom.Uea.UeaSinkSwim.ResidualArgmax
import Cleanroom.Uea.UeaSinkSwim.TheoremA

/-!
# Audit r2 (adversarial) probe for `uea-sink-swim`: D1 separated from D0 on sink-or-swim

The package's D1 witness (`BestOnPath.piB_on_chain`) lives on the trap chain, where `π^B = π^R` (both are `stay`:
`TrapChain.piB_stay`, `TrapChain.piR_stay`). So no theorem in the package exhibits a model on which D1's policy
differs from D0's, or on which D0's policy violates D1's bound. The mandate's unformalized remark (F-19's remaining
half) is exactly that model: on `sos P` in the good-point regime `c ≤ b(1-δs)`, `π^B` jumps at the island (it is the
good point, `gap = 0`), while `π^R` stays (the trap) whenever `b(1-s) < c`. At the witness parameters
`b = 1, c = 1/2, δ = 1/4, s = 3/4`: `gap(π^B) = 0`, `gap(π^R) = 1/2 > 1/4 = ε₀`. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSinkSwim.AuditR2Adversarial

open Classical
open Finset
open Cleanroom.Uea.UeaColeShadow
open Cleanroom.Uea.UeaColeShadow.SinkOrSwim
open ResidualArgmax (Alt altChoice piR)
open BestOnPath

variable (P : Params)

/-- On `Fin 2`, `rival(h, a)` is the other action's `Alt`. -/
theorem rival_le_other {n : ℕ} (h : Hist (Fin 2) Unit n) (a b : Fin 2) (hab : b ≠ a) :
    rival (sos P) n h a ≤ Alt (sos P) n h b := by
  unfold rival
  split_ifs with hne
  · rw [Finset.sup'_le_iff]
    intro x hx
    -- `rival` is defined over a generic `A`, so its `erase` carries `Classical.propDecidable`
    have hx' : x ≠ a :=
      ((@Finset.mem_erase (Fin 2) (fun a b => Classical.propDecidable (a = b)) x a univ).1 hx).1
    have hxb : x = b := by
      revert hx' hab
      fin_cases x <;> fin_cases a <;> fin_cases b <;> decide
    rw [hxb]
  · exact Alt_nonneg (sos P) n h b

theorem rival_eq_other {n : ℕ} (h : Hist (Fin 2) Unit n) (a b : Fin 2) (hab : b ≠ a) :
    rival (sos P) n h a = Alt (sos P) n h b :=
  le_antisymm (rival_le_other P h a b hab) (Alt_le_rival (sos P) hab)

/-! ### The water node: `B(water) = b` -/

theorem children_terminal_water (a : Fin 2) : ∀ e, ¬ (sos P).nonterminal 2 (ext water a e) :=
  fun _ => not_nt_two P _

theorem S_water (a : Fin 2) : S (sos P) 1 water a = (sos P).Qstar 1 water a :=
  S_eq_Qstar_of_children_terminal (sos P) (children_terminal_water P a)

theorem val_water (a : Fin 2) : val (sos P) 1 water a = (sos P).Qstar 1 water a := by
  by_cases hA : (sos P).xinsA 1 water a = 0
  · rw [val_of_xinsA_eq_zero _ hA]
  · rw [val_of_xinsA_ne_zero _ hA, cont_eq_Qstar_of_children_terminal _ (children_terminal_water P a)]

theorem Alt_water_1 : Alt (sos P) 1 water 1 = 0 :=
  le_antisymm (le_trans (Alt_le_Qstar _ _ _ _) (TheoremA.Qstar_water_1 P).le) (Alt_nonneg _ _ _ _)

theorem feasible_water_0 : feasible (sos P) 1 water 0 := by
  rw [feasible_iff, S_water, TheoremA.Qstar_water_0, rival_eq_other P water 0 1 (by decide), Alt_water_1]
  exact (TheoremA.b_pos P).le

theorem B_water : B (sos P) 1 water = P.b := by
  have hmem : (0 : Fin 2) ∈ univ.filter (feasible (sos P) 1 water) := mem_filter.2 ⟨mem_univ _, feasible_water_0 P⟩
  have hne : (univ.filter (feasible (sos P) 1 water)).Nonempty := ⟨0, hmem⟩
  rw [B_eq_sup' _ (nt_water P) hne]
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro a _
    rw [val_water]
    exact le_trans ((sos P).Qstar_le_Vstar (nt_water P) a) (Vstar_water P).le
  · refine le_trans ?_ (le_sup' _ hmem)
    rw [val_water, TheoremA.Qstar_water_0]

/-! ### The island: `S`, `val`, `feasible` for both actions -/

theorem xinsA_island_1_ne : (sos P).xinsA 0 island 1 ≠ 0 := by
  rw [ResidualArgmax.sos_xinsA_island_1]; exact P.hδ.ne'

theorem cont_island_1 : cont (sos P) 0 island 1 = P.b := by
  rw [cont_eq, Fintype.sum_unique, xie_eq_one]
  show 1 * ((sos P).γ ^ 0 * (sos P).r 0 water + B (sos P) 1 water) = P.b
  rw [B_water]
  simp [r, water]

theorem wtA_island_1 : wtA (sos P) 0 island 1 = 1 - P.δ := by
  unfold wtA
  rw [Pe_zero, ResidualArgmax.sos_xinsA_island_1]
  have h1 : (1 - (sos P).δ) * 1 + P.δ = 1 := by show (1 - P.δ) * 1 + P.δ = 1; ring
  rw [if_neg (by rw [h1]; exact one_ne_zero), h1, div_one, mul_one]
  try rfl

theorem Qmix_island_1 : (sos P).Qmix 0 island 1 = P.b * (1 - P.s) := by
  have := (ResidualArgmax.sos_Alt_island P).2
  unfold Alt at this
  rwa [if_neg (xinsA_island_1_ne P)] at this

/-- `S(island, jump) = b(1-δs)` — the good point's `Q_ξ(jump)`. -/
theorem S_island_1 : S (sos P) 0 island 1 = P.b * (1 - P.δ * P.s) := by
  rw [S_of_xinsA_ne_zero _ (xinsA_island_1_ne P), wtA_island_1, cont_island_1, Qmix_island_1]
  ring

theorem S_island_0 : S (sos P) 0 island 0 = P.c := by
  rw [S_of_xinsA_eq_zero _ (ResidualArgmax.sos_xinsA_island_0 P), Qstar_island_0]

theorem val_island_0 : val (sos P) 0 island 0 = P.c := by
  rw [val_of_xinsA_eq_zero _ (ResidualArgmax.sos_xinsA_island_0 P), Qstar_island_0]

theorem val_island_1 : val (sos P) 0 island 1 = P.b := by
  rw [val_of_xinsA_ne_zero _ (xinsA_island_1_ne P), cont_island_1]

/-- `jump` is feasible at the island iff the good point's condition `c ≤ b(1-δs)` holds. -/
theorem feasible_island_1_iff : feasible (sos P) 0 island 1 ↔ P.c ≤ P.b * (1 - P.δ * P.s) := by
  rw [feasible_iff, S_island_1, rival_eq_other P island 1 0 (by decide), (ResidualArgmax.sos_Alt_island P).1]

/-- `stay` is feasible at the island iff the trap's condition `b(1-s) ≤ c` holds. -/
theorem feasible_island_0_iff : feasible (sos P) 0 island 0 ↔ P.b * (1 - P.s) ≤ P.c := by
  rw [feasible_iff, S_island_0, rival_eq_other P island 0 1 (by decide), (ResidualArgmax.sos_Alt_island P).2]

/-! ### `π^B` on sink-or-swim -/

theorem B_island (hgood : P.c ≤ P.b * (1 - P.δ * P.s)) : B (sos P) 0 island = P.b := by
  have hmem : (1 : Fin 2) ∈ univ.filter (feasible (sos P) 0 island) :=
    mem_filter.2 ⟨mem_univ _, (feasible_island_1_iff P).2 hgood⟩
  have hne : (univ.filter (feasible (sos P) 0 island)).Nonempty := ⟨1, hmem⟩
  rw [B_eq_sup' _ (nt_island P) hne]
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro a _
    revert a
    refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [val_island_0]; exact P.hcb.le
    · rw [val_island_1]
  · refine le_trans ?_ (le_sup' _ hmem)
    rw [val_island_1]

theorem choice_island (hgood : P.c ≤ P.b * (1 - P.δ * P.s)) : choice (sos P) 0 island = 1 := by
  have hB := B_eq_val_choice (sos P) (nt_island P)
  rw [B_island P hgood] at hB
  by_contra hne
  have h0 : choice (sos P) 0 island = 0 := by
    generalize choice (sos P) 0 island = x at hne ⊢
    fin_cases x <;> simp_all
  rw [h0, val_island_0] at hB
  exact P.hcb.ne' hB

/-- **`π^B` is the good point on sink-or-swim in the good-point regime**: it jumps surely at the island whenever
`c ≤ b(1-δs)` — the mandate's "`π^B = good` in the coexistence regime" (F-19's remaining half). -/
theorem piB_sos_is_good (hgood : P.c ≤ P.b * (1 - P.δ * P.s)) : piB (sos P) 0 island 1 = 1 := by
  rw [← choice_island P hgood]
  exact piB_onPath_choice (sos P) (onPath_zero (sos P) island)

/-- **D1 separated from D0 (N+)**: at `b = 1, c = 1/2, δ = 1/4, s = 3/4`, `π^B` jumps (the good point) and `π^R` stays
(the trap); `π^B` has root loss `0`, `π^R` has root loss `1/2`, and D1's root bound `ε₀ = 1 - (1-δ)^(T-1)` is `1/4`:
D0's fixed point violates D1's bound, D1's fixed point meets it with room to spare. -/
theorem separation :
    piB (sos TheoremA.witParams) 0 island 1 = 1 ∧ piR (sos TheoremA.witParams) 0 island 0 = 1 ∧
    (sos TheoremA.witParams).gap (piB (sos TheoremA.witParams)) 0 island = 0 ∧
    (sos TheoremA.witParams).gap (piR (sos TheoremA.witParams)) 0 island = 1 / 2 ∧
    eps (sos TheoremA.witParams) 0 = 1 / 4 := by
  have hgood : TheoremA.witParams.c ≤ TheoremA.witParams.b * (1 - TheoremA.witParams.δ * TheoremA.witParams.s) := by
    unfold TheoremA.witParams; norm_num
  have htrap : TheoremA.witParams.b * (1 - TheoremA.witParams.s) < TheoremA.witParams.c := by
    unfold TheoremA.witParams; norm_num
  have hR := ResidualArgmax.piR_sos_is_trap TheoremA.witParams htrap
  refine ⟨piB_sos_is_good _ hgood, hR, ?_, ?_, ?_⟩
  · unfold Model.gap
    rw [Vpi_piB_onPath _ 0 island (onPath_zero _ _), B_island _ hgood, Vstar_island, sub_self]
  · have hπ := ResidualArgmax.piR_isPolicy (sos TheoremA.witParams)
    have h1 : piR (sos TheoremA.witParams) 0 island 1 = 0 := by
      have := hπ.fin_two_zero (nt_island TheoremA.witParams); rw [hR] at this; linarith
    unfold Model.gap
    rw [Vpi_island _ _ hπ, h1, Vstar_island]
    show (1:ℝ) - ((1 - 0) * (1 / 2) + 0 * (piR (sos TheoremA.witParams) 1 water 0 * 1)) = 1 / 2
    ring
  · show (1:ℝ) - (1 - 1 / 4) ^ (2 - 1 - 0) = 1 / 4
    norm_num

end Cleanroom.Uea.UeaSinkSwim.AuditR2Adversarial
