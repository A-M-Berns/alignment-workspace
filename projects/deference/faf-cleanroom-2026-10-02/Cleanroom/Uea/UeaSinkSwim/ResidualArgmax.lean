import Cleanroom.Uea.UeaColeShadow.Facts
import Cleanroom.Uea.UeaColeShadow.SinkOrSwim

/-!
# D0: the residual-argmax policy is a pure plain fixed point of every model

`Alt(h, a) := Q^*(h, a)` if the residual puts no mass on `(h, a)`, else `Q̄(h, a)` (the residual
continuation of Lemma A); `π^R` plays one fixed maximiser of `Alt(h, ·)` at every history. **Theorem D0**:
`π^R` is a pure plain fixed point of **every** model. No proof exists in the source
(`theorem1_search.py`, docstring only); the proof here is the mandate writer's sketch, verified: the
invariant `Alt(h, a) ≤ Q^{π^R}(h, a)` at every decision node (depth induction; on residual-null
subtrees `π^R` is `argmax Q^*` and optimal), then at `h` every unplayed action has `Q_ξ = Alt` (Lemma A
with the self term `0`, or `Q^*` on a null subtree) and the played action has
`Q_ξ = w_{ha} Q^π + (1 - w_{ha}) Q̄ ≥ Alt`.

Corollary: a pure plain fixed point exists for every model — this is `uea-cole-shadow`'s open statement
`Model.pure_exists_open`, discharged here (consolidation retires that OPEN row).

Honesty remark: on sink-or-swim with `b(1-s) < c` the policy `π^R` is the **trap** — a pure fixed point
always exists, and it can be the bad one.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace
`Cleanroom.Uea.UeaSinkSwim.ResidualArgmax` (faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace ResidualArgmax

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-! ### `Alt`, the choice, and `π^R` -/

/-- `Alt(h, a) := Q^*_ξ(h, a)` if `ξ_{-S}(ha) = 0`, else `Q̄(h, a)` (policy-free).
Source: `theorem1_search.py` `Structure` (`Alt_h(a) := Qbar(h,a) if a not in N(h), else Q^*(h,a)`); [[uea-2-inventory]] 2-008
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Alt (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  if M.xinsA n h a = 0 then M.Qstar n h a else M.Qmix n h a

/-- One fixed maximiser of `Alt(h, ·)` (a `Classical.choice`, the same disclosure as `π⋆`: the script takes
the first maximiser in an enumeration; any fixed selection works).
Source: `theorem1_search.py` `residual_argmax_policy`
Kind: D
Fidelity: variant: a fixed choice instead of the first action of an enumeration (disclosed)
Hyps: n/a -/
noncomputable def altChoice (n : ℕ) (h : Hist A E n) : A :=
  Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (Alt M n h))

theorem Alt_le_altChoice (n : ℕ) (h : Hist A E n) (a : A) : Alt M n h a ≤ Alt M n h (altChoice M n h) := by
  have hspec := Classical.choose_spec (Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (Alt M n h))
  unfold altChoice
  rw [← hspec.2]
  exact le_sup' _ (mem_univ a)

open Classical in
/-- **The residual-argmax policy** `π^R`: play `altChoice(h)` surely at every history.
Source: `theorem1_search.py` `residual_argmax_policy`; [[uea-2-inventory]] 2-008
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def piR : Policy A E := fun n h a => if a = altChoice M n h then 1 else 0

theorem piR_apply_self (n : ℕ) (h : Hist A E n) : piR M n h (altChoice M n h) = 1 := by simp [piR]

theorem piR_apply_ne {n : ℕ} {h : Hist A E n} {a : A} (ha : a ≠ altChoice M n h) : piR M n h a = 0 := by
  simp [piR, ha]

theorem piR_isPolicy : M.IsPolicy (piR M) := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold piR; split_ifs <;> norm_num
  · rw [sum_eq_single (altChoice M n h)]
    · exact piR_apply_self M n h
    · intro b _ hb; exact piR_apply_ne M hb
    · intro habs; exact absurd (mem_univ _) habs

theorem piR_isPure : M.IsPure (piR M) := fun n h _ => ⟨altChoice M n h, piR_apply_self M n h⟩

/-- At a decision node `V^{π^R}(h) = Q^{π^R}(h, altChoice(h))`. -/
theorem Vpi_piR_eq {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vpi (piR M) n h = M.Qpi (piR M) n h (altChoice M n h) := by
  rw [M.Vpi_eq hnt, sum_eq_single (altChoice M n h)]
  · rw [piR_apply_self, one_mul]
  · intro b _ hb; rw [piR_apply_ne M hb, zero_mul]
  · intro habs; exact absurd (mem_univ _) habs

/-! ### Residual-null subtrees: `π^R` is `argmax Q^*` there and optimal -/

/-- On a residual-null subtree (`ξ_{-S}(h) = 0`) `π^R` is optimal: `V^{π^R}(h) = V^*(h)`.
Source: mandate target 6 (sketch step "if `xinsA h a = 0` the children are residual-null, where `π^R` plays `argmax Q^*`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vpi_piR_eq_Vstar_of_xins_eq_zero : ∀ n h, M.xins n h = 0 → M.Vpi (piR M) n h = M.Vstar n h := by
  refine M.depth_induction (fun n h => M.xins n h = 0 → M.Vpi (piR M) n h = M.Vstar n h) ?_ ?_
  · intro n h hnt _
    rw [M.Vpi_of_not_nonterminal hnt, M.Vstar_of_not_nonterminal hnt]
  · intro n h hnt ih hx
    have hQ : ∀ a, M.Qpi (piR M) n h a = M.Qstar n h a := by
      intro a
      rw [M.Qpi_eq_sum, M.Qstar_eq_sum]
      exact sum_congr rfl fun e _ => by rw [ih a e (M.xins_ext_eq_zero hx a e)]
    have hAlt : ∀ a, Alt M n h a = M.Qstar n h a := fun a => by
      unfold Alt; rw [if_pos (M.xinsA_eq_zero_of_xins_eq_zero hx a)]
    rw [Vpi_piR_eq M hnt, M.Vstar_eq hnt, hQ]
    apply le_antisymm
    · exact le_sup' _ (mem_univ _)
    · rw [Finset.sup'_le_iff]
      intro b _
      rw [← hAlt b, ← hAlt (altChoice M n h)]
      exact Alt_le_altChoice M n h b

/-- `Q^{π^R}(h, a) = Q^*(h, a)` when `ξ_{-S}(ha) = 0`. -/
theorem Qpi_piR_eq_Qstar_of_xinsA_eq_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a = 0) :
    M.Qpi (piR M) n h a = M.Qstar n h a := by
  rw [M.Qpi_eq_sum, M.Qstar_eq_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [Vpi_piR_eq_Vstar_of_xins_eq_zero M _ _ (by rw [M.xins_ext, hA, zero_mul])]

/-- `Q_ξ(h, a) = Q^*(h, a)` under `π^R` when `ξ_{-S}(ha) = 0` (the children are `ξ_{-S}`-null, so `V_ξ = V^π = V^*`). -/
theorem Qxi_piR_eq_Qstar_of_xinsA_eq_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a = 0) :
    M.Qxi (piR M) n h a = M.Qstar n h a := by
  rw [M.Qxi_eq_sum, M.Qstar_eq_sum]
  refine sum_congr rfl fun e _ => ?_
  have hx0 : M.xins (n + 1) (ext h a e) = 0 := by rw [M.xins_ext, hA, zero_mul]
  rw [M.Vxi_eq_Vpi_of_xins_eq_zero (π := piR M) _ _ hx0, Vpi_piR_eq_Vstar_of_xins_eq_zero M _ _ hx0]

/-! ### The invariant `Alt ≤ Q^{π^R}` -/

/-- `V^{π̄}(h) ≤ V^{π^R}(h)`, given the invariant at `h` (`V^{π̄} = 0` where `ξ_{-S}(h) = 0`; otherwise
`V^{π̄} = ∑ π̄ Q̄ ≤ ∑ π̄ · max Alt ≤ Q^{π^R}(h, altChoice) = V^{π^R}(h)`). -/
theorem Vbar_le_Vpi_piR (n : ℕ) (h : Hist A E n)
    (ih : M.nonterminal n h → ∀ a, Alt M n h a ≤ M.Qpi (piR M) n h a) :
    M.Vbar n h ≤ M.Vpi (piR M) n h := by
  by_cases hnt : M.nonterminal n h
  · by_cases hx : M.xins n h = 0
    · rw [M.Vbar_eq hnt]
      rw [sum_eq_zero fun a _ => by rw [M.pibar_of_xins_eq_zero hx a, zero_mul]]
      exact M.Vpi_nonneg (piR_isPolicy M) n h
    · rw [M.Vbar_eq hnt, Vpi_piR_eq M hnt]
      calc ∑ a, M.pibar n h a * M.Qbar n h a
          ≤ ∑ a, M.pibar n h a * M.Qpi (piR M) n h (altChoice M n h) := by
            refine sum_le_sum fun a _ => ?_
            by_cases hA : M.xinsA n h a = 0
            · have h0 : M.pibar n h a = 0 := by unfold Model.pibar; rw [hA, zero_div]
              rw [h0, zero_mul, zero_mul]
            · refine mul_le_mul_of_nonneg_left ?_ (M.pibar_nonneg n h a)
              calc M.Qbar n h a = Alt M n h a := by unfold Alt; rw [if_neg hA, M.Qmix_eq_Qbar hA]
                _ ≤ Alt M n h (altChoice M n h) := Alt_le_altChoice M n h a
                _ ≤ M.Qpi (piR M) n h (altChoice M n h) := ih hnt _
        _ = M.Qpi (piR M) n h (altChoice M n h) := by rw [← sum_mul, M.pibar_sum_eq_one hx, one_mul]
  · rw [M.Vbar_of_not_nonterminal hnt, M.Vpi_of_not_nonterminal hnt]

/-- **The D0 invariant**: at every decision node and every action, `Alt(h, a) ≤ Q^{π^R}(h, a)`.
Source: mandate target 6 (the mandate writer's sketch, verified here)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Alt_le_Qpi_piR : ∀ n h, M.nonterminal n h → ∀ a, Alt M n h a ≤ M.Qpi (piR M) n h a := by
  refine M.depth_induction (fun n h => M.nonterminal n h → ∀ a, Alt M n h a ≤ M.Qpi (piR M) n h a) ?_ ?_
  · intro n h hnt hnt'; exact absurd hnt' hnt
  · intro n h _ ih _ a
    unfold Alt
    split_ifs with hA
    · exact (Qpi_piR_eq_Qstar_of_xinsA_eq_zero M hA).ge
    · rw [M.Qmix_eq_Qbar hA, M.Qbar_eq_sum, M.Qpi_eq_sum]
      refine sum_le_sum fun e _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (M.xie_nonneg n h a e)
      exact add_le_add (le_refl _) (Vbar_le_Vpi_piR M _ _ (ih a e))

/-! ### The fixed-point condition -/

/-- An unplayed action is valued at `Alt`: `Q_ξ(h, b) = Alt(h, b)` for `b ≠ altChoice(h)` (Lemma A with the
self term `0` where the residual has mass; `Q^*` on a residual-null subtree).
Source: mandate target 6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_piR_of_ne {n : ℕ} {h : Hist A E n} {b : A} (hb : b ≠ altChoice M n h) :
    M.Qxi (piR M) n h b = Alt M n h b := by
  have hπ := piR_isPolicy M
  unfold Alt
  split_ifs with hA
  · exact Qxi_piR_eq_Qstar_of_xinsA_eq_zero M hA
  · have hxiA : M.xiA (piR M) n h b = M.xinsA n h b := by
      rw [M.xiA_eq, piR_apply_ne M hb, mul_zero, zero_add]
    have hne : M.xiA (piR M) n h b ≠ 0 := by rw [hxiA]; exact hA
    rw [M.Qxi_eq_wA hπ hne, M.wA_of_xiA_ne_zero hne, piR_apply_ne M hb]
    simp

/-- The played action is valued at least `Alt`: `Alt(h, a_R) ≤ Q_ξ(h, a_R)`
(`Q_ξ = w_{ha} Q^π + (1 - w_{ha}) Q̄ ≥ Alt` by the invariant; `= Q^* = Alt` on a residual-null subtree).
Source: mandate target 6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Alt_le_Qxi_piR_self {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    Alt M n h (altChoice M n h) ≤ M.Qxi (piR M) n h (altChoice M n h) := by
  have hπ := piR_isPolicy M
  by_cases hA : M.xinsA n h (altChoice M n h) = 0
  · apply le_of_eq
    unfold Alt
    rw [if_pos hA, Qxi_piR_eq_Qstar_of_xinsA_eq_zero M hA]
  · have hxiA : M.xiA (piR M) n h (altChoice M n h) =
        (1 - M.δ) * M.xiS (piR M) n h + M.xinsA n h (altChoice M n h) := by
      rw [M.xiA_eq, piR_apply_self, mul_one]
    have hne : M.xiA (piR M) n h (altChoice M n h) ≠ 0 := by
      rw [hxiA]
      have h1 := mul_nonneg (by linarith [M.δ_lt_one] : (0:ℝ) ≤ 1 - M.δ) (M.xiS_nonneg hπ n h hnt)
      have h2 := lt_of_le_of_ne (M.xinsA_nonneg n h _) (Ne.symm hA)
      linarith
    rw [M.Qxi_eq_wA hπ hne]
    have hAlt : Alt M n h (altChoice M n h) = M.Qmix n h (altChoice M n h) := by unfold Alt; rw [if_neg hA]
    have hw0 := M.wA_nonneg hπ hnt (altChoice M n h)
    have hw1 := M.wA_le_one hπ hnt (altChoice M n h)
    have hI := Alt_le_Qpi_piR M n h hnt (altChoice M n h)
    rw [hAlt] at hI ⊢
    nlinarith

/-- **Theorem D0**: `π^R` is a pure plain fixed point of every model.
Source: [[uea-2-inventory]] 2-008 (`theorem1_search.py` docstring, "Theorem D0: always a pure fixed point");
[[uea-inventory]] 018; [[sequential-self-game]] §4.5 CONJECTURE (pure fixed points at every depth)
Kind: P
Fidelity: exact (every model, every depth; the source verified 292 random instances)
Hyps: (a) -/
theorem piR_isPlainFP : M.IsPure (piR M) ∧ M.IsPlainFP (piR M) := by
  refine ⟨piR_isPure M, piR_isPolicy M, fun n h hnt a ha => ?_⟩
  have ha' : a = altChoice M n h := by
    by_contra hne
    rw [piR_apply_ne M hne] at ha
    exact lt_irrefl _ ha
  subst ha'
  apply le_antisymm (M.Qxi_le_Mx _ _ _)
  rw [M.Mx_le_iff]
  intro b
  by_cases hb : b = altChoice M n h
  · rw [hb]
  · rw [Qxi_piR_of_ne M hb]
    exact le_trans (Alt_le_altChoice M n h b) (Alt_le_Qxi_piR_self M hnt)

/-- **Pure plain fixed points exist for every model** — `uea-cole-shadow`'s open statement
`Model.pure_exists_open` ([[sequential-self-game]] §4.5 CONJECTURE, ~0.6), discharged by D0.
Source: [[sequential-self-game]] §4.5; [[uea-inventory]] 013, 018; `run/wp/uea-cole-shadow/uea-cole-shadow-open.txt`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_pure_isPlainFP_all : ∃ π, M.IsPure π ∧ M.IsPlainFP π :=
  ⟨piR M, piR_isPlainFP M⟩

end ResidualArgmax

/-! ### Honesty remark: on sink-or-swim, `π^R` is the trap whenever `b(1-s) < c` -/

namespace ResidualArgmax

open Cleanroom.Uea.UeaColeShadow.SinkOrSwim

variable (P : Params)

theorem sos_xinsA_island_0 : (sos P).xinsA 0 island 0 = 0 := by
  simp [Model.xinsA, νa]

theorem sos_xinsA_island_1 : (sos P).xinsA 0 island 1 = P.δ := by
  simp [Model.xinsA, Fin.sum_univ_two, νa]; ring

theorem sos_Qbar_water_0 : (sos P).Qbar 1 water 0 = P.b := by
  rw [Model.Qbar_eq_sum, Fintype.sum_unique, xie_eq_one, (sos P).Vbar_of_not_nonterminal (not_nt_two P _)]
  simp [r, water]

theorem sos_Qbar_water_1 : (sos P).Qbar 1 water 1 = 0 := by
  rw [Model.Qbar_eq_sum, Fintype.sum_unique, xie_eq_one, (sos P).Vbar_of_not_nonterminal (not_nt_two P _)]
  simp [r, water]

theorem sos_pibar_water_0 : (sos P).pibar 1 water 0 = 1 - P.s := by
  unfold Model.pibar
  rw [xinsA_water_swim, xins_water]
  have := P.hδ.ne'
  field_simp

/-- `Alt(island, stay) = c` and `Alt(island, jump) = b(1-s)` on sink-or-swim. -/
theorem sos_Alt_island : Alt (sos P) 0 island 0 = P.c ∧ Alt (sos P) 0 island 1 = P.b * (1 - P.s) := by
  constructor
  · unfold Alt
    rw [if_pos (sos_xinsA_island_0 P), Qstar_island_0]
  · unfold Alt
    rw [if_neg (by rw [sos_xinsA_island_1]; exact P.hδ.ne'), (sos P).Qmix_eq_Qbar (by rw [sos_xinsA_island_1]; exact P.hδ.ne'),
      Model.Qbar_eq_sum, Fintype.sum_unique, xie_eq_one]
    show 1 * ((sos P).γ ^ 0 * (sos P).r 0 water + (sos P).Vbar 1 water) = P.b * (1 - P.s)
    rw [(sos P).Vbar_eq (nt_water P), Fin.sum_univ_two, sos_Qbar_water_0, sos_Qbar_water_1, sos_pibar_water_0]
    simp [r, water]
    ring

/-- **D0 is honest**: on `sos P` with `b(1-s) < c`, `π^R` plays `stay` at the island — it is the trap.
Source: mandate target 6 (non-vacuity remark)
Kind: N+
Fidelity: exact (strict inequality; at `b(1-s) = c` the choice is unspecified)
Hyps: (a) -/
theorem piR_sos_is_trap (h : P.b * (1 - P.s) < P.c) : piR (sos P) 0 island 0 = 1 := by
  obtain ⟨h0, h1⟩ := sos_Alt_island P
  have hch : altChoice (sos P) 0 island = 0 := by
    have := Alt_le_altChoice (sos P) 0 island 0
    have hc : altChoice (sos P) 0 island = 0 ∨ altChoice (sos P) 0 island = 1 := by
      generalize altChoice (sos P) 0 island = x
      fin_cases x <;> simp
    rcases hc with hc | hc
    · exact hc
    · rw [hc, h1, h0] at this
      linarith
  rw [← hch, piR_apply_self]

end ResidualArgmax

end Cleanroom.Uea.UeaSinkSwim
