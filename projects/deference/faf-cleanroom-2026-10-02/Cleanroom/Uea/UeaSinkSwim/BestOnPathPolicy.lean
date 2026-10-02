import Cleanroom.Uea.UeaSinkSwim.BestOnPath

/-!
# D1, part 2: the best-on-path policy `π^B`, its fixed-point property and the bound; target 9(+)

`choice(h)` is a fixed feasible maximiser of `val(h, ·)`; `onPath(h)` holds when every action along `h` was
the `choice` at its node; `π^B` plays `choice(h)` surely at on-path nodes and `π^R` elsewhere.

**Theorem D1**: `π^B` is a pure plain fixed point of every model, and at every decision node with
`w_h ≥ 1 - δ` its loss is at most `ε_n = 1 - (1-δ)^(T-1-n)`. Proof: off the path the self-mass is `0`, so
`Q_ξ = Alt` at every action and `π^B = π^R` is an argmax; on the path `ξ_S = Pe`, `V^{π^B} = B`, every
unplayed action has `Q_ξ = Alt ≤ rival(choice) ≤ S(choice) = Q_ξ(choice)` (feasibility of the choice), and
`w_h ≥ 1 - δ` forces on-path (`ξ_S > 0`) or `ξ`-null (loss `0`), where `V^* - B ≤ ε_n` (part 1).

**Target 9(+)**: `∀ ε > 0, ∀ T ≥ 2, ∃ δ₀ = ε/(T-1), ∀ M` with `M.T = T`, `M.δ < δ₀`: `π^B` is a pure plain
fixed point with loss `< ε` at every node with `w_h ≥ 1 - δ` (Bernoulli: `1 - (1-δ)^(T-1) ≤ (T-1) δ`).
Neither this nor 9(−) uses the trust bound as a hypothesis.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.BestOnPath`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow
open ResidualArgmax (Alt altChoice piR piR_isPolicy piR_apply_self piR_apply_ne Vpi_piR_eq_Vstar_of_xins_eq_zero
  Alt_le_altChoice)

namespace BestOnPath

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-! ### The choice, the path, the policy -/

open Classical in
/-- One fixed feasible maximiser of `val(h, ·)` (a `Classical.choice`; the script takes the first).
Source: `theorem1_search.py` `best_onpath` (`choice`)
Kind: D
Fidelity: variant: a fixed choice instead of the first action of an enumeration (disclosed)
Hyps: n/a -/
noncomputable def choice (n : ℕ) (h : Hist A E n) : A :=
  if hne : (univ.filter (feasible M n h)).Nonempty then
    Classical.choose (Finset.exists_mem_eq_sup' hne (val M n h))
  else altChoice M n h

open Classical in
theorem choice_spec {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    feasible M n h (choice M n h) ∧ B M n h = val M n h (choice M n h) := by
  have hne := filter_nonempty M hnt
  have hspec := Classical.choose_spec (Finset.exists_mem_eq_sup' hne (val M n h))
  unfold choice
  rw [dif_pos hne]
  exact ⟨(mem_filter.1 hspec.1).2, by rw [B_eq_sup' M hnt hne]; exact hspec.2⟩

theorem choice_feasible {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) : feasible M n h (choice M n h) :=
  (choice_spec M hnt).1

theorem B_eq_val_choice {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) : B M n h = val M n h (choice M n h) :=
  (choice_spec M hnt).2

/-- `onPath(h)`: every action along `h` was the `choice` at its node.
Source: `theorem1_search.py` `best_onpath_policy` (`onpath`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def onPath : (n : ℕ) → Hist A E n → Prop
  | 0, _ => True
  | n + 1, h => onPath n (Fin.init h) ∧ (h (Fin.last n)).1 = choice M n (Fin.init h)

theorem onPath_zero (h : Hist A E 0) : onPath M 0 h := trivial

theorem onPath_ext_iff {n : ℕ} (h : Hist A E n) (a : A) (e : E) :
    onPath M (n + 1) (ext h a e) ↔ onPath M n h ∧ a = choice M n h := by
  simp [onPath]

theorem onPath_init {n : ℕ} {h : Hist A E (n + 1)} (hp : onPath M (n + 1) h) : onPath M n (Fin.init h) := hp.1

open Classical in
/-- **The best-on-path policy** `π^B`: `choice(h)` surely at on-path nodes, `π^R` elsewhere.
Source: `theorem1_search.py` `best_onpath_policy`; [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def piB : Policy A E := fun n h a =>
  if onPath M n h then (if a = choice M n h then 1 else 0) else piR M n h a

open Classical in
theorem piB_onPath {n : ℕ} {h : Hist A E n} (hp : onPath M n h) (a : A) :
    piB M n h a = if a = choice M n h then 1 else 0 := by
  simp [piB, hp]

theorem piB_offPath {n : ℕ} {h : Hist A E n} (hp : ¬ onPath M n h) (a : A) : piB M n h a = piR M n h a := by
  simp [piB, hp]

theorem piB_onPath_choice {n : ℕ} {h : Hist A E n} (hp : onPath M n h) : piB M n h (choice M n h) = 1 := by
  rw [piB_onPath M hp, if_pos rfl]

theorem piB_onPath_ne {n : ℕ} {h : Hist A E n} (hp : onPath M n h) {a : A} (ha : a ≠ choice M n h) :
    piB M n h a = 0 := by
  rw [piB_onPath M hp, if_neg ha]

theorem piB_isPolicy : M.IsPolicy (piB M) := by
  intro n h hnt
  by_cases hp : onPath M n h
  · refine ⟨fun a => ?_, ?_⟩
    · rw [piB_onPath M hp]; split_ifs <;> norm_num
    · rw [sum_eq_single (choice M n h)]
      · exact piB_onPath_choice M hp
      · intro b _ hb; exact piB_onPath_ne M hp hb
      · intro habs; exact absurd (mem_univ _) habs
  · have := piR_isPolicy M n h hnt
    refine ⟨fun a => ?_, ?_⟩
    · rw [piB_offPath M hp]; exact this.1 a
    · rw [sum_congr rfl fun a _ => piB_offPath M hp a]; exact this.2

theorem piB_isPure : M.IsPure (piB M) := by
  intro n h hnt
  by_cases hp : onPath M n h
  · exact ⟨choice M n h, piB_onPath_choice M hp⟩
  · exact ⟨altChoice M n h, by rw [piB_offPath M hp]; exact piR_apply_self M n h⟩

/-! ### Off the path: no self-mass, `π^B = π^R` -/

/-- Off the path the self-hypothesis has no mass: `ξ_S(h) = 0`. -/
theorem xiS_piB_offPath : ∀ (n : ℕ) (h : Hist A E n), ¬ onPath M n h → M.xiS (piB M) n h = 0 := by
  intro n
  induction n with
  | zero => intro h hp; exact absurd (onPath_zero M h) hp
  | succ n ih =>
    intro h hp
    have hx := M.xiS_ext (piB M) (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
    rw [ext_init_last] at hx
    rw [hx]
    by_cases hp' : onPath M n (Fin.init h)
    · have hne : (h (Fin.last n)).1 ≠ choice M n (Fin.init h) := fun heq => hp ⟨hp', heq⟩
      rw [piB_onPath_ne M hp' hne]; ring
    · rw [ih _ hp']; ring

/-- Off the path `π^B` has the values of `π^R` (the whole subtree is off the path).
Source: mandate target 7
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Vpi_piB_offPath : ∀ (n : ℕ) (h : Hist A E n), ¬ onPath M n h → M.Vpi (piB M) n h = M.Vpi (piR M) n h := by
  refine M.depth_induction (fun n h => ¬ onPath M n h → M.Vpi (piB M) n h = M.Vpi (piR M) n h) ?_ ?_
  · intro n h hnt _
    rw [M.Vpi_of_not_nonterminal hnt, M.Vpi_of_not_nonterminal hnt]
  · intro n h hnt ih hp
    rw [M.Vpi_eq hnt, M.Vpi_eq hnt]
    refine sum_congr rfl fun a _ => ?_
    rw [piB_offPath M hp a]
    congr 1
    rw [Model.Qpi_eq_sum, Model.Qpi_eq_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [ih a e (fun hc => hp ((onPath_ext_iff M h a e).1 hc).1)]

/-! ### On the path: `ξ_S = Pe` and `V^{π^B} = B` -/

theorem xiS_piB_onPath : ∀ (n : ℕ) (h : Hist A E n), onPath M n h → M.xiS (piB M) n h = Pe M n h := by
  intro n
  induction n with
  | zero => intro h _; simp
  | succ n ih =>
    intro h hp
    have hx := M.xiS_ext (piB M) (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
    rw [ext_init_last] at hx
    rw [hx, ih _ hp.1, hp.2, piB_onPath_choice M hp.1, mul_one]
    simp [Pe, hp.2]

/-- `V^{π^B}(h) = B(h)` at every on-path history.
Source: mandate target 7 ("on-path `Vpi piB = B`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vpi_piB_onPath : ∀ (n : ℕ) (h : Hist A E n), onPath M n h → M.Vpi (piB M) n h = B M n h := by
  refine M.depth_induction (fun n h => onPath M n h → M.Vpi (piB M) n h = B M n h) ?_ ?_
  · intro n h hnt _
    rw [M.Vpi_of_not_nonterminal hnt, B_eq_zero_of_not_nonterminal M hnt]
  · intro n h hnt ih hp
    have hQ : M.Qpi (piB M) n h (choice M n h) = cont M n h (choice M n h) := by
      rw [Model.Qpi_eq_sum, cont_eq]
      refine sum_congr rfl fun e _ => ?_
      rw [ih _ e ((onPath_ext_iff M h _ e).2 ⟨hp, rfl⟩)]
    rw [M.Vpi_eq hnt, sum_eq_single (choice M n h)]
    · rw [piB_onPath_choice M hp, one_mul, hQ, B_eq_val_choice M hnt]
      by_cases hA : M.xinsA n h (choice M n h) = 0
      · rw [val_of_xinsA_eq_zero M hA, cont_eq, M.Qstar_eq_sum]
        refine sum_congr rfl fun e _ => ?_
        rw [B_eq_Vstar_of_xins_eq_zero M _ _ (by rw [M.xins_ext, hA, zero_mul])]
      · rw [val_of_xinsA_ne_zero M hA]
    · intro b _ hb; rw [piB_onPath_ne M hp hb, zero_mul]
    · intro habs; exact absurd (mem_univ _) habs

/-! ### `Q_ξ` under `π^B` -/

/-- An action with no self-mass after it is valued at `Alt`: `Q_ξ(h, b) = Alt(h, b)` whenever
`ξ_S(h) π^B(b|h) = 0` and the children of `(h, b)` are off the path or residual-null.
Source: mandate target 7
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Qxi_piB_eq_Alt {n : ℕ} {h : Hist A E n} {b : A} (hself : M.xiS (piB M) n h * piB M n h b = 0)
    (hoff : ∀ e, ¬ onPath M (n + 1) (ext h b e)) : M.Qxi (piB M) n h b = Alt M n h b := by
  have hπ := piB_isPolicy M
  unfold Alt
  split_ifs with hA
  · rw [M.Qxi_eq_sum, M.Qstar_eq_sum]
    refine sum_congr rfl fun e _ => ?_
    have hx0 : M.xins (n + 1) (ext h b e) = 0 := by rw [M.xins_ext, hA, zero_mul]
    rw [M.Vxi_eq_Vpi_of_xins_eq_zero (π := piB M) _ _ hx0, Vpi_piB_offPath M _ _ (hoff e),
      Vpi_piR_eq_Vstar_of_xins_eq_zero M _ _ hx0]
  · have hxiA : M.xiA (piB M) n h b = M.xinsA n h b := by
      rw [M.xiA_eq, mul_assoc, hself, mul_zero, zero_add]
    have hne : M.xiA (piB M) n h b ≠ 0 := by rw [hxiA]; exact hA
    rw [M.Qxi_eq_wA hπ hne, M.wA_of_xiA_ne_zero hne, mul_assoc, hself]
    simp

theorem Qxi_piB_offPath {n : ℕ} {h : Hist A E n} (hp : ¬ onPath M n h) (b : A) :
    M.Qxi (piB M) n h b = Alt M n h b :=
  Qxi_piB_eq_Alt M (by rw [xiS_piB_offPath M n h hp, zero_mul])
    (fun e hc => hp ((onPath_ext_iff M h b e).1 hc).1)

theorem Qxi_piB_onPath_ne {n : ℕ} {h : Hist A E n} (hp : onPath M n h) {b : A} (hb : b ≠ choice M n h) :
    M.Qxi (piB M) n h b = Alt M n h b :=
  Qxi_piB_eq_Alt M (by rw [piB_onPath_ne M hp hb, mul_zero])
    (fun e hc => hb ((onPath_ext_iff M h b e).1 hc).2)

/-- On the path the chosen action is valued at `S`: `Q_ξ(h, choice(h)) = S(h, choice(h))`
(`w_{h choice} = wtA` since `ξ_S(h) = Pe(h)` and `π^B(choice|h) = 1`; `Q^{π^B}(h, choice) = cont`).
Source: mandate target 7
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_piB_onPath_choice {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hp : onPath M n h) :
    M.Qxi (piB M) n h (choice M n h) = S M n h (choice M n h) := by
  have hπ := piB_isPolicy M
  have hQ : M.Qpi (piB M) n h (choice M n h) = cont M n h (choice M n h) := by
    rw [Model.Qpi_eq_sum, cont_eq]
    refine sum_congr rfl fun e _ => ?_
    rw [Vpi_piB_onPath M _ _ ((onPath_ext_iff M h _ e).2 ⟨hp, rfl⟩)]
  by_cases hA : M.xinsA n h (choice M n h) = 0
  · rw [S_of_xinsA_eq_zero M hA, M.Qxi_eq_sum, M.Qstar_eq_sum]
    refine sum_congr rfl fun e _ => ?_
    have hx0 : M.xins (n + 1) (ext h (choice M n h) e) = 0 := by rw [M.xins_ext, hA, zero_mul]
    rw [M.Vxi_eq_Vpi_of_xins_eq_zero (π := piB M) _ _ hx0,
      Vpi_piB_onPath M _ _ ((onPath_ext_iff M h _ e).2 ⟨hp, rfl⟩), B_eq_Vstar_of_xins_eq_zero M _ _ hx0]
  · have hS := xiS_piB_onPath M n h hp
    have hxiA : M.xiA (piB M) n h (choice M n h) = (1 - M.δ) * Pe M n h + M.xinsA n h (choice M n h) := by
      rw [M.xiA_eq, hS, piB_onPath_choice M hp, mul_one]
    have hD : (1 - M.δ) * Pe M n h + M.xinsA n h (choice M n h) ≠ 0 := by
      have := Pe_nonneg M n h
      have := lt_of_le_of_ne (M.xinsA_nonneg n h _) (Ne.symm hA)
      have := one_sub_δ_pos M
      positivity
    have hne : M.xiA (piB M) n h (choice M n h) ≠ 0 := by rw [hxiA]; exact hD
    have hw : M.wA (piB M) n h (choice M n h) = wtA M n h (choice M n h) := by
      rw [M.wA_of_xiA_ne_zero hne, hxiA, hS, piB_onPath_choice M hp, mul_one]
      unfold wtA
      rw [if_neg hD]
    rw [M.Qxi_eq_wA hπ hne, hw, hQ, S_of_xinsA_ne_zero M hA]

/-! ### Theorem D1 -/

/-- **`π^B` is a pure plain fixed point of every model.**
Source: [[uea-2-inventory]] 2-009 (D1, the fixed-point half); the proof is the mandate writer's sketch, verified
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem piB_isPlainFP : M.IsPure (piB M) ∧ M.IsPlainFP (piB M) := by
  refine ⟨piB_isPure M, piB_isPolicy M, fun n h hnt a ha => ?_⟩
  by_cases hp : onPath M n h
  · have ha' : a = choice M n h := by
      by_contra hne
      rw [piB_onPath_ne M hp hne] at ha
      exact lt_irrefl _ ha
    subst ha'
    apply le_antisymm (M.Qxi_le_Mx _ _ _)
    rw [M.Mx_le_iff]
    intro b
    by_cases hb : b = choice M n h
    · rw [hb]
    · rw [Qxi_piB_onPath_ne M hp hb, Qxi_piB_onPath_choice M hnt hp]
      exact le_trans (Alt_le_rival M hb) (choice_feasible M hnt)
  · have ha' : a = altChoice M n h := by
      by_contra hne
      rw [piB_offPath M hp, piR_apply_ne M hne] at ha
      exact lt_irrefl _ ha
    subst ha'
    apply le_antisymm (M.Qxi_le_Mx _ _ _)
    rw [M.Mx_le_iff]
    intro b
    rw [Qxi_piB_offPath M hp b, Qxi_piB_offPath M hp]
    exact Alt_le_altChoice M n h b

/-- On the path `w_h ≥ 1 - δ` (`ξ_S = Pe`, `ξ_{-S} ≤ δ Pe`). -/
theorem one_sub_δ_le_wS_piB_onPath {n : ℕ} {h : Hist A E n} (hp : onPath M n h) :
    1 - M.δ ≤ M.wS (piB M) n h := by
  by_cases hx : M.xi (piB M) n h = 0
  · rw [Model.wS_of_xi_eq_zero M hx]; linarith [M.δ_pos]
  · rw [Model.wS_of_xi_ne_zero M hx, xiS_piB_onPath M n h hp]
    have hxi : M.xi (piB M) n h = (1 - M.δ) * Pe M n h + M.xins n h := by
      unfold Model.xi; rw [xiS_piB_onPath M n h hp]
    have hpos : 0 < M.xi (piB M) n h := by
      rw [hxi]
      have := Pe_nonneg M n h; have := M.xins_nonneg n h; have := one_sub_δ_pos M
      exact lt_of_le_of_ne (by positivity) (by rw [← hxi]; exact Ne.symm hx)
    rw [le_div_iff₀ hpos, hxi]
    have h4 := xins_le_delta_Pe M n h
    have := one_sub_δ_pos M
    nlinarith [M.δ_pos, Pe_nonneg M n h]

/-- **The loss of `π^B` at a trusted node**: at every decision node with `w_h ≥ 1 - δ`,
`V^*(h) - V^{π^B}(h) ≤ ε_n = 1 - (1-δ)^(T-1-n)` (such a node is on the path, where `V^{π^B} = B`, or
`ξ`-null, where the loss is `0`).
Source: [[uea-2-inventory]] 2-009 (D1, the bound)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap_piB_le {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hw : 1 - M.δ ≤ M.wS (piB M) n h) :
    M.gap (piB M) n h ≤ eps M n := by
  have hπ := piB_isPolicy M
  by_cases hx : M.xi (piB M) n h = 0
  · have hx0 : M.xins n h = 0 := M.xins_eq_zero_of_xi_eq_zero hπ hnt hx
    have hV : M.Vpi (piB M) n h = M.Vstar n h := by
      by_cases hp : onPath M n h
      · rw [Vpi_piB_onPath M n h hp, B_eq_Vstar_of_xins_eq_zero M n h hx0]
      · rw [Vpi_piB_offPath M n h hp, Vpi_piR_eq_Vstar_of_xins_eq_zero M n h hx0]
    unfold Model.gap
    rw [hV, sub_self]
    exact eps_nonneg M n
  · have hwpos : 0 < M.wS (piB M) n h := lt_of_lt_of_le (one_sub_δ_pos M) hw
    have hS : 0 < M.xiS (piB M) n h := M.xiS_pos_of_wS_pos hπ hnt hx hwpos
    have hp : onPath M n h := by
      by_contra hp
      rw [xiS_piB_offPath M n h hp] at hS
      exact lt_irrefl _ hS
    unfold Model.gap
    rw [Vpi_piB_onPath M n h hp]
    exact Vstar_sub_B_le M n h

/-- **Theorem D1**: `π^B` is a pure plain fixed point of every model, and at every decision node with
`w_h ≥ 1 - δ` its loss is at most `1 - (1-δ)^(T-1-n)`. Corollary: `L ≤ 1 - (1-δ)^(T-1) ≤ (T-1) δ`.
Source: [[uea-2-inventory]] 2-009 (D1); `theorem1_search.py` `best_onpath`, `bound`; [[uea-inventory]] 018
Kind: P
Fidelity: exact (the source verified 292 random instances; the proof is the mandate writer's sketch, verified)
Hyps: (a) -/
theorem theoremD1 : M.IsPure (piB M) ∧ M.IsPlainFP (piB M) ∧
    ∀ n h, M.nonterminal n h → 1 - M.δ ≤ M.wS (piB M) n h →
      M.gap (piB M) n h ≤ 1 - (1 - M.δ) ^ (M.T - 1 - n) :=
  ⟨(piB_isPlainFP M).1, (piB_isPlainFP M).2, fun _ _ hnt hw => gap_piB_le M hnt hw⟩

/-- Every on-path node is trusted (`w ≥ 1 - δ`) and so carries the bound. -/
theorem gap_piB_onPath_le {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hp : onPath M n h) :
    M.gap (piB M) n h ≤ eps M n :=
  gap_piB_le M hnt (one_sub_δ_le_wS_piB_onPath M hp)

/-- Bernoulli: `1 - (1-δ)^k ≤ k δ`. -/
theorem one_sub_pow_le (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) : 1 - (1 - δ) ^ k ≤ k * δ := by
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) k
  rw [show (1 : ℝ) + -δ = 1 - δ by ring] at this
  linarith

/-- **Corollary (the horizon bound)**: at every trusted node, `gap ≤ 1 - (1-δ)^(T-1) ≤ (T-1) δ`.
Source: [[uea-2-inventory]] 2-009 ("hence `L ≤ 1-(1-δ)^{T-1} ≤ (T-1)δ`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gap_piB_le_horizon {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hw : 1 - M.δ ≤ M.wS (piB M) n h) :
    M.gap (piB M) n h ≤ 1 - (1 - M.δ) ^ (M.T - 1) ∧ M.gap (piB M) n h ≤ (M.T - 1 : ℕ) * M.δ := by
  have h1 := gap_piB_le M hnt hw
  have h2 : (1 - M.δ) ^ (M.T - 1) ≤ (1 - M.δ) ^ (M.T - 1 - n) :=
    pow_le_pow_of_le_one (one_sub_δ_pos M).le (one_sub_δ_le_one M) (Nat.sub_le _ _)
  have h3 := one_sub_pow_le M.δ M.δ_pos.le M.δ_lt_one.le (M.T - 1)
  unfold eps at h1
  exact ⟨by linarith, by linarith⟩

end BestOnPath

/-! ### Target 9(+): Cole's conclusion for the plain agent with a horizon-dependent `δ` -/

namespace Quantifiers

open BestOnPath

/-- **`∀ε ∀T ∃δ` (target 9(+))**: for every `ε > 0` and horizon `T ≥ 2` there is `δ₀ = ε/(T-1) > 0` such that every
model of horizon `T` with non-self prior `δ < δ₀` has a pure plain fixed point (`π^B`) whose loss at every
decision node with `w_h ≥ 1 - δ` is `< ε`. Cole's revised conclusion is witnessable for the plain agent with a
horizon-dependent `δ` — the same quantifier structure as his `T_ε`; the trust bound is not a hypothesis here
(it is what makes the per-node bound hold at *every* fixed point, Theorem B). With `TrapChain.no_horizon_free_delta`
(9(−)): `∀ε ∃δ ∀T` fails at `γ = 1`.
Source: [[uea-2-inventory]] 2-010 (positive half), 2-009; [[uea-inventory]] 018, 006
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem horizon_dependent_delta (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 2 ≤ T) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (A E ι : Type) [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι),
        M.T = T → M.δ < δ₀ →
          ∃ π, M.IsPure π ∧ M.IsPlainFP π ∧
            ∀ n h, M.nonterminal n h → 1 - M.δ ≤ M.wS π n h → M.gap π n h < ε := by
  have hT1 : (0 : ℝ) < (T - 1 : ℕ) := by
    have : 1 ≤ T - 1 := by omega
    exact_mod_cast this
  refine ⟨ε / (T - 1 : ℕ), div_pos hε hT1, ?_⟩
  intro A E ι _ _ _ _ M hMT hMδ
  refine ⟨piB M, (piB_isPlainFP M).1, (piB_isPlainFP M).2, fun n h hnt hw => ?_⟩
  have h1 := (gap_piB_le_horizon M hnt hw).2
  rw [hMT] at h1
  have h2 : ((T - 1 : ℕ) : ℝ) * M.δ < ((T - 1 : ℕ) : ℝ) * (ε / (T - 1 : ℕ)) :=
    mul_lt_mul_of_pos_left hMδ hT1
  rw [mul_div_cancel₀ _ hT1.ne'] at h2
  linarith

end Quantifiers

end Cleanroom.Uea.UeaSinkSwim
